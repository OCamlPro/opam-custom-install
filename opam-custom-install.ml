(**************************************************************************)
(*                                                                        *)
(*    Copyright 2020 OCamlPro                                             *)
(*                                                                        *)
(*  All rights reserved. This file is distributed under the terms of the  *)
(*  GNU Lesser General Public License version 2.1, with the special       *)
(*  exception on linking described in the file LICENSE.                   *)
(*                                                                        *)
(**************************************************************************)

open Cmdliner
open OpamTypes
open OpamPackage.Set.Op

let custom_install_doc =
  "Install a package using a custom command."

let custom_install =
  let doc = custom_install_doc in
  let man = [
    `S Manpage.s_description;
    `P "This command allows to wrap a custom install command, and make opam \
        register it as the installation of a given package.";
    `P "Be aware that this is a low-level command that allows you to break \
        some opam invariants: use this if you want to be in complete control \
        over the installation of the given package, and are ready to cope with \
        the consequences in the opam commands that you will run next.";
    `P "Any previously installed version of the package will still be removed \
        before performing the installation, together with packages that have a \
        dependency on $(i,PACKAGE) (unless $(b,--no-recompilations) was \
        specified), which will be recompiled afterwards.";
    `P "Usecase: you are working on the source of some package, pinned or not, \
        and want to quickly test your patched version without having opam \
        clone and recompile the whole source. Running $(b,opam custom-install \
        foo -- make install) instead of just $(b,make install) has the \
        benefits that (i) opam will allow you to intall packages depending on \
        $(b,foo), and (ii) when you choose to reinstall $(b,foo) later on, \
        opam will be able to cleanly remove your custom installation.";
    `S Manpage.s_arguments;
    `S Manpage.s_options;
  ] @ OpamArg.man_build_option_section
  in
  let no_recompilations =
    Arg.(value & flag & info ["no-recompilations"; "n"] ~doc:
           "Just do the installation, ignoring and preserving the state of any \
            dependent packages.")
  in
  let package =
    Arg.(required & pos 0 (some OpamArg.package) None &
         info [] ~docv:"PACKAGE[.VERSION]" ~doc:
           "Package which should be registered as installed with the files \
            installed by $(i,COMMAND).")
  in
  let cmd =
    Arg.(non_empty & pos_right 0 string [] &
         info [] ~docv:"-- COMMAND [ARG]" ~doc:
           "Command to run in the current directory that is expected to \
            install the files for $(i,PACKAGE) to the current opam switch \
            prefix. Variable expansions like $(b,%{prefix}%), $(b,%{name}%), \
            $(b,%{version}%) and $(b,%{package}) are expanded as per the \
            $(i,install:) package definition field.")
  in
  let custom_install
      global_options build_options no_recompilations package cmd =
    OpamArg.apply_global_options global_options;
    OpamArg.apply_build_options build_options;
    OpamClientConfig.update ~inplace_build:true ();
    OpamGlobalState.with_ `Lock_none @@ fun gt ->
    OpamSwitchState.with_ `Lock_write gt @@ fun st ->
    let nv = match package with
      | name, Some v -> OpamPackage.create name v
      | name, None ->
        try OpamSwitchState.get_package st name
        with Not_found ->
          OpamPackage.create name (OpamPackage.Version.of_string "~dev")
    in
    let is_installed = OpamSwitchState.is_name_installed st nv.name in
    let build_dir = OpamFilename.cwd () in
    let opam =
      OpamFile.OPAM.create nv
      |> OpamFile.OPAM.with_install
        [List.map (fun a -> CString a, None) cmd, None]
      |> OpamFile.OPAM.with_synopsis
        ("Package installed using 'opam custom-install' from "^
         OpamFilename.Dir.to_string build_dir)
      |> OpamFile.OPAM.with_url (* needed for inplace_build correct build dir *)
        (* FIXME: but that incurs an undesirable sync *)
        (OpamFile.URL.create
           (OpamUrl.parse ~backend:`rsync
              (OpamFilename.Dir.to_string build_dir)))
    in
    let st =
      {st with
       opams = OpamPackage.Map.add nv opam st.opams;
       packages = OpamPackage.Set.add nv st.packages;
       available_packages =
         lazy (OpamPackage.Set.add nv (Lazy.force st.available_packages));
      }
    in
    let simple_install () =
      (* when no recompilations are needed *)
      let st =
        if is_installed then
          let old_pkg = OpamPackage.package_of_name st.installed nv.name in
          let st = OpamSwitchAction.remove_from_installed st old_pkg in
          OpamProcess.Job.run @@
          OpamAction.remove_package st ~force:true old_pkg;
          st
        else st
      in
      match
        OpamProcess.Job.run @@
        OpamAction.install_package st ~build_dir nv
      with
      | Some exn -> raise exn
      | None -> OpamSwitchAction.add_to_installed st ~root:true nv
    in
    let st =
      if no_recompilations || not is_installed then simple_install ()
      else
      let atoms = [OpamSolution.eq_atom_of_package nv] in
      let st, full_orphans, orphan_versions =
        OpamClient.check_conflicts st atoms
      in
      let request = OpamSolver.request ~install:atoms ~criteria:`Fixup () in
      let requested = OpamPackage.Name.Set.singleton nv.name in
      let solution =
        OpamSolution.resolve st Reinstall
          ~orphans:(full_orphans ++ orphan_versions)
          ~reinstall:(OpamPackage.packages_of_names st.installed requested)
          ~requested
          request
      in
      let st, res = match solution with
        | Conflicts cs ->
          (* this shouldn't happen, the package requested has no requirements *)
          OpamConsole.error "Package conflict!";
          OpamConsole.errmsg "%s"
            (OpamCudf.string_of_conflicts st.packages
               (OpamSwitchState.unavailable_reason st) cs);
          OpamStd.Sys.exit_because `No_solution
        | Success solution ->
          (* let solution = OpamSolver.filter_solution ((<>) nv) solution in
           * OpamSolver.filter_solution
           * if OpamSolver.solution_is_empty solution then simple_install () *)
          OpamSolution.apply st ~requested ~assume_built:true solution
      in
      OpamSolution.check_solution st (Success res);
      st
    in
    OpamSwitchState.drop st
  in
  Term.(const custom_install
        $OpamArg.global_options $OpamArg.build_options
        $no_recompilations $package $cmd),
  OpamArg.term_info "custom-install" ~doc ~man

let () =
  OpamSystem.init ();
  OpamCliMain.main_catch_all @@ fun () ->
  match Term.eval ~catch:false custom_install with
  | `Error _ -> exit (OpamStd.Sys.get_exit_code `Bad_arguments)
  | _        -> exit (OpamStd.Sys.get_exit_code `Success)




(* -- junkyard, might be useful for scrap code if we want to do the
   recompilations more manually *)


(* let with_recompile_cone st nv f =
 *   let revdeps =
 *     let deps nv =
 *       OpamSwitchState.opam st nv |>
 *       OpamPackageVar.all_depends
 *         ~build:true ~post:false ~test:false ~doc:false
 *         ~dev:(OpamSwitchState.is_dev_package st nv)
 *     in
 *     OpamPackage.Set.filter (fun nv1 -> OpamFormula.verifies (deps nv1) nv)
 *       st.installed_packages
 *   in
 *   if OpamPackage.Set.is_empty revdeps then f () else
 *   let univ =
 *     OpamSwitchState.universe ~reinstall:revdeps ~requested:nv st
 *   in
 * 
 *    * let sol =
 *    *   OpamSolver.resolve universe ~orphans:OpamPackage.Set.empty
 *    *     { criteria=`Fixup;
 *    *       wish_install=[];
 *    *       wish_remove=[];
 *    *       wish_upgrade=[];
 *    *       extra_attributes=[];
 *    *     } *)
  

  (* let recompile_cone =
   *   OpamPackage.Set.of_list @@
   *   OpamSolver.reverse_dependencies
   *     ~depopts:true ~installed:true ~unavailable:true
   *     ~build:true ~post:false
   *     universe (OpamPackage.Set.singleton nv)
   * in
   * 
   * (\* The API exposes no other way to create an empty solution *\)
   * let solution = OpamSolver.solution_of_json `Null in
   * OpamSolver.print_solution
   *   ~messages:(fun _ -> [])
   *   ~append:(fun nv -> if OpamSwitchState.Set.mem nv st.pinned then "*" else "")
   *   ~requested:OpamPackage.Name.Set.empty
   *   ~reinstall:recompile_cone
   *   solution;
   * 
   * let 
   *   OpamSwitchState.universe ~reinstall:(OpamPackage.Set.singleton nv) ~requested:nv st
   * in
   * let sol =
   *   OpamSolver.resolve universe ~orphans:OpamPackage.Set.empty
   *     { criteria=`Fixup;
   *       wish_install=[];
   *       wish_remove=[];
   *       wish_upgrade=[];
   *       extra_attributes=[];
   *     }
   * in *)


open Cmdliner
open OpamTypes
open OpamPackage.Set.Op

let custom_install_doc =
  "Install a package using a custom command."

module OpamClient = struct
  include OpamClient

  (* Functions that should be exported from OpamClient, copied verbatim
     (as of 20544c6) *)
open OpamTypes
open OpamStateTypes
open OpamStd.Op
open OpamPackage.Set.Op

let log fmt = OpamConsole.log "CLIENT" fmt
let slog = OpamConsole.slog

let orphans ?changes ?(transitive=false) t =
  let all = t.packages ++ t.installed in
  let available = Lazy.force t.available_packages in
  let allnames = OpamPackage.names_of_packages all in
  let invalidated = Lazy.force t.invalidated in
  let universe =
    OpamSwitchState.universe t ~requested:OpamPackage.Name.Set.empty Reinstall
  in
  (* Basic definition of orphan packages *)
  let orphans =
    t.installed -- available
  in
  log "Base orphans: %a" (slog OpamPackage.Set.to_string) orphans;
  (* Restriction to the request-related packages *)
  let changes = match changes with
    | None -> None
    | Some ch ->
      Some
        (OpamPackage.Name.Set.fold (fun name ch ->
             try
               OpamPackage.Set.add
                 (OpamPackage.package_of_name t.installed name) ch
             with Not_found -> ch)
            (OpamPackage.names_of_packages ch)
            ch)
  in
  let orphans = match changes with
    | None -> orphans
    | Some ch ->
      if OpamPackage.Set.is_empty orphans then orphans else
      let recompile_cone =
        OpamPackage.Set.of_list @@
        OpamSolver.reverse_dependencies
          ~depopts:true ~installed:true ~unavailable:true
          ~build:true ~post:false
          universe ch
      in
      orphans %% recompile_cone
  in
  (* invalidated packages forbid changes of their reverse dependencies, while
     basic orphans do not *)
  let orphans = orphans ++ invalidated in
  (* Pinned versions of packages remain always available *)
  let orphans = orphans -- OpamPinned.packages t in
  (* Splits between full orphans (no version left) and partial ones *)
  let full_partition orphans =
    let orphan_names = (* names for which there is no available version left *)
      OpamPackage.Name.Set.diff
        allnames
        (OpamPackage.names_of_packages (available -- orphans)) in
    OpamPackage.Set.partition
      (fun nv -> OpamPackage.Name.Set.mem nv.name orphan_names)
      orphans
  in
  let full_orphans, orphan_versions = full_partition orphans in
  (* Closure *)
  let full_orphans, orphan_versions =
    if not transitive then full_orphans, orphan_versions else
    let rec add_trans full_orphans orphan_versions =
      (* fixpoint to check all packages with no available version *)
      let new_orphans =
        OpamPackage.Set.of_list @@
        OpamSolver.reverse_dependencies
          ~depopts:false ~installed:false ~unavailable:true
          ~build:true ~post:false
          universe full_orphans
      in
      let full, versions = full_partition (new_orphans++orphan_versions) in
      if OpamPackage.Set.equal full_orphans full
      then full, versions
      else add_trans full versions
    in
    add_trans full_orphans orphan_versions
  in
  (* Installed packages outside the set of changes are otherwise safe:
     re-add them to the universe *)
  let t =
    if changes = None then t else
    let available_packages = lazy (available ++ (t.installed -- orphans)) in
    { t with available_packages }
  in
  log "Orphans: (changes: %a, transitive: %b) -> full %a, versions %a"
    (slog @@ OpamStd.Option.to_string OpamPackage.Set.to_string) changes
    transitive
    (slog @@ OpamPackage.Name.Set.to_string @* OpamPackage.names_of_packages)
    full_orphans
    (slog OpamPackage.Set.to_string) orphan_versions;
  t, full_orphans, orphan_versions

(* Checks a request for [atoms] for conflicts with the orphan packages *)
let check_conflicts t atoms =
  let changes = OpamSwitchState.packages_of_atoms t atoms in
  let t, full_orphans, orphan_versions = orphans ~changes t in
  let available = Lazy.force t.available_packages in
  let available_changes = changes %% available in
  (* packages which still have local data are OK for install/reinstall if still
     "available" *)
  let full_orphans_reinstallable, full_orphans =
    OpamPackage.Set.partition (fun nv ->
        match OpamPackage.Map.find_opt nv t.opams with
        | None -> false
        | Some opam ->
          OpamFilter.eval_to_bool ~default:false
            (OpamPackageVar.resolve_switch ~package:nv t)
            (OpamFile.OPAM.available opam))
      full_orphans
  in
  let orphan_versions_reinstallable, orphan_versions =
    OpamPackage.Set.partition (fun nv ->
        not (OpamPackage.has_name available_changes nv.name) &&
        match OpamPackage.Map.find_opt nv t.opams with
        | None -> false
        | Some opam ->
          OpamFilter.eval_to_bool ~default:false
            (OpamPackageVar.resolve_switch ~package:nv t)
            (OpamFile.OPAM.available opam))
      orphan_versions
  in
  let orphans = full_orphans ++ orphan_versions in
  let conflict_atoms =
    let non_orphans = lazy (t.packages -- full_orphans -- orphan_versions) in
    List.filter
      (fun (name,_ as a) ->
         not (OpamPackage.has_name t.pinned name) &&
         OpamPackage.Set.exists (OpamFormula.check a) orphans && (*optim*)
         not (OpamPackage.Set.exists (OpamFormula.check a) (* real check *)
                (Lazy.force non_orphans)))
      atoms
  in
  if conflict_atoms <> [] then
    (* Atoms that were unavailable to begin with should be already filtered out
       at this point (by [sanitize_atom_list]) *)
    OpamConsole.error_and_exit `Not_found
      "Sorry, these packages are no longer available from the repositories: \
       %s"
      (OpamStd.Format.pretty_list
         (List.map OpamFormula.string_of_atom conflict_atoms))
  else
    {t with available_packages = lazy
              (available ++
               full_orphans_reinstallable ++
               orphan_versions_reinstallable)},
    full_orphans,
    orphan_versions

end

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
         info [] ~docv:"-- COMMAND [ARG]"
           ~doc:
           "Command to run in the current directory that is expected to \
            install the files for $(i,PACKAGE) to the current opam switch \
            prefix.")
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
       available_packages = lazy (OpamPackage.Set.add nv (Lazy.force st.available_packages));
      }
    in
    let simple_install () =
      (* when no recompilations are needed *)
      if is_installed then
        OpamProcess.Job.run @@
        OpamAction.remove_package st ~force:true @@
        OpamPackage.package_of_name st.installed nv.name;
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


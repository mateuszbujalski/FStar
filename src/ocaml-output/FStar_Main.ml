open Prims
let (uu___0 : unit) = FStar_Version.dummy () 
let (process_args :
  unit -> (FStar_Getopt.parse_cmdline_res * Prims.string Prims.list)) =
  fun uu____12  -> FStar_Options.parse_cmd_line () 
let (cleanup : unit -> unit) = fun uu____25  -> FStar_Util.kill_all () 
let (finished_message :
  (Prims.bool * FStar_Ident.lident) Prims.list -> Prims.int -> unit) =
  fun fmods  ->
    fun errs  ->
      let print_to =
        if errs > Prims.int_zero
        then FStar_Util.print_error
        else FStar_Util.print_string  in
      let uu____67 =
        let uu____69 = FStar_Options.silent ()  in Prims.op_Negation uu____69
         in
      if uu____67
      then
        (FStar_All.pipe_right fmods
           (FStar_List.iter
              (fun uu____91  ->
                 match uu____91 with
                 | (iface1,name) ->
                     let tag =
                       if iface1 then "i'face (or impl+i'face)" else "module"
                        in
                     let uu____109 =
                       let uu____111 = FStar_Ident.string_of_lid name  in
                       FStar_Options.should_print_message uu____111  in
                     if uu____109
                     then
                       let uu____114 =
                         let uu____116 = FStar_Ident.string_of_lid name  in
                         FStar_Util.format2 "Verified %s: %s\n" tag uu____116
                          in
                       print_to uu____114
                     else ()));
         if errs > Prims.int_zero
         then
           (if errs = Prims.int_one
            then FStar_Util.print_error "1 error was reported (see above)\n"
            else
              (let uu____129 = FStar_Util.string_of_int errs  in
               FStar_Util.print1_error
                 "%s errors were reported (see above)\n" uu____129))
         else
           (let uu____134 =
              FStar_Util.colorize_bold
                "All verification conditions discharged successfully"
               in
            FStar_Util.print1 "%s\n" uu____134))
      else ()
  
let (report_errors : (Prims.bool * FStar_Ident.lident) Prims.list -> unit) =
  fun fmods  ->
    (let uu____161 = FStar_Errors.report_all ()  in
     FStar_All.pipe_right uu____161 (fun a1  -> ()));
    (let nerrs = FStar_Errors.get_err_count ()  in
     if nerrs > Prims.int_zero
     then (finished_message fmods nerrs; FStar_All.exit Prims.int_one)
     else ())
  
let (load_native_tactics : unit -> unit) =
  fun uu____179  ->
    let modules_to_load =
      let uu____183 = FStar_Options.load ()  in
      FStar_All.pipe_right uu____183 (FStar_List.map FStar_Ident.lid_of_str)
       in
    let ml_module_name m =
      let uu____200 = FStar_Extraction_ML_Util.mlpath_of_lid m  in
      FStar_All.pipe_right uu____200 FStar_Extraction_ML_Util.flatten_mlpath
       in
    let ml_file m =
      let uu____225 = ml_module_name m  in Prims.op_Hat uu____225 ".ml"  in
    let cmxs_file m =
      let cmxs =
        let uu____237 = ml_module_name m  in Prims.op_Hat uu____237 ".cmxs"
         in
      let uu____240 = FStar_Options.find_file cmxs  in
      match uu____240 with
      | FStar_Pervasives_Native.Some f -> f
      | FStar_Pervasives_Native.None  ->
          let uu____249 =
            let uu____253 = ml_file m  in FStar_Options.find_file uu____253
             in
          (match uu____249 with
           | FStar_Pervasives_Native.None  ->
               let uu____257 =
                 let uu____263 =
                   let uu____265 = ml_file m  in
                   FStar_Util.format1
                     "Failed to compile native tactic; extracted module %s not found"
                     uu____265
                    in
                 (FStar_Errors.Fatal_FailToCompileNativeTactic, uu____263)
                  in
               FStar_Errors.raise_err uu____257
           | FStar_Pervasives_Native.Some ml ->
               let dir = FStar_Util.dirname ml  in
               ((let uu____276 =
                   let uu____280 = ml_module_name m  in [uu____280]  in
                 FStar_Tactics_Load.compile_modules dir uu____276);
                (let uu____284 = FStar_Options.find_file cmxs  in
                 match uu____284 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____290 =
                       let uu____296 =
                         FStar_Util.format1
                           "Failed to compile native tactic; compiled object %s not found"
                           cmxs
                          in
                       (FStar_Errors.Fatal_FailToCompileNativeTactic,
                         uu____296)
                        in
                     FStar_Errors.raise_err uu____290
                 | FStar_Pervasives_Native.Some f -> f)))
       in
    let cmxs_files =
      FStar_All.pipe_right modules_to_load (FStar_List.map cmxs_file)  in
    FStar_List.iter (fun x  -> FStar_Util.print1 "cmxs file: %s\n" x)
      cmxs_files;
    (let uu____321 =
       let uu____323 = FStar_Options.no_load_fstartaclib ()  in
       Prims.op_Negation uu____323  in
     if uu____321 then FStar_Tactics_Load.load_lib () else ());
    FStar_Tactics_Load.load_tactics cmxs_files;
    (let uu____330 = FStar_Options.use_native_tactics ()  in
     FStar_Util.iter_opt uu____330 FStar_Tactics_Load.load_tactics_dir)
  
let (fstar_files :
  Prims.string Prims.list FStar_Pervasives_Native.option FStar_ST.ref) =
  FStar_Util.mk_ref FStar_Pervasives_Native.None 
let go : 'Auu____356 . 'Auu____356 -> unit =
  fun uu____361  ->
    let uu____362 = process_args ()  in
    match uu____362 with
    | (res,filenames) ->
        (match res with
         | FStar_Getopt.Help  ->
             (FStar_Options.display_usage (); FStar_All.exit Prims.int_zero)
         | FStar_Getopt.Error msg ->
             (FStar_Util.print_error msg; FStar_All.exit Prims.int_one)
         | uu____384 when FStar_Options.print_cache_version () ->
             ((let uu____386 =
                 FStar_Util.string_of_int
                   FStar_CheckedFiles.cache_version_number
                  in
               FStar_Util.print1 "F* cache version number: %s\n" uu____386);
              FStar_All.exit Prims.int_zero)
         | FStar_Getopt.Success  ->
             (FStar_ST.op_Colon_Equals fstar_files
                (FStar_Pervasives_Native.Some filenames);
              (let uu____423 =
                 let uu____425 = FStar_Options.dep ()  in
                 uu____425 <> FStar_Pervasives_Native.None  in
               if uu____423
               then
                 let uu____434 =
                   FStar_Parser_Dep.collect filenames
                     FStar_CheckedFiles.load_parsing_data_from_cache
                    in
                 match uu____434 with
                 | (uu____442,deps) -> FStar_Parser_Dep.print deps
               else
                 (let uu____452 =
                    ((FStar_Options.use_extracted_interfaces ()) &&
                       (let uu____455 = FStar_Options.expose_interfaces ()
                           in
                        Prims.op_Negation uu____455))
                      && ((FStar_List.length filenames) > Prims.int_one)
                     in
                  if uu____452
                  then
                    let uu____460 =
                      let uu____466 =
                        let uu____468 =
                          FStar_Util.string_of_int
                            (FStar_List.length filenames)
                           in
                        Prims.op_Hat
                          "Only one command line file is allowed if --use_extracted_interfaces is set, found "
                          uu____468
                         in
                      (FStar_Errors.Error_TooManyFiles, uu____466)  in
                    FStar_Errors.raise_error uu____460 FStar_Range.dummyRange
                  else
                    (let uu____475 =
                       (FStar_Options.print ()) ||
                         (FStar_Options.print_in_place ())
                        in
                     if uu____475
                     then
                       (if FStar_Platform.is_fstar_compiler_using_ocaml
                        then
                          let printing_mode =
                            let uu____480 = FStar_Options.print ()  in
                            if uu____480
                            then FStar_Prettyprint.FromTempToStdout
                            else FStar_Prettyprint.FromTempToFile  in
                          FStar_Prettyprint.generate printing_mode filenames
                        else
                          failwith
                            "You seem to be using the F#-generated version ofthe compiler ; \\o\n                         reindenting is not known to work yet with this version")
                     else
                       (let uu____490 = FStar_Options.lsp_server ()  in
                        if uu____490
                        then FStar_Interactive_Lsp.start_server ()
                        else
                          (load_native_tactics ();
                           (let uu____496 = FStar_Options.interactive ()  in
                            if uu____496
                            then
                              match filenames with
                              | [] ->
                                  (FStar_Errors.log_issue
                                     FStar_Range.dummyRange
                                     (FStar_Errors.Error_MissingFileName,
                                       "--ide: Name of current file missing in command line invocation\n");
                                   FStar_All.exit Prims.int_one)
                              | uu____504::uu____505::uu____506 ->
                                  (FStar_Errors.log_issue
                                     FStar_Range.dummyRange
                                     (FStar_Errors.Error_TooManyFiles,
                                       "--ide: Too many files in command line invocation\n");
                                   FStar_All.exit Prims.int_one)
                              | filename::[] ->
                                  let uu____522 =
                                    FStar_Options.legacy_interactive ()  in
                                  (if uu____522
                                   then
                                     FStar_Interactive_Legacy.interactive_mode
                                       filename
                                   else
                                     FStar_Interactive_Ide.interactive_mode
                                       filename)
                            else
                              if
                                (FStar_List.length filenames) >=
                                  Prims.int_one
                              then
                                (let uu____532 =
                                   FStar_Dependencies.find_deps_if_needed
                                     filenames
                                     FStar_CheckedFiles.load_parsing_data_from_cache
                                    in
                                 match uu____532 with
                                 | (filenames1,dep_graph1) ->
                                     let uu____548 =
                                       FStar_Universal.batch_mode_tc
                                         filenames1 dep_graph1
                                        in
                                     (match uu____548 with
                                      | (tcrs,env,cleanup1) ->
                                          ((let uu____574 = cleanup1 env  in
                                            ());
                                           (let module_names =
                                              FStar_All.pipe_right tcrs
                                                (FStar_List.map
                                                   (fun tcr  ->
                                                      FStar_Universal.module_or_interface_name
                                                        tcr.FStar_CheckedFiles.checked_module))
                                               in
                                            report_errors module_names;
                                            finished_message module_names
                                              Prims.int_zero))))
                              else
                                FStar_Errors.raise_error
                                  (FStar_Errors.Error_MissingFileName,
                                    "No file provided")
                                  FStar_Range.dummyRange))))))))
  
let (lazy_chooser :
  FStar_Syntax_Syntax.lazy_kind ->
    FStar_Syntax_Syntax.lazyinfo ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun k  ->
    fun i  ->
      match k with
      | FStar_Syntax_Syntax.BadLazy  ->
          failwith "lazy chooser: got a BadLazy"
      | FStar_Syntax_Syntax.Lazy_bv  ->
          FStar_Reflection_Embeddings.unfold_lazy_bv i
      | FStar_Syntax_Syntax.Lazy_binder  ->
          FStar_Reflection_Embeddings.unfold_lazy_binder i
      | FStar_Syntax_Syntax.Lazy_optionstate  ->
          FStar_Reflection_Embeddings.unfold_lazy_optionstate i
      | FStar_Syntax_Syntax.Lazy_fvar  ->
          FStar_Reflection_Embeddings.unfold_lazy_fvar i
      | FStar_Syntax_Syntax.Lazy_comp  ->
          FStar_Reflection_Embeddings.unfold_lazy_comp i
      | FStar_Syntax_Syntax.Lazy_env  ->
          FStar_Reflection_Embeddings.unfold_lazy_env i
      | FStar_Syntax_Syntax.Lazy_sigelt  ->
          FStar_Reflection_Embeddings.unfold_lazy_sigelt i
      | FStar_Syntax_Syntax.Lazy_proofstate  ->
          FStar_Tactics_Embedding.unfold_lazy_proofstate i
      | FStar_Syntax_Syntax.Lazy_goal  ->
          FStar_Tactics_Embedding.unfold_lazy_goal i
      | FStar_Syntax_Syntax.Lazy_uvar  ->
          FStar_Syntax_Util.exp_string "((uvar))"
      | FStar_Syntax_Syntax.Lazy_embedding (uu____624,t) ->
          FStar_Thunk.force t
  
let (setup_hooks : unit -> unit) =
  fun uu____641  ->
    FStar_Options.initialize_parse_warn_error
      FStar_Parser_ParseIt.parse_warn_error;
    FStar_ST.op_Colon_Equals FStar_Syntax_Syntax.lazy_chooser
      (FStar_Pervasives_Native.Some lazy_chooser);
    FStar_ST.op_Colon_Equals FStar_Syntax_Util.tts_f
      (FStar_Pervasives_Native.Some FStar_Syntax_Print.term_to_string);
    FStar_ST.op_Colon_Equals FStar_TypeChecker_Normalize.unembed_binder_knot
      (FStar_Pervasives_Native.Some FStar_Reflection_Embeddings.e_binder);
    FStar_ST.op_Colon_Equals FStar_TypeChecker_Tc.unembed_optionstate_knot
      (FStar_Pervasives_Native.Some FStar_Reflection_Embeddings.e_optionstate)
  
let (handle_error : Prims.exn -> unit) =
  fun e  ->
    if FStar_Errors.handleable e then FStar_Errors.err_exn e else ();
    (let uu____792 = FStar_Options.trace_error ()  in
     if uu____792
     then
       let uu____795 = FStar_Util.message_of_exn e  in
       let uu____797 = FStar_Util.trace_of_exn e  in
       FStar_Util.print2_error "Unexpected error\n%s\n%s\n" uu____795
         uu____797
     else
       if Prims.op_Negation (FStar_Errors.handleable e)
       then
         (let uu____803 = FStar_Util.message_of_exn e  in
          FStar_Util.print1_error
            "Unexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error.\n%s\n"
            uu____803)
       else ());
    cleanup ();
    report_errors []
  
let main : 'Auu____819 . unit -> 'Auu____819 =
  fun uu____824  ->
    try
      (fun uu___129_832  ->
         match () with
         | () ->
             (setup_hooks ();
              (let uu____834 = FStar_Util.record_time go  in
               match uu____834 with
               | (uu____840,time) ->
                   ((let uu____845 = FStar_Options.query_stats ()  in
                     if uu____845
                     then
                       let uu____848 = FStar_Util.string_of_int time  in
                       let uu____850 =
                         let uu____852 = FStar_Getopt.cmdline ()  in
                         FStar_String.concat " " uu____852  in
                       FStar_Util.print2_error "TOTAL TIME %s ms: %s\n"
                         uu____848 uu____850
                     else ());
                    cleanup ();
                    FStar_All.exit Prims.int_zero)))) ()
    with
    | uu___128_864 ->
        (handle_error uu___128_864; FStar_All.exit Prims.int_one)
  
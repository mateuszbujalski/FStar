open Prims
type env_t = FStar_Extraction_ML_UEnv.uenv
let (fail_exp :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun lid  ->
    fun t  ->
      let uu____25 =
        let uu____32 =
          let uu____33 =
            let uu____50 =
              FStar_Syntax_Syntax.fvar FStar_Parser_Const.failwith_lid
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            let uu____53 =
              let uu____64 = FStar_Syntax_Syntax.iarg t  in
              let uu____73 =
                let uu____84 =
                  let uu____93 =
                    let uu____94 =
                      let uu____101 =
                        let uu____102 =
                          let uu____103 =
                            let uu____109 =
                              let uu____111 =
                                FStar_Syntax_Print.lid_to_string lid  in
                              Prims.op_Hat "Not yet implemented:" uu____111
                               in
                            (uu____109, FStar_Range.dummyRange)  in
                          FStar_Const.Const_string uu____103  in
                        FStar_Syntax_Syntax.Tm_constant uu____102  in
                      FStar_Syntax_Syntax.mk uu____101  in
                    uu____94 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange
                     in
                  FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____93  in
                [uu____84]  in
              uu____64 :: uu____73  in
            (uu____50, uu____53)  in
          FStar_Syntax_Syntax.Tm_app uu____33  in
        FStar_Syntax_Syntax.mk uu____32  in
      uu____25 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (always_fail :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.letbinding)
  =
  fun lid  ->
    fun t  ->
      let imp =
        let uu____177 = FStar_Syntax_Util.arrow_formals t  in
        match uu____177 with
        | ([],t1) ->
            let b =
              let uu____204 =
                FStar_Syntax_Syntax.gen_bv "_" FStar_Pervasives_Native.None
                  t1
                 in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____204  in
            let uu____212 = fail_exp lid t1  in
            FStar_Syntax_Util.abs [b] uu____212 FStar_Pervasives_Native.None
        | (bs,t1) ->
            let uu____233 = fail_exp lid t1  in
            FStar_Syntax_Util.abs bs uu____233 FStar_Pervasives_Native.None
         in
      let lb =
        let uu____237 =
          let uu____242 =
            FStar_Syntax_Syntax.lid_as_fv lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Util.Inr uu____242  in
        {
          FStar_Syntax_Syntax.lbname = uu____237;
          FStar_Syntax_Syntax.lbunivs = [];
          FStar_Syntax_Syntax.lbtyp = t;
          FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_ML_lid;
          FStar_Syntax_Syntax.lbdef = imp;
          FStar_Syntax_Syntax.lbattrs = [];
          FStar_Syntax_Syntax.lbpos = (imp.FStar_Syntax_Syntax.pos)
        }  in
      lb
  
let (mangle_projector_lid : FStar_Ident.lident -> FStar_Ident.lident) =
  fun x  -> x 
let (lident_as_mlsymbol :
  FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlsymbol) =
  fun id1  ->
    let uu____259 =
      let uu____261 = FStar_Ident.ident_of_lid id1  in
      FStar_Ident.text_of_id uu____261  in
    FStar_Extraction_ML_Syntax.avoid_keyword uu____259
  
let as_pair :
  'Auu____267 . 'Auu____267 Prims.list -> ('Auu____267 * 'Auu____267) =
  fun uu___0_278  ->
    match uu___0_278 with
    | a::b::[] -> (a, b)
    | uu____283 -> failwith "Expected a list with 2 elements"
  
let (flag_of_qual :
  FStar_Syntax_Syntax.qualifier ->
    FStar_Extraction_ML_Syntax.meta FStar_Pervasives_Native.option)
  =
  fun uu___1_298  ->
    match uu___1_298 with
    | FStar_Syntax_Syntax.Assumption  ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Assumed
    | FStar_Syntax_Syntax.Private  ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Private
    | FStar_Syntax_Syntax.NoExtract  ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.NoExtract
    | uu____301 -> FStar_Pervasives_Native.None
  
let rec (extract_meta :
  FStar_Syntax_Syntax.term ->
    FStar_Extraction_ML_Syntax.meta FStar_Pervasives_Native.option)
  =
  fun x  ->
    let uu____310 = FStar_Syntax_Subst.compress x  in
    match uu____310 with
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
        FStar_Syntax_Syntax.pos = uu____314;
        FStar_Syntax_Syntax.vars = uu____315;_} ->
        let uu____318 =
          let uu____320 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____320  in
        (match uu____318 with
         | "FStar.Pervasives.PpxDerivingShow" ->
             FStar_Pervasives_Native.Some
               FStar_Extraction_ML_Syntax.PpxDerivingShow
         | "FStar.Pervasives.PpxDerivingYoJson" ->
             FStar_Pervasives_Native.Some
               FStar_Extraction_ML_Syntax.PpxDerivingYoJson
         | "FStar.Pervasives.CInline" ->
             FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.CInline
         | "FStar.Pervasives.Substitute" ->
             FStar_Pervasives_Native.Some
               FStar_Extraction_ML_Syntax.Substitute
         | "FStar.Pervasives.Gc" ->
             FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.GCType
         | "FStar.Pervasives.CAbstractStruct" ->
             FStar_Pervasives_Native.Some
               FStar_Extraction_ML_Syntax.CAbstract
         | "FStar.Pervasives.CIfDef" ->
             FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.CIfDef
         | "FStar.Pervasives.CMacro" ->
             FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.CMacro
         | "Prims.deprecated" ->
             FStar_Pervasives_Native.Some
               (FStar_Extraction_ML_Syntax.Deprecated "")
         | uu____333 -> FStar_Pervasives_Native.None)
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____336;
             FStar_Syntax_Syntax.vars = uu____337;_},({
                                                        FStar_Syntax_Syntax.n
                                                          =
                                                          FStar_Syntax_Syntax.Tm_constant
                                                          (FStar_Const.Const_string
                                                          (s,uu____339));
                                                        FStar_Syntax_Syntax.pos
                                                          = uu____340;
                                                        FStar_Syntax_Syntax.vars
                                                          = uu____341;_},uu____342)::[]);
        FStar_Syntax_Syntax.pos = uu____343;
        FStar_Syntax_Syntax.vars = uu____344;_} ->
        let uu____387 =
          let uu____389 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____389  in
        (match uu____387 with
         | "FStar.Pervasives.PpxDerivingShowConstant" ->
             FStar_Pervasives_Native.Some
               (FStar_Extraction_ML_Syntax.PpxDerivingShowConstant s)
         | "FStar.Pervasives.Comment" ->
             FStar_Pervasives_Native.Some
               (FStar_Extraction_ML_Syntax.Comment s)
         | "FStar.Pervasives.CPrologue" ->
             FStar_Pervasives_Native.Some
               (FStar_Extraction_ML_Syntax.CPrologue s)
         | "FStar.Pervasives.CEpilogue" ->
             FStar_Pervasives_Native.Some
               (FStar_Extraction_ML_Syntax.CEpilogue s)
         | "FStar.Pervasives.CConst" ->
             FStar_Pervasives_Native.Some
               (FStar_Extraction_ML_Syntax.CConst s)
         | "FStar.Pervasives.CCConv" ->
             FStar_Pervasives_Native.Some
               (FStar_Extraction_ML_Syntax.CCConv s)
         | "Prims.deprecated" ->
             FStar_Pervasives_Native.Some
               (FStar_Extraction_ML_Syntax.Deprecated s)
         | uu____399 -> FStar_Pervasives_Native.None)
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("KremlinPrivate",uu____401));
        FStar_Syntax_Syntax.pos = uu____402;
        FStar_Syntax_Syntax.vars = uu____403;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Private
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("c_inline",uu____408));
        FStar_Syntax_Syntax.pos = uu____409;
        FStar_Syntax_Syntax.vars = uu____410;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.CInline
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("substitute",uu____415));
        FStar_Syntax_Syntax.pos = uu____416;
        FStar_Syntax_Syntax.vars = uu____417;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Substitute
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_meta (x1,uu____423);
        FStar_Syntax_Syntax.pos = uu____424;
        FStar_Syntax_Syntax.vars = uu____425;_} -> extract_meta x1
    | uu____432 -> FStar_Pervasives_Native.None
  
let (extract_metadata :
  FStar_Syntax_Syntax.term Prims.list ->
    FStar_Extraction_ML_Syntax.meta Prims.list)
  = fun metas  -> FStar_List.choose extract_meta metas 
let binders_as_mlty_binders :
  'Auu____452 .
    FStar_Extraction_ML_UEnv.uenv ->
      (FStar_Syntax_Syntax.bv * 'Auu____452) Prims.list ->
        (FStar_Extraction_ML_UEnv.uenv * Prims.string Prims.list)
  =
  fun env  ->
    fun bs  ->
      FStar_Util.fold_map
        (fun env1  ->
           fun uu____494  ->
             match uu____494 with
             | (bv,uu____505) ->
                 let uu____506 =
                   let uu____507 =
                     let uu____510 =
                       let uu____511 =
                         FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv  in
                       FStar_Extraction_ML_Syntax.MLTY_Var uu____511  in
                     FStar_Pervasives_Native.Some uu____510  in
                   FStar_Extraction_ML_UEnv.extend_ty env1 bv uu____507  in
                 let uu____513 = FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv
                    in
                 (uu____506, uu____513)) env bs
  
type data_constructor =
  {
  dname: FStar_Ident.lident ;
  dtyp: FStar_Syntax_Syntax.typ }
let (__proj__Mkdata_constructor__item__dname :
  data_constructor -> FStar_Ident.lident) =
  fun projectee  -> match projectee with | { dname; dtyp;_} -> dname 
let (__proj__Mkdata_constructor__item__dtyp :
  data_constructor -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | { dname; dtyp;_} -> dtyp 
type inductive_family =
  {
  ifv: FStar_Syntax_Syntax.fv ;
  iname: FStar_Ident.lident ;
  iparams: FStar_Syntax_Syntax.binders ;
  ityp: FStar_Syntax_Syntax.term ;
  idatas: data_constructor Prims.list ;
  iquals: FStar_Syntax_Syntax.qualifier Prims.list ;
  imetadata: FStar_Extraction_ML_Syntax.metadata }
let (__proj__Mkinductive_family__item__ifv :
  inductive_family -> FStar_Syntax_Syntax.fv) =
  fun projectee  ->
    match projectee with
    | { ifv; iname; iparams; ityp; idatas; iquals; imetadata;_} -> ifv
  
let (__proj__Mkinductive_family__item__iname :
  inductive_family -> FStar_Ident.lident) =
  fun projectee  ->
    match projectee with
    | { ifv; iname; iparams; ityp; idatas; iquals; imetadata;_} -> iname
  
let (__proj__Mkinductive_family__item__iparams :
  inductive_family -> FStar_Syntax_Syntax.binders) =
  fun projectee  ->
    match projectee with
    | { ifv; iname; iparams; ityp; idatas; iquals; imetadata;_} -> iparams
  
let (__proj__Mkinductive_family__item__ityp :
  inductive_family -> FStar_Syntax_Syntax.term) =
  fun projectee  ->
    match projectee with
    | { ifv; iname; iparams; ityp; idatas; iquals; imetadata;_} -> ityp
  
let (__proj__Mkinductive_family__item__idatas :
  inductive_family -> data_constructor Prims.list) =
  fun projectee  ->
    match projectee with
    | { ifv; iname; iparams; ityp; idatas; iquals; imetadata;_} -> idatas
  
let (__proj__Mkinductive_family__item__iquals :
  inductive_family -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun projectee  ->
    match projectee with
    | { ifv; iname; iparams; ityp; idatas; iquals; imetadata;_} -> iquals
  
let (__proj__Mkinductive_family__item__imetadata :
  inductive_family -> FStar_Extraction_ML_Syntax.metadata) =
  fun projectee  ->
    match projectee with
    | { ifv; iname; iparams; ityp; idatas; iquals; imetadata;_} -> imetadata
  
let (print_ifamily : inductive_family -> unit) =
  fun i  ->
    let uu____714 = FStar_Syntax_Print.lid_to_string i.iname  in
    let uu____716 = FStar_Syntax_Print.binders_to_string " " i.iparams  in
    let uu____719 = FStar_Syntax_Print.term_to_string i.ityp  in
    let uu____721 =
      let uu____723 =
        FStar_All.pipe_right i.idatas
          (FStar_List.map
             (fun d  ->
                let uu____737 = FStar_Syntax_Print.lid_to_string d.dname  in
                let uu____739 =
                  let uu____741 = FStar_Syntax_Print.term_to_string d.dtyp
                     in
                  Prims.op_Hat " : " uu____741  in
                Prims.op_Hat uu____737 uu____739))
         in
      FStar_All.pipe_right uu____723 (FStar_String.concat "\n\t\t")  in
    FStar_Util.print4 "\n\t%s %s : %s { %s }\n" uu____714 uu____716 uu____719
      uu____721
  
let (bundle_as_inductive_families :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_Extraction_ML_UEnv.uenv * inductive_family Prims.list))
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        let uu____786 =
          FStar_Util.fold_map
            (fun env1  ->
               fun se  ->
                 match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_inductive_typ
                     (l,us,bs,t,_mut_i,datas) ->
                     let uu____837 = FStar_Syntax_Subst.open_univ_vars us t
                        in
                     (match uu____837 with
                      | (_us,t1) ->
                          let uu____850 = FStar_Syntax_Subst.open_term bs t1
                             in
                          (match uu____850 with
                           | (bs1,t2) ->
                               let datas1 =
                                 FStar_All.pipe_right ses
                                   (FStar_List.collect
                                      (fun se1  ->
                                         match se1.FStar_Syntax_Syntax.sigel
                                         with
                                         | FStar_Syntax_Syntax.Sig_datacon
                                             (d,us1,t3,l',nparams,uu____896)
                                             when FStar_Ident.lid_equals l l'
                                             ->
                                             let uu____903 =
                                               FStar_Syntax_Subst.open_univ_vars
                                                 us1 t3
                                                in
                                             (match uu____903 with
                                              | (_us1,t4) ->
                                                  let uu____912 =
                                                    FStar_Syntax_Util.arrow_formals
                                                      t4
                                                     in
                                                  (match uu____912 with
                                                   | (bs',body) ->
                                                       let uu____927 =
                                                         FStar_Util.first_N
                                                           (FStar_List.length
                                                              bs1) bs'
                                                          in
                                                       (match uu____927 with
                                                        | (bs_params,rest) ->
                                                            let subst1 =
                                                              FStar_List.map2
                                                                (fun
                                                                   uu____1018
                                                                    ->
                                                                   fun
                                                                    uu____1019
                                                                     ->
                                                                    match 
                                                                    (uu____1018,
                                                                    uu____1019)
                                                                    with
                                                                    | 
                                                                    ((b',uu____1045),
                                                                    (b,uu____1047))
                                                                    ->
                                                                    let uu____1068
                                                                    =
                                                                    let uu____1075
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    b  in
                                                                    (b',
                                                                    uu____1075)
                                                                     in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____1068)
                                                                bs_params bs1
                                                               in
                                                            let t5 =
                                                              let uu____1081
                                                                =
                                                                let uu____1082
                                                                  =
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    body
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  rest
                                                                  uu____1082
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____1081
                                                                (FStar_Syntax_Subst.subst
                                                                   subst1)
                                                               in
                                                            [{
                                                               dname = d;
                                                               dtyp = t5
                                                             }])))
                                         | uu____1085 -> []))
                                  in
                               let metadata =
                                 let uu____1089 =
                                   extract_metadata
                                     se.FStar_Syntax_Syntax.sigattrs
                                    in
                                 let uu____1092 =
                                   FStar_List.choose flag_of_qual quals  in
                                 FStar_List.append uu____1089 uu____1092  in
                               let fv =
                                 FStar_Syntax_Syntax.lid_as_fv l
                                   FStar_Syntax_Syntax.delta_constant
                                   FStar_Pervasives_Native.None
                                  in
                               let env2 =
                                 FStar_Extraction_ML_UEnv.extend_type_name
                                   env1 fv
                                  in
                               (env2,
                                 [{
                                    ifv = fv;
                                    iname = l;
                                    iparams = bs1;
                                    ityp = t2;
                                    idatas = datas1;
                                    iquals =
                                      (se.FStar_Syntax_Syntax.sigquals);
                                    imetadata = metadata
                                  }])))
                 | uu____1099 -> (env1, [])) env ses
           in
        match uu____786 with
        | (env1,ifams) -> (env1, (FStar_List.flatten ifams))
  
type iface =
  {
  iface_module_name: FStar_Extraction_ML_Syntax.mlpath ;
  iface_bindings:
    (FStar_Syntax_Syntax.fv * FStar_Extraction_ML_UEnv.exp_binding)
      Prims.list
    ;
  iface_tydefs: FStar_Extraction_ML_UEnv.tydef Prims.list ;
  iface_type_names: FStar_Syntax_Syntax.fv Prims.list }
let (__proj__Mkiface__item__iface_module_name :
  iface -> FStar_Extraction_ML_Syntax.mlpath) =
  fun projectee  ->
    match projectee with
    | { iface_module_name; iface_bindings; iface_tydefs; iface_type_names;_}
        -> iface_module_name
  
let (__proj__Mkiface__item__iface_bindings :
  iface ->
    (FStar_Syntax_Syntax.fv * FStar_Extraction_ML_UEnv.exp_binding)
      Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { iface_module_name; iface_bindings; iface_tydefs; iface_type_names;_}
        -> iface_bindings
  
let (__proj__Mkiface__item__iface_tydefs :
  iface -> FStar_Extraction_ML_UEnv.tydef Prims.list) =
  fun projectee  ->
    match projectee with
    | { iface_module_name; iface_bindings; iface_tydefs; iface_type_names;_}
        -> iface_tydefs
  
let (__proj__Mkiface__item__iface_type_names :
  iface -> FStar_Syntax_Syntax.fv Prims.list) =
  fun projectee  ->
    match projectee with
    | { iface_module_name; iface_bindings; iface_tydefs; iface_type_names;_}
        -> iface_type_names
  
let (empty_iface : iface) =
  {
    iface_module_name = ([], "");
    iface_bindings = [];
    iface_tydefs = [];
    iface_type_names = []
  } 
let (iface_of_bindings :
  (FStar_Syntax_Syntax.fv * FStar_Extraction_ML_UEnv.exp_binding) Prims.list
    -> iface)
  =
  fun fvs  ->
    let uu___216_1279 = empty_iface  in
    {
      iface_module_name = (uu___216_1279.iface_module_name);
      iface_bindings = fvs;
      iface_tydefs = (uu___216_1279.iface_tydefs);
      iface_type_names = (uu___216_1279.iface_type_names)
    }
  
let (iface_of_tydefs : FStar_Extraction_ML_UEnv.tydef Prims.list -> iface) =
  fun tds  ->
    let uu___219_1290 = empty_iface  in
    let uu____1291 =
      FStar_List.map (fun td  -> td.FStar_Extraction_ML_UEnv.tydef_fv) tds
       in
    {
      iface_module_name = (uu___219_1290.iface_module_name);
      iface_bindings = (uu___219_1290.iface_bindings);
      iface_tydefs = tds;
      iface_type_names = uu____1291
    }
  
let (iface_of_type_names : FStar_Syntax_Syntax.fv Prims.list -> iface) =
  fun fvs  ->
    let uu___223_1306 = empty_iface  in
    {
      iface_module_name = (uu___223_1306.iface_module_name);
      iface_bindings = (uu___223_1306.iface_bindings);
      iface_tydefs = (uu___223_1306.iface_tydefs);
      iface_type_names = fvs
    }
  
let (iface_union : iface -> iface -> iface) =
  fun if1  ->
    fun if2  ->
      let uu____1318 =
        if if1.iface_module_name <> if1.iface_module_name
        then failwith "Union not defined"
        else if1.iface_module_name  in
      {
        iface_module_name = uu____1318;
        iface_bindings =
          (FStar_List.append if1.iface_bindings if2.iface_bindings);
        iface_tydefs = (FStar_List.append if1.iface_tydefs if2.iface_tydefs);
        iface_type_names =
          (FStar_List.append if1.iface_type_names if2.iface_type_names)
      }
  
let (iface_union_l : iface Prims.list -> iface) =
  fun ifs  -> FStar_List.fold_right iface_union ifs empty_iface 
let (mlpath_to_string : FStar_Extraction_ML_Syntax.mlpath -> Prims.string) =
  fun p  ->
    FStar_String.concat ". "
      (FStar_List.append (FStar_Pervasives_Native.fst p)
         [FStar_Pervasives_Native.snd p])
  
let tscheme_to_string :
  'Auu____1363 .
    FStar_Extraction_ML_Syntax.mlpath ->
      ('Auu____1363 * FStar_Extraction_ML_Syntax.mlty) -> Prims.string
  =
  fun cm  ->
    fun ts  ->
      FStar_Extraction_ML_Code.string_of_mlty cm
        (FStar_Pervasives_Native.snd ts)
  
let (print_exp_binding :
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_UEnv.exp_binding -> Prims.string)
  =
  fun cm  ->
    fun e  ->
      let uu____1395 =
        FStar_Extraction_ML_Code.string_of_mlexpr cm
          e.FStar_Extraction_ML_UEnv.exp_b_expr
         in
      let uu____1397 =
        tscheme_to_string cm e.FStar_Extraction_ML_UEnv.exp_b_tscheme  in
      let uu____1399 =
        FStar_Util.string_of_bool e.FStar_Extraction_ML_UEnv.exp_b_inst_ok
         in
      FStar_Util.format4
        "{\n\texp_b_name = %s\n\texp_b_expr = %s\n\texp_b_tscheme = %s\n\texp_b_is_rec = %s }"
        e.FStar_Extraction_ML_UEnv.exp_b_name uu____1395 uu____1397
        uu____1399
  
let (print_binding :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Syntax_Syntax.fv * FStar_Extraction_ML_UEnv.exp_binding) ->
      Prims.string)
  =
  fun cm  ->
    fun uu____1417  ->
      match uu____1417 with
      | (fv,exp_binding) ->
          let uu____1425 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____1427 = print_exp_binding cm exp_binding  in
          FStar_Util.format2 "(%s, %s)" uu____1425 uu____1427
  
let (print_tydef :
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_UEnv.tydef -> Prims.string)
  =
  fun cm  ->
    fun tydef  ->
      let uu____1442 =
        FStar_Syntax_Print.fv_to_string
          tydef.FStar_Extraction_ML_UEnv.tydef_fv
         in
      let uu____1444 =
        tscheme_to_string cm tydef.FStar_Extraction_ML_UEnv.tydef_def  in
      FStar_Util.format2 "(%s, %s)" uu____1442 uu____1444
  
let (iface_to_string : iface -> Prims.string) =
  fun iface1  ->
    let cm = iface1.iface_module_name  in
    let print_type_name tn = FStar_Syntax_Print.fv_to_string tn  in
    let uu____1462 =
      let uu____1464 =
        FStar_List.map (print_binding cm) iface1.iface_bindings  in
      FStar_All.pipe_right uu____1464 (FStar_String.concat "\n")  in
    let uu____1478 =
      let uu____1480 = FStar_List.map (print_tydef cm) iface1.iface_tydefs
         in
      FStar_All.pipe_right uu____1480 (FStar_String.concat "\n")  in
    let uu____1490 =
      let uu____1492 = FStar_List.map print_type_name iface1.iface_type_names
         in
      FStar_All.pipe_right uu____1492 (FStar_String.concat "\n")  in
    FStar_Util.format4
      "Interface %s = {\niface_bindings=\n%s;\n\niface_tydefs=\n%s;\n\niface_type_names=%s;\n}"
      (mlpath_to_string iface1.iface_module_name) uu____1462 uu____1478
      uu____1490
  
let (gamma_to_string : FStar_Extraction_ML_UEnv.uenv -> Prims.string) =
  fun env  ->
    let cm = env.FStar_Extraction_ML_UEnv.currentModule  in
    let gamma =
      FStar_List.collect
        (fun uu___2_1525  ->
           match uu___2_1525 with
           | FStar_Extraction_ML_UEnv.Fv (b,e) -> [(b, e)]
           | uu____1542 -> []) env.FStar_Extraction_ML_UEnv.env_bindings
       in
    let uu____1547 =
      let uu____1549 = FStar_List.map (print_binding cm) gamma  in
      FStar_All.pipe_right uu____1549 (FStar_String.concat "\n")  in
    FStar_Util.format1 "Gamma = {\n %s }" uu____1547
  
let (extract_typ_abbrev :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Syntax_Syntax.term Prims.list ->
        FStar_Syntax_Syntax.letbinding ->
          (env_t * iface * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list))
  =
  fun env  ->
    fun quals  ->
      fun attrs  ->
        fun lb  ->
          let uu____1609 =
            let uu____1618 =
              FStar_TypeChecker_Env.open_universes_in
                env.FStar_Extraction_ML_UEnv.env_tcenv
                lb.FStar_Syntax_Syntax.lbunivs
                [lb.FStar_Syntax_Syntax.lbdef; lb.FStar_Syntax_Syntax.lbtyp]
               in
            match uu____1618 with
            | (tcenv,uu____1636,def_typ) ->
                let uu____1642 = as_pair def_typ  in (tcenv, uu____1642)
             in
          match uu____1609 with
          | (tcenv,(lbdef,lbtyp)) ->
              let lbtyp1 =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.UnfoldUntil
                    FStar_Syntax_Syntax.delta_constant] tcenv lbtyp
                 in
              let lbdef1 =
                FStar_TypeChecker_Normalize.eta_expand_with_type tcenv lbdef
                  lbtyp1
                 in
              let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
              let lid =
                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
              let def =
                let uu____1673 =
                  let uu____1674 = FStar_Syntax_Subst.compress lbdef1  in
                  FStar_All.pipe_right uu____1674 FStar_Syntax_Util.unmeta
                   in
                FStar_All.pipe_right uu____1673 FStar_Syntax_Util.un_uinst
                 in
              let def1 =
                match def.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_abs uu____1682 ->
                    FStar_Extraction_ML_Term.normalize_abs def
                | uu____1701 -> def  in
              let uu____1702 =
                match def1.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____1713) ->
                    FStar_Syntax_Subst.open_term bs body
                | uu____1738 -> ([], def1)  in
              (match uu____1702 with
               | (bs,body) ->
                   let assumed =
                     FStar_Util.for_some
                       (fun uu___3_1758  ->
                          match uu___3_1758 with
                          | FStar_Syntax_Syntax.Assumption  -> true
                          | uu____1761 -> false) quals
                      in
                   let uu____1763 = binders_as_mlty_binders env bs  in
                   (match uu____1763 with
                    | (env1,ml_bs) ->
                        let body1 =
                          let uu____1790 =
                            FStar_Extraction_ML_Term.term_as_mlty env1 body
                             in
                          FStar_All.pipe_right uu____1790
                            (FStar_Extraction_ML_Util.eraseTypeDeep
                               (FStar_Extraction_ML_Util.udelta_unfold env1))
                           in
                        let mangled_projector =
                          let uu____1795 =
                            FStar_All.pipe_right quals
                              (FStar_Util.for_some
                                 (fun uu___4_1802  ->
                                    match uu___4_1802 with
                                    | FStar_Syntax_Syntax.Projector
                                        uu____1804 -> true
                                    | uu____1810 -> false))
                             in
                          if uu____1795
                          then
                            let mname = mangle_projector_lid lid  in
                            let uu____1817 =
                              let uu____1819 = FStar_Ident.ident_of_lid mname
                                 in
                              FStar_Ident.text_of_id uu____1819  in
                            FStar_Pervasives_Native.Some uu____1817
                          else FStar_Pervasives_Native.None  in
                        let metadata =
                          let uu____1827 = extract_metadata attrs  in
                          let uu____1830 =
                            FStar_List.choose flag_of_qual quals  in
                          FStar_List.append uu____1827 uu____1830  in
                        let td =
                          let uu____1853 = lident_as_mlsymbol lid  in
                          (assumed, uu____1853, mangled_projector, ml_bs,
                            metadata,
                            (FStar_Pervasives_Native.Some
                               (FStar_Extraction_ML_Syntax.MLTD_Abbrev body1)))
                           in
                        let def2 =
                          let uu____1865 =
                            let uu____1866 =
                              let uu____1867 = FStar_Ident.range_of_lid lid
                                 in
                              FStar_Extraction_ML_Util.mlloc_of_range
                                uu____1867
                               in
                            FStar_Extraction_ML_Syntax.MLM_Loc uu____1866  in
                          [uu____1865;
                          FStar_Extraction_ML_Syntax.MLM_Ty [td]]  in
                        let uu____1868 =
                          let uu____1873 =
                            FStar_All.pipe_right quals
                              (FStar_Util.for_some
                                 (fun uu___5_1879  ->
                                    match uu___5_1879 with
                                    | FStar_Syntax_Syntax.Assumption  -> true
                                    | FStar_Syntax_Syntax.New  -> true
                                    | uu____1883 -> false))
                             in
                          if uu____1873
                          then
                            let uu____1890 =
                              FStar_Extraction_ML_UEnv.extend_type_name env
                                fv
                               in
                            (uu____1890, (iface_of_type_names [fv]))
                          else
                            (let uu____1893 =
                               FStar_Extraction_ML_UEnv.extend_tydef env fv
                                 td
                                in
                             match uu____1893 with
                             | (env2,tydef) ->
                                 let uu____1904 = iface_of_tydefs [tydef]  in
                                 (env2, uu____1904))
                           in
                        (match uu____1868 with
                         | (env2,iface1) -> (env2, iface1, def2))))
  
let (extract_let_rec_type :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Syntax_Syntax.term Prims.list ->
        FStar_Syntax_Syntax.letbinding ->
          (env_t * iface * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list))
  =
  fun env  ->
    fun quals  ->
      fun attrs  ->
        fun lb  ->
          let lbtyp =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Env.Beta;
              FStar_TypeChecker_Env.AllowUnboundUniverses;
              FStar_TypeChecker_Env.EraseUniverses;
              FStar_TypeChecker_Env.UnfoldUntil
                FStar_Syntax_Syntax.delta_constant]
              env.FStar_Extraction_ML_UEnv.env_tcenv
              lb.FStar_Syntax_Syntax.lbtyp
             in
          let uu____1963 = FStar_Syntax_Util.arrow_formals lbtyp  in
          match uu____1963 with
          | (bs,uu____1979) ->
              let uu____1984 = binders_as_mlty_binders env bs  in
              (match uu____1984 with
               | (env1,ml_bs) ->
                   let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                      in
                   let lid =
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   let body = FStar_Extraction_ML_Syntax.MLTY_Top  in
                   let metadata =
                     let uu____2016 = extract_metadata attrs  in
                     let uu____2019 = FStar_List.choose flag_of_qual quals
                        in
                     FStar_List.append uu____2016 uu____2019  in
                   let assumed = false  in
                   let td =
                     let uu____2045 = lident_as_mlsymbol lid  in
                     (assumed, uu____2045, FStar_Pervasives_Native.None,
                       ml_bs, metadata,
                       (FStar_Pervasives_Native.Some
                          (FStar_Extraction_ML_Syntax.MLTD_Abbrev body)))
                      in
                   let def =
                     let uu____2058 =
                       let uu____2059 =
                         let uu____2060 = FStar_Ident.range_of_lid lid  in
                         FStar_Extraction_ML_Util.mlloc_of_range uu____2060
                          in
                       FStar_Extraction_ML_Syntax.MLM_Loc uu____2059  in
                     [uu____2058; FStar_Extraction_ML_Syntax.MLM_Ty [td]]  in
                   let uu____2061 =
                     FStar_Extraction_ML_UEnv.extend_tydef env fv td  in
                   (match uu____2061 with
                    | (env2,tydef) ->
                        let iface1 = iface_of_tydefs [tydef]  in
                        (env2, iface1, def)))
  
let (extract_bundle_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.sigelt -> (env_t * iface))
  =
  fun env  ->
    fun se  ->
      let extract_ctor env_iparams ml_tyvars env1 ctor =
        let mlt =
          let uu____2142 =
            FStar_Extraction_ML_Term.term_as_mlty env_iparams ctor.dtyp  in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env_iparams) uu____2142
           in
        let tys = (ml_tyvars, mlt)  in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp  in
        let uu____2149 =
          FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false  in
        match uu____2149 with | (env2,uu____2168,b) -> (env2, (fvv, b))  in
      let extract_one_family env1 ind =
        let uu____2207 = binders_as_mlty_binders env1 ind.iparams  in
        match uu____2207 with
        | (env_iparams,vars) ->
            let uu____2235 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor env_iparams vars) env1)
               in
            (match uu____2235 with | (env2,ctors) -> (env2, ctors))
         in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____2299,t,uu____2301,uu____2302,uu____2303);
            FStar_Syntax_Syntax.sigrng = uu____2304;
            FStar_Syntax_Syntax.sigquals = uu____2305;
            FStar_Syntax_Syntax.sigmeta = uu____2306;
            FStar_Syntax_Syntax.sigattrs = uu____2307;
            FStar_Syntax_Syntax.sigopts = uu____2308;_}::[],uu____2309),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____2330 = extract_ctor env [] env { dname = l; dtyp = t }
             in
          (match uu____2330 with
           | (env1,ctor) -> (env1, (iface_of_bindings [ctor])))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____2363),quals) ->
          let uu____2377 =
            FStar_Syntax_Util.has_attribute se.FStar_Syntax_Syntax.sigattrs
              FStar_Parser_Const.erasable_attr
             in
          if uu____2377
          then (env, empty_iface)
          else
            (let uu____2386 = bundle_as_inductive_families env ses quals  in
             match uu____2386 with
             | (env1,ifams) ->
                 let uu____2403 =
                   FStar_Util.fold_map extract_one_family env1 ifams  in
                 (match uu____2403 with
                  | (env2,td) ->
                      let uu____2444 =
                        let uu____2445 =
                          let uu____2446 =
                            FStar_List.map (fun x  -> x.ifv) ifams  in
                          iface_of_type_names uu____2446  in
                        iface_union uu____2445
                          (iface_of_bindings (FStar_List.flatten td))
                         in
                      (env2, uu____2444)))
      | uu____2455 -> failwith "Unexpected signature element"
  
let (extract_type_declaration :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.term Prims.list ->
          FStar_Syntax_Syntax.univ_name Prims.list ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
              (env_t * iface * FStar_Extraction_ML_Syntax.mlmodule1
                Prims.list))
  =
  fun g  ->
    fun lid  ->
      fun quals  ->
        fun attrs  ->
          fun univs1  ->
            fun t  ->
              let uu____2530 =
                let uu____2532 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun uu___6_2538  ->
                          match uu___6_2538 with
                          | FStar_Syntax_Syntax.Assumption  -> true
                          | uu____2541 -> false))
                   in
                Prims.op_Negation uu____2532  in
              if uu____2530
              then (g, empty_iface, [])
              else
                (let uu____2556 = FStar_Syntax_Util.arrow_formals t  in
                 match uu____2556 with
                 | (bs,uu____2572) ->
                     let fv =
                       FStar_Syntax_Syntax.lid_as_fv lid
                         FStar_Syntax_Syntax.delta_constant
                         FStar_Pervasives_Native.None
                        in
                     let lb =
                       let uu____2579 =
                         FStar_Syntax_Util.abs bs FStar_Syntax_Syntax.t_unit
                           FStar_Pervasives_Native.None
                          in
                       {
                         FStar_Syntax_Syntax.lbname = (FStar_Util.Inr fv);
                         FStar_Syntax_Syntax.lbunivs = univs1;
                         FStar_Syntax_Syntax.lbtyp = t;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_Tot_lid;
                         FStar_Syntax_Syntax.lbdef = uu____2579;
                         FStar_Syntax_Syntax.lbattrs = attrs;
                         FStar_Syntax_Syntax.lbpos =
                           (t.FStar_Syntax_Syntax.pos)
                       }  in
                     extract_typ_abbrev g quals attrs lb)
  
let (extract_reifiable_effect :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.eff_decl ->
      (FStar_Extraction_ML_UEnv.uenv * iface *
        FStar_Extraction_ML_Syntax.mlmodule1 Prims.list))
  =
  fun g  ->
    fun ed  ->
      let extend_env g1 lid ml_name tm tysc =
        let fv =
          FStar_Syntax_Syntax.lid_as_fv lid
            FStar_Syntax_Syntax.delta_equational FStar_Pervasives_Native.None
           in
        let uu____2642 =
          FStar_Extraction_ML_UEnv.extend_fv' g1 fv ml_name tysc false false
           in
        match uu____2642 with
        | (g2,mangled_name,exp_binding) ->
            ((let uu____2664 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g2.FStar_Extraction_ML_UEnv.env_tcenv)
                  (FStar_Options.Other "ExtractionReify")
                 in
              if uu____2664
              then FStar_Util.print1 "Mangled name: %s\n" mangled_name
              else ());
             (let lb =
                {
                  FStar_Extraction_ML_Syntax.mllb_name = mangled_name;
                  FStar_Extraction_ML_Syntax.mllb_tysc =
                    FStar_Pervasives_Native.None;
                  FStar_Extraction_ML_Syntax.mllb_add_unit = false;
                  FStar_Extraction_ML_Syntax.mllb_def = tm;
                  FStar_Extraction_ML_Syntax.mllb_meta = [];
                  FStar_Extraction_ML_Syntax.print_typ = false
                }  in
              (g2, (iface_of_bindings [(fv, exp_binding)]),
                (FStar_Extraction_ML_Syntax.MLM_Let
                   (FStar_Extraction_ML_Syntax.NonRec, [lb])))))
         in
      let rec extract_fv tm =
        (let uu____2700 =
           FStar_All.pipe_left
             (FStar_TypeChecker_Env.debug
                g.FStar_Extraction_ML_UEnv.env_tcenv)
             (FStar_Options.Other "ExtractionReify")
            in
         if uu____2700
         then
           let uu____2705 = FStar_Syntax_Print.term_to_string tm  in
           FStar_Util.print1 "extract_fv term: %s\n" uu____2705
         else ());
        (let uu____2710 =
           let uu____2711 = FStar_Syntax_Subst.compress tm  in
           uu____2711.FStar_Syntax_Syntax.n  in
         match uu____2710 with
         | FStar_Syntax_Syntax.Tm_uinst (tm1,uu____2719) -> extract_fv tm1
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             let mlp =
               FStar_Extraction_ML_Syntax.mlpath_of_lident
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             let uu____2726 = FStar_Extraction_ML_UEnv.lookup_fv g fv  in
             (match uu____2726 with
              | { FStar_Extraction_ML_UEnv.exp_b_name = uu____2731;
                  FStar_Extraction_ML_UEnv.exp_b_expr = uu____2732;
                  FStar_Extraction_ML_UEnv.exp_b_tscheme = tysc;
                  FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____2734;_} ->
                  let uu____2737 =
                    FStar_All.pipe_left
                      (FStar_Extraction_ML_Syntax.with_ty
                         FStar_Extraction_ML_Syntax.MLTY_Top)
                      (FStar_Extraction_ML_Syntax.MLE_Name mlp)
                     in
                  (uu____2737, tysc))
         | uu____2738 ->
             let uu____2739 =
               let uu____2741 =
                 FStar_Range.string_of_range tm.FStar_Syntax_Syntax.pos  in
               let uu____2743 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.format2 "(%s) Not an fv: %s" uu____2741 uu____2743
                in
             failwith uu____2739)
         in
      let extract_action g1 a =
        (let uu____2771 =
           FStar_All.pipe_left
             (FStar_TypeChecker_Env.debug
                g1.FStar_Extraction_ML_UEnv.env_tcenv)
             (FStar_Options.Other "ExtractionReify")
            in
         if uu____2771
         then
           let uu____2776 =
             FStar_Syntax_Print.term_to_string
               a.FStar_Syntax_Syntax.action_typ
              in
           let uu____2778 =
             FStar_Syntax_Print.term_to_string
               a.FStar_Syntax_Syntax.action_defn
              in
           FStar_Util.print2 "Action type %s and term %s\n" uu____2776
             uu____2778
         else ());
        (let uu____2783 = FStar_Extraction_ML_UEnv.action_name ed a  in
         match uu____2783 with
         | (a_nm,a_lid) ->
             let lbname =
               let uu____2803 =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some
                      ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos))
                   FStar_Syntax_Syntax.tun
                  in
               FStar_Util.Inl uu____2803  in
             let lb =
               FStar_Syntax_Syntax.mk_lb
                 (lbname, (a.FStar_Syntax_Syntax.action_univs),
                   FStar_Parser_Const.effect_Tot_lid,
                   (a.FStar_Syntax_Syntax.action_typ),
                   (a.FStar_Syntax_Syntax.action_defn), [],
                   ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos))
                in
             let lbs = (false, [lb])  in
             let action_lb =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let
                    (lbs, FStar_Syntax_Util.exp_false_bool))
                 FStar_Pervasives_Native.None
                 (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                in
             let uu____2833 =
               FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb  in
             (match uu____2833 with
              | (a_let,uu____2849,ty) ->
                  ((let uu____2852 =
                      FStar_All.pipe_left
                        (FStar_TypeChecker_Env.debug
                           g1.FStar_Extraction_ML_UEnv.env_tcenv)
                        (FStar_Options.Other "ExtractionReify")
                       in
                    if uu____2852
                    then
                      let uu____2857 =
                        FStar_Extraction_ML_Code.string_of_mlexpr a_nm a_let
                         in
                      FStar_Util.print1 "Extracted action term: %s\n"
                        uu____2857
                    else ());
                   (let uu____2862 =
                      match a_let.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Let
                          ((uu____2885,mllb::[]),uu____2887) ->
                          (match mllb.FStar_Extraction_ML_Syntax.mllb_tysc
                           with
                           | FStar_Pervasives_Native.Some tysc ->
                               ((mllb.FStar_Extraction_ML_Syntax.mllb_def),
                                 tysc)
                           | FStar_Pervasives_Native.None  ->
                               failwith "No type scheme")
                      | uu____2927 -> failwith "Impossible"  in
                    match uu____2862 with
                    | (exp,tysc) ->
                        ((let uu____2965 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug
                                 g1.FStar_Extraction_ML_UEnv.env_tcenv)
                              (FStar_Options.Other "ExtractionReify")
                             in
                          if uu____2965
                          then
                            ((let uu____2971 =
                                FStar_Extraction_ML_Code.string_of_mlty a_nm
                                  (FStar_Pervasives_Native.snd tysc)
                                 in
                              FStar_Util.print1 "Extracted action type: %s\n"
                                uu____2971);
                             FStar_List.iter
                               (fun x  ->
                                  FStar_Util.print1 "and binders: %s\n" x)
                               (FStar_Pervasives_Native.fst tysc))
                          else ());
                         (let uu____2987 = extend_env g1 a_lid a_nm exp tysc
                             in
                          match uu____2987 with
                          | (env,iface1,impl) -> (env, (iface1, impl))))))))
         in
      let uu____3009 =
        let uu____3016 =
          let uu____3021 =
            let uu____3024 =
              let uu____3033 =
                FStar_All.pipe_right ed FStar_Syntax_Util.get_return_repr  in
              FStar_All.pipe_right uu____3033 FStar_Util.must  in
            FStar_All.pipe_right uu____3024 FStar_Pervasives_Native.snd  in
          extract_fv uu____3021  in
        match uu____3016 with
        | (return_tm,ty_sc) ->
            let uu____3102 =
              FStar_Extraction_ML_UEnv.monad_op_name ed "return"  in
            (match uu____3102 with
             | (return_nm,return_lid) ->
                 extend_env g return_lid return_nm return_tm ty_sc)
         in
      match uu____3009 with
      | (g1,return_iface,return_decl) ->
          let uu____3127 =
            let uu____3134 =
              let uu____3139 =
                let uu____3142 =
                  let uu____3151 =
                    FStar_All.pipe_right ed FStar_Syntax_Util.get_bind_repr
                     in
                  FStar_All.pipe_right uu____3151 FStar_Util.must  in
                FStar_All.pipe_right uu____3142 FStar_Pervasives_Native.snd
                 in
              extract_fv uu____3139  in
            match uu____3134 with
            | (bind_tm,ty_sc) ->
                let uu____3220 =
                  FStar_Extraction_ML_UEnv.monad_op_name ed "bind"  in
                (match uu____3220 with
                 | (bind_nm,bind_lid) ->
                     extend_env g1 bind_lid bind_nm bind_tm ty_sc)
             in
          (match uu____3127 with
           | (g2,bind_iface,bind_decl) ->
               let uu____3245 =
                 FStar_Util.fold_map extract_action g2
                   ed.FStar_Syntax_Syntax.actions
                  in
               (match uu____3245 with
                | (g3,actions) ->
                    let uu____3282 = FStar_List.unzip actions  in
                    (match uu____3282 with
                     | (actions_iface,actions1) ->
                         let uu____3309 =
                           iface_union_l (return_iface :: bind_iface ::
                             actions_iface)
                            in
                         (g3, uu____3309, (return_decl :: bind_decl ::
                           actions1)))))
  
let (extract_let_rec_types :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Extraction_ML_UEnv.uenv ->
      FStar_Syntax_Syntax.letbinding Prims.list ->
        (FStar_Extraction_ML_UEnv.uenv * iface *
          FStar_Extraction_ML_Syntax.mlmodule1 Prims.list))
  =
  fun se  ->
    fun env  ->
      fun lbs  ->
        let uu____3340 =
          FStar_Util.for_some
            (fun lb  ->
               let uu____3345 =
                 FStar_Extraction_ML_Term.is_arity env
                   lb.FStar_Syntax_Syntax.lbtyp
                  in
               Prims.op_Negation uu____3345) lbs
           in
        if uu____3340
        then
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExtractionUnsupported,
              "Mutually recursively defined typed and terms cannot yet be extracted")
            se.FStar_Syntax_Syntax.sigrng
        else
          (let uu____3368 =
             FStar_List.fold_left
               (fun uu____3403  ->
                  fun lb  ->
                    match uu____3403 with
                    | (env1,iface_opt,impls) ->
                        let uu____3444 =
                          extract_let_rec_type env1
                            se.FStar_Syntax_Syntax.sigquals
                            se.FStar_Syntax_Syntax.sigattrs lb
                           in
                        (match uu____3444 with
                         | (env2,iface1,impl) ->
                             let iface_opt1 =
                               match iface_opt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.Some iface1
                               | FStar_Pervasives_Native.Some iface' ->
                                   let uu____3478 = iface_union iface' iface1
                                      in
                                   FStar_Pervasives_Native.Some uu____3478
                                in
                             (env2, iface_opt1, (impl :: impls))))
               (env, FStar_Pervasives_Native.None, []) lbs
              in
           match uu____3368 with
           | (env1,iface_opt,impls) ->
               let uu____3518 = FStar_Option.get iface_opt  in
               let uu____3519 =
                 FStar_All.pipe_right (FStar_List.rev impls)
                   FStar_List.flatten
                  in
               (env1, uu____3518, uu____3519))
  
let (extract_sigelt_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.sigelt -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle uu____3551 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____3560 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_datacon uu____3577 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) when
          FStar_Extraction_ML_Term.is_arity g t ->
          let uu____3596 =
            extract_type_declaration g lid se.FStar_Syntax_Syntax.sigquals
              se.FStar_Syntax_Syntax.sigattrs univs1 t
             in
          (match uu____3596 with | (env,iface1,uu____3611) -> (env, iface1))
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____3617) when
          FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp ->
          let uu____3626 =
            extract_typ_abbrev g se.FStar_Syntax_Syntax.sigquals
              se.FStar_Syntax_Syntax.sigattrs lb
             in
          (match uu____3626 with | (env,iface1,uu____3641) -> (env, iface1))
      | FStar_Syntax_Syntax.Sig_let ((true ,lbs),uu____3647) when
          FStar_Util.for_some
            (fun lb  ->
               FStar_Extraction_ML_Term.is_arity g
                 lb.FStar_Syntax_Syntax.lbtyp) lbs
          ->
          let uu____3660 = extract_let_rec_types se g lbs  in
          (match uu____3660 with | (env,iface1,uu____3675) -> (env, iface1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,_univs,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let uu____3686 =
            (FStar_All.pipe_right quals
               (FStar_List.contains FStar_Syntax_Syntax.Assumption))
              &&
              (let uu____3692 =
                 FStar_TypeChecker_Util.must_erase_for_extraction
                   g.FStar_Extraction_ML_UEnv.env_tcenv t
                  in
               Prims.op_Negation uu____3692)
             in
          if uu____3686
          then
            let uu____3699 =
              let uu____3710 =
                let uu____3711 =
                  let uu____3714 = always_fail lid t  in [uu____3714]  in
                (false, uu____3711)  in
              FStar_Extraction_ML_Term.extract_lb_iface g uu____3710  in
            (match uu____3699 with
             | (g1,bindings) -> (g1, (iface_of_bindings bindings)))
          else (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____3740) ->
          let uu____3745 = FStar_Extraction_ML_Term.extract_lb_iface g lbs
             in
          (match uu____3745 with
           | (g1,bindings) -> (g1, (iface_of_bindings bindings)))
      | FStar_Syntax_Syntax.Sig_main uu____3774 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_assume uu____3775 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____3782 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____3783 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____3796 ->
          (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_pragma p ->
          (FStar_Syntax_Util.process_pragma p se.FStar_Syntax_Syntax.sigrng;
           (g, empty_iface))
      | FStar_Syntax_Syntax.Sig_splice uu____3809 ->
          failwith "impossible: trying to extract splice"
      | FStar_Syntax_Syntax.Sig_fail uu____3821 ->
          failwith "impossible: trying to extract Sig_fail"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____3840 =
            (FStar_TypeChecker_Env.is_reifiable_effect
               g.FStar_Extraction_ML_UEnv.env_tcenv
               ed.FStar_Syntax_Syntax.mname)
              && (FStar_List.isEmpty ed.FStar_Syntax_Syntax.binders)
             in
          if uu____3840
          then
            let uu____3853 = extract_reifiable_effect g ed  in
            (match uu____3853 with | (env,iface1,uu____3868) -> (env, iface1))
          else (g, empty_iface)
  
let (extract_iface' :
  env_t ->
    FStar_Syntax_Syntax.modul -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g  ->
    fun modul  ->
      let uu____3890 = FStar_Options.interactive ()  in
      if uu____3890
      then (g, empty_iface)
      else
        (let uu____3899 = FStar_Options.restore_cmd_line_options true  in
         let decls = modul.FStar_Syntax_Syntax.declarations  in
         let iface1 =
           let uu___621_3903 = empty_iface  in
           {
             iface_module_name = (g.FStar_Extraction_ML_UEnv.currentModule);
             iface_bindings = (uu___621_3903.iface_bindings);
             iface_tydefs = (uu___621_3903.iface_tydefs);
             iface_type_names = (uu___621_3903.iface_type_names)
           }  in
         let res =
           FStar_List.fold_left
             (fun uu____3921  ->
                fun se  ->
                  match uu____3921 with
                  | (g1,iface2) ->
                      let uu____3933 = extract_sigelt_iface g1 se  in
                      (match uu____3933 with
                       | (g2,iface') ->
                           let uu____3944 = iface_union iface2 iface'  in
                           (g2, uu____3944))) (g, iface1) decls
            in
         (let uu____3946 = FStar_Options.restore_cmd_line_options true  in
          FStar_All.pipe_left (fun a1  -> ()) uu____3946);
         res)
  
let (extract_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.modul -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g  ->
    fun modul  ->
      let uu____3963 = FStar_Options.debug_any ()  in
      if uu____3963
      then
        let uu____3970 =
          let uu____3972 =
            FStar_Ident.string_of_lid modul.FStar_Syntax_Syntax.name  in
          FStar_Util.format1 "Extracted interface of %s" uu____3972  in
        FStar_Util.measure_execution_time uu____3970
          (fun uu____3980  -> extract_iface' g modul)
      else extract_iface' g modul
  
let (extend_with_iface :
  FStar_Extraction_ML_UEnv.uenv -> iface -> FStar_Extraction_ML_UEnv.uenv) =
  fun g  ->
    fun iface1  ->
      let mlident_map =
        FStar_List.fold_left
          (fun acc  ->
             fun uu____4010  ->
               match uu____4010 with
               | (uu____4021,x) ->
                   FStar_Util.psmap_add acc
                     x.FStar_Extraction_ML_UEnv.exp_b_name "")
          g.FStar_Extraction_ML_UEnv.env_mlident_map iface1.iface_bindings
         in
      let uu___644_4025 = g  in
      let uu____4026 =
        let uu____4029 =
          FStar_List.map (fun _4036  -> FStar_Extraction_ML_UEnv.Fv _4036)
            iface1.iface_bindings
           in
        FStar_List.append uu____4029 g.FStar_Extraction_ML_UEnv.env_bindings
         in
      {
        FStar_Extraction_ML_UEnv.env_tcenv =
          (uu___644_4025.FStar_Extraction_ML_UEnv.env_tcenv);
        FStar_Extraction_ML_UEnv.env_bindings = uu____4026;
        FStar_Extraction_ML_UEnv.env_mlident_map = mlident_map;
        FStar_Extraction_ML_UEnv.tydefs =
          (FStar_List.append iface1.iface_tydefs
             g.FStar_Extraction_ML_UEnv.tydefs);
        FStar_Extraction_ML_UEnv.type_names =
          (FStar_List.append iface1.iface_type_names
             g.FStar_Extraction_ML_UEnv.type_names);
        FStar_Extraction_ML_UEnv.currentModule =
          (uu___644_4025.FStar_Extraction_ML_UEnv.currentModule)
      }
  
let (extract_bundle :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_Extraction_ML_UEnv.uenv * FStar_Extraction_ML_Syntax.mlmodule1
        Prims.list))
  =
  fun env  ->
    fun se  ->
      let extract_ctor env_iparams ml_tyvars env1 ctor =
        let mlt =
          let uu____4114 =
            FStar_Extraction_ML_Term.term_as_mlty env_iparams ctor.dtyp  in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env_iparams) uu____4114
           in
        let steps =
          [FStar_TypeChecker_Env.Inlining;
          FStar_TypeChecker_Env.UnfoldUntil
            FStar_Syntax_Syntax.delta_constant;
          FStar_TypeChecker_Env.EraseUniverses;
          FStar_TypeChecker_Env.AllowUnboundUniverses]  in
        let names1 =
          let uu____4122 =
            let uu____4123 =
              let uu____4126 =
                FStar_TypeChecker_Normalize.normalize steps
                  env_iparams.FStar_Extraction_ML_UEnv.env_tcenv ctor.dtyp
                 in
              FStar_Syntax_Subst.compress uu____4126  in
            uu____4123.FStar_Syntax_Syntax.n  in
          match uu____4122 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,uu____4131) ->
              FStar_List.map
                (fun uu____4164  ->
                   match uu____4164 with
                   | ({ FStar_Syntax_Syntax.ppname = ppname;
                        FStar_Syntax_Syntax.index = uu____4173;
                        FStar_Syntax_Syntax.sort = uu____4174;_},uu____4175)
                       -> FStar_Ident.text_of_id ppname) bs
          | uu____4183 -> []  in
        let tys = (ml_tyvars, mlt)  in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp  in
        let uu____4191 =
          FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false  in
        match uu____4191 with
        | (env2,uu____4218,uu____4219) ->
            let uu____4222 =
              let uu____4235 = lident_as_mlsymbol ctor.dname  in
              let uu____4237 =
                let uu____4245 = FStar_Extraction_ML_Util.argTypes mlt  in
                FStar_List.zip names1 uu____4245  in
              (uu____4235, uu____4237)  in
            (env2, uu____4222)
         in
      let extract_one_family env1 ind =
        let uu____4306 = binders_as_mlty_binders env1 ind.iparams  in
        match uu____4306 with
        | (env_iparams,vars) ->
            let uu____4350 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor env_iparams vars) env1)
               in
            (match uu____4350 with
             | (env2,ctors) ->
                 let uu____4457 = FStar_Syntax_Util.arrow_formals ind.ityp
                    in
                 (match uu____4457 with
                  | (indices,uu____4491) ->
                      let ml_params =
                        let uu____4500 =
                          FStar_All.pipe_right indices
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____4526  ->
                                    let uu____4534 =
                                      FStar_Util.string_of_int i  in
                                    Prims.op_Hat "'dummyV" uu____4534))
                           in
                        FStar_List.append vars uu____4500  in
                      let tbody =
                        let uu____4539 =
                          FStar_Util.find_opt
                            (fun uu___7_4544  ->
                               match uu___7_4544 with
                               | FStar_Syntax_Syntax.RecordType uu____4546 ->
                                   true
                               | uu____4556 -> false) ind.iquals
                           in
                        match uu____4539 with
                        | FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.RecordType (ns,ids)) ->
                            let uu____4568 = FStar_List.hd ctors  in
                            (match uu____4568 with
                             | (uu____4593,c_ty) ->
                                 let fields =
                                   FStar_List.map2
                                     (fun id1  ->
                                        fun uu____4637  ->
                                          match uu____4637 with
                                          | (uu____4648,ty) ->
                                              let lid =
                                                FStar_Ident.lid_of_ids
                                                  (FStar_List.append ns [id1])
                                                 in
                                              let uu____4653 =
                                                lident_as_mlsymbol lid  in
                                              (uu____4653, ty)) ids c_ty
                                    in
                                 FStar_Extraction_ML_Syntax.MLTD_Record
                                   fields)
                        | uu____4656 ->
                            FStar_Extraction_ML_Syntax.MLTD_DType ctors
                         in
                      let uu____4659 =
                        let uu____4682 = lident_as_mlsymbol ind.iname  in
                        (false, uu____4682, FStar_Pervasives_Native.None,
                          ml_params, (ind.imetadata),
                          (FStar_Pervasives_Native.Some tbody))
                         in
                      (env2, uu____4659)))
         in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____4727,t,uu____4729,uu____4730,uu____4731);
            FStar_Syntax_Syntax.sigrng = uu____4732;
            FStar_Syntax_Syntax.sigquals = uu____4733;
            FStar_Syntax_Syntax.sigmeta = uu____4734;
            FStar_Syntax_Syntax.sigattrs = uu____4735;
            FStar_Syntax_Syntax.sigopts = uu____4736;_}::[],uu____4737),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____4758 = extract_ctor env [] env { dname = l; dtyp = t }
             in
          (match uu____4758 with
           | (env1,ctor) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Exn ctor]))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____4811),quals) ->
          let uu____4825 =
            FStar_Syntax_Util.has_attribute se.FStar_Syntax_Syntax.sigattrs
              FStar_Parser_Const.erasable_attr
             in
          if uu____4825
          then (env, [])
          else
            (let uu____4838 = bundle_as_inductive_families env ses quals  in
             match uu____4838 with
             | (env1,ifams) ->
                 let uu____4857 =
                   FStar_Util.fold_map extract_one_family env1 ifams  in
                 (match uu____4857 with
                  | (env2,td) ->
                      (env2, [FStar_Extraction_ML_Syntax.MLM_Ty td])))
      | uu____4966 -> failwith "Unexpected signature element"
  
let (maybe_register_plugin :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      FStar_Extraction_ML_Syntax.mlmodule1 Prims.list)
  =
  fun g  ->
    fun se  ->
      let w =
        FStar_Extraction_ML_Syntax.with_ty
          FStar_Extraction_ML_Syntax.MLTY_Top
         in
      let plugin_with_arity attrs =
        FStar_Util.find_map attrs
          (fun t  ->
             let uu____5024 = FStar_Syntax_Util.head_and_args t  in
             match uu____5024 with
             | (head1,args) ->
                 let uu____5072 =
                   let uu____5074 =
                     FStar_Syntax_Util.is_fvar FStar_Parser_Const.plugin_attr
                       head1
                      in
                   Prims.op_Negation uu____5074  in
                 if uu____5072
                 then FStar_Pervasives_Native.None
                 else
                   (match args with
                    | ({
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_int (s,uu____5093));
                         FStar_Syntax_Syntax.pos = uu____5094;
                         FStar_Syntax_Syntax.vars = uu____5095;_},uu____5096)::[]
                        ->
                        let uu____5135 =
                          let uu____5139 = FStar_Util.int_of_string s  in
                          FStar_Pervasives_Native.Some uu____5139  in
                        FStar_Pervasives_Native.Some uu____5135
                    | uu____5145 ->
                        FStar_Pervasives_Native.Some
                          FStar_Pervasives_Native.None))
         in
      let uu____5160 =
        let uu____5162 = FStar_Options.codegen ()  in
        uu____5162 <> (FStar_Pervasives_Native.Some FStar_Options.Plugin)  in
      if uu____5160
      then []
      else
        (let uu____5172 = plugin_with_arity se.FStar_Syntax_Syntax.sigattrs
            in
         match uu____5172 with
         | FStar_Pervasives_Native.None  -> []
         | FStar_Pervasives_Native.Some arity_opt ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
                  let mk_registration lb =
                    let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                       in
                    let fv_lid1 =
                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                       in
                    let fv_t = lb.FStar_Syntax_Syntax.lbtyp  in
                    let ml_name_str =
                      let uu____5214 =
                        let uu____5215 = FStar_Ident.string_of_lid fv_lid1
                           in
                        FStar_Extraction_ML_Syntax.MLC_String uu____5215  in
                      FStar_Extraction_ML_Syntax.MLE_Const uu____5214  in
                    let uu____5217 =
                      FStar_Extraction_ML_Util.interpret_plugin_as_term_fun
                        g.FStar_Extraction_ML_UEnv.env_tcenv fv fv_t
                        arity_opt ml_name_str
                       in
                    match uu____5217 with
                    | FStar_Pervasives_Native.Some
                        (interp,nbe_interp,arity,plugin) ->
                        let uu____5250 =
                          if plugin
                          then
                            ("FStar_Tactics_Native.register_plugin",
                              [interp; nbe_interp])
                          else
                            ("FStar_Tactics_Native.register_tactic",
                              [interp])
                           in
                        (match uu____5250 with
                         | (register,args) ->
                             let h =
                               let uu____5287 =
                                 let uu____5288 =
                                   let uu____5289 =
                                     FStar_Ident.lid_of_str register  in
                                   FStar_Extraction_ML_Syntax.mlpath_of_lident
                                     uu____5289
                                    in
                                 FStar_Extraction_ML_Syntax.MLE_Name
                                   uu____5288
                                  in
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    FStar_Extraction_ML_Syntax.MLTY_Top)
                                 uu____5287
                                in
                             let arity1 =
                               let uu____5291 =
                                 let uu____5292 =
                                   let uu____5304 =
                                     FStar_Util.string_of_int arity  in
                                   (uu____5304, FStar_Pervasives_Native.None)
                                    in
                                 FStar_Extraction_ML_Syntax.MLC_Int
                                   uu____5292
                                  in
                               FStar_Extraction_ML_Syntax.MLE_Const
                                 uu____5291
                                in
                             let app =
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    FStar_Extraction_ML_Syntax.MLTY_Top)
                                 (FStar_Extraction_ML_Syntax.MLE_App
                                    (h,
                                      (FStar_List.append
                                         [w ml_name_str; w arity1] args)))
                                in
                             [FStar_Extraction_ML_Syntax.MLM_Top app])
                    | FStar_Pervasives_Native.None  -> []  in
                  FStar_List.collect mk_registration
                    (FStar_Pervasives_Native.snd lbs)
              | uu____5333 -> []))
  
let rec (extract_sig :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (env_t * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list))
  =
  fun g  ->
    fun se  ->
      FStar_Extraction_ML_UEnv.debug g
        (fun u  ->
           let uu____5361 = FStar_Syntax_Print.sigelt_to_string se  in
           FStar_Util.print1 ">>>> extract_sig %s \n" uu____5361);
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_bundle uu____5370 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____5379 ->
           extract_bundle g se
       | FStar_Syntax_Syntax.Sig_datacon uu____5396 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_new_effect ed when
           FStar_TypeChecker_Env.is_reifiable_effect
             g.FStar_Extraction_ML_UEnv.env_tcenv
             ed.FStar_Syntax_Syntax.mname
           ->
           let uu____5413 = extract_reifiable_effect g ed  in
           (match uu____5413 with | (env,_iface,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_splice uu____5437 ->
           failwith "impossible: trying to extract splice"
       | FStar_Syntax_Syntax.Sig_fail uu____5451 ->
           failwith "impossible: trying to extract Sig_fail"
       | FStar_Syntax_Syntax.Sig_new_effect uu____5471 -> (g, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) when
           FStar_Extraction_ML_Term.is_arity g t ->
           let uu____5477 =
             extract_type_declaration g lid se.FStar_Syntax_Syntax.sigquals
               se.FStar_Syntax_Syntax.sigattrs univs1 t
              in
           (match uu____5477 with | (env,uu____5493,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____5502) when
           FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp
           ->
           let uu____5511 =
             extract_typ_abbrev g se.FStar_Syntax_Syntax.sigquals
               se.FStar_Syntax_Syntax.sigattrs lb
              in
           (match uu____5511 with | (env,uu____5527,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_let ((true ,lbs),uu____5536) when
           FStar_Util.for_some
             (fun lb  ->
                FStar_Extraction_ML_Term.is_arity g
                  lb.FStar_Syntax_Syntax.lbtyp) lbs
           ->
           let uu____5549 = extract_let_rec_types se g lbs  in
           (match uu____5549 with | (env,uu____5565,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____5574) ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____5585 =
             let uu____5594 =
               FStar_Syntax_Util.extract_attr'
                 FStar_Parser_Const.postprocess_extr_with attrs
                in
             match uu____5594 with
             | FStar_Pervasives_Native.None  ->
                 (attrs, FStar_Pervasives_Native.None)
             | FStar_Pervasives_Native.Some
                 (ats,(tau,FStar_Pervasives_Native.None )::uu____5623) ->
                 (ats, (FStar_Pervasives_Native.Some tau))
             | FStar_Pervasives_Native.Some (ats,args) ->
                 (FStar_Errors.log_issue se.FStar_Syntax_Syntax.sigrng
                    (FStar_Errors.Warning_UnrecognizedAttribute,
                      "Ill-formed application of `postprocess_for_extraction_with`");
                  (attrs, FStar_Pervasives_Native.None))
              in
           (match uu____5585 with
            | (attrs1,post_tau) ->
                let postprocess_lb tau lb =
                  let lbdef =
                    FStar_TypeChecker_Env.postprocess
                      g.FStar_Extraction_ML_UEnv.env_tcenv tau
                      lb.FStar_Syntax_Syntax.lbtyp
                      lb.FStar_Syntax_Syntax.lbdef
                     in
                  let uu___878_5709 = lb  in
                  {
                    FStar_Syntax_Syntax.lbname =
                      (uu___878_5709.FStar_Syntax_Syntax.lbname);
                    FStar_Syntax_Syntax.lbunivs =
                      (uu___878_5709.FStar_Syntax_Syntax.lbunivs);
                    FStar_Syntax_Syntax.lbtyp =
                      (uu___878_5709.FStar_Syntax_Syntax.lbtyp);
                    FStar_Syntax_Syntax.lbeff =
                      (uu___878_5709.FStar_Syntax_Syntax.lbeff);
                    FStar_Syntax_Syntax.lbdef = lbdef;
                    FStar_Syntax_Syntax.lbattrs =
                      (uu___878_5709.FStar_Syntax_Syntax.lbattrs);
                    FStar_Syntax_Syntax.lbpos =
                      (uu___878_5709.FStar_Syntax_Syntax.lbpos)
                  }  in
                let lbs1 =
                  let uu____5718 =
                    match post_tau with
                    | FStar_Pervasives_Native.Some tau ->
                        FStar_List.map (postprocess_lb tau)
                          (FStar_Pervasives_Native.snd lbs)
                    | FStar_Pervasives_Native.None  ->
                        FStar_Pervasives_Native.snd lbs
                     in
                  ((FStar_Pervasives_Native.fst lbs), uu____5718)  in
                let uu____5736 =
                  let uu____5743 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_let
                         (lbs1, FStar_Syntax_Util.exp_false_bool))
                      FStar_Pervasives_Native.None
                      se.FStar_Syntax_Syntax.sigrng
                     in
                  FStar_Extraction_ML_Term.term_as_mlexpr g uu____5743  in
                (match uu____5736 with
                 | (ml_let,uu____5760,uu____5761) ->
                     (match ml_let.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Let
                          ((flavor,bindings),uu____5770) ->
                          let flags = FStar_List.choose flag_of_qual quals
                             in
                          let flags' = extract_metadata attrs1  in
                          let uu____5787 =
                            FStar_List.fold_left2
                              (fun uu____5813  ->
                                 fun ml_lb  ->
                                   fun uu____5815  ->
                                     match (uu____5813, uu____5815) with
                                     | ((env,ml_lbs),{
                                                       FStar_Syntax_Syntax.lbname
                                                         = lbname;
                                                       FStar_Syntax_Syntax.lbunivs
                                                         = uu____5837;
                                                       FStar_Syntax_Syntax.lbtyp
                                                         = t;
                                                       FStar_Syntax_Syntax.lbeff
                                                         = uu____5839;
                                                       FStar_Syntax_Syntax.lbdef
                                                         = uu____5840;
                                                       FStar_Syntax_Syntax.lbattrs
                                                         = uu____5841;
                                                       FStar_Syntax_Syntax.lbpos
                                                         = uu____5842;_})
                                         ->
                                         let uu____5867 =
                                           FStar_All.pipe_right
                                             ml_lb.FStar_Extraction_ML_Syntax.mllb_meta
                                             (FStar_List.contains
                                                FStar_Extraction_ML_Syntax.Erased)
                                            in
                                         if uu____5867
                                         then (env, ml_lbs)
                                         else
                                           (let lb_lid =
                                              let uu____5884 =
                                                let uu____5887 =
                                                  FStar_Util.right lbname  in
                                                uu____5887.FStar_Syntax_Syntax.fv_name
                                                 in
                                              uu____5884.FStar_Syntax_Syntax.v
                                               in
                                            let flags'' =
                                              let uu____5891 =
                                                let uu____5892 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____5892.FStar_Syntax_Syntax.n
                                                 in
                                              match uu____5891 with
                                              | FStar_Syntax_Syntax.Tm_arrow
                                                  (uu____5897,{
                                                                FStar_Syntax_Syntax.n
                                                                  =
                                                                  FStar_Syntax_Syntax.Comp
                                                                  {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____5898;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    = e;
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    =
                                                                    uu____5900;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____5901;
                                                                    FStar_Syntax_Syntax.flags
                                                                    =
                                                                    uu____5902;_};
                                                                FStar_Syntax_Syntax.pos
                                                                  =
                                                                  uu____5903;
                                                                FStar_Syntax_Syntax.vars
                                                                  =
                                                                  uu____5904;_})
                                                  when
                                                  let uu____5939 =
                                                    FStar_Ident.string_of_lid
                                                      e
                                                     in
                                                  uu____5939 =
                                                    "FStar.HyperStack.ST.StackInline"
                                                  ->
                                                  [FStar_Extraction_ML_Syntax.StackInline]
                                              | uu____5943 -> []  in
                                            let meta =
                                              FStar_List.append flags
                                                (FStar_List.append flags'
                                                   flags'')
                                               in
                                            let ml_lb1 =
                                              let uu___926_5948 = ml_lb  in
                                              {
                                                FStar_Extraction_ML_Syntax.mllb_name
                                                  =
                                                  (uu___926_5948.FStar_Extraction_ML_Syntax.mllb_name);
                                                FStar_Extraction_ML_Syntax.mllb_tysc
                                                  =
                                                  (uu___926_5948.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                FStar_Extraction_ML_Syntax.mllb_add_unit
                                                  =
                                                  (uu___926_5948.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                FStar_Extraction_ML_Syntax.mllb_def
                                                  =
                                                  (uu___926_5948.FStar_Extraction_ML_Syntax.mllb_def);
                                                FStar_Extraction_ML_Syntax.mllb_meta
                                                  = meta;
                                                FStar_Extraction_ML_Syntax.print_typ
                                                  =
                                                  (uu___926_5948.FStar_Extraction_ML_Syntax.print_typ)
                                              }  in
                                            let uu____5949 =
                                              let uu____5954 =
                                                FStar_All.pipe_right quals
                                                  (FStar_Util.for_some
                                                     (fun uu___8_5961  ->
                                                        match uu___8_5961
                                                        with
                                                        | FStar_Syntax_Syntax.Projector
                                                            uu____5963 ->
                                                            true
                                                        | uu____5969 -> false))
                                                 in
                                              if uu____5954
                                              then
                                                let mname =
                                                  let uu____5985 =
                                                    mangle_projector_lid
                                                      lb_lid
                                                     in
                                                  FStar_All.pipe_right
                                                    uu____5985
                                                    FStar_Extraction_ML_Syntax.mlpath_of_lident
                                                   in
                                                let uu____5994 =
                                                  let uu____6002 =
                                                    FStar_Util.right lbname
                                                     in
                                                  let uu____6003 =
                                                    FStar_Util.must
                                                      ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc
                                                     in
                                                  FStar_Extraction_ML_UEnv.extend_fv'
                                                    env uu____6002 mname
                                                    uu____6003
                                                    ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit
                                                    false
                                                   in
                                                match uu____5994 with
                                                | (env1,uu____6010,uu____6011)
                                                    ->
                                                    (env1,
                                                      (let uu___939_6015 =
                                                         ml_lb1  in
                                                       {
                                                         FStar_Extraction_ML_Syntax.mllb_name
                                                           =
                                                           (FStar_Pervasives_Native.snd
                                                              mname);
                                                         FStar_Extraction_ML_Syntax.mllb_tysc
                                                           =
                                                           (uu___939_6015.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                         FStar_Extraction_ML_Syntax.mllb_add_unit
                                                           =
                                                           (uu___939_6015.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                         FStar_Extraction_ML_Syntax.mllb_def
                                                           =
                                                           (uu___939_6015.FStar_Extraction_ML_Syntax.mllb_def);
                                                         FStar_Extraction_ML_Syntax.mllb_meta
                                                           =
                                                           (uu___939_6015.FStar_Extraction_ML_Syntax.mllb_meta);
                                                         FStar_Extraction_ML_Syntax.print_typ
                                                           =
                                                           (uu___939_6015.FStar_Extraction_ML_Syntax.print_typ)
                                                       }))
                                              else
                                                (let uu____6022 =
                                                   let uu____6030 =
                                                     FStar_Util.must
                                                       ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc
                                                      in
                                                   FStar_Extraction_ML_UEnv.extend_lb
                                                     env lbname t uu____6030
                                                     ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit
                                                     false
                                                    in
                                                 match uu____6022 with
                                                 | (env1,uu____6037,uu____6038)
                                                     -> (env1, ml_lb1))
                                               in
                                            match uu____5949 with
                                            | (g1,ml_lb2) ->
                                                (g1, (ml_lb2 :: ml_lbs))))
                              (g, []) bindings
                              (FStar_Pervasives_Native.snd lbs1)
                             in
                          (match uu____5787 with
                           | (g1,ml_lbs') ->
                               let uu____6068 =
                                 let uu____6071 =
                                   let uu____6074 =
                                     let uu____6075 =
                                       FStar_Extraction_ML_Util.mlloc_of_range
                                         se.FStar_Syntax_Syntax.sigrng
                                        in
                                     FStar_Extraction_ML_Syntax.MLM_Loc
                                       uu____6075
                                      in
                                   [uu____6074;
                                   FStar_Extraction_ML_Syntax.MLM_Let
                                     (flavor, (FStar_List.rev ml_lbs'))]
                                    in
                                 let uu____6078 = maybe_register_plugin g1 se
                                    in
                                 FStar_List.append uu____6071 uu____6078  in
                               (g1, uu____6068))
                      | uu____6083 ->
                          let uu____6084 =
                            let uu____6086 =
                              FStar_Extraction_ML_Code.string_of_mlexpr
                                g.FStar_Extraction_ML_UEnv.currentModule
                                ml_let
                               in
                            FStar_Util.format1
                              "Impossible: Translated a let to a non-let: %s"
                              uu____6086
                             in
                          failwith uu____6084)))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____6096,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____6101 =
             (FStar_All.pipe_right quals
                (FStar_List.contains FStar_Syntax_Syntax.Assumption))
               &&
               (let uu____6107 =
                  FStar_TypeChecker_Util.must_erase_for_extraction
                    g.FStar_Extraction_ML_UEnv.env_tcenv t
                   in
                Prims.op_Negation uu____6107)
              in
           if uu____6101
           then
             let always_fail1 =
               let uu___959_6117 = se  in
               let uu____6118 =
                 let uu____6119 =
                   let uu____6126 =
                     let uu____6127 =
                       let uu____6130 = always_fail lid t  in [uu____6130]
                        in
                     (false, uu____6127)  in
                   (uu____6126, [])  in
                 FStar_Syntax_Syntax.Sig_let uu____6119  in
               {
                 FStar_Syntax_Syntax.sigel = uu____6118;
                 FStar_Syntax_Syntax.sigrng =
                   (uu___959_6117.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___959_6117.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___959_6117.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___959_6117.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___959_6117.FStar_Syntax_Syntax.sigopts)
               }  in
             let uu____6137 = extract_sig g always_fail1  in
             (match uu____6137 with
              | (g1,mlm) ->
                  let uu____6156 =
                    FStar_Util.find_map quals
                      (fun uu___9_6161  ->
                         match uu___9_6161 with
                         | FStar_Syntax_Syntax.Discriminator l ->
                             FStar_Pervasives_Native.Some l
                         | uu____6165 -> FStar_Pervasives_Native.None)
                     in
                  (match uu____6156 with
                   | FStar_Pervasives_Native.Some l ->
                       let uu____6173 =
                         let uu____6176 =
                           let uu____6177 =
                             FStar_Extraction_ML_Util.mlloc_of_range
                               se.FStar_Syntax_Syntax.sigrng
                              in
                           FStar_Extraction_ML_Syntax.MLM_Loc uu____6177  in
                         let uu____6178 =
                           let uu____6181 =
                             FStar_Extraction_ML_Term.ind_discriminator_body
                               g1 lid l
                              in
                           [uu____6181]  in
                         uu____6176 :: uu____6178  in
                       (g1, uu____6173)
                   | uu____6184 ->
                       let uu____6187 =
                         FStar_Util.find_map quals
                           (fun uu___10_6193  ->
                              match uu___10_6193 with
                              | FStar_Syntax_Syntax.Projector (l,uu____6197)
                                  -> FStar_Pervasives_Native.Some l
                              | uu____6198 -> FStar_Pervasives_Native.None)
                          in
                       (match uu____6187 with
                        | FStar_Pervasives_Native.Some uu____6205 -> (g1, [])
                        | uu____6208 -> (g1, mlm))))
           else (g, [])
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____6218 = FStar_Extraction_ML_Term.term_as_mlexpr g e  in
           (match uu____6218 with
            | (ml_main,uu____6232,uu____6233) ->
                let uu____6234 =
                  let uu____6237 =
                    let uu____6238 =
                      FStar_Extraction_ML_Util.mlloc_of_range
                        se.FStar_Syntax_Syntax.sigrng
                       in
                    FStar_Extraction_ML_Syntax.MLM_Loc uu____6238  in
                  [uu____6237; FStar_Extraction_ML_Syntax.MLM_Top ml_main]
                   in
                (g, uu____6234))
       | FStar_Syntax_Syntax.Sig_assume uu____6241 -> (g, [])
       | FStar_Syntax_Syntax.Sig_sub_effect uu____6250 -> (g, [])
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____6253 -> (g, [])
       | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____6268 -> (g, [])
       | FStar_Syntax_Syntax.Sig_pragma p ->
           (FStar_Syntax_Util.process_pragma p se.FStar_Syntax_Syntax.sigrng;
            (g, [])))
  
let (extract' :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Extraction_ML_UEnv.uenv * FStar_Extraction_ML_Syntax.mllib
        FStar_Pervasives_Native.option))
  =
  fun g  ->
    fun m  ->
      let uu____6308 = FStar_Options.restore_cmd_line_options true  in
      let name =
        FStar_Extraction_ML_Syntax.mlpath_of_lident
          m.FStar_Syntax_Syntax.name
         in
      let g1 =
        let uu___1002_6312 = g  in
        let uu____6313 =
          FStar_TypeChecker_Env.set_current_module
            g.FStar_Extraction_ML_UEnv.env_tcenv m.FStar_Syntax_Syntax.name
           in
        {
          FStar_Extraction_ML_UEnv.env_tcenv = uu____6313;
          FStar_Extraction_ML_UEnv.env_bindings =
            (uu___1002_6312.FStar_Extraction_ML_UEnv.env_bindings);
          FStar_Extraction_ML_UEnv.env_mlident_map =
            (uu___1002_6312.FStar_Extraction_ML_UEnv.env_mlident_map);
          FStar_Extraction_ML_UEnv.tydefs =
            (uu___1002_6312.FStar_Extraction_ML_UEnv.tydefs);
          FStar_Extraction_ML_UEnv.type_names =
            (uu___1002_6312.FStar_Extraction_ML_UEnv.type_names);
          FStar_Extraction_ML_UEnv.currentModule = name
        }  in
      let uu____6314 =
        FStar_Util.fold_map
          (fun g2  ->
             fun se  ->
               let uu____6333 =
                 let uu____6335 =
                   FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
                 FStar_Options.debug_module uu____6335  in
               if uu____6333
               then
                 let nm =
                   let uu____6346 =
                     FStar_All.pipe_right
                       (FStar_Syntax_Util.lids_of_sigelt se)
                       (FStar_List.map FStar_Ident.string_of_lid)
                      in
                   FStar_All.pipe_right uu____6346 (FStar_String.concat ", ")
                    in
                 (FStar_Util.print1 "+++About to extract {%s}\n" nm;
                  (let uu____6363 = FStar_Util.format1 "---Extracted {%s}" nm
                      in
                   FStar_Util.measure_execution_time uu____6363
                     (fun uu____6373  -> extract_sig g2 se)))
               else extract_sig g2 se) g1 m.FStar_Syntax_Syntax.declarations
         in
      match uu____6314 with
      | (g2,sigs) ->
          let mlm = FStar_List.flatten sigs  in
          let is_kremlin =
            let uu____6395 = FStar_Options.codegen ()  in
            uu____6395 = (FStar_Pervasives_Native.Some FStar_Options.Kremlin)
             in
          let uu____6400 =
            (let uu____6404 =
               FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
             uu____6404 <> "Prims") &&
              (is_kremlin ||
                 (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface))
             in
          if uu____6400
          then
            ((let uu____6416 =
                let uu____6418 = FStar_Options.silent ()  in
                Prims.op_Negation uu____6418  in
              if uu____6416
              then
                let uu____6421 =
                  FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
                FStar_Util.print1 "Extracted module %s\n" uu____6421
              else ());
             (g2,
               (FStar_Pervasives_Native.Some
                  (FStar_Extraction_ML_Syntax.MLLib
                     [(name, (FStar_Pervasives_Native.Some ([], mlm)),
                        (FStar_Extraction_ML_Syntax.MLLib []))]))))
          else (g2, FStar_Pervasives_Native.None)
  
let (extract :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Extraction_ML_UEnv.uenv * FStar_Extraction_ML_Syntax.mllib
        FStar_Pervasives_Native.option))
  =
  fun g  ->
    fun m  ->
      (let uu____6496 = FStar_Options.restore_cmd_line_options true  in
       FStar_All.pipe_left (fun a2  -> ()) uu____6496);
      (let uu____6499 =
         let uu____6501 =
           let uu____6503 =
             FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
           FStar_Options.should_extract uu____6503  in
         Prims.op_Negation uu____6501  in
       if uu____6499
       then
         let uu____6506 =
           let uu____6508 =
             FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
           FStar_Util.format1
             "Extract called on a module %s that should not be extracted"
             uu____6508
            in
         failwith uu____6506
       else ());
      (let uu____6513 = FStar_Options.interactive ()  in
       if uu____6513
       then (g, FStar_Pervasives_Native.None)
       else
         (let res =
            let uu____6533 = FStar_Options.debug_any ()  in
            if uu____6533
            then
              let msg =
                let uu____6544 =
                  FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name
                   in
                FStar_Util.format1 "Extracting module %s" uu____6544  in
              FStar_Util.measure_execution_time msg
                (fun uu____6554  -> extract' g m)
            else extract' g m  in
          (let uu____6558 = FStar_Options.restore_cmd_line_options true  in
           FStar_All.pipe_left (fun a3  -> ()) uu____6558);
          res))
  
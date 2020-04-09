open Prims
type annotated_pat =
  (FStar_Syntax_Syntax.pat * (FStar_Syntax_Syntax.bv *
    FStar_Syntax_Syntax.typ) Prims.list)
let (desugar_disjunctive_pattern :
  (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t *
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
    FStar_Syntax_Syntax.syntax) Prims.list) Prims.list ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.branch Prims.list)
  =
  fun annotated_pats  ->
    fun when_opt  ->
      fun branch1  ->
        FStar_All.pipe_right annotated_pats
          (FStar_List.map
             (fun uu____103  ->
                match uu____103 with
                | (pat,annots) ->
                    let branch2 =
                      FStar_List.fold_left
                        (fun br  ->
                           fun uu____158  ->
                             match uu____158 with
                             | (bv,ty) ->
                                 let lb =
                                   let uu____176 =
                                     FStar_Syntax_Syntax.bv_to_name bv  in
                                   FStar_Syntax_Util.mk_letbinding
                                     (FStar_Util.Inl bv) [] ty
                                     FStar_Parser_Const.effect_Tot_lid
                                     uu____176 [] br.FStar_Syntax_Syntax.pos
                                    in
                                 let branch2 =
                                   let uu____182 =
                                     let uu____183 =
                                       FStar_Syntax_Syntax.mk_binder bv  in
                                     [uu____183]  in
                                   FStar_Syntax_Subst.close uu____182 branch1
                                    in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((false, [lb]), branch2))
                                   FStar_Pervasives_Native.None
                                   br.FStar_Syntax_Syntax.pos) branch1 annots
                       in
                    FStar_Syntax_Util.branch (pat, when_opt, branch2)))
  
let (trans_qual :
  FStar_Range.range ->
    FStar_Ident.lident FStar_Pervasives_Native.option ->
      FStar_Parser_AST.qualifier -> FStar_Syntax_Syntax.qualifier)
  =
  fun r  ->
    fun maybe_effect_id  ->
      fun uu___0_240  ->
        match uu___0_240 with
        | FStar_Parser_AST.Private  -> FStar_Syntax_Syntax.Private
        | FStar_Parser_AST.Assumption  -> FStar_Syntax_Syntax.Assumption
        | FStar_Parser_AST.Unfold_for_unification_and_vcgen  ->
            FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
        | FStar_Parser_AST.Inline_for_extraction  ->
            FStar_Syntax_Syntax.Inline_for_extraction
        | FStar_Parser_AST.NoExtract  -> FStar_Syntax_Syntax.NoExtract
        | FStar_Parser_AST.Irreducible  -> FStar_Syntax_Syntax.Irreducible
        | FStar_Parser_AST.Logic  -> FStar_Syntax_Syntax.Logic
        | FStar_Parser_AST.TotalEffect  -> FStar_Syntax_Syntax.TotalEffect
        | FStar_Parser_AST.Effect_qual  -> FStar_Syntax_Syntax.Effect
        | FStar_Parser_AST.New  -> FStar_Syntax_Syntax.New
        | FStar_Parser_AST.Abstract  -> FStar_Syntax_Syntax.Abstract
        | FStar_Parser_AST.Opaque  ->
            (FStar_Errors.log_issue r
               (FStar_Errors.Warning_DeprecatedOpaqueQualifier,
                 "The 'opaque' qualifier is deprecated since its use was strangely schizophrenic. There were two overloaded uses: (1) Given 'opaque val f : t', the behavior was to exclude the definition of 'f' to the SMT solver. This corresponds roughly to the new 'irreducible' qualifier. (2) Given 'opaque type t = t'', the behavior was to provide the definition of 't' to the SMT solver, but not to inline it, unless absolutely required for unification. This corresponds roughly to the behavior of 'unfoldable' (which is currently the default).");
             FStar_Syntax_Syntax.Visible_default)
        | FStar_Parser_AST.Reflectable  ->
            (match maybe_effect_id with
             | FStar_Pervasives_Native.None  ->
                 FStar_Errors.raise_error
                   (FStar_Errors.Fatal_ReflectOnlySupportedOnEffects,
                     "Qualifier reflect only supported on effects") r
             | FStar_Pervasives_Native.Some effect_id ->
                 FStar_Syntax_Syntax.Reflectable effect_id)
        | FStar_Parser_AST.Reifiable  -> FStar_Syntax_Syntax.Reifiable
        | FStar_Parser_AST.Noeq  -> FStar_Syntax_Syntax.Noeq
        | FStar_Parser_AST.Unopteq  -> FStar_Syntax_Syntax.Unopteq
        | FStar_Parser_AST.DefaultEffect  ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_DefaultQualifierNotAllowedOnEffects,
                "The 'default' qualifier on effects is no longer supported")
              r
        | FStar_Parser_AST.Inline  ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnsupportedQualifier,
                "Unsupported qualifier") r
        | FStar_Parser_AST.Visible  ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnsupportedQualifier,
                "Unsupported qualifier") r
  
let (trans_pragma : FStar_Parser_AST.pragma -> FStar_Syntax_Syntax.pragma) =
  fun uu___1_260  ->
    match uu___1_260 with
    | FStar_Parser_AST.SetOptions s -> FStar_Syntax_Syntax.SetOptions s
    | FStar_Parser_AST.ResetOptions sopt ->
        FStar_Syntax_Syntax.ResetOptions sopt
    | FStar_Parser_AST.PushOptions sopt ->
        FStar_Syntax_Syntax.PushOptions sopt
    | FStar_Parser_AST.PopOptions  -> FStar_Syntax_Syntax.PopOptions
    | FStar_Parser_AST.RestartSolver  -> FStar_Syntax_Syntax.RestartSolver
    | FStar_Parser_AST.LightOff  -> FStar_Syntax_Syntax.LightOff
  
let (as_imp :
  FStar_Parser_AST.imp ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
  =
  fun uu___2_278  ->
    match uu___2_278 with
    | FStar_Parser_AST.Hash  ->
        FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
    | uu____281 -> FStar_Pervasives_Native.None
  
let arg_withimp_e :
  'Auu____289 .
    FStar_Parser_AST.imp ->
      'Auu____289 ->
        ('Auu____289 * FStar_Syntax_Syntax.arg_qualifier
          FStar_Pervasives_Native.option)
  = fun imp  -> fun t  -> (t, (as_imp imp)) 
let arg_withimp_t :
  'Auu____315 .
    FStar_Parser_AST.imp ->
      'Auu____315 ->
        ('Auu____315 * FStar_Syntax_Syntax.arg_qualifier
          FStar_Pervasives_Native.option)
  =
  fun imp  ->
    fun t  ->
      match imp with
      | FStar_Parser_AST.Hash  ->
          (t, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag))
      | uu____334 -> (t, FStar_Pervasives_Native.None)
  
let (contains_binder : FStar_Parser_AST.binder Prims.list -> Prims.bool) =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_Util.for_some
         (fun b  ->
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated uu____355 -> true
            | uu____361 -> false))
  
let rec (unparen : FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Paren t1 -> unparen t1
    | uu____370 -> t
  
let (tm_type_z : FStar_Range.range -> FStar_Parser_AST.term) =
  fun r  ->
    let uu____377 =
      let uu____378 = FStar_Ident.lid_of_path ["Type0"] r  in
      FStar_Parser_AST.Name uu____378  in
    FStar_Parser_AST.mk_term uu____377 r FStar_Parser_AST.Kind
  
let (tm_type : FStar_Range.range -> FStar_Parser_AST.term) =
  fun r  ->
    let uu____388 =
      let uu____389 = FStar_Ident.lid_of_path ["Type"] r  in
      FStar_Parser_AST.Name uu____389  in
    FStar_Parser_AST.mk_term uu____388 r FStar_Parser_AST.Kind
  
let rec (is_comp_type :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____405 =
        let uu____406 = unparen t  in uu____406.FStar_Parser_AST.tm  in
      match uu____405 with
      | FStar_Parser_AST.Name l ->
          let uu____409 = FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
          FStar_All.pipe_right uu____409 FStar_Option.isSome
      | FStar_Parser_AST.Construct (l,uu____416) ->
          let uu____429 = FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
          FStar_All.pipe_right uu____429 FStar_Option.isSome
      | FStar_Parser_AST.App (head1,uu____436,uu____437) ->
          is_comp_type env head1
      | FStar_Parser_AST.Paren t1 -> failwith "impossible"
      | FStar_Parser_AST.Ascribed (t1,uu____442,uu____443) ->
          is_comp_type env t1
      | FStar_Parser_AST.LetOpen (uu____448,t1) -> is_comp_type env t1
      | uu____450 -> false
  
let (unit_ty : FStar_Parser_AST.term) =
  FStar_Parser_AST.mk_term
    (FStar_Parser_AST.Name FStar_Parser_Const.unit_lid)
    FStar_Range.dummyRange FStar_Parser_AST.Type_level
  
type env_t = FStar_Syntax_DsEnv.env
type lenv_t = FStar_Syntax_Syntax.bv Prims.list
let (desugar_name' :
  (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
    env_t ->
      Prims.bool ->
        FStar_Ident.lid ->
          FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun setpos  ->
    fun env  ->
      fun resolve  ->
        fun l  ->
          let tm_attrs_opt =
            if resolve
            then FStar_Syntax_DsEnv.try_lookup_lid_with_attributes env l
            else
              FStar_Syntax_DsEnv.try_lookup_lid_with_attributes_no_resolve
                env l
             in
          match tm_attrs_opt with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (tm,attrs) ->
              let warn_if_deprecated attrs1 =
                FStar_List.iter
                  (fun a  ->
                     match a.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_fvar fv;
                            FStar_Syntax_Syntax.pos = uu____551;
                            FStar_Syntax_Syntax.vars = uu____552;_},args)
                         when
                         FStar_Ident.lid_equals
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           FStar_Parser_Const.deprecated_attr
                         ->
                         let msg =
                           let uu____580 =
                             FStar_Syntax_Print.term_to_string tm  in
                           Prims.op_Hat uu____580 " is deprecated"  in
                         let msg1 =
                           if (FStar_List.length args) > Prims.int_zero
                           then
                             let uu____596 =
                               let uu____597 =
                                 let uu____600 = FStar_List.hd args  in
                                 FStar_Pervasives_Native.fst uu____600  in
                               uu____597.FStar_Syntax_Syntax.n  in
                             match uu____596 with
                             | FStar_Syntax_Syntax.Tm_constant
                                 (FStar_Const.Const_string (s,uu____623))
                                 when
                                 Prims.op_Negation
                                   ((FStar_Util.trim_string s) = "")
                                 ->
                                 Prims.op_Hat msg
                                   (Prims.op_Hat ", use "
                                      (Prims.op_Hat s " instead"))
                             | uu____630 -> msg
                           else msg  in
                         let uu____633 = FStar_Ident.range_of_lid l  in
                         FStar_Errors.log_issue uu____633
                           (FStar_Errors.Warning_DeprecatedDefinition, msg1)
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Ident.lid_equals
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           FStar_Parser_Const.deprecated_attr
                         ->
                         let msg =
                           let uu____638 =
                             FStar_Syntax_Print.term_to_string tm  in
                           Prims.op_Hat uu____638 " is deprecated"  in
                         let uu____641 = FStar_Ident.range_of_lid l  in
                         FStar_Errors.log_issue uu____641
                           (FStar_Errors.Warning_DeprecatedDefinition, msg)
                     | uu____643 -> ()) attrs1
                 in
              (warn_if_deprecated attrs;
               (let tm1 = setpos tm  in FStar_Pervasives_Native.Some tm1))
  
let desugar_name :
  'Auu____659 .
    'Auu____659 ->
      (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
        env_t -> Prims.bool -> FStar_Ident.lident -> FStar_Syntax_Syntax.term
  =
  fun mk1  ->
    fun setpos  ->
      fun env  ->
        fun resolve  ->
          fun l  ->
            FStar_Syntax_DsEnv.fail_or env (desugar_name' setpos env resolve)
              l
  
let (compile_op_lid :
  Prims.int -> Prims.string -> FStar_Range.range -> FStar_Ident.lident) =
  fun n1  ->
    fun s  ->
      fun r  ->
        let uu____712 =
          let uu____713 =
            let uu____714 =
              let uu____720 = FStar_Parser_AST.compile_op n1 s r  in
              (uu____720, r)  in
            FStar_Ident.mk_ident uu____714  in
          [uu____713]  in
        FStar_All.pipe_right uu____712 FStar_Ident.lid_of_ids
  
let op_as_term :
  'Auu____734 .
    env_t ->
      Prims.int ->
        'Auu____734 ->
          FStar_Ident.ident ->
            FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun arity  ->
      fun rng  ->
        fun op  ->
          let r l dd =
            let uu____772 =
              let uu____773 =
                let uu____774 =
                  let uu____775 = FStar_Ident.range_of_id op  in
                  FStar_Ident.set_lid_range l uu____775  in
                FStar_Syntax_Syntax.lid_as_fv uu____774 dd
                  FStar_Pervasives_Native.None
                 in
              FStar_All.pipe_right uu____773 FStar_Syntax_Syntax.fv_to_tm  in
            FStar_Pervasives_Native.Some uu____772  in
          let fallback uu____783 =
            let uu____784 = FStar_Ident.text_of_id op  in
            match uu____784 with
            | "=" ->
                r FStar_Parser_Const.op_Eq
                  FStar_Syntax_Syntax.delta_equational
            | ":=" ->
                r FStar_Parser_Const.write_lid
                  FStar_Syntax_Syntax.delta_equational
            | "<" ->
                r FStar_Parser_Const.op_LT
                  FStar_Syntax_Syntax.delta_equational
            | "<=" ->
                r FStar_Parser_Const.op_LTE
                  FStar_Syntax_Syntax.delta_equational
            | ">" ->
                r FStar_Parser_Const.op_GT
                  FStar_Syntax_Syntax.delta_equational
            | ">=" ->
                r FStar_Parser_Const.op_GTE
                  FStar_Syntax_Syntax.delta_equational
            | "&&" ->
                r FStar_Parser_Const.op_And
                  FStar_Syntax_Syntax.delta_equational
            | "||" ->
                r FStar_Parser_Const.op_Or
                  FStar_Syntax_Syntax.delta_equational
            | "+" ->
                r FStar_Parser_Const.op_Addition
                  FStar_Syntax_Syntax.delta_equational
            | "-" when arity = Prims.int_one ->
                r FStar_Parser_Const.op_Minus
                  FStar_Syntax_Syntax.delta_equational
            | "-" ->
                r FStar_Parser_Const.op_Subtraction
                  FStar_Syntax_Syntax.delta_equational
            | "/" ->
                r FStar_Parser_Const.op_Division
                  FStar_Syntax_Syntax.delta_equational
            | "%" ->
                r FStar_Parser_Const.op_Modulus
                  FStar_Syntax_Syntax.delta_equational
            | "!" ->
                r FStar_Parser_Const.read_lid
                  FStar_Syntax_Syntax.delta_equational
            | "@" ->
                let uu____805 = FStar_Options.ml_ish ()  in
                if uu____805
                then
                  r FStar_Parser_Const.list_append_lid
                    (FStar_Syntax_Syntax.Delta_equational_at_level
                       (Prims.of_int (2)))
                else
                  r FStar_Parser_Const.list_tot_append_lid
                    (FStar_Syntax_Syntax.Delta_equational_at_level
                       (Prims.of_int (2)))
            | "|>" ->
                r FStar_Parser_Const.pipe_right_lid
                  FStar_Syntax_Syntax.delta_equational
            | "<|" ->
                r FStar_Parser_Const.pipe_left_lid
                  FStar_Syntax_Syntax.delta_equational
            | "<>" ->
                r FStar_Parser_Const.op_notEq
                  FStar_Syntax_Syntax.delta_equational
            | "~" ->
                r FStar_Parser_Const.not_lid
                  (FStar_Syntax_Syntax.Delta_constant_at_level
                     (Prims.of_int (2)))
            | "==" ->
                r FStar_Parser_Const.eq2_lid
                  (FStar_Syntax_Syntax.Delta_constant_at_level
                     (Prims.of_int (2)))
            | "<<" ->
                r FStar_Parser_Const.precedes_lid
                  FStar_Syntax_Syntax.delta_constant
            | "/\\" ->
                r FStar_Parser_Const.and_lid
                  (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_one)
            | "\\/" ->
                r FStar_Parser_Const.or_lid
                  (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_one)
            | "==>" ->
                r FStar_Parser_Const.imp_lid
                  (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_one)
            | "<==>" ->
                r FStar_Parser_Const.iff_lid
                  (FStar_Syntax_Syntax.Delta_constant_at_level
                     (Prims.of_int (2)))
            | uu____830 -> FStar_Pervasives_Native.None  in
          let uu____832 =
            let uu____835 =
              let uu____836 = FStar_Ident.text_of_id op  in
              let uu____838 = FStar_Ident.range_of_id op  in
              compile_op_lid arity uu____836 uu____838  in
            desugar_name'
              (fun t  ->
                 let uu___202_846 = t  in
                 let uu____847 = FStar_Ident.range_of_id op  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___202_846.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = uu____847;
                   FStar_Syntax_Syntax.vars =
                     (uu___202_846.FStar_Syntax_Syntax.vars)
                 }) env true uu____835
             in
          match uu____832 with
          | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
          | uu____852 -> fallback ()
  
let (sort_ftv : FStar_Ident.ident Prims.list -> FStar_Ident.ident Prims.list)
  =
  fun ftv  ->
    let uu____867 =
      FStar_Util.remove_dups
        (fun x  ->
           fun y  ->
             let uu____876 = FStar_Ident.text_of_id x  in
             let uu____878 = FStar_Ident.text_of_id y  in
             uu____876 = uu____878) ftv
       in
    FStar_All.pipe_left
      (FStar_Util.sort_with
         (fun x  ->
            fun y  ->
              let uu____891 = FStar_Ident.text_of_id x  in
              let uu____893 = FStar_Ident.text_of_id y  in
              FStar_String.compare uu____891 uu____893)) uu____867
  
let rec (free_type_vars_b :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder ->
      (FStar_Syntax_DsEnv.env * FStar_Ident.ident Prims.list))
  =
  fun env  ->
    fun binder  ->
      match binder.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable uu____928 -> (env, [])
      | FStar_Parser_AST.TVariable x ->
          let uu____932 = FStar_Syntax_DsEnv.push_bv env x  in
          (match uu____932 with | (env1,uu____944) -> (env1, [x]))
      | FStar_Parser_AST.Annotated (uu____947,term) ->
          let uu____949 = free_type_vars env term  in (env, uu____949)
      | FStar_Parser_AST.TAnnotated (id1,uu____955) ->
          let uu____956 = FStar_Syntax_DsEnv.push_bv env id1  in
          (match uu____956 with | (env1,uu____968) -> (env1, []))
      | FStar_Parser_AST.NoName t ->
          let uu____972 = free_type_vars env t  in (env, uu____972)

and (free_type_vars :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.term -> FStar_Ident.ident Prims.list)
  =
  fun env  ->
    fun t  ->
      let uu____979 =
        let uu____980 = unparen t  in uu____980.FStar_Parser_AST.tm  in
      match uu____979 with
      | FStar_Parser_AST.Labeled uu____983 ->
          failwith "Impossible --- labeled source term"
      | FStar_Parser_AST.Tvar a ->
          let uu____996 = FStar_Syntax_DsEnv.try_lookup_id env a  in
          (match uu____996 with
           | FStar_Pervasives_Native.None  -> [a]
           | uu____1001 -> [])
      | FStar_Parser_AST.Wild  -> []
      | FStar_Parser_AST.Const uu____1004 -> []
      | FStar_Parser_AST.Uvar uu____1005 -> []
      | FStar_Parser_AST.Var uu____1006 -> []
      | FStar_Parser_AST.Projector uu____1007 -> []
      | FStar_Parser_AST.Discrim uu____1012 -> []
      | FStar_Parser_AST.Name uu____1013 -> []
      | FStar_Parser_AST.Requires (t1,uu____1015) -> free_type_vars env t1
      | FStar_Parser_AST.Ensures (t1,uu____1023) -> free_type_vars env t1
      | FStar_Parser_AST.NamedTyp (uu____1030,t1) -> free_type_vars env t1
      | FStar_Parser_AST.Paren t1 -> failwith "impossible"
      | FStar_Parser_AST.Ascribed (t1,t',tacopt) ->
          let ts = t1 :: t' ::
            (match tacopt with
             | FStar_Pervasives_Native.None  -> []
             | FStar_Pervasives_Native.Some t2 -> [t2])
             in
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.Construct (uu____1049,ts) ->
          FStar_List.collect
            (fun uu____1070  ->
               match uu____1070 with
               | (t1,uu____1078) -> free_type_vars env t1) ts
      | FStar_Parser_AST.Op (uu____1079,ts) ->
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.App (t1,t2,uu____1087) ->
          let uu____1088 = free_type_vars env t1  in
          let uu____1091 = free_type_vars env t2  in
          FStar_List.append uu____1088 uu____1091
      | FStar_Parser_AST.Refine (b,t1) ->
          let uu____1096 = free_type_vars_b env b  in
          (match uu____1096 with
           | (env1,f) ->
               let uu____1111 = free_type_vars env1 t1  in
               FStar_List.append f uu____1111)
      | FStar_Parser_AST.Sum (binders,body) ->
          let uu____1128 =
            FStar_List.fold_left
              (fun uu____1152  ->
                 fun bt  ->
                   match uu____1152 with
                   | (env1,free) ->
                       let uu____1176 =
                         match bt with
                         | FStar_Util.Inl binder ->
                             free_type_vars_b env1 binder
                         | FStar_Util.Inr t1 ->
                             let uu____1191 = free_type_vars env1 body  in
                             (env1, uu____1191)
                          in
                       (match uu____1176 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____1128 with
           | (env1,free) ->
               let uu____1220 = free_type_vars env1 body  in
               FStar_List.append free uu____1220)
      | FStar_Parser_AST.Product (binders,body) ->
          let uu____1229 =
            FStar_List.fold_left
              (fun uu____1249  ->
                 fun binder  ->
                   match uu____1249 with
                   | (env1,free) ->
                       let uu____1269 = free_type_vars_b env1 binder  in
                       (match uu____1269 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____1229 with
           | (env1,free) ->
               let uu____1300 = free_type_vars env1 body  in
               FStar_List.append free uu____1300)
      | FStar_Parser_AST.Project (t1,uu____1304) -> free_type_vars env t1
      | FStar_Parser_AST.Attributes cattributes ->
          FStar_List.collect (free_type_vars env) cattributes
      | FStar_Parser_AST.CalcProof (rel,init1,steps) ->
          let uu____1315 = free_type_vars env rel  in
          let uu____1318 =
            let uu____1321 = free_type_vars env init1  in
            let uu____1324 =
              FStar_List.collect
                (fun uu____1333  ->
                   match uu____1333 with
                   | FStar_Parser_AST.CalcStep (rel1,just,next) ->
                       let uu____1339 = free_type_vars env rel1  in
                       let uu____1342 =
                         let uu____1345 = free_type_vars env just  in
                         let uu____1348 = free_type_vars env next  in
                         FStar_List.append uu____1345 uu____1348  in
                       FStar_List.append uu____1339 uu____1342) steps
               in
            FStar_List.append uu____1321 uu____1324  in
          FStar_List.append uu____1315 uu____1318
      | FStar_Parser_AST.Abs uu____1351 -> []
      | FStar_Parser_AST.Let uu____1358 -> []
      | FStar_Parser_AST.LetOpen uu____1379 -> []
      | FStar_Parser_AST.If uu____1384 -> []
      | FStar_Parser_AST.QForall uu____1391 -> []
      | FStar_Parser_AST.QExists uu____1410 -> []
      | FStar_Parser_AST.Record uu____1429 -> []
      | FStar_Parser_AST.Match uu____1442 -> []
      | FStar_Parser_AST.TryWith uu____1457 -> []
      | FStar_Parser_AST.Bind uu____1472 -> []
      | FStar_Parser_AST.Quote uu____1479 -> []
      | FStar_Parser_AST.VQuote uu____1484 -> []
      | FStar_Parser_AST.Antiquote uu____1485 -> []
      | FStar_Parser_AST.Seq uu____1486 -> []

let (head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp)
      Prims.list))
  =
  fun t  ->
    let rec aux args t1 =
      let uu____1540 =
        let uu____1541 = unparen t1  in uu____1541.FStar_Parser_AST.tm  in
      match uu____1540 with
      | FStar_Parser_AST.App (t2,arg,imp) -> aux ((arg, imp) :: args) t2
      | FStar_Parser_AST.Construct (l,args') ->
          ({
             FStar_Parser_AST.tm = (FStar_Parser_AST.Name l);
             FStar_Parser_AST.range = (t1.FStar_Parser_AST.range);
             FStar_Parser_AST.level = (t1.FStar_Parser_AST.level)
           }, (FStar_List.append args' args))
      | uu____1583 -> (t1, args)  in
    aux [] t
  
let (close :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun env  ->
    fun t  ->
      let ftv =
        let uu____1608 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____1608  in
      if (FStar_List.length ftv) = Prims.int_zero
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____1631 =
                     let uu____1632 =
                       let uu____1637 =
                         let uu____1638 = FStar_Ident.range_of_id x  in
                         tm_type uu____1638  in
                       (x, uu____1637)  in
                     FStar_Parser_AST.TAnnotated uu____1632  in
                   let uu____1639 = FStar_Ident.range_of_id x  in
                   FStar_Parser_AST.mk_binder uu____1631 uu____1639
                     FStar_Parser_AST.Type_level
                     (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)))
            in
         let result =
           FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (binders, t))
             t.FStar_Parser_AST.range t.FStar_Parser_AST.level
            in
         result)
  
let (close_fun :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun env  ->
    fun t  ->
      let ftv =
        let uu____1657 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____1657  in
      if (FStar_List.length ftv) = Prims.int_zero
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____1680 =
                     let uu____1681 =
                       let uu____1686 =
                         let uu____1687 = FStar_Ident.range_of_id x  in
                         tm_type uu____1687  in
                       (x, uu____1686)  in
                     FStar_Parser_AST.TAnnotated uu____1681  in
                   let uu____1688 = FStar_Ident.range_of_id x  in
                   FStar_Parser_AST.mk_binder uu____1680 uu____1688
                     FStar_Parser_AST.Type_level
                     (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)))
            in
         let t1 =
           let uu____1690 =
             let uu____1691 = unparen t  in uu____1691.FStar_Parser_AST.tm
              in
           match uu____1690 with
           | FStar_Parser_AST.Product uu____1692 -> t
           | uu____1699 ->
               FStar_Parser_AST.mk_term
                 (FStar_Parser_AST.App
                    ((FStar_Parser_AST.mk_term
                        (FStar_Parser_AST.Name
                           FStar_Parser_Const.effect_Tot_lid)
                        t.FStar_Parser_AST.range t.FStar_Parser_AST.level),
                      t, FStar_Parser_AST.Nothing)) t.FStar_Parser_AST.range
                 t.FStar_Parser_AST.level
            in
         let result =
           FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (binders, t1))
             t1.FStar_Parser_AST.range t1.FStar_Parser_AST.level
            in
         result)
  
let rec (uncurry :
  FStar_Parser_AST.binder Prims.list ->
    FStar_Parser_AST.term ->
      (FStar_Parser_AST.binder Prims.list * FStar_Parser_AST.term))
  =
  fun bs  ->
    fun t  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (binders,t1) ->
          uncurry (FStar_List.append bs binders) t1
      | uu____1736 -> (bs, t)
  
let rec (is_var_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatWild uu____1747 -> true
    | FStar_Parser_AST.PatTvar (uu____1751,uu____1752) -> true
    | FStar_Parser_AST.PatVar (uu____1758,uu____1759) -> true
    | FStar_Parser_AST.PatAscribed (p1,uu____1766) -> is_var_pattern p1
    | uu____1779 -> false
  
let rec (is_app_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (p1,uu____1790) -> is_app_pattern p1
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu____1803;
           FStar_Parser_AST.prange = uu____1804;_},uu____1805)
        -> true
    | uu____1817 -> false
  
let (replace_unit_pattern :
  FStar_Parser_AST.pattern -> FStar_Parser_AST.pattern) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatConst (FStar_Const.Const_unit ) ->
        FStar_Parser_AST.mk_pattern
          (FStar_Parser_AST.PatAscribed
             ((FStar_Parser_AST.mk_pattern
                 (FStar_Parser_AST.PatWild FStar_Pervasives_Native.None)
                 p.FStar_Parser_AST.prange),
               (unit_ty, FStar_Pervasives_Native.None)))
          p.FStar_Parser_AST.prange
    | uu____1833 -> p
  
let rec (destruct_app_pattern :
  FStar_Syntax_DsEnv.env ->
    Prims.bool ->
      FStar_Parser_AST.pattern ->
        ((FStar_Ident.ident,FStar_Ident.lident) FStar_Util.either *
          FStar_Parser_AST.pattern Prims.list * (FStar_Parser_AST.term *
          FStar_Parser_AST.term FStar_Pervasives_Native.option)
          FStar_Pervasives_Native.option))
  =
  fun env  ->
    fun is_top_level1  ->
      fun p  ->
        match p.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatAscribed (p1,t) ->
            let uu____1906 = destruct_app_pattern env is_top_level1 p1  in
            (match uu____1906 with
             | (name,args,uu____1949) ->
                 (name, args, (FStar_Pervasives_Native.Some t)))
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____1999);
               FStar_Parser_AST.prange = uu____2000;_},args)
            when is_top_level1 ->
            let uu____2010 =
              let uu____2015 = FStar_Syntax_DsEnv.qualify env id1  in
              FStar_Util.Inr uu____2015  in
            (uu____2010, args, FStar_Pervasives_Native.None)
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____2037);
               FStar_Parser_AST.prange = uu____2038;_},args)
            -> ((FStar_Util.Inl id1), args, FStar_Pervasives_Native.None)
        | uu____2068 -> failwith "Not an app pattern"
  
let rec (gather_pattern_bound_vars_maybe_top :
  FStar_Ident.ident FStar_Util.set ->
    FStar_Parser_AST.pattern -> FStar_Ident.ident FStar_Util.set)
  =
  fun acc  ->
    fun p  ->
      let gather_pattern_bound_vars_from_list =
        FStar_List.fold_left gather_pattern_bound_vars_maybe_top acc  in
      match p.FStar_Parser_AST.pat with
      | FStar_Parser_AST.PatWild uu____2120 -> acc
      | FStar_Parser_AST.PatConst uu____2123 -> acc
      | FStar_Parser_AST.PatName uu____2124 -> acc
      | FStar_Parser_AST.PatOp uu____2125 -> acc
      | FStar_Parser_AST.PatApp (phead,pats) ->
          gather_pattern_bound_vars_from_list (phead :: pats)
      | FStar_Parser_AST.PatTvar (x,uu____2133) -> FStar_Util.set_add x acc
      | FStar_Parser_AST.PatVar (x,uu____2139) -> FStar_Util.set_add x acc
      | FStar_Parser_AST.PatList pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatTuple (pats,uu____2148) ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatOr pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatRecord guarded_pats ->
          let uu____2165 =
            FStar_List.map FStar_Pervasives_Native.snd guarded_pats  in
          gather_pattern_bound_vars_from_list uu____2165
      | FStar_Parser_AST.PatAscribed (pat,uu____2173) ->
          gather_pattern_bound_vars_maybe_top acc pat
  
let (gather_pattern_bound_vars :
  FStar_Parser_AST.pattern -> FStar_Ident.ident FStar_Util.set) =
  let acc =
    FStar_Util.new_set
      (fun id1  ->
         fun id2  ->
           let uu____2201 =
             let uu____2203 = FStar_Ident.text_of_id id1  in
             let uu____2205 = FStar_Ident.text_of_id id2  in
             uu____2203 = uu____2205  in
           if uu____2201 then Prims.int_zero else Prims.int_one)
     in
  fun p  -> gather_pattern_bound_vars_maybe_top acc p 
type bnd =
  | LocalBinder of (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) 
  | LetBinder of (FStar_Ident.lident * (FStar_Syntax_Syntax.term *
  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)) 
let (uu___is_LocalBinder : bnd -> Prims.bool) =
  fun projectee  ->
    match projectee with | LocalBinder _0 -> true | uu____2253 -> false
  
let (__proj__LocalBinder__item___0 :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)) =
  fun projectee  -> match projectee with | LocalBinder _0 -> _0 
let (uu___is_LetBinder : bnd -> Prims.bool) =
  fun projectee  ->
    match projectee with | LetBinder _0 -> true | uu____2294 -> false
  
let (__proj__LetBinder__item___0 :
  bnd ->
    (FStar_Ident.lident * (FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)))
  = fun projectee  -> match projectee with | LetBinder _0 -> _0 
let (is_implicit : bnd -> Prims.bool) =
  fun b  ->
    match b with
    | LocalBinder
        (uu____2342,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____2343))
        -> true
    | uu____2346 -> false
  
let (binder_of_bnd :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)) =
  fun uu___3_2357  ->
    match uu___3_2357 with
    | LocalBinder (a,aq) -> (a, aq)
    | uu____2364 -> failwith "Impossible"
  
let (mk_lb :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list *
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Range.range)
    -> FStar_Syntax_Syntax.letbinding)
  =
  fun uu____2397  ->
    match uu____2397 with
    | (attrs,n1,t,e,pos) ->
        {
          FStar_Syntax_Syntax.lbname = n1;
          FStar_Syntax_Syntax.lbunivs = [];
          FStar_Syntax_Syntax.lbtyp = t;
          FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_ALL_lid;
          FStar_Syntax_Syntax.lbdef = e;
          FStar_Syntax_Syntax.lbattrs = attrs;
          FStar_Syntax_Syntax.lbpos = pos
        }
  
let (no_annot_abs :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun bs  ->
    fun t  -> FStar_Syntax_Util.abs bs t FStar_Pervasives_Native.None
  
let (mk_ref_read :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun tm  ->
    let tm' =
      let uu____2479 =
        let uu____2496 =
          let uu____2499 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____2499  in
        let uu____2500 =
          let uu____2511 =
            let uu____2520 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____2520)  in
          [uu____2511]  in
        (uu____2496, uu____2500)  in
      FStar_Syntax_Syntax.Tm_app uu____2479  in
    FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
      tm.FStar_Syntax_Syntax.pos
  
let (mk_ref_alloc :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun tm  ->
    let tm' =
      let uu____2569 =
        let uu____2586 =
          let uu____2589 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.salloc_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____2589  in
        let uu____2590 =
          let uu____2601 =
            let uu____2610 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____2610)  in
          [uu____2601]  in
        (uu____2586, uu____2590)  in
      FStar_Syntax_Syntax.Tm_app uu____2569  in
    FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
      tm.FStar_Syntax_Syntax.pos
  
let (mk_ref_assign :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Range.range ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
      fun pos  ->
        let tm =
          let uu____2673 =
            let uu____2690 =
              let uu____2693 =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.swrite_lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____2693  in
            let uu____2694 =
              let uu____2705 =
                let uu____2714 = FStar_Syntax_Syntax.as_implicit false  in
                (t1, uu____2714)  in
              let uu____2722 =
                let uu____2733 =
                  let uu____2742 = FStar_Syntax_Syntax.as_implicit false  in
                  (t2, uu____2742)  in
                [uu____2733]  in
              uu____2705 :: uu____2722  in
            (uu____2690, uu____2694)  in
          FStar_Syntax_Syntax.Tm_app uu____2673  in
        FStar_Syntax_Syntax.mk tm FStar_Pervasives_Native.None pos
  
let rec (generalize_annotated_univs :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt) =
  fun s  ->
    let bs_univnames bs =
      let uu____2802 =
        let uu____2817 =
          FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name  in
        FStar_List.fold_left
          (fun uvs  ->
             fun uu____2836  ->
               match uu____2836 with
               | ({ FStar_Syntax_Syntax.ppname = uu____2847;
                    FStar_Syntax_Syntax.index = uu____2848;
                    FStar_Syntax_Syntax.sort = t;_},uu____2850)
                   ->
                   let uu____2858 = FStar_Syntax_Free.univnames t  in
                   FStar_Util.set_union uvs uu____2858) uu____2817
         in
      FStar_All.pipe_right bs uu____2802  in
    let empty_set = FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name
       in
    match s.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____2874 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_datacon uu____2892 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
        let uvs =
          let uu____2920 =
            FStar_All.pipe_right sigs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun se  ->
                      let se_univs =
                        match se.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_inductive_typ
                            (uu____2941,uu____2942,bs,t,uu____2945,uu____2946)
                            ->
                            let uu____2955 = bs_univnames bs  in
                            let uu____2958 = FStar_Syntax_Free.univnames t
                               in
                            FStar_Util.set_union uu____2955 uu____2958
                        | FStar_Syntax_Syntax.Sig_datacon
                            (uu____2961,uu____2962,t,uu____2964,uu____2965,uu____2966)
                            -> FStar_Syntax_Free.univnames t
                        | uu____2973 ->
                            failwith
                              "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"
                         in
                      FStar_Util.set_union uvs se_univs) empty_set)
             in
          FStar_All.pipe_right uu____2920 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___589_2982 = s  in
        let uu____2983 =
          let uu____2984 =
            let uu____2993 =
              FStar_All.pipe_right sigs
                (FStar_List.map
                   (fun se  ->
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_inductive_typ
                          (lid,uu____3011,bs,t,lids1,lids2) ->
                          let uu___600_3024 = se  in
                          let uu____3025 =
                            let uu____3026 =
                              let uu____3043 =
                                FStar_Syntax_Subst.subst_binders usubst bs
                                 in
                              let uu____3044 =
                                let uu____3045 =
                                  FStar_Syntax_Subst.shift_subst
                                    (FStar_List.length bs) usubst
                                   in
                                FStar_Syntax_Subst.subst uu____3045 t  in
                              (lid, uvs, uu____3043, uu____3044, lids1,
                                lids2)
                               in
                            FStar_Syntax_Syntax.Sig_inductive_typ uu____3026
                             in
                          {
                            FStar_Syntax_Syntax.sigel = uu____3025;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___600_3024.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___600_3024.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___600_3024.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___600_3024.FStar_Syntax_Syntax.sigattrs);
                            FStar_Syntax_Syntax.sigopts =
                              (uu___600_3024.FStar_Syntax_Syntax.sigopts)
                          }
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid,uu____3059,t,tlid,n1,lids1) ->
                          let uu___610_3070 = se  in
                          let uu____3071 =
                            let uu____3072 =
                              let uu____3088 =
                                FStar_Syntax_Subst.subst usubst t  in
                              (lid, uvs, uu____3088, tlid, n1, lids1)  in
                            FStar_Syntax_Syntax.Sig_datacon uu____3072  in
                          {
                            FStar_Syntax_Syntax.sigel = uu____3071;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___610_3070.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___610_3070.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___610_3070.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___610_3070.FStar_Syntax_Syntax.sigattrs);
                            FStar_Syntax_Syntax.sigopts =
                              (uu___610_3070.FStar_Syntax_Syntax.sigopts)
                          }
                      | uu____3092 ->
                          failwith
                            "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"))
               in
            (uu____2993, lids)  in
          FStar_Syntax_Syntax.Sig_bundle uu____2984  in
        {
          FStar_Syntax_Syntax.sigel = uu____2983;
          FStar_Syntax_Syntax.sigrng =
            (uu___589_2982.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___589_2982.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___589_2982.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___589_2982.FStar_Syntax_Syntax.sigattrs);
          FStar_Syntax_Syntax.sigopts =
            (uu___589_2982.FStar_Syntax_Syntax.sigopts)
        }
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____3099,t) ->
        let uvs =
          let uu____3102 = FStar_Syntax_Free.univnames t  in
          FStar_All.pipe_right uu____3102 FStar_Util.set_elements  in
        let uu___619_3107 = s  in
        let uu____3108 =
          let uu____3109 =
            let uu____3116 = FStar_Syntax_Subst.close_univ_vars uvs t  in
            (lid, uvs, uu____3116)  in
          FStar_Syntax_Syntax.Sig_declare_typ uu____3109  in
        {
          FStar_Syntax_Syntax.sigel = uu____3108;
          FStar_Syntax_Syntax.sigrng =
            (uu___619_3107.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___619_3107.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___619_3107.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___619_3107.FStar_Syntax_Syntax.sigattrs);
          FStar_Syntax_Syntax.sigopts =
            (uu___619_3107.FStar_Syntax_Syntax.sigopts)
        }
    | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
        let lb_univnames lb =
          let uu____3140 =
            FStar_Syntax_Free.univnames lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____3143 =
            match (lb.FStar_Syntax_Syntax.lbdef).FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs (bs,e,uu____3150) ->
                let uvs1 = bs_univnames bs  in
                let uvs2 =
                  match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____3183,(FStar_Util.Inl t,uu____3185),uu____3186)
                      -> FStar_Syntax_Free.univnames t
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____3233,(FStar_Util.Inr c,uu____3235),uu____3236)
                      -> FStar_Syntax_Free.univnames_comp c
                  | uu____3283 -> empty_set  in
                FStar_Util.set_union uvs1 uvs2
            | FStar_Syntax_Syntax.Tm_arrow (bs,uu____3285) -> bs_univnames bs
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____3306,(FStar_Util.Inl t,uu____3308),uu____3309) ->
                FStar_Syntax_Free.univnames t
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____3356,(FStar_Util.Inr c,uu____3358),uu____3359) ->
                FStar_Syntax_Free.univnames_comp c
            | uu____3406 -> empty_set  in
          FStar_Util.set_union uu____3140 uu____3143  in
        let all_lb_univs =
          let uu____3410 =
            FStar_All.pipe_right lbs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun lb  ->
                      let uu____3426 = lb_univnames lb  in
                      FStar_Util.set_union uvs uu____3426) empty_set)
             in
          FStar_All.pipe_right uu____3410 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing all_lb_univs  in
        let uu___678_3436 = s  in
        let uu____3437 =
          let uu____3438 =
            let uu____3445 =
              let uu____3446 =
                FStar_All.pipe_right lbs
                  (FStar_List.map
                     (fun lb  ->
                        let uu___681_3458 = lb  in
                        let uu____3459 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____3462 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___681_3458.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = all_lb_univs;
                          FStar_Syntax_Syntax.lbtyp = uu____3459;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___681_3458.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____3462;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___681_3458.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___681_3458.FStar_Syntax_Syntax.lbpos)
                        }))
                 in
              (b, uu____3446)  in
            (uu____3445, lids)  in
          FStar_Syntax_Syntax.Sig_let uu____3438  in
        {
          FStar_Syntax_Syntax.sigel = uu____3437;
          FStar_Syntax_Syntax.sigrng =
            (uu___678_3436.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___678_3436.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___678_3436.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___678_3436.FStar_Syntax_Syntax.sigattrs);
          FStar_Syntax_Syntax.sigopts =
            (uu___678_3436.FStar_Syntax_Syntax.sigopts)
        }
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____3471,fml) ->
        let uvs =
          let uu____3474 = FStar_Syntax_Free.univnames fml  in
          FStar_All.pipe_right uu____3474 FStar_Util.set_elements  in
        let uu___689_3479 = s  in
        let uu____3480 =
          let uu____3481 =
            let uu____3488 = FStar_Syntax_Subst.close_univ_vars uvs fml  in
            (lid, uvs, uu____3488)  in
          FStar_Syntax_Syntax.Sig_assume uu____3481  in
        {
          FStar_Syntax_Syntax.sigel = uu____3480;
          FStar_Syntax_Syntax.sigrng =
            (uu___689_3479.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___689_3479.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___689_3479.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___689_3479.FStar_Syntax_Syntax.sigattrs);
          FStar_Syntax_Syntax.sigopts =
            (uu___689_3479.FStar_Syntax_Syntax.sigopts)
        }
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uu____3490,bs,c,flags) ->
        let uvs =
          let uu____3499 =
            let uu____3502 = bs_univnames bs  in
            let uu____3505 = FStar_Syntax_Free.univnames_comp c  in
            FStar_Util.set_union uu____3502 uu____3505  in
          FStar_All.pipe_right uu____3499 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___700_3513 = s  in
        let uu____3514 =
          let uu____3515 =
            let uu____3528 = FStar_Syntax_Subst.subst_binders usubst bs  in
            let uu____3529 = FStar_Syntax_Subst.subst_comp usubst c  in
            (lid, uvs, uu____3528, uu____3529, flags)  in
          FStar_Syntax_Syntax.Sig_effect_abbrev uu____3515  in
        {
          FStar_Syntax_Syntax.sigel = uu____3514;
          FStar_Syntax_Syntax.sigrng =
            (uu___700_3513.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___700_3513.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___700_3513.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___700_3513.FStar_Syntax_Syntax.sigattrs);
          FStar_Syntax_Syntax.sigopts =
            (uu___700_3513.FStar_Syntax_Syntax.sigopts)
        }
    | FStar_Syntax_Syntax.Sig_fail (errs,lax1,ses) ->
        let uu___707_3547 = s  in
        let uu____3548 =
          let uu____3549 =
            let uu____3562 = FStar_List.map generalize_annotated_univs ses
               in
            (errs, lax1, uu____3562)  in
          FStar_Syntax_Syntax.Sig_fail uu____3549  in
        {
          FStar_Syntax_Syntax.sigel = uu____3548;
          FStar_Syntax_Syntax.sigrng =
            (uu___707_3547.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___707_3547.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___707_3547.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___707_3547.FStar_Syntax_Syntax.sigattrs);
          FStar_Syntax_Syntax.sigopts =
            (uu___707_3547.FStar_Syntax_Syntax.sigopts)
        }
    | FStar_Syntax_Syntax.Sig_new_effect uu____3571 -> s
    | FStar_Syntax_Syntax.Sig_sub_effect uu____3572 -> s
    | FStar_Syntax_Syntax.Sig_main uu____3573 -> s
    | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____3574 -> s
    | FStar_Syntax_Syntax.Sig_splice uu____3585 -> s
    | FStar_Syntax_Syntax.Sig_pragma uu____3592 -> s
  
let (is_special_effect_combinator : Prims.string -> Prims.bool) =
  fun uu___4_3600  ->
    match uu___4_3600 with
    | "lift1" -> true
    | "lift2" -> true
    | "pure" -> true
    | "app" -> true
    | "push" -> true
    | "wp_if_then_else" -> true
    | "wp_assert" -> true
    | "wp_assume" -> true
    | "wp_close" -> true
    | "stronger" -> true
    | "ite_wp" -> true
    | "wp_trivial" -> true
    | "ctx" -> true
    | "gctx" -> true
    | "lift_from_pure" -> true
    | "return_wp" -> true
    | "return_elab" -> true
    | "bind_wp" -> true
    | "bind_elab" -> true
    | "repr" -> true
    | "post" -> true
    | "pre" -> true
    | "wp" -> true
    | uu____3649 -> false
  
let rec (sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe)
  =
  fun u  ->
    fun n1  ->
      if n1 = Prims.int_zero
      then u
      else
        (let uu____3670 = sum_to_universe u (n1 - Prims.int_one)  in
         FStar_Syntax_Syntax.U_succ uu____3670)
  
let (int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe) =
  fun n1  -> sum_to_universe FStar_Syntax_Syntax.U_zero n1 
let rec (desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either)
  =
  fun t  ->
    let uu____3696 =
      let uu____3697 = unparen t  in uu____3697.FStar_Parser_AST.tm  in
    match uu____3696 with
    | FStar_Parser_AST.Wild  ->
        let uu____3703 =
          let uu____3704 = FStar_Syntax_Unionfind.univ_fresh ()  in
          FStar_Syntax_Syntax.U_unif uu____3704  in
        FStar_Util.Inr uu____3703
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____3717)) ->
        let n1 = FStar_Util.int_of_string repr  in
        (if n1 < Prims.int_zero
         then
           FStar_Errors.raise_error
             (FStar_Errors.Fatal_NegativeUniverseConstFatal_NotSupported,
               (Prims.op_Hat
                  "Negative universe constant  are not supported : " repr))
             t.FStar_Parser_AST.range
         else ();
         FStar_Util.Inl n1)
    | FStar_Parser_AST.Op (op_plus,t1::t2::[]) ->
        let u1 = desugar_maybe_non_constant_universe t1  in
        let u2 = desugar_maybe_non_constant_universe t2  in
        (match (u1, u2) with
         | (FStar_Util.Inl n1,FStar_Util.Inl n2) -> FStar_Util.Inl (n1 + n2)
         | (FStar_Util.Inl n1,FStar_Util.Inr u) ->
             let uu____3808 = sum_to_universe u n1  in
             FStar_Util.Inr uu____3808
         | (FStar_Util.Inr u,FStar_Util.Inl n1) ->
             let uu____3825 = sum_to_universe u n1  in
             FStar_Util.Inr uu____3825
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____3841 =
               let uu____3847 =
                 let uu____3849 = FStar_Parser_AST.term_to_string t  in
                 Prims.op_Hat
                   "This universe might contain a sum of two universe variables "
                   uu____3849
                  in
               (FStar_Errors.Fatal_UniverseMightContainSumOfTwoUnivVars,
                 uu____3847)
                in
             FStar_Errors.raise_error uu____3841 t.FStar_Parser_AST.range)
    | FStar_Parser_AST.App uu____3858 ->
        let rec aux t1 univargs =
          let uu____3895 =
            let uu____3896 = unparen t1  in uu____3896.FStar_Parser_AST.tm
             in
          match uu____3895 with
          | FStar_Parser_AST.App (t2,targ,uu____3904) ->
              let uarg = desugar_maybe_non_constant_universe targ  in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              if
                FStar_List.existsb
                  (fun uu___5_3931  ->
                     match uu___5_3931 with
                     | FStar_Util.Inr uu____3938 -> true
                     | uu____3941 -> false) univargs
              then
                let uu____3949 =
                  let uu____3950 =
                    FStar_List.map
                      (fun uu___6_3960  ->
                         match uu___6_3960 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs
                     in
                  FStar_Syntax_Syntax.U_max uu____3950  in
                FStar_Util.Inr uu____3949
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___7_3986  ->
                        match uu___7_3986 with
                        | FStar_Util.Inl n1 -> n1
                        | FStar_Util.Inr uu____3996 -> failwith "impossible")
                     univargs
                    in
                 let uu____4000 =
                   FStar_List.fold_left
                     (fun m  -> fun n1  -> if m > n1 then m else n1)
                     Prims.int_zero nargs
                    in
                 FStar_Util.Inl uu____4000)
          | uu____4016 ->
              let uu____4017 =
                let uu____4023 =
                  let uu____4025 =
                    let uu____4027 = FStar_Parser_AST.term_to_string t1  in
                    Prims.op_Hat uu____4027 " in universe context"  in
                  Prims.op_Hat "Unexpected term " uu____4025  in
                (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____4023)  in
              FStar_Errors.raise_error uu____4017 t1.FStar_Parser_AST.range
           in
        aux t []
    | uu____4042 ->
        let uu____4043 =
          let uu____4049 =
            let uu____4051 =
              let uu____4053 = FStar_Parser_AST.term_to_string t  in
              Prims.op_Hat uu____4053 " in universe context"  in
            Prims.op_Hat "Unexpected term " uu____4051  in
          (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____4049)  in
        FStar_Errors.raise_error uu____4043 t.FStar_Parser_AST.range
  
let (desugar_universe :
  FStar_Parser_AST.term -> FStar_Syntax_Syntax.universe) =
  fun t  ->
    let u = desugar_maybe_non_constant_universe t  in
    match u with
    | FStar_Util.Inl n1 -> int_to_universe n1
    | FStar_Util.Inr u1 -> u1
  
let (check_no_aq : FStar_Syntax_Syntax.antiquotations -> unit) =
  fun aq  ->
    match aq with
    | [] -> ()
    | (bv,{
            FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_quoted
              (e,{
                   FStar_Syntax_Syntax.qkind =
                     FStar_Syntax_Syntax.Quote_dynamic ;
                   FStar_Syntax_Syntax.antiquotes = uu____4094;_});
            FStar_Syntax_Syntax.pos = uu____4095;
            FStar_Syntax_Syntax.vars = uu____4096;_})::uu____4097
        ->
        let uu____4128 =
          let uu____4134 =
            let uu____4136 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `@(%s)" uu____4136
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____4134)  in
        FStar_Errors.raise_error uu____4128 e.FStar_Syntax_Syntax.pos
    | (bv,e)::uu____4142 ->
        let uu____4161 =
          let uu____4167 =
            let uu____4169 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `#(%s)" uu____4169
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____4167)  in
        FStar_Errors.raise_error uu____4161 e.FStar_Syntax_Syntax.pos
  
let check_fields :
  'Auu____4182 .
    FStar_Syntax_DsEnv.env ->
      (FStar_Ident.lident * 'Auu____4182) Prims.list ->
        FStar_Range.range -> FStar_Syntax_DsEnv.record_or_dc
  =
  fun env  ->
    fun fields  ->
      fun rg  ->
        let uu____4210 = FStar_List.hd fields  in
        match uu____4210 with
        | (f,uu____4220) ->
            let record =
              FStar_Syntax_DsEnv.fail_or env
                (FStar_Syntax_DsEnv.try_lookup_record_by_field_name env) f
               in
            let check_field uu____4231 =
              match uu____4231 with
              | (f',uu____4237) ->
                  let uu____4238 =
                    FStar_Syntax_DsEnv.belongs_to_record env f' record  in
                  if uu____4238
                  then ()
                  else
                    (let msg =
                       let uu____4245 = FStar_Ident.string_of_lid f  in
                       let uu____4247 =
                         FStar_Ident.string_of_lid
                           record.FStar_Syntax_DsEnv.typename
                          in
                       let uu____4249 = FStar_Ident.string_of_lid f'  in
                       FStar_Util.format3
                         "Field %s belongs to record type %s, whereas field %s does not"
                         uu____4245 uu____4247 uu____4249
                        in
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_FieldsNotBelongToSameRecordType,
                         msg) rg)
               in
            ((let uu____4254 = FStar_List.tl fields  in
              FStar_List.iter check_field uu____4254);
             (match () with | () -> record))
  
let (check_linear_pattern_variables :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t Prims.list ->
    FStar_Range.range -> unit)
  =
  fun pats  ->
    fun r  ->
      let rec pat_vars p =
        match p.FStar_Syntax_Syntax.v with
        | FStar_Syntax_Syntax.Pat_dot_term uu____4302 ->
            FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_wild uu____4309 ->
            FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_constant uu____4310 ->
            FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_var x ->
            FStar_Util.set_add x FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_cons (uu____4312,pats1) ->
            let aux out uu____4353 =
              match uu____4353 with
              | (p1,uu____4366) ->
                  let intersection =
                    let uu____4376 = pat_vars p1  in
                    FStar_Util.set_intersect uu____4376 out  in
                  let uu____4379 = FStar_Util.set_is_empty intersection  in
                  if uu____4379
                  then
                    let uu____4384 = pat_vars p1  in
                    FStar_Util.set_union out uu____4384
                  else
                    (let duplicate_bv =
                       let uu____4390 = FStar_Util.set_elements intersection
                          in
                       FStar_List.hd uu____4390  in
                     let uu____4393 =
                       let uu____4399 =
                         let uu____4401 =
                           FStar_Ident.text_of_id
                             duplicate_bv.FStar_Syntax_Syntax.ppname
                            in
                         FStar_Util.format1
                           "Non-linear patterns are not permitted: `%s` appears more than once in this pattern."
                           uu____4401
                          in
                       (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                         uu____4399)
                        in
                     FStar_Errors.raise_error uu____4393 r)
               in
            FStar_List.fold_left aux FStar_Syntax_Syntax.no_names pats1
         in
      match pats with
      | [] -> ()
      | p::[] ->
          let uu____4425 = pat_vars p  in
          FStar_All.pipe_right uu____4425 (fun a1  -> ())
      | p::ps ->
          let pvars = pat_vars p  in
          let aux p1 =
            let uu____4453 =
              let uu____4455 = pat_vars p1  in
              FStar_Util.set_eq pvars uu____4455  in
            if uu____4453
            then ()
            else
              (let nonlinear_vars =
                 let uu____4464 = pat_vars p1  in
                 FStar_Util.set_symmetric_difference pvars uu____4464  in
               let first_nonlinear_var =
                 let uu____4468 = FStar_Util.set_elements nonlinear_vars  in
                 FStar_List.hd uu____4468  in
               let uu____4471 =
                 let uu____4477 =
                   let uu____4479 =
                     FStar_Ident.text_of_id
                       first_nonlinear_var.FStar_Syntax_Syntax.ppname
                      in
                   FStar_Util.format1
                     "Patterns in this match are incoherent, variable %s is bound in some but not all patterns."
                     uu____4479
                    in
                 (FStar_Errors.Fatal_IncoherentPatterns, uu____4477)  in
               FStar_Errors.raise_error uu____4471 r)
             in
          FStar_List.iter aux ps
  
let (smt_pat_lid : FStar_Range.range -> FStar_Ident.lident) =
  fun r  -> FStar_Ident.set_lid_range FStar_Parser_Const.smtpat_lid r 
let (smt_pat_or_lid : FStar_Range.range -> FStar_Ident.lident) =
  fun r  -> FStar_Ident.set_lid_range FStar_Parser_Const.smtpatOr_lid r 
let rec (desugar_data_pat :
  Prims.bool ->
    env_t ->
      FStar_Parser_AST.pattern -> (env_t * bnd * annotated_pat Prims.list))
  =
  fun top_level_ascr_allowed  ->
    fun env  ->
      fun p  ->
        let resolvex l e x =
          let uu____4806 =
            FStar_Util.find_opt
              (fun y  ->
                 let uu____4813 =
                   FStar_Ident.text_of_id y.FStar_Syntax_Syntax.ppname  in
                 let uu____4815 = FStar_Ident.text_of_id x  in
                 uu____4813 = uu____4815) l
             in
          match uu____4806 with
          | FStar_Pervasives_Native.Some y -> (l, e, y)
          | uu____4829 ->
              let uu____4832 = FStar_Syntax_DsEnv.push_bv e x  in
              (match uu____4832 with | (e1,x1) -> ((x1 :: l), e1, x1))
           in
        let rec aux' top loc env1 p1 =
          let pos q =
            FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange  in
          let pos_r r q = FStar_Syntax_Syntax.withinfo q r  in
          let orig = p1  in
          match p1.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOr uu____4973 ->
              failwith "impossible: PatOr handled below"
          | FStar_Parser_AST.PatOp op ->
              let id_op =
                let uu____4995 =
                  let uu____5001 =
                    let uu____5003 = FStar_Ident.text_of_id op  in
                    let uu____5005 = FStar_Ident.range_of_id op  in
                    FStar_Parser_AST.compile_op Prims.int_zero uu____5003
                      uu____5005
                     in
                  let uu____5007 = FStar_Ident.range_of_id op  in
                  (uu____5001, uu____5007)  in
                FStar_Ident.mk_ident uu____4995  in
              let p2 =
                let uu___934_5010 = p1  in
                {
                  FStar_Parser_AST.pat =
                    (FStar_Parser_AST.PatVar
                       (id_op, FStar_Pervasives_Native.None));
                  FStar_Parser_AST.prange =
                    (uu___934_5010.FStar_Parser_AST.prange)
                }  in
              aux loc env1 p2
          | FStar_Parser_AST.PatAscribed (p2,(t,tacopt)) ->
              ((match tacopt with
                | FStar_Pervasives_Native.None  -> ()
                | FStar_Pervasives_Native.Some uu____5027 ->
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                        "Type ascriptions within patterns cannot be associated with a tactic")
                      orig.FStar_Parser_AST.prange);
               (let uu____5030 = aux loc env1 p2  in
                match uu____5030 with
                | (loc1,env',binder,p3,annots) ->
                    let uu____5086 =
                      match binder with
                      | LetBinder uu____5107 -> failwith "impossible"
                      | LocalBinder (x,aq) ->
                          let t1 =
                            let uu____5132 = close_fun env1 t  in
                            desugar_term env1 uu____5132  in
                          let x1 =
                            let uu___960_5134 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___960_5134.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___960_5134.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }  in
                          ([(x1, t1)], (LocalBinder (x1, aq)))
                       in
                    (match uu____5086 with
                     | (annots',binder1) ->
                         ((match p3.FStar_Syntax_Syntax.v with
                           | FStar_Syntax_Syntax.Pat_var uu____5180 -> ()
                           | FStar_Syntax_Syntax.Pat_wild uu____5181 -> ()
                           | uu____5182 when top && top_level_ascr_allowed ->
                               ()
                           | uu____5183 ->
                               FStar_Errors.raise_error
                                 (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                                   "Type ascriptions within patterns are only allowed on variables")
                                 orig.FStar_Parser_AST.prange);
                          (loc1, env', binder1, p3,
                            (FStar_List.append annots' annots))))))
          | FStar_Parser_AST.PatWild aq ->
              let aq1 = trans_aqual env1 aq  in
              let x =
                FStar_Syntax_Syntax.new_bv
                  (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                  FStar_Syntax_Syntax.tun
                 in
              let uu____5201 =
                FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
              (loc, env1, (LocalBinder (x, aq1)), uu____5201, [])
          | FStar_Parser_AST.PatConst c ->
              let x =
                FStar_Syntax_Syntax.new_bv
                  (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                  FStar_Syntax_Syntax.tun
                 in
              let uu____5214 =
                FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
                 in
              (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                uu____5214, [])
          | FStar_Parser_AST.PatTvar (x,aq) ->
              let aq1 = trans_aqual env1 aq  in
              let uu____5232 = resolvex loc env1 x  in
              (match uu____5232 with
               | (loc1,env2,xbv) ->
                   let uu____5264 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_var xbv)
                      in
                   (loc1, env2, (LocalBinder (xbv, aq1)), uu____5264, []))
          | FStar_Parser_AST.PatVar (x,aq) ->
              let aq1 = trans_aqual env1 aq  in
              let uu____5282 = resolvex loc env1 x  in
              (match uu____5282 with
               | (loc1,env2,xbv) ->
                   let uu____5314 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_var xbv)
                      in
                   (loc1, env2, (LocalBinder (xbv, aq1)), uu____5314, []))
          | FStar_Parser_AST.PatName l ->
              let l1 =
                FStar_Syntax_DsEnv.fail_or env1
                  (FStar_Syntax_DsEnv.try_lookup_datacon env1) l
                 in
              let x =
                FStar_Syntax_Syntax.new_bv
                  (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                  FStar_Syntax_Syntax.tun
                 in
              let uu____5328 =
                FStar_All.pipe_left pos
                  (FStar_Syntax_Syntax.Pat_cons (l1, []))
                 in
              (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                uu____5328, [])
          | FStar_Parser_AST.PatApp
              ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
                 FStar_Parser_AST.prange = uu____5356;_},args)
              ->
              let uu____5362 =
                FStar_List.fold_right
                  (fun arg  ->
                     fun uu____5423  ->
                       match uu____5423 with
                       | (loc1,env2,annots,args1) ->
                           let uu____5504 = aux loc1 env2 arg  in
                           (match uu____5504 with
                            | (loc2,env3,b,arg1,ans) ->
                                let imp = is_implicit b  in
                                (loc2, env3, (FStar_List.append ans annots),
                                  ((arg1, imp) :: args1)))) args
                  (loc, env1, [], [])
                 in
              (match uu____5362 with
               | (loc1,env2,annots,args1) ->
                   let l1 =
                     FStar_Syntax_DsEnv.fail_or env2
                       (FStar_Syntax_DsEnv.try_lookup_datacon env2) l
                      in
                   let x =
                     FStar_Syntax_Syntax.new_bv
                       (FStar_Pervasives_Native.Some
                          (p1.FStar_Parser_AST.prange))
                       FStar_Syntax_Syntax.tun
                      in
                   let uu____5676 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                      in
                   (loc1, env2,
                     (LocalBinder (x, FStar_Pervasives_Native.None)),
                     uu____5676, annots))
          | FStar_Parser_AST.PatApp uu____5692 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
                p1.FStar_Parser_AST.prange
          | FStar_Parser_AST.PatList pats ->
              let uu____5720 =
                FStar_List.fold_right
                  (fun pat  ->
                     fun uu____5770  ->
                       match uu____5770 with
                       | (loc1,env2,annots,pats1) ->
                           let uu____5831 = aux loc1 env2 pat  in
                           (match uu____5831 with
                            | (loc2,env3,uu____5870,pat1,ans) ->
                                (loc2, env3, (FStar_List.append ans annots),
                                  (pat1 :: pats1)))) pats (loc, env1, [], [])
                 in
              (match uu____5720 with
               | (loc1,env2,annots,pats1) ->
                   let pat =
                     let uu____5964 =
                       let uu____5967 =
                         let uu____5974 =
                           FStar_Range.end_range p1.FStar_Parser_AST.prange
                            in
                         pos_r uu____5974  in
                       let uu____5975 =
                         let uu____5976 =
                           let uu____5990 =
                             FStar_Syntax_Syntax.lid_as_fv
                               FStar_Parser_Const.nil_lid
                               FStar_Syntax_Syntax.delta_constant
                               (FStar_Pervasives_Native.Some
                                  FStar_Syntax_Syntax.Data_ctor)
                              in
                           (uu____5990, [])  in
                         FStar_Syntax_Syntax.Pat_cons uu____5976  in
                       FStar_All.pipe_left uu____5967 uu____5975  in
                     FStar_List.fold_right
                       (fun hd1  ->
                          fun tl1  ->
                            let r =
                              FStar_Range.union_ranges
                                hd1.FStar_Syntax_Syntax.p
                                tl1.FStar_Syntax_Syntax.p
                               in
                            let uu____6024 =
                              let uu____6025 =
                                let uu____6039 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Parser_Const.cons_lid
                                    FStar_Syntax_Syntax.delta_constant
                                    (FStar_Pervasives_Native.Some
                                       FStar_Syntax_Syntax.Data_ctor)
                                   in
                                (uu____6039, [(hd1, false); (tl1, false)])
                                 in
                              FStar_Syntax_Syntax.Pat_cons uu____6025  in
                            FStar_All.pipe_left (pos_r r) uu____6024) pats1
                       uu____5964
                      in
                   let x =
                     FStar_Syntax_Syntax.new_bv
                       (FStar_Pervasives_Native.Some
                          (p1.FStar_Parser_AST.prange))
                       FStar_Syntax_Syntax.tun
                      in
                   (loc1, env2,
                     (LocalBinder (x, FStar_Pervasives_Native.None)), pat,
                     annots))
          | FStar_Parser_AST.PatTuple (args,dep1) ->
              let uu____6095 =
                FStar_List.fold_left
                  (fun uu____6154  ->
                     fun p2  ->
                       match uu____6154 with
                       | (loc1,env2,annots,pats) ->
                           let uu____6236 = aux loc1 env2 p2  in
                           (match uu____6236 with
                            | (loc2,env3,uu____6280,pat,ans) ->
                                (loc2, env3, (FStar_List.append ans annots),
                                  ((pat, false) :: pats))))
                  (loc, env1, [], []) args
                 in
              (match uu____6095 with
               | (loc1,env2,annots,args1) ->
                   let args2 = FStar_List.rev args1  in
                   let l =
                     if dep1
                     then
                       FStar_Parser_Const.mk_dtuple_data_lid
                         (FStar_List.length args2) p1.FStar_Parser_AST.prange
                     else
                       FStar_Parser_Const.mk_tuple_data_lid
                         (FStar_List.length args2) p1.FStar_Parser_AST.prange
                      in
                   let constr =
                     FStar_Syntax_DsEnv.fail_or env2
                       (FStar_Syntax_DsEnv.try_lookup_lid env2) l
                      in
                   let l1 =
                     match constr.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                     | uu____6443 -> failwith "impossible"  in
                   let x =
                     FStar_Syntax_Syntax.new_bv
                       (FStar_Pervasives_Native.Some
                          (p1.FStar_Parser_AST.prange))
                       FStar_Syntax_Syntax.tun
                      in
                   let uu____6446 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                      in
                   (loc1, env2,
                     (LocalBinder (x, FStar_Pervasives_Native.None)),
                     uu____6446, annots))
          | FStar_Parser_AST.PatRecord [] ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
                p1.FStar_Parser_AST.prange
          | FStar_Parser_AST.PatRecord fields ->
              let record =
                check_fields env1 fields p1.FStar_Parser_AST.prange  in
              let fields1 =
                FStar_All.pipe_right fields
                  (FStar_List.map
                     (fun uu____6523  ->
                        match uu____6523 with
                        | (f,p2) ->
                            let uu____6534 = FStar_Ident.ident_of_lid f  in
                            (uu____6534, p2)))
                 in
              let args =
                FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                  (FStar_List.map
                     (fun uu____6554  ->
                        match uu____6554 with
                        | (f,uu____6560) ->
                            let uu____6561 =
                              FStar_All.pipe_right fields1
                                (FStar_List.tryFind
                                   (fun uu____6589  ->
                                      match uu____6589 with
                                      | (g,uu____6596) ->
                                          let uu____6597 =
                                            FStar_Ident.text_of_id f  in
                                          let uu____6599 =
                                            FStar_Ident.text_of_id g  in
                                          uu____6597 = uu____6599))
                               in
                            (match uu____6561 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Parser_AST.mk_pattern
                                   (FStar_Parser_AST.PatWild
                                      FStar_Pervasives_Native.None)
                                   p1.FStar_Parser_AST.prange
                             | FStar_Pervasives_Native.Some (uu____6606,p2)
                                 -> p2)))
                 in
              let app =
                let uu____6613 =
                  let uu____6614 =
                    let uu____6621 =
                      let uu____6622 =
                        let uu____6623 =
                          let uu____6624 =
                            let uu____6625 =
                              FStar_Ident.ns_of_lid
                                record.FStar_Syntax_DsEnv.typename
                               in
                            FStar_List.append uu____6625
                              [record.FStar_Syntax_DsEnv.constrname]
                             in
                          FStar_Ident.lid_of_ids uu____6624  in
                        FStar_Parser_AST.PatName uu____6623  in
                      FStar_Parser_AST.mk_pattern uu____6622
                        p1.FStar_Parser_AST.prange
                       in
                    (uu____6621, args)  in
                  FStar_Parser_AST.PatApp uu____6614  in
                FStar_Parser_AST.mk_pattern uu____6613
                  p1.FStar_Parser_AST.prange
                 in
              let uu____6630 = aux loc env1 app  in
              (match uu____6630 with
               | (env2,e,b,p2,annots) ->
                   let p3 =
                     match p2.FStar_Syntax_Syntax.v with
                     | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                         let uu____6707 =
                           let uu____6708 =
                             let uu____6722 =
                               let uu___1110_6723 = fv  in
                               let uu____6724 =
                                 let uu____6727 =
                                   let uu____6728 =
                                     let uu____6735 =
                                       FStar_All.pipe_right
                                         record.FStar_Syntax_DsEnv.fields
                                         (FStar_List.map
                                            FStar_Pervasives_Native.fst)
                                        in
                                     ((record.FStar_Syntax_DsEnv.typename),
                                       uu____6735)
                                      in
                                   FStar_Syntax_Syntax.Record_ctor uu____6728
                                    in
                                 FStar_Pervasives_Native.Some uu____6727  in
                               {
                                 FStar_Syntax_Syntax.fv_name =
                                   (uu___1110_6723.FStar_Syntax_Syntax.fv_name);
                                 FStar_Syntax_Syntax.fv_delta =
                                   (uu___1110_6723.FStar_Syntax_Syntax.fv_delta);
                                 FStar_Syntax_Syntax.fv_qual = uu____6724
                               }  in
                             (uu____6722, args1)  in
                           FStar_Syntax_Syntax.Pat_cons uu____6708  in
                         FStar_All.pipe_left pos uu____6707
                     | uu____6761 -> p2  in
                   (env2, e, b, p3, annots))
        
        and aux loc env1 p1 = aux' false loc env1 p1
         in
        let aux_maybe_or env1 p1 =
          let loc = []  in
          match p1.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOr [] -> failwith "impossible"
          | FStar_Parser_AST.PatOr (p2::ps) ->
              let uu____6845 = aux' true loc env1 p2  in
              (match uu____6845 with
               | (loc1,env2,var,p3,ans) ->
                   let uu____6898 =
                     FStar_List.fold_left
                       (fun uu____6946  ->
                          fun p4  ->
                            match uu____6946 with
                            | (loc2,env3,ps1) ->
                                let uu____7011 = aux' true loc2 env3 p4  in
                                (match uu____7011 with
                                 | (loc3,env4,uu____7049,p5,ans1) ->
                                     (loc3, env4, ((p5, ans1) :: ps1))))
                       (loc1, env2, []) ps
                      in
                   (match uu____6898 with
                    | (loc2,env3,ps1) ->
                        let pats = (p3, ans) :: (FStar_List.rev ps1)  in
                        (env3, var, pats)))
          | uu____7210 ->
              let uu____7211 = aux' true loc env1 p1  in
              (match uu____7211 with
               | (loc1,env2,vars,pat,ans) -> (env2, vars, [(pat, ans)]))
           in
        let uu____7302 = aux_maybe_or env p  in
        match uu____7302 with
        | (env1,b,pats) ->
            ((let uu____7357 =
                FStar_List.map FStar_Pervasives_Native.fst pats  in
              check_linear_pattern_variables uu____7357
                p.FStar_Parser_AST.prange);
             (env1, b, pats))

and (desugar_binding_pat_maybe_top :
  Prims.bool ->
    FStar_Syntax_DsEnv.env ->
      FStar_Parser_AST.pattern -> (env_t * bnd * annotated_pat Prims.list))
  =
  fun top  ->
    fun env  ->
      fun p  ->
        if top
        then
          let mklet x ty tacopt =
            let uu____7431 =
              let uu____7432 =
                let uu____7443 = FStar_Syntax_DsEnv.qualify env x  in
                (uu____7443, (ty, tacopt))  in
              LetBinder uu____7432  in
            (env, uu____7431, [])  in
          let op_to_ident x =
            let uu____7460 =
              let uu____7466 =
                let uu____7468 = FStar_Ident.text_of_id x  in
                let uu____7470 = FStar_Ident.range_of_id x  in
                FStar_Parser_AST.compile_op Prims.int_zero uu____7468
                  uu____7470
                 in
              let uu____7472 = FStar_Ident.range_of_id x  in
              (uu____7466, uu____7472)  in
            FStar_Ident.mk_ident uu____7460  in
          match p.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOp x ->
              let uu____7483 = op_to_ident x  in
              mklet uu____7483 FStar_Syntax_Syntax.tun
                FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatVar (x,uu____7485) ->
              mklet x FStar_Syntax_Syntax.tun FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatAscribed
              ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatOp x;
                 FStar_Parser_AST.prange = uu____7491;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____7507 = op_to_ident x  in
              let uu____7508 = desugar_term env t  in
              mklet uu____7507 uu____7508 tacopt1
          | FStar_Parser_AST.PatAscribed
              ({
                 FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                   (x,uu____7510);
                 FStar_Parser_AST.prange = uu____7511;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____7531 = desugar_term env t  in
              mklet x uu____7531 tacopt1
          | uu____7532 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnexpectedPattern,
                  "Unexpected pattern at the top-level")
                p.FStar_Parser_AST.prange
        else
          (let uu____7545 = desugar_data_pat true env p  in
           match uu____7545 with
           | (env1,binder,p1) ->
               let p2 =
                 match p1 with
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                        uu____7575;
                      FStar_Syntax_Syntax.p = uu____7576;_},uu____7577)::[]
                     -> []
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                        uu____7590;
                      FStar_Syntax_Syntax.p = uu____7591;_},uu____7592)::[]
                     -> []
                 | uu____7605 -> p1  in
               (env1, binder, p2))

and (desugar_binding_pat :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.pattern -> (env_t * bnd * annotated_pat Prims.list))
  = fun env  -> fun p  -> desugar_binding_pat_maybe_top false env p

and (desugar_match_pat_maybe_top :
  Prims.bool ->
    env_t -> FStar_Parser_AST.pattern -> (env_t * annotated_pat Prims.list))
  =
  fun uu____7613  ->
    fun env  ->
      fun pat  ->
        let uu____7617 = desugar_data_pat false env pat  in
        match uu____7617 with | (env1,uu____7634,pat1) -> (env1, pat1)

and (desugar_match_pat :
  env_t -> FStar_Parser_AST.pattern -> (env_t * annotated_pat Prims.list)) =
  fun env  -> fun p  -> desugar_match_pat_maybe_top false env p

and (desugar_term_aq :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.antiquotations))
  =
  fun env  ->
    fun e  ->
      let env1 = FStar_Syntax_DsEnv.set_expect_typ env false  in
      desugar_term_maybe_top false env1 e

and (desugar_term :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      let uu____7656 = desugar_term_aq env e  in
      match uu____7656 with | (t,aq) -> (check_no_aq aq; t)

and (desugar_typ_aq :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.antiquotations))
  =
  fun env  ->
    fun e  ->
      let env1 = FStar_Syntax_DsEnv.set_expect_typ env true  in
      desugar_term_maybe_top false env1 e

and (desugar_typ :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      let uu____7675 = desugar_typ_aq env e  in
      match uu____7675 with | (t,aq) -> (check_no_aq aq; t)

and (desugar_machine_integer :
  FStar_Syntax_DsEnv.env ->
    Prims.string ->
      (FStar_Const.signedness * FStar_Const.width) ->
        FStar_Range.range -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun repr  ->
      fun uu____7685  ->
        fun range  ->
          match uu____7685 with
          | (signedness,width) ->
              let tnm =
                Prims.op_Hat "FStar."
                  (Prims.op_Hat
                     (match signedness with
                      | FStar_Const.Unsigned  -> "U"
                      | FStar_Const.Signed  -> "")
                     (Prims.op_Hat "Int"
                        (match width with
                         | FStar_Const.Int8  -> "8"
                         | FStar_Const.Int16  -> "16"
                         | FStar_Const.Int32  -> "32"
                         | FStar_Const.Int64  -> "64")))
                 in
              ((let uu____7707 =
                  let uu____7709 =
                    FStar_Const.within_bounds repr signedness width  in
                  Prims.op_Negation uu____7709  in
                if uu____7707
                then
                  let uu____7712 =
                    let uu____7718 =
                      FStar_Util.format2
                        "%s is not in the expected range for %s" repr tnm
                       in
                    (FStar_Errors.Error_OutOfRange, uu____7718)  in
                  FStar_Errors.log_issue range uu____7712
                else ());
               (let private_intro_nm =
                  Prims.op_Hat tnm
                    (Prims.op_Hat ".__"
                       (Prims.op_Hat
                          (match signedness with
                           | FStar_Const.Unsigned  -> "u"
                           | FStar_Const.Signed  -> "") "int_to_t"))
                   in
                let intro_nm =
                  Prims.op_Hat tnm
                    (Prims.op_Hat "."
                       (Prims.op_Hat
                          (match signedness with
                           | FStar_Const.Unsigned  -> "u"
                           | FStar_Const.Signed  -> "") "int_to_t"))
                   in
                let lid =
                  let uu____7739 = FStar_Ident.path_of_text intro_nm  in
                  FStar_Ident.lid_of_path uu____7739 range  in
                let lid1 =
                  let uu____7743 = FStar_Syntax_DsEnv.try_lookup_lid env lid
                     in
                  match uu____7743 with
                  | FStar_Pervasives_Native.Some intro_term ->
                      (match intro_term.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let private_lid =
                             let uu____7753 =
                               FStar_Ident.path_of_text private_intro_nm  in
                             FStar_Ident.lid_of_path uu____7753 range  in
                           let private_fv =
                             let uu____7755 =
                               FStar_Syntax_Util.incr_delta_depth
                                 fv.FStar_Syntax_Syntax.fv_delta
                                in
                             FStar_Syntax_Syntax.lid_as_fv private_lid
                               uu____7755 fv.FStar_Syntax_Syntax.fv_qual
                              in
                           let uu___1277_7756 = intro_term  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_fvar private_fv);
                             FStar_Syntax_Syntax.pos =
                               (uu___1277_7756.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___1277_7756.FStar_Syntax_Syntax.vars)
                           }
                       | uu____7757 ->
                           failwith
                             (Prims.op_Hat "Unexpected non-fvar for "
                                intro_nm))
                  | FStar_Pervasives_Native.None  ->
                      let uu____7761 =
                        let uu____7767 =
                          FStar_Util.format1
                            "Unexpected numeric literal.  Restart F* to load %s."
                            tnm
                           in
                        (FStar_Errors.Fatal_UnexpectedNumericLiteral,
                          uu____7767)
                         in
                      FStar_Errors.raise_error uu____7761 range
                   in
                let repr1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_int
                          (repr, FStar_Pervasives_Native.None)))
                    FStar_Pervasives_Native.None range
                   in
                let uu____7787 =
                  let uu____7794 =
                    let uu____7795 =
                      let uu____7812 =
                        let uu____7823 =
                          let uu____7832 =
                            FStar_Syntax_Syntax.as_implicit false  in
                          (repr1, uu____7832)  in
                        [uu____7823]  in
                      (lid1, uu____7812)  in
                    FStar_Syntax_Syntax.Tm_app uu____7795  in
                  FStar_Syntax_Syntax.mk uu____7794  in
                uu____7787 FStar_Pervasives_Native.None range))

and (desugar_term_maybe_top :
  Prims.bool ->
    env_t ->
      FStar_Parser_AST.term ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.antiquotations))
  =
  fun top_level  ->
    fun env  ->
      fun top  ->
        let mk1 e =
          FStar_Syntax_Syntax.mk e FStar_Pervasives_Native.None
            top.FStar_Parser_AST.range
           in
        let noaqs = []  in
        let join_aqs aqs = FStar_List.flatten aqs  in
        let setpos e =
          let uu___1293_7951 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___1293_7951.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___1293_7951.FStar_Syntax_Syntax.vars)
          }  in
        let uu____7954 =
          let uu____7955 = unparen top  in uu____7955.FStar_Parser_AST.tm  in
        match uu____7954 with
        | FStar_Parser_AST.Wild  -> ((setpos FStar_Syntax_Syntax.tun), noaqs)
        | FStar_Parser_AST.Labeled uu____7960 ->
            let uu____7969 = desugar_formula env top  in (uu____7969, noaqs)
        | FStar_Parser_AST.Requires (t,lopt) ->
            let uu____7978 = desugar_formula env t  in (uu____7978, noaqs)
        | FStar_Parser_AST.Ensures (t,lopt) ->
            let uu____7987 = desugar_formula env t  in (uu____7987, noaqs)
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int
            (i,FStar_Pervasives_Native.Some size)) ->
            let uu____8014 =
              desugar_machine_integer env i size top.FStar_Parser_AST.range
               in
            (uu____8014, noaqs)
        | FStar_Parser_AST.Const c ->
            let uu____8016 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
            (uu____8016, noaqs)
        | FStar_Parser_AST.Op (id1,args) when
            let uu____8023 = FStar_Ident.text_of_id id1  in
            uu____8023 = "=!=" ->
            let r = FStar_Ident.range_of_id id1  in
            let e =
              let uu____8029 =
                let uu____8030 =
                  let uu____8037 = FStar_Ident.mk_ident ("==", r)  in
                  (uu____8037, args)  in
                FStar_Parser_AST.Op uu____8030  in
              FStar_Parser_AST.mk_term uu____8029 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let uu____8042 =
              let uu____8043 =
                let uu____8044 =
                  let uu____8051 = FStar_Ident.mk_ident ("~", r)  in
                  (uu____8051, [e])  in
                FStar_Parser_AST.Op uu____8044  in
              FStar_Parser_AST.mk_term uu____8043 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            desugar_term_aq env uu____8042
        | FStar_Parser_AST.Op (op_star,lhs::rhs::[]) when
            (let uu____8063 = FStar_Ident.text_of_id op_star  in
             uu____8063 = "*") &&
              (let uu____8068 =
                 op_as_term env (Prims.of_int (2)) top.FStar_Parser_AST.range
                   op_star
                  in
               FStar_All.pipe_right uu____8068 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op (id1,t1::t2::[]) when
                  (let uu____8092 = FStar_Ident.text_of_id id1  in
                   uu____8092 = "*") &&
                    (let uu____8097 =
                       op_as_term env (Prims.of_int (2))
                         top.FStar_Parser_AST.range op_star
                        in
                     FStar_All.pipe_right uu____8097 FStar_Option.isNone)
                  ->
                  let uu____8104 = flatten1 t1  in
                  FStar_List.append uu____8104 [t2]
              | uu____8107 -> [t]  in
            let terms = flatten1 lhs  in
            let t =
              let uu___1338_8112 = top  in
              let uu____8113 =
                let uu____8114 =
                  let uu____8125 =
                    FStar_List.map (fun _8136  -> FStar_Util.Inr _8136) terms
                     in
                  (uu____8125, rhs)  in
                FStar_Parser_AST.Sum uu____8114  in
              {
                FStar_Parser_AST.tm = uu____8113;
                FStar_Parser_AST.range =
                  (uu___1338_8112.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1338_8112.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env t
        | FStar_Parser_AST.Tvar a ->
            let uu____8144 =
              let uu____8145 =
                FStar_Syntax_DsEnv.fail_or2
                  (FStar_Syntax_DsEnv.try_lookup_id env) a
                 in
              FStar_All.pipe_left setpos uu____8145  in
            (uu____8144, noaqs)
        | FStar_Parser_AST.Uvar u ->
            let uu____8151 =
              let uu____8157 =
                let uu____8159 =
                  let uu____8161 = FStar_Ident.text_of_id u  in
                  Prims.op_Hat uu____8161 " in non-universe context"  in
                Prims.op_Hat "Unexpected universe variable " uu____8159  in
              (FStar_Errors.Fatal_UnexpectedUniverseVariable, uu____8157)  in
            FStar_Errors.raise_error uu____8151 top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s,args) ->
            let uu____8176 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s
               in
            (match uu____8176 with
             | FStar_Pervasives_Native.None  ->
                 let uu____8183 =
                   let uu____8189 =
                     let uu____8191 = FStar_Ident.text_of_id s  in
                     Prims.op_Hat "Unexpected or unbound operator: "
                       uu____8191
                      in
                   (FStar_Errors.Fatal_UnepxectedOrUnboundOperator,
                     uu____8189)
                    in
                 FStar_Errors.raise_error uu____8183
                   top.FStar_Parser_AST.range
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > Prims.int_zero
                 then
                   let uu____8206 =
                     let uu____8231 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun t  ->
                               let uu____8293 = desugar_term_aq env t  in
                               match uu____8293 with
                               | (t',s1) ->
                                   ((t', FStar_Pervasives_Native.None), s1)))
                        in
                     FStar_All.pipe_right uu____8231 FStar_List.unzip  in
                   (match uu____8206 with
                    | (args1,aqs) ->
                        let uu____8426 =
                          mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))  in
                        (uu____8426, (join_aqs aqs)))
                 else (op, noaqs))
        | FStar_Parser_AST.Construct (n1,(a,uu____8443)::[]) when
            let uu____8458 = FStar_Ident.string_of_lid n1  in
            uu____8458 = "SMTPat" ->
            let uu____8462 =
              let uu___1367_8463 = top  in
              let uu____8464 =
                let uu____8465 =
                  let uu____8472 =
                    let uu___1369_8473 = top  in
                    let uu____8474 =
                      let uu____8475 = smt_pat_lid top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____8475  in
                    {
                      FStar_Parser_AST.tm = uu____8474;
                      FStar_Parser_AST.range =
                        (uu___1369_8473.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1369_8473.FStar_Parser_AST.level)
                    }  in
                  (uu____8472, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____8465  in
              {
                FStar_Parser_AST.tm = uu____8464;
                FStar_Parser_AST.range =
                  (uu___1367_8463.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1367_8463.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____8462
        | FStar_Parser_AST.Construct (n1,(a,uu____8478)::[]) when
            let uu____8493 = FStar_Ident.string_of_lid n1  in
            uu____8493 = "SMTPatT" ->
            (FStar_Errors.log_issue top.FStar_Parser_AST.range
               (FStar_Errors.Warning_SMTPatTDeprecated,
                 "SMTPatT is deprecated; please just use SMTPat");
             (let uu____8500 =
                let uu___1379_8501 = top  in
                let uu____8502 =
                  let uu____8503 =
                    let uu____8510 =
                      let uu___1381_8511 = top  in
                      let uu____8512 =
                        let uu____8513 =
                          smt_pat_lid top.FStar_Parser_AST.range  in
                        FStar_Parser_AST.Var uu____8513  in
                      {
                        FStar_Parser_AST.tm = uu____8512;
                        FStar_Parser_AST.range =
                          (uu___1381_8511.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___1381_8511.FStar_Parser_AST.level)
                      }  in
                    (uu____8510, a, FStar_Parser_AST.Nothing)  in
                  FStar_Parser_AST.App uu____8503  in
                {
                  FStar_Parser_AST.tm = uu____8502;
                  FStar_Parser_AST.range =
                    (uu___1379_8501.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___1379_8501.FStar_Parser_AST.level)
                }  in
              desugar_term_maybe_top top_level env uu____8500))
        | FStar_Parser_AST.Construct (n1,(a,uu____8516)::[]) when
            let uu____8531 = FStar_Ident.string_of_lid n1  in
            uu____8531 = "SMTPatOr" ->
            let uu____8535 =
              let uu___1390_8536 = top  in
              let uu____8537 =
                let uu____8538 =
                  let uu____8545 =
                    let uu___1392_8546 = top  in
                    let uu____8547 =
                      let uu____8548 =
                        smt_pat_or_lid top.FStar_Parser_AST.range  in
                      FStar_Parser_AST.Var uu____8548  in
                    {
                      FStar_Parser_AST.tm = uu____8547;
                      FStar_Parser_AST.range =
                        (uu___1392_8546.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1392_8546.FStar_Parser_AST.level)
                    }  in
                  (uu____8545, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____8538  in
              {
                FStar_Parser_AST.tm = uu____8537;
                FStar_Parser_AST.range =
                  (uu___1390_8536.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1390_8536.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____8535
        | FStar_Parser_AST.Name lid when
            let uu____8550 = FStar_Ident.string_of_lid lid  in
            uu____8550 = "Type0" ->
            let uu____8554 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
               in
            (uu____8554, noaqs)
        | FStar_Parser_AST.Name lid when
            let uu____8556 = FStar_Ident.string_of_lid lid  in
            uu____8556 = "Type" ->
            let uu____8560 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
               in
            (uu____8560, noaqs)
        | FStar_Parser_AST.Construct (lid,(t,FStar_Parser_AST.UnivApp )::[])
            when
            let uu____8577 = FStar_Ident.string_of_lid lid  in
            uu____8577 = "Type" ->
            let uu____8581 =
              let uu____8582 =
                let uu____8583 = desugar_universe t  in
                FStar_Syntax_Syntax.Tm_type uu____8583  in
              mk1 uu____8582  in
            (uu____8581, noaqs)
        | FStar_Parser_AST.Name lid when
            let uu____8585 = FStar_Ident.string_of_lid lid  in
            uu____8585 = "Effect" ->
            let uu____8589 =
              mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
               in
            (uu____8589, noaqs)
        | FStar_Parser_AST.Name lid when
            let uu____8591 = FStar_Ident.string_of_lid lid  in
            uu____8591 = "True" ->
            let uu____8595 =
              let uu____8596 =
                FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____8596
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____8595, noaqs)
        | FStar_Parser_AST.Name lid when
            let uu____8598 = FStar_Ident.string_of_lid lid  in
            uu____8598 = "False" ->
            let uu____8602 =
              let uu____8603 =
                FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____8603
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____8602, noaqs)
        | FStar_Parser_AST.Projector (eff_name,id1) when
            (let uu____8608 = FStar_Ident.text_of_id id1  in
             is_special_effect_combinator uu____8608) &&
              (FStar_Syntax_DsEnv.is_effect_name env eff_name)
            ->
            let txt = FStar_Ident.text_of_id id1  in
            let uu____8612 =
              FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name  in
            (match uu____8612 with
             | FStar_Pervasives_Native.Some ed ->
                 let lid = FStar_Syntax_Util.dm4f_lid ed txt  in
                 let uu____8621 =
                   FStar_Syntax_Syntax.fvar lid
                     (FStar_Syntax_Syntax.Delta_constant_at_level
                        Prims.int_one) FStar_Pervasives_Native.None
                    in
                 (uu____8621, noaqs)
             | FStar_Pervasives_Native.None  ->
                 let uu____8623 =
                   let uu____8625 = FStar_Ident.string_of_lid eff_name  in
                   FStar_Util.format2
                     "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                     uu____8625 txt
                    in
                 failwith uu____8623)
        | FStar_Parser_AST.Var l ->
            let uu____8633 = desugar_name mk1 setpos env true l  in
            (uu____8633, noaqs)
        | FStar_Parser_AST.Name l ->
            let uu____8641 = desugar_name mk1 setpos env true l  in
            (uu____8641, noaqs)
        | FStar_Parser_AST.Projector (l,i) ->
            let name =
              let uu____8658 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                 in
              match uu____8658 with
              | FStar_Pervasives_Native.Some uu____8668 ->
                  FStar_Pervasives_Native.Some (true, l)
              | FStar_Pervasives_Native.None  ->
                  let uu____8676 =
                    FStar_Syntax_DsEnv.try_lookup_root_effect_name env l  in
                  (match uu____8676 with
                   | FStar_Pervasives_Native.Some new_name ->
                       FStar_Pervasives_Native.Some (false, new_name)
                   | uu____8694 -> FStar_Pervasives_Native.None)
               in
            (match name with
             | FStar_Pervasives_Native.Some (resolve,new_name) ->
                 let uu____8715 =
                   let uu____8716 =
                     FStar_Syntax_Util.mk_field_projector_name_from_ident
                       new_name i
                      in
                   desugar_name mk1 setpos env resolve uu____8716  in
                 (uu____8715, noaqs)
             | uu____8722 ->
                 let uu____8730 =
                   let uu____8736 =
                     let uu____8738 = FStar_Ident.string_of_lid l  in
                     FStar_Util.format1
                       "Data constructor or effect %s not found" uu____8738
                      in
                   (FStar_Errors.Fatal_EffectNotFound, uu____8736)  in
                 FStar_Errors.raise_error uu____8730
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Discrim lid ->
            let uu____8747 = FStar_Syntax_DsEnv.try_lookup_datacon env lid
               in
            (match uu____8747 with
             | FStar_Pervasives_Native.None  ->
                 let uu____8754 =
                   let uu____8760 =
                     let uu____8762 = FStar_Ident.string_of_lid lid  in
                     FStar_Util.format1 "Data constructor %s not found"
                       uu____8762
                      in
                   (FStar_Errors.Fatal_DataContructorNotFound, uu____8760)
                    in
                 FStar_Errors.raise_error uu____8754
                   top.FStar_Parser_AST.range
             | uu____8770 ->
                 let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                 let uu____8774 = desugar_name mk1 setpos env true lid'  in
                 (uu____8774, noaqs))
        | FStar_Parser_AST.Construct (l,args) ->
            let uu____8795 = FStar_Syntax_DsEnv.try_lookup_datacon env l  in
            (match uu____8795 with
             | FStar_Pervasives_Native.Some head1 ->
                 let head2 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1)  in
                 (match args with
                  | [] -> (head2, noaqs)
                  | uu____8814 ->
                      let uu____8821 =
                        FStar_Util.take
                          (fun uu____8845  ->
                             match uu____8845 with
                             | (uu____8851,imp) ->
                                 imp = FStar_Parser_AST.UnivApp) args
                         in
                      (match uu____8821 with
                       | (universes,args1) ->
                           let universes1 =
                             FStar_List.map
                               (fun x  ->
                                  desugar_universe
                                    (FStar_Pervasives_Native.fst x))
                               universes
                              in
                           let uu____8896 =
                             let uu____8921 =
                               FStar_List.map
                                 (fun uu____8964  ->
                                    match uu____8964 with
                                    | (t,imp) ->
                                        let uu____8981 =
                                          desugar_term_aq env t  in
                                        (match uu____8981 with
                                         | (te,aq) ->
                                             ((arg_withimp_e imp te), aq)))
                                 args1
                                in
                             FStar_All.pipe_right uu____8921 FStar_List.unzip
                              in
                           (match uu____8896 with
                            | (args2,aqs) ->
                                let head3 =
                                  if universes1 = []
                                  then head2
                                  else
                                    mk1
                                      (FStar_Syntax_Syntax.Tm_uinst
                                         (head2, universes1))
                                   in
                                let uu____9124 =
                                  mk1
                                    (FStar_Syntax_Syntax.Tm_app
                                       (head3, args2))
                                   in
                                (uu____9124, (join_aqs aqs)))))
             | FStar_Pervasives_Native.None  ->
                 let err =
                   let uu____9143 =
                     FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
                   match uu____9143 with
                   | FStar_Pervasives_Native.None  ->
                       let uu____9151 =
                         let uu____9153 =
                           let uu____9155 = FStar_Ident.string_of_lid l  in
                           Prims.op_Hat uu____9155 " not found"  in
                         Prims.op_Hat "Constructor " uu____9153  in
                       (FStar_Errors.Fatal_ConstructorNotFound, uu____9151)
                   | FStar_Pervasives_Native.Some uu____9160 ->
                       let uu____9161 =
                         let uu____9163 =
                           let uu____9165 = FStar_Ident.string_of_lid l  in
                           Prims.op_Hat uu____9165
                             " used at an unexpected position"
                            in
                         Prims.op_Hat "Effect " uu____9163  in
                       (FStar_Errors.Fatal_UnexpectedEffect, uu____9161)
                    in
                 FStar_Errors.raise_error err top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Sum (binders,t) when
            FStar_Util.for_all
              (fun uu___8_9194  ->
                 match uu___8_9194 with
                 | FStar_Util.Inr uu____9200 -> true
                 | uu____9202 -> false) binders
            ->
            let terms =
              let uu____9211 =
                FStar_All.pipe_right binders
                  (FStar_List.map
                     (fun uu___9_9228  ->
                        match uu___9_9228 with
                        | FStar_Util.Inr x -> x
                        | FStar_Util.Inl uu____9234 -> failwith "Impossible"))
                 in
              FStar_List.append uu____9211 [t]  in
            let uu____9236 =
              let uu____9261 =
                FStar_All.pipe_right terms
                  (FStar_List.map
                     (fun t1  ->
                        let uu____9318 = desugar_typ_aq env t1  in
                        match uu____9318 with
                        | (t',aq) ->
                            let uu____9329 = FStar_Syntax_Syntax.as_arg t'
                               in
                            (uu____9329, aq)))
                 in
              FStar_All.pipe_right uu____9261 FStar_List.unzip  in
            (match uu____9236 with
             | (targs,aqs) ->
                 let tup =
                   let uu____9439 =
                     FStar_Parser_Const.mk_tuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env
                     (FStar_Syntax_DsEnv.try_lookup_lid env) uu____9439
                    in
                 let uu____9448 =
                   mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs))  in
                 (uu____9448, (join_aqs aqs)))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____9475 =
              let uu____9492 =
                let uu____9499 =
                  let uu____9506 =
                    FStar_All.pipe_left (fun _9515  -> FStar_Util.Inl _9515)
                      (FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                         t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                         FStar_Pervasives_Native.None)
                     in
                  [uu____9506]  in
                FStar_List.append binders uu____9499  in
              FStar_List.fold_left
                (fun uu____9560  ->
                   fun b  ->
                     match uu____9560 with
                     | (env1,tparams,typs) ->
                         let uu____9621 =
                           match b with
                           | FStar_Util.Inl b1 -> desugar_binder env1 b1
                           | FStar_Util.Inr t1 ->
                               let uu____9636 = desugar_typ env1 t1  in
                               (FStar_Pervasives_Native.None, uu____9636)
                            in
                         (match uu____9621 with
                          | (xopt,t1) ->
                              let uu____9661 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____9670 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env1, uu____9670)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_Syntax_DsEnv.push_bv env1 x
                                 in
                              (match uu____9661 with
                               | (env2,x) ->
                                   let uu____9690 =
                                     let uu____9693 =
                                       let uu____9696 =
                                         let uu____9697 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____9697
                                          in
                                       [uu____9696]  in
                                     FStar_List.append typs uu____9693  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___1521_9723 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___1521_9723.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___1521_9723.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____9690)))) (env, [], []) uu____9492
               in
            (match uu____9475 with
             | (env1,uu____9751,targs) ->
                 let tup =
                   let uu____9774 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env1
                     (FStar_Syntax_DsEnv.try_lookup_lid env1) uu____9774
                    in
                 let uu____9775 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_app (tup, targs))
                    in
                 (uu____9775, noaqs))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____9794 = uncurry binders t  in
            (match uu____9794 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___10_9838 =
                   match uu___10_9838 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range true env1 t1
                          in
                       let uu____9855 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____9855
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1  in
                       let uu____9879 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb  in
                       (match uu____9879 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1)
                    in
                 let uu____9912 = aux env [] bs  in (uu____9912, noaqs))
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____9921 = desugar_binder env b  in
            (match uu____9921 with
             | (FStar_Pervasives_Native.None ,uu____9932) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____9947 =
                   as_binder env FStar_Pervasives_Native.None b1  in
                 (match uu____9947 with
                  | ((x,uu____9963),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____9976 =
                        let uu____9977 = FStar_Syntax_Util.refine x f1  in
                        FStar_All.pipe_left setpos uu____9977  in
                      (uu____9976, noaqs)))
        | FStar_Parser_AST.Abs (binders,body) ->
            let bvss = FStar_List.map gather_pattern_bound_vars binders  in
            let check_disjoint sets =
              let rec aux acc sets1 =
                match sets1 with
                | [] -> FStar_Pervasives_Native.None
                | set1::sets2 ->
                    let i = FStar_Util.set_intersect acc set1  in
                    let uu____10055 = FStar_Util.set_is_empty i  in
                    if uu____10055
                    then
                      let uu____10060 = FStar_Util.set_union acc set1  in
                      aux uu____10060 sets2
                    else
                      (let uu____10065 =
                         let uu____10066 = FStar_Util.set_elements i  in
                         FStar_List.hd uu____10066  in
                       FStar_Pervasives_Native.Some uu____10065)
                 in
              let uu____10069 = FStar_Syntax_Syntax.new_id_set ()  in
              aux uu____10069 sets  in
            ((let uu____10073 = check_disjoint bvss  in
              match uu____10073 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some id1 ->
                  let uu____10077 =
                    let uu____10083 =
                      let uu____10085 = FStar_Ident.text_of_id id1  in
                      FStar_Util.format1
                        "Non-linear patterns are not permitted: `%s` appears more than once in this function definition."
                        uu____10085
                       in
                    (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                      uu____10083)
                     in
                  let uu____10089 = FStar_Ident.range_of_id id1  in
                  FStar_Errors.raise_error uu____10077 uu____10089);
             (let binders1 =
                FStar_All.pipe_right binders
                  (FStar_List.map replace_unit_pattern)
                 in
              let uu____10097 =
                FStar_List.fold_left
                  (fun uu____10117  ->
                     fun pat  ->
                       match uu____10117 with
                       | (env1,ftvs) ->
                           (match pat.FStar_Parser_AST.pat with
                            | FStar_Parser_AST.PatAscribed
                                (uu____10143,(t,FStar_Pervasives_Native.None
                                              ))
                                ->
                                let uu____10153 =
                                  let uu____10156 = free_type_vars env1 t  in
                                  FStar_List.append uu____10156 ftvs  in
                                (env1, uu____10153)
                            | FStar_Parser_AST.PatAscribed
                                (uu____10161,(t,FStar_Pervasives_Native.Some
                                              tac))
                                ->
                                let uu____10172 =
                                  let uu____10175 = free_type_vars env1 t  in
                                  let uu____10178 =
                                    let uu____10181 = free_type_vars env1 tac
                                       in
                                    FStar_List.append uu____10181 ftvs  in
                                  FStar_List.append uu____10175 uu____10178
                                   in
                                (env1, uu____10172)
                            | uu____10186 -> (env1, ftvs))) (env, [])
                  binders1
                 in
              match uu____10097 with
              | (uu____10195,ftv) ->
                  let ftv1 = sort_ftv ftv  in
                  let binders2 =
                    let uu____10207 =
                      FStar_All.pipe_right ftv1
                        (FStar_List.map
                           (fun a  ->
                              FStar_Parser_AST.mk_pattern
                                (FStar_Parser_AST.PatTvar
                                   (a,
                                     (FStar_Pervasives_Native.Some
                                        FStar_Parser_AST.Implicit)))
                                top.FStar_Parser_AST.range))
                       in
                    FStar_List.append uu____10207 binders1  in
                  let rec aux env1 bs sc_pat_opt pats =
                    match pats with
                    | [] ->
                        let uu____10287 = desugar_term_aq env1 body  in
                        (match uu____10287 with
                         | (body1,aq) ->
                             let body2 =
                               match sc_pat_opt with
                               | FStar_Pervasives_Native.Some (sc,pat) ->
                                   let body2 =
                                     let uu____10322 =
                                       let uu____10323 =
                                         FStar_Syntax_Syntax.pat_bvs pat  in
                                       FStar_All.pipe_right uu____10323
                                         (FStar_List.map
                                            FStar_Syntax_Syntax.mk_binder)
                                        in
                                     FStar_Syntax_Subst.close uu____10322
                                       body1
                                      in
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_match
                                        (sc,
                                          [(pat,
                                             FStar_Pervasives_Native.None,
                                             body2)]))
                                     FStar_Pervasives_Native.None
                                     body2.FStar_Syntax_Syntax.pos
                               | FStar_Pervasives_Native.None  -> body1  in
                             let uu____10392 =
                               let uu____10393 =
                                 no_annot_abs (FStar_List.rev bs) body2  in
                               setpos uu____10393  in
                             (uu____10392, aq))
                    | p::rest ->
                        let uu____10406 = desugar_binding_pat env1 p  in
                        (match uu____10406 with
                         | (env2,b,pat) ->
                             let pat1 =
                               match pat with
                               | [] -> FStar_Pervasives_Native.None
                               | (p1,uu____10438)::[] ->
                                   FStar_Pervasives_Native.Some p1
                               | uu____10453 ->
                                   FStar_Errors.raise_error
                                     (FStar_Errors.Fatal_UnsupportedDisjuctivePatterns,
                                       "Disjunctive patterns are not supported in abstractions")
                                     p.FStar_Parser_AST.prange
                                in
                             let uu____10462 =
                               match b with
                               | LetBinder uu____10503 ->
                                   failwith "Impossible"
                               | LocalBinder (x,aq) ->
                                   let sc_pat_opt1 =
                                     match (pat1, sc_pat_opt) with
                                     | (FStar_Pervasives_Native.None
                                        ,uu____10572) -> sc_pat_opt
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.None ) ->
                                         let uu____10626 =
                                           let uu____10635 =
                                             FStar_Syntax_Syntax.bv_to_name x
                                              in
                                           (uu____10635, p1)  in
                                         FStar_Pervasives_Native.Some
                                           uu____10626
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.Some
                                        (sc,p')) ->
                                         (match ((sc.FStar_Syntax_Syntax.n),
                                                  (p'.FStar_Syntax_Syntax.v))
                                          with
                                          | (FStar_Syntax_Syntax.Tm_name
                                             uu____10697,uu____10698) ->
                                              let tup2 =
                                                let uu____10700 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    (Prims.of_int (2))
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____10700
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____10705 =
                                                  let uu____10712 =
                                                    let uu____10713 =
                                                      let uu____10730 =
                                                        mk1
                                                          (FStar_Syntax_Syntax.Tm_fvar
                                                             tup2)
                                                         in
                                                      let uu____10733 =
                                                        let uu____10744 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            sc
                                                           in
                                                        let uu____10753 =
                                                          let uu____10764 =
                                                            let uu____10773 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                x
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_Syntax_Syntax.as_arg
                                                              uu____10773
                                                             in
                                                          [uu____10764]  in
                                                        uu____10744 ::
                                                          uu____10753
                                                         in
                                                      (uu____10730,
                                                        uu____10733)
                                                       in
                                                    FStar_Syntax_Syntax.Tm_app
                                                      uu____10713
                                                     in
                                                  FStar_Syntax_Syntax.mk
                                                    uu____10712
                                                   in
                                                uu____10705
                                                  FStar_Pervasives_Native.None
                                                  top.FStar_Parser_AST.range
                                                 in
                                              let p2 =
                                                let uu____10821 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tup2,
                                                       [(p', false);
                                                       (p1, false)]))
                                                  uu____10821
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | (FStar_Syntax_Syntax.Tm_app
                                             (uu____10872,args),FStar_Syntax_Syntax.Pat_cons
                                             (uu____10874,pats1)) ->
                                              let tupn =
                                                let uu____10919 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    (Prims.int_one +
                                                       (FStar_List.length
                                                          args))
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____10919
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____10932 =
                                                  let uu____10933 =
                                                    let uu____10950 =
                                                      mk1
                                                        (FStar_Syntax_Syntax.Tm_fvar
                                                           tupn)
                                                       in
                                                    let uu____10953 =
                                                      let uu____10964 =
                                                        let uu____10975 =
                                                          let uu____10984 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x
                                                             in
                                                          FStar_All.pipe_left
                                                            FStar_Syntax_Syntax.as_arg
                                                            uu____10984
                                                           in
                                                        [uu____10975]  in
                                                      FStar_List.append args
                                                        uu____10964
                                                       in
                                                    (uu____10950,
                                                      uu____10953)
                                                     in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____10933
                                                   in
                                                mk1 uu____10932  in
                                              let p2 =
                                                let uu____11032 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tupn,
                                                       (FStar_List.append
                                                          pats1 [(p1, false)])))
                                                  uu____11032
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | uu____11079 ->
                                              failwith "Impossible")
                                      in
                                   ((x, aq), sc_pat_opt1)
                                in
                             (match uu____10462 with
                              | (b1,sc_pat_opt1) ->
                                  aux env2 (b1 :: bs) sc_pat_opt1 rest))
                     in
                  aux env [] FStar_Pervasives_Native.None binders2))
        | FStar_Parser_AST.App
            (uu____11171,uu____11172,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____11194 =
                let uu____11195 = unparen e  in
                uu____11195.FStar_Parser_AST.tm  in
              match uu____11194 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____11205 ->
                  let uu____11206 = desugar_term_aq env e  in
                  (match uu____11206 with
                   | (head1,aq) ->
                       let uu____11219 =
                         mk1
                           (FStar_Syntax_Syntax.Tm_uinst (head1, universes))
                          in
                       (uu____11219, aq))
               in
            aux [] top
        | FStar_Parser_AST.App uu____11226 ->
            let rec aux args aqs e =
              let uu____11303 =
                let uu____11304 = unparen e  in
                uu____11304.FStar_Parser_AST.tm  in
              match uu____11303 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let uu____11322 = desugar_term_aq env t  in
                  (match uu____11322 with
                   | (t1,aq) ->
                       let arg = arg_withimp_e imp t1  in
                       aux (arg :: args) (aq :: aqs) e1)
              | uu____11370 ->
                  let uu____11371 = desugar_term_aq env e  in
                  (match uu____11371 with
                   | (head1,aq) ->
                       let uu____11392 =
                         mk1 (FStar_Syntax_Syntax.Tm_app (head1, args))  in
                       (uu____11392, (join_aqs (aq :: aqs))))
               in
            aux [] [] top
        | FStar_Parser_AST.Bind (x,t1,t2) ->
            let xpat =
              let uu____11445 = FStar_Ident.range_of_id x  in
              FStar_Parser_AST.mk_pattern
                (FStar_Parser_AST.PatVar (x, FStar_Pervasives_Native.None))
                uu____11445
               in
            let k =
              FStar_Parser_AST.mk_term (FStar_Parser_AST.Abs ([xpat], t2))
                t2.FStar_Parser_AST.range t2.FStar_Parser_AST.level
               in
            let bind_lid =
              let uu____11452 = FStar_Ident.range_of_id x  in
              FStar_Ident.lid_of_path ["bind"] uu____11452  in
            let bind1 =
              let uu____11457 = FStar_Ident.range_of_id x  in
              FStar_Parser_AST.mk_term (FStar_Parser_AST.Var bind_lid)
                uu____11457 FStar_Parser_AST.Expr
               in
            let uu____11458 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range
               in
            desugar_term_aq env uu____11458
        | FStar_Parser_AST.Seq (t1,t2) ->
            let t =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.Let
                   (FStar_Parser_AST.NoLetQualifier,
                     [(FStar_Pervasives_Native.None,
                        ((FStar_Parser_AST.mk_pattern
                            (FStar_Parser_AST.PatWild
                               FStar_Pervasives_Native.None)
                            t1.FStar_Parser_AST.range), t1))], t2))
                top.FStar_Parser_AST.range FStar_Parser_AST.Expr
               in
            let uu____11510 = desugar_term_aq env t  in
            (match uu____11510 with
             | (tm,s) ->
                 let uu____11521 =
                   mk1
                     (FStar_Syntax_Syntax.Tm_meta
                        (tm,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Sequence)))
                    in
                 (uu____11521, s))
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in
            let uu____11527 =
              let uu____11540 = FStar_Syntax_DsEnv.expect_typ env1  in
              if uu____11540 then desugar_typ_aq else desugar_term_aq  in
            uu____11527 env1 e
        | FStar_Parser_AST.Let (qual,lbs,body) ->
            let is_rec = qual = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____11607 =
              let bindings = lbs  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____11750  ->
                        match uu____11750 with
                        | (attr_opt,(p,def)) ->
                            let uu____11808 = is_app_pattern p  in
                            if uu____11808
                            then
                              let uu____11841 =
                                destruct_app_pattern env top_level p  in
                              (attr_opt, uu____11841, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____11924 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (attr_opt, uu____11924, def1)
                               | uu____11969 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id1,uu____12007);
                                           FStar_Parser_AST.prange =
                                             uu____12008;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____12057 =
                                            let uu____12078 =
                                              let uu____12083 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____12083  in
                                            (uu____12078, [],
                                              (FStar_Pervasives_Native.Some t))
                                             in
                                          (attr_opt, uu____12057, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id1,uu____12175) ->
                                        if top_level
                                        then
                                          let uu____12211 =
                                            let uu____12232 =
                                              let uu____12237 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____12237  in
                                            (uu____12232, [],
                                              FStar_Pervasives_Native.None)
                                             in
                                          (attr_opt, uu____12211, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              FStar_Pervasives_Native.None),
                                            def)
                                    | uu____12328 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_UnexpectedLetBinding,
                                            "Unexpected let binding")
                                          p.FStar_Parser_AST.prange))))
                 in
              let uu____12361 =
                FStar_List.fold_left
                  (fun uu____12450  ->
                     fun uu____12451  ->
                       match (uu____12450, uu____12451) with
                       | ((env1,fnames,rec_bindings,used_markers),(_attr_opt,
                                                                   (f,uu____12581,uu____12582),uu____12583))
                           ->
                           let uu____12717 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____12757 =
                                   FStar_Syntax_DsEnv.push_bv' env1 x  in
                                 (match uu____12757 with
                                  | (env2,xx,used_marker) ->
                                      let dummy_ref = FStar_Util.mk_ref true
                                         in
                                      let uu____12792 =
                                        let uu____12795 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____12795 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx),
                                        uu____12792, (used_marker ::
                                        used_markers)))
                             | FStar_Util.Inr l ->
                                 let uu____12811 =
                                   let uu____12819 =
                                     FStar_Ident.ident_of_lid l  in
                                   FStar_Syntax_DsEnv.push_top_level_rec_binding
                                     env1 uu____12819
                                     FStar_Syntax_Syntax.delta_equational
                                    in
                                 (match uu____12811 with
                                  | (env2,used_marker) ->
                                      (env2, (FStar_Util.Inr l),
                                        rec_bindings, (used_marker ::
                                        used_markers)))
                              in
                           (match uu____12717 with
                            | (env2,lbname,rec_bindings1,used_markers1) ->
                                (env2, (lbname :: fnames), rec_bindings1,
                                  used_markers1))) (env, [], [], []) funs
                 in
              match uu____12361 with
              | (env',fnames,rec_bindings,used_markers) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let used_markers1 = FStar_List.rev used_markers  in
                  let desugar_one_def env1 lbname uu____13065 =
                    match uu____13065 with
                    | (attrs_opt,(uu____13105,args,result_t),def) ->
                        let args1 =
                          FStar_All.pipe_right args
                            (FStar_List.map replace_unit_pattern)
                           in
                        let pos = def.FStar_Parser_AST.range  in
                        let def1 =
                          match result_t with
                          | FStar_Pervasives_Native.None  -> def
                          | FStar_Pervasives_Native.Some (t,tacopt) ->
                              let t1 =
                                let uu____13197 = is_comp_type env1 t  in
                                if uu____13197
                                then
                                  ((let uu____13201 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____13211 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____13211))
                                       in
                                    match uu____13201 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange);
                                   t)
                                else
                                  (let uu____13218 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____13221 =
                                           FStar_Syntax_DsEnv.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____13221))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             Prims.int_zero))
                                      in
                                   if uu____13218
                                   then FStar_Parser_AST.ml_comp t
                                   else FStar_Parser_AST.tot_comp t)
                                 in
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.Ascribed (def, t1, tacopt))
                                def.FStar_Parser_AST.range
                                FStar_Parser_AST.Expr
                           in
                        let def2 =
                          match args1 with
                          | [] -> def1
                          | uu____13232 ->
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.un_curry_abs args1 def1)
                                top.FStar_Parser_AST.range
                                top.FStar_Parser_AST.level
                           in
                        let uu____13235 = desugar_term_aq env1 def2  in
                        (match uu____13235 with
                         | (body1,aq) ->
                             let lbname1 =
                               match lbname with
                               | FStar_Util.Inl x -> FStar_Util.Inl x
                               | FStar_Util.Inr l ->
                                   let uu____13257 =
                                     let uu____13258 =
                                       FStar_Syntax_Util.incr_delta_qualifier
                                         body1
                                        in
                                     FStar_Syntax_Syntax.lid_as_fv l
                                       uu____13258
                                       FStar_Pervasives_Native.None
                                      in
                                   FStar_Util.Inr uu____13257
                                in
                             let body2 =
                               if is_rec
                               then
                                 FStar_Syntax_Subst.close rec_bindings1 body1
                               else body1  in
                             let attrs =
                               match attrs_opt with
                               | FStar_Pervasives_Native.None  -> []
                               | FStar_Pervasives_Native.Some l ->
                                   FStar_List.map (desugar_term env1) l
                                in
                             ((mk_lb
                                 (attrs, lbname1, FStar_Syntax_Syntax.tun,
                                   body2, pos)), aq))
                     in
                  let uu____13299 =
                    let uu____13316 =
                      FStar_List.map2
                        (desugar_one_def (if is_rec then env' else env))
                        fnames1 funs
                       in
                    FStar_All.pipe_right uu____13316 FStar_List.unzip  in
                  (match uu____13299 with
                   | (lbs1,aqss) ->
                       let uu____13458 = desugar_term_aq env' body  in
                       (match uu____13458 with
                        | (body1,aq) ->
                            (if is_rec
                             then
                               FStar_List.iter2
                                 (fun uu____13564  ->
                                    fun used_marker  ->
                                      match uu____13564 with
                                      | (_attr_opt,(f,uu____13638,uu____13639),uu____13640)
                                          ->
                                          let uu____13697 =
                                            let uu____13699 =
                                              FStar_ST.op_Bang used_marker
                                               in
                                            Prims.op_Negation uu____13699  in
                                          if uu____13697
                                          then
                                            let uu____13723 =
                                              match f with
                                              | FStar_Util.Inl x ->
                                                  let uu____13741 =
                                                    FStar_Ident.text_of_id x
                                                     in
                                                  let uu____13743 =
                                                    FStar_Ident.range_of_id x
                                                     in
                                                  (uu____13741, "Local",
                                                    uu____13743)
                                              | FStar_Util.Inr l ->
                                                  let uu____13748 =
                                                    FStar_Ident.string_of_lid
                                                      l
                                                     in
                                                  let uu____13750 =
                                                    FStar_Ident.range_of_lid
                                                      l
                                                     in
                                                  (uu____13748, "Global",
                                                    uu____13750)
                                               in
                                            (match uu____13723 with
                                             | (nm,gl,rng) ->
                                                 let uu____13761 =
                                                   let uu____13767 =
                                                     FStar_Util.format2
                                                       "%s binding %s is recursive but not used in its body"
                                                       gl nm
                                                      in
                                                   (FStar_Errors.Warning_UnusedLetRec,
                                                     uu____13767)
                                                    in
                                                 FStar_Errors.log_issue rng
                                                   uu____13761)
                                          else ()) funs used_markers1
                             else ();
                             (let uu____13775 =
                                let uu____13778 =
                                  let uu____13779 =
                                    let uu____13793 =
                                      FStar_Syntax_Subst.close rec_bindings1
                                        body1
                                       in
                                    ((is_rec, lbs1), uu____13793)  in
                                  FStar_Syntax_Syntax.Tm_let uu____13779  in
                                FStar_All.pipe_left mk1 uu____13778  in
                              (uu____13775,
                                (FStar_List.append aq
                                   (FStar_List.flatten aqss)))))))
               in
            let ds_non_rec attrs_opt pat t1 t2 =
              let attrs =
                match attrs_opt with
                | FStar_Pervasives_Native.None  -> []
                | FStar_Pervasives_Native.Some l ->
                    FStar_List.map (desugar_term env) l
                 in
              let uu____13895 = desugar_term_aq env t1  in
              match uu____13895 with
              | (t11,aq0) ->
                  let uu____13916 =
                    desugar_binding_pat_maybe_top top_level env pat  in
                  (match uu____13916 with
                   | (env1,binder,pat1) ->
                       let uu____13946 =
                         match binder with
                         | LetBinder (l,(t,_tacopt)) ->
                             let uu____13988 = desugar_term_aq env1 t2  in
                             (match uu____13988 with
                              | (body1,aq) ->
                                  let fv =
                                    let uu____14010 =
                                      FStar_Syntax_Util.incr_delta_qualifier
                                        t11
                                       in
                                    FStar_Syntax_Syntax.lid_as_fv l
                                      uu____14010
                                      FStar_Pervasives_Native.None
                                     in
                                  let uu____14011 =
                                    FStar_All.pipe_left mk1
                                      (FStar_Syntax_Syntax.Tm_let
                                         ((false,
                                            [mk_lb
                                               (attrs, (FStar_Util.Inr fv),
                                                 t, t11,
                                                 (t11.FStar_Syntax_Syntax.pos))]),
                                           body1))
                                     in
                                  (uu____14011, aq))
                         | LocalBinder (x,uu____14052) ->
                             let uu____14053 = desugar_term_aq env1 t2  in
                             (match uu____14053 with
                              | (body1,aq) ->
                                  let body2 =
                                    match pat1 with
                                    | [] -> body1
                                    | ({
                                         FStar_Syntax_Syntax.v =
                                           FStar_Syntax_Syntax.Pat_wild
                                           uu____14075;
                                         FStar_Syntax_Syntax.p = uu____14076;_},uu____14077)::[]
                                        -> body1
                                    | uu____14090 ->
                                        let uu____14093 =
                                          let uu____14100 =
                                            let uu____14101 =
                                              let uu____14124 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  x
                                                 in
                                              let uu____14127 =
                                                desugar_disjunctive_pattern
                                                  pat1
                                                  FStar_Pervasives_Native.None
                                                  body1
                                                 in
                                              (uu____14124, uu____14127)  in
                                            FStar_Syntax_Syntax.Tm_match
                                              uu____14101
                                             in
                                          FStar_Syntax_Syntax.mk uu____14100
                                           in
                                        uu____14093
                                          FStar_Pervasives_Native.None
                                          top.FStar_Parser_AST.range
                                     in
                                  let uu____14164 =
                                    let uu____14167 =
                                      let uu____14168 =
                                        let uu____14182 =
                                          let uu____14185 =
                                            let uu____14186 =
                                              FStar_Syntax_Syntax.mk_binder x
                                               in
                                            [uu____14186]  in
                                          FStar_Syntax_Subst.close
                                            uu____14185 body2
                                           in
                                        ((false,
                                           [mk_lb
                                              (attrs, (FStar_Util.Inl x),
                                                (x.FStar_Syntax_Syntax.sort),
                                                t11,
                                                (t11.FStar_Syntax_Syntax.pos))]),
                                          uu____14182)
                                         in
                                      FStar_Syntax_Syntax.Tm_let uu____14168
                                       in
                                    FStar_All.pipe_left mk1 uu____14167  in
                                  (uu____14164, aq))
                          in
                       (match uu____13946 with
                        | (tm,aq1) -> (tm, (FStar_List.append aq0 aq1))))
               in
            let uu____14294 = FStar_List.hd lbs  in
            (match uu____14294 with
             | (attrs,(head_pat,defn)) ->
                 let uu____14338 = is_rec || (is_app_pattern head_pat)  in
                 if uu____14338
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let t_bool1 =
              let uu____14354 =
                let uu____14355 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.delta_constant
                    FStar_Pervasives_Native.None
                   in
                FStar_Syntax_Syntax.Tm_fvar uu____14355  in
              mk1 uu____14354  in
            let uu____14356 = desugar_term_aq env t1  in
            (match uu____14356 with
             | (t1',aq1) ->
                 let uu____14367 = desugar_term_aq env t2  in
                 (match uu____14367 with
                  | (t2',aq2) ->
                      let uu____14378 = desugar_term_aq env t3  in
                      (match uu____14378 with
                       | (t3',aq3) ->
                           let uu____14389 =
                             let uu____14390 =
                               let uu____14391 =
                                 let uu____14414 =
                                   let uu____14431 =
                                     let uu____14446 =
                                       FStar_Syntax_Syntax.withinfo
                                         (FStar_Syntax_Syntax.Pat_constant
                                            (FStar_Const.Const_bool true))
                                         t1.FStar_Parser_AST.range
                                        in
                                     (uu____14446,
                                       FStar_Pervasives_Native.None, t2')
                                      in
                                   let uu____14460 =
                                     let uu____14477 =
                                       let uu____14492 =
                                         FStar_Syntax_Syntax.withinfo
                                           (FStar_Syntax_Syntax.Pat_wild x)
                                           t1.FStar_Parser_AST.range
                                          in
                                       (uu____14492,
                                         FStar_Pervasives_Native.None, t3')
                                        in
                                     [uu____14477]  in
                                   uu____14431 :: uu____14460  in
                                 (t1', uu____14414)  in
                               FStar_Syntax_Syntax.Tm_match uu____14391  in
                             mk1 uu____14390  in
                           (uu____14389, (join_aqs [aq1; aq2; aq3])))))
        | FStar_Parser_AST.TryWith (e,branches) ->
            let r = top.FStar_Parser_AST.range  in
            let handler = FStar_Parser_AST.mk_function branches r r  in
            let body =
              FStar_Parser_AST.mk_function
                [((FStar_Parser_AST.mk_pattern
                     (FStar_Parser_AST.PatConst FStar_Const.Const_unit) r),
                   FStar_Pervasives_Native.None, e)] r r
               in
            let try_with_lid1 = FStar_Ident.lid_of_path ["try_with"] r  in
            let try_with1 =
              FStar_Parser_AST.mk_term (FStar_Parser_AST.Var try_with_lid1) r
                FStar_Parser_AST.Expr
               in
            let a1 =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.App
                   (try_with1, body, FStar_Parser_AST.Nothing)) r
                top.FStar_Parser_AST.level
               in
            let a2 =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.App (a1, handler, FStar_Parser_AST.Nothing))
                r top.FStar_Parser_AST.level
               in
            desugar_term_aq env a2
        | FStar_Parser_AST.Match (e,branches) ->
            let desugar_branch uu____14688 =
              match uu____14688 with
              | (pat,wopt,b) ->
                  let uu____14710 = desugar_match_pat env pat  in
                  (match uu____14710 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____14741 = desugar_term env1 e1  in
                             FStar_Pervasives_Native.Some uu____14741
                          in
                       let uu____14746 = desugar_term_aq env1 b  in
                       (match uu____14746 with
                        | (b1,aq) ->
                            let uu____14759 =
                              desugar_disjunctive_pattern pat1 wopt1 b1  in
                            (uu____14759, aq)))
               in
            let uu____14764 = desugar_term_aq env e  in
            (match uu____14764 with
             | (e1,aq) ->
                 let uu____14775 =
                   let uu____14806 =
                     let uu____14839 = FStar_List.map desugar_branch branches
                        in
                     FStar_All.pipe_right uu____14839 FStar_List.unzip  in
                   FStar_All.pipe_right uu____14806
                     (fun uu____15057  ->
                        match uu____15057 with
                        | (x,y) -> ((FStar_List.flatten x), y))
                    in
                 (match uu____14775 with
                  | (brs,aqs) ->
                      let uu____15276 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_match (e1, brs))
                         in
                      (uu____15276, (join_aqs (aq :: aqs)))))
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let uu____15310 =
              let uu____15331 = is_comp_type env t  in
              if uu____15331
              then
                let comp = desugar_comp t.FStar_Parser_AST.range true env t
                   in
                ((FStar_Util.Inr comp), [])
              else
                (let uu____15386 = desugar_term_aq env t  in
                 match uu____15386 with
                 | (tm,aq) -> ((FStar_Util.Inl tm), aq))
               in
            (match uu____15310 with
             | (annot,aq0) ->
                 let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)
                    in
                 let uu____15478 = desugar_term_aq env e  in
                 (match uu____15478 with
                  | (e1,aq) ->
                      let uu____15489 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (e1, (annot, tac_opt1),
                               FStar_Pervasives_Native.None))
                         in
                      (uu____15489, (FStar_List.append aq0 aq))))
        | FStar_Parser_AST.Record (uu____15528,[]) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____15571 = FStar_List.hd fields  in
              match uu____15571 with
              | (f,uu____15583) -> FStar_Ident.ns_of_lid f  in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____15631  ->
                        match uu____15631 with
                        | (g,uu____15638) ->
                            let uu____15639 = FStar_Ident.text_of_id f  in
                            let uu____15641 =
                              let uu____15643 = FStar_Ident.ident_of_lid g
                                 in
                              FStar_Ident.text_of_id uu____15643  in
                            uu____15639 = uu____15641))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | FStar_Pervasives_Native.Some (uu____15650,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____15664 =
                         let uu____15670 =
                           let uu____15672 = FStar_Ident.text_of_id f  in
                           let uu____15674 =
                             FStar_Ident.string_of_lid
                               record.FStar_Syntax_DsEnv.typename
                              in
                           FStar_Util.format2
                             "Field %s of record type %s is missing"
                             uu____15672 uu____15674
                            in
                         (FStar_Errors.Fatal_MissingFieldInRecord,
                           uu____15670)
                          in
                       FStar_Errors.raise_error uu____15664
                         top.FStar_Parser_AST.range
                   | FStar_Pervasives_Native.Some x ->
                       (fn,
                         (FStar_Parser_AST.mk_term
                            (FStar_Parser_AST.Project (x, fn))
                            x.FStar_Parser_AST.range x.FStar_Parser_AST.level)))
               in
            let user_constrname =
              FStar_Ident.lid_of_ids
                (FStar_List.append user_ns
                   [record.FStar_Syntax_DsEnv.constrname])
               in
            let recterm =
              match eopt with
              | FStar_Pervasives_Native.None  ->
                  let uu____15685 =
                    let uu____15696 =
                      FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                        (FStar_List.map
                           (fun uu____15727  ->
                              match uu____15727 with
                              | (f,uu____15737) ->
                                  let uu____15738 =
                                    let uu____15739 =
                                      get_field FStar_Pervasives_Native.None
                                        f
                                       in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____15739
                                     in
                                  (uu____15738, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____15696)  in
                  FStar_Parser_AST.Construct uu____15685
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____15757 =
                      let uu____15758 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____15758  in
                    let uu____15759 = FStar_Ident.range_of_id x  in
                    FStar_Parser_AST.mk_term uu____15757 uu____15759
                      FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____15761 =
                      let uu____15774 =
                        FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                          (FStar_List.map
                             (fun uu____15804  ->
                                match uu____15804 with
                                | (f,uu____15814) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f))
                         in
                      (FStar_Pervasives_Native.None, uu____15774)  in
                    FStar_Parser_AST.Record uu____15761  in
                  let uu____15823 =
                    let uu____15844 =
                      let uu____15859 =
                        let uu____15872 =
                          let uu____15877 =
                            let uu____15878 = FStar_Ident.range_of_id x  in
                            FStar_Parser_AST.mk_pattern
                              (FStar_Parser_AST.PatVar
                                 (x, FStar_Pervasives_Native.None))
                              uu____15878
                             in
                          (uu____15877, e)  in
                        (FStar_Pervasives_Native.None, uu____15872)  in
                      [uu____15859]  in
                    (FStar_Parser_AST.NoLetQualifier, uu____15844,
                      (FStar_Parser_AST.mk_term record1
                         top.FStar_Parser_AST.range
                         top.FStar_Parser_AST.level))
                     in
                  FStar_Parser_AST.Let uu____15823
               in
            let recterm1 =
              FStar_Parser_AST.mk_term recterm top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let uu____15930 = desugar_term_aq env recterm1  in
            (match uu____15930 with
             | (e,s) ->
                 (match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____15946;
                         FStar_Syntax_Syntax.vars = uu____15947;_},args)
                      ->
                      let uu____15973 =
                        let uu____15974 =
                          let uu____15975 =
                            let uu____15992 =
                              let uu____15995 =
                                FStar_Ident.set_lid_range
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              let uu____15996 =
                                let uu____15999 =
                                  let uu____16000 =
                                    let uu____16007 =
                                      FStar_All.pipe_right
                                        record.FStar_Syntax_DsEnv.fields
                                        (FStar_List.map
                                           FStar_Pervasives_Native.fst)
                                       in
                                    ((record.FStar_Syntax_DsEnv.typename),
                                      uu____16007)
                                     in
                                  FStar_Syntax_Syntax.Record_ctor uu____16000
                                   in
                                FStar_Pervasives_Native.Some uu____15999  in
                              FStar_Syntax_Syntax.fvar uu____15995
                                FStar_Syntax_Syntax.delta_constant
                                uu____15996
                               in
                            (uu____15992, args)  in
                          FStar_Syntax_Syntax.Tm_app uu____15975  in
                        FStar_All.pipe_left mk1 uu____15974  in
                      (uu____15973, s)
                  | uu____16036 -> (e, s)))
        | FStar_Parser_AST.Project (e,f) ->
            let uu____16039 =
              FStar_Syntax_DsEnv.fail_or env
                (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f
               in
            (match uu____16039 with
             | (constrname,is_rec) ->
                 let uu____16058 = desugar_term_aq env e  in
                 (match uu____16058 with
                  | (e1,s) ->
                      let projname =
                        let uu____16070 = FStar_Ident.ident_of_lid f  in
                        FStar_Syntax_Util.mk_field_projector_name_from_ident
                          constrname uu____16070
                         in
                      let qual =
                        if is_rec
                        then
                          let uu____16077 =
                            let uu____16078 =
                              let uu____16083 = FStar_Ident.ident_of_lid f
                                 in
                              (constrname, uu____16083)  in
                            FStar_Syntax_Syntax.Record_projector uu____16078
                             in
                          FStar_Pervasives_Native.Some uu____16077
                        else FStar_Pervasives_Native.None  in
                      let uu____16086 =
                        let uu____16087 =
                          let uu____16088 =
                            let uu____16105 =
                              let uu____16108 =
                                let uu____16109 = FStar_Ident.range_of_lid f
                                   in
                                FStar_Ident.set_lid_range projname
                                  uu____16109
                                 in
                              FStar_Syntax_Syntax.fvar uu____16108
                                (FStar_Syntax_Syntax.Delta_equational_at_level
                                   Prims.int_one) qual
                               in
                            let uu____16111 =
                              let uu____16122 = FStar_Syntax_Syntax.as_arg e1
                                 in
                              [uu____16122]  in
                            (uu____16105, uu____16111)  in
                          FStar_Syntax_Syntax.Tm_app uu____16088  in
                        FStar_All.pipe_left mk1 uu____16087  in
                      (uu____16086, s)))
        | FStar_Parser_AST.NamedTyp (n1,e) ->
            ((let uu____16162 = FStar_Ident.range_of_id n1  in
              FStar_Errors.log_issue uu____16162
                (FStar_Errors.Warning_IgnoredBinding,
                  "This name is being ignored"));
             desugar_term_aq env e)
        | FStar_Parser_AST.Paren e -> failwith "impossible"
        | FStar_Parser_AST.VQuote e ->
            let tm = desugar_term env e  in
            let uu____16173 =
              let uu____16174 = FStar_Syntax_Subst.compress tm  in
              uu____16174.FStar_Syntax_Syntax.n  in
            (match uu____16173 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____16182 =
                   let uu___2089_16183 =
                     let uu____16184 =
                       let uu____16186 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Ident.string_of_lid uu____16186  in
                     FStar_Syntax_Util.exp_string uu____16184  in
                   {
                     FStar_Syntax_Syntax.n =
                       (uu___2089_16183.FStar_Syntax_Syntax.n);
                     FStar_Syntax_Syntax.pos = (e.FStar_Parser_AST.range);
                     FStar_Syntax_Syntax.vars =
                       (uu___2089_16183.FStar_Syntax_Syntax.vars)
                   }  in
                 (uu____16182, noaqs)
             | uu____16187 ->
                 let uu____16188 =
                   let uu____16194 =
                     let uu____16196 = FStar_Syntax_Print.term_to_string tm
                        in
                     Prims.op_Hat "VQuote, expected an fvar, got: "
                       uu____16196
                      in
                   (FStar_Errors.Fatal_UnexpectedTermVQuote, uu____16194)  in
                 FStar_Errors.raise_error uu____16188
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Static ) ->
            let uu____16205 = desugar_term_aq env e  in
            (match uu____16205 with
             | (tm,vts) ->
                 let qi =
                   {
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static;
                     FStar_Syntax_Syntax.antiquotes = vts
                   }  in
                 let uu____16217 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_quoted (tm, qi))
                    in
                 (uu____16217, noaqs))
        | FStar_Parser_AST.Antiquote e ->
            let bv =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (e.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let uu____16222 = FStar_Syntax_Syntax.bv_to_name bv  in
            let uu____16223 =
              let uu____16224 =
                let uu____16231 = desugar_term env e  in (bv, uu____16231)
                 in
              [uu____16224]  in
            (uu____16222, uu____16223)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Dynamic ) ->
            let qi =
              {
                FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
                FStar_Syntax_Syntax.antiquotes = []
              }  in
            let uu____16256 =
              let uu____16257 =
                let uu____16258 =
                  let uu____16265 = desugar_term env e  in (uu____16265, qi)
                   in
                FStar_Syntax_Syntax.Tm_quoted uu____16258  in
              FStar_All.pipe_left mk1 uu____16257  in
            (uu____16256, noaqs)
        | FStar_Parser_AST.CalcProof (rel,init_expr,steps) ->
            let is_impl rel1 =
              let is_impl_t t =
                match t.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.imp_lid
                | uu____16294 -> false  in
              let uu____16296 =
                let uu____16297 = unparen rel1  in
                uu____16297.FStar_Parser_AST.tm  in
              match uu____16296 with
              | FStar_Parser_AST.Op (id1,uu____16300) ->
                  let uu____16305 =
                    op_as_term env (Prims.of_int (2)) FStar_Range.dummyRange
                      id1
                     in
                  (match uu____16305 with
                   | FStar_Pervasives_Native.Some t -> is_impl_t t
                   | FStar_Pervasives_Native.None  -> false)
              | FStar_Parser_AST.Var lid ->
                  let uu____16313 = desugar_name' (fun x  -> x) env true lid
                     in
                  (match uu____16313 with
                   | FStar_Pervasives_Native.Some t -> is_impl_t t
                   | FStar_Pervasives_Native.None  -> false)
              | FStar_Parser_AST.Tvar id1 ->
                  let uu____16324 = FStar_Syntax_DsEnv.try_lookup_id env id1
                     in
                  (match uu____16324 with
                   | FStar_Pervasives_Native.Some t -> is_impl_t t
                   | FStar_Pervasives_Native.None  -> false)
              | uu____16330 -> false  in
            let eta_and_annot rel1 =
              let x = FStar_Ident.gen' "x" rel1.FStar_Parser_AST.range  in
              let y = FStar_Ident.gen' "y" rel1.FStar_Parser_AST.range  in
              let xt =
                FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar x)
                  rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                 in
              let yt =
                FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar y)
                  rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                 in
              let pats =
                [FStar_Parser_AST.mk_pattern
                   (FStar_Parser_AST.PatVar (x, FStar_Pervasives_Native.None))
                   rel1.FStar_Parser_AST.range;
                FStar_Parser_AST.mk_pattern
                  (FStar_Parser_AST.PatVar (y, FStar_Pervasives_Native.None))
                  rel1.FStar_Parser_AST.range]
                 in
              let uu____16351 =
                let uu____16352 =
                  let uu____16359 =
                    let uu____16360 =
                      let uu____16361 =
                        let uu____16370 =
                          FStar_Parser_AST.mkApp rel1
                            [(xt, FStar_Parser_AST.Nothing);
                            (yt, FStar_Parser_AST.Nothing)]
                            rel1.FStar_Parser_AST.range
                           in
                        let uu____16383 =
                          let uu____16384 =
                            let uu____16385 = FStar_Ident.lid_of_str "Type0"
                               in
                            FStar_Parser_AST.Name uu____16385  in
                          FStar_Parser_AST.mk_term uu____16384
                            rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                           in
                        (uu____16370, uu____16383,
                          FStar_Pervasives_Native.None)
                         in
                      FStar_Parser_AST.Ascribed uu____16361  in
                    FStar_Parser_AST.mk_term uu____16360
                      rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                     in
                  (pats, uu____16359)  in
                FStar_Parser_AST.Abs uu____16352  in
              FStar_Parser_AST.mk_term uu____16351
                rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
               in
            let rel1 = eta_and_annot rel  in
            let wild r =
              FStar_Parser_AST.mk_term FStar_Parser_AST.Wild r
                FStar_Parser_AST.Expr
               in
            let init1 =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.Var FStar_Parser_Const.calc_init_lid)
                FStar_Range.dummyRange FStar_Parser_AST.Expr
               in
            let push_impl r =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.Var FStar_Parser_Const.calc_push_impl_lid)
                r FStar_Parser_AST.Expr
               in
            let last_expr =
              let uu____16406 = FStar_List.last steps  in
              match uu____16406 with
              | FStar_Pervasives_Native.Some (FStar_Parser_AST.CalcStep
                  (uu____16409,uu____16410,last_expr)) -> last_expr
              | uu____16412 -> failwith "impossible: no last_expr on calc"
               in
            let step r =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.Var FStar_Parser_Const.calc_step_lid) r
                FStar_Parser_AST.Expr
               in
            let finish1 =
              FStar_Parser_AST.mkApp
                (FStar_Parser_AST.mk_term
                   (FStar_Parser_AST.Var FStar_Parser_Const.calc_finish_lid)
                   top.FStar_Parser_AST.range FStar_Parser_AST.Expr)
                [(rel1, FStar_Parser_AST.Nothing)] top.FStar_Parser_AST.range
               in
            let e =
              FStar_Parser_AST.mkApp init1
                [(init_expr, FStar_Parser_AST.Nothing)]
                FStar_Range.dummyRange
               in
            let uu____16440 =
              FStar_List.fold_left
                (fun uu____16458  ->
                   fun uu____16459  ->
                     match (uu____16458, uu____16459) with
                     | ((e1,prev),FStar_Parser_AST.CalcStep
                        (rel2,just,next_expr)) ->
                         let just1 =
                           let uu____16482 = is_impl rel2  in
                           if uu____16482
                           then
                             let uu____16485 =
                               let uu____16492 =
                                 let uu____16497 =
                                   FStar_Parser_AST.thunk just  in
                                 (uu____16497, FStar_Parser_AST.Nothing)  in
                               [uu____16492]  in
                             FStar_Parser_AST.mkApp
                               (push_impl just.FStar_Parser_AST.range)
                               uu____16485 just.FStar_Parser_AST.range
                           else just  in
                         let pf =
                           let uu____16509 =
                             let uu____16516 =
                               let uu____16523 =
                                 let uu____16530 =
                                   let uu____16537 =
                                     let uu____16542 = eta_and_annot rel2  in
                                     (uu____16542, FStar_Parser_AST.Nothing)
                                      in
                                   let uu____16543 =
                                     let uu____16550 =
                                       let uu____16557 =
                                         let uu____16562 =
                                           FStar_Parser_AST.thunk e1  in
                                         (uu____16562,
                                           FStar_Parser_AST.Nothing)
                                          in
                                       let uu____16563 =
                                         let uu____16570 =
                                           let uu____16575 =
                                             FStar_Parser_AST.thunk just1  in
                                           (uu____16575,
                                             FStar_Parser_AST.Nothing)
                                            in
                                         [uu____16570]  in
                                       uu____16557 :: uu____16563  in
                                     (next_expr, FStar_Parser_AST.Nothing) ::
                                       uu____16550
                                      in
                                   uu____16537 :: uu____16543  in
                                 (prev, FStar_Parser_AST.Hash) :: uu____16530
                                  in
                               (init_expr, FStar_Parser_AST.Hash) ::
                                 uu____16523
                                in
                             ((wild rel2.FStar_Parser_AST.range),
                               FStar_Parser_AST.Hash) :: uu____16516
                              in
                           FStar_Parser_AST.mkApp
                             (step rel2.FStar_Parser_AST.range) uu____16509
                             FStar_Range.dummyRange
                            in
                         (pf, next_expr)) (e, init_expr) steps
               in
            (match uu____16440 with
             | (e1,uu____16613) ->
                 let e2 =
                   let uu____16615 =
                     let uu____16622 =
                       let uu____16629 =
                         let uu____16636 =
                           let uu____16641 = FStar_Parser_AST.thunk e1  in
                           (uu____16641, FStar_Parser_AST.Nothing)  in
                         [uu____16636]  in
                       (last_expr, FStar_Parser_AST.Hash) :: uu____16629  in
                     (init_expr, FStar_Parser_AST.Hash) :: uu____16622  in
                   FStar_Parser_AST.mkApp finish1 uu____16615
                     FStar_Range.dummyRange
                    in
                 desugar_term_maybe_top top_level env e2)
        | uu____16658 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            let uu____16659 = desugar_formula env top  in
            (uu____16659, noaqs)
        | uu____16660 ->
            let uu____16661 =
              let uu____16667 =
                let uu____16669 = FStar_Parser_AST.term_to_string top  in
                Prims.op_Hat "Unexpected term: " uu____16669  in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____16667)  in
            FStar_Errors.raise_error uu____16661 top.FStar_Parser_AST.range

and (desugar_args :
  FStar_Syntax_DsEnv.env ->
    (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list)
  =
  fun env  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____16713  ->
              match uu____16713 with
              | (a,imp) ->
                  let uu____16726 = desugar_term env a  in
                  arg_withimp_e imp uu____16726))

and (desugar_comp :
  FStar_Range.range ->
    Prims.bool ->
      FStar_Syntax_DsEnv.env ->
        FStar_Parser_AST.term ->
          FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)
  =
  fun r  ->
    fun allow_type_promotion  ->
      fun env  ->
        fun t  ->
          let fail1 err = FStar_Errors.raise_error err r  in
          let is_requires uu____16763 =
            match uu____16763 with
            | (t1,uu____16770) ->
                let uu____16771 =
                  let uu____16772 = unparen t1  in
                  uu____16772.FStar_Parser_AST.tm  in
                (match uu____16771 with
                 | FStar_Parser_AST.Requires uu____16774 -> true
                 | uu____16783 -> false)
             in
          let is_ensures uu____16795 =
            match uu____16795 with
            | (t1,uu____16802) ->
                let uu____16803 =
                  let uu____16804 = unparen t1  in
                  uu____16804.FStar_Parser_AST.tm  in
                (match uu____16803 with
                 | FStar_Parser_AST.Ensures uu____16806 -> true
                 | uu____16815 -> false)
             in
          let is_app head1 uu____16833 =
            match uu____16833 with
            | (t1,uu____16841) ->
                let uu____16842 =
                  let uu____16843 = unparen t1  in
                  uu____16843.FStar_Parser_AST.tm  in
                (match uu____16842 with
                 | FStar_Parser_AST.App
                     ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                        FStar_Parser_AST.range = uu____16846;
                        FStar_Parser_AST.level = uu____16847;_},uu____16848,uu____16849)
                     ->
                     let uu____16850 =
                       let uu____16852 = FStar_Ident.ident_of_lid d  in
                       FStar_Ident.text_of_id uu____16852  in
                     uu____16850 = head1
                 | uu____16854 -> false)
             in
          let is_smt_pat uu____16866 =
            match uu____16866 with
            | (t1,uu____16873) ->
                let uu____16874 =
                  let uu____16875 = unparen t1  in
                  uu____16875.FStar_Parser_AST.tm  in
                (match uu____16874 with
                 | FStar_Parser_AST.Construct
                     (cons1,({
                               FStar_Parser_AST.tm =
                                 FStar_Parser_AST.Construct
                                 (smtpat,uu____16879);
                               FStar_Parser_AST.range = uu____16880;
                               FStar_Parser_AST.level = uu____16881;_},uu____16882)::uu____16883::[])
                     ->
                     (FStar_Ident.lid_equals cons1
                        FStar_Parser_Const.cons_lid)
                       &&
                       (FStar_Util.for_some
                          (fun s  ->
                             let uu____16923 =
                               FStar_Ident.string_of_lid smtpat  in
                             uu____16923 = s)
                          ["SMTPat"; "SMTPatT"; "SMTPatOr"])
                 | FStar_Parser_AST.Construct
                     (cons1,({
                               FStar_Parser_AST.tm = FStar_Parser_AST.Var
                                 smtpat;
                               FStar_Parser_AST.range = uu____16935;
                               FStar_Parser_AST.level = uu____16936;_},uu____16937)::uu____16938::[])
                     ->
                     (FStar_Ident.lid_equals cons1
                        FStar_Parser_Const.cons_lid)
                       &&
                       (FStar_Util.for_some
                          (fun s  ->
                             let uu____16966 =
                               FStar_Ident.string_of_lid smtpat  in
                             uu____16966 = s) ["smt_pat"; "smt_pat_or"])
                 | uu____16974 -> false)
             in
          let is_decreases = is_app "decreases"  in
          let pre_process_comp_typ t1 =
            let uu____17009 = head_and_args t1  in
            match uu____17009 with
            | (head1,args) ->
                (match head1.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.Name lemma when
                     let uu____17067 =
                       let uu____17069 = FStar_Ident.ident_of_lid lemma  in
                       FStar_Ident.text_of_id uu____17069  in
                     uu____17067 = "Lemma" ->
                     let unit_tm =
                       ((FStar_Parser_AST.mk_term
                           (FStar_Parser_AST.Name FStar_Parser_Const.unit_lid)
                           t1.FStar_Parser_AST.range
                           FStar_Parser_AST.Type_level),
                         FStar_Parser_AST.Nothing)
                        in
                     let nil_pat =
                       ((FStar_Parser_AST.mk_term
                           (FStar_Parser_AST.Name FStar_Parser_Const.nil_lid)
                           t1.FStar_Parser_AST.range FStar_Parser_AST.Expr),
                         FStar_Parser_AST.Nothing)
                        in
                     let req_true =
                       let req =
                         FStar_Parser_AST.Requires
                           ((FStar_Parser_AST.mk_term
                               (FStar_Parser_AST.Name
                                  FStar_Parser_Const.true_lid)
                               t1.FStar_Parser_AST.range
                               FStar_Parser_AST.Formula),
                             FStar_Pervasives_Native.None)
                          in
                       ((FStar_Parser_AST.mk_term req
                           t1.FStar_Parser_AST.range
                           FStar_Parser_AST.Type_level),
                         FStar_Parser_AST.Nothing)
                        in
                     let thunk_ens uu____17105 =
                       match uu____17105 with
                       | (e,i) ->
                           let uu____17116 = FStar_Parser_AST.thunk e  in
                           (uu____17116, i)
                        in
                     let fail_lemma uu____17128 =
                       let expected_one_of =
                         ["Lemma post";
                         "Lemma (ensures post)";
                         "Lemma (requires pre) (ensures post)";
                         "Lemma post [SMTPat ...]";
                         "Lemma (ensures post) [SMTPat ...]";
                         "Lemma (ensures post) (decreases d)";
                         "Lemma (ensures post) (decreases d) [SMTPat ...]";
                         "Lemma (requires pre) (ensures post) (decreases d)";
                         "Lemma (requires pre) (ensures post) [SMTPat ...]";
                         "Lemma (requires pre) (ensures post) (decreases d) [SMTPat ...]"]
                          in
                       let msg = FStar_String.concat "\n\t" expected_one_of
                          in
                       FStar_Errors.raise_error
                         (FStar_Errors.Fatal_InvalidLemmaArgument,
                           (Prims.op_Hat
                              "Invalid arguments to 'Lemma'; expected one of the following:\n\t"
                              msg)) t1.FStar_Parser_AST.range
                        in
                     let args1 =
                       match args with
                       | [] -> fail_lemma ()
                       | req::[] when is_requires req -> fail_lemma ()
                       | smtpat::[] when is_smt_pat smtpat -> fail_lemma ()
                       | dec::[] when is_decreases dec -> fail_lemma ()
                       | ens::[] ->
                           let uu____17234 =
                             let uu____17241 =
                               let uu____17248 = thunk_ens ens  in
                               [uu____17248; nil_pat]  in
                             req_true :: uu____17241  in
                           unit_tm :: uu____17234
                       | req::ens::[] when
                           (is_requires req) && (is_ensures ens) ->
                           let uu____17295 =
                             let uu____17302 =
                               let uu____17309 = thunk_ens ens  in
                               [uu____17309; nil_pat]  in
                             req :: uu____17302  in
                           unit_tm :: uu____17295
                       | ens::smtpat::[] when
                           (((let uu____17358 = is_requires ens  in
                              Prims.op_Negation uu____17358) &&
                               (let uu____17361 = is_smt_pat ens  in
                                Prims.op_Negation uu____17361))
                              &&
                              (let uu____17364 = is_decreases ens  in
                               Prims.op_Negation uu____17364))
                             && (is_smt_pat smtpat)
                           ->
                           let uu____17366 =
                             let uu____17373 =
                               let uu____17380 = thunk_ens ens  in
                               [uu____17380; smtpat]  in
                             req_true :: uu____17373  in
                           unit_tm :: uu____17366
                       | ens::dec::[] when
                           (is_ensures ens) && (is_decreases dec) ->
                           let uu____17427 =
                             let uu____17434 =
                               let uu____17441 = thunk_ens ens  in
                               [uu____17441; nil_pat; dec]  in
                             req_true :: uu____17434  in
                           unit_tm :: uu____17427
                       | ens::dec::smtpat::[] when
                           ((is_ensures ens) && (is_decreases dec)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____17501 =
                             let uu____17508 =
                               let uu____17515 = thunk_ens ens  in
                               [uu____17515; smtpat; dec]  in
                             req_true :: uu____17508  in
                           unit_tm :: uu____17501
                       | req::ens::dec::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_decreases dec)
                           ->
                           let uu____17575 =
                             let uu____17582 =
                               let uu____17589 = thunk_ens ens  in
                               [uu____17589; nil_pat; dec]  in
                             req :: uu____17582  in
                           unit_tm :: uu____17575
                       | req::ens::smtpat::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____17649 =
                             let uu____17656 =
                               let uu____17663 = thunk_ens ens  in
                               [uu____17663; smtpat]  in
                             req :: uu____17656  in
                           unit_tm :: uu____17649
                       | req::ens::dec::smtpat::[] when
                           (((is_requires req) && (is_ensures ens)) &&
                              (is_smt_pat smtpat))
                             && (is_decreases dec)
                           ->
                           let uu____17728 =
                             let uu____17735 =
                               let uu____17742 = thunk_ens ens  in
                               [uu____17742; dec; smtpat]  in
                             req :: uu____17735  in
                           unit_tm :: uu____17728
                       | _other -> fail_lemma ()  in
                     let head_and_attributes =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) lemma
                        in
                     (head_and_attributes, args1)
                 | FStar_Parser_AST.Name l when
                     FStar_Syntax_DsEnv.is_effect_name env l ->
                     let uu____17804 =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) l
                        in
                     (uu____17804, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____17832 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____17832
                        FStar_Parser_Const.prims_lid)
                       &&
                       (let uu____17834 =
                          let uu____17836 = FStar_Ident.ident_of_lid l  in
                          FStar_Ident.text_of_id uu____17836  in
                        uu____17834 = "Tot")
                     ->
                     let uu____17839 =
                       let uu____17846 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____17846, [])  in
                     (uu____17839, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____17864 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____17864
                        FStar_Parser_Const.prims_lid)
                       &&
                       (let uu____17866 =
                          let uu____17868 = FStar_Ident.ident_of_lid l  in
                          FStar_Ident.text_of_id uu____17868  in
                        uu____17866 = "GTot")
                     ->
                     let uu____17871 =
                       let uu____17878 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_GTot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____17878, [])  in
                     (uu____17871, args)
                 | FStar_Parser_AST.Name l when
                     ((let uu____17896 =
                         let uu____17898 = FStar_Ident.ident_of_lid l  in
                         FStar_Ident.text_of_id uu____17898  in
                       uu____17896 = "Type") ||
                        (let uu____17902 =
                           let uu____17904 = FStar_Ident.ident_of_lid l  in
                           FStar_Ident.text_of_id uu____17904  in
                         uu____17902 = "Type0"))
                       ||
                       (let uu____17908 =
                          let uu____17910 = FStar_Ident.ident_of_lid l  in
                          FStar_Ident.text_of_id uu____17910  in
                        uu____17908 = "Effect")
                     ->
                     let uu____17913 =
                       let uu____17920 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____17920, [])  in
                     (uu____17913, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____17943 when allow_type_promotion ->
                     let default_effect =
                       let uu____17945 = FStar_Options.ml_ish ()  in
                       if uu____17945
                       then FStar_Parser_Const.effect_ML_lid
                       else
                         ((let uu____17951 =
                             FStar_Options.warn_default_effects ()  in
                           if uu____17951
                           then
                             FStar_Errors.log_issue
                               head1.FStar_Parser_AST.range
                               (FStar_Errors.Warning_UseDefaultEffect,
                                 "Using default effect Tot")
                           else ());
                          FStar_Parser_Const.effect_Tot_lid)
                        in
                     let uu____17958 =
                       let uu____17965 =
                         FStar_Ident.set_lid_range default_effect
                           head1.FStar_Parser_AST.range
                          in
                       (uu____17965, [])  in
                     (uu____17958, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____17988 ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_EffectNotFound,
                         "Expected an effect constructor")
                       t1.FStar_Parser_AST.range)
             in
          let uu____18007 = pre_process_comp_typ t  in
          match uu____18007 with
          | ((eff,cattributes),args) ->
              (if (FStar_List.length args) = Prims.int_zero
               then
                 (let uu____18059 =
                    let uu____18065 =
                      let uu____18067 = FStar_Syntax_Print.lid_to_string eff
                         in
                      FStar_Util.format1 "Not enough args to effect %s"
                        uu____18067
                       in
                    (FStar_Errors.Fatal_NotEnoughArgsToEffect, uu____18065)
                     in
                  fail1 uu____18059)
               else ();
               (let is_universe uu____18083 =
                  match uu____18083 with
                  | (uu____18089,imp) -> imp = FStar_Parser_AST.UnivApp  in
                let uu____18091 = FStar_Util.take is_universe args  in
                match uu____18091 with
                | (universes,args1) ->
                    let universes1 =
                      FStar_List.map
                        (fun uu____18150  ->
                           match uu____18150 with
                           | (u,imp) -> desugar_universe u) universes
                       in
                    let uu____18157 =
                      let uu____18172 = FStar_List.hd args1  in
                      let uu____18181 = FStar_List.tl args1  in
                      (uu____18172, uu____18181)  in
                    (match uu____18157 with
                     | (result_arg,rest) ->
                         let result_typ =
                           desugar_typ env
                             (FStar_Pervasives_Native.fst result_arg)
                            in
                         let rest1 = desugar_args env rest  in
                         let uu____18236 =
                           let is_decrease uu____18275 =
                             match uu____18275 with
                             | (t1,uu____18286) ->
                                 (match t1.FStar_Syntax_Syntax.n with
                                  | FStar_Syntax_Syntax.Tm_app
                                      ({
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_fvar fv;
                                         FStar_Syntax_Syntax.pos =
                                           uu____18297;
                                         FStar_Syntax_Syntax.vars =
                                           uu____18298;_},uu____18299::[])
                                      ->
                                      FStar_Syntax_Syntax.fv_eq_lid fv
                                        FStar_Parser_Const.decreases_lid
                                  | uu____18338 -> false)
                              in
                           FStar_All.pipe_right rest1
                             (FStar_List.partition is_decrease)
                            in
                         (match uu____18236 with
                          | (dec,rest2) ->
                              let decreases_clause =
                                FStar_All.pipe_right dec
                                  (FStar_List.map
                                     (fun uu____18455  ->
                                        match uu____18455 with
                                        | (t1,uu____18465) ->
                                            (match t1.FStar_Syntax_Syntax.n
                                             with
                                             | FStar_Syntax_Syntax.Tm_app
                                                 (uu____18474,(arg,uu____18476)::[])
                                                 ->
                                                 FStar_Syntax_Syntax.DECREASES
                                                   arg
                                             | uu____18515 ->
                                                 failwith "impos")))
                                 in
                              let no_additional_args =
                                let is_empty l =
                                  match l with
                                  | [] -> true
                                  | uu____18536 -> false  in
                                (((is_empty decreases_clause) &&
                                    (is_empty rest2))
                                   && (is_empty cattributes))
                                  && (is_empty universes1)
                                 in
                              let uu____18548 =
                                no_additional_args &&
                                  (FStar_Ident.lid_equals eff
                                     FStar_Parser_Const.effect_Tot_lid)
                                 in
                              if uu____18548
                              then FStar_Syntax_Syntax.mk_Total result_typ
                              else
                                (let uu____18555 =
                                   no_additional_args &&
                                     (FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_GTot_lid)
                                    in
                                 if uu____18555
                                 then
                                   FStar_Syntax_Syntax.mk_GTotal result_typ
                                 else
                                   (let flags =
                                      let uu____18565 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____18565
                                      then [FStar_Syntax_Syntax.LEMMA]
                                      else
                                        (let uu____18572 =
                                           FStar_Ident.lid_equals eff
                                             FStar_Parser_Const.effect_Tot_lid
                                            in
                                         if uu____18572
                                         then [FStar_Syntax_Syntax.TOTAL]
                                         else
                                           (let uu____18579 =
                                              FStar_Ident.lid_equals eff
                                                FStar_Parser_Const.effect_ML_lid
                                               in
                                            if uu____18579
                                            then
                                              [FStar_Syntax_Syntax.MLEFFECT]
                                            else
                                              (let uu____18586 =
                                                 FStar_Ident.lid_equals eff
                                                   FStar_Parser_Const.effect_GTot_lid
                                                  in
                                               if uu____18586
                                               then
                                                 [FStar_Syntax_Syntax.SOMETRIVIAL]
                                               else [])))
                                       in
                                    let flags1 =
                                      FStar_List.append flags cattributes  in
                                    let rest3 =
                                      let uu____18607 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____18607
                                      then
                                        match rest2 with
                                        | req::ens::(pat,aq)::[] ->
                                            let pat1 =
                                              match pat.FStar_Syntax_Syntax.n
                                              with
                                              | FStar_Syntax_Syntax.Tm_fvar
                                                  fv when
                                                  FStar_Syntax_Syntax.fv_eq_lid
                                                    fv
                                                    FStar_Parser_Const.nil_lid
                                                  ->
                                                  let nil =
                                                    FStar_Syntax_Syntax.mk_Tm_uinst
                                                      pat
                                                      [FStar_Syntax_Syntax.U_zero]
                                                     in
                                                  let pattern =
                                                    let uu____18698 =
                                                      FStar_Ident.set_lid_range
                                                        FStar_Parser_Const.pattern_lid
                                                        pat.FStar_Syntax_Syntax.pos
                                                       in
                                                    FStar_Syntax_Syntax.fvar
                                                      uu____18698
                                                      FStar_Syntax_Syntax.delta_constant
                                                      FStar_Pervasives_Native.None
                                                     in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    nil
                                                    [(pattern,
                                                       (FStar_Pervasives_Native.Some
                                                          FStar_Syntax_Syntax.imp_tag))]
                                                    FStar_Pervasives_Native.None
                                                    pat.FStar_Syntax_Syntax.pos
                                              | uu____18719 -> pat  in
                                            let uu____18720 =
                                              let uu____18731 =
                                                let uu____18742 =
                                                  let uu____18751 =
                                                    FStar_Syntax_Syntax.mk
                                                      (FStar_Syntax_Syntax.Tm_meta
                                                         (pat1,
                                                           (FStar_Syntax_Syntax.Meta_desugared
                                                              FStar_Syntax_Syntax.Meta_smt_pat)))
                                                      FStar_Pervasives_Native.None
                                                      pat1.FStar_Syntax_Syntax.pos
                                                     in
                                                  (uu____18751, aq)  in
                                                [uu____18742]  in
                                              ens :: uu____18731  in
                                            req :: uu____18720
                                        | uu____18792 -> rest2
                                      else rest2  in
                                    FStar_Syntax_Syntax.mk_Comp
                                      {
                                        FStar_Syntax_Syntax.comp_univs =
                                          universes1;
                                        FStar_Syntax_Syntax.effect_name = eff;
                                        FStar_Syntax_Syntax.result_typ =
                                          result_typ;
                                        FStar_Syntax_Syntax.effect_args =
                                          rest3;
                                        FStar_Syntax_Syntax.flags =
                                          (FStar_List.append flags1
                                             decreases_clause)
                                      }))))))

and (desugar_formula :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun f  ->
      let mk1 t =
        FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None
          f.FStar_Parser_AST.range
         in
      let setpos t =
        let uu___2414_18827 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___2414_18827.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___2414_18827.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___2421_18881 = b  in
             {
               FStar_Parser_AST.b = (uu___2421_18881.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___2421_18881.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___2421_18881.FStar_Parser_AST.aqual)
             })
           in
        let with_pats env1 uu____18910 body1 =
          match uu____18910 with
          | (names1,pats1) ->
              (match (names1, pats1) with
               | ([],[]) -> body1
               | ([],uu____18956::uu____18957) ->
                   failwith
                     "Impossible: Annotated pattern without binders in scope"
               | uu____18975 ->
                   let names2 =
                     FStar_All.pipe_right names1
                       (FStar_List.map
                          (fun i  ->
                             let uu___2440_19003 =
                               FStar_Syntax_DsEnv.fail_or2
                                 (FStar_Syntax_DsEnv.try_lookup_id env1) i
                                in
                             let uu____19004 = FStar_Ident.range_of_id i  in
                             {
                               FStar_Syntax_Syntax.n =
                                 (uu___2440_19003.FStar_Syntax_Syntax.n);
                               FStar_Syntax_Syntax.pos = uu____19004;
                               FStar_Syntax_Syntax.vars =
                                 (uu___2440_19003.FStar_Syntax_Syntax.vars)
                             }))
                      in
                   let pats2 =
                     FStar_All.pipe_right pats1
                       (FStar_List.map
                          (fun es  ->
                             FStar_All.pipe_right es
                               (FStar_List.map
                                  (fun e  ->
                                     let uu____19067 = desugar_term env1 e
                                        in
                                     FStar_All.pipe_left
                                       (arg_withimp_t
                                          FStar_Parser_AST.Nothing)
                                       uu____19067))))
                      in
                   mk1
                     (FStar_Syntax_Syntax.Tm_meta
                        (body1,
                          (FStar_Syntax_Syntax.Meta_pattern (names2, pats2)))))
           in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____19098 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____19098 with
             | (env1,a1) ->
                 let a2 =
                   let uu___2453_19108 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___2453_19108.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___2453_19108.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let body1 = desugar_formula env1 body  in
                 let body2 = with_pats env1 pats body1  in
                 let body3 =
                   let uu____19114 =
                     let uu____19117 =
                       let uu____19118 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____19118]  in
                     no_annot_abs uu____19117 body2  in
                   FStar_All.pipe_left setpos uu____19114  in
                 let uu____19139 =
                   let uu____19140 =
                     let uu____19157 =
                       let uu____19160 =
                         FStar_Ident.set_lid_range q
                           b.FStar_Parser_AST.brange
                          in
                       FStar_Syntax_Syntax.fvar uu____19160
                         (FStar_Syntax_Syntax.Delta_constant_at_level
                            Prims.int_one) FStar_Pervasives_Native.None
                        in
                     let uu____19162 =
                       let uu____19173 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____19173]  in
                     (uu____19157, uu____19162)  in
                   FStar_Syntax_Syntax.Tm_app uu____19140  in
                 FStar_All.pipe_left mk1 uu____19139)
        | uu____19212 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____19277 = q (rest, pats, body)  in
              let uu____19280 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____19277 uu____19280
                FStar_Parser_AST.Formula
               in
            let uu____19281 = q ([b], ([], []), body1)  in
            FStar_Parser_AST.mk_term uu____19281 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____19292 -> failwith "impossible"  in
      let uu____19296 =
        let uu____19297 = unparen f  in uu____19297.FStar_Parser_AST.tm  in
      match uu____19296 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____19310,uu____19311) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____19335,uu____19336) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____19392 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____19392
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____19436 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____19436
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> failwith "impossible"
      | uu____19500 -> desugar_term env f

and (desugar_binder :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder ->
      (FStar_Ident.ident FStar_Pervasives_Native.option *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.TAnnotated (x,t) ->
          let uu____19511 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____19511)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____19516 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____19516)
      | FStar_Parser_AST.TVariable x ->
          let uu____19520 =
            let uu____19521 = FStar_Ident.range_of_id x  in
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None uu____19521
             in
          ((FStar_Pervasives_Native.Some x), uu____19520)
      | FStar_Parser_AST.NoName t ->
          let uu____19525 = desugar_typ env t  in
          (FStar_Pervasives_Native.None, uu____19525)
      | FStar_Parser_AST.Variable x ->
          ((FStar_Pervasives_Native.Some x), FStar_Syntax_Syntax.tun)

and (as_binder :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
      (FStar_Ident.ident FStar_Pervasives_Native.option *
        FStar_Syntax_Syntax.term) ->
        ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
          FStar_Pervasives_Native.option) * FStar_Syntax_DsEnv.env))
  =
  fun env  ->
    fun imp  ->
      fun uu___11_19533  ->
        match uu___11_19533 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____19555 = FStar_Syntax_Syntax.null_binder k  in
            (uu____19555, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____19572 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____19572 with
             | (env1,a1) ->
                 let uu____19589 =
                   let uu____19596 = trans_aqual env1 imp  in
                   ((let uu___2553_19602 = a1  in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___2553_19602.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___2553_19602.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = k
                     }), uu____19596)
                    in
                 (uu____19589, env1))

and (trans_aqual :
  env_t ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.aqual)
  =
  fun env  ->
    fun uu___12_19610  ->
      match uu___12_19610 with
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Equality
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta t) ->
          let uu____19614 =
            let uu____19615 = desugar_term env t  in
            FStar_Syntax_Syntax.Meta uu____19615  in
          FStar_Pervasives_Native.Some uu____19614
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None

let (typars_of_binders :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_Syntax_DsEnv.env * (FStar_Syntax_Syntax.bv *
        FStar_Syntax_Syntax.aqual) Prims.list))
  =
  fun env  ->
    fun bs  ->
      let uu____19643 =
        FStar_List.fold_left
          (fun uu____19676  ->
             fun b  ->
               match uu____19676 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___2571_19720 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___2571_19720.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___2571_19720.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___2571_19720.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____19735 = FStar_Syntax_DsEnv.push_bv env1 a
                           in
                        (match uu____19735 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___2581_19753 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___2581_19753.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___2581_19753.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             let uu____19754 =
                               let uu____19761 =
                                 let uu____19766 =
                                   trans_aqual env2 b.FStar_Parser_AST.aqual
                                    in
                                 (a2, uu____19766)  in
                               uu____19761 :: out  in
                             (env2, uu____19754))
                    | uu____19777 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs
         in
      match uu____19643 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))
  
let (desugar_attributes :
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____19865 =
          let uu____19866 = unparen t  in uu____19866.FStar_Parser_AST.tm  in
        match uu____19865 with
        | FStar_Parser_AST.Var lid when
            let uu____19868 = FStar_Ident.string_of_lid lid  in
            uu____19868 = "cps" -> FStar_Syntax_Syntax.CPS
        | uu____19872 ->
            let uu____19873 =
              let uu____19879 =
                let uu____19881 = FStar_Parser_AST.term_to_string t  in
                Prims.op_Hat "Unknown attribute " uu____19881  in
              (FStar_Errors.Fatal_UnknownAttribute, uu____19879)  in
            FStar_Errors.raise_error uu____19873 t.FStar_Parser_AST.range
         in
      FStar_List.map desugar_attribute cattributes
  
let (binder_ident :
  FStar_Parser_AST.binder -> FStar_Ident.ident FStar_Pervasives_Native.option)
  =
  fun b  ->
    match b.FStar_Parser_AST.b with
    | FStar_Parser_AST.TAnnotated (x,uu____19898) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Annotated (x,uu____19900) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.TVariable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Variable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.NoName uu____19903 -> FStar_Pervasives_Native.None
  
let (binder_idents :
  FStar_Parser_AST.binder Prims.list -> FStar_Ident.ident Prims.list) =
  fun bs  ->
    FStar_List.collect
      (fun b  ->
         let uu____19921 = binder_ident b  in
         FStar_Common.list_of_option uu____19921) bs
  
let (mk_data_discriminators :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_Syntax_DsEnv.env ->
      FStar_Ident.lident Prims.list -> FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun quals  ->
    fun env  ->
      fun datas  ->
        let quals1 =
          FStar_All.pipe_right quals
            (FStar_List.filter
               (fun uu___13_19958  ->
                  match uu___13_19958 with
                  | FStar_Syntax_Syntax.NoExtract  -> true
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____19963 -> false))
           in
        let quals2 q =
          let uu____19977 =
            (let uu____19981 = FStar_Syntax_DsEnv.iface env  in
             Prims.op_Negation uu____19981) ||
              (FStar_Syntax_DsEnv.admitted_iface env)
             in
          if uu____19977
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1  in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d  in
                let uu____19998 = FStar_Ident.range_of_lid disc_name  in
                let uu____19999 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d]
                   in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng = uu____19998;
                  FStar_Syntax_Syntax.sigquals = uu____19999;
                  FStar_Syntax_Syntax.sigmeta =
                    FStar_Syntax_Syntax.default_sigmeta;
                  FStar_Syntax_Syntax.sigattrs = [];
                  FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
                }))
  
let (mk_indexed_projector_names :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_Syntax_Syntax.fv_qual ->
      FStar_Syntax_DsEnv.env ->
        FStar_Ident.lident ->
          FStar_Syntax_Syntax.binder Prims.list ->
            FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun iquals  ->
    fun fvq  ->
      fun env  ->
        fun lid  ->
          fun fields  ->
            let p = FStar_Ident.range_of_lid lid  in
            let uu____20039 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____20075  ->
                        match uu____20075 with
                        | (x,uu____20086) ->
                            let field_name =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            let only_decl =
                              ((let uu____20096 =
                                  FStar_Syntax_DsEnv.current_module env  in
                                FStar_Ident.lid_equals
                                  FStar_Parser_Const.prims_lid uu____20096)
                                 || (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                ||
                                (let uu____20098 =
                                   let uu____20100 =
                                     FStar_Syntax_DsEnv.current_module env
                                      in
                                   FStar_Ident.string_of_lid uu____20100  in
                                 FStar_Options.dont_gen_projectors
                                   uu____20098)
                               in
                            let no_decl =
                              FStar_Syntax_Syntax.is_type
                                x.FStar_Syntax_Syntax.sort
                               in
                            let quals q =
                              if only_decl
                              then
                                let uu____20118 =
                                  FStar_List.filter
                                    (fun uu___14_20122  ->
                                       match uu___14_20122 with
                                       | FStar_Syntax_Syntax.Abstract  ->
                                           false
                                       | uu____20125 -> true) q
                                   in
                                FStar_Syntax_Syntax.Assumption :: uu____20118
                              else q  in
                            let quals1 =
                              let iquals1 =
                                FStar_All.pipe_right iquals
                                  (FStar_List.filter
                                     (fun uu___15_20140  ->
                                        match uu___15_20140 with
                                        | FStar_Syntax_Syntax.NoExtract  ->
                                            true
                                        | FStar_Syntax_Syntax.Abstract  ->
                                            true
                                        | FStar_Syntax_Syntax.Private  ->
                                            true
                                        | uu____20145 -> false))
                                 in
                              quals (FStar_Syntax_Syntax.OnlyName ::
                                (FStar_Syntax_Syntax.Projector
                                   (lid, (x.FStar_Syntax_Syntax.ppname))) ::
                                iquals1)
                               in
                            let decl =
                              let uu____20148 =
                                FStar_Ident.range_of_lid field_name  in
                              {
                                FStar_Syntax_Syntax.sigel =
                                  (FStar_Syntax_Syntax.Sig_declare_typ
                                     (field_name, [],
                                       FStar_Syntax_Syntax.tun));
                                FStar_Syntax_Syntax.sigrng = uu____20148;
                                FStar_Syntax_Syntax.sigquals = quals1;
                                FStar_Syntax_Syntax.sigmeta =
                                  FStar_Syntax_Syntax.default_sigmeta;
                                FStar_Syntax_Syntax.sigattrs = [];
                                FStar_Syntax_Syntax.sigopts =
                                  FStar_Pervasives_Native.None
                              }  in
                            if only_decl
                            then [decl]
                            else
                              (let dd =
                                 let uu____20155 =
                                   FStar_All.pipe_right quals1
                                     (FStar_List.contains
                                        FStar_Syntax_Syntax.Abstract)
                                    in
                                 if uu____20155
                                 then
                                   FStar_Syntax_Syntax.Delta_abstract
                                     (FStar_Syntax_Syntax.Delta_equational_at_level
                                        Prims.int_one)
                                 else
                                   FStar_Syntax_Syntax.Delta_equational_at_level
                                     Prims.int_one
                                  in
                               let lb =
                                 let uu____20166 =
                                   let uu____20171 =
                                     FStar_Syntax_Syntax.lid_as_fv field_name
                                       dd FStar_Pervasives_Native.None
                                      in
                                   FStar_Util.Inr uu____20171  in
                                 {
                                   FStar_Syntax_Syntax.lbname = uu____20166;
                                   FStar_Syntax_Syntax.lbunivs = [];
                                   FStar_Syntax_Syntax.lbtyp =
                                     FStar_Syntax_Syntax.tun;
                                   FStar_Syntax_Syntax.lbeff =
                                     FStar_Parser_Const.effect_Tot_lid;
                                   FStar_Syntax_Syntax.lbdef =
                                     FStar_Syntax_Syntax.tun;
                                   FStar_Syntax_Syntax.lbattrs = [];
                                   FStar_Syntax_Syntax.lbpos =
                                     FStar_Range.dummyRange
                                 }  in
                               let impl =
                                 let uu____20175 =
                                   let uu____20176 =
                                     let uu____20183 =
                                       let uu____20186 =
                                         let uu____20187 =
                                           FStar_All.pipe_right
                                             lb.FStar_Syntax_Syntax.lbname
                                             FStar_Util.right
                                            in
                                         FStar_All.pipe_right uu____20187
                                           (fun fv  ->
                                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                          in
                                       [uu____20186]  in
                                     ((false, [lb]), uu____20183)  in
                                   FStar_Syntax_Syntax.Sig_let uu____20176
                                    in
                                 {
                                   FStar_Syntax_Syntax.sigel = uu____20175;
                                   FStar_Syntax_Syntax.sigrng = p;
                                   FStar_Syntax_Syntax.sigquals = quals1;
                                   FStar_Syntax_Syntax.sigmeta =
                                     FStar_Syntax_Syntax.default_sigmeta;
                                   FStar_Syntax_Syntax.sigattrs = [];
                                   FStar_Syntax_Syntax.sigopts =
                                     FStar_Pervasives_Native.None
                                 }  in
                               if no_decl then [impl] else [decl; impl])))
               in
            FStar_All.pipe_right uu____20039 FStar_List.flatten
  
let (mk_data_projector_names :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_Syntax_DsEnv.env ->
      FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun iquals  ->
    fun env  ->
      fun se  ->
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_datacon
            (lid,uu____20236,t,uu____20238,n1,uu____20240) when
            let uu____20247 =
              FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid  in
            Prims.op_Negation uu____20247 ->
            let uu____20249 = FStar_Syntax_Util.arrow_formals t  in
            (match uu____20249 with
             | (formals,uu____20259) ->
                 (match formals with
                  | [] -> []
                  | uu____20272 ->
                      let filter_records uu___16_20280 =
                        match uu___16_20280 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____20283,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____20295 -> FStar_Pervasives_Native.None  in
                      let fv_qual =
                        let uu____20297 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records
                           in
                        match uu____20297 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Syntax_Syntax.Data_ctor
                        | FStar_Pervasives_Native.Some q -> q  in
                      let iquals1 =
                        if
                          (FStar_List.contains FStar_Syntax_Syntax.Abstract
                             iquals)
                            &&
                            (Prims.op_Negation
                               (FStar_List.contains
                                  FStar_Syntax_Syntax.Private iquals))
                        then FStar_Syntax_Syntax.Private :: iquals
                        else iquals  in
                      let uu____20309 = FStar_Util.first_N n1 formals  in
                      (match uu____20309 with
                       | (uu____20338,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____20372 -> []
  
let (mk_typ_abbrev :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.decl ->
      FStar_Ident.lident ->
        FStar_Syntax_Syntax.univ_name Prims.list ->
          (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
            FStar_Pervasives_Native.option) Prims.list ->
            FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
              FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
                FStar_Ident.lident Prims.list ->
                  FStar_Syntax_Syntax.qualifier Prims.list ->
                    FStar_Range.range -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun d  ->
      fun lid  ->
        fun uvs  ->
          fun typars  ->
            fun kopt  ->
              fun t  ->
                fun lids  ->
                  fun quals  ->
                    fun rng  ->
                      let attrs =
                        FStar_List.map (desugar_term env)
                          d.FStar_Parser_AST.attrs
                         in
                      let val_attrs =
                        let uu____20466 =
                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                            env lid
                           in
                        FStar_All.pipe_right uu____20466
                          FStar_Pervasives_Native.snd
                         in
                      let dd =
                        let uu____20490 =
                          FStar_All.pipe_right quals
                            (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                           in
                        if uu____20490
                        then
                          let uu____20496 =
                            FStar_Syntax_Util.incr_delta_qualifier t  in
                          FStar_Syntax_Syntax.Delta_abstract uu____20496
                        else FStar_Syntax_Util.incr_delta_qualifier t  in
                      let lb =
                        let uu____20500 =
                          let uu____20505 =
                            FStar_Syntax_Syntax.lid_as_fv lid dd
                              FStar_Pervasives_Native.None
                             in
                          FStar_Util.Inr uu____20505  in
                        let uu____20506 =
                          if FStar_Util.is_some kopt
                          then
                            let uu____20512 =
                              let uu____20515 =
                                FStar_All.pipe_right kopt FStar_Util.must  in
                              FStar_Syntax_Syntax.mk_Total uu____20515  in
                            FStar_Syntax_Util.arrow typars uu____20512
                          else FStar_Syntax_Syntax.tun  in
                        let uu____20520 = no_annot_abs typars t  in
                        {
                          FStar_Syntax_Syntax.lbname = uu____20500;
                          FStar_Syntax_Syntax.lbunivs = uvs;
                          FStar_Syntax_Syntax.lbtyp = uu____20506;
                          FStar_Syntax_Syntax.lbeff =
                            FStar_Parser_Const.effect_Tot_lid;
                          FStar_Syntax_Syntax.lbdef = uu____20520;
                          FStar_Syntax_Syntax.lbattrs = [];
                          FStar_Syntax_Syntax.lbpos = rng
                        }  in
                      {
                        FStar_Syntax_Syntax.sigel =
                          (FStar_Syntax_Syntax.Sig_let ((false, [lb]), lids));
                        FStar_Syntax_Syntax.sigrng = rng;
                        FStar_Syntax_Syntax.sigquals = quals;
                        FStar_Syntax_Syntax.sigmeta =
                          FStar_Syntax_Syntax.default_sigmeta;
                        FStar_Syntax_Syntax.sigattrs =
                          (FStar_List.append val_attrs attrs);
                        FStar_Syntax_Syntax.sigopts =
                          FStar_Pervasives_Native.None
                      }
  
let rec (desugar_tycon :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.decl ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Parser_AST.tycon Prims.list ->
          (env_t * FStar_Syntax_Syntax.sigelts))
  =
  fun env  ->
    fun d  ->
      fun quals  ->
        fun tcs  ->
          let rng = d.FStar_Parser_AST.drange  in
          let tycon_id uu___17_20574 =
            match uu___17_20574 with
            | FStar_Parser_AST.TyconAbstract (id1,uu____20576,uu____20577) ->
                id1
            | FStar_Parser_AST.TyconAbbrev
                (id1,uu____20587,uu____20588,uu____20589) -> id1
            | FStar_Parser_AST.TyconRecord
                (id1,uu____20599,uu____20600,uu____20601) -> id1
            | FStar_Parser_AST.TyconVariant
                (id1,uu____20623,uu____20624,uu____20625) -> id1
             in
          let binder_to_term1 b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____20663) ->
                let uu____20664 =
                  let uu____20665 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____20665  in
                let uu____20666 = FStar_Ident.range_of_id x  in
                FStar_Parser_AST.mk_term uu____20664 uu____20666
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____20668 =
                  let uu____20669 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____20669  in
                let uu____20670 = FStar_Ident.range_of_id x  in
                FStar_Parser_AST.mk_term uu____20668 uu____20670
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____20672) ->
                let uu____20673 = FStar_Ident.range_of_id a  in
                FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar a)
                  uu____20673 FStar_Parser_AST.Type_level
            | FStar_Parser_AST.TVariable a ->
                let uu____20675 = FStar_Ident.range_of_id a  in
                FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar a)
                  uu____20675 FStar_Parser_AST.Type_level
            | FStar_Parser_AST.NoName t -> t  in
          let tot =
            FStar_Parser_AST.mk_term
              (FStar_Parser_AST.Name FStar_Parser_Const.effect_Tot_lid) rng
              FStar_Parser_AST.Expr
             in
          let with_constructor_effect t =
            FStar_Parser_AST.mk_term
              (FStar_Parser_AST.App (tot, t, FStar_Parser_AST.Nothing))
              t.FStar_Parser_AST.range t.FStar_Parser_AST.level
             in
          let apply_binders t binders =
            let imp_of_aqual b =
              match b.FStar_Parser_AST.aqual with
              | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit ) ->
                  FStar_Parser_AST.Hash
              | uu____20705 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____20713 =
                     let uu____20714 =
                       let uu____20721 = binder_to_term1 b  in
                       (out, uu____20721, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____20714  in
                   FStar_Parser_AST.mk_term uu____20713
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___18_20733 =
            match uu___18_20733 with
            | FStar_Parser_AST.TyconRecord (id1,parms,kopt,fields) ->
                let constrName =
                  let uu____20765 =
                    let uu____20771 =
                      let uu____20773 = FStar_Ident.text_of_id id1  in
                      Prims.op_Hat "Mk" uu____20773  in
                    let uu____20776 = FStar_Ident.range_of_id id1  in
                    (uu____20771, uu____20776)  in
                  FStar_Ident.mk_ident uu____20765  in
                let mfields =
                  FStar_List.map
                    (fun uu____20789  ->
                       match uu____20789 with
                       | (x,t) ->
                           let uu____20796 = FStar_Ident.range_of_id x  in
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated (x, t)) uu____20796
                             FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields
                   in
                let result =
                  let uu____20798 =
                    let uu____20799 =
                      let uu____20800 = FStar_Ident.lid_of_ids [id1]  in
                      FStar_Parser_AST.Var uu____20800  in
                    let uu____20801 = FStar_Ident.range_of_id id1  in
                    FStar_Parser_AST.mk_term uu____20799 uu____20801
                      FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____20798 parms  in
                let constrTyp =
                  let uu____20803 = FStar_Ident.range_of_id id1  in
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    uu____20803 FStar_Parser_AST.Type_level
                   in
                let names1 =
                  let uu____20809 = binder_idents parms  in id1 ::
                    uu____20809
                   in
                (FStar_List.iter
                   (fun uu____20823  ->
                      match uu____20823 with
                      | (f,uu____20829) ->
                          let uu____20830 =
                            FStar_Util.for_some
                              (fun i  -> FStar_Ident.ident_equals f i) names1
                             in
                          if uu____20830
                          then
                            let uu____20835 =
                              let uu____20841 =
                                let uu____20843 = FStar_Ident.text_of_id f
                                   in
                                FStar_Util.format1
                                  "Field %s shadows the record's name or a parameter of it, please rename it"
                                  uu____20843
                                 in
                              (FStar_Errors.Error_FieldShadow, uu____20841)
                               in
                            let uu____20847 = FStar_Ident.range_of_id f  in
                            FStar_Errors.raise_error uu____20835 uu____20847
                          else ()) fields;
                 (let uu____20850 =
                    FStar_All.pipe_right fields
                      (FStar_List.map FStar_Pervasives_Native.fst)
                     in
                  ((FStar_Parser_AST.TyconVariant
                      (id1, parms, kopt,
                        [(constrName,
                           (FStar_Pervasives_Native.Some constrTyp), false)])),
                    uu____20850)))
            | uu____20904 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___19_20944 =
            match uu___19_20944 with
            | FStar_Parser_AST.TyconAbstract (id1,binders,kopt) ->
                let uu____20968 = typars_of_binders _env binders  in
                (match uu____20968 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k
                        in
                     let tconstr =
                       let uu____21004 =
                         let uu____21005 =
                           let uu____21006 = FStar_Ident.lid_of_ids [id1]  in
                           FStar_Parser_AST.Var uu____21006  in
                         let uu____21007 = FStar_Ident.range_of_id id1  in
                         FStar_Parser_AST.mk_term uu____21005 uu____21007
                           FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____21004 binders  in
                     let qlid = FStar_Syntax_DsEnv.qualify _env id1  in
                     let typars1 = FStar_Syntax_Subst.close_binders typars
                        in
                     let k1 = FStar_Syntax_Subst.close typars1 k  in
                     let se =
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_inductive_typ
                              (qlid, [], typars1, k1, mutuals, []));
                         FStar_Syntax_Syntax.sigrng = rng;
                         FStar_Syntax_Syntax.sigquals = quals1;
                         FStar_Syntax_Syntax.sigmeta =
                           FStar_Syntax_Syntax.default_sigmeta;
                         FStar_Syntax_Syntax.sigattrs = [];
                         FStar_Syntax_Syntax.sigopts =
                           FStar_Pervasives_Native.None
                       }  in
                     let uu____21016 =
                       FStar_Syntax_DsEnv.push_top_level_rec_binding _env id1
                         FStar_Syntax_Syntax.delta_constant
                        in
                     (match uu____21016 with
                      | (_env1,uu____21033) ->
                          let uu____21040 =
                            FStar_Syntax_DsEnv.push_top_level_rec_binding
                              _env' id1 FStar_Syntax_Syntax.delta_constant
                             in
                          (match uu____21040 with
                           | (_env2,uu____21057) ->
                               (_env1, _env2, se, tconstr))))
            | uu____21064 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____21107 =
              FStar_List.fold_left
                (fun uu____21141  ->
                   fun uu____21142  ->
                     match (uu____21141, uu____21142) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____21211 =
                           FStar_Syntax_DsEnv.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____21211 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____21107 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id1,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____21302 =
                      let uu____21303 = FStar_Ident.range_of_id id1  in
                      tm_type_z uu____21303  in
                    FStar_Pervasives_Native.Some uu____21302
                | uu____21304 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id1, bs, kopt1)  in
              let uu____21312 = desugar_abstract_tc quals env [] tc  in
              (match uu____21312 with
               | (uu____21325,uu____21326,se,uu____21328) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____21331,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals  in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____21350 =
                                 let uu____21352 = FStar_Options.ml_ish ()
                                    in
                                 Prims.op_Negation uu____21352  in
                               if uu____21350
                               then
                                 let uu____21355 =
                                   let uu____21361 =
                                     let uu____21363 =
                                       FStar_Syntax_Print.lid_to_string l  in
                                     FStar_Util.format1
                                       "Adding an implicit 'assume new' qualifier on %s"
                                       uu____21363
                                      in
                                   (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                     uu____21361)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____21355
                               else ());
                              FStar_Syntax_Syntax.Assumption
                              ::
                              FStar_Syntax_Syntax.New
                              ::
                              quals1)
                            in
                         let t =
                           match typars with
                           | [] -> k
                           | uu____21376 ->
                               let uu____21377 =
                                 let uu____21384 =
                                   let uu____21385 =
                                     let uu____21400 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____21400)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____21385
                                    in
                                 FStar_Syntax_Syntax.mk uu____21384  in
                               uu____21377 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___2858_21413 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___2858_21413.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___2858_21413.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___2858_21413.FStar_Syntax_Syntax.sigattrs);
                           FStar_Syntax_Syntax.sigopts =
                             (uu___2858_21413.FStar_Syntax_Syntax.sigopts)
                         }
                     | uu____21414 -> failwith "Impossible"  in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se1  in
                   (env1, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t))::[] ->
              let uu____21429 = typars_of_binders env binders  in
              (match uu____21429 with
               | (env',typars) ->
                   let kopt1 =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____21463 =
                           FStar_Util.for_some
                             (fun uu___20_21466  ->
                                match uu___20_21466 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____21469 -> false) quals
                            in
                         if uu____21463
                         then
                           FStar_Pervasives_Native.Some
                             FStar_Syntax_Syntax.teff
                         else FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some k ->
                         let uu____21477 = desugar_term env' k  in
                         FStar_Pervasives_Native.Some uu____21477
                      in
                   let t0 = t  in
                   let quals1 =
                     let uu____21482 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___21_21488  ->
                               match uu___21_21488 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____21491 -> false))
                        in
                     if uu____21482
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_Syntax_DsEnv.qualify env id1  in
                   let se =
                     let uu____21505 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____21505
                     then
                       let uu____21511 =
                         let uu____21518 =
                           let uu____21519 = unparen t  in
                           uu____21519.FStar_Parser_AST.tm  in
                         match uu____21518 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____21540 =
                               match FStar_List.rev args with
                               | (last_arg,uu____21570)::args_rev ->
                                   let uu____21582 =
                                     let uu____21583 = unparen last_arg  in
                                     uu____21583.FStar_Parser_AST.tm  in
                                   (match uu____21582 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____21611 -> ([], args))
                               | uu____21620 -> ([], args)  in
                             (match uu____21540 with
                              | (cattributes,args1) ->
                                  let uu____21659 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____21659))
                         | uu____21670 -> (t, [])  in
                       match uu____21511 with
                       | (t1,cattributes) ->
                           let c =
                             desugar_comp t1.FStar_Parser_AST.range false
                               env' t1
                              in
                           let typars1 =
                             FStar_Syntax_Subst.close_binders typars  in
                           let c1 = FStar_Syntax_Subst.close_comp typars1 c
                              in
                           let quals2 =
                             FStar_All.pipe_right quals1
                               (FStar_List.filter
                                  (fun uu___22_21693  ->
                                     match uu___22_21693 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____21696 -> true))
                              in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (FStar_Syntax_Syntax.Sig_effect_abbrev
                                  (qlid, [], typars1, c1,
                                    (FStar_List.append cattributes
                                       (FStar_Syntax_Util.comp_flags c1))));
                             FStar_Syntax_Syntax.sigrng = rng;
                             FStar_Syntax_Syntax.sigquals = quals2;
                             FStar_Syntax_Syntax.sigmeta =
                               FStar_Syntax_Syntax.default_sigmeta;
                             FStar_Syntax_Syntax.sigattrs = [];
                             FStar_Syntax_Syntax.sigopts =
                               FStar_Pervasives_Native.None
                           }
                     else
                       (let t1 = desugar_typ env' t  in
                        mk_typ_abbrev env d qlid [] typars kopt1 t1 [qlid]
                          quals1 rng)
                      in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se  in
                   (env1, [se]))
          | (FStar_Parser_AST.TyconRecord uu____21704)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____21724 = tycon_record_as_variant trec  in
              (match uu____21724 with
               | (t,fs) ->
                   let uu____21741 =
                     let uu____21744 =
                       let uu____21745 =
                         let uu____21754 =
                           let uu____21757 =
                             FStar_Syntax_DsEnv.current_module env  in
                           FStar_Ident.ids_of_lid uu____21757  in
                         (uu____21754, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____21745  in
                     uu____21744 :: quals  in
                   desugar_tycon env d uu____21741 [t])
          | uu____21762::uu____21763 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____21921 = et  in
                match uu____21921 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____22131 ->
                         let trec = tc  in
                         let uu____22151 = tycon_record_as_variant trec  in
                         (match uu____22151 with
                          | (t,fs) ->
                              let uu____22207 =
                                let uu____22210 =
                                  let uu____22211 =
                                    let uu____22220 =
                                      let uu____22223 =
                                        FStar_Syntax_DsEnv.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____22223  in
                                    (uu____22220, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____22211
                                   in
                                uu____22210 :: quals1  in
                              collect_tcs uu____22207 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id1,binders,kopt,constructors) ->
                         let uu____22301 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____22301 with
                          | (env2,uu____22358,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t) ->
                         let uu____22495 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____22495 with
                          | (env2,uu____22552,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____22668 ->
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                             "Mutually defined type contains a non-inductive element")
                           rng)
                 in
              let uu____22714 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____22714 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___24_23166  ->
                             match uu___24_23166 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id1,uvs,tpars,k,uu____23220,uu____23221);
                                    FStar_Syntax_Syntax.sigrng = uu____23222;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____23223;
                                    FStar_Syntax_Syntax.sigmeta = uu____23224;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____23225;
                                    FStar_Syntax_Syntax.sigopts = uu____23226;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____23288 =
                                     typars_of_binders env1 binders  in
                                   match uu____23288 with
                                   | (env2,tpars1) ->
                                       let uu____23315 =
                                         push_tparams env2 tpars1  in
                                       (match uu____23315 with
                                        | (env_tps,tpars2) ->
                                            let t1 = desugar_typ env_tps t
                                               in
                                            let tpars3 =
                                              FStar_Syntax_Subst.close_binders
                                                tpars2
                                               in
                                            FStar_Syntax_Subst.close tpars3
                                              t1)
                                    in
                                 let uu____23344 =
                                   let uu____23355 =
                                     mk_typ_abbrev env1 d id1 uvs tpars
                                       (FStar_Pervasives_Native.Some k) t1
                                       [id1] quals1 rng
                                      in
                                   ([], uu____23355)  in
                                 [uu____23344]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs1,tpars,k,mutuals1,uu____23391);
                                    FStar_Syntax_Syntax.sigrng = uu____23392;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____23394;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____23395;
                                    FStar_Syntax_Syntax.sigopts = uu____23396;_},constrs,tconstr,quals1)
                                 ->
                                 let mk_tot t =
                                   let tot1 =
                                     FStar_Parser_AST.mk_term
                                       (FStar_Parser_AST.Name
                                          FStar_Parser_Const.effect_Tot_lid)
                                       t.FStar_Parser_AST.range
                                       t.FStar_Parser_AST.level
                                      in
                                   FStar_Parser_AST.mk_term
                                     (FStar_Parser_AST.App
                                        (tot1, t, FStar_Parser_AST.Nothing))
                                     t.FStar_Parser_AST.range
                                     t.FStar_Parser_AST.level
                                    in
                                 let tycon = (tname, tpars, k)  in
                                 let uu____23487 = push_tparams env1 tpars
                                    in
                                 (match uu____23487 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____23546  ->
                                             match uu____23546 with
                                             | (x,uu____23558) ->
                                                 (x,
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps
                                         in
                                      let tot_tconstr = mk_tot tconstr  in
                                      let attrs =
                                        FStar_List.map (desugar_term env1)
                                          d.FStar_Parser_AST.attrs
                                         in
                                      let val_attrs =
                                        let uu____23569 =
                                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                                            env1 tname
                                           in
                                        FStar_All.pipe_right uu____23569
                                          FStar_Pervasives_Native.snd
                                         in
                                      let uu____23592 =
                                        let uu____23611 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____23688  ->
                                                  match uu____23688 with
                                                  | (id1,topt,of_notation) ->
                                                      let t =
                                                        if of_notation
                                                        then
                                                          match topt with
                                                          | FStar_Pervasives_Native.Some
                                                              t ->
                                                              FStar_Parser_AST.mk_term
                                                                (FStar_Parser_AST.Product
                                                                   ([
                                                                    FStar_Parser_AST.mk_binder
                                                                    (FStar_Parser_AST.NoName
                                                                    t)
                                                                    t.FStar_Parser_AST.range
                                                                    t.FStar_Parser_AST.level
                                                                    FStar_Pervasives_Native.None],
                                                                    tot_tconstr))
                                                                t.FStar_Parser_AST.range
                                                                t.FStar_Parser_AST.level
                                                          | FStar_Pervasives_Native.None
                                                               -> tconstr
                                                        else
                                                          (match topt with
                                                           | FStar_Pervasives_Native.None
                                                                ->
                                                               failwith
                                                                 "Impossible"
                                                           | FStar_Pervasives_Native.Some
                                                               t -> t)
                                                         in
                                                      let t1 =
                                                        let uu____23731 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____23731
                                                         in
                                                      let name =
                                                        FStar_Syntax_DsEnv.qualify
                                                          env1 id1
                                                         in
                                                      let quals2 =
                                                        FStar_All.pipe_right
                                                          tname_quals
                                                          (FStar_List.collect
                                                             (fun
                                                                uu___23_23742
                                                                 ->
                                                                match uu___23_23742
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____23754
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____23762 =
                                                        let uu____23773 =
                                                          let uu____23774 =
                                                            let uu____23775 =
                                                              let uu____23791
                                                                =
                                                                let uu____23792
                                                                  =
                                                                  let uu____23795
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____23795
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____23792
                                                                 in
                                                              (name, univs1,
                                                                uu____23791,
                                                                tname, ntps,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____23775
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____23774;
                                                            FStar_Syntax_Syntax.sigrng
                                                              = rng;
                                                            FStar_Syntax_Syntax.sigquals
                                                              = quals2;
                                                            FStar_Syntax_Syntax.sigmeta
                                                              =
                                                              FStar_Syntax_Syntax.default_sigmeta;
                                                            FStar_Syntax_Syntax.sigattrs
                                                              =
                                                              (FStar_List.append
                                                                 val_attrs
                                                                 attrs);
                                                            FStar_Syntax_Syntax.sigopts
                                                              =
                                                              FStar_Pervasives_Native.None
                                                          }  in
                                                        (tps, uu____23773)
                                                         in
                                                      (name, uu____23762)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____23611
                                         in
                                      (match uu____23592 with
                                       | (constrNames,constrs1) ->
                                           ([],
                                             {
                                               FStar_Syntax_Syntax.sigel =
                                                 (FStar_Syntax_Syntax.Sig_inductive_typ
                                                    (tname, univs1, tpars, k,
                                                      mutuals1, constrNames));
                                               FStar_Syntax_Syntax.sigrng =
                                                 rng;
                                               FStar_Syntax_Syntax.sigquals =
                                                 tname_quals;
                                               FStar_Syntax_Syntax.sigmeta =
                                                 FStar_Syntax_Syntax.default_sigmeta;
                                               FStar_Syntax_Syntax.sigattrs =
                                                 (FStar_List.append val_attrs
                                                    attrs);
                                               FStar_Syntax_Syntax.sigopts =
                                                 FStar_Pervasives_Native.None
                                             })
                                           :: constrs1))
                             | uu____23927 -> failwith "impossible"))
                      in
                   let sigelts =
                     FStar_All.pipe_right tps_sigelts
                       (FStar_List.map
                          (fun uu____24008  ->
                             match uu____24008 with | (uu____24019,se) -> se))
                      in
                   let uu____24033 =
                     let uu____24040 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____24040 rng
                      in
                   (match uu____24033 with
                    | (bundle,abbrevs) ->
                        let env2 = FStar_Syntax_DsEnv.push_sigelt env0 bundle
                           in
                        let env3 =
                          FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt
                            env2 abbrevs
                           in
                        let data_ops =
                          FStar_All.pipe_right tps_sigelts
                            (FStar_List.collect
                               (fun uu____24085  ->
                                  match uu____24085 with
                                  | (tps,se) ->
                                      mk_data_projector_names quals env3 se))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____24133,tps,k,uu____24136,constrs)
                                      ->
                                      let quals1 =
                                        se.FStar_Syntax_Syntax.sigquals  in
                                      let quals2 =
                                        if
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract
                                             quals1)
                                            &&
                                            (Prims.op_Negation
                                               (FStar_List.contains
                                                  FStar_Syntax_Syntax.Private
                                                  quals1))
                                        then FStar_Syntax_Syntax.Private ::
                                          quals1
                                        else quals1  in
                                      let uu____24157 =
                                        FStar_All.pipe_right constrs
                                          (FStar_List.filter
                                             (fun data_lid  ->
                                                let data_quals =
                                                  let data_se =
                                                    let uu____24172 =
                                                      FStar_All.pipe_right
                                                        sigelts
                                                        (FStar_List.find
                                                           (fun se1  ->
                                                              match se1.FStar_Syntax_Syntax.sigel
                                                              with
                                                              | FStar_Syntax_Syntax.Sig_datacon
                                                                  (name,uu____24189,uu____24190,uu____24191,uu____24192,uu____24193)
                                                                  ->
                                                                  FStar_Ident.lid_equals
                                                                    name
                                                                    data_lid
                                                              | uu____24200
                                                                  -> false))
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____24172
                                                      FStar_Util.must
                                                     in
                                                  data_se.FStar_Syntax_Syntax.sigquals
                                                   in
                                                let uu____24204 =
                                                  FStar_All.pipe_right
                                                    data_quals
                                                    (FStar_List.existsb
                                                       (fun uu___25_24211  ->
                                                          match uu___25_24211
                                                          with
                                                          | FStar_Syntax_Syntax.RecordConstructor
                                                              uu____24213 ->
                                                              true
                                                          | uu____24223 ->
                                                              false))
                                                   in
                                                Prims.op_Negation uu____24204))
                                         in
                                      mk_data_discriminators quals2 env3
                                        uu____24157
                                  | uu____24225 -> []))
                           in
                        let ops = FStar_List.append discs data_ops  in
                        let env4 =
                          FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt
                            env3 ops
                           in
                        (env4,
                          (FStar_List.append [bundle]
                             (FStar_List.append abbrevs ops)))))
          | [] -> failwith "impossible"
  
let (desugar_binders :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_Syntax_DsEnv.env * (FStar_Syntax_Syntax.bv *
        FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
        Prims.list))
  =
  fun env  ->
    fun binders  ->
      let uu____24262 =
        FStar_List.fold_left
          (fun uu____24297  ->
             fun b  ->
               match uu____24297 with
               | (env1,binders1) ->
                   let uu____24341 = desugar_binder env1 b  in
                   (match uu____24341 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____24364 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k)
                           in
                        (match uu____24364 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____24417 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders
         in
      match uu____24262 with
      | (env1,binders1) -> (env1, (FStar_List.rev binders1))
  
let (push_reflect_effect :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Ident.lid -> FStar_Range.range -> FStar_Syntax_DsEnv.env)
  =
  fun env  ->
    fun quals  ->
      fun effect_name  ->
        fun range  ->
          let uu____24521 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___26_24528  ->
                    match uu___26_24528 with
                    | FStar_Syntax_Syntax.Reflectable uu____24530 -> true
                    | uu____24532 -> false))
             in
          if uu____24521
          then
            let monad_env =
              let uu____24536 = FStar_Ident.ident_of_lid effect_name  in
              FStar_Syntax_DsEnv.enter_monad_scope env uu____24536  in
            let reflect_lid =
              let uu____24538 = FStar_Ident.id_of_text "reflect"  in
              FStar_All.pipe_right uu____24538
                (FStar_Syntax_DsEnv.qualify monad_env)
               in
            let quals1 =
              [FStar_Syntax_Syntax.Assumption;
              FStar_Syntax_Syntax.Reflectable effect_name]  in
            let refl_decl =
              {
                FStar_Syntax_Syntax.sigel =
                  (FStar_Syntax_Syntax.Sig_declare_typ
                     (reflect_lid, [], FStar_Syntax_Syntax.tun));
                FStar_Syntax_Syntax.sigrng = range;
                FStar_Syntax_Syntax.sigquals = quals1;
                FStar_Syntax_Syntax.sigmeta =
                  FStar_Syntax_Syntax.default_sigmeta;
                FStar_Syntax_Syntax.sigattrs = [];
                FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
              }  in
            FStar_Syntax_DsEnv.push_sigelt env refl_decl
          else env
  
let (parse_attr_with_list :
  Prims.bool ->
    FStar_Syntax_Syntax.term ->
      FStar_Ident.lident ->
        (Prims.int Prims.list FStar_Pervasives_Native.option * Prims.bool))
  =
  fun warn  ->
    fun at  ->
      fun head1  ->
        let warn1 uu____24589 =
          if warn
          then
            let uu____24591 =
              let uu____24597 =
                let uu____24599 = FStar_Ident.string_of_lid head1  in
                FStar_Util.format1
                  "Found ill-applied '%s', argument should be a non-empty list of integer literals"
                  uu____24599
                 in
              (FStar_Errors.Warning_UnappliedFail, uu____24597)  in
            FStar_Errors.log_issue at.FStar_Syntax_Syntax.pos uu____24591
          else ()  in
        let uu____24605 = FStar_Syntax_Util.head_and_args at  in
        match uu____24605 with
        | (hd1,args) ->
            let uu____24658 =
              let uu____24659 = FStar_Syntax_Subst.compress hd1  in
              uu____24659.FStar_Syntax_Syntax.n  in
            (match uu____24658 with
             | FStar_Syntax_Syntax.Tm_fvar fv when
                 FStar_Syntax_Syntax.fv_eq_lid fv head1 ->
                 (match args with
                  | [] -> ((FStar_Pervasives_Native.Some []), true)
                  | (a1,uu____24703)::[] ->
                      let uu____24728 =
                        let uu____24733 =
                          let uu____24742 =
                            FStar_Syntax_Embeddings.e_list
                              FStar_Syntax_Embeddings.e_int
                             in
                          FStar_Syntax_Embeddings.unembed uu____24742 a1  in
                        uu____24733 true FStar_Syntax_Embeddings.id_norm_cb
                         in
                      (match uu____24728 with
                       | FStar_Pervasives_Native.Some es ->
                           let uu____24765 =
                             let uu____24771 =
                               FStar_List.map FStar_BigInt.to_int_fs es  in
                             FStar_Pervasives_Native.Some uu____24771  in
                           (uu____24765, true)
                       | uu____24786 ->
                           (warn1 (); (FStar_Pervasives_Native.None, true)))
                  | uu____24802 ->
                      (warn1 (); (FStar_Pervasives_Native.None, true)))
             | uu____24824 -> (FStar_Pervasives_Native.None, false))
  
let (get_fail_attr1 :
  Prims.bool ->
    FStar_Syntax_Syntax.term ->
      (Prims.int Prims.list * Prims.bool) FStar_Pervasives_Native.option)
  =
  fun warn  ->
    fun at  ->
      let rebind res b =
        match res with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some l ->
            FStar_Pervasives_Native.Some (l, b)
         in
      let uu____24941 =
        parse_attr_with_list warn at FStar_Parser_Const.fail_attr  in
      match uu____24941 with
      | (res,matched) ->
          if matched
          then rebind res false
          else
            (let uu____24990 =
               parse_attr_with_list warn at FStar_Parser_Const.fail_lax_attr
                in
             match uu____24990 with | (res1,uu____25012) -> rebind res1 true)
  
let (get_fail_attr :
  Prims.bool ->
    FStar_Syntax_Syntax.term Prims.list ->
      (Prims.int Prims.list * Prims.bool) FStar_Pervasives_Native.option)
  =
  fun warn  ->
    fun ats  ->
      let comb f1 f2 =
        match (f1, f2) with
        | (FStar_Pervasives_Native.Some (e1,l1),FStar_Pervasives_Native.Some
           (e2,l2)) ->
            FStar_Pervasives_Native.Some
              ((FStar_List.append e1 e2), (l1 || l2))
        | (FStar_Pervasives_Native.Some (e,l),FStar_Pervasives_Native.None )
            -> FStar_Pervasives_Native.Some (e, l)
        | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some (e,l))
            -> FStar_Pervasives_Native.Some (e, l)
        | uu____25339 -> FStar_Pervasives_Native.None  in
      FStar_List.fold_right
        (fun at  ->
           fun acc  ->
             let uu____25397 = get_fail_attr1 warn at  in
             comb uu____25397 acc) ats FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  FStar_Syntax_DsEnv.env ->
    FStar_Ident.lident -> FStar_Range.range -> FStar_Syntax_Syntax.eff_decl)
  =
  fun env  ->
    fun l  ->
      fun r  ->
        let uu____25432 = FStar_Syntax_DsEnv.try_lookup_effect_defn env l  in
        match uu____25432 with
        | FStar_Pervasives_Native.None  ->
            let uu____25435 =
              let uu____25441 =
                let uu____25443 =
                  let uu____25445 = FStar_Syntax_Print.lid_to_string l  in
                  Prims.op_Hat uu____25445 " not found"  in
                Prims.op_Hat "Effect name " uu____25443  in
              (FStar_Errors.Fatal_EffectNotFound, uu____25441)  in
            FStar_Errors.raise_error uu____25435 r
        | FStar_Pervasives_Native.Some l1 -> l1
  
let rec (desugar_effect :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.decl ->
      FStar_Parser_AST.qualifiers ->
        Prims.bool ->
          FStar_Ident.ident ->
            FStar_Parser_AST.binder Prims.list ->
              FStar_Parser_AST.term ->
                FStar_Parser_AST.decl Prims.list ->
                  FStar_Parser_AST.term Prims.list ->
                    (FStar_Syntax_DsEnv.env * FStar_Syntax_Syntax.sigelt
                      Prims.list))
  =
  fun env  ->
    fun d  ->
      fun quals  ->
        fun is_layered1  ->
          fun eff_name  ->
            fun eff_binders  ->
              fun eff_typ  ->
                fun eff_decls  ->
                  fun attrs  ->
                    let env0 = env  in
                    let monad_env =
                      FStar_Syntax_DsEnv.enter_monad_scope env eff_name  in
                    let uu____25601 = desugar_binders monad_env eff_binders
                       in
                    match uu____25601 with
                    | (env1,binders) ->
                        let eff_t = desugar_term env1 eff_typ  in
                        let num_indices =
                          let uu____25640 =
                            let uu____25649 =
                              FStar_Syntax_Util.arrow_formals eff_t  in
                            FStar_Pervasives_Native.fst uu____25649  in
                          FStar_List.length uu____25640  in
                        (if is_layered1 && (num_indices <= Prims.int_one)
                         then
                           (let uu____25667 =
                              let uu____25673 =
                                let uu____25675 =
                                  let uu____25677 =
                                    FStar_Ident.text_of_id eff_name  in
                                  Prims.op_Hat uu____25677
                                    "is defined as a layered effect but has no indices"
                                   in
                                Prims.op_Hat "Effect " uu____25675  in
                              (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                uu____25673)
                               in
                            FStar_Errors.raise_error uu____25667
                              d.FStar_Parser_AST.drange)
                         else ();
                         (let for_free = num_indices = Prims.int_one  in
                          let mandatory_members =
                            let rr_members = ["repr"; "return"; "bind"]  in
                            if for_free
                            then rr_members
                            else
                              if is_layered1
                              then
                                FStar_List.append rr_members
                                  ["subcomp"; "if_then_else"]
                              else
                                FStar_List.append rr_members
                                  ["return_wp";
                                  "bind_wp";
                                  "if_then_else";
                                  "ite_wp";
                                  "stronger";
                                  "close_wp";
                                  "trivial"]
                             in
                          let name_of_eff_decl decl =
                            match decl.FStar_Parser_AST.d with
                            | FStar_Parser_AST.Tycon
                                (uu____25745,uu____25746,(FStar_Parser_AST.TyconAbbrev
                                 (name,uu____25748,uu____25749,uu____25750))::[])
                                -> FStar_Ident.text_of_id name
                            | uu____25765 ->
                                failwith
                                  "Malformed effect member declaration."
                             in
                          let uu____25768 =
                            FStar_List.partition
                              (fun decl  ->
                                 let uu____25780 = name_of_eff_decl decl  in
                                 FStar_List.mem uu____25780 mandatory_members)
                              eff_decls
                             in
                          match uu____25768 with
                          | (mandatory_members_decls,actions) ->
                              let uu____25799 =
                                FStar_All.pipe_right mandatory_members_decls
                                  (FStar_List.fold_left
                                     (fun uu____25828  ->
                                        fun decl  ->
                                          match uu____25828 with
                                          | (env2,out) ->
                                              let uu____25848 =
                                                desugar_decl env2 decl  in
                                              (match uu____25848 with
                                               | (env3,ses) ->
                                                   let uu____25861 =
                                                     let uu____25864 =
                                                       FStar_List.hd ses  in
                                                     uu____25864 :: out  in
                                                   (env3, uu____25861)))
                                     (env1, []))
                                 in
                              (match uu____25799 with
                               | (env2,decls) ->
                                   let binders1 =
                                     FStar_Syntax_Subst.close_binders binders
                                      in
                                   let actions1 =
                                     FStar_All.pipe_right actions
                                       (FStar_List.map
                                          (fun d1  ->
                                             match d1.FStar_Parser_AST.d with
                                             | FStar_Parser_AST.Tycon
                                                 (uu____25910,uu____25911,(FStar_Parser_AST.TyconAbbrev
                                                  (name,action_params,uu____25914,
                                                   {
                                                     FStar_Parser_AST.tm =
                                                       FStar_Parser_AST.Construct
                                                       (uu____25915,(def,uu____25917)::
                                                        (cps_type,uu____25919)::[]);
                                                     FStar_Parser_AST.range =
                                                       uu____25920;
                                                     FStar_Parser_AST.level =
                                                       uu____25921;_}))::[])
                                                 when
                                                 Prims.op_Negation for_free
                                                 ->
                                                 let uu____25954 =
                                                   desugar_binders env2
                                                     action_params
                                                    in
                                                 (match uu____25954 with
                                                  | (env3,action_params1) ->
                                                      let action_params2 =
                                                        FStar_Syntax_Subst.close_binders
                                                          action_params1
                                                         in
                                                      let uu____25986 =
                                                        FStar_Syntax_DsEnv.qualify
                                                          env3 name
                                                         in
                                                      let uu____25987 =
                                                        let uu____25988 =
                                                          desugar_term env3
                                                            def
                                                           in
                                                        FStar_Syntax_Subst.close
                                                          (FStar_List.append
                                                             binders1
                                                             action_params2)
                                                          uu____25988
                                                         in
                                                      let uu____25995 =
                                                        let uu____25996 =
                                                          desugar_typ env3
                                                            cps_type
                                                           in
                                                        FStar_Syntax_Subst.close
                                                          (FStar_List.append
                                                             binders1
                                                             action_params2)
                                                          uu____25996
                                                         in
                                                      {
                                                        FStar_Syntax_Syntax.action_name
                                                          = uu____25986;
                                                        FStar_Syntax_Syntax.action_unqualified_name
                                                          = name;
                                                        FStar_Syntax_Syntax.action_univs
                                                          = [];
                                                        FStar_Syntax_Syntax.action_params
                                                          = action_params2;
                                                        FStar_Syntax_Syntax.action_defn
                                                          = uu____25987;
                                                        FStar_Syntax_Syntax.action_typ
                                                          = uu____25995
                                                      })
                                             | FStar_Parser_AST.Tycon
                                                 (uu____26003,uu____26004,(FStar_Parser_AST.TyconAbbrev
                                                  (name,action_params,uu____26007,defn))::[])
                                                 when for_free || is_layered1
                                                 ->
                                                 let uu____26023 =
                                                   desugar_binders env2
                                                     action_params
                                                    in
                                                 (match uu____26023 with
                                                  | (env3,action_params1) ->
                                                      let action_params2 =
                                                        FStar_Syntax_Subst.close_binders
                                                          action_params1
                                                         in
                                                      let uu____26055 =
                                                        FStar_Syntax_DsEnv.qualify
                                                          env3 name
                                                         in
                                                      let uu____26056 =
                                                        let uu____26057 =
                                                          desugar_term env3
                                                            defn
                                                           in
                                                        FStar_Syntax_Subst.close
                                                          (FStar_List.append
                                                             binders1
                                                             action_params2)
                                                          uu____26057
                                                         in
                                                      {
                                                        FStar_Syntax_Syntax.action_name
                                                          = uu____26055;
                                                        FStar_Syntax_Syntax.action_unqualified_name
                                                          = name;
                                                        FStar_Syntax_Syntax.action_univs
                                                          = [];
                                                        FStar_Syntax_Syntax.action_params
                                                          = action_params2;
                                                        FStar_Syntax_Syntax.action_defn
                                                          = uu____26056;
                                                        FStar_Syntax_Syntax.action_typ
                                                          =
                                                          FStar_Syntax_Syntax.tun
                                                      })
                                             | uu____26064 ->
                                                 FStar_Errors.raise_error
                                                   (FStar_Errors.Fatal_MalformedActionDeclaration,
                                                     "Malformed action declaration; if this is an \"effect for free\", just provide the direct-style declaration. If this is not an \"effect for free\", please provide a pair of the definition and its cps-type with arrows inserted in the right place (see examples).")
                                                   d1.FStar_Parser_AST.drange))
                                      in
                                   let eff_t1 =
                                     FStar_Syntax_Subst.close binders1 eff_t
                                      in
                                   let lookup1 s =
                                     let l =
                                       let uu____26083 =
                                         FStar_Ident.mk_ident
                                           (s, (d.FStar_Parser_AST.drange))
                                          in
                                       FStar_Syntax_DsEnv.qualify env2
                                         uu____26083
                                        in
                                     let uu____26085 =
                                       let uu____26086 =
                                         FStar_Syntax_DsEnv.fail_or env2
                                           (FStar_Syntax_DsEnv.try_lookup_definition
                                              env2) l
                                          in
                                       FStar_All.pipe_left
                                         (FStar_Syntax_Subst.close binders1)
                                         uu____26086
                                        in
                                     ([], uu____26085)  in
                                   let mname =
                                     FStar_Syntax_DsEnv.qualify env0 eff_name
                                      in
                                   let qualifiers =
                                     FStar_List.map
                                       (trans_qual d.FStar_Parser_AST.drange
                                          (FStar_Pervasives_Native.Some mname))
                                       quals
                                      in
                                   let dummy_tscheme =
                                     ([], FStar_Syntax_Syntax.tun)  in
                                   let combinators =
                                     if for_free
                                     then
                                       let uu____26108 =
                                         let uu____26109 =
                                           let uu____26112 = lookup1 "repr"
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____26112
                                            in
                                         let uu____26114 =
                                           let uu____26117 = lookup1 "return"
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____26117
                                            in
                                         let uu____26119 =
                                           let uu____26122 = lookup1 "bind"
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____26122
                                            in
                                         {
                                           FStar_Syntax_Syntax.ret_wp =
                                             dummy_tscheme;
                                           FStar_Syntax_Syntax.bind_wp =
                                             dummy_tscheme;
                                           FStar_Syntax_Syntax.stronger =
                                             dummy_tscheme;
                                           FStar_Syntax_Syntax.if_then_else =
                                             dummy_tscheme;
                                           FStar_Syntax_Syntax.ite_wp =
                                             dummy_tscheme;
                                           FStar_Syntax_Syntax.close_wp =
                                             dummy_tscheme;
                                           FStar_Syntax_Syntax.trivial =
                                             dummy_tscheme;
                                           FStar_Syntax_Syntax.repr =
                                             uu____26109;
                                           FStar_Syntax_Syntax.return_repr =
                                             uu____26114;
                                           FStar_Syntax_Syntax.bind_repr =
                                             uu____26119
                                         }  in
                                       FStar_Syntax_Syntax.DM4F_eff
                                         uu____26108
                                     else
                                       if is_layered1
                                       then
                                         (let to_comb uu____26156 =
                                            match uu____26156 with
                                            | (us,t) ->
                                                ((us, t), dummy_tscheme)
                                             in
                                          let uu____26203 =
                                            let uu____26204 =
                                              FStar_Ident.lid_of_str ""  in
                                            let uu____26206 =
                                              let uu____26211 =
                                                lookup1 "repr"  in
                                              FStar_All.pipe_right
                                                uu____26211 to_comb
                                               in
                                            let uu____26229 =
                                              let uu____26234 =
                                                lookup1 "return"  in
                                              FStar_All.pipe_right
                                                uu____26234 to_comb
                                               in
                                            let uu____26252 =
                                              let uu____26257 =
                                                lookup1 "bind"  in
                                              FStar_All.pipe_right
                                                uu____26257 to_comb
                                               in
                                            let uu____26275 =
                                              let uu____26280 =
                                                lookup1 "subcomp"  in
                                              FStar_All.pipe_right
                                                uu____26280 to_comb
                                               in
                                            let uu____26298 =
                                              let uu____26303 =
                                                lookup1 "if_then_else"  in
                                              FStar_All.pipe_right
                                                uu____26303 to_comb
                                               in
                                            {
                                              FStar_Syntax_Syntax.l_base_effect
                                                = uu____26204;
                                              FStar_Syntax_Syntax.l_repr =
                                                uu____26206;
                                              FStar_Syntax_Syntax.l_return =
                                                uu____26229;
                                              FStar_Syntax_Syntax.l_bind =
                                                uu____26252;
                                              FStar_Syntax_Syntax.l_subcomp =
                                                uu____26275;
                                              FStar_Syntax_Syntax.l_if_then_else
                                                = uu____26298
                                            }  in
                                          FStar_Syntax_Syntax.Layered_eff
                                            uu____26203)
                                       else
                                         (let rr =
                                            FStar_Util.for_some
                                              (fun uu___27_26326  ->
                                                 match uu___27_26326 with
                                                 | FStar_Syntax_Syntax.Reifiable
                                                      -> true
                                                 | FStar_Syntax_Syntax.Reflectable
                                                     uu____26329 -> true
                                                 | uu____26331 -> false)
                                              qualifiers
                                             in
                                          let uu____26333 =
                                            let uu____26334 =
                                              lookup1 "return_wp"  in
                                            let uu____26336 =
                                              lookup1 "bind_wp"  in
                                            let uu____26338 =
                                              lookup1 "stronger"  in
                                            let uu____26340 =
                                              lookup1 "if_then_else"  in
                                            let uu____26342 =
                                              lookup1 "ite_wp"  in
                                            let uu____26344 =
                                              lookup1 "close_wp"  in
                                            let uu____26346 =
                                              lookup1 "trivial"  in
                                            let uu____26348 =
                                              if rr
                                              then
                                                let uu____26354 =
                                                  lookup1 "repr"  in
                                                FStar_Pervasives_Native.Some
                                                  uu____26354
                                              else
                                                FStar_Pervasives_Native.None
                                               in
                                            let uu____26358 =
                                              if rr
                                              then
                                                let uu____26364 =
                                                  lookup1 "return"  in
                                                FStar_Pervasives_Native.Some
                                                  uu____26364
                                              else
                                                FStar_Pervasives_Native.None
                                               in
                                            let uu____26368 =
                                              if rr
                                              then
                                                let uu____26374 =
                                                  lookup1 "bind"  in
                                                FStar_Pervasives_Native.Some
                                                  uu____26374
                                              else
                                                FStar_Pervasives_Native.None
                                               in
                                            {
                                              FStar_Syntax_Syntax.ret_wp =
                                                uu____26334;
                                              FStar_Syntax_Syntax.bind_wp =
                                                uu____26336;
                                              FStar_Syntax_Syntax.stronger =
                                                uu____26338;
                                              FStar_Syntax_Syntax.if_then_else
                                                = uu____26340;
                                              FStar_Syntax_Syntax.ite_wp =
                                                uu____26342;
                                              FStar_Syntax_Syntax.close_wp =
                                                uu____26344;
                                              FStar_Syntax_Syntax.trivial =
                                                uu____26346;
                                              FStar_Syntax_Syntax.repr =
                                                uu____26348;
                                              FStar_Syntax_Syntax.return_repr
                                                = uu____26358;
                                              FStar_Syntax_Syntax.bind_repr =
                                                uu____26368
                                            }  in
                                          FStar_Syntax_Syntax.Primitive_eff
                                            uu____26333)
                                      in
                                   let sigel =
                                     let uu____26379 =
                                       let uu____26380 =
                                         FStar_List.map (desugar_term env2)
                                           attrs
                                          in
                                       {
                                         FStar_Syntax_Syntax.mname = mname;
                                         FStar_Syntax_Syntax.cattributes = [];
                                         FStar_Syntax_Syntax.univs = [];
                                         FStar_Syntax_Syntax.binders =
                                           binders1;
                                         FStar_Syntax_Syntax.signature =
                                           ([], eff_t1);
                                         FStar_Syntax_Syntax.combinators =
                                           combinators;
                                         FStar_Syntax_Syntax.actions =
                                           actions1;
                                         FStar_Syntax_Syntax.eff_attrs =
                                           uu____26380
                                       }  in
                                     FStar_Syntax_Syntax.Sig_new_effect
                                       uu____26379
                                      in
                                   let se =
                                     {
                                       FStar_Syntax_Syntax.sigel = sigel;
                                       FStar_Syntax_Syntax.sigrng =
                                         (d.FStar_Parser_AST.drange);
                                       FStar_Syntax_Syntax.sigquals =
                                         qualifiers;
                                       FStar_Syntax_Syntax.sigmeta =
                                         FStar_Syntax_Syntax.default_sigmeta;
                                       FStar_Syntax_Syntax.sigattrs = [];
                                       FStar_Syntax_Syntax.sigopts =
                                         FStar_Pervasives_Native.None
                                     }  in
                                   let env3 =
                                     FStar_Syntax_DsEnv.push_sigelt env0 se
                                      in
                                   let env4 =
                                     FStar_All.pipe_right actions1
                                       (FStar_List.fold_left
                                          (fun env4  ->
                                             fun a  ->
                                               let uu____26397 =
                                                 FStar_Syntax_Util.action_as_lb
                                                   mname a
                                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Syntax_DsEnv.push_sigelt
                                                 env4 uu____26397) env3)
                                      in
                                   let env5 =
                                     push_reflect_effect env4 qualifiers
                                       mname d.FStar_Parser_AST.drange
                                      in
                                   (env5, [se]))))

and (desugar_redefine_effect :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.decl ->
      (FStar_Ident.lident FStar_Pervasives_Native.option ->
         FStar_Parser_AST.qualifier -> FStar_Syntax_Syntax.qualifier)
        ->
        FStar_Parser_AST.qualifier Prims.list ->
          FStar_Ident.ident ->
            FStar_Parser_AST.binder Prims.list ->
              FStar_Parser_AST.term ->
                (FStar_Syntax_DsEnv.env * FStar_Syntax_Syntax.sigelt
                  Prims.list))
  =
  fun env  ->
    fun d  ->
      fun trans_qual1  ->
        fun quals  ->
          fun eff_name  ->
            fun eff_binders  ->
              fun defn  ->
                let env0 = env  in
                let env1 = FStar_Syntax_DsEnv.enter_monad_scope env eff_name
                   in
                let uu____26420 = desugar_binders env1 eff_binders  in
                match uu____26420 with
                | (env2,binders) ->
                    let uu____26457 =
                      let uu____26468 = head_and_args defn  in
                      match uu____26468 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____26505 ->
                                let uu____26506 =
                                  let uu____26512 =
                                    let uu____26514 =
                                      let uu____26516 =
                                        FStar_Parser_AST.term_to_string head1
                                         in
                                      Prims.op_Hat uu____26516 " not found"
                                       in
                                    Prims.op_Hat "Effect " uu____26514  in
                                  (FStar_Errors.Fatal_EffectNotFound,
                                    uu____26512)
                                   in
                                FStar_Errors.raise_error uu____26506
                                  d.FStar_Parser_AST.drange
                             in
                          let ed =
                            FStar_Syntax_DsEnv.fail_or env2
                              (FStar_Syntax_DsEnv.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____26522 =
                            match FStar_List.rev args with
                            | (last_arg,uu____26552)::args_rev ->
                                let uu____26564 =
                                  let uu____26565 = unparen last_arg  in
                                  uu____26565.FStar_Parser_AST.tm  in
                                (match uu____26564 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____26593 -> ([], args))
                            | uu____26602 -> ([], args)  in
                          (match uu____26522 with
                           | (cattributes,args1) ->
                               let uu____26645 = desugar_args env2 args1  in
                               let uu____26646 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____26645, uu____26646))
                       in
                    (match uu____26457 with
                     | (ed_lid,ed,args,cattributes) ->
                         let binders1 =
                           FStar_Syntax_Subst.close_binders binders  in
                         (if
                            (FStar_List.length args) <>
                              (FStar_List.length
                                 ed.FStar_Syntax_Syntax.binders)
                          then
                            FStar_Errors.raise_error
                              (FStar_Errors.Fatal_ArgumentLengthMismatch,
                                "Unexpected number of arguments to effect constructor")
                              defn.FStar_Parser_AST.range
                          else ();
                          (let uu____26686 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit
                              in
                           match uu____26686 with
                           | (ed_binders,uu____26700,ed_binders_opening) ->
                               let sub' shift_n uu____26719 =
                                 match uu____26719 with
                                 | (us,x) ->
                                     let x1 =
                                       let uu____26734 =
                                         FStar_Syntax_Subst.shift_subst
                                           (shift_n + (FStar_List.length us))
                                           ed_binders_opening
                                          in
                                       FStar_Syntax_Subst.subst uu____26734 x
                                        in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args
                                        in
                                     let uu____26738 =
                                       let uu____26739 =
                                         FStar_Syntax_Subst.subst s x1  in
                                       (us, uu____26739)  in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu____26738
                                  in
                               let sub1 = sub' Prims.int_zero  in
                               let mname =
                                 FStar_Syntax_DsEnv.qualify env0 eff_name  in
                               let ed1 =
                                 let uu____26760 =
                                   sub1 ed.FStar_Syntax_Syntax.signature  in
                                 let uu____26761 =
                                   FStar_Syntax_Util.apply_eff_combinators
                                     sub1 ed.FStar_Syntax_Syntax.combinators
                                    in
                                 let uu____26762 =
                                   FStar_List.map
                                     (fun action  ->
                                        let nparam =
                                          FStar_List.length
                                            action.FStar_Syntax_Syntax.action_params
                                           in
                                        let uu____26778 =
                                          FStar_Syntax_DsEnv.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name
                                           in
                                        let uu____26779 =
                                          let uu____26780 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____26780
                                           in
                                        let uu____26795 =
                                          let uu____26796 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____26796
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu____26778;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____26779;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____26795
                                        }) ed.FStar_Syntax_Syntax.actions
                                    in
                                 {
                                   FStar_Syntax_Syntax.mname = mname;
                                   FStar_Syntax_Syntax.cattributes =
                                     cattributes;
                                   FStar_Syntax_Syntax.univs =
                                     (ed.FStar_Syntax_Syntax.univs);
                                   FStar_Syntax_Syntax.binders = binders1;
                                   FStar_Syntax_Syntax.signature =
                                     uu____26760;
                                   FStar_Syntax_Syntax.combinators =
                                     uu____26761;
                                   FStar_Syntax_Syntax.actions = uu____26762;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (ed.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               let se =
                                 let uu____26812 =
                                   let uu____26815 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname)
                                      in
                                   FStar_List.map uu____26815 quals  in
                                 {
                                   FStar_Syntax_Syntax.sigel =
                                     (FStar_Syntax_Syntax.Sig_new_effect ed1);
                                   FStar_Syntax_Syntax.sigrng =
                                     (d.FStar_Parser_AST.drange);
                                   FStar_Syntax_Syntax.sigquals = uu____26812;
                                   FStar_Syntax_Syntax.sigmeta =
                                     FStar_Syntax_Syntax.default_sigmeta;
                                   FStar_Syntax_Syntax.sigattrs = [];
                                   FStar_Syntax_Syntax.sigopts =
                                     FStar_Pervasives_Native.None
                                 }  in
                               let monad_env = env2  in
                               let env3 =
                                 FStar_Syntax_DsEnv.push_sigelt env0 se  in
                               let env4 =
                                 FStar_All.pipe_right
                                   ed1.FStar_Syntax_Syntax.actions
                                   (FStar_List.fold_left
                                      (fun env4  ->
                                         fun a  ->
                                           let uu____26830 =
                                             FStar_Syntax_Util.action_as_lb
                                               mname a
                                               (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                              in
                                           FStar_Syntax_DsEnv.push_sigelt
                                             env4 uu____26830) env3)
                                  in
                               let env5 =
                                 let uu____26832 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable)
                                    in
                                 if uu____26832
                                 then
                                   let reflect_lid =
                                     let uu____26839 =
                                       FStar_Ident.id_of_text "reflect"  in
                                     FStar_All.pipe_right uu____26839
                                       (FStar_Syntax_DsEnv.qualify monad_env)
                                      in
                                   let quals1 =
                                     [FStar_Syntax_Syntax.Assumption;
                                     FStar_Syntax_Syntax.Reflectable mname]
                                      in
                                   let refl_decl =
                                     {
                                       FStar_Syntax_Syntax.sigel =
                                         (FStar_Syntax_Syntax.Sig_declare_typ
                                            (reflect_lid, [],
                                              FStar_Syntax_Syntax.tun));
                                       FStar_Syntax_Syntax.sigrng =
                                         (d.FStar_Parser_AST.drange);
                                       FStar_Syntax_Syntax.sigquals = quals1;
                                       FStar_Syntax_Syntax.sigmeta =
                                         FStar_Syntax_Syntax.default_sigmeta;
                                       FStar_Syntax_Syntax.sigattrs = [];
                                       FStar_Syntax_Syntax.sigopts =
                                         FStar_Pervasives_Native.None
                                     }  in
                                   FStar_Syntax_DsEnv.push_sigelt env4
                                     refl_decl
                                 else env4  in
                               (env5, [se]))))

and (desugar_decl_aux :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts))
  =
  fun env  ->
    fun d  ->
      let no_fail_attrs ats =
        FStar_List.filter
          (fun at  ->
             let uu____26872 = get_fail_attr1 false at  in
             FStar_Option.isNone uu____26872) ats
         in
      let env0 =
        let uu____26893 = FStar_Syntax_DsEnv.snapshot env  in
        FStar_All.pipe_right uu____26893 FStar_Pervasives_Native.snd  in
      let attrs = FStar_List.map (desugar_term env) d.FStar_Parser_AST.attrs
         in
      let uu____26908 =
        let uu____26915 = get_fail_attr false attrs  in
        match uu____26915 with
        | FStar_Pervasives_Native.Some (expected_errs,lax1) ->
            let d1 =
              let uu___3413_26952 = d  in
              {
                FStar_Parser_AST.d = (uu___3413_26952.FStar_Parser_AST.d);
                FStar_Parser_AST.drange =
                  (uu___3413_26952.FStar_Parser_AST.drange);
                FStar_Parser_AST.quals =
                  (uu___3413_26952.FStar_Parser_AST.quals);
                FStar_Parser_AST.attrs = []
              }  in
            let uu____26953 =
              FStar_Errors.catch_errors
                (fun uu____26971  ->
                   FStar_Options.with_saved_options
                     (fun uu____26977  -> desugar_decl_noattrs env d1))
               in
            (match uu____26953 with
             | (errs,r) ->
                 (match (errs, r) with
                  | ([],FStar_Pervasives_Native.Some (env1,ses)) ->
                      let ses1 =
                        FStar_List.map
                          (fun se  ->
                             let uu___3428_27037 = se  in
                             let uu____27038 = no_fail_attrs attrs  in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (uu___3428_27037.FStar_Syntax_Syntax.sigel);
                               FStar_Syntax_Syntax.sigrng =
                                 (uu___3428_27037.FStar_Syntax_Syntax.sigrng);
                               FStar_Syntax_Syntax.sigquals =
                                 (uu___3428_27037.FStar_Syntax_Syntax.sigquals);
                               FStar_Syntax_Syntax.sigmeta =
                                 (uu___3428_27037.FStar_Syntax_Syntax.sigmeta);
                               FStar_Syntax_Syntax.sigattrs = uu____27038;
                               FStar_Syntax_Syntax.sigopts =
                                 (uu___3428_27037.FStar_Syntax_Syntax.sigopts)
                             }) ses
                         in
                      let se =
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_fail
                               (expected_errs, lax1, ses1));
                          FStar_Syntax_Syntax.sigrng =
                            (d1.FStar_Parser_AST.drange);
                          FStar_Syntax_Syntax.sigquals = [];
                          FStar_Syntax_Syntax.sigmeta =
                            FStar_Syntax_Syntax.default_sigmeta;
                          FStar_Syntax_Syntax.sigattrs = [];
                          FStar_Syntax_Syntax.sigopts =
                            FStar_Pervasives_Native.None
                        }  in
                      (env0, [se])
                  | (errs1,ropt) ->
                      let errnos =
                        FStar_List.concatMap
                          (fun i  ->
                             FStar_Common.list_of_option
                               i.FStar_Errors.issue_number) errs1
                         in
                      if expected_errs = []
                      then (env0, [])
                      else
                        (let uu____27091 =
                           FStar_Errors.find_multiset_discrepancy
                             expected_errs errnos
                            in
                         match uu____27091 with
                         | FStar_Pervasives_Native.None  -> (env0, [])
                         | FStar_Pervasives_Native.Some (e,n1,n2) ->
                             (FStar_List.iter FStar_Errors.print_issue errs1;
                              (let uu____27140 =
                                 let uu____27146 =
                                   let uu____27148 =
                                     FStar_Common.string_of_list
                                       FStar_Util.string_of_int expected_errs
                                      in
                                   let uu____27151 =
                                     FStar_Common.string_of_list
                                       FStar_Util.string_of_int errnos
                                      in
                                   let uu____27154 =
                                     FStar_Util.string_of_int e  in
                                   let uu____27156 =
                                     FStar_Util.string_of_int n2  in
                                   let uu____27158 =
                                     FStar_Util.string_of_int n1  in
                                   FStar_Util.format5
                                     "This top-level definition was expected to raise error codes %s, but it raised %s (at desugaring time). Error #%s was raised %s times, instead of %s."
                                     uu____27148 uu____27151 uu____27154
                                     uu____27156 uu____27158
                                    in
                                 (FStar_Errors.Error_DidNotFail, uu____27146)
                                  in
                               FStar_Errors.log_issue
                                 d1.FStar_Parser_AST.drange uu____27140);
                              (env0, [])))))
        | FStar_Pervasives_Native.None  -> desugar_decl_noattrs env d  in
      match uu____26908 with
      | (env1,sigelts) ->
          let rec val_attrs ses =
            match ses with
            | {
                FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                  uu____27196;
                FStar_Syntax_Syntax.sigrng = uu____27197;
                FStar_Syntax_Syntax.sigquals = uu____27198;
                FStar_Syntax_Syntax.sigmeta = uu____27199;
                FStar_Syntax_Syntax.sigattrs = uu____27200;
                FStar_Syntax_Syntax.sigopts = uu____27201;_}::[] ->
                let uu____27214 =
                  let uu____27217 = FStar_List.hd sigelts  in
                  FStar_Syntax_Util.lids_of_sigelt uu____27217  in
                FStar_All.pipe_right uu____27214
                  (FStar_List.collect
                     (fun nm  ->
                        let uu____27225 =
                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                            env0 nm
                           in
                        FStar_Pervasives_Native.snd uu____27225))
            | {
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_inductive_typ uu____27238;
                FStar_Syntax_Syntax.sigrng = uu____27239;
                FStar_Syntax_Syntax.sigquals = uu____27240;
                FStar_Syntax_Syntax.sigmeta = uu____27241;
                FStar_Syntax_Syntax.sigattrs = uu____27242;
                FStar_Syntax_Syntax.sigopts = uu____27243;_}::uu____27244 ->
                let uu____27269 =
                  let uu____27272 = FStar_List.hd sigelts  in
                  FStar_Syntax_Util.lids_of_sigelt uu____27272  in
                FStar_All.pipe_right uu____27269
                  (FStar_List.collect
                     (fun nm  ->
                        let uu____27280 =
                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                            env0 nm
                           in
                        FStar_Pervasives_Native.snd uu____27280))
            | {
                FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_fail
                  (_errs,_lax,ses1);
                FStar_Syntax_Syntax.sigrng = uu____27296;
                FStar_Syntax_Syntax.sigquals = uu____27297;
                FStar_Syntax_Syntax.sigmeta = uu____27298;
                FStar_Syntax_Syntax.sigattrs = uu____27299;
                FStar_Syntax_Syntax.sigopts = uu____27300;_}::[] ->
                FStar_List.collect (fun se  -> val_attrs [se]) ses1
            | uu____27321 -> []  in
          let attrs1 =
            let uu____27327 = val_attrs sigelts  in
            FStar_List.append attrs uu____27327  in
          let uu____27330 =
            FStar_List.map
              (fun sigelt  ->
                 let uu___3488_27334 = sigelt  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (uu___3488_27334.FStar_Syntax_Syntax.sigel);
                   FStar_Syntax_Syntax.sigrng =
                     (uu___3488_27334.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___3488_27334.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___3488_27334.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs = attrs1;
                   FStar_Syntax_Syntax.sigopts =
                     (uu___3488_27334.FStar_Syntax_Syntax.sigopts)
                 }) sigelts
             in
          (env1, uu____27330)

and (desugar_decl :
  env_t -> FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts)) =
  fun env  ->
    fun d  ->
      let uu____27341 = desugar_decl_aux env d  in
      match uu____27341 with
      | (env1,ses) ->
          let uu____27352 =
            FStar_All.pipe_right ses
              (FStar_List.map generalize_annotated_univs)
             in
          (env1, uu____27352)

and (desugar_decl_noattrs :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts))
  =
  fun env  ->
    fun d  ->
      let trans_qual1 = trans_qual d.FStar_Parser_AST.drange  in
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Pragma p ->
          let p1 = trans_pragma p  in
          (FStar_Syntax_Util.process_pragma p1 d.FStar_Parser_AST.drange;
           (let se =
              {
                FStar_Syntax_Syntax.sigel =
                  (FStar_Syntax_Syntax.Sig_pragma p1);
                FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
                FStar_Syntax_Syntax.sigquals = [];
                FStar_Syntax_Syntax.sigmeta =
                  FStar_Syntax_Syntax.default_sigmeta;
                FStar_Syntax_Syntax.sigattrs = [];
                FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
              }  in
            (env, [se])))
      | FStar_Parser_AST.TopLevelModule id1 -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in (env1, [])
      | FStar_Parser_AST.Friend lid ->
          let uu____27384 = FStar_Syntax_DsEnv.iface env  in
          if uu____27384
          then
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_FriendInterface,
                "'friend' declarations are not allowed in interfaces")
              d.FStar_Parser_AST.drange
          else
            (let uu____27399 =
               let uu____27401 =
                 let uu____27403 = FStar_Syntax_DsEnv.dep_graph env  in
                 let uu____27404 = FStar_Syntax_DsEnv.current_module env  in
                 FStar_Parser_Dep.module_has_interface uu____27403
                   uu____27404
                  in
               Prims.op_Negation uu____27401  in
             if uu____27399
             then
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_FriendInterface,
                   "'friend' declarations are not allowed in modules that lack interfaces")
                 d.FStar_Parser_AST.drange
             else
               (let uu____27418 =
                  let uu____27420 =
                    let uu____27422 = FStar_Syntax_DsEnv.dep_graph env  in
                    FStar_Parser_Dep.module_has_interface uu____27422 lid  in
                  Prims.op_Negation uu____27420  in
                if uu____27418
                then
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_FriendInterface,
                      "'friend' declarations cannot refer to modules that lack interfaces")
                    d.FStar_Parser_AST.drange
                else
                  (let uu____27436 =
                     let uu____27438 =
                       let uu____27440 = FStar_Syntax_DsEnv.dep_graph env  in
                       FStar_Parser_Dep.deps_has_implementation uu____27440
                         lid
                        in
                     Prims.op_Negation uu____27438  in
                   if uu____27436
                   then
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_FriendInterface,
                         "'friend' module has not been loaded; recompute dependences (C-c C-r) if in interactive mode")
                       d.FStar_Parser_AST.drange
                   else (env, []))))
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_Syntax_DsEnv.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____27458 = FStar_Syntax_DsEnv.push_module_abbrev env x l  in
          (uu____27458, [])
      | FStar_Parser_AST.Tycon (is_effect,typeclass,tcs) ->
          let quals = d.FStar_Parser_AST.quals  in
          let quals1 =
            if is_effect
            then FStar_Parser_AST.Effect_qual :: quals
            else quals  in
          let quals2 =
            if typeclass
            then
              match tcs with
              | (FStar_Parser_AST.TyconRecord uu____27487)::[] ->
                  FStar_Parser_AST.Noeq :: quals1
              | uu____27506 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Error_BadClassDecl,
                      "Ill-formed `class` declaration: definition must be a record type")
                    d.FStar_Parser_AST.drange
            else quals1  in
          let uu____27515 =
            let uu____27520 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals2
               in
            desugar_tycon env d uu____27520 tcs  in
          (match uu____27515 with
           | (env1,ses) ->
               let mkclass lid =
                 let uu____27537 =
                   let uu____27538 =
                     let uu____27545 =
                       FStar_Syntax_Syntax.new_bv
                         FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun
                        in
                     FStar_Syntax_Syntax.mk_binder uu____27545  in
                   [uu____27538]  in
                 let uu____27558 =
                   let uu____27561 =
                     FStar_Syntax_Syntax.tabbrev
                       FStar_Parser_Const.mk_class_lid
                      in
                   let uu____27564 =
                     let uu____27575 =
                       let uu____27584 =
                         let uu____27585 = FStar_Ident.string_of_lid lid  in
                         FStar_Syntax_Util.exp_string uu____27585  in
                       FStar_Syntax_Syntax.as_arg uu____27584  in
                     [uu____27575]  in
                   FStar_Syntax_Util.mk_app uu____27561 uu____27564  in
                 FStar_Syntax_Util.abs uu____27537 uu____27558
                   FStar_Pervasives_Native.None
                  in
               let get_meths se =
                 let rec get_fname quals3 =
                   match quals3 with
                   | (FStar_Syntax_Syntax.Projector
                       (uu____27625,id1))::uu____27627 ->
                       FStar_Pervasives_Native.Some id1
                   | uu____27630::quals4 -> get_fname quals4
                   | [] -> FStar_Pervasives_Native.None  in
                 let uu____27634 = get_fname se.FStar_Syntax_Syntax.sigquals
                    in
                 match uu____27634 with
                 | FStar_Pervasives_Native.None  -> []
                 | FStar_Pervasives_Native.Some id1 ->
                     let uu____27640 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     [uu____27640]
                  in
               let rec splice_decl meths se =
                 match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_bundle (ses1,uu____27661) ->
                     FStar_List.concatMap (splice_decl meths) ses1
                 | FStar_Syntax_Syntax.Sig_inductive_typ
                     (lid,uu____27671,uu____27672,uu____27673,uu____27674,uu____27675)
                     ->
                     let uu____27684 =
                       let uu____27685 =
                         let uu____27686 =
                           let uu____27693 = mkclass lid  in
                           (meths, uu____27693)  in
                         FStar_Syntax_Syntax.Sig_splice uu____27686  in
                       {
                         FStar_Syntax_Syntax.sigel = uu____27685;
                         FStar_Syntax_Syntax.sigrng =
                           (d.FStar_Parser_AST.drange);
                         FStar_Syntax_Syntax.sigquals = [];
                         FStar_Syntax_Syntax.sigmeta =
                           FStar_Syntax_Syntax.default_sigmeta;
                         FStar_Syntax_Syntax.sigattrs = [];
                         FStar_Syntax_Syntax.sigopts =
                           FStar_Pervasives_Native.None
                       }  in
                     [uu____27684]
                 | uu____27696 -> []  in
               let extra =
                 if typeclass
                 then
                   let meths = FStar_List.concatMap get_meths ses  in
                   FStar_List.concatMap (splice_decl meths) ses
                 else []  in
               let env2 =
                 FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt env1
                   extra
                  in
               (env2, (FStar_List.append ses extra)))
      | FStar_Parser_AST.TopLevelLet (isrec,lets) ->
          let quals = d.FStar_Parser_AST.quals  in
          let expand_toplevel_pattern =
            (isrec = FStar_Parser_AST.NoLetQualifier) &&
              (match lets with
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____27730;
                    FStar_Parser_AST.prange = uu____27731;_},uu____27732)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____27742;
                    FStar_Parser_AST.prange = uu____27743;_},uu____27744)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatOp
                           uu____27760;
                         FStar_Parser_AST.prange = uu____27761;_},uu____27762);
                    FStar_Parser_AST.prange = uu____27763;_},uu____27764)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____27786;
                         FStar_Parser_AST.prange = uu____27787;_},uu____27788);
                    FStar_Parser_AST.prange = uu____27789;_},uu____27790)::[]
                   -> false
               | (p,uu____27819)::[] ->
                   let uu____27828 = is_app_pattern p  in
                   Prims.op_Negation uu____27828
               | uu____27830 -> false)
             in
          if Prims.op_Negation expand_toplevel_pattern
          then
            let lets1 =
              FStar_List.map (fun x  -> (FStar_Pervasives_Native.None, x))
                lets
               in
            let as_inner_let =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.Let
                   (isrec, lets1,
                     (FStar_Parser_AST.mk_term
                        (FStar_Parser_AST.Const FStar_Const.Const_unit)
                        d.FStar_Parser_AST.drange FStar_Parser_AST.Expr)))
                d.FStar_Parser_AST.drange FStar_Parser_AST.Expr
               in
            let uu____27905 = desugar_term_maybe_top true env as_inner_let
               in
            (match uu____27905 with
             | (ds_lets,aq) ->
                 (check_no_aq aq;
                  (let uu____27918 =
                     let uu____27919 =
                       FStar_All.pipe_left FStar_Syntax_Subst.compress
                         ds_lets
                        in
                     uu____27919.FStar_Syntax_Syntax.n  in
                   match uu____27918 with
                   | FStar_Syntax_Syntax.Tm_let (lbs,uu____27929) ->
                       let fvs =
                         FStar_All.pipe_right
                           (FStar_Pervasives_Native.snd lbs)
                           (FStar_List.map
                              (fun lb  ->
                                 FStar_Util.right
                                   lb.FStar_Syntax_Syntax.lbname))
                          in
                       let uu____27960 =
                         FStar_List.fold_right
                           (fun fv  ->
                              fun uu____27985  ->
                                match uu____27985 with
                                | (qs,ats) ->
                                    let uu____28012 =
                                      FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                                        env
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    (match uu____28012 with
                                     | (qs',ats') ->
                                         ((FStar_List.append qs' qs),
                                           (FStar_List.append ats' ats))))
                           fvs ([], [])
                          in
                       (match uu____27960 with
                        | (val_quals,val_attrs) ->
                            let quals1 =
                              match quals with
                              | uu____28066::uu____28067 ->
                                  FStar_List.map
                                    (trans_qual1 FStar_Pervasives_Native.None)
                                    quals
                              | uu____28070 -> val_quals  in
                            let quals2 =
                              let uu____28074 =
                                FStar_All.pipe_right lets1
                                  (FStar_Util.for_some
                                     (fun uu____28107  ->
                                        match uu____28107 with
                                        | (uu____28121,(uu____28122,t)) ->
                                            t.FStar_Parser_AST.level =
                                              FStar_Parser_AST.Formula))
                                 in
                              if uu____28074
                              then FStar_Syntax_Syntax.Logic :: quals1
                              else quals1  in
                            let lbs1 =
                              let uu____28142 =
                                FStar_All.pipe_right quals2
                                  (FStar_List.contains
                                     FStar_Syntax_Syntax.Abstract)
                                 in
                              if uu____28142
                              then
                                let uu____28148 =
                                  FStar_All.pipe_right
                                    (FStar_Pervasives_Native.snd lbs)
                                    (FStar_List.map
                                       (fun lb  ->
                                          let fv =
                                            FStar_Util.right
                                              lb.FStar_Syntax_Syntax.lbname
                                             in
                                          let uu___3665_28163 = lb  in
                                          {
                                            FStar_Syntax_Syntax.lbname =
                                              (FStar_Util.Inr
                                                 (let uu___3667_28165 = fv
                                                     in
                                                  {
                                                    FStar_Syntax_Syntax.fv_name
                                                      =
                                                      (uu___3667_28165.FStar_Syntax_Syntax.fv_name);
                                                    FStar_Syntax_Syntax.fv_delta
                                                      =
                                                      (FStar_Syntax_Syntax.Delta_abstract
                                                         (fv.FStar_Syntax_Syntax.fv_delta));
                                                    FStar_Syntax_Syntax.fv_qual
                                                      =
                                                      (uu___3667_28165.FStar_Syntax_Syntax.fv_qual)
                                                  }));
                                            FStar_Syntax_Syntax.lbunivs =
                                              (uu___3665_28163.FStar_Syntax_Syntax.lbunivs);
                                            FStar_Syntax_Syntax.lbtyp =
                                              (uu___3665_28163.FStar_Syntax_Syntax.lbtyp);
                                            FStar_Syntax_Syntax.lbeff =
                                              (uu___3665_28163.FStar_Syntax_Syntax.lbeff);
                                            FStar_Syntax_Syntax.lbdef =
                                              (uu___3665_28163.FStar_Syntax_Syntax.lbdef);
                                            FStar_Syntax_Syntax.lbattrs =
                                              (uu___3665_28163.FStar_Syntax_Syntax.lbattrs);
                                            FStar_Syntax_Syntax.lbpos =
                                              (uu___3665_28163.FStar_Syntax_Syntax.lbpos)
                                          }))
                                   in
                                ((FStar_Pervasives_Native.fst lbs),
                                  uu____28148)
                              else lbs  in
                            let names1 =
                              FStar_All.pipe_right fvs
                                (FStar_List.map
                                   (fun fv  ->
                                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                               in
                            let attrs =
                              FStar_List.map (desugar_term env)
                                d.FStar_Parser_AST.attrs
                               in
                            let s =
                              {
                                FStar_Syntax_Syntax.sigel =
                                  (FStar_Syntax_Syntax.Sig_let (lbs1, names1));
                                FStar_Syntax_Syntax.sigrng =
                                  (d.FStar_Parser_AST.drange);
                                FStar_Syntax_Syntax.sigquals = quals2;
                                FStar_Syntax_Syntax.sigmeta =
                                  FStar_Syntax_Syntax.default_sigmeta;
                                FStar_Syntax_Syntax.sigattrs =
                                  (FStar_List.append val_attrs attrs);
                                FStar_Syntax_Syntax.sigopts =
                                  FStar_Pervasives_Native.None
                              }  in
                            let env1 = FStar_Syntax_DsEnv.push_sigelt env s
                               in
                            (env1, [s]))
                   | uu____28190 ->
                       failwith "Desugaring a let did not produce a let")))
          else
            (let uu____28198 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____28217 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____28198 with
             | (pat,body) ->
                 let fresh_toplevel_name =
                   FStar_Ident.gen FStar_Range.dummyRange  in
                 let fresh_pat =
                   let var_pat =
                     FStar_Parser_AST.mk_pattern
                       (FStar_Parser_AST.PatVar
                          (fresh_toplevel_name, FStar_Pervasives_Native.None))
                       FStar_Range.dummyRange
                      in
                   match pat.FStar_Parser_AST.pat with
                   | FStar_Parser_AST.PatAscribed (pat1,ty) ->
                       let uu___3690_28254 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___3690_28254.FStar_Parser_AST.prange)
                       }
                   | uu____28261 -> var_pat  in
                 let main_let =
                   desugar_decl env
                     (let uu___3694_28268 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___3694_28268.FStar_Parser_AST.drange);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___3694_28268.FStar_Parser_AST.attrs)
                      })
                    in
                 let main =
                   let uu____28284 =
                     let uu____28285 =
                       FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                     FStar_Parser_AST.Var uu____28285  in
                   FStar_Parser_AST.mk_term uu____28284
                     pat.FStar_Parser_AST.prange FStar_Parser_AST.Expr
                    in
                 let build_generic_projection uu____28309 id_opt =
                   match uu____28309 with
                   | (env1,ses) ->
                       let uu____28331 =
                         match id_opt with
                         | FStar_Pervasives_Native.Some id1 ->
                             let lid = FStar_Ident.lid_of_ids [id1]  in
                             let branch1 =
                               let uu____28343 = FStar_Ident.range_of_lid lid
                                  in
                               FStar_Parser_AST.mk_term
                                 (FStar_Parser_AST.Var lid) uu____28343
                                 FStar_Parser_AST.Expr
                                in
                             let bv_pat =
                               let uu____28345 = FStar_Ident.range_of_id id1
                                  in
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatVar
                                    (id1, FStar_Pervasives_Native.None))
                                 uu____28345
                                in
                             (bv_pat, branch1)
                         | FStar_Pervasives_Native.None  ->
                             let id1 = FStar_Ident.gen FStar_Range.dummyRange
                                in
                             let branch1 =
                               FStar_Parser_AST.mk_term
                                 (FStar_Parser_AST.Const
                                    FStar_Const.Const_unit)
                                 FStar_Range.dummyRange FStar_Parser_AST.Expr
                                in
                             let bv_pat =
                               let uu____28351 = FStar_Ident.range_of_id id1
                                  in
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatVar
                                    (id1, FStar_Pervasives_Native.None))
                                 uu____28351
                                in
                             let bv_pat1 =
                               let uu____28355 = FStar_Ident.range_of_id id1
                                  in
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatAscribed
                                    (bv_pat,
                                      (unit_ty, FStar_Pervasives_Native.None)))
                                 uu____28355
                                in
                             (bv_pat1, branch1)
                          in
                       (match uu____28331 with
                        | (bv_pat,branch1) ->
                            let body1 =
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.Match
                                   (main,
                                     [(pat, FStar_Pervasives_Native.None,
                                        branch1)]))
                                main.FStar_Parser_AST.range
                                FStar_Parser_AST.Expr
                               in
                            let id_decl =
                              FStar_Parser_AST.mk_decl
                                (FStar_Parser_AST.TopLevelLet
                                   (FStar_Parser_AST.NoLetQualifier,
                                     [(bv_pat, body1)]))
                                FStar_Range.dummyRange []
                               in
                            let uu____28416 = desugar_decl env1 id_decl  in
                            (match uu____28416 with
                             | (env2,ses') ->
                                 (env2, (FStar_List.append ses ses'))))
                    in
                 let build_projection uu____28452 id1 =
                   match uu____28452 with
                   | (env1,ses) ->
                       build_generic_projection (env1, ses)
                         (FStar_Pervasives_Native.Some id1)
                    in
                 let build_coverage_check uu____28491 =
                   match uu____28491 with
                   | (env1,ses) ->
                       build_generic_projection (env1, ses)
                         FStar_Pervasives_Native.None
                    in
                 let bvs =
                   let uu____28515 = gather_pattern_bound_vars pat  in
                   FStar_All.pipe_right uu____28515 FStar_Util.set_elements
                    in
                 let uu____28522 =
                   (FStar_List.isEmpty bvs) &&
                     (let uu____28525 = is_var_pattern pat  in
                      Prims.op_Negation uu____28525)
                    in
                 if uu____28522
                 then build_coverage_check main_let
                 else FStar_List.fold_left build_projection main_let bvs)
      | FStar_Parser_AST.Main t ->
          let e = desugar_term env t  in
          let se =
            {
              FStar_Syntax_Syntax.sigel = (FStar_Syntax_Syntax.Sig_main e);
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = [];
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = [];
              FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
            }  in
          (env, [se])
      | FStar_Parser_AST.Assume (id1,t) ->
          let f = desugar_formula env t  in
          let lid = FStar_Syntax_DsEnv.qualify env id1  in
          (env,
            [{
               FStar_Syntax_Syntax.sigel =
                 (FStar_Syntax_Syntax.Sig_assume (lid, [], f));
               FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
               FStar_Syntax_Syntax.sigquals =
                 [FStar_Syntax_Syntax.Assumption];
               FStar_Syntax_Syntax.sigmeta =
                 FStar_Syntax_Syntax.default_sigmeta;
               FStar_Syntax_Syntax.sigattrs = [];
               FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
             }])
      | FStar_Parser_AST.Val (id1,t) ->
          let quals = d.FStar_Parser_AST.quals  in
          let t1 =
            let uu____28549 = close_fun env t  in
            desugar_term env uu____28549  in
          let quals1 =
            let uu____28553 =
              (FStar_Syntax_DsEnv.iface env) &&
                (FStar_Syntax_DsEnv.admitted_iface env)
               in
            if uu____28553
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_Syntax_DsEnv.qualify env id1  in
          let attrs =
            FStar_List.map (desugar_term env) d.FStar_Parser_AST.attrs  in
          let se =
            let uu____28565 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1
               in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____28565;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = attrs;
              FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
            }  in
          let env1 = FStar_Syntax_DsEnv.push_sigelt env se  in (env1, [se])
      | FStar_Parser_AST.Exception (id1,t_opt) ->
          let t =
            match t_opt with
            | FStar_Pervasives_Native.None  ->
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_lid env)
                  FStar_Parser_Const.exn_lid
            | FStar_Pervasives_Native.Some term ->
                let t = desugar_term env term  in
                let uu____28578 =
                  let uu____28587 = FStar_Syntax_Syntax.null_binder t  in
                  [uu____28587]  in
                let uu____28606 =
                  let uu____28609 =
                    FStar_Syntax_DsEnv.fail_or env
                      (FStar_Syntax_DsEnv.try_lookup_lid env)
                      FStar_Parser_Const.exn_lid
                     in
                  FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total
                    uu____28609
                   in
                FStar_Syntax_Util.arrow uu____28578 uu____28606
             in
          let l = FStar_Syntax_DsEnv.qualify env id1  in
          let qual = [FStar_Syntax_Syntax.ExceptionConstructor]  in
          let se =
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_datacon
                   (l, [], t, FStar_Parser_Const.exn_lid, Prims.int_zero,
                     [FStar_Parser_Const.exn_lid]));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = qual;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = [];
              FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
            }  in
          let se' =
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_bundle ([se], [l]));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = qual;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = [];
              FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
            }  in
          let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
          let data_ops = mk_data_projector_names [] env1 se  in
          let discs = mk_data_discriminators [] env1 [l]  in
          let env2 =
            FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt env1
              (FStar_List.append discs data_ops)
             in
          (env2, (FStar_List.append (se' :: discs) data_ops))
      | FStar_Parser_AST.NewEffect (FStar_Parser_AST.RedefineEffect
          (eff_name,eff_binders,defn)) ->
          let quals = d.FStar_Parser_AST.quals  in
          desugar_redefine_effect env d trans_qual1 quals eff_name
            eff_binders defn
      | FStar_Parser_AST.NewEffect (FStar_Parser_AST.DefineEffect
          (eff_name,eff_binders,eff_typ,eff_decls)) ->
          let quals = d.FStar_Parser_AST.quals  in
          let attrs = d.FStar_Parser_AST.attrs  in
          desugar_effect env d quals false eff_name eff_binders eff_typ
            eff_decls attrs
      | FStar_Parser_AST.LayeredEffect (FStar_Parser_AST.DefineEffect
          (eff_name,eff_binders,eff_typ,eff_decls)) ->
          let quals = d.FStar_Parser_AST.quals  in
          let attrs = d.FStar_Parser_AST.attrs  in
          desugar_effect env d quals true eff_name eff_binders eff_typ
            eff_decls attrs
      | FStar_Parser_AST.LayeredEffect (FStar_Parser_AST.RedefineEffect
          uu____28672) ->
          failwith
            "Impossible: LayeredEffect (RedefineEffect _) (should not be parseable)"
      | FStar_Parser_AST.SubEffect l ->
          let src_ed =
            lookup_effect_lid env l.FStar_Parser_AST.msource
              d.FStar_Parser_AST.drange
             in
          let dst_ed =
            lookup_effect_lid env l.FStar_Parser_AST.mdest
              d.FStar_Parser_AST.drange
             in
          let uu____28689 =
            let uu____28691 =
              (FStar_Syntax_Util.is_layered src_ed) ||
                (FStar_Syntax_Util.is_layered dst_ed)
               in
            Prims.op_Negation uu____28691  in
          if uu____28689
          then
            let uu____28698 =
              match l.FStar_Parser_AST.lift_op with
              | FStar_Parser_AST.NonReifiableLift t ->
                  let uu____28716 =
                    let uu____28719 =
                      let uu____28720 = desugar_term env t  in
                      ([], uu____28720)  in
                    FStar_Pervasives_Native.Some uu____28719  in
                  (uu____28716, FStar_Pervasives_Native.None)
              | FStar_Parser_AST.ReifiableLift (wp,t) ->
                  let uu____28733 =
                    let uu____28736 =
                      let uu____28737 = desugar_term env wp  in
                      ([], uu____28737)  in
                    FStar_Pervasives_Native.Some uu____28736  in
                  let uu____28744 =
                    let uu____28747 =
                      let uu____28748 = desugar_term env t  in
                      ([], uu____28748)  in
                    FStar_Pervasives_Native.Some uu____28747  in
                  (uu____28733, uu____28744)
              | FStar_Parser_AST.LiftForFree t ->
                  let uu____28760 =
                    let uu____28763 =
                      let uu____28764 = desugar_term env t  in
                      ([], uu____28764)  in
                    FStar_Pervasives_Native.Some uu____28763  in
                  (FStar_Pervasives_Native.None, uu____28760)
               in
            (match uu____28698 with
             | (lift_wp,lift) ->
                 let se =
                   {
                     FStar_Syntax_Syntax.sigel =
                       (FStar_Syntax_Syntax.Sig_sub_effect
                          {
                            FStar_Syntax_Syntax.source =
                              (src_ed.FStar_Syntax_Syntax.mname);
                            FStar_Syntax_Syntax.target =
                              (dst_ed.FStar_Syntax_Syntax.mname);
                            FStar_Syntax_Syntax.lift_wp = lift_wp;
                            FStar_Syntax_Syntax.lift = lift
                          });
                     FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
                     FStar_Syntax_Syntax.sigquals = [];
                     FStar_Syntax_Syntax.sigmeta =
                       FStar_Syntax_Syntax.default_sigmeta;
                     FStar_Syntax_Syntax.sigattrs = [];
                     FStar_Syntax_Syntax.sigopts =
                       FStar_Pervasives_Native.None
                   }  in
                 (env, [se]))
          else
            (match l.FStar_Parser_AST.lift_op with
             | FStar_Parser_AST.NonReifiableLift t ->
                 let sub_eff =
                   let uu____28798 =
                     let uu____28801 =
                       let uu____28802 = desugar_term env t  in
                       ([], uu____28802)  in
                     FStar_Pervasives_Native.Some uu____28801  in
                   {
                     FStar_Syntax_Syntax.source =
                       (src_ed.FStar_Syntax_Syntax.mname);
                     FStar_Syntax_Syntax.target =
                       (dst_ed.FStar_Syntax_Syntax.mname);
                     FStar_Syntax_Syntax.lift_wp =
                       FStar_Pervasives_Native.None;
                     FStar_Syntax_Syntax.lift = uu____28798
                   }  in
                 (env,
                   [{
                      FStar_Syntax_Syntax.sigel =
                        (FStar_Syntax_Syntax.Sig_sub_effect sub_eff);
                      FStar_Syntax_Syntax.sigrng =
                        (d.FStar_Parser_AST.drange);
                      FStar_Syntax_Syntax.sigquals = [];
                      FStar_Syntax_Syntax.sigmeta =
                        FStar_Syntax_Syntax.default_sigmeta;
                      FStar_Syntax_Syntax.sigattrs = [];
                      FStar_Syntax_Syntax.sigopts =
                        FStar_Pervasives_Native.None
                    }])
             | uu____28809 ->
                 failwith
                   "Impossible! unexpected lift_op for lift to a layered effect")
      | FStar_Parser_AST.Polymonadic_bind (m_eff,n_eff,p_eff,bind1) ->
          let m = lookup_effect_lid env m_eff d.FStar_Parser_AST.drange  in
          let n1 = lookup_effect_lid env n_eff d.FStar_Parser_AST.drange  in
          let p = lookup_effect_lid env p_eff d.FStar_Parser_AST.drange  in
          let uu____28822 =
            let uu____28823 =
              let uu____28824 =
                let uu____28825 =
                  let uu____28836 =
                    let uu____28837 = desugar_term env bind1  in
                    ([], uu____28837)  in
                  ((m.FStar_Syntax_Syntax.mname),
                    (n1.FStar_Syntax_Syntax.mname),
                    (p.FStar_Syntax_Syntax.mname), uu____28836,
                    ([], FStar_Syntax_Syntax.tun))
                   in
                FStar_Syntax_Syntax.Sig_polymonadic_bind uu____28825  in
              {
                FStar_Syntax_Syntax.sigel = uu____28824;
                FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
                FStar_Syntax_Syntax.sigquals = [];
                FStar_Syntax_Syntax.sigmeta =
                  FStar_Syntax_Syntax.default_sigmeta;
                FStar_Syntax_Syntax.sigattrs = [];
                FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
              }  in
            [uu____28823]  in
          (env, uu____28822)
      | FStar_Parser_AST.Splice (ids,t) ->
          let t1 = desugar_term env t  in
          let se =
            let uu____28856 =
              let uu____28857 =
                let uu____28864 =
                  FStar_List.map (FStar_Syntax_DsEnv.qualify env) ids  in
                (uu____28864, t1)  in
              FStar_Syntax_Syntax.Sig_splice uu____28857  in
            {
              FStar_Syntax_Syntax.sigel = uu____28856;
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = [];
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = [];
              FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
            }  in
          let env1 = FStar_Syntax_DsEnv.push_sigelt env se  in (env1, [se])

let (desugar_decls :
  env_t ->
    FStar_Parser_AST.decl Prims.list ->
      (env_t * FStar_Syntax_Syntax.sigelt Prims.list))
  =
  fun env  ->
    fun decls  ->
      let uu____28891 =
        FStar_List.fold_left
          (fun uu____28911  ->
             fun d  ->
               match uu____28911 with
               | (env1,sigelts) ->
                   let uu____28931 = desugar_decl env1 d  in
                   (match uu____28931 with
                    | (env2,se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls
         in
      match uu____28891 with | (env1,sigelts) -> (env1, sigelts)
  
let (open_prims_all :
  (FStar_Parser_AST.decoration Prims.list -> FStar_Parser_AST.decl)
    Prims.list)
  =
  [FStar_Parser_AST.mk_decl
     (FStar_Parser_AST.Open FStar_Parser_Const.prims_lid)
     FStar_Range.dummyRange;
  FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open FStar_Parser_Const.all_lid)
    FStar_Range.dummyRange]
  
let (desugar_modul_common :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Syntax_DsEnv.env ->
      FStar_Parser_AST.modul ->
        (env_t * FStar_Syntax_Syntax.modul * Prims.bool))
  =
  fun curmod  ->
    fun env  ->
      fun m  ->
        let env1 =
          match (curmod, m) with
          | (FStar_Pervasives_Native.None ,uu____29022) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____29026;
               FStar_Syntax_Syntax.exports = uu____29027;
               FStar_Syntax_Syntax.is_interface = uu____29028;_},FStar_Parser_AST.Module
             (current_lid,uu____29030)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____29039) ->
              let uu____29042 =
                FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod
                 in
              FStar_Pervasives_Native.fst uu____29042
           in
        let uu____29047 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____29089 =
                FStar_Syntax_DsEnv.prepare_module_or_interface true admitted
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____29089, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____29111 =
                FStar_Syntax_DsEnv.prepare_module_or_interface false false
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____29111, mname, decls, false)
           in
        match uu____29047 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____29153 = desugar_decls env2 decls  in
            (match uu____29153 with
             | (env3,sigelts) ->
                 let modul =
                   {
                     FStar_Syntax_Syntax.name = mname;
                     FStar_Syntax_Syntax.declarations = sigelts;
                     FStar_Syntax_Syntax.exports = [];
                     FStar_Syntax_Syntax.is_interface = intf
                   }  in
                 (env3, modul, pop_when_done))
  
let (as_interface : FStar_Parser_AST.modul -> FStar_Parser_AST.modul) =
  fun m  ->
    match m with
    | FStar_Parser_AST.Module (mname,decls) ->
        FStar_Parser_AST.Interface (mname, decls, true)
    | i -> i
  
let (desugar_partial_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    env_t -> FStar_Parser_AST.modul -> (env_t * FStar_Syntax_Syntax.modul))
  =
  fun curmod  ->
    fun env  ->
      fun m  ->
        let m1 =
          let uu____29221 =
            (FStar_Options.interactive ()) &&
              (let uu____29224 =
                 let uu____29226 =
                   let uu____29228 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____29228  in
                 FStar_Util.get_file_extension uu____29226  in
               FStar_List.mem uu____29224 ["fsti"; "fsi"])
             in
          if uu____29221 then as_interface m else m  in
        let uu____29242 = desugar_modul_common curmod env m1  in
        match uu____29242 with
        | (env1,modul,pop_when_done) ->
            if pop_when_done
            then
              let uu____29264 = FStar_Syntax_DsEnv.pop ()  in
              (uu____29264, modul)
            else (env1, modul)
  
let (desugar_modul :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.modul -> (env_t * FStar_Syntax_Syntax.modul))
  =
  fun env  ->
    fun m  ->
      let uu____29286 =
        desugar_modul_common FStar_Pervasives_Native.None env m  in
      match uu____29286 with
      | (env1,modul,pop_when_done) ->
          let uu____29303 =
            FStar_Syntax_DsEnv.finish_module_or_interface env1 modul  in
          (match uu____29303 with
           | (env2,modul1) ->
               ((let uu____29315 =
                   let uu____29317 =
                     FStar_Ident.string_of_lid
                       modul1.FStar_Syntax_Syntax.name
                      in
                   FStar_Options.dump_module uu____29317  in
                 if uu____29315
                 then
                   let uu____29320 =
                     FStar_Syntax_Print.modul_to_string modul1  in
                   FStar_Util.print1 "Module after desugaring:\n%s\n"
                     uu____29320
                 else ());
                (let uu____29325 =
                   if pop_when_done
                   then
                     FStar_Syntax_DsEnv.export_interface
                       modul1.FStar_Syntax_Syntax.name env2
                   else env2  in
                 (uu____29325, modul1))))
  
let with_options : 'a . (unit -> 'a) -> 'a =
  fun f  ->
    FStar_Options.push ();
    (let res = f ()  in
     let light = FStar_Options.ml_ish ()  in
     FStar_Options.pop ();
     if light then FStar_Options.set_ml_ish () else ();
     res)
  
let (ast_modul_to_modul :
  FStar_Parser_AST.modul ->
    FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun env  ->
      with_options
        (fun uu____29375  ->
           let uu____29376 = desugar_modul env modul  in
           match uu____29376 with | (e,m) -> (m, e))
  
let (decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv)
  =
  fun decls  ->
    fun env  ->
      with_options
        (fun uu____29414  ->
           let uu____29415 = desugar_decls env decls  in
           match uu____29415 with | (env1,sigelts) -> (sigelts, env1))
  
let (partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun a_modul  ->
      fun env  ->
        with_options
          (fun uu____29466  ->
             let uu____29467 = desugar_partial_modul modul env a_modul  in
             match uu____29467 with | (env1,modul1) -> (modul1, env1))
  
let (add_modul_to_env :
  FStar_Syntax_Syntax.modul ->
    FStar_Syntax_DsEnv.module_inclusion_info ->
      (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
        unit FStar_Syntax_DsEnv.withenv)
  =
  fun m  ->
    fun mii  ->
      fun erase_univs  ->
        fun en  ->
          let erase_univs_ed ed =
            let erase_binders bs =
              match bs with
              | [] -> []
              | uu____29562 ->
                  let t =
                    let uu____29572 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Pervasives_Native.None FStar_Range.dummyRange
                       in
                    erase_univs uu____29572  in
                  let uu____29585 =
                    let uu____29586 = FStar_Syntax_Subst.compress t  in
                    uu____29586.FStar_Syntax_Syntax.n  in
                  (match uu____29585 with
                   | FStar_Syntax_Syntax.Tm_abs (bs1,uu____29598,uu____29599)
                       -> bs1
                   | uu____29624 -> failwith "Impossible")
               in
            let uu____29634 =
              let uu____29641 = erase_binders ed.FStar_Syntax_Syntax.binders
                 in
              FStar_Syntax_Subst.open_term' uu____29641
                FStar_Syntax_Syntax.t_unit
               in
            match uu____29634 with
            | (binders,uu____29643,binders_opening) ->
                let erase_term t =
                  let uu____29651 =
                    let uu____29652 =
                      FStar_Syntax_Subst.subst binders_opening t  in
                    erase_univs uu____29652  in
                  FStar_Syntax_Subst.close binders uu____29651  in
                let erase_tscheme uu____29670 =
                  match uu____29670 with
                  | (us,t) ->
                      let t1 =
                        let uu____29690 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening
                           in
                        FStar_Syntax_Subst.subst uu____29690 t  in
                      let uu____29693 =
                        let uu____29694 = erase_univs t1  in
                        FStar_Syntax_Subst.close binders uu____29694  in
                      ([], uu____29693)
                   in
                let erase_action action =
                  let opening =
                    FStar_Syntax_Subst.shift_subst
                      (FStar_List.length
                         action.FStar_Syntax_Syntax.action_univs)
                      binders_opening
                     in
                  let erased_action_params =
                    match action.FStar_Syntax_Syntax.action_params with
                    | [] -> []
                    | uu____29717 ->
                        let bs =
                          let uu____29727 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params
                             in
                          FStar_All.pipe_left erase_binders uu____29727  in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Pervasives_Native.None
                            FStar_Range.dummyRange
                           in
                        let uu____29767 =
                          let uu____29768 =
                            let uu____29771 =
                              FStar_Syntax_Subst.close binders t  in
                            FStar_Syntax_Subst.compress uu____29771  in
                          uu____29768.FStar_Syntax_Syntax.n  in
                        (match uu____29767 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1,uu____29773,uu____29774) -> bs1
                         | uu____29799 -> failwith "Impossible")
                     in
                  let erase_term1 t =
                    let uu____29807 =
                      let uu____29808 = FStar_Syntax_Subst.subst opening t
                         in
                      erase_univs uu____29808  in
                    FStar_Syntax_Subst.close binders uu____29807  in
                  let uu___3990_29809 = action  in
                  let uu____29810 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn  in
                  let uu____29811 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ  in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___3990_29809.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___3990_29809.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____29810;
                    FStar_Syntax_Syntax.action_typ = uu____29811
                  }  in
                let uu___3992_29812 = ed  in
                let uu____29813 = FStar_Syntax_Subst.close_binders binders
                   in
                let uu____29814 =
                  erase_tscheme ed.FStar_Syntax_Syntax.signature  in
                let uu____29815 =
                  FStar_Syntax_Util.apply_eff_combinators erase_tscheme
                    ed.FStar_Syntax_Syntax.combinators
                   in
                let uu____29816 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions
                   in
                {
                  FStar_Syntax_Syntax.mname =
                    (uu___3992_29812.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.cattributes =
                    (uu___3992_29812.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____29813;
                  FStar_Syntax_Syntax.signature = uu____29814;
                  FStar_Syntax_Syntax.combinators = uu____29815;
                  FStar_Syntax_Syntax.actions = uu____29816;
                  FStar_Syntax_Syntax.eff_attrs =
                    (uu___3992_29812.FStar_Syntax_Syntax.eff_attrs)
                }
             in
          let push_sigelt1 env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___3999_29832 = se  in
                  let uu____29833 =
                    let uu____29834 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect uu____29834  in
                  {
                    FStar_Syntax_Syntax.sigel = uu____29833;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___3999_29832.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___3999_29832.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___3999_29832.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___3999_29832.FStar_Syntax_Syntax.sigattrs);
                    FStar_Syntax_Syntax.sigopts =
                      (uu___3999_29832.FStar_Syntax_Syntax.sigopts)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____29836 -> FStar_Syntax_DsEnv.push_sigelt env se  in
          let uu____29837 =
            FStar_Syntax_DsEnv.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii
             in
          match uu____29837 with
          | (en1,pop_when_done) ->
              let en2 =
                let uu____29854 =
                  FStar_Syntax_DsEnv.set_current_module en1
                    m.FStar_Syntax_Syntax.name
                   in
                FStar_List.fold_left push_sigelt1 uu____29854
                  m.FStar_Syntax_Syntax.exports
                 in
              let env = FStar_Syntax_DsEnv.finish en2 m  in
              let uu____29856 =
                if pop_when_done
                then
                  FStar_Syntax_DsEnv.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env  in
              ((), uu____29856)
  
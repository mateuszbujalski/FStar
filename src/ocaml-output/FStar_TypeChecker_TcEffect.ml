open Prims
let (dmff_cps_and_elaborate :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.eff_decl *
        FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option))
  = fun env  -> fun ed  -> FStar_TypeChecker_DMFF.cps_and_elaborate env ed 
let (check_and_gen :
  FStar_TypeChecker_Env.env ->
    Prims.string ->
      Prims.string ->
        Prims.int ->
          (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term) ->
            (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term *
              FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun eff_name  ->
      fun comb  ->
        fun n1  ->
          fun uu____58  ->
            match uu____58 with
            | (us,t) ->
                let uu____80 = FStar_Syntax_Subst.open_univ_vars us t  in
                (match uu____80 with
                 | (us1,t1) ->
                     let uu____93 =
                       let uu____98 =
                         let uu____105 =
                           FStar_TypeChecker_Env.push_univ_vars env us1  in
                         FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                           uu____105 t1
                          in
                       match uu____98 with
                       | (t2,lc,g) ->
                           (FStar_TypeChecker_Rel.force_trivial_guard env g;
                            (t2, (lc.FStar_TypeChecker_Common.res_typ)))
                        in
                     (match uu____93 with
                      | (t2,ty) ->
                          let uu____122 =
                            FStar_TypeChecker_Util.generalize_universes env
                              t2
                             in
                          (match uu____122 with
                           | (g_us,t3) ->
                               let ty1 =
                                 FStar_Syntax_Subst.close_univ_vars g_us ty
                                  in
                               (if (FStar_List.length g_us) <> n1
                                then
                                  (let error =
                                     let uu____145 =
                                       FStar_Util.string_of_int n1  in
                                     let uu____147 =
                                       let uu____149 =
                                         FStar_All.pipe_right g_us
                                           FStar_List.length
                                          in
                                       FStar_All.pipe_right uu____149
                                         FStar_Util.string_of_int
                                        in
                                     let uu____156 =
                                       FStar_Syntax_Print.tscheme_to_string
                                         (g_us, t3)
                                        in
                                     FStar_Util.format5
                                       "Expected %s:%s to be universe-polymorphic in %s universes, but found %s (tscheme: %s)"
                                       eff_name comb uu____145 uu____147
                                       uu____156
                                      in
                                   FStar_Errors.raise_error
                                     (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                       error) t3.FStar_Syntax_Syntax.pos;
                                   (match us1 with
                                    | [] -> ()
                                    | uu____165 ->
                                        let uu____166 =
                                          ((FStar_List.length us1) =
                                             (FStar_List.length g_us))
                                            &&
                                            (FStar_List.forall2
                                               (fun u1  ->
                                                  fun u2  ->
                                                    let uu____173 =
                                                      FStar_Syntax_Syntax.order_univ_name
                                                        u1 u2
                                                       in
                                                    uu____173 =
                                                      Prims.int_zero) us1
                                               g_us)
                                           in
                                        if uu____166
                                        then ()
                                        else
                                          (let uu____180 =
                                             let uu____186 =
                                               let uu____188 =
                                                 FStar_Syntax_Print.univ_names_to_string
                                                   us1
                                                  in
                                               let uu____190 =
                                                 FStar_Syntax_Print.univ_names_to_string
                                                   g_us
                                                  in
                                               FStar_Util.format4
                                                 "Expected and generalized universes in the declaration for %s:%s are different, input: %s, but after gen: %s"
                                                 eff_name comb uu____188
                                                 uu____190
                                                in
                                             (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                               uu____186)
                                              in
                                           FStar_Errors.raise_error uu____180
                                             t3.FStar_Syntax_Syntax.pos)))
                                else ();
                                (g_us, t3, ty1)))))
  
let (pure_wp_uvar :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      Prims.string ->
        FStar_Range.range ->
          (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun t  ->
      fun reason  ->
        fun r  ->
          let pure_wp_t =
            let pure_wp_ts =
              let uu____229 =
                FStar_TypeChecker_Env.lookup_definition
                  [FStar_TypeChecker_Env.NoDelta] env
                  FStar_Parser_Const.pure_wp_lid
                 in
              FStar_All.pipe_right uu____229 FStar_Util.must  in
            let uu____234 = FStar_TypeChecker_Env.inst_tscheme pure_wp_ts  in
            match uu____234 with
            | (uu____239,pure_wp_t) ->
                let uu____241 =
                  let uu____246 =
                    let uu____247 =
                      FStar_All.pipe_right t FStar_Syntax_Syntax.as_arg  in
                    [uu____247]  in
                  FStar_Syntax_Syntax.mk_Tm_app pure_wp_t uu____246  in
                uu____241 FStar_Pervasives_Native.None r
             in
          let uu____280 =
            FStar_TypeChecker_Util.new_implicit_var reason r env pure_wp_t
             in
          match uu____280 with
          | (pure_wp_uvar,uu____298,guard_wp) -> (pure_wp_uvar, guard_wp)
  
let (check_no_subtyping_for_layered_combinator :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option -> unit)
  =
  fun env  ->
    fun t  ->
      fun k  ->
        (let uu____333 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "LayeredEffects")
            in
         if uu____333
         then
           let uu____338 = FStar_Syntax_Print.term_to_string t  in
           let uu____340 =
             match k with
             | FStar_Pervasives_Native.None  -> "None"
             | FStar_Pervasives_Native.Some k1 ->
                 FStar_Syntax_Print.term_to_string k1
              in
           FStar_Util.print2
             "Checking that %s is well typed with no subtyping (k:%s)\n"
             uu____338 uu____340
         else ());
        (let env1 =
           let uu___54_349 = env  in
           {
             FStar_TypeChecker_Env.solver =
               (uu___54_349.FStar_TypeChecker_Env.solver);
             FStar_TypeChecker_Env.range =
               (uu___54_349.FStar_TypeChecker_Env.range);
             FStar_TypeChecker_Env.curmodule =
               (uu___54_349.FStar_TypeChecker_Env.curmodule);
             FStar_TypeChecker_Env.gamma =
               (uu___54_349.FStar_TypeChecker_Env.gamma);
             FStar_TypeChecker_Env.gamma_sig =
               (uu___54_349.FStar_TypeChecker_Env.gamma_sig);
             FStar_TypeChecker_Env.gamma_cache =
               (uu___54_349.FStar_TypeChecker_Env.gamma_cache);
             FStar_TypeChecker_Env.modules =
               (uu___54_349.FStar_TypeChecker_Env.modules);
             FStar_TypeChecker_Env.expected_typ =
               (uu___54_349.FStar_TypeChecker_Env.expected_typ);
             FStar_TypeChecker_Env.sigtab =
               (uu___54_349.FStar_TypeChecker_Env.sigtab);
             FStar_TypeChecker_Env.attrtab =
               (uu___54_349.FStar_TypeChecker_Env.attrtab);
             FStar_TypeChecker_Env.instantiate_imp =
               (uu___54_349.FStar_TypeChecker_Env.instantiate_imp);
             FStar_TypeChecker_Env.effects =
               (uu___54_349.FStar_TypeChecker_Env.effects);
             FStar_TypeChecker_Env.generalize =
               (uu___54_349.FStar_TypeChecker_Env.generalize);
             FStar_TypeChecker_Env.letrecs =
               (uu___54_349.FStar_TypeChecker_Env.letrecs);
             FStar_TypeChecker_Env.top_level =
               (uu___54_349.FStar_TypeChecker_Env.top_level);
             FStar_TypeChecker_Env.check_uvars =
               (uu___54_349.FStar_TypeChecker_Env.check_uvars);
             FStar_TypeChecker_Env.use_eq =
               (uu___54_349.FStar_TypeChecker_Env.use_eq);
             FStar_TypeChecker_Env.use_eq_strict = true;
             FStar_TypeChecker_Env.is_iface =
               (uu___54_349.FStar_TypeChecker_Env.is_iface);
             FStar_TypeChecker_Env.admit =
               (uu___54_349.FStar_TypeChecker_Env.admit);
             FStar_TypeChecker_Env.lax =
               (uu___54_349.FStar_TypeChecker_Env.lax);
             FStar_TypeChecker_Env.lax_universes =
               (uu___54_349.FStar_TypeChecker_Env.lax_universes);
             FStar_TypeChecker_Env.phase1 =
               (uu___54_349.FStar_TypeChecker_Env.phase1);
             FStar_TypeChecker_Env.failhard =
               (uu___54_349.FStar_TypeChecker_Env.failhard);
             FStar_TypeChecker_Env.nosynth =
               (uu___54_349.FStar_TypeChecker_Env.nosynth);
             FStar_TypeChecker_Env.uvar_subtyping =
               (uu___54_349.FStar_TypeChecker_Env.uvar_subtyping);
             FStar_TypeChecker_Env.tc_term =
               (uu___54_349.FStar_TypeChecker_Env.tc_term);
             FStar_TypeChecker_Env.type_of =
               (uu___54_349.FStar_TypeChecker_Env.type_of);
             FStar_TypeChecker_Env.universe_of =
               (uu___54_349.FStar_TypeChecker_Env.universe_of);
             FStar_TypeChecker_Env.check_type_of =
               (uu___54_349.FStar_TypeChecker_Env.check_type_of);
             FStar_TypeChecker_Env.use_bv_sorts =
               (uu___54_349.FStar_TypeChecker_Env.use_bv_sorts);
             FStar_TypeChecker_Env.qtbl_name_and_index =
               (uu___54_349.FStar_TypeChecker_Env.qtbl_name_and_index);
             FStar_TypeChecker_Env.normalized_eff_names =
               (uu___54_349.FStar_TypeChecker_Env.normalized_eff_names);
             FStar_TypeChecker_Env.fv_delta_depths =
               (uu___54_349.FStar_TypeChecker_Env.fv_delta_depths);
             FStar_TypeChecker_Env.proof_ns =
               (uu___54_349.FStar_TypeChecker_Env.proof_ns);
             FStar_TypeChecker_Env.synth_hook =
               (uu___54_349.FStar_TypeChecker_Env.synth_hook);
             FStar_TypeChecker_Env.try_solve_implicits_hook =
               (uu___54_349.FStar_TypeChecker_Env.try_solve_implicits_hook);
             FStar_TypeChecker_Env.splice =
               (uu___54_349.FStar_TypeChecker_Env.splice);
             FStar_TypeChecker_Env.mpreprocess =
               (uu___54_349.FStar_TypeChecker_Env.mpreprocess);
             FStar_TypeChecker_Env.postprocess =
               (uu___54_349.FStar_TypeChecker_Env.postprocess);
             FStar_TypeChecker_Env.is_native_tactic =
               (uu___54_349.FStar_TypeChecker_Env.is_native_tactic);
             FStar_TypeChecker_Env.identifier_info =
               (uu___54_349.FStar_TypeChecker_Env.identifier_info);
             FStar_TypeChecker_Env.tc_hooks =
               (uu___54_349.FStar_TypeChecker_Env.tc_hooks);
             FStar_TypeChecker_Env.dsenv =
               (uu___54_349.FStar_TypeChecker_Env.dsenv);
             FStar_TypeChecker_Env.nbe =
               (uu___54_349.FStar_TypeChecker_Env.nbe);
             FStar_TypeChecker_Env.strict_args_tab =
               (uu___54_349.FStar_TypeChecker_Env.strict_args_tab);
             FStar_TypeChecker_Env.erasable_types_tab =
               (uu___54_349.FStar_TypeChecker_Env.erasable_types_tab)
           }  in
         match k with
         | FStar_Pervasives_Native.None  ->
             let uu____351 = FStar_TypeChecker_TcTerm.tc_trivial_guard env1 t
                in
             ()
         | FStar_Pervasives_Native.Some k1 ->
             let uu____357 =
               FStar_TypeChecker_TcTerm.tc_check_trivial_guard env1 t k1  in
             ())
  
let (tc_layered_eff_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.eff_decl)
  =
  fun env0  ->
    fun ed  ->
      fun quals  ->
        (let uu____379 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
             (FStar_Options.Other "LayeredEffects")
            in
         if uu____379
         then
           let uu____384 = FStar_Syntax_Print.eff_decl_to_string false ed  in
           FStar_Util.print1 "Typechecking layered effect: \n\t%s\n"
             uu____384
         else ());
        if
          ((FStar_List.length ed.FStar_Syntax_Syntax.univs) <> Prims.int_zero)
            ||
            ((FStar_List.length ed.FStar_Syntax_Syntax.binders) <>
               Prims.int_zero)
        then
          (let uu____402 =
             let uu____408 =
               let uu____410 =
                 let uu____412 =
                   FStar_Ident.string_of_lid ed.FStar_Syntax_Syntax.mname  in
                 Prims.op_Hat uu____412 ")"  in
               Prims.op_Hat "Binders are not supported for layered effects ("
                 uu____410
                in
             (FStar_Errors.Fatal_UnexpectedEffect, uu____408)  in
           let uu____417 =
             FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname  in
           FStar_Errors.raise_error uu____402 uu____417)
        else ();
        (let log_combinator s uu____443 =
           match uu____443 with
           | (us,t,ty) ->
               let uu____472 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
                   (FStar_Options.Other "LayeredEffects")
                  in
               if uu____472
               then
                 let uu____477 =
                   FStar_Ident.string_of_lid ed.FStar_Syntax_Syntax.mname  in
                 let uu____479 = FStar_Syntax_Print.tscheme_to_string (us, t)
                    in
                 let uu____485 =
                   FStar_Syntax_Print.tscheme_to_string (us, ty)  in
                 FStar_Util.print4 "Typechecked %s:%s = %s:%s\n" uu____477 s
                   uu____479 uu____485
               else ()
            in
         let fresh_a_and_u_a a =
           let uu____510 = FStar_Syntax_Util.type_u ()  in
           FStar_All.pipe_right uu____510
             (fun uu____527  ->
                match uu____527 with
                | (t,u) ->
                    let uu____538 =
                      let uu____539 =
                        FStar_Syntax_Syntax.gen_bv a
                          FStar_Pervasives_Native.None t
                         in
                      FStar_All.pipe_right uu____539
                        FStar_Syntax_Syntax.mk_binder
                       in
                    (uu____538, u))
            in
         let fresh_x_a x a =
           let uu____553 =
             let uu____554 =
               let uu____555 =
                 FStar_All.pipe_right a FStar_Pervasives_Native.fst  in
               FStar_All.pipe_right uu____555 FStar_Syntax_Syntax.bv_to_name
                in
             FStar_Syntax_Syntax.gen_bv x FStar_Pervasives_Native.None
               uu____554
              in
           FStar_All.pipe_right uu____553 FStar_Syntax_Syntax.mk_binder  in
         let check_and_gen1 =
           let uu____589 =
             FStar_Ident.string_of_lid ed.FStar_Syntax_Syntax.mname  in
           check_and_gen env0 uu____589  in
         let signature =
           let r =
             (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos
              in
           let uu____609 =
             check_and_gen1 "signature" Prims.int_one
               ed.FStar_Syntax_Syntax.signature
              in
           match uu____609 with
           | (sig_us,sig_t,sig_ty) ->
               let uu____633 = FStar_Syntax_Subst.open_univ_vars sig_us sig_t
                  in
               (match uu____633 with
                | (us,t) ->
                    let env = FStar_TypeChecker_Env.push_univ_vars env0 us
                       in
                    let uu____653 = fresh_a_and_u_a "a"  in
                    (match uu____653 with
                     | (a,u) ->
                         let rest_bs =
                           let uu____674 =
                             let uu____675 =
                               FStar_All.pipe_right a
                                 FStar_Pervasives_Native.fst
                                in
                             FStar_All.pipe_right uu____675
                               FStar_Syntax_Syntax.bv_to_name
                              in
                           FStar_TypeChecker_Util.layered_effect_indices_as_binders
                             env r ed.FStar_Syntax_Syntax.mname
                             (sig_us, sig_t) u uu____674
                            in
                         let bs = a :: rest_bs  in
                         let k =
                           let uu____706 =
                             FStar_Syntax_Syntax.mk_Total
                               FStar_Syntax_Syntax.teff
                              in
                           FStar_Syntax_Util.arrow bs uu____706  in
                         let g_eq = FStar_TypeChecker_Rel.teq env t k  in
                         (FStar_TypeChecker_Rel.force_trivial_guard env g_eq;
                          (let uu____711 =
                             let uu____714 =
                               FStar_All.pipe_right k
                                 (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                    env)
                                in
                             FStar_Syntax_Subst.close_univ_vars us uu____714
                              in
                           (sig_us, uu____711, sig_ty)))))
            in
         log_combinator "signature" signature;
         (let uu____723 =
            let repr_ts =
              let uu____745 =
                FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr  in
              FStar_All.pipe_right uu____745 FStar_Util.must  in
            let r =
              (FStar_Pervasives_Native.snd repr_ts).FStar_Syntax_Syntax.pos
               in
            let uu____773 = check_and_gen1 "repr" Prims.int_one repr_ts  in
            match uu____773 with
            | (repr_us,repr_t,repr_ty) ->
                let underlying_effect_lid =
                  let repr_t1 =
                    FStar_TypeChecker_Normalize.normalize
                      [FStar_TypeChecker_Env.UnfoldUntil
                         (FStar_Syntax_Syntax.Delta_constant_at_level
                            Prims.int_zero);
                      FStar_TypeChecker_Env.AllowUnboundUniverses] env0
                      repr_t
                     in
                  let uu____804 =
                    let uu____805 = FStar_Syntax_Subst.compress repr_t1  in
                    uu____805.FStar_Syntax_Syntax.n  in
                  match uu____804 with
                  | FStar_Syntax_Syntax.Tm_abs (uu____808,t,uu____810) ->
                      let uu____835 =
                        let uu____836 = FStar_Syntax_Subst.compress t  in
                        uu____836.FStar_Syntax_Syntax.n  in
                      (match uu____835 with
                       | FStar_Syntax_Syntax.Tm_arrow (uu____839,c) ->
                           let uu____861 =
                             FStar_All.pipe_right c
                               FStar_Syntax_Util.comp_effect_name
                              in
                           FStar_All.pipe_right uu____861
                             (FStar_TypeChecker_Env.norm_eff_name env0)
                       | uu____864 ->
                           let uu____865 =
                             let uu____871 =
                               let uu____873 =
                                 FStar_All.pipe_right
                                   ed.FStar_Syntax_Syntax.mname
                                   FStar_Ident.string_of_lid
                                  in
                               let uu____876 =
                                 FStar_Syntax_Print.term_to_string t  in
                               FStar_Util.format2
                                 "repr body for %s is not an arrow (%s)"
                                 uu____873 uu____876
                                in
                             (FStar_Errors.Fatal_UnexpectedEffect, uu____871)
                              in
                           FStar_Errors.raise_error uu____865 r)
                  | uu____880 ->
                      let uu____881 =
                        let uu____887 =
                          let uu____889 =
                            FStar_All.pipe_right ed.FStar_Syntax_Syntax.mname
                              FStar_Ident.string_of_lid
                             in
                          let uu____892 =
                            FStar_Syntax_Print.term_to_string repr_t1  in
                          FStar_Util.format2
                            "repr for %s is not an abstraction (%s)"
                            uu____889 uu____892
                           in
                        (FStar_Errors.Fatal_UnexpectedEffect, uu____887)  in
                      FStar_Errors.raise_error uu____881 r
                   in
                ((let uu____897 =
                    (FStar_All.pipe_right quals
                       (FStar_List.contains FStar_Syntax_Syntax.TotalEffect))
                      &&
                      (let uu____903 =
                         FStar_TypeChecker_Env.is_total_effect env0
                           underlying_effect_lid
                          in
                       Prims.op_Negation uu____903)
                     in
                  if uu____897
                  then
                    let uu____906 =
                      let uu____912 =
                        let uu____914 =
                          FStar_All.pipe_right ed.FStar_Syntax_Syntax.mname
                            FStar_Ident.string_of_lid
                           in
                        let uu____917 =
                          FStar_All.pipe_right underlying_effect_lid
                            FStar_Ident.string_of_lid
                           in
                        FStar_Util.format2
                          "Effect %s is marked total but its underlying effect %s is not total"
                          uu____914 uu____917
                         in
                      (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                        uu____912)
                       in
                    FStar_Errors.raise_error uu____906 r
                  else ());
                 (let uu____924 =
                    FStar_Syntax_Subst.open_univ_vars repr_us repr_ty  in
                  match uu____924 with
                  | (us,ty) ->
                      let env = FStar_TypeChecker_Env.push_univ_vars env0 us
                         in
                      let uu____948 = fresh_a_and_u_a "a"  in
                      (match uu____948 with
                       | (a,u) ->
                           let rest_bs =
                             let signature_ts =
                               let uu____974 = signature  in
                               match uu____974 with
                               | (us1,t,uu____989) -> (us1, t)  in
                             let uu____1006 =
                               let uu____1007 =
                                 FStar_All.pipe_right a
                                   FStar_Pervasives_Native.fst
                                  in
                               FStar_All.pipe_right uu____1007
                                 FStar_Syntax_Syntax.bv_to_name
                                in
                             FStar_TypeChecker_Util.layered_effect_indices_as_binders
                               env r ed.FStar_Syntax_Syntax.mname
                               signature_ts u uu____1006
                              in
                           let bs = a :: rest_bs  in
                           let k =
                             let uu____1034 =
                               let uu____1037 = FStar_Syntax_Util.type_u ()
                                  in
                               FStar_All.pipe_right uu____1037
                                 (fun uu____1050  ->
                                    match uu____1050 with
                                    | (t,u1) ->
                                        let uu____1057 =
                                          let uu____1060 =
                                            FStar_TypeChecker_Env.new_u_univ
                                              ()
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____1060
                                           in
                                        FStar_Syntax_Syntax.mk_Total' t
                                          uu____1057)
                                in
                             FStar_Syntax_Util.arrow bs uu____1034  in
                           let g = FStar_TypeChecker_Rel.teq env ty k  in
                           (FStar_TypeChecker_Rel.force_trivial_guard env g;
                            (let uu____1063 =
                               let uu____1076 =
                                 let uu____1079 =
                                   FStar_All.pipe_right k
                                     (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                        env)
                                    in
                                 FStar_Syntax_Subst.close_univ_vars us
                                   uu____1079
                                  in
                               (repr_us, repr_t, uu____1076)  in
                             (uu____1063, underlying_effect_lid))))))
             in
          match uu____723 with
          | (repr,underlying_effect_lid) ->
              (log_combinator "repr" repr;
               (let fresh_repr r env u a_tm =
                  let signature_ts =
                    let uu____1152 = signature  in
                    match uu____1152 with | (us,t,uu____1167) -> (us, t)  in
                  let repr_ts =
                    let uu____1185 = repr  in
                    match uu____1185 with | (us,t,uu____1200) -> (us, t)  in
                  FStar_TypeChecker_Util.fresh_effect_repr env r
                    ed.FStar_Syntax_Syntax.mname signature_ts
                    (FStar_Pervasives_Native.Some repr_ts) u a_tm
                   in
                let not_an_arrow_error comb n1 t r =
                  let uu____1250 =
                    let uu____1256 =
                      let uu____1258 =
                        FStar_Ident.string_of_lid
                          ed.FStar_Syntax_Syntax.mname
                         in
                      let uu____1260 = FStar_Util.string_of_int n1  in
                      let uu____1262 = FStar_Syntax_Print.tag_of_term t  in
                      let uu____1264 = FStar_Syntax_Print.term_to_string t
                         in
                      FStar_Util.format5
                        "Type of %s:%s is not an arrow with >= %s binders (%s::%s)"
                        uu____1258 comb uu____1260 uu____1262 uu____1264
                       in
                    (FStar_Errors.Fatal_UnexpectedEffect, uu____1256)  in
                  FStar_Errors.raise_error uu____1250 r  in
                let return_repr =
                  let return_repr_ts =
                    let uu____1294 =
                      FStar_All.pipe_right ed
                        FStar_Syntax_Util.get_return_repr
                       in
                    FStar_All.pipe_right uu____1294 FStar_Util.must  in
                  let r =
                    (FStar_Pervasives_Native.snd return_repr_ts).FStar_Syntax_Syntax.pos
                     in
                  let uu____1322 =
                    check_and_gen1 "return_repr" Prims.int_one return_repr_ts
                     in
                  match uu____1322 with
                  | (ret_us,ret_t,ret_ty) ->
                      let uu____1346 =
                        FStar_Syntax_Subst.open_univ_vars ret_us ret_ty  in
                      (match uu____1346 with
                       | (us,ty) ->
                           let env =
                             FStar_TypeChecker_Env.push_univ_vars env0 us  in
                           (check_no_subtyping_for_layered_combinator env ty
                              FStar_Pervasives_Native.None;
                            (let uu____1367 = fresh_a_and_u_a "a"  in
                             match uu____1367 with
                             | (a,u_a) ->
                                 let x_a = fresh_x_a "x" a  in
                                 let rest_bs =
                                   let uu____1398 =
                                     let uu____1399 =
                                       FStar_Syntax_Subst.compress ty  in
                                     uu____1399.FStar_Syntax_Syntax.n  in
                                   match uu____1398 with
                                   | FStar_Syntax_Syntax.Tm_arrow
                                       (bs,uu____1411) when
                                       (FStar_List.length bs) >=
                                         (Prims.of_int (2))
                                       ->
                                       let uu____1439 =
                                         FStar_Syntax_Subst.open_binders bs
                                          in
                                       (match uu____1439 with
                                        | (a',uu____1449)::(x',uu____1451)::bs1
                                            ->
                                            let uu____1481 =
                                              let uu____1482 =
                                                let uu____1487 =
                                                  let uu____1490 =
                                                    let uu____1491 =
                                                      let uu____1498 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          (FStar_Pervasives_Native.fst
                                                             a)
                                                         in
                                                      (a', uu____1498)  in
                                                    FStar_Syntax_Syntax.NT
                                                      uu____1491
                                                     in
                                                  [uu____1490]  in
                                                FStar_Syntax_Subst.subst_binders
                                                  uu____1487
                                                 in
                                              FStar_All.pipe_right bs1
                                                uu____1482
                                               in
                                            let uu____1505 =
                                              let uu____1518 =
                                                let uu____1521 =
                                                  let uu____1522 =
                                                    let uu____1529 =
                                                      FStar_Syntax_Syntax.bv_to_name
                                                        (FStar_Pervasives_Native.fst
                                                           x_a)
                                                       in
                                                    (x', uu____1529)  in
                                                  FStar_Syntax_Syntax.NT
                                                    uu____1522
                                                   in
                                                [uu____1521]  in
                                              FStar_Syntax_Subst.subst_binders
                                                uu____1518
                                               in
                                            FStar_All.pipe_right uu____1481
                                              uu____1505)
                                   | uu____1544 ->
                                       not_an_arrow_error "return"
                                         (Prims.of_int (2)) ty r
                                    in
                                 let bs = a :: x_a :: rest_bs  in
                                 let uu____1568 =
                                   let uu____1573 =
                                     FStar_TypeChecker_Env.push_binders env
                                       bs
                                      in
                                   let uu____1574 =
                                     FStar_All.pipe_right
                                       (FStar_Pervasives_Native.fst a)
                                       FStar_Syntax_Syntax.bv_to_name
                                      in
                                   fresh_repr r uu____1573 u_a uu____1574  in
                                 (match uu____1568 with
                                  | (repr1,g) ->
                                      let k =
                                        let uu____1594 =
                                          FStar_Syntax_Syntax.mk_Total' repr1
                                            (FStar_Pervasives_Native.Some u_a)
                                           in
                                        FStar_Syntax_Util.arrow bs uu____1594
                                         in
                                      let g_eq =
                                        FStar_TypeChecker_Rel.teq env ty k
                                         in
                                      ((let uu____1599 =
                                          FStar_TypeChecker_Env.conj_guard g
                                            g_eq
                                           in
                                        FStar_TypeChecker_Rel.force_trivial_guard
                                          env uu____1599);
                                       (let uu____1600 =
                                          let uu____1603 =
                                            FStar_All.pipe_right k
                                              (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                 env)
                                             in
                                          FStar_All.pipe_right uu____1603
                                            (FStar_Syntax_Subst.close_univ_vars
                                               us)
                                           in
                                        (ret_us, ret_t, uu____1600)))))))
                   in
                log_combinator "return_repr" return_repr;
                (let bind_repr =
                   let bind_repr_ts =
                     let uu____1632 =
                       FStar_All.pipe_right ed
                         FStar_Syntax_Util.get_bind_repr
                        in
                     FStar_All.pipe_right uu____1632 FStar_Util.must  in
                   let r =
                     (FStar_Pervasives_Native.snd bind_repr_ts).FStar_Syntax_Syntax.pos
                      in
                   let uu____1644 =
                     check_and_gen1 "bind_repr" (Prims.of_int (2))
                       bind_repr_ts
                      in
                   match uu____1644 with
                   | (bind_us,bind_t,bind_ty) ->
                       let uu____1668 =
                         FStar_Syntax_Subst.open_univ_vars bind_us bind_ty
                          in
                       (match uu____1668 with
                        | (us,ty) ->
                            let env =
                              FStar_TypeChecker_Env.push_univ_vars env0 us
                               in
                            (check_no_subtyping_for_layered_combinator env ty
                               FStar_Pervasives_Native.None;
                             (let uu____1689 = fresh_a_and_u_a "a"  in
                              match uu____1689 with
                              | (a,u_a) ->
                                  let uu____1709 = fresh_a_and_u_a "b"  in
                                  (match uu____1709 with
                                   | (b,u_b) ->
                                       let rest_bs =
                                         let uu____1738 =
                                           let uu____1739 =
                                             FStar_Syntax_Subst.compress ty
                                              in
                                           uu____1739.FStar_Syntax_Syntax.n
                                            in
                                         match uu____1738 with
                                         | FStar_Syntax_Syntax.Tm_arrow
                                             (bs,uu____1751) when
                                             (FStar_List.length bs) >=
                                               (Prims.of_int (4))
                                             ->
                                             let uu____1779 =
                                               FStar_Syntax_Subst.open_binders
                                                 bs
                                                in
                                             (match uu____1779 with
                                              | (a',uu____1789)::(b',uu____1791)::bs1
                                                  ->
                                                  let uu____1821 =
                                                    let uu____1822 =
                                                      FStar_All.pipe_right
                                                        bs1
                                                        (FStar_List.splitAt
                                                           ((FStar_List.length
                                                               bs1)
                                                              -
                                                              (Prims.of_int (2))))
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____1822
                                                      FStar_Pervasives_Native.fst
                                                     in
                                                  let uu____1920 =
                                                    let uu____1933 =
                                                      let uu____1936 =
                                                        let uu____1937 =
                                                          let uu____1944 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              (FStar_Pervasives_Native.fst
                                                                 a)
                                                             in
                                                          (a', uu____1944)
                                                           in
                                                        FStar_Syntax_Syntax.NT
                                                          uu____1937
                                                         in
                                                      let uu____1951 =
                                                        let uu____1954 =
                                                          let uu____1955 =
                                                            let uu____1962 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                (FStar_Pervasives_Native.fst
                                                                   b)
                                                               in
                                                            (b', uu____1962)
                                                             in
                                                          FStar_Syntax_Syntax.NT
                                                            uu____1955
                                                           in
                                                        [uu____1954]  in
                                                      uu____1936 ::
                                                        uu____1951
                                                       in
                                                    FStar_Syntax_Subst.subst_binders
                                                      uu____1933
                                                     in
                                                  FStar_All.pipe_right
                                                    uu____1821 uu____1920)
                                         | uu____1977 ->
                                             not_an_arrow_error "bind"
                                               (Prims.of_int (4)) ty r
                                          in
                                       let bs = a :: b :: rest_bs  in
                                       let uu____2001 =
                                         let uu____2012 =
                                           let uu____2017 =
                                             FStar_TypeChecker_Env.push_binders
                                               env bs
                                              in
                                           let uu____2018 =
                                             FStar_All.pipe_right
                                               (FStar_Pervasives_Native.fst a)
                                               FStar_Syntax_Syntax.bv_to_name
                                              in
                                           fresh_repr r uu____2017 u_a
                                             uu____2018
                                            in
                                         match uu____2012 with
                                         | (repr1,g) ->
                                             let uu____2033 =
                                               let uu____2040 =
                                                 FStar_Syntax_Syntax.gen_bv
                                                   "f"
                                                   FStar_Pervasives_Native.None
                                                   repr1
                                                  in
                                               FStar_All.pipe_right
                                                 uu____2040
                                                 FStar_Syntax_Syntax.mk_binder
                                                in
                                             (uu____2033, g)
                                          in
                                       (match uu____2001 with
                                        | (f,guard_f) ->
                                            let uu____2080 =
                                              let x_a = fresh_x_a "x" a  in
                                              let uu____2093 =
                                                let uu____2098 =
                                                  FStar_TypeChecker_Env.push_binders
                                                    env
                                                    (FStar_List.append bs
                                                       [x_a])
                                                   in
                                                let uu____2117 =
                                                  FStar_All.pipe_right
                                                    (FStar_Pervasives_Native.fst
                                                       b)
                                                    FStar_Syntax_Syntax.bv_to_name
                                                   in
                                                fresh_repr r uu____2098 u_b
                                                  uu____2117
                                                 in
                                              match uu____2093 with
                                              | (repr1,g) ->
                                                  let uu____2132 =
                                                    let uu____2139 =
                                                      let uu____2140 =
                                                        let uu____2141 =
                                                          let uu____2144 =
                                                            let uu____2147 =
                                                              FStar_TypeChecker_Env.new_u_univ
                                                                ()
                                                               in
                                                            FStar_Pervasives_Native.Some
                                                              uu____2147
                                                             in
                                                          FStar_Syntax_Syntax.mk_Total'
                                                            repr1 uu____2144
                                                           in
                                                        FStar_Syntax_Util.arrow
                                                          [x_a] uu____2141
                                                         in
                                                      FStar_Syntax_Syntax.gen_bv
                                                        "g"
                                                        FStar_Pervasives_Native.None
                                                        uu____2140
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____2139
                                                      FStar_Syntax_Syntax.mk_binder
                                                     in
                                                  (uu____2132, g)
                                               in
                                            (match uu____2080 with
                                             | (g,guard_g) ->
                                                 let uu____2199 =
                                                   let uu____2204 =
                                                     FStar_TypeChecker_Env.push_binders
                                                       env bs
                                                      in
                                                   let uu____2205 =
                                                     FStar_All.pipe_right
                                                       (FStar_Pervasives_Native.fst
                                                          b)
                                                       FStar_Syntax_Syntax.bv_to_name
                                                      in
                                                   fresh_repr r uu____2204
                                                     u_b uu____2205
                                                    in
                                                 (match uu____2199 with
                                                  | (repr1,guard_repr) ->
                                                      let uu____2222 =
                                                        let uu____2227 =
                                                          FStar_TypeChecker_Env.push_binders
                                                            env bs
                                                           in
                                                        let uu____2228 =
                                                          let uu____2230 =
                                                            FStar_Ident.string_of_lid
                                                              ed.FStar_Syntax_Syntax.mname
                                                             in
                                                          FStar_Util.format1
                                                            "implicit for pure_wp in checking bind for %s"
                                                            uu____2230
                                                           in
                                                        pure_wp_uvar
                                                          uu____2227 repr1
                                                          uu____2228 r
                                                         in
                                                      (match uu____2222 with
                                                       | (pure_wp_uvar1,g_pure_wp_uvar)
                                                           ->
                                                           let k =
                                                             let uu____2250 =
                                                               let uu____2253
                                                                 =
                                                                 let uu____2254
                                                                   =
                                                                   let uu____2255
                                                                    =
                                                                    FStar_TypeChecker_Env.new_u_univ
                                                                    ()  in
                                                                   [uu____2255]
                                                                    in
                                                                 let uu____2256
                                                                   =
                                                                   let uu____2267
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    pure_wp_uvar1
                                                                    FStar_Syntax_Syntax.as_arg
                                                                     in
                                                                   [uu____2267]
                                                                    in
                                                                 {
                                                                   FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____2254;
                                                                   FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    FStar_Parser_Const.effect_PURE_lid;
                                                                   FStar_Syntax_Syntax.result_typ
                                                                    = repr1;
                                                                   FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____2256;
                                                                   FStar_Syntax_Syntax.flags
                                                                    = []
                                                                 }  in
                                                               FStar_Syntax_Syntax.mk_Comp
                                                                 uu____2253
                                                                in
                                                             FStar_Syntax_Util.arrow
                                                               (FStar_List.append
                                                                  bs 
                                                                  [f; g])
                                                               uu____2250
                                                              in
                                                           let guard_eq =
                                                             FStar_TypeChecker_Rel.teq
                                                               env ty k
                                                              in
                                                           (FStar_List.iter
                                                              (FStar_TypeChecker_Rel.force_trivial_guard
                                                                 env)
                                                              [guard_f;
                                                              guard_g;
                                                              guard_repr;
                                                              g_pure_wp_uvar;
                                                              guard_eq];
                                                            (let uu____2326 =
                                                               let uu____2329
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   k
                                                                   (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                                    env)
                                                                  in
                                                               FStar_All.pipe_right
                                                                 uu____2329
                                                                 (FStar_Syntax_Subst.close_univ_vars
                                                                    bind_us)
                                                                in
                                                             (bind_us,
                                                               bind_t,
                                                               uu____2326)))))))))))
                    in
                 log_combinator "bind_repr" bind_repr;
                 (let stronger_repr =
                    let stronger_repr =
                      let uu____2358 =
                        FStar_All.pipe_right ed
                          FStar_Syntax_Util.get_stronger_repr
                         in
                      FStar_All.pipe_right uu____2358 FStar_Util.must  in
                    let r =
                      (FStar_Pervasives_Native.snd stronger_repr).FStar_Syntax_Syntax.pos
                       in
                    let uu____2386 =
                      check_and_gen1 "stronger_repr" Prims.int_one
                        stronger_repr
                       in
                    match uu____2386 with
                    | (stronger_us,stronger_t,stronger_ty) ->
                        ((let uu____2411 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env0)
                              (FStar_Options.Other "LayeredEffects")
                             in
                          if uu____2411
                          then
                            let uu____2416 =
                              FStar_Syntax_Print.tscheme_to_string
                                (stronger_us, stronger_t)
                               in
                            let uu____2422 =
                              FStar_Syntax_Print.tscheme_to_string
                                (stronger_us, stronger_ty)
                               in
                            FStar_Util.print2
                              "stronger combinator typechecked with term: %s and type: %s\n"
                              uu____2416 uu____2422
                          else ());
                         (let uu____2431 =
                            FStar_Syntax_Subst.open_univ_vars stronger_us
                              stronger_ty
                             in
                          match uu____2431 with
                          | (us,ty) ->
                              let env =
                                FStar_TypeChecker_Env.push_univ_vars env0 us
                                 in
                              (check_no_subtyping_for_layered_combinator env
                                 ty FStar_Pervasives_Native.None;
                               (let uu____2452 = fresh_a_and_u_a "a"  in
                                match uu____2452 with
                                | (a,u) ->
                                    let rest_bs =
                                      let uu____2481 =
                                        let uu____2482 =
                                          FStar_Syntax_Subst.compress ty  in
                                        uu____2482.FStar_Syntax_Syntax.n  in
                                      match uu____2481 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (bs,uu____2494) when
                                          (FStar_List.length bs) >=
                                            (Prims.of_int (2))
                                          ->
                                          let uu____2522 =
                                            FStar_Syntax_Subst.open_binders
                                              bs
                                             in
                                          (match uu____2522 with
                                           | (a',uu____2532)::bs1 ->
                                               let uu____2552 =
                                                 let uu____2553 =
                                                   FStar_All.pipe_right bs1
                                                     (FStar_List.splitAt
                                                        ((FStar_List.length
                                                            bs1)
                                                           - Prims.int_one))
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____2553
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               let uu____2619 =
                                                 let uu____2632 =
                                                   let uu____2635 =
                                                     let uu____2636 =
                                                       let uu____2643 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           (FStar_Pervasives_Native.fst
                                                              a)
                                                          in
                                                       (a', uu____2643)  in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____2636
                                                      in
                                                   [uu____2635]  in
                                                 FStar_Syntax_Subst.subst_binders
                                                   uu____2632
                                                  in
                                               FStar_All.pipe_right
                                                 uu____2552 uu____2619)
                                      | uu____2658 ->
                                          not_an_arrow_error "stronger"
                                            (Prims.of_int (2)) ty r
                                       in
                                    let bs = a :: rest_bs  in
                                    let uu____2676 =
                                      let uu____2687 =
                                        let uu____2692 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs
                                           in
                                        let uu____2693 =
                                          FStar_All.pipe_right
                                            (FStar_Pervasives_Native.fst a)
                                            FStar_Syntax_Syntax.bv_to_name
                                           in
                                        fresh_repr r uu____2692 u uu____2693
                                         in
                                      match uu____2687 with
                                      | (repr1,g) ->
                                          let uu____2708 =
                                            let uu____2715 =
                                              FStar_Syntax_Syntax.gen_bv "f"
                                                FStar_Pervasives_Native.None
                                                repr1
                                               in
                                            FStar_All.pipe_right uu____2715
                                              FStar_Syntax_Syntax.mk_binder
                                             in
                                          (uu____2708, g)
                                       in
                                    (match uu____2676 with
                                     | (f,guard_f) ->
                                         let uu____2755 =
                                           let uu____2760 =
                                             FStar_TypeChecker_Env.push_binders
                                               env bs
                                              in
                                           let uu____2761 =
                                             FStar_All.pipe_right
                                               (FStar_Pervasives_Native.fst a)
                                               FStar_Syntax_Syntax.bv_to_name
                                              in
                                           fresh_repr r uu____2760 u
                                             uu____2761
                                            in
                                         (match uu____2755 with
                                          | (ret_t,guard_ret_t) ->
                                              let uu____2778 =
                                                let uu____2783 =
                                                  FStar_TypeChecker_Env.push_binders
                                                    env bs
                                                   in
                                                let uu____2784 =
                                                  let uu____2786 =
                                                    FStar_Ident.string_of_lid
                                                      ed.FStar_Syntax_Syntax.mname
                                                     in
                                                  FStar_Util.format1
                                                    "implicit for pure_wp in checking stronger for %s"
                                                    uu____2786
                                                   in
                                                pure_wp_uvar uu____2783 ret_t
                                                  uu____2784 r
                                                 in
                                              (match uu____2778 with
                                               | (pure_wp_uvar1,guard_wp) ->
                                                   let c =
                                                     let uu____2804 =
                                                       let uu____2805 =
                                                         let uu____2806 =
                                                           FStar_TypeChecker_Env.new_u_univ
                                                             ()
                                                            in
                                                         [uu____2806]  in
                                                       let uu____2807 =
                                                         let uu____2818 =
                                                           FStar_All.pipe_right
                                                             pure_wp_uvar1
                                                             FStar_Syntax_Syntax.as_arg
                                                            in
                                                         [uu____2818]  in
                                                       {
                                                         FStar_Syntax_Syntax.comp_univs
                                                           = uu____2805;
                                                         FStar_Syntax_Syntax.effect_name
                                                           =
                                                           FStar_Parser_Const.effect_PURE_lid;
                                                         FStar_Syntax_Syntax.result_typ
                                                           = ret_t;
                                                         FStar_Syntax_Syntax.effect_args
                                                           = uu____2807;
                                                         FStar_Syntax_Syntax.flags
                                                           = []
                                                       }  in
                                                     FStar_Syntax_Syntax.mk_Comp
                                                       uu____2804
                                                      in
                                                   let k =
                                                     FStar_Syntax_Util.arrow
                                                       (FStar_List.append bs
                                                          [f]) c
                                                      in
                                                   ((let uu____2873 =
                                                       FStar_All.pipe_left
                                                         (FStar_TypeChecker_Env.debug
                                                            env)
                                                         (FStar_Options.Other
                                                            "LayeredEffects")
                                                        in
                                                     if uu____2873
                                                     then
                                                       let uu____2878 =
                                                         FStar_Syntax_Print.term_to_string
                                                           k
                                                          in
                                                       FStar_Util.print1
                                                         "Expected type before unification: %s\n"
                                                         uu____2878
                                                     else ());
                                                    (let guard_eq =
                                                       FStar_TypeChecker_Rel.teq
                                                         env ty k
                                                        in
                                                     FStar_List.iter
                                                       (FStar_TypeChecker_Rel.force_trivial_guard
                                                          env)
                                                       [guard_f;
                                                       guard_ret_t;
                                                       guard_wp;
                                                       guard_eq];
                                                     (let uu____2885 =
                                                        let uu____2888 =
                                                          let uu____2889 =
                                                            FStar_All.pipe_right
                                                              k
                                                              (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                                 env)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____2889
                                                            (FStar_TypeChecker_Normalize.normalize
                                                               [FStar_TypeChecker_Env.Beta;
                                                               FStar_TypeChecker_Env.Eager_unfolding]
                                                               env)
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____2888
                                                          (FStar_Syntax_Subst.close_univ_vars
                                                             stronger_us)
                                                         in
                                                      (stronger_us,
                                                        stronger_t,
                                                        uu____2885)))))))))))
                     in
                  log_combinator "stronger_repr" stronger_repr;
                  (let if_then_else1 =
                     let if_then_else_ts =
                       let uu____2920 =
                         FStar_All.pipe_right ed
                           FStar_Syntax_Util.get_layered_if_then_else_combinator
                          in
                       FStar_All.pipe_right uu____2920 FStar_Util.must  in
                     let r =
                       (FStar_Pervasives_Native.snd if_then_else_ts).FStar_Syntax_Syntax.pos
                        in
                     let uu____2936 =
                       check_and_gen1 "if_then_else" Prims.int_one
                         if_then_else_ts
                        in
                     match uu____2936 with
                     | (if_then_else_us,if_then_else_t,if_then_else_ty) ->
                         let uu____2960 =
                           FStar_Syntax_Subst.open_univ_vars if_then_else_us
                             if_then_else_t
                            in
                         (match uu____2960 with
                          | (us,t) ->
                              let uu____2979 =
                                FStar_Syntax_Subst.open_univ_vars
                                  if_then_else_us if_then_else_ty
                                 in
                              (match uu____2979 with
                               | (uu____2996,ty) ->
                                   let env =
                                     FStar_TypeChecker_Env.push_univ_vars
                                       env0 us
                                      in
                                   (check_no_subtyping_for_layered_combinator
                                      env t (FStar_Pervasives_Native.Some ty);
                                    (let uu____3000 = fresh_a_and_u_a "a"  in
                                     match uu____3000 with
                                     | (a,u_a) ->
                                         let rest_bs =
                                           let uu____3029 =
                                             let uu____3030 =
                                               FStar_Syntax_Subst.compress ty
                                                in
                                             uu____3030.FStar_Syntax_Syntax.n
                                              in
                                           match uu____3029 with
                                           | FStar_Syntax_Syntax.Tm_arrow
                                               (bs,uu____3042) when
                                               (FStar_List.length bs) >=
                                                 (Prims.of_int (4))
                                               ->
                                               let uu____3070 =
                                                 FStar_Syntax_Subst.open_binders
                                                   bs
                                                  in
                                               (match uu____3070 with
                                                | (a',uu____3080)::bs1 ->
                                                    let uu____3100 =
                                                      let uu____3101 =
                                                        FStar_All.pipe_right
                                                          bs1
                                                          (FStar_List.splitAt
                                                             ((FStar_List.length
                                                                 bs1)
                                                                -
                                                                (Prims.of_int (3))))
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____3101
                                                        FStar_Pervasives_Native.fst
                                                       in
                                                    let uu____3199 =
                                                      let uu____3212 =
                                                        let uu____3215 =
                                                          let uu____3216 =
                                                            let uu____3223 =
                                                              let uu____3226
                                                                =
                                                                FStar_All.pipe_right
                                                                  a
                                                                  FStar_Pervasives_Native.fst
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____3226
                                                                FStar_Syntax_Syntax.bv_to_name
                                                               in
                                                            (a', uu____3223)
                                                             in
                                                          FStar_Syntax_Syntax.NT
                                                            uu____3216
                                                           in
                                                        [uu____3215]  in
                                                      FStar_Syntax_Subst.subst_binders
                                                        uu____3212
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____3100 uu____3199)
                                           | uu____3247 ->
                                               not_an_arrow_error
                                                 "if_then_else"
                                                 (Prims.of_int (4)) ty r
                                            in
                                         let bs = a :: rest_bs  in
                                         let uu____3265 =
                                           let uu____3276 =
                                             let uu____3281 =
                                               FStar_TypeChecker_Env.push_binders
                                                 env bs
                                                in
                                             let uu____3282 =
                                               let uu____3283 =
                                                 FStar_All.pipe_right a
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               FStar_All.pipe_right
                                                 uu____3283
                                                 FStar_Syntax_Syntax.bv_to_name
                                                in
                                             fresh_repr r uu____3281 u_a
                                               uu____3282
                                              in
                                           match uu____3276 with
                                           | (repr1,g) ->
                                               let uu____3304 =
                                                 let uu____3311 =
                                                   FStar_Syntax_Syntax.gen_bv
                                                     "f"
                                                     FStar_Pervasives_Native.None
                                                     repr1
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____3311
                                                   FStar_Syntax_Syntax.mk_binder
                                                  in
                                               (uu____3304, g)
                                            in
                                         (match uu____3265 with
                                          | (f_bs,guard_f) ->
                                              let uu____3351 =
                                                let uu____3362 =
                                                  let uu____3367 =
                                                    FStar_TypeChecker_Env.push_binders
                                                      env bs
                                                     in
                                                  let uu____3368 =
                                                    let uu____3369 =
                                                      FStar_All.pipe_right a
                                                        FStar_Pervasives_Native.fst
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____3369
                                                      FStar_Syntax_Syntax.bv_to_name
                                                     in
                                                  fresh_repr r uu____3367 u_a
                                                    uu____3368
                                                   in
                                                match uu____3362 with
                                                | (repr1,g) ->
                                                    let uu____3390 =
                                                      let uu____3397 =
                                                        FStar_Syntax_Syntax.gen_bv
                                                          "g"
                                                          FStar_Pervasives_Native.None
                                                          repr1
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____3397
                                                        FStar_Syntax_Syntax.mk_binder
                                                       in
                                                    (uu____3390, g)
                                                 in
                                              (match uu____3351 with
                                               | (g_bs,guard_g) ->
                                                   let p_b =
                                                     let uu____3444 =
                                                       FStar_Syntax_Syntax.gen_bv
                                                         "p"
                                                         FStar_Pervasives_Native.None
                                                         FStar_Syntax_Util.ktype0
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____3444
                                                       FStar_Syntax_Syntax.mk_binder
                                                      in
                                                   let uu____3452 =
                                                     let uu____3457 =
                                                       FStar_TypeChecker_Env.push_binders
                                                         env
                                                         (FStar_List.append
                                                            bs [p_b])
                                                        in
                                                     let uu____3476 =
                                                       let uu____3477 =
                                                         FStar_All.pipe_right
                                                           a
                                                           FStar_Pervasives_Native.fst
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____3477
                                                         FStar_Syntax_Syntax.bv_to_name
                                                        in
                                                     fresh_repr r uu____3457
                                                       u_a uu____3476
                                                      in
                                                   (match uu____3452 with
                                                    | (t_body,guard_body) ->
                                                        let k =
                                                          FStar_Syntax_Util.abs
                                                            (FStar_List.append
                                                               bs
                                                               [f_bs;
                                                               g_bs;
                                                               p_b]) t_body
                                                            FStar_Pervasives_Native.None
                                                           in
                                                        let guard_eq =
                                                          FStar_TypeChecker_Rel.teq
                                                            env t k
                                                           in
                                                        (FStar_All.pipe_right
                                                           [guard_f;
                                                           guard_g;
                                                           guard_body;
                                                           guard_eq]
                                                           (FStar_List.iter
                                                              (FStar_TypeChecker_Rel.force_trivial_guard
                                                                 env));
                                                         (let uu____3537 =
                                                            let uu____3540 =
                                                              FStar_All.pipe_right
                                                                k
                                                                (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                                   env)
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____3540
                                                              (FStar_Syntax_Subst.close_univ_vars
                                                                 if_then_else_us)
                                                             in
                                                          (if_then_else_us,
                                                            uu____3537,
                                                            if_then_else_ty))))))))))
                      in
                   log_combinator "if_then_else" if_then_else1;
                   (let r =
                      let uu____3553 =
                        let uu____3556 =
                          let uu____3565 =
                            FStar_All.pipe_right ed
                              FStar_Syntax_Util.get_layered_if_then_else_combinator
                             in
                          FStar_All.pipe_right uu____3565 FStar_Util.must  in
                        FStar_All.pipe_right uu____3556
                          FStar_Pervasives_Native.snd
                         in
                      uu____3553.FStar_Syntax_Syntax.pos  in
                    let uu____3594 = if_then_else1  in
                    match uu____3594 with
                    | (ite_us,ite_t,uu____3609) ->
                        let uu____3622 =
                          FStar_Syntax_Subst.open_univ_vars ite_us ite_t  in
                        (match uu____3622 with
                         | (us,ite_t1) ->
                             let uu____3629 =
                               let uu____3640 =
                                 let uu____3641 =
                                   FStar_Syntax_Subst.compress ite_t1  in
                                 uu____3641.FStar_Syntax_Syntax.n  in
                               match uu____3640 with
                               | FStar_Syntax_Syntax.Tm_abs
                                   (bs,uu____3655,uu____3656) ->
                                   let bs1 =
                                     FStar_Syntax_Subst.open_binders bs  in
                                   let uu____3682 =
                                     let uu____3689 =
                                       let uu____3692 =
                                         let uu____3695 =
                                           let uu____3704 =
                                             FStar_All.pipe_right bs1
                                               (FStar_List.splitAt
                                                  ((FStar_List.length bs1) -
                                                     (Prims.of_int (3))))
                                              in
                                           FStar_All.pipe_right uu____3704
                                             FStar_Pervasives_Native.snd
                                            in
                                         FStar_All.pipe_right uu____3695
                                           (FStar_List.map
                                              FStar_Pervasives_Native.fst)
                                          in
                                       FStar_All.pipe_right uu____3692
                                         (FStar_List.map
                                            FStar_Syntax_Syntax.bv_to_name)
                                        in
                                     FStar_All.pipe_right uu____3689
                                       (fun l  ->
                                          let uu____3848 = l  in
                                          match uu____3848 with
                                          | f::g::p::[] -> (f, g, p))
                                      in
                                   (match uu____3682 with
                                    | (f,g,p) ->
                                        let uu____3873 =
                                          let uu____3874 =
                                            FStar_TypeChecker_Env.push_univ_vars
                                              env0 us
                                             in
                                          FStar_TypeChecker_Env.push_binders
                                            uu____3874 bs1
                                           in
                                        let uu____3875 =
                                          let uu____3876 =
                                            let uu____3881 =
                                              let uu____3882 =
                                                let uu____3885 =
                                                  FStar_All.pipe_right bs1
                                                    (FStar_List.map
                                                       FStar_Pervasives_Native.fst)
                                                   in
                                                FStar_All.pipe_right
                                                  uu____3885
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.bv_to_name)
                                                 in
                                              FStar_All.pipe_right uu____3882
                                                (FStar_List.map
                                                   FStar_Syntax_Syntax.as_arg)
                                               in
                                            FStar_Syntax_Syntax.mk_Tm_app
                                              ite_t1 uu____3881
                                             in
                                          uu____3876
                                            FStar_Pervasives_Native.None r
                                           in
                                        (uu____3873, uu____3875, f, g, p))
                               | uu____3912 ->
                                   failwith
                                     "Impossible! ite_t must have been an abstraction with at least 3 binders"
                                in
                             (match uu____3629 with
                              | (env,ite_t_applied,f_t,g_t,p_t) ->
                                  let uu____3929 =
                                    let uu____3938 = stronger_repr  in
                                    match uu____3938 with
                                    | (uu____3959,subcomp_t,subcomp_ty) ->
                                        let uu____3974 =
                                          FStar_Syntax_Subst.open_univ_vars
                                            us subcomp_t
                                           in
                                        (match uu____3974 with
                                         | (uu____3987,subcomp_t1) ->
                                             let bs_except_last =
                                               let uu____3998 =
                                                 FStar_Syntax_Subst.open_univ_vars
                                                   us subcomp_ty
                                                  in
                                               match uu____3998 with
                                               | (uu____4011,subcomp_ty1) ->
                                                   let uu____4013 =
                                                     let uu____4014 =
                                                       FStar_Syntax_Subst.compress
                                                         subcomp_ty1
                                                        in
                                                     uu____4014.FStar_Syntax_Syntax.n
                                                      in
                                                   (match uu____4013 with
                                                    | FStar_Syntax_Syntax.Tm_arrow
                                                        (bs,uu____4026) ->
                                                        let uu____4047 =
                                                          FStar_All.pipe_right
                                                            bs
                                                            (FStar_List.splitAt
                                                               ((FStar_List.length
                                                                   bs)
                                                                  -
                                                                  Prims.int_one))
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____4047
                                                          FStar_Pervasives_Native.fst
                                                    | uu____4153 ->
                                                        failwith
                                                          "Impossible! subcomp_ty must have been an arrow with at lease 1 binder")
                                                in
                                             let aux t =
                                               let uu____4171 =
                                                 let uu____4176 =
                                                   let uu____4177 =
                                                     let uu____4180 =
                                                       FStar_All.pipe_right
                                                         bs_except_last
                                                         (FStar_List.map
                                                            (fun uu____4200 
                                                               ->
                                                               FStar_Syntax_Syntax.tun))
                                                        in
                                                     FStar_List.append
                                                       uu____4180 [t]
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____4177
                                                     (FStar_List.map
                                                        FStar_Syntax_Syntax.as_arg)
                                                    in
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   subcomp_t1 uu____4176
                                                  in
                                               uu____4171
                                                 FStar_Pervasives_Native.None
                                                 r
                                                in
                                             let uu____4209 = aux f_t  in
                                             let uu____4212 = aux g_t  in
                                             (uu____4209, uu____4212))
                                     in
                                  (match uu____3929 with
                                   | (subcomp_f,subcomp_g) ->
                                       let uu____4229 =
                                         let aux t =
                                           let uu____4246 =
                                             let uu____4253 =
                                               let uu____4254 =
                                                 let uu____4281 =
                                                   let uu____4298 =
                                                     let uu____4307 =
                                                       FStar_Syntax_Syntax.mk_Total
                                                         ite_t_applied
                                                        in
                                                     FStar_Util.Inr
                                                       uu____4307
                                                      in
                                                   (uu____4298,
                                                     FStar_Pervasives_Native.None)
                                                    in
                                                 (t, uu____4281,
                                                   FStar_Pervasives_Native.None)
                                                  in
                                               FStar_Syntax_Syntax.Tm_ascribed
                                                 uu____4254
                                                in
                                             FStar_Syntax_Syntax.mk
                                               uu____4253
                                              in
                                           uu____4246
                                             FStar_Pervasives_Native.None r
                                            in
                                         let uu____4348 = aux subcomp_f  in
                                         let uu____4349 = aux subcomp_g  in
                                         (uu____4348, uu____4349)  in
                                       (match uu____4229 with
                                        | (tm_subcomp_ascribed_f,tm_subcomp_ascribed_g)
                                            ->
                                            ((let uu____4353 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env)
                                                  (FStar_Options.Other
                                                     "LayeredEffects")
                                                 in
                                              if uu____4353
                                              then
                                                let uu____4358 =
                                                  FStar_Syntax_Print.term_to_string
                                                    tm_subcomp_ascribed_f
                                                   in
                                                let uu____4360 =
                                                  FStar_Syntax_Print.term_to_string
                                                    tm_subcomp_ascribed_g
                                                   in
                                                FStar_Util.print2
                                                  "Checking the soundness of the if_then_else combinators, f: %s, g: %s\n"
                                                  uu____4358 uu____4360
                                              else ());
                                             (let uu____4365 =
                                                FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                  env tm_subcomp_ascribed_f
                                                 in
                                              match uu____4365 with
                                              | (uu____4372,uu____4373,g_f)
                                                  ->
                                                  let g_f1 =
                                                    let uu____4376 =
                                                      FStar_TypeChecker_Env.guard_of_guard_formula
                                                        (FStar_TypeChecker_Common.NonTrivial
                                                           p_t)
                                                       in
                                                    FStar_TypeChecker_Env.imp_guard
                                                      uu____4376 g_f
                                                     in
                                                  (FStar_TypeChecker_Rel.force_trivial_guard
                                                     env g_f1;
                                                   (let uu____4378 =
                                                      FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                        env
                                                        tm_subcomp_ascribed_g
                                                       in
                                                    match uu____4378 with
                                                    | (uu____4385,uu____4386,g_g)
                                                        ->
                                                        let g_g1 =
                                                          let not_p =
                                                            let uu____4392 =
                                                              let uu____4397
                                                                =
                                                                let uu____4398
                                                                  =
                                                                  FStar_Syntax_Syntax.lid_as_fv
                                                                    FStar_Parser_Const.not_lid
                                                                    FStar_Syntax_Syntax.delta_constant
                                                                    FStar_Pervasives_Native.None
                                                                   in
                                                                FStar_All.pipe_right
                                                                  uu____4398
                                                                  FStar_Syntax_Syntax.fv_to_tm
                                                                 in
                                                              let uu____4399
                                                                =
                                                                let uu____4400
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    p_t
                                                                    FStar_Syntax_Syntax.as_arg
                                                                   in
                                                                [uu____4400]
                                                                 in
                                                              FStar_Syntax_Syntax.mk_Tm_app
                                                                uu____4397
                                                                uu____4399
                                                               in
                                                            uu____4392
                                                              FStar_Pervasives_Native.None
                                                              r
                                                             in
                                                          let uu____4433 =
                                                            FStar_TypeChecker_Env.guard_of_guard_formula
                                                              (FStar_TypeChecker_Common.NonTrivial
                                                                 not_p)
                                                             in
                                                          FStar_TypeChecker_Env.imp_guard
                                                            uu____4433 g_g
                                                           in
                                                        FStar_TypeChecker_Rel.force_trivial_guard
                                                          env g_g1)))))))));
                   (let tc_action env act =
                      let env01 = env  in
                      let r =
                        (act.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                         in
                      if
                        (FStar_List.length
                           act.FStar_Syntax_Syntax.action_params)
                          <> Prims.int_zero
                      then
                        (let uu____4457 =
                           let uu____4463 =
                             let uu____4465 =
                               FStar_Ident.string_of_lid
                                 ed.FStar_Syntax_Syntax.mname
                                in
                             let uu____4467 =
                               FStar_Ident.string_of_lid
                                 act.FStar_Syntax_Syntax.action_name
                                in
                             let uu____4469 =
                               FStar_Syntax_Print.binders_to_string "; "
                                 act.FStar_Syntax_Syntax.action_params
                                in
                             FStar_Util.format3
                               "Action %s:%s has non-empty action params (%s)"
                               uu____4465 uu____4467 uu____4469
                              in
                           (FStar_Errors.Fatal_MalformedActionDeclaration,
                             uu____4463)
                            in
                         FStar_Errors.raise_error uu____4457 r)
                      else ();
                      (let uu____4476 =
                         let uu____4481 =
                           FStar_Syntax_Subst.univ_var_opening
                             act.FStar_Syntax_Syntax.action_univs
                            in
                         match uu____4481 with
                         | (usubst,us) ->
                             let uu____4504 =
                               FStar_TypeChecker_Env.push_univ_vars env us
                                in
                             let uu____4505 =
                               let uu___446_4506 = act  in
                               let uu____4507 =
                                 FStar_Syntax_Subst.subst usubst
                                   act.FStar_Syntax_Syntax.action_defn
                                  in
                               let uu____4508 =
                                 FStar_Syntax_Subst.subst usubst
                                   act.FStar_Syntax_Syntax.action_typ
                                  in
                               {
                                 FStar_Syntax_Syntax.action_name =
                                   (uu___446_4506.FStar_Syntax_Syntax.action_name);
                                 FStar_Syntax_Syntax.action_unqualified_name
                                   =
                                   (uu___446_4506.FStar_Syntax_Syntax.action_unqualified_name);
                                 FStar_Syntax_Syntax.action_univs = us;
                                 FStar_Syntax_Syntax.action_params =
                                   (uu___446_4506.FStar_Syntax_Syntax.action_params);
                                 FStar_Syntax_Syntax.action_defn = uu____4507;
                                 FStar_Syntax_Syntax.action_typ = uu____4508
                               }  in
                             (uu____4504, uu____4505)
                          in
                       match uu____4476 with
                       | (env1,act1) ->
                           let act_typ =
                             let uu____4512 =
                               let uu____4513 =
                                 FStar_Syntax_Subst.compress
                                   act1.FStar_Syntax_Syntax.action_typ
                                  in
                               uu____4513.FStar_Syntax_Syntax.n  in
                             match uu____4512 with
                             | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                                 let ct =
                                   FStar_Syntax_Util.comp_to_comp_typ c  in
                                 let uu____4539 =
                                   FStar_Ident.lid_equals
                                     ct.FStar_Syntax_Syntax.effect_name
                                     ed.FStar_Syntax_Syntax.mname
                                    in
                                 if uu____4539
                                 then
                                   let repr_ts =
                                     let uu____4543 = repr  in
                                     match uu____4543 with
                                     | (us,t,uu____4558) -> (us, t)  in
                                   let repr1 =
                                     let uu____4576 =
                                       FStar_TypeChecker_Env.inst_tscheme_with
                                         repr_ts
                                         ct.FStar_Syntax_Syntax.comp_univs
                                        in
                                     FStar_All.pipe_right uu____4576
                                       FStar_Pervasives_Native.snd
                                      in
                                   let repr2 =
                                     let uu____4588 =
                                       let uu____4593 =
                                         let uu____4594 =
                                           FStar_Syntax_Syntax.as_arg
                                             ct.FStar_Syntax_Syntax.result_typ
                                            in
                                         uu____4594 ::
                                           (ct.FStar_Syntax_Syntax.effect_args)
                                          in
                                       FStar_Syntax_Syntax.mk_Tm_app repr1
                                         uu____4593
                                        in
                                     uu____4588 FStar_Pervasives_Native.None
                                       r
                                      in
                                   let c1 =
                                     let uu____4612 =
                                       let uu____4615 =
                                         FStar_TypeChecker_Env.new_u_univ ()
                                          in
                                       FStar_Pervasives_Native.Some
                                         uu____4615
                                        in
                                     FStar_Syntax_Syntax.mk_Total' repr2
                                       uu____4612
                                      in
                                   FStar_Syntax_Util.arrow bs c1
                                 else act1.FStar_Syntax_Syntax.action_typ
                             | uu____4618 ->
                                 act1.FStar_Syntax_Syntax.action_typ
                              in
                           let uu____4619 =
                             FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                               env1 act_typ
                              in
                           (match uu____4619 with
                            | (act_typ1,uu____4627,g_t) ->
                                let uu____4629 =
                                  let uu____4636 =
                                    let uu___471_4637 =
                                      FStar_TypeChecker_Env.set_expected_typ
                                        env1 act_typ1
                                       in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___471_4637.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___471_4637.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___471_4637.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___471_4637.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___471_4637.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___471_4637.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___471_4637.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___471_4637.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___471_4637.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___471_4637.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        false;
                                      FStar_TypeChecker_Env.effects =
                                        (uu___471_4637.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___471_4637.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___471_4637.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___471_4637.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___471_4637.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___471_4637.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.use_eq_strict =
                                        (uu___471_4637.FStar_TypeChecker_Env.use_eq_strict);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___471_4637.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___471_4637.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___471_4637.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___471_4637.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___471_4637.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___471_4637.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___471_4637.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___471_4637.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___471_4637.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___471_4637.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___471_4637.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___471_4637.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___471_4637.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___471_4637.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___471_4637.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___471_4637.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___471_4637.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___471_4637.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.try_solve_implicits_hook
                                        =
                                        (uu___471_4637.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___471_4637.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.mpreprocess =
                                        (uu___471_4637.FStar_TypeChecker_Env.mpreprocess);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___471_4637.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___471_4637.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___471_4637.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___471_4637.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___471_4637.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___471_4637.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___471_4637.FStar_TypeChecker_Env.strict_args_tab);
                                      FStar_TypeChecker_Env.erasable_types_tab
                                        =
                                        (uu___471_4637.FStar_TypeChecker_Env.erasable_types_tab)
                                    }  in
                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                    uu____4636
                                    act1.FStar_Syntax_Syntax.action_defn
                                   in
                                (match uu____4629 with
                                 | (act_defn,uu____4640,g_d) ->
                                     ((let uu____4643 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env1)
                                           (FStar_Options.Other
                                              "LayeredEffects")
                                          in
                                       if uu____4643
                                       then
                                         let uu____4648 =
                                           FStar_Syntax_Print.term_to_string
                                             act_defn
                                            in
                                         let uu____4650 =
                                           FStar_Syntax_Print.term_to_string
                                             act_typ1
                                            in
                                         FStar_Util.print2
                                           "Typechecked action definition: %s and action type: %s\n"
                                           uu____4648 uu____4650
                                       else ());
                                      (let uu____4655 =
                                         let act_typ2 =
                                           FStar_TypeChecker_Normalize.normalize
                                             [FStar_TypeChecker_Env.Beta]
                                             env1 act_typ1
                                            in
                                         let uu____4663 =
                                           let uu____4664 =
                                             FStar_Syntax_Subst.compress
                                               act_typ2
                                              in
                                           uu____4664.FStar_Syntax_Syntax.n
                                            in
                                         match uu____4663 with
                                         | FStar_Syntax_Syntax.Tm_arrow
                                             (bs,uu____4674) ->
                                             let bs1 =
                                               FStar_Syntax_Subst.open_binders
                                                 bs
                                                in
                                             let env2 =
                                               FStar_TypeChecker_Env.push_binders
                                                 env1 bs1
                                                in
                                             let uu____4697 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             (match uu____4697 with
                                              | (t,u) ->
                                                  let reason =
                                                    let uu____4712 =
                                                      FStar_Ident.string_of_lid
                                                        ed.FStar_Syntax_Syntax.mname
                                                       in
                                                    let uu____4714 =
                                                      FStar_Ident.string_of_lid
                                                        act1.FStar_Syntax_Syntax.action_name
                                                       in
                                                    FStar_Util.format2
                                                      "implicit for return type of action %s:%s"
                                                      uu____4712 uu____4714
                                                     in
                                                  let uu____4717 =
                                                    FStar_TypeChecker_Util.new_implicit_var
                                                      reason r env2 t
                                                     in
                                                  (match uu____4717 with
                                                   | (a_tm,uu____4737,g_tm)
                                                       ->
                                                       let uu____4751 =
                                                         fresh_repr r env2 u
                                                           a_tm
                                                          in
                                                       (match uu____4751 with
                                                        | (repr1,g) ->
                                                            let uu____4764 =
                                                              let uu____4767
                                                                =
                                                                let uu____4770
                                                                  =
                                                                  let uu____4773
                                                                    =
                                                                    FStar_TypeChecker_Env.new_u_univ
                                                                    ()  in
                                                                  FStar_All.pipe_right
                                                                    uu____4773
                                                                    (
                                                                    fun _4776
                                                                     ->
                                                                    FStar_Pervasives_Native.Some
                                                                    _4776)
                                                                   in
                                                                FStar_Syntax_Syntax.mk_Total'
                                                                  repr1
                                                                  uu____4770
                                                                 in
                                                              FStar_Syntax_Util.arrow
                                                                bs1
                                                                uu____4767
                                                               in
                                                            let uu____4777 =
                                                              FStar_TypeChecker_Env.conj_guard
                                                                g g_tm
                                                               in
                                                            (uu____4764,
                                                              uu____4777))))
                                         | uu____4780 ->
                                             let uu____4781 =
                                               let uu____4787 =
                                                 let uu____4789 =
                                                   FStar_Ident.string_of_lid
                                                     ed.FStar_Syntax_Syntax.mname
                                                    in
                                                 let uu____4791 =
                                                   FStar_Ident.string_of_lid
                                                     act1.FStar_Syntax_Syntax.action_name
                                                    in
                                                 let uu____4793 =
                                                   FStar_Syntax_Print.term_to_string
                                                     act_typ2
                                                    in
                                                 FStar_Util.format3
                                                   "Unexpected non-function type for action %s:%s (%s)"
                                                   uu____4789 uu____4791
                                                   uu____4793
                                                  in
                                               (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                 uu____4787)
                                                in
                                             FStar_Errors.raise_error
                                               uu____4781 r
                                          in
                                       match uu____4655 with
                                       | (k,g_k) ->
                                           ((let uu____4810 =
                                               FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env1)
                                                 (FStar_Options.Other
                                                    "LayeredEffects")
                                                in
                                             if uu____4810
                                             then
                                               let uu____4815 =
                                                 FStar_Syntax_Print.term_to_string
                                                   k
                                                  in
                                               FStar_Util.print1
                                                 "Expected action type: %s\n"
                                                 uu____4815
                                             else ());
                                            (let g =
                                               FStar_TypeChecker_Rel.teq env1
                                                 act_typ1 k
                                                in
                                             FStar_List.iter
                                               (FStar_TypeChecker_Rel.force_trivial_guard
                                                  env1) [g_t; g_d; g_k; g];
                                             (let uu____4823 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env1)
                                                  (FStar_Options.Other
                                                     "LayeredEffects")
                                                 in
                                              if uu____4823
                                              then
                                                let uu____4828 =
                                                  FStar_Syntax_Print.term_to_string
                                                    k
                                                   in
                                                FStar_Util.print1
                                                  "Expected action type after unification: %s\n"
                                                  uu____4828
                                              else ());
                                             (let act_typ2 =
                                                let err_msg t =
                                                  let uu____4841 =
                                                    FStar_Ident.string_of_lid
                                                      ed.FStar_Syntax_Syntax.mname
                                                     in
                                                  let uu____4843 =
                                                    FStar_Ident.string_of_lid
                                                      act1.FStar_Syntax_Syntax.action_name
                                                     in
                                                  let uu____4845 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t
                                                     in
                                                  FStar_Util.format3
                                                    "Unexpected (k-)type of action %s:%s, expected bs -> repr<u> i_1 ... i_n, found: %s"
                                                    uu____4841 uu____4843
                                                    uu____4845
                                                   in
                                                let repr_args t =
                                                  let uu____4866 =
                                                    let uu____4867 =
                                                      FStar_Syntax_Subst.compress
                                                        t
                                                       in
                                                    uu____4867.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____4866 with
                                                  | FStar_Syntax_Syntax.Tm_app
                                                      (head1,a::is) ->
                                                      let uu____4919 =
                                                        let uu____4920 =
                                                          FStar_Syntax_Subst.compress
                                                            head1
                                                           in
                                                        uu____4920.FStar_Syntax_Syntax.n
                                                         in
                                                      (match uu____4919 with
                                                       | FStar_Syntax_Syntax.Tm_uinst
                                                           (uu____4929,us) ->
                                                           (us,
                                                             (FStar_Pervasives_Native.fst
                                                                a), is)
                                                       | uu____4939 ->
                                                           let uu____4940 =
                                                             let uu____4946 =
                                                               err_msg t  in
                                                             (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                               uu____4946)
                                                              in
                                                           FStar_Errors.raise_error
                                                             uu____4940 r)
                                                  | uu____4955 ->
                                                      let uu____4956 =
                                                        let uu____4962 =
                                                          err_msg t  in
                                                        (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                          uu____4962)
                                                         in
                                                      FStar_Errors.raise_error
                                                        uu____4956 r
                                                   in
                                                let k1 =
                                                  FStar_TypeChecker_Normalize.normalize
                                                    [FStar_TypeChecker_Env.Beta]
                                                    env1 k
                                                   in
                                                let uu____4972 =
                                                  let uu____4973 =
                                                    FStar_Syntax_Subst.compress
                                                      k1
                                                     in
                                                  uu____4973.FStar_Syntax_Syntax.n
                                                   in
                                                match uu____4972 with
                                                | FStar_Syntax_Syntax.Tm_arrow
                                                    (bs,c) ->
                                                    let uu____4998 =
                                                      FStar_Syntax_Subst.open_comp
                                                        bs c
                                                       in
                                                    (match uu____4998 with
                                                     | (bs1,c1) ->
                                                         let uu____5005 =
                                                           repr_args
                                                             (FStar_Syntax_Util.comp_result
                                                                c1)
                                                            in
                                                         (match uu____5005
                                                          with
                                                          | (us,a,is) ->
                                                              let ct =
                                                                {
                                                                  FStar_Syntax_Syntax.comp_univs
                                                                    = us;
                                                                  FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (
                                                                    ed.FStar_Syntax_Syntax.mname);
                                                                  FStar_Syntax_Syntax.result_typ
                                                                    = a;
                                                                  FStar_Syntax_Syntax.effect_args
                                                                    = is;
                                                                  FStar_Syntax_Syntax.flags
                                                                    = []
                                                                }  in
                                                              let uu____5016
                                                                =
                                                                FStar_Syntax_Syntax.mk_Comp
                                                                  ct
                                                                 in
                                                              FStar_Syntax_Util.arrow
                                                                bs1
                                                                uu____5016))
                                                | uu____5019 ->
                                                    let uu____5020 =
                                                      let uu____5026 =
                                                        err_msg k1  in
                                                      (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                        uu____5026)
                                                       in
                                                    FStar_Errors.raise_error
                                                      uu____5020 r
                                                 in
                                              (let uu____5030 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env1)
                                                   (FStar_Options.Other
                                                      "LayeredEffects")
                                                  in
                                               if uu____5030
                                               then
                                                 let uu____5035 =
                                                   FStar_Syntax_Print.term_to_string
                                                     act_typ2
                                                    in
                                                 FStar_Util.print1
                                                   "Action type after injecting it into the monad: %s\n"
                                                   uu____5035
                                               else ());
                                              (let act2 =
                                                 let uu____5041 =
                                                   FStar_TypeChecker_Util.generalize_universes
                                                     env1 act_defn
                                                    in
                                                 match uu____5041 with
                                                 | (us,act_defn1) ->
                                                     if
                                                       act1.FStar_Syntax_Syntax.action_univs
                                                         = []
                                                     then
                                                       let uu___544_5055 =
                                                         act1  in
                                                       let uu____5056 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us act_typ2
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.action_name
                                                           =
                                                           (uu___544_5055.FStar_Syntax_Syntax.action_name);
                                                         FStar_Syntax_Syntax.action_unqualified_name
                                                           =
                                                           (uu___544_5055.FStar_Syntax_Syntax.action_unqualified_name);
                                                         FStar_Syntax_Syntax.action_univs
                                                           = us;
                                                         FStar_Syntax_Syntax.action_params
                                                           =
                                                           (uu___544_5055.FStar_Syntax_Syntax.action_params);
                                                         FStar_Syntax_Syntax.action_defn
                                                           = act_defn1;
                                                         FStar_Syntax_Syntax.action_typ
                                                           = uu____5056
                                                       }
                                                     else
                                                       (let uu____5059 =
                                                          ((FStar_List.length
                                                              us)
                                                             =
                                                             (FStar_List.length
                                                                act1.FStar_Syntax_Syntax.action_univs))
                                                            &&
                                                            (FStar_List.forall2
                                                               (fun u1  ->
                                                                  fun u2  ->
                                                                    let uu____5066
                                                                    =
                                                                    FStar_Syntax_Syntax.order_univ_name
                                                                    u1 u2  in
                                                                    uu____5066
                                                                    =
                                                                    Prims.int_zero)
                                                               us
                                                               act1.FStar_Syntax_Syntax.action_univs)
                                                           in
                                                        if uu____5059
                                                        then
                                                          let uu___549_5071 =
                                                            act1  in
                                                          let uu____5072 =
                                                            FStar_Syntax_Subst.close_univ_vars
                                                              act1.FStar_Syntax_Syntax.action_univs
                                                              act_typ2
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.action_name
                                                              =
                                                              (uu___549_5071.FStar_Syntax_Syntax.action_name);
                                                            FStar_Syntax_Syntax.action_unqualified_name
                                                              =
                                                              (uu___549_5071.FStar_Syntax_Syntax.action_unqualified_name);
                                                            FStar_Syntax_Syntax.action_univs
                                                              =
                                                              (uu___549_5071.FStar_Syntax_Syntax.action_univs);
                                                            FStar_Syntax_Syntax.action_params
                                                              =
                                                              (uu___549_5071.FStar_Syntax_Syntax.action_params);
                                                            FStar_Syntax_Syntax.action_defn
                                                              = act_defn1;
                                                            FStar_Syntax_Syntax.action_typ
                                                              = uu____5072
                                                          }
                                                        else
                                                          (let uu____5075 =
                                                             let uu____5081 =
                                                               let uu____5083
                                                                 =
                                                                 FStar_Ident.string_of_lid
                                                                   ed.FStar_Syntax_Syntax.mname
                                                                  in
                                                               let uu____5085
                                                                 =
                                                                 FStar_Ident.string_of_lid
                                                                   act1.FStar_Syntax_Syntax.action_name
                                                                  in
                                                               let uu____5087
                                                                 =
                                                                 FStar_Syntax_Print.univ_names_to_string
                                                                   us
                                                                  in
                                                               let uu____5089
                                                                 =
                                                                 FStar_Syntax_Print.univ_names_to_string
                                                                   act1.FStar_Syntax_Syntax.action_univs
                                                                  in
                                                               FStar_Util.format4
                                                                 "Expected and generalized universes in the declaration for %s:%s are different, input: %s, but after gen: %s"
                                                                 uu____5083
                                                                 uu____5085
                                                                 uu____5087
                                                                 uu____5089
                                                                in
                                                             (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                               uu____5081)
                                                              in
                                                           FStar_Errors.raise_error
                                                             uu____5075 r))
                                                  in
                                               act2)))))))))
                       in
                    let tschemes_of uu____5114 =
                      match uu____5114 with
                      | (us,t,ty) -> ((us, t), (us, ty))  in
                    let combinators =
                      let uu____5159 =
                        let uu____5160 = tschemes_of repr  in
                        let uu____5165 = tschemes_of return_repr  in
                        let uu____5170 = tschemes_of bind_repr  in
                        let uu____5175 = tschemes_of stronger_repr  in
                        let uu____5180 = tschemes_of if_then_else1  in
                        {
                          FStar_Syntax_Syntax.l_base_effect =
                            underlying_effect_lid;
                          FStar_Syntax_Syntax.l_repr = uu____5160;
                          FStar_Syntax_Syntax.l_return = uu____5165;
                          FStar_Syntax_Syntax.l_bind = uu____5170;
                          FStar_Syntax_Syntax.l_subcomp = uu____5175;
                          FStar_Syntax_Syntax.l_if_then_else = uu____5180
                        }  in
                      FStar_Syntax_Syntax.Layered_eff uu____5159  in
                    let uu___558_5185 = ed  in
                    let uu____5186 =
                      FStar_List.map (tc_action env0)
                        ed.FStar_Syntax_Syntax.actions
                       in
                    {
                      FStar_Syntax_Syntax.mname =
                        (uu___558_5185.FStar_Syntax_Syntax.mname);
                      FStar_Syntax_Syntax.cattributes =
                        (uu___558_5185.FStar_Syntax_Syntax.cattributes);
                      FStar_Syntax_Syntax.univs =
                        (uu___558_5185.FStar_Syntax_Syntax.univs);
                      FStar_Syntax_Syntax.binders =
                        (uu___558_5185.FStar_Syntax_Syntax.binders);
                      FStar_Syntax_Syntax.signature =
                        (let uu____5193 = signature  in
                         match uu____5193 with | (us,t,uu____5208) -> (us, t));
                      FStar_Syntax_Syntax.combinators = combinators;
                      FStar_Syntax_Syntax.actions = uu____5186;
                      FStar_Syntax_Syntax.eff_attrs =
                        (uu___558_5185.FStar_Syntax_Syntax.eff_attrs)
                    }))))))))
  
let (tc_non_layered_eff_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.eff_decl)
  =
  fun env0  ->
    fun ed  ->
      fun _quals  ->
        (let uu____5246 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
             (FStar_Options.Other "ED")
            in
         if uu____5246
         then
           let uu____5251 = FStar_Syntax_Print.eff_decl_to_string false ed
              in
           FStar_Util.print1 "Typechecking eff_decl: \n\t%s\n" uu____5251
         else ());
        (let uu____5257 =
           let uu____5262 =
             FStar_Syntax_Subst.univ_var_opening ed.FStar_Syntax_Syntax.univs
              in
           match uu____5262 with
           | (ed_univs_subst,ed_univs) ->
               let bs =
                 let uu____5286 =
                   FStar_Syntax_Subst.subst_binders ed_univs_subst
                     ed.FStar_Syntax_Syntax.binders
                    in
                 FStar_Syntax_Subst.open_binders uu____5286  in
               let uu____5287 =
                 let uu____5294 =
                   FStar_TypeChecker_Env.push_univ_vars env0 ed_univs  in
                 FStar_TypeChecker_TcTerm.tc_tparams uu____5294 bs  in
               (match uu____5287 with
                | (bs1,uu____5300,uu____5301) ->
                    let uu____5302 =
                      let tmp_t =
                        let uu____5312 =
                          let uu____5315 =
                            FStar_All.pipe_right FStar_Syntax_Syntax.U_zero
                              (fun _5320  ->
                                 FStar_Pervasives_Native.Some _5320)
                             in
                          FStar_Syntax_Syntax.mk_Total'
                            FStar_Syntax_Syntax.t_unit uu____5315
                           in
                        FStar_Syntax_Util.arrow bs1 uu____5312  in
                      let uu____5321 =
                        FStar_TypeChecker_Util.generalize_universes env0
                          tmp_t
                         in
                      match uu____5321 with
                      | (us,tmp_t1) ->
                          let uu____5338 =
                            let uu____5339 =
                              let uu____5340 =
                                FStar_All.pipe_right tmp_t1
                                  FStar_Syntax_Util.arrow_formals
                                 in
                              FStar_All.pipe_right uu____5340
                                FStar_Pervasives_Native.fst
                               in
                            FStar_All.pipe_right uu____5339
                              FStar_Syntax_Subst.close_binders
                             in
                          (us, uu____5338)
                       in
                    (match uu____5302 with
                     | (us,bs2) ->
                         (match ed_univs with
                          | [] -> (us, bs2)
                          | uu____5377 ->
                              let uu____5380 =
                                ((FStar_List.length ed_univs) =
                                   (FStar_List.length us))
                                  &&
                                  (FStar_List.forall2
                                     (fun u1  ->
                                        fun u2  ->
                                          let uu____5387 =
                                            FStar_Syntax_Syntax.order_univ_name
                                              u1 u2
                                             in
                                          uu____5387 = Prims.int_zero)
                                     ed_univs us)
                                 in
                              if uu____5380
                              then (us, bs2)
                              else
                                (let uu____5398 =
                                   let uu____5404 =
                                     let uu____5406 =
                                       FStar_Ident.string_of_lid
                                         ed.FStar_Syntax_Syntax.mname
                                        in
                                     let uu____5408 =
                                       FStar_Util.string_of_int
                                         (FStar_List.length ed_univs)
                                        in
                                     let uu____5410 =
                                       FStar_Util.string_of_int
                                         (FStar_List.length us)
                                        in
                                     FStar_Util.format3
                                       "Expected and generalized universes in effect declaration for %s are different, expected: %s, but found %s"
                                       uu____5406 uu____5408 uu____5410
                                      in
                                   (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                     uu____5404)
                                    in
                                 let uu____5414 =
                                   FStar_Ident.range_of_lid
                                     ed.FStar_Syntax_Syntax.mname
                                    in
                                 FStar_Errors.raise_error uu____5398
                                   uu____5414))))
            in
         match uu____5257 with
         | (us,bs) ->
             let ed1 =
               let uu___592_5422 = ed  in
               {
                 FStar_Syntax_Syntax.mname =
                   (uu___592_5422.FStar_Syntax_Syntax.mname);
                 FStar_Syntax_Syntax.cattributes =
                   (uu___592_5422.FStar_Syntax_Syntax.cattributes);
                 FStar_Syntax_Syntax.univs = us;
                 FStar_Syntax_Syntax.binders = bs;
                 FStar_Syntax_Syntax.signature =
                   (uu___592_5422.FStar_Syntax_Syntax.signature);
                 FStar_Syntax_Syntax.combinators =
                   (uu___592_5422.FStar_Syntax_Syntax.combinators);
                 FStar_Syntax_Syntax.actions =
                   (uu___592_5422.FStar_Syntax_Syntax.actions);
                 FStar_Syntax_Syntax.eff_attrs =
                   (uu___592_5422.FStar_Syntax_Syntax.eff_attrs)
               }  in
             let uu____5423 = FStar_Syntax_Subst.univ_var_opening us  in
             (match uu____5423 with
              | (ed_univs_subst,ed_univs) ->
                  let uu____5442 =
                    let uu____5447 =
                      FStar_Syntax_Subst.subst_binders ed_univs_subst bs  in
                    FStar_Syntax_Subst.open_binders' uu____5447  in
                  (match uu____5442 with
                   | (ed_bs,ed_bs_subst) ->
                       let ed2 =
                         let op uu____5468 =
                           match uu____5468 with
                           | (us1,t) ->
                               let t1 =
                                 let uu____5488 =
                                   FStar_Syntax_Subst.shift_subst
                                     ((FStar_List.length ed_bs) +
                                        (FStar_List.length us1))
                                     ed_univs_subst
                                    in
                                 FStar_Syntax_Subst.subst uu____5488 t  in
                               let uu____5497 =
                                 let uu____5498 =
                                   FStar_Syntax_Subst.shift_subst
                                     (FStar_List.length us1) ed_bs_subst
                                    in
                                 FStar_Syntax_Subst.subst uu____5498 t1  in
                               (us1, uu____5497)
                            in
                         let uu___606_5503 = ed1  in
                         let uu____5504 =
                           op ed1.FStar_Syntax_Syntax.signature  in
                         let uu____5505 =
                           FStar_Syntax_Util.apply_eff_combinators op
                             ed1.FStar_Syntax_Syntax.combinators
                            in
                         let uu____5506 =
                           FStar_List.map
                             (fun a  ->
                                let uu___609_5514 = a  in
                                let uu____5515 =
                                  let uu____5516 =
                                    op
                                      ((a.FStar_Syntax_Syntax.action_univs),
                                        (a.FStar_Syntax_Syntax.action_defn))
                                     in
                                  FStar_Pervasives_Native.snd uu____5516  in
                                let uu____5527 =
                                  let uu____5528 =
                                    op
                                      ((a.FStar_Syntax_Syntax.action_univs),
                                        (a.FStar_Syntax_Syntax.action_typ))
                                     in
                                  FStar_Pervasives_Native.snd uu____5528  in
                                {
                                  FStar_Syntax_Syntax.action_name =
                                    (uu___609_5514.FStar_Syntax_Syntax.action_name);
                                  FStar_Syntax_Syntax.action_unqualified_name
                                    =
                                    (uu___609_5514.FStar_Syntax_Syntax.action_unqualified_name);
                                  FStar_Syntax_Syntax.action_univs =
                                    (uu___609_5514.FStar_Syntax_Syntax.action_univs);
                                  FStar_Syntax_Syntax.action_params =
                                    (uu___609_5514.FStar_Syntax_Syntax.action_params);
                                  FStar_Syntax_Syntax.action_defn =
                                    uu____5515;
                                  FStar_Syntax_Syntax.action_typ = uu____5527
                                }) ed1.FStar_Syntax_Syntax.actions
                            in
                         {
                           FStar_Syntax_Syntax.mname =
                             (uu___606_5503.FStar_Syntax_Syntax.mname);
                           FStar_Syntax_Syntax.cattributes =
                             (uu___606_5503.FStar_Syntax_Syntax.cattributes);
                           FStar_Syntax_Syntax.univs =
                             (uu___606_5503.FStar_Syntax_Syntax.univs);
                           FStar_Syntax_Syntax.binders =
                             (uu___606_5503.FStar_Syntax_Syntax.binders);
                           FStar_Syntax_Syntax.signature = uu____5504;
                           FStar_Syntax_Syntax.combinators = uu____5505;
                           FStar_Syntax_Syntax.actions = uu____5506;
                           FStar_Syntax_Syntax.eff_attrs =
                             (uu___606_5503.FStar_Syntax_Syntax.eff_attrs)
                         }  in
                       ((let uu____5540 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env0)
                             (FStar_Options.Other "ED")
                            in
                         if uu____5540
                         then
                           let uu____5545 =
                             FStar_Syntax_Print.eff_decl_to_string false ed2
                              in
                           FStar_Util.print1
                             "After typechecking binders eff_decl: \n\t%s\n"
                             uu____5545
                         else ());
                        (let env =
                           let uu____5552 =
                             FStar_TypeChecker_Env.push_univ_vars env0
                               ed_univs
                              in
                           FStar_TypeChecker_Env.push_binders uu____5552
                             ed_bs
                            in
                         let check_and_gen' comb n1 env_opt uu____5587 k =
                           match uu____5587 with
                           | (us1,t) ->
                               let env1 =
                                 if FStar_Util.is_some env_opt
                                 then
                                   FStar_All.pipe_right env_opt
                                     FStar_Util.must
                                 else env  in
                               let uu____5607 =
                                 FStar_Syntax_Subst.open_univ_vars us1 t  in
                               (match uu____5607 with
                                | (us2,t1) ->
                                    let t2 =
                                      match k with
                                      | FStar_Pervasives_Native.Some k1 ->
                                          let uu____5616 =
                                            FStar_TypeChecker_Env.push_univ_vars
                                              env1 us2
                                             in
                                          FStar_TypeChecker_TcTerm.tc_check_trivial_guard
                                            uu____5616 t1 k1
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____5617 =
                                            let uu____5624 =
                                              FStar_TypeChecker_Env.push_univ_vars
                                                env1 us2
                                               in
                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                              uu____5624 t1
                                             in
                                          (match uu____5617 with
                                           | (t2,uu____5626,g) ->
                                               (FStar_TypeChecker_Rel.force_trivial_guard
                                                  env1 g;
                                                t2))
                                       in
                                    let uu____5629 =
                                      FStar_TypeChecker_Util.generalize_universes
                                        env1 t2
                                       in
                                    (match uu____5629 with
                                     | (g_us,t3) ->
                                         (if (FStar_List.length g_us) <> n1
                                          then
                                            (let error =
                                               let uu____5645 =
                                                 FStar_Ident.string_of_lid
                                                   ed2.FStar_Syntax_Syntax.mname
                                                  in
                                               let uu____5647 =
                                                 FStar_Util.string_of_int n1
                                                  in
                                               let uu____5649 =
                                                 let uu____5651 =
                                                   FStar_All.pipe_right g_us
                                                     FStar_List.length
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____5651
                                                   FStar_Util.string_of_int
                                                  in
                                               FStar_Util.format4
                                                 "Expected %s:%s to be universe-polymorphic in %s universes, found %s"
                                                 uu____5645 comb uu____5647
                                                 uu____5649
                                                in
                                             FStar_Errors.raise_error
                                               (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                                 error)
                                               t3.FStar_Syntax_Syntax.pos)
                                          else ();
                                          (match us2 with
                                           | [] -> (g_us, t3)
                                           | uu____5666 ->
                                               let uu____5667 =
                                                 ((FStar_List.length us2) =
                                                    (FStar_List.length g_us))
                                                   &&
                                                   (FStar_List.forall2
                                                      (fun u1  ->
                                                         fun u2  ->
                                                           let uu____5674 =
                                                             FStar_Syntax_Syntax.order_univ_name
                                                               u1 u2
                                                              in
                                                           uu____5674 =
                                                             Prims.int_zero)
                                                      us2 g_us)
                                                  in
                                               if uu____5667
                                               then (g_us, t3)
                                               else
                                                 (let uu____5685 =
                                                    let uu____5691 =
                                                      let uu____5693 =
                                                        FStar_Ident.string_of_lid
                                                          ed2.FStar_Syntax_Syntax.mname
                                                         in
                                                      let uu____5695 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             us2)
                                                         in
                                                      let uu____5697 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             g_us)
                                                         in
                                                      FStar_Util.format4
                                                        "Expected and generalized universes in the declaration for %s:%s are different, expected: %s, but found %s"
                                                        uu____5693 comb
                                                        uu____5695 uu____5697
                                                       in
                                                    (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                      uu____5691)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____5685
                                                    t3.FStar_Syntax_Syntax.pos)))))
                            in
                         let signature =
                           check_and_gen' "signature" Prims.int_one
                             FStar_Pervasives_Native.None
                             ed2.FStar_Syntax_Syntax.signature
                             FStar_Pervasives_Native.None
                            in
                         (let uu____5705 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env0)
                              (FStar_Options.Other "ED")
                             in
                          if uu____5705
                          then
                            let uu____5710 =
                              FStar_Syntax_Print.tscheme_to_string signature
                               in
                            FStar_Util.print1 "Typechecked signature: %s\n"
                              uu____5710
                          else ());
                         (let fresh_a_and_wp uu____5726 =
                            let fail1 t =
                              let uu____5739 =
                                FStar_TypeChecker_Err.unexpected_signature_for_monad
                                  env ed2.FStar_Syntax_Syntax.mname t
                                 in
                              FStar_Errors.raise_error uu____5739
                                (FStar_Pervasives_Native.snd
                                   ed2.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos
                               in
                            let uu____5755 =
                              FStar_TypeChecker_Env.inst_tscheme signature
                               in
                            match uu____5755 with
                            | (uu____5766,signature1) ->
                                let uu____5768 =
                                  let uu____5769 =
                                    FStar_Syntax_Subst.compress signature1
                                     in
                                  uu____5769.FStar_Syntax_Syntax.n  in
                                (match uu____5768 with
                                 | FStar_Syntax_Syntax.Tm_arrow
                                     (bs1,uu____5779) ->
                                     let bs2 =
                                       FStar_Syntax_Subst.open_binders bs1
                                        in
                                     (match bs2 with
                                      | (a,uu____5808)::(wp,uu____5810)::[]
                                          ->
                                          (a, (wp.FStar_Syntax_Syntax.sort))
                                      | uu____5839 -> fail1 signature1)
                                 | uu____5840 -> fail1 signature1)
                             in
                          let log_combinator s ts =
                            let uu____5854 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "ED")
                               in
                            if uu____5854
                            then
                              let uu____5859 =
                                FStar_Ident.string_of_lid
                                  ed2.FStar_Syntax_Syntax.mname
                                 in
                              let uu____5861 =
                                FStar_Syntax_Print.tscheme_to_string ts  in
                              FStar_Util.print3 "Typechecked %s:%s = %s\n"
                                uu____5859 s uu____5861
                            else ()  in
                          let ret_wp =
                            let uu____5867 = fresh_a_and_wp ()  in
                            match uu____5867 with
                            | (a,wp_sort) ->
                                let k =
                                  let uu____5883 =
                                    let uu____5892 =
                                      FStar_Syntax_Syntax.mk_binder a  in
                                    let uu____5899 =
                                      let uu____5908 =
                                        let uu____5915 =
                                          FStar_Syntax_Syntax.bv_to_name a
                                           in
                                        FStar_Syntax_Syntax.null_binder
                                          uu____5915
                                         in
                                      [uu____5908]  in
                                    uu____5892 :: uu____5899  in
                                  let uu____5934 =
                                    FStar_Syntax_Syntax.mk_GTotal wp_sort  in
                                  FStar_Syntax_Util.arrow uu____5883
                                    uu____5934
                                   in
                                let uu____5937 =
                                  FStar_All.pipe_right ed2
                                    FStar_Syntax_Util.get_return_vc_combinator
                                   in
                                check_and_gen' "ret_wp" Prims.int_one
                                  FStar_Pervasives_Native.None uu____5937
                                  (FStar_Pervasives_Native.Some k)
                             in
                          log_combinator "ret_wp" ret_wp;
                          (let bind_wp =
                             let uu____5951 = fresh_a_and_wp ()  in
                             match uu____5951 with
                             | (a,wp_sort_a) ->
                                 let uu____5964 = fresh_a_and_wp ()  in
                                 (match uu____5964 with
                                  | (b,wp_sort_b) ->
                                      let wp_sort_a_b =
                                        let uu____5980 =
                                          let uu____5989 =
                                            let uu____5996 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a
                                               in
                                            FStar_Syntax_Syntax.null_binder
                                              uu____5996
                                             in
                                          [uu____5989]  in
                                        let uu____6009 =
                                          FStar_Syntax_Syntax.mk_Total
                                            wp_sort_b
                                           in
                                        FStar_Syntax_Util.arrow uu____5980
                                          uu____6009
                                         in
                                      let k =
                                        let uu____6015 =
                                          let uu____6024 =
                                            FStar_Syntax_Syntax.null_binder
                                              FStar_Syntax_Syntax.t_range
                                             in
                                          let uu____6031 =
                                            let uu____6040 =
                                              FStar_Syntax_Syntax.mk_binder a
                                               in
                                            let uu____6047 =
                                              let uu____6056 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  b
                                                 in
                                              let uu____6063 =
                                                let uu____6072 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_sort_a
                                                   in
                                                let uu____6079 =
                                                  let uu____6088 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_sort_a_b
                                                     in
                                                  [uu____6088]  in
                                                uu____6072 :: uu____6079  in
                                              uu____6056 :: uu____6063  in
                                            uu____6040 :: uu____6047  in
                                          uu____6024 :: uu____6031  in
                                        let uu____6131 =
                                          FStar_Syntax_Syntax.mk_Total
                                            wp_sort_b
                                           in
                                        FStar_Syntax_Util.arrow uu____6015
                                          uu____6131
                                         in
                                      let uu____6134 =
                                        FStar_All.pipe_right ed2
                                          FStar_Syntax_Util.get_bind_vc_combinator
                                         in
                                      check_and_gen' "bind_wp"
                                        (Prims.of_int (2))
                                        FStar_Pervasives_Native.None
                                        uu____6134
                                        (FStar_Pervasives_Native.Some k))
                              in
                           log_combinator "bind_wp" bind_wp;
                           (let stronger =
                              let uu____6148 = fresh_a_and_wp ()  in
                              match uu____6148 with
                              | (a,wp_sort_a) ->
                                  let uu____6161 =
                                    FStar_Syntax_Util.type_u ()  in
                                  (match uu____6161 with
                                   | (t,uu____6167) ->
                                       let k =
                                         let uu____6171 =
                                           let uu____6180 =
                                             FStar_Syntax_Syntax.mk_binder a
                                              in
                                           let uu____6187 =
                                             let uu____6196 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_a
                                                in
                                             let uu____6203 =
                                               let uu____6212 =
                                                 FStar_Syntax_Syntax.null_binder
                                                   wp_sort_a
                                                  in
                                               [uu____6212]  in
                                             uu____6196 :: uu____6203  in
                                           uu____6180 :: uu____6187  in
                                         let uu____6243 =
                                           FStar_Syntax_Syntax.mk_Total t  in
                                         FStar_Syntax_Util.arrow uu____6171
                                           uu____6243
                                          in
                                       let uu____6246 =
                                         FStar_All.pipe_right ed2
                                           FStar_Syntax_Util.get_stronger_vc_combinator
                                          in
                                       check_and_gen' "stronger"
                                         Prims.int_one
                                         FStar_Pervasives_Native.None
                                         uu____6246
                                         (FStar_Pervasives_Native.Some k))
                               in
                            log_combinator "stronger" stronger;
                            (let if_then_else1 =
                               let uu____6260 = fresh_a_and_wp ()  in
                               match uu____6260 with
                               | (a,wp_sort_a) ->
                                   let p =
                                     let uu____6274 =
                                       let uu____6277 =
                                         FStar_Ident.range_of_lid
                                           ed2.FStar_Syntax_Syntax.mname
                                          in
                                       FStar_Pervasives_Native.Some
                                         uu____6277
                                        in
                                     let uu____6278 =
                                       let uu____6279 =
                                         FStar_Syntax_Util.type_u ()  in
                                       FStar_All.pipe_right uu____6279
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_Syntax_Syntax.new_bv uu____6274
                                       uu____6278
                                      in
                                   let k =
                                     let uu____6291 =
                                       let uu____6300 =
                                         FStar_Syntax_Syntax.mk_binder a  in
                                       let uu____6307 =
                                         let uu____6316 =
                                           FStar_Syntax_Syntax.mk_binder p
                                            in
                                         let uu____6323 =
                                           let uu____6332 =
                                             FStar_Syntax_Syntax.null_binder
                                               wp_sort_a
                                              in
                                           let uu____6339 =
                                             let uu____6348 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_a
                                                in
                                             [uu____6348]  in
                                           uu____6332 :: uu____6339  in
                                         uu____6316 :: uu____6323  in
                                       uu____6300 :: uu____6307  in
                                     let uu____6385 =
                                       FStar_Syntax_Syntax.mk_Total wp_sort_a
                                        in
                                     FStar_Syntax_Util.arrow uu____6291
                                       uu____6385
                                      in
                                   let uu____6388 =
                                     let uu____6393 =
                                       FStar_All.pipe_right ed2
                                         FStar_Syntax_Util.get_wp_if_then_else_combinator
                                        in
                                     FStar_All.pipe_right uu____6393
                                       FStar_Util.must
                                      in
                                   check_and_gen' "if_then_else"
                                     Prims.int_one
                                     FStar_Pervasives_Native.None uu____6388
                                     (FStar_Pervasives_Native.Some k)
                                in
                             log_combinator "if_then_else" if_then_else1;
                             (let ite_wp =
                                let uu____6425 = fresh_a_and_wp ()  in
                                match uu____6425 with
                                | (a,wp_sort_a) ->
                                    let k =
                                      let uu____6441 =
                                        let uu____6450 =
                                          FStar_Syntax_Syntax.mk_binder a  in
                                        let uu____6457 =
                                          let uu____6466 =
                                            FStar_Syntax_Syntax.null_binder
                                              wp_sort_a
                                             in
                                          [uu____6466]  in
                                        uu____6450 :: uu____6457  in
                                      let uu____6491 =
                                        FStar_Syntax_Syntax.mk_Total
                                          wp_sort_a
                                         in
                                      FStar_Syntax_Util.arrow uu____6441
                                        uu____6491
                                       in
                                    let uu____6494 =
                                      let uu____6499 =
                                        FStar_All.pipe_right ed2
                                          FStar_Syntax_Util.get_wp_ite_combinator
                                         in
                                      FStar_All.pipe_right uu____6499
                                        FStar_Util.must
                                       in
                                    check_and_gen' "ite_wp" Prims.int_one
                                      FStar_Pervasives_Native.None uu____6494
                                      (FStar_Pervasives_Native.Some k)
                                 in
                              log_combinator "ite_wp" ite_wp;
                              (let close_wp =
                                 let uu____6515 = fresh_a_and_wp ()  in
                                 match uu____6515 with
                                 | (a,wp_sort_a) ->
                                     let b =
                                       let uu____6529 =
                                         let uu____6532 =
                                           FStar_Ident.range_of_lid
                                             ed2.FStar_Syntax_Syntax.mname
                                            in
                                         FStar_Pervasives_Native.Some
                                           uu____6532
                                          in
                                       let uu____6533 =
                                         let uu____6534 =
                                           FStar_Syntax_Util.type_u ()  in
                                         FStar_All.pipe_right uu____6534
                                           FStar_Pervasives_Native.fst
                                          in
                                       FStar_Syntax_Syntax.new_bv uu____6529
                                         uu____6533
                                        in
                                     let wp_sort_b_a =
                                       let uu____6546 =
                                         let uu____6555 =
                                           let uu____6562 =
                                             FStar_Syntax_Syntax.bv_to_name b
                                              in
                                           FStar_Syntax_Syntax.null_binder
                                             uu____6562
                                            in
                                         [uu____6555]  in
                                       let uu____6575 =
                                         FStar_Syntax_Syntax.mk_Total
                                           wp_sort_a
                                          in
                                       FStar_Syntax_Util.arrow uu____6546
                                         uu____6575
                                        in
                                     let k =
                                       let uu____6581 =
                                         let uu____6590 =
                                           FStar_Syntax_Syntax.mk_binder a
                                            in
                                         let uu____6597 =
                                           let uu____6606 =
                                             FStar_Syntax_Syntax.mk_binder b
                                              in
                                           let uu____6613 =
                                             let uu____6622 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_b_a
                                                in
                                             [uu____6622]  in
                                           uu____6606 :: uu____6613  in
                                         uu____6590 :: uu____6597  in
                                       let uu____6653 =
                                         FStar_Syntax_Syntax.mk_Total
                                           wp_sort_a
                                          in
                                       FStar_Syntax_Util.arrow uu____6581
                                         uu____6653
                                        in
                                     let uu____6656 =
                                       let uu____6661 =
                                         FStar_All.pipe_right ed2
                                           FStar_Syntax_Util.get_wp_close_combinator
                                          in
                                       FStar_All.pipe_right uu____6661
                                         FStar_Util.must
                                        in
                                     check_and_gen' "close_wp"
                                       (Prims.of_int (2))
                                       FStar_Pervasives_Native.None
                                       uu____6656
                                       (FStar_Pervasives_Native.Some k)
                                  in
                               log_combinator "close_wp" close_wp;
                               (let trivial =
                                  let uu____6677 = fresh_a_and_wp ()  in
                                  match uu____6677 with
                                  | (a,wp_sort_a) ->
                                      let uu____6690 =
                                        FStar_Syntax_Util.type_u ()  in
                                      (match uu____6690 with
                                       | (t,uu____6696) ->
                                           let k =
                                             let uu____6700 =
                                               let uu____6709 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   a
                                                  in
                                               let uu____6716 =
                                                 let uu____6725 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     wp_sort_a
                                                    in
                                                 [uu____6725]  in
                                               uu____6709 :: uu____6716  in
                                             let uu____6750 =
                                               FStar_Syntax_Syntax.mk_GTotal
                                                 t
                                                in
                                             FStar_Syntax_Util.arrow
                                               uu____6700 uu____6750
                                              in
                                           let trivial =
                                             let uu____6754 =
                                               let uu____6759 =
                                                 FStar_All.pipe_right ed2
                                                   FStar_Syntax_Util.get_wp_trivial_combinator
                                                  in
                                               FStar_All.pipe_right
                                                 uu____6759 FStar_Util.must
                                                in
                                             check_and_gen' "trivial"
                                               Prims.int_one
                                               FStar_Pervasives_Native.None
                                               uu____6754
                                               (FStar_Pervasives_Native.Some
                                                  k)
                                              in
                                           (log_combinator "trivial" trivial;
                                            trivial))
                                   in
                                let uu____6774 =
                                  let uu____6791 =
                                    FStar_All.pipe_right ed2
                                      FStar_Syntax_Util.get_eff_repr
                                     in
                                  match uu____6791 with
                                  | FStar_Pervasives_Native.None  ->
                                      (FStar_Pervasives_Native.None,
                                        FStar_Pervasives_Native.None,
                                        FStar_Pervasives_Native.None,
                                        (ed2.FStar_Syntax_Syntax.actions))
                                  | uu____6820 ->
                                      let repr =
                                        let uu____6824 = fresh_a_and_wp ()
                                           in
                                        match uu____6824 with
                                        | (a,wp_sort_a) ->
                                            let uu____6837 =
                                              FStar_Syntax_Util.type_u ()  in
                                            (match uu____6837 with
                                             | (t,uu____6843) ->
                                                 let k =
                                                   let uu____6847 =
                                                     let uu____6856 =
                                                       FStar_Syntax_Syntax.mk_binder
                                                         a
                                                        in
                                                     let uu____6863 =
                                                       let uu____6872 =
                                                         FStar_Syntax_Syntax.null_binder
                                                           wp_sort_a
                                                          in
                                                       [uu____6872]  in
                                                     uu____6856 :: uu____6863
                                                      in
                                                   let uu____6897 =
                                                     FStar_Syntax_Syntax.mk_GTotal
                                                       t
                                                      in
                                                   FStar_Syntax_Util.arrow
                                                     uu____6847 uu____6897
                                                    in
                                                 let uu____6900 =
                                                   let uu____6905 =
                                                     FStar_All.pipe_right ed2
                                                       FStar_Syntax_Util.get_eff_repr
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____6905
                                                     FStar_Util.must
                                                    in
                                                 check_and_gen' "repr"
                                                   Prims.int_one
                                                   FStar_Pervasives_Native.None
                                                   uu____6900
                                                   (FStar_Pervasives_Native.Some
                                                      k))
                                         in
                                      (log_combinator "repr" repr;
                                       (let mk_repr' t wp =
                                          let uu____6949 =
                                            FStar_TypeChecker_Env.inst_tscheme
                                              repr
                                             in
                                          match uu____6949 with
                                          | (uu____6956,repr1) ->
                                              let repr2 =
                                                FStar_TypeChecker_Normalize.normalize
                                                  [FStar_TypeChecker_Env.EraseUniverses;
                                                  FStar_TypeChecker_Env.AllowUnboundUniverses]
                                                  env repr1
                                                 in
                                              let uu____6959 =
                                                let uu____6966 =
                                                  let uu____6967 =
                                                    let uu____6984 =
                                                      let uu____6995 =
                                                        FStar_All.pipe_right
                                                          t
                                                          FStar_Syntax_Syntax.as_arg
                                                         in
                                                      let uu____7012 =
                                                        let uu____7023 =
                                                          FStar_All.pipe_right
                                                            wp
                                                            FStar_Syntax_Syntax.as_arg
                                                           in
                                                        [uu____7023]  in
                                                      uu____6995 ::
                                                        uu____7012
                                                       in
                                                    (repr2, uu____6984)  in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____6967
                                                   in
                                                FStar_Syntax_Syntax.mk
                                                  uu____6966
                                                 in
                                              uu____6959
                                                FStar_Pervasives_Native.None
                                                FStar_Range.dummyRange
                                           in
                                        let mk_repr a wp =
                                          let uu____7089 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          mk_repr' uu____7089 wp  in
                                        let destruct_repr t =
                                          let uu____7104 =
                                            let uu____7105 =
                                              FStar_Syntax_Subst.compress t
                                               in
                                            uu____7105.FStar_Syntax_Syntax.n
                                             in
                                          match uu____7104 with
                                          | FStar_Syntax_Syntax.Tm_app
                                              (uu____7116,(t1,uu____7118)::
                                               (wp,uu____7120)::[])
                                              -> (t1, wp)
                                          | uu____7179 ->
                                              failwith "Unexpected repr type"
                                           in
                                        let return_repr =
                                          let return_repr_ts =
                                            let uu____7195 =
                                              FStar_All.pipe_right ed2
                                                FStar_Syntax_Util.get_return_repr
                                               in
                                            FStar_All.pipe_right uu____7195
                                              FStar_Util.must
                                             in
                                          let uu____7222 = fresh_a_and_wp ()
                                             in
                                          match uu____7222 with
                                          | (a,uu____7230) ->
                                              let x_a =
                                                let uu____7236 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    a
                                                   in
                                                FStar_Syntax_Syntax.gen_bv
                                                  "x_a"
                                                  FStar_Pervasives_Native.None
                                                  uu____7236
                                                 in
                                              let res =
                                                let wp =
                                                  let uu____7244 =
                                                    let uu____7249 =
                                                      let uu____7250 =
                                                        FStar_TypeChecker_Env.inst_tscheme
                                                          ret_wp
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____7250
                                                        FStar_Pervasives_Native.snd
                                                       in
                                                    let uu____7259 =
                                                      let uu____7260 =
                                                        let uu____7269 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            a
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____7269
                                                          FStar_Syntax_Syntax.as_arg
                                                         in
                                                      let uu____7278 =
                                                        let uu____7289 =
                                                          let uu____7298 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x_a
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____7298
                                                            FStar_Syntax_Syntax.as_arg
                                                           in
                                                        [uu____7289]  in
                                                      uu____7260 ::
                                                        uu____7278
                                                       in
                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                      uu____7249 uu____7259
                                                     in
                                                  uu____7244
                                                    FStar_Pervasives_Native.None
                                                    FStar_Range.dummyRange
                                                   in
                                                mk_repr a wp  in
                                              let k =
                                                let uu____7334 =
                                                  let uu____7343 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      a
                                                     in
                                                  let uu____7350 =
                                                    let uu____7359 =
                                                      FStar_Syntax_Syntax.mk_binder
                                                        x_a
                                                       in
                                                    [uu____7359]  in
                                                  uu____7343 :: uu____7350
                                                   in
                                                let uu____7384 =
                                                  FStar_Syntax_Syntax.mk_Total
                                                    res
                                                   in
                                                FStar_Syntax_Util.arrow
                                                  uu____7334 uu____7384
                                                 in
                                              let uu____7387 =
                                                FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                  env k
                                                 in
                                              (match uu____7387 with
                                               | (k1,uu____7395,uu____7396)
                                                   ->
                                                   let env1 =
                                                     let uu____7400 =
                                                       FStar_TypeChecker_Env.set_range
                                                         env
                                                         (FStar_Pervasives_Native.snd
                                                            return_repr_ts).FStar_Syntax_Syntax.pos
                                                        in
                                                     FStar_Pervasives_Native.Some
                                                       uu____7400
                                                      in
                                                   check_and_gen'
                                                     "return_repr"
                                                     Prims.int_one env1
                                                     return_repr_ts
                                                     (FStar_Pervasives_Native.Some
                                                        k1))
                                           in
                                        log_combinator "return_repr"
                                          return_repr;
                                        (let bind_repr =
                                           let bind_repr_ts =
                                             let uu____7413 =
                                               FStar_All.pipe_right ed2
                                                 FStar_Syntax_Util.get_bind_repr
                                                in
                                             FStar_All.pipe_right uu____7413
                                               FStar_Util.must
                                              in
                                           let r =
                                             let uu____7451 =
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 FStar_Parser_Const.range_0
                                                 FStar_Syntax_Syntax.delta_constant
                                                 FStar_Pervasives_Native.None
                                                in
                                             FStar_All.pipe_right uu____7451
                                               FStar_Syntax_Syntax.fv_to_tm
                                              in
                                           let uu____7452 = fresh_a_and_wp ()
                                              in
                                           match uu____7452 with
                                           | (a,wp_sort_a) ->
                                               let uu____7465 =
                                                 fresh_a_and_wp ()  in
                                               (match uu____7465 with
                                                | (b,wp_sort_b) ->
                                                    let wp_sort_a_b =
                                                      let uu____7481 =
                                                        let uu____7490 =
                                                          let uu____7497 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              a
                                                             in
                                                          FStar_Syntax_Syntax.null_binder
                                                            uu____7497
                                                           in
                                                        [uu____7490]  in
                                                      let uu____7510 =
                                                        FStar_Syntax_Syntax.mk_Total
                                                          wp_sort_b
                                                         in
                                                      FStar_Syntax_Util.arrow
                                                        uu____7481 uu____7510
                                                       in
                                                    let wp_f =
                                                      FStar_Syntax_Syntax.gen_bv
                                                        "wp_f"
                                                        FStar_Pervasives_Native.None
                                                        wp_sort_a
                                                       in
                                                    let wp_g =
                                                      FStar_Syntax_Syntax.gen_bv
                                                        "wp_g"
                                                        FStar_Pervasives_Native.None
                                                        wp_sort_a_b
                                                       in
                                                    let x_a =
                                                      let uu____7518 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          a
                                                         in
                                                      FStar_Syntax_Syntax.gen_bv
                                                        "x_a"
                                                        FStar_Pervasives_Native.None
                                                        uu____7518
                                                       in
                                                    let wp_g_x =
                                                      let uu____7523 =
                                                        let uu____7528 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            wp_g
                                                           in
                                                        let uu____7529 =
                                                          let uu____7530 =
                                                            let uu____7539 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                x_a
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____7539
                                                              FStar_Syntax_Syntax.as_arg
                                                             in
                                                          [uu____7530]  in
                                                        FStar_Syntax_Syntax.mk_Tm_app
                                                          uu____7528
                                                          uu____7529
                                                         in
                                                      uu____7523
                                                        FStar_Pervasives_Native.None
                                                        FStar_Range.dummyRange
                                                       in
                                                    let res =
                                                      let wp =
                                                        let uu____7570 =
                                                          let uu____7575 =
                                                            let uu____7576 =
                                                              FStar_TypeChecker_Env.inst_tscheme
                                                                bind_wp
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____7576
                                                              FStar_Pervasives_Native.snd
                                                             in
                                                          let uu____7585 =
                                                            let uu____7586 =
                                                              let uu____7589
                                                                =
                                                                let uu____7592
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    a
                                                                   in
                                                                let uu____7593
                                                                  =
                                                                  let uu____7596
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    b  in
                                                                  let uu____7597
                                                                    =
                                                                    let uu____7600
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_f  in
                                                                    let uu____7601
                                                                    =
                                                                    let uu____7604
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_g  in
                                                                    [uu____7604]
                                                                     in
                                                                    uu____7600
                                                                    ::
                                                                    uu____7601
                                                                     in
                                                                  uu____7596
                                                                    ::
                                                                    uu____7597
                                                                   in
                                                                uu____7592 ::
                                                                  uu____7593
                                                                 in
                                                              r :: uu____7589
                                                               in
                                                            FStar_List.map
                                                              FStar_Syntax_Syntax.as_arg
                                                              uu____7586
                                                             in
                                                          FStar_Syntax_Syntax.mk_Tm_app
                                                            uu____7575
                                                            uu____7585
                                                           in
                                                        uu____7570
                                                          FStar_Pervasives_Native.None
                                                          FStar_Range.dummyRange
                                                         in
                                                      mk_repr b wp  in
                                                    let maybe_range_arg =
                                                      let uu____7622 =
                                                        FStar_Util.for_some
                                                          (FStar_Syntax_Util.attr_eq
                                                             FStar_Syntax_Util.dm4f_bind_range_attr)
                                                          ed2.FStar_Syntax_Syntax.eff_attrs
                                                         in
                                                      if uu____7622
                                                      then
                                                        let uu____7633 =
                                                          FStar_Syntax_Syntax.null_binder
                                                            FStar_Syntax_Syntax.t_range
                                                           in
                                                        let uu____7640 =
                                                          let uu____7649 =
                                                            FStar_Syntax_Syntax.null_binder
                                                              FStar_Syntax_Syntax.t_range
                                                             in
                                                          [uu____7649]  in
                                                        uu____7633 ::
                                                          uu____7640
                                                      else []  in
                                                    let k =
                                                      let uu____7685 =
                                                        let uu____7694 =
                                                          let uu____7703 =
                                                            FStar_Syntax_Syntax.mk_binder
                                                              a
                                                             in
                                                          let uu____7710 =
                                                            let uu____7719 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                b
                                                               in
                                                            [uu____7719]  in
                                                          uu____7703 ::
                                                            uu____7710
                                                           in
                                                        let uu____7744 =
                                                          let uu____7753 =
                                                            let uu____7762 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                wp_f
                                                               in
                                                            let uu____7769 =
                                                              let uu____7778
                                                                =
                                                                let uu____7785
                                                                  =
                                                                  let uu____7786
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_f  in
                                                                  mk_repr a
                                                                    uu____7786
                                                                   in
                                                                FStar_Syntax_Syntax.null_binder
                                                                  uu____7785
                                                                 in
                                                              let uu____7787
                                                                =
                                                                let uu____7796
                                                                  =
                                                                  FStar_Syntax_Syntax.mk_binder
                                                                    wp_g
                                                                   in
                                                                let uu____7803
                                                                  =
                                                                  let uu____7812
                                                                    =
                                                                    let uu____7819
                                                                    =
                                                                    let uu____7820
                                                                    =
                                                                    let uu____7829
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    x_a  in
                                                                    [uu____7829]
                                                                     in
                                                                    let uu____7848
                                                                    =
                                                                    let uu____7851
                                                                    =
                                                                    mk_repr b
                                                                    wp_g_x
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    uu____7851
                                                                     in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____7820
                                                                    uu____7848
                                                                     in
                                                                    FStar_Syntax_Syntax.null_binder
                                                                    uu____7819
                                                                     in
                                                                  [uu____7812]
                                                                   in
                                                                uu____7796 ::
                                                                  uu____7803
                                                                 in
                                                              uu____7778 ::
                                                                uu____7787
                                                               in
                                                            uu____7762 ::
                                                              uu____7769
                                                             in
                                                          FStar_List.append
                                                            maybe_range_arg
                                                            uu____7753
                                                           in
                                                        FStar_List.append
                                                          uu____7694
                                                          uu____7744
                                                         in
                                                      let uu____7896 =
                                                        FStar_Syntax_Syntax.mk_Total
                                                          res
                                                         in
                                                      FStar_Syntax_Util.arrow
                                                        uu____7685 uu____7896
                                                       in
                                                    let uu____7899 =
                                                      FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                        env k
                                                       in
                                                    (match uu____7899 with
                                                     | (k1,uu____7907,uu____7908)
                                                         ->
                                                         let env1 =
                                                           FStar_TypeChecker_Env.set_range
                                                             env
                                                             (FStar_Pervasives_Native.snd
                                                                bind_repr_ts).FStar_Syntax_Syntax.pos
                                                            in
                                                         let env2 =
                                                           FStar_All.pipe_right
                                                             (let uu___804_7918
                                                                = env1  in
                                                              {
                                                                FStar_TypeChecker_Env.solver
                                                                  =
                                                                  (uu___804_7918.FStar_TypeChecker_Env.solver);
                                                                FStar_TypeChecker_Env.range
                                                                  =
                                                                  (uu___804_7918.FStar_TypeChecker_Env.range);
                                                                FStar_TypeChecker_Env.curmodule
                                                                  =
                                                                  (uu___804_7918.FStar_TypeChecker_Env.curmodule);
                                                                FStar_TypeChecker_Env.gamma
                                                                  =
                                                                  (uu___804_7918.FStar_TypeChecker_Env.gamma);
                                                                FStar_TypeChecker_Env.gamma_sig
                                                                  =
                                                                  (uu___804_7918.FStar_TypeChecker_Env.gamma_sig);
                                                                FStar_TypeChecker_Env.gamma_cache
                                                                  =
                                                                  (uu___804_7918.FStar_TypeChecker_Env.gamma_cache);
                                                                FStar_TypeChecker_Env.modules
                                                                  =
                                                                  (uu___804_7918.FStar_TypeChecker_Env.modules);
                                                                FStar_TypeChecker_Env.expected_typ
                                                                  =
                                                                  (uu___804_7918.FStar_TypeChecker_Env.expected_typ);
                                                                FStar_TypeChecker_Env.sigtab
                                                                  =
                                                                  (uu___804_7918.FStar_TypeChecker_Env.sigtab);
                                                                FStar_TypeChecker_Env.attrtab
                                                                  =
                                                                  (uu___804_7918.FStar_TypeChecker_Env.attrtab);
                                                                FStar_TypeChecker_Env.instantiate_imp
                                                                  =
                                                                  (uu___804_7918.FStar_TypeChecker_Env.instantiate_imp);
                                                                FStar_TypeChecker_Env.effects
                                                                  =
                                                                  (uu___804_7918.FStar_TypeChecker_Env.effects);
                                                                FStar_TypeChecker_Env.generalize
                                                                  =
                                                                  (uu___804_7918.FStar_TypeChecker_Env.generalize);
                                                                FStar_TypeChecker_Env.letrecs
                                                                  =
                                                                  (uu___804_7918.FStar_TypeChecker_Env.letrecs);
                                                                FStar_TypeChecker_Env.top_level
                                                                  =
                                                                  (uu___804_7918.FStar_TypeChecker_Env.top_level);
                                                                FStar_TypeChecker_Env.check_uvars
                                                                  =
                                                                  (uu___804_7918.FStar_TypeChecker_Env.check_uvars);
                                                                FStar_TypeChecker_Env.use_eq
                                                                  =
                                                                  (uu___804_7918.FStar_TypeChecker_Env.use_eq);
                                                                FStar_TypeChecker_Env.use_eq_strict
                                                                  =
                                                                  (uu___804_7918.FStar_TypeChecker_Env.use_eq_strict);
                                                                FStar_TypeChecker_Env.is_iface
                                                                  =
                                                                  (uu___804_7918.FStar_TypeChecker_Env.is_iface);
                                                                FStar_TypeChecker_Env.admit
                                                                  =
                                                                  (uu___804_7918.FStar_TypeChecker_Env.admit);
                                                                FStar_TypeChecker_Env.lax
                                                                  = true;
                                                                FStar_TypeChecker_Env.lax_universes
                                                                  =
                                                                  (uu___804_7918.FStar_TypeChecker_Env.lax_universes);
                                                                FStar_TypeChecker_Env.phase1
                                                                  =
                                                                  (uu___804_7918.FStar_TypeChecker_Env.phase1);
                                                                FStar_TypeChecker_Env.failhard
                                                                  =
                                                                  (uu___804_7918.FStar_TypeChecker_Env.failhard);
                                                                FStar_TypeChecker_Env.nosynth
                                                                  =
                                                                  (uu___804_7918.FStar_TypeChecker_Env.nosynth);
                                                                FStar_TypeChecker_Env.uvar_subtyping
                                                                  =
                                                                  (uu___804_7918.FStar_TypeChecker_Env.uvar_subtyping);
                                                                FStar_TypeChecker_Env.tc_term
                                                                  =
                                                                  (uu___804_7918.FStar_TypeChecker_Env.tc_term);
                                                                FStar_TypeChecker_Env.type_of
                                                                  =
                                                                  (uu___804_7918.FStar_TypeChecker_Env.type_of);
                                                                FStar_TypeChecker_Env.universe_of
                                                                  =
                                                                  (uu___804_7918.FStar_TypeChecker_Env.universe_of);
                                                                FStar_TypeChecker_Env.check_type_of
                                                                  =
                                                                  (uu___804_7918.FStar_TypeChecker_Env.check_type_of);
                                                                FStar_TypeChecker_Env.use_bv_sorts
                                                                  =
                                                                  (uu___804_7918.FStar_TypeChecker_Env.use_bv_sorts);
                                                                FStar_TypeChecker_Env.qtbl_name_and_index
                                                                  =
                                                                  (uu___804_7918.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                FStar_TypeChecker_Env.normalized_eff_names
                                                                  =
                                                                  (uu___804_7918.FStar_TypeChecker_Env.normalized_eff_names);
                                                                FStar_TypeChecker_Env.fv_delta_depths
                                                                  =
                                                                  (uu___804_7918.FStar_TypeChecker_Env.fv_delta_depths);
                                                                FStar_TypeChecker_Env.proof_ns
                                                                  =
                                                                  (uu___804_7918.FStar_TypeChecker_Env.proof_ns);
                                                                FStar_TypeChecker_Env.synth_hook
                                                                  =
                                                                  (uu___804_7918.FStar_TypeChecker_Env.synth_hook);
                                                                FStar_TypeChecker_Env.try_solve_implicits_hook
                                                                  =
                                                                  (uu___804_7918.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                                FStar_TypeChecker_Env.splice
                                                                  =
                                                                  (uu___804_7918.FStar_TypeChecker_Env.splice);
                                                                FStar_TypeChecker_Env.mpreprocess
                                                                  =
                                                                  (uu___804_7918.FStar_TypeChecker_Env.mpreprocess);
                                                                FStar_TypeChecker_Env.postprocess
                                                                  =
                                                                  (uu___804_7918.FStar_TypeChecker_Env.postprocess);
                                                                FStar_TypeChecker_Env.is_native_tactic
                                                                  =
                                                                  (uu___804_7918.FStar_TypeChecker_Env.is_native_tactic);
                                                                FStar_TypeChecker_Env.identifier_info
                                                                  =
                                                                  (uu___804_7918.FStar_TypeChecker_Env.identifier_info);
                                                                FStar_TypeChecker_Env.tc_hooks
                                                                  =
                                                                  (uu___804_7918.FStar_TypeChecker_Env.tc_hooks);
                                                                FStar_TypeChecker_Env.dsenv
                                                                  =
                                                                  (uu___804_7918.FStar_TypeChecker_Env.dsenv);
                                                                FStar_TypeChecker_Env.nbe
                                                                  =
                                                                  (uu___804_7918.FStar_TypeChecker_Env.nbe);
                                                                FStar_TypeChecker_Env.strict_args_tab
                                                                  =
                                                                  (uu___804_7918.FStar_TypeChecker_Env.strict_args_tab);
                                                                FStar_TypeChecker_Env.erasable_types_tab
                                                                  =
                                                                  (uu___804_7918.FStar_TypeChecker_Env.erasable_types_tab)
                                                              })
                                                             (fun _7920  ->
                                                                FStar_Pervasives_Native.Some
                                                                  _7920)
                                                            in
                                                         check_and_gen'
                                                           "bind_repr"
                                                           (Prims.of_int (2))
                                                           env2 bind_repr_ts
                                                           (FStar_Pervasives_Native.Some
                                                              k1)))
                                            in
                                         log_combinator "bind_repr" bind_repr;
                                         (let actions =
                                            let check_action act =
                                              if
                                                (FStar_List.length
                                                   act.FStar_Syntax_Syntax.action_params)
                                                  <> Prims.int_zero
                                              then
                                                failwith
                                                  "tc_eff_decl: expected action_params to be empty"
                                              else ();
                                              (let uu____7947 =
                                                 if
                                                   act.FStar_Syntax_Syntax.action_univs
                                                     = []
                                                 then (env, act)
                                                 else
                                                   (let uu____7961 =
                                                      FStar_Syntax_Subst.univ_var_opening
                                                        act.FStar_Syntax_Syntax.action_univs
                                                       in
                                                    match uu____7961 with
                                                    | (usubst,uvs) ->
                                                        let uu____7984 =
                                                          FStar_TypeChecker_Env.push_univ_vars
                                                            env uvs
                                                           in
                                                        let uu____7985 =
                                                          let uu___817_7986 =
                                                            act  in
                                                          let uu____7987 =
                                                            FStar_Syntax_Subst.subst
                                                              usubst
                                                              act.FStar_Syntax_Syntax.action_defn
                                                             in
                                                          let uu____7988 =
                                                            FStar_Syntax_Subst.subst
                                                              usubst
                                                              act.FStar_Syntax_Syntax.action_typ
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.action_name
                                                              =
                                                              (uu___817_7986.FStar_Syntax_Syntax.action_name);
                                                            FStar_Syntax_Syntax.action_unqualified_name
                                                              =
                                                              (uu___817_7986.FStar_Syntax_Syntax.action_unqualified_name);
                                                            FStar_Syntax_Syntax.action_univs
                                                              = uvs;
                                                            FStar_Syntax_Syntax.action_params
                                                              =
                                                              (uu___817_7986.FStar_Syntax_Syntax.action_params);
                                                            FStar_Syntax_Syntax.action_defn
                                                              = uu____7987;
                                                            FStar_Syntax_Syntax.action_typ
                                                              = uu____7988
                                                          }  in
                                                        (uu____7984,
                                                          uu____7985))
                                                  in
                                               match uu____7947 with
                                               | (env1,act1) ->
                                                   let act_typ =
                                                     let uu____7992 =
                                                       let uu____7993 =
                                                         FStar_Syntax_Subst.compress
                                                           act1.FStar_Syntax_Syntax.action_typ
                                                          in
                                                       uu____7993.FStar_Syntax_Syntax.n
                                                        in
                                                     match uu____7992 with
                                                     | FStar_Syntax_Syntax.Tm_arrow
                                                         (bs1,c) ->
                                                         let c1 =
                                                           FStar_Syntax_Util.comp_to_comp_typ
                                                             c
                                                            in
                                                         let uu____8019 =
                                                           FStar_Ident.lid_equals
                                                             c1.FStar_Syntax_Syntax.effect_name
                                                             ed2.FStar_Syntax_Syntax.mname
                                                            in
                                                         if uu____8019
                                                         then
                                                           let uu____8022 =
                                                             let uu____8025 =
                                                               let uu____8026
                                                                 =
                                                                 let uu____8027
                                                                   =
                                                                   FStar_List.hd
                                                                    c1.FStar_Syntax_Syntax.effect_args
                                                                    in
                                                                 FStar_Pervasives_Native.fst
                                                                   uu____8027
                                                                  in
                                                               mk_repr'
                                                                 c1.FStar_Syntax_Syntax.result_typ
                                                                 uu____8026
                                                                in
                                                             FStar_Syntax_Syntax.mk_Total
                                                               uu____8025
                                                              in
                                                           FStar_Syntax_Util.arrow
                                                             bs1 uu____8022
                                                         else
                                                           act1.FStar_Syntax_Syntax.action_typ
                                                     | uu____8050 ->
                                                         act1.FStar_Syntax_Syntax.action_typ
                                                      in
                                                   let uu____8051 =
                                                     FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                       env1 act_typ
                                                      in
                                                   (match uu____8051 with
                                                    | (act_typ1,uu____8059,g_t)
                                                        ->
                                                        let env' =
                                                          let uu___834_8062 =
                                                            FStar_TypeChecker_Env.set_expected_typ
                                                              env1 act_typ1
                                                             in
                                                          {
                                                            FStar_TypeChecker_Env.solver
                                                              =
                                                              (uu___834_8062.FStar_TypeChecker_Env.solver);
                                                            FStar_TypeChecker_Env.range
                                                              =
                                                              (uu___834_8062.FStar_TypeChecker_Env.range);
                                                            FStar_TypeChecker_Env.curmodule
                                                              =
                                                              (uu___834_8062.FStar_TypeChecker_Env.curmodule);
                                                            FStar_TypeChecker_Env.gamma
                                                              =
                                                              (uu___834_8062.FStar_TypeChecker_Env.gamma);
                                                            FStar_TypeChecker_Env.gamma_sig
                                                              =
                                                              (uu___834_8062.FStar_TypeChecker_Env.gamma_sig);
                                                            FStar_TypeChecker_Env.gamma_cache
                                                              =
                                                              (uu___834_8062.FStar_TypeChecker_Env.gamma_cache);
                                                            FStar_TypeChecker_Env.modules
                                                              =
                                                              (uu___834_8062.FStar_TypeChecker_Env.modules);
                                                            FStar_TypeChecker_Env.expected_typ
                                                              =
                                                              (uu___834_8062.FStar_TypeChecker_Env.expected_typ);
                                                            FStar_TypeChecker_Env.sigtab
                                                              =
                                                              (uu___834_8062.FStar_TypeChecker_Env.sigtab);
                                                            FStar_TypeChecker_Env.attrtab
                                                              =
                                                              (uu___834_8062.FStar_TypeChecker_Env.attrtab);
                                                            FStar_TypeChecker_Env.instantiate_imp
                                                              = false;
                                                            FStar_TypeChecker_Env.effects
                                                              =
                                                              (uu___834_8062.FStar_TypeChecker_Env.effects);
                                                            FStar_TypeChecker_Env.generalize
                                                              =
                                                              (uu___834_8062.FStar_TypeChecker_Env.generalize);
                                                            FStar_TypeChecker_Env.letrecs
                                                              =
                                                              (uu___834_8062.FStar_TypeChecker_Env.letrecs);
                                                            FStar_TypeChecker_Env.top_level
                                                              =
                                                              (uu___834_8062.FStar_TypeChecker_Env.top_level);
                                                            FStar_TypeChecker_Env.check_uvars
                                                              =
                                                              (uu___834_8062.FStar_TypeChecker_Env.check_uvars);
                                                            FStar_TypeChecker_Env.use_eq
                                                              =
                                                              (uu___834_8062.FStar_TypeChecker_Env.use_eq);
                                                            FStar_TypeChecker_Env.use_eq_strict
                                                              =
                                                              (uu___834_8062.FStar_TypeChecker_Env.use_eq_strict);
                                                            FStar_TypeChecker_Env.is_iface
                                                              =
                                                              (uu___834_8062.FStar_TypeChecker_Env.is_iface);
                                                            FStar_TypeChecker_Env.admit
                                                              =
                                                              (uu___834_8062.FStar_TypeChecker_Env.admit);
                                                            FStar_TypeChecker_Env.lax
                                                              =
                                                              (uu___834_8062.FStar_TypeChecker_Env.lax);
                                                            FStar_TypeChecker_Env.lax_universes
                                                              =
                                                              (uu___834_8062.FStar_TypeChecker_Env.lax_universes);
                                                            FStar_TypeChecker_Env.phase1
                                                              =
                                                              (uu___834_8062.FStar_TypeChecker_Env.phase1);
                                                            FStar_TypeChecker_Env.failhard
                                                              =
                                                              (uu___834_8062.FStar_TypeChecker_Env.failhard);
                                                            FStar_TypeChecker_Env.nosynth
                                                              =
                                                              (uu___834_8062.FStar_TypeChecker_Env.nosynth);
                                                            FStar_TypeChecker_Env.uvar_subtyping
                                                              =
                                                              (uu___834_8062.FStar_TypeChecker_Env.uvar_subtyping);
                                                            FStar_TypeChecker_Env.tc_term
                                                              =
                                                              (uu___834_8062.FStar_TypeChecker_Env.tc_term);
                                                            FStar_TypeChecker_Env.type_of
                                                              =
                                                              (uu___834_8062.FStar_TypeChecker_Env.type_of);
                                                            FStar_TypeChecker_Env.universe_of
                                                              =
                                                              (uu___834_8062.FStar_TypeChecker_Env.universe_of);
                                                            FStar_TypeChecker_Env.check_type_of
                                                              =
                                                              (uu___834_8062.FStar_TypeChecker_Env.check_type_of);
                                                            FStar_TypeChecker_Env.use_bv_sorts
                                                              =
                                                              (uu___834_8062.FStar_TypeChecker_Env.use_bv_sorts);
                                                            FStar_TypeChecker_Env.qtbl_name_and_index
                                                              =
                                                              (uu___834_8062.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                            FStar_TypeChecker_Env.normalized_eff_names
                                                              =
                                                              (uu___834_8062.FStar_TypeChecker_Env.normalized_eff_names);
                                                            FStar_TypeChecker_Env.fv_delta_depths
                                                              =
                                                              (uu___834_8062.FStar_TypeChecker_Env.fv_delta_depths);
                                                            FStar_TypeChecker_Env.proof_ns
                                                              =
                                                              (uu___834_8062.FStar_TypeChecker_Env.proof_ns);
                                                            FStar_TypeChecker_Env.synth_hook
                                                              =
                                                              (uu___834_8062.FStar_TypeChecker_Env.synth_hook);
                                                            FStar_TypeChecker_Env.try_solve_implicits_hook
                                                              =
                                                              (uu___834_8062.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                            FStar_TypeChecker_Env.splice
                                                              =
                                                              (uu___834_8062.FStar_TypeChecker_Env.splice);
                                                            FStar_TypeChecker_Env.mpreprocess
                                                              =
                                                              (uu___834_8062.FStar_TypeChecker_Env.mpreprocess);
                                                            FStar_TypeChecker_Env.postprocess
                                                              =
                                                              (uu___834_8062.FStar_TypeChecker_Env.postprocess);
                                                            FStar_TypeChecker_Env.is_native_tactic
                                                              =
                                                              (uu___834_8062.FStar_TypeChecker_Env.is_native_tactic);
                                                            FStar_TypeChecker_Env.identifier_info
                                                              =
                                                              (uu___834_8062.FStar_TypeChecker_Env.identifier_info);
                                                            FStar_TypeChecker_Env.tc_hooks
                                                              =
                                                              (uu___834_8062.FStar_TypeChecker_Env.tc_hooks);
                                                            FStar_TypeChecker_Env.dsenv
                                                              =
                                                              (uu___834_8062.FStar_TypeChecker_Env.dsenv);
                                                            FStar_TypeChecker_Env.nbe
                                                              =
                                                              (uu___834_8062.FStar_TypeChecker_Env.nbe);
                                                            FStar_TypeChecker_Env.strict_args_tab
                                                              =
                                                              (uu___834_8062.FStar_TypeChecker_Env.strict_args_tab);
                                                            FStar_TypeChecker_Env.erasable_types_tab
                                                              =
                                                              (uu___834_8062.FStar_TypeChecker_Env.erasable_types_tab)
                                                          }  in
                                                        ((let uu____8065 =
                                                            FStar_TypeChecker_Env.debug
                                                              env1
                                                              (FStar_Options.Other
                                                                 "ED")
                                                             in
                                                          if uu____8065
                                                          then
                                                            let uu____8069 =
                                                              FStar_Ident.string_of_lid
                                                                act1.FStar_Syntax_Syntax.action_name
                                                               in
                                                            let uu____8071 =
                                                              FStar_Syntax_Print.term_to_string
                                                                act1.FStar_Syntax_Syntax.action_defn
                                                               in
                                                            let uu____8073 =
                                                              FStar_Syntax_Print.term_to_string
                                                                act_typ1
                                                               in
                                                            FStar_Util.print3
                                                              "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                              uu____8069
                                                              uu____8071
                                                              uu____8073
                                                          else ());
                                                         (let uu____8078 =
                                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                              env'
                                                              act1.FStar_Syntax_Syntax.action_defn
                                                             in
                                                          match uu____8078
                                                          with
                                                          | (act_defn,uu____8086,g_a)
                                                              ->
                                                              let act_defn1 =
                                                                FStar_TypeChecker_Normalize.normalize
                                                                  [FStar_TypeChecker_Env.UnfoldUntil
                                                                    FStar_Syntax_Syntax.delta_constant]
                                                                  env1
                                                                  act_defn
                                                                 in
                                                              let act_typ2 =
                                                                FStar_TypeChecker_Normalize.normalize
                                                                  [FStar_TypeChecker_Env.UnfoldUntil
                                                                    FStar_Syntax_Syntax.delta_constant;
                                                                  FStar_TypeChecker_Env.Eager_unfolding;
                                                                  FStar_TypeChecker_Env.Beta]
                                                                  env1
                                                                  act_typ1
                                                                 in
                                                              let uu____8090
                                                                =
                                                                let act_typ3
                                                                  =
                                                                  FStar_Syntax_Subst.compress
                                                                    act_typ2
                                                                   in
                                                                match 
                                                                  act_typ3.FStar_Syntax_Syntax.n
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs1,c)
                                                                    ->
                                                                    let uu____8126
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs1 c  in
                                                                    (match uu____8126
                                                                    with
                                                                    | 
                                                                    (bs2,uu____8138)
                                                                    ->
                                                                    let res =
                                                                    mk_repr'
                                                                    FStar_Syntax_Syntax.tun
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    let k =
                                                                    let uu____8145
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    res  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____8145
                                                                     in
                                                                    let uu____8148
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                    env1 k
                                                                     in
                                                                    (match uu____8148
                                                                    with
                                                                    | 
                                                                    (k1,uu____8162,g)
                                                                    ->
                                                                    (k1, g)))
                                                                | uu____8166
                                                                    ->
                                                                    let uu____8167
                                                                    =
                                                                    let uu____8173
                                                                    =
                                                                    let uu____8175
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    act_typ3
                                                                     in
                                                                    let uu____8177
                                                                    =
                                                                    FStar_Syntax_Print.tag_of_term
                                                                    act_typ3
                                                                     in
                                                                    FStar_Util.format2
                                                                    "Actions must have function types (not: %s, a.k.a. %s)"
                                                                    uu____8175
                                                                    uu____8177
                                                                     in
                                                                    (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                                    uu____8173)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____8167
                                                                    act_defn1.FStar_Syntax_Syntax.pos
                                                                 in
                                                              (match uu____8090
                                                               with
                                                               | (expected_k,g_k)
                                                                   ->
                                                                   let g =
                                                                    FStar_TypeChecker_Rel.teq
                                                                    env1
                                                                    act_typ2
                                                                    expected_k
                                                                     in
                                                                   ((
                                                                    let uu____8195
                                                                    =
                                                                    let uu____8196
                                                                    =
                                                                    let uu____8197
                                                                    =
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_t g  in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_k
                                                                    uu____8197
                                                                     in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_a
                                                                    uu____8196
                                                                     in
                                                                    FStar_TypeChecker_Rel.force_trivial_guard
                                                                    env1
                                                                    uu____8195);
                                                                    (
                                                                    let act_typ3
                                                                    =
                                                                    let uu____8199
                                                                    =
                                                                    let uu____8200
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    expected_k
                                                                     in
                                                                    uu____8200.FStar_Syntax_Syntax.n
                                                                     in
                                                                    match uu____8199
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs1,c)
                                                                    ->
                                                                    let uu____8225
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs1 c  in
                                                                    (match uu____8225
                                                                    with
                                                                    | 
                                                                    (bs2,c1)
                                                                    ->
                                                                    let uu____8232
                                                                    =
                                                                    destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1)  in
                                                                    (match uu____8232
                                                                    with
                                                                    | 
                                                                    (a,wp) ->
                                                                    let c2 =
                                                                    let uu____8252
                                                                    =
                                                                    let uu____8253
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 a
                                                                     in
                                                                    [uu____8253]
                                                                     in
                                                                    let uu____8254
                                                                    =
                                                                    let uu____8265
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp  in
                                                                    [uu____8265]
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____8252;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____8254;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    }  in
                                                                    let uu____8290
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____8290))
                                                                    | 
                                                                    uu____8293
                                                                    ->
                                                                    failwith
                                                                    "Impossible (expected_k is an arrow)"
                                                                     in
                                                                    let uu____8295
                                                                    =
                                                                    if
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    = []
                                                                    then
                                                                    FStar_TypeChecker_Util.generalize_universes
                                                                    env1
                                                                    act_defn1
                                                                    else
                                                                    (let uu____8317
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    act_defn1
                                                                     in
                                                                    ((act1.FStar_Syntax_Syntax.action_univs),
                                                                    uu____8317))
                                                                     in
                                                                    match uu____8295
                                                                    with
                                                                    | 
                                                                    (univs1,act_defn2)
                                                                    ->
                                                                    let act_typ4
                                                                    =
                                                                    FStar_TypeChecker_Normalize.normalize
                                                                    [FStar_TypeChecker_Env.Beta]
                                                                    env1
                                                                    act_typ3
                                                                     in
                                                                    let act_typ5
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    univs1
                                                                    act_typ4
                                                                     in
                                                                    let uu___884_8336
                                                                    = act1
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___884_8336.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___884_8336.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    = univs1;
                                                                    FStar_Syntax_Syntax.action_params
                                                                    =
                                                                    (uu___884_8336.FStar_Syntax_Syntax.action_params);
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    act_defn2;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    act_typ5
                                                                    })))))))
                                               in
                                            FStar_All.pipe_right
                                              ed2.FStar_Syntax_Syntax.actions
                                              (FStar_List.map check_action)
                                             in
                                          ((FStar_Pervasives_Native.Some repr),
                                            (FStar_Pervasives_Native.Some
                                               return_repr),
                                            (FStar_Pervasives_Native.Some
                                               bind_repr), actions)))))
                                   in
                                match uu____6774 with
                                | (repr,return_repr,bind_repr,actions) ->
                                    let cl ts =
                                      let ts1 =
                                        FStar_Syntax_Subst.close_tscheme
                                          ed_bs ts
                                         in
                                      let ed_univs_closing =
                                        FStar_Syntax_Subst.univ_var_closing
                                          ed_univs
                                         in
                                      let uu____8379 =
                                        FStar_Syntax_Subst.shift_subst
                                          (FStar_List.length ed_bs)
                                          ed_univs_closing
                                         in
                                      FStar_Syntax_Subst.subst_tscheme
                                        uu____8379 ts1
                                       in
                                    let combinators =
                                      {
                                        FStar_Syntax_Syntax.ret_wp = ret_wp;
                                        FStar_Syntax_Syntax.bind_wp = bind_wp;
                                        FStar_Syntax_Syntax.stronger =
                                          stronger;
                                        FStar_Syntax_Syntax.if_then_else =
                                          if_then_else1;
                                        FStar_Syntax_Syntax.ite_wp = ite_wp;
                                        FStar_Syntax_Syntax.close_wp =
                                          close_wp;
                                        FStar_Syntax_Syntax.trivial = trivial;
                                        FStar_Syntax_Syntax.repr = repr;
                                        FStar_Syntax_Syntax.return_repr =
                                          return_repr;
                                        FStar_Syntax_Syntax.bind_repr =
                                          bind_repr
                                      }  in
                                    let combinators1 =
                                      FStar_Syntax_Util.apply_wp_eff_combinators
                                        cl combinators
                                       in
                                    let combinators2 =
                                      match ed2.FStar_Syntax_Syntax.combinators
                                      with
                                      | FStar_Syntax_Syntax.Primitive_eff
                                          uu____8391 ->
                                          FStar_Syntax_Syntax.Primitive_eff
                                            combinators1
                                      | FStar_Syntax_Syntax.DM4F_eff
                                          uu____8392 ->
                                          FStar_Syntax_Syntax.DM4F_eff
                                            combinators1
                                      | uu____8393 ->
                                          failwith
                                            "Impossible! tc_eff_decl on a layered effect is not expected"
                                       in
                                    let ed3 =
                                      let uu___904_8396 = ed2  in
                                      let uu____8397 = cl signature  in
                                      let uu____8398 =
                                        FStar_List.map
                                          (fun a  ->
                                             let uu___907_8406 = a  in
                                             let uu____8407 =
                                               let uu____8408 =
                                                 cl
                                                   ((a.FStar_Syntax_Syntax.action_univs),
                                                     (a.FStar_Syntax_Syntax.action_defn))
                                                  in
                                               FStar_All.pipe_right
                                                 uu____8408
                                                 FStar_Pervasives_Native.snd
                                                in
                                             let uu____8433 =
                                               let uu____8434 =
                                                 cl
                                                   ((a.FStar_Syntax_Syntax.action_univs),
                                                     (a.FStar_Syntax_Syntax.action_typ))
                                                  in
                                               FStar_All.pipe_right
                                                 uu____8434
                                                 FStar_Pervasives_Native.snd
                                                in
                                             {
                                               FStar_Syntax_Syntax.action_name
                                                 =
                                                 (uu___907_8406.FStar_Syntax_Syntax.action_name);
                                               FStar_Syntax_Syntax.action_unqualified_name
                                                 =
                                                 (uu___907_8406.FStar_Syntax_Syntax.action_unqualified_name);
                                               FStar_Syntax_Syntax.action_univs
                                                 =
                                                 (uu___907_8406.FStar_Syntax_Syntax.action_univs);
                                               FStar_Syntax_Syntax.action_params
                                                 =
                                                 (uu___907_8406.FStar_Syntax_Syntax.action_params);
                                               FStar_Syntax_Syntax.action_defn
                                                 = uu____8407;
                                               FStar_Syntax_Syntax.action_typ
                                                 = uu____8433
                                             }) actions
                                         in
                                      {
                                        FStar_Syntax_Syntax.mname =
                                          (uu___904_8396.FStar_Syntax_Syntax.mname);
                                        FStar_Syntax_Syntax.cattributes =
                                          (uu___904_8396.FStar_Syntax_Syntax.cattributes);
                                        FStar_Syntax_Syntax.univs =
                                          (uu___904_8396.FStar_Syntax_Syntax.univs);
                                        FStar_Syntax_Syntax.binders =
                                          (uu___904_8396.FStar_Syntax_Syntax.binders);
                                        FStar_Syntax_Syntax.signature =
                                          uu____8397;
                                        FStar_Syntax_Syntax.combinators =
                                          combinators2;
                                        FStar_Syntax_Syntax.actions =
                                          uu____8398;
                                        FStar_Syntax_Syntax.eff_attrs =
                                          (uu___904_8396.FStar_Syntax_Syntax.eff_attrs)
                                      }  in
                                    ((let uu____8460 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env)
                                          (FStar_Options.Other "ED")
                                         in
                                      if uu____8460
                                      then
                                        let uu____8465 =
                                          FStar_Syntax_Print.eff_decl_to_string
                                            false ed3
                                           in
                                        FStar_Util.print1
                                          "Typechecked effect declaration:\n\t%s\n"
                                          uu____8465
                                      else ());
                                     ed3)))))))))))))
  
let (tc_eff_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.eff_decl)
  =
  fun env  ->
    fun ed  ->
      fun quals  ->
        let uu____8491 =
          let uu____8506 =
            FStar_All.pipe_right ed FStar_Syntax_Util.is_layered  in
          if uu____8506 then tc_layered_eff_decl else tc_non_layered_eff_decl
           in
        uu____8491 env ed quals
  
let (monad_signature :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax))
  =
  fun env  ->
    fun m  ->
      fun s  ->
        let fail1 uu____8556 =
          let uu____8557 =
            FStar_TypeChecker_Err.unexpected_signature_for_monad env m s  in
          let uu____8563 = FStar_Ident.range_of_lid m  in
          FStar_Errors.raise_error uu____8557 uu____8563  in
        let s1 = FStar_Syntax_Subst.compress s  in
        match s1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let bs1 = FStar_Syntax_Subst.open_binders bs  in
            (match bs1 with
             | (a,uu____8607)::(wp,uu____8609)::[] ->
                 (a, (wp.FStar_Syntax_Syntax.sort))
             | uu____8638 -> fail1 ())
        | uu____8639 -> fail1 ()
  
let (tc_layered_lift :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_Syntax_Syntax.sub_eff)
  =
  fun env0  ->
    fun sub1  ->
      (let uu____8652 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
           (FStar_Options.Other "LayeredEffects")
          in
       if uu____8652
       then
         let uu____8657 = FStar_Syntax_Print.sub_eff_to_string sub1  in
         FStar_Util.print1 "Typechecking sub_effect: %s\n" uu____8657
       else ());
      (let lift_ts =
         FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift FStar_Util.must
          in
       let r =
         let uu____8674 =
           FStar_All.pipe_right lift_ts FStar_Pervasives_Native.snd  in
         uu____8674.FStar_Syntax_Syntax.pos  in
       (let src_ed =
          FStar_TypeChecker_Env.get_effect_decl env0
            sub1.FStar_Syntax_Syntax.source
           in
        let tgt_ed =
          FStar_TypeChecker_Env.get_effect_decl env0
            sub1.FStar_Syntax_Syntax.target
           in
        let uu____8686 =
          ((FStar_All.pipe_right src_ed FStar_Syntax_Util.is_layered) &&
             (let uu____8690 =
                let uu____8691 =
                  FStar_All.pipe_right src_ed
                    FStar_Syntax_Util.get_layered_effect_base
                   in
                FStar_All.pipe_right uu____8691 FStar_Util.must  in
              FStar_Ident.lid_equals uu____8690
                tgt_ed.FStar_Syntax_Syntax.mname))
            ||
            (((FStar_All.pipe_right tgt_ed FStar_Syntax_Util.is_layered) &&
                (let uu____8700 =
                   let uu____8701 =
                     FStar_All.pipe_right tgt_ed
                       FStar_Syntax_Util.get_layered_effect_base
                      in
                   FStar_All.pipe_right uu____8701 FStar_Util.must  in
                 FStar_Ident.lid_equals uu____8700
                   src_ed.FStar_Syntax_Syntax.mname))
               &&
               (let uu____8709 =
                  FStar_Ident.lid_equals src_ed.FStar_Syntax_Syntax.mname
                    FStar_Parser_Const.effect_PURE_lid
                   in
                Prims.op_Negation uu____8709))
           in
        if uu____8686
        then
          let uu____8712 =
            let uu____8718 =
              let uu____8720 =
                FStar_All.pipe_right src_ed.FStar_Syntax_Syntax.mname
                  FStar_Ident.string_of_lid
                 in
              let uu____8723 =
                FStar_All.pipe_right tgt_ed.FStar_Syntax_Syntax.mname
                  FStar_Ident.string_of_lid
                 in
              FStar_Util.format2
                "Lifts cannot be defined from a layered effect to its repr or vice versa (%s and %s here)"
                uu____8720 uu____8723
               in
            (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____8718)  in
          FStar_Errors.raise_error uu____8712 r
        else ());
       (let uu____8730 = check_and_gen env0 "" "lift" Prims.int_one lift_ts
           in
        match uu____8730 with
        | (us,lift,lift_ty) ->
            ((let uu____8744 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
                  (FStar_Options.Other "LayeredEffects")
                 in
              if uu____8744
              then
                let uu____8749 =
                  FStar_Syntax_Print.tscheme_to_string (us, lift)  in
                let uu____8755 =
                  FStar_Syntax_Print.tscheme_to_string (us, lift_ty)  in
                FStar_Util.print2 "Typechecked lift: %s and lift_ty: %s\n"
                  uu____8749 uu____8755
              else ());
             (let uu____8764 = FStar_Syntax_Subst.open_univ_vars us lift_ty
                 in
              match uu____8764 with
              | (us1,lift_ty1) ->
                  let env = FStar_TypeChecker_Env.push_univ_vars env0 us1  in
                  (check_no_subtyping_for_layered_combinator env lift_ty1
                     FStar_Pervasives_Native.None;
                   (let lift_t_shape_error s =
                      let uu____8782 =
                        FStar_Ident.string_of_lid
                          sub1.FStar_Syntax_Syntax.source
                         in
                      let uu____8784 =
                        FStar_Ident.string_of_lid
                          sub1.FStar_Syntax_Syntax.target
                         in
                      let uu____8786 =
                        FStar_Syntax_Print.term_to_string lift_ty1  in
                      FStar_Util.format4
                        "Unexpected shape of lift %s~>%s, reason:%s (t:%s)"
                        uu____8782 uu____8784 s uu____8786
                       in
                    let uu____8789 =
                      let uu____8796 =
                        let uu____8801 = FStar_Syntax_Util.type_u ()  in
                        FStar_All.pipe_right uu____8801
                          (fun uu____8818  ->
                             match uu____8818 with
                             | (t,u) ->
                                 let uu____8829 =
                                   let uu____8830 =
                                     FStar_Syntax_Syntax.gen_bv "a"
                                       FStar_Pervasives_Native.None t
                                      in
                                   FStar_All.pipe_right uu____8830
                                     FStar_Syntax_Syntax.mk_binder
                                    in
                                 (uu____8829, u))
                         in
                      match uu____8796 with
                      | (a,u_a) ->
                          let rest_bs =
                            let uu____8849 =
                              let uu____8850 =
                                FStar_Syntax_Subst.compress lift_ty1  in
                              uu____8850.FStar_Syntax_Syntax.n  in
                            match uu____8849 with
                            | FStar_Syntax_Syntax.Tm_arrow (bs,uu____8862)
                                when
                                (FStar_List.length bs) >= (Prims.of_int (2))
                                ->
                                let uu____8890 =
                                  FStar_Syntax_Subst.open_binders bs  in
                                (match uu____8890 with
                                 | (a',uu____8900)::bs1 ->
                                     let uu____8920 =
                                       let uu____8921 =
                                         FStar_All.pipe_right bs1
                                           (FStar_List.splitAt
                                              ((FStar_List.length bs1) -
                                                 Prims.int_one))
                                          in
                                       FStar_All.pipe_right uu____8921
                                         FStar_Pervasives_Native.fst
                                        in
                                     let uu____8987 =
                                       let uu____9000 =
                                         let uu____9003 =
                                           let uu____9004 =
                                             let uu____9011 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 (FStar_Pervasives_Native.fst
                                                    a)
                                                in
                                             (a', uu____9011)  in
                                           FStar_Syntax_Syntax.NT uu____9004
                                            in
                                         [uu____9003]  in
                                       FStar_Syntax_Subst.subst_binders
                                         uu____9000
                                        in
                                     FStar_All.pipe_right uu____8920
                                       uu____8987)
                            | uu____9026 ->
                                let uu____9027 =
                                  let uu____9033 =
                                    lift_t_shape_error
                                      "either not an arrow, or not enough binders"
                                     in
                                  (FStar_Errors.Fatal_UnexpectedExpressionType,
                                    uu____9033)
                                   in
                                FStar_Errors.raise_error uu____9027 r
                             in
                          let uu____9045 =
                            let uu____9056 =
                              let uu____9061 =
                                FStar_TypeChecker_Env.push_binders env (a ::
                                  rest_bs)
                                 in
                              let uu____9068 =
                                let uu____9069 =
                                  FStar_All.pipe_right a
                                    FStar_Pervasives_Native.fst
                                   in
                                FStar_All.pipe_right uu____9069
                                  FStar_Syntax_Syntax.bv_to_name
                                 in
                              FStar_TypeChecker_Util.fresh_effect_repr_en
                                uu____9061 r sub1.FStar_Syntax_Syntax.source
                                u_a uu____9068
                               in
                            match uu____9056 with
                            | (f_sort,g) ->
                                let uu____9090 =
                                  let uu____9097 =
                                    FStar_Syntax_Syntax.gen_bv "f"
                                      FStar_Pervasives_Native.None f_sort
                                     in
                                  FStar_All.pipe_right uu____9097
                                    FStar_Syntax_Syntax.mk_binder
                                   in
                                (uu____9090, g)
                             in
                          (match uu____9045 with
                           | (f_b,g_f_b) ->
                               let bs = a ::
                                 (FStar_List.append rest_bs [f_b])  in
                               let uu____9164 =
                                 let uu____9169 =
                                   FStar_TypeChecker_Env.push_binders env bs
                                    in
                                 let uu____9170 =
                                   let uu____9171 =
                                     FStar_All.pipe_right a
                                       FStar_Pervasives_Native.fst
                                      in
                                   FStar_All.pipe_right uu____9171
                                     FStar_Syntax_Syntax.bv_to_name
                                    in
                                 FStar_TypeChecker_Util.fresh_effect_repr_en
                                   uu____9169 r
                                   sub1.FStar_Syntax_Syntax.target u_a
                                   uu____9170
                                  in
                               (match uu____9164 with
                                | (repr,g_repr) ->
                                    let uu____9188 =
                                      let uu____9193 =
                                        FStar_TypeChecker_Env.push_binders
                                          env bs
                                         in
                                      let uu____9194 =
                                        let uu____9196 =
                                          FStar_Ident.string_of_lid
                                            sub1.FStar_Syntax_Syntax.source
                                           in
                                        let uu____9198 =
                                          FStar_Ident.string_of_lid
                                            sub1.FStar_Syntax_Syntax.target
                                           in
                                        FStar_Util.format2
                                          "implicit for pure_wp in typechecking lift %s~>%s"
                                          uu____9196 uu____9198
                                         in
                                      pure_wp_uvar uu____9193 repr uu____9194
                                        r
                                       in
                                    (match uu____9188 with
                                     | (pure_wp_uvar1,guard_wp) ->
                                         let c =
                                           let uu____9210 =
                                             let uu____9211 =
                                               let uu____9212 =
                                                 FStar_TypeChecker_Env.new_u_univ
                                                   ()
                                                  in
                                               [uu____9212]  in
                                             let uu____9213 =
                                               let uu____9224 =
                                                 FStar_All.pipe_right
                                                   pure_wp_uvar1
                                                   FStar_Syntax_Syntax.as_arg
                                                  in
                                               [uu____9224]  in
                                             {
                                               FStar_Syntax_Syntax.comp_univs
                                                 = uu____9211;
                                               FStar_Syntax_Syntax.effect_name
                                                 =
                                                 FStar_Parser_Const.effect_PURE_lid;
                                               FStar_Syntax_Syntax.result_typ
                                                 = repr;
                                               FStar_Syntax_Syntax.effect_args
                                                 = uu____9213;
                                               FStar_Syntax_Syntax.flags = []
                                             }  in
                                           FStar_Syntax_Syntax.mk_Comp
                                             uu____9210
                                            in
                                         let uu____9257 =
                                           FStar_Syntax_Util.arrow bs c  in
                                         let uu____9260 =
                                           let uu____9261 =
                                             FStar_TypeChecker_Env.conj_guard
                                               g_f_b g_repr
                                              in
                                           FStar_TypeChecker_Env.conj_guard
                                             uu____9261 guard_wp
                                            in
                                         (uu____9257, uu____9260))))
                       in
                    match uu____8789 with
                    | (k,g_k) ->
                        ((let uu____9271 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "LayeredEffects")
                             in
                          if uu____9271
                          then
                            let uu____9276 =
                              FStar_Syntax_Print.term_to_string k  in
                            FStar_Util.print1
                              "tc_layered_lift: before unification k: %s\n"
                              uu____9276
                          else ());
                         (let g = FStar_TypeChecker_Rel.teq env lift_ty1 k
                             in
                          FStar_TypeChecker_Rel.force_trivial_guard env g_k;
                          FStar_TypeChecker_Rel.force_trivial_guard env g;
                          (let uu____9285 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env0)
                               (FStar_Options.Other "LayeredEffects")
                              in
                           if uu____9285
                           then
                             let uu____9290 =
                               FStar_Syntax_Print.term_to_string k  in
                             FStar_Util.print1 "After unification k: %s\n"
                               uu____9290
                           else ());
                          (let sub2 =
                             let uu___1000_9296 = sub1  in
                             let uu____9297 =
                               let uu____9300 =
                                 let uu____9301 =
                                   let uu____9304 =
                                     FStar_All.pipe_right k
                                       (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                          env)
                                      in
                                   FStar_All.pipe_right uu____9304
                                     (FStar_Syntax_Subst.close_univ_vars us1)
                                    in
                                 (us1, uu____9301)  in
                               FStar_Pervasives_Native.Some uu____9300  in
                             {
                               FStar_Syntax_Syntax.source =
                                 (uu___1000_9296.FStar_Syntax_Syntax.source);
                               FStar_Syntax_Syntax.target =
                                 (uu___1000_9296.FStar_Syntax_Syntax.target);
                               FStar_Syntax_Syntax.lift_wp = uu____9297;
                               FStar_Syntax_Syntax.lift =
                                 (FStar_Pervasives_Native.Some (us1, lift))
                             }  in
                           (let uu____9316 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env0)
                                (FStar_Options.Other "LayeredEffects")
                               in
                            if uu____9316
                            then
                              let uu____9321 =
                                FStar_Syntax_Print.sub_eff_to_string sub2  in
                              FStar_Util.print1 "Final sub_effect: %s\n"
                                uu____9321
                            else ());
                           sub2)))))))))
  
let (tc_lift :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff ->
      FStar_Range.range -> FStar_Syntax_Syntax.sub_eff)
  =
  fun env  ->
    fun sub1  ->
      fun r  ->
        let check_and_gen1 env1 t k =
          let uu____9358 =
            FStar_TypeChecker_TcTerm.tc_check_trivial_guard env1 t k  in
          FStar_TypeChecker_Util.generalize_universes env1 uu____9358  in
        let ed_src =
          FStar_TypeChecker_Env.get_effect_decl env
            sub1.FStar_Syntax_Syntax.source
           in
        let ed_tgt =
          FStar_TypeChecker_Env.get_effect_decl env
            sub1.FStar_Syntax_Syntax.target
           in
        let uu____9361 =
          (FStar_All.pipe_right ed_src FStar_Syntax_Util.is_layered) ||
            (FStar_All.pipe_right ed_tgt FStar_Syntax_Util.is_layered)
           in
        if uu____9361
        then tc_layered_lift env sub1
        else
          (let uu____9368 =
             let uu____9375 =
               FStar_TypeChecker_Env.lookup_effect_lid env
                 sub1.FStar_Syntax_Syntax.source
                in
             monad_signature env sub1.FStar_Syntax_Syntax.source uu____9375
              in
           match uu____9368 with
           | (a,wp_a_src) ->
               let uu____9382 =
                 let uu____9389 =
                   FStar_TypeChecker_Env.lookup_effect_lid env
                     sub1.FStar_Syntax_Syntax.target
                    in
                 monad_signature env sub1.FStar_Syntax_Syntax.target
                   uu____9389
                  in
               (match uu____9382 with
                | (b,wp_b_tgt) ->
                    let wp_a_tgt =
                      let uu____9397 =
                        let uu____9400 =
                          let uu____9401 =
                            let uu____9408 = FStar_Syntax_Syntax.bv_to_name a
                               in
                            (b, uu____9408)  in
                          FStar_Syntax_Syntax.NT uu____9401  in
                        [uu____9400]  in
                      FStar_Syntax_Subst.subst uu____9397 wp_b_tgt  in
                    let expected_k =
                      let uu____9416 =
                        let uu____9425 = FStar_Syntax_Syntax.mk_binder a  in
                        let uu____9432 =
                          let uu____9441 =
                            FStar_Syntax_Syntax.null_binder wp_a_src  in
                          [uu____9441]  in
                        uu____9425 :: uu____9432  in
                      let uu____9466 = FStar_Syntax_Syntax.mk_Total wp_a_tgt
                         in
                      FStar_Syntax_Util.arrow uu____9416 uu____9466  in
                    let repr_type eff_name a1 wp =
                      (let uu____9488 =
                         let uu____9490 =
                           FStar_TypeChecker_Env.is_reifiable_effect env
                             eff_name
                            in
                         Prims.op_Negation uu____9490  in
                       if uu____9488
                       then
                         let uu____9493 =
                           let uu____9499 =
                             let uu____9501 =
                               FStar_Ident.string_of_lid eff_name  in
                             FStar_Util.format1 "Effect %s cannot be reified"
                               uu____9501
                              in
                           (FStar_Errors.Fatal_EffectCannotBeReified,
                             uu____9499)
                            in
                         let uu____9505 = FStar_TypeChecker_Env.get_range env
                            in
                         FStar_Errors.raise_error uu____9493 uu____9505
                       else ());
                      (let uu____9508 =
                         FStar_TypeChecker_Env.effect_decl_opt env eff_name
                          in
                       match uu____9508 with
                       | FStar_Pervasives_Native.None  ->
                           failwith
                             "internal error: reifiable effect has no decl?"
                       | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                           let repr =
                             let uu____9541 =
                               let uu____9542 =
                                 FStar_All.pipe_right ed
                                   FStar_Syntax_Util.get_eff_repr
                                  in
                               FStar_All.pipe_right uu____9542
                                 FStar_Util.must
                                in
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               [FStar_Syntax_Syntax.U_unknown] env ed
                               uu____9541
                              in
                           let uu____9549 =
                             FStar_TypeChecker_Env.get_range env  in
                           let uu____9550 =
                             let uu____9557 =
                               let uu____9558 =
                                 let uu____9575 =
                                   let uu____9586 =
                                     FStar_Syntax_Syntax.as_arg a1  in
                                   let uu____9595 =
                                     let uu____9606 =
                                       FStar_Syntax_Syntax.as_arg wp  in
                                     [uu____9606]  in
                                   uu____9586 :: uu____9595  in
                                 (repr, uu____9575)  in
                               FStar_Syntax_Syntax.Tm_app uu____9558  in
                             FStar_Syntax_Syntax.mk uu____9557  in
                           uu____9550 FStar_Pervasives_Native.None uu____9549)
                       in
                    let uu____9651 =
                      match ((sub1.FStar_Syntax_Syntax.lift),
                              (sub1.FStar_Syntax_Syntax.lift_wp))
                      with
                      | (FStar_Pervasives_Native.None
                         ,FStar_Pervasives_Native.None ) ->
                          failwith "Impossible (parser)"
                      | (lift,FStar_Pervasives_Native.Some (uvs,lift_wp)) ->
                          let uu____9824 =
                            if (FStar_List.length uvs) > Prims.int_zero
                            then
                              let uu____9835 =
                                FStar_Syntax_Subst.univ_var_opening uvs  in
                              match uu____9835 with
                              | (usubst,uvs1) ->
                                  let uu____9858 =
                                    FStar_TypeChecker_Env.push_univ_vars env
                                      uvs1
                                     in
                                  let uu____9859 =
                                    FStar_Syntax_Subst.subst usubst lift_wp
                                     in
                                  (uu____9858, uu____9859)
                            else (env, lift_wp)  in
                          (match uu____9824 with
                           | (env1,lift_wp1) ->
                               let lift_wp2 =
                                 if (FStar_List.length uvs) = Prims.int_zero
                                 then check_and_gen1 env1 lift_wp1 expected_k
                                 else
                                   (let lift_wp2 =
                                      FStar_TypeChecker_TcTerm.tc_check_trivial_guard
                                        env1 lift_wp1 expected_k
                                       in
                                    let uu____9909 =
                                      FStar_Syntax_Subst.close_univ_vars uvs
                                        lift_wp2
                                       in
                                    (uvs, uu____9909))
                                  in
                               (lift, lift_wp2))
                      | (FStar_Pervasives_Native.Some
                         (what,lift),FStar_Pervasives_Native.None ) ->
                          let uu____9980 =
                            if (FStar_List.length what) > Prims.int_zero
                            then
                              let uu____9995 =
                                FStar_Syntax_Subst.univ_var_opening what  in
                              match uu____9995 with
                              | (usubst,uvs) ->
                                  let uu____10020 =
                                    FStar_Syntax_Subst.subst usubst lift  in
                                  (uvs, uu____10020)
                            else ([], lift)  in
                          (match uu____9980 with
                           | (uvs,lift1) ->
                               ((let uu____10056 =
                                   FStar_TypeChecker_Env.debug env
                                     (FStar_Options.Other "ED")
                                    in
                                 if uu____10056
                                 then
                                   let uu____10060 =
                                     FStar_Syntax_Print.term_to_string lift1
                                      in
                                   FStar_Util.print1 "Lift for free : %s\n"
                                     uu____10060
                                 else ());
                                (let dmff_env =
                                   FStar_TypeChecker_DMFF.empty env
                                     (FStar_TypeChecker_TcTerm.tc_constant
                                        env FStar_Range.dummyRange)
                                    in
                                 let uu____10066 =
                                   let uu____10073 =
                                     FStar_TypeChecker_Env.push_univ_vars env
                                       uvs
                                      in
                                   FStar_TypeChecker_TcTerm.tc_term
                                     uu____10073 lift1
                                    in
                                 match uu____10066 with
                                 | (lift2,comp,uu____10098) ->
                                     let uu____10099 =
                                       FStar_TypeChecker_DMFF.star_expr
                                         dmff_env lift2
                                        in
                                     (match uu____10099 with
                                      | (uu____10128,lift_wp,lift_elab) ->
                                          let lift_wp1 =
                                            FStar_TypeChecker_DMFF.recheck_debug
                                              "lift-wp" env lift_wp
                                             in
                                          let lift_elab1 =
                                            FStar_TypeChecker_DMFF.recheck_debug
                                              "lift-elab" env lift_elab
                                             in
                                          if
                                            (FStar_List.length uvs) =
                                              Prims.int_zero
                                          then
                                            let uu____10160 =
                                              let uu____10171 =
                                                FStar_TypeChecker_Util.generalize_universes
                                                  env lift_elab1
                                                 in
                                              FStar_Pervasives_Native.Some
                                                uu____10171
                                               in
                                            let uu____10188 =
                                              FStar_TypeChecker_Util.generalize_universes
                                                env lift_wp1
                                               in
                                            (uu____10160, uu____10188)
                                          else
                                            (let uu____10217 =
                                               let uu____10228 =
                                                 let uu____10237 =
                                                   FStar_Syntax_Subst.close_univ_vars
                                                     uvs lift_elab1
                                                    in
                                                 (uvs, uu____10237)  in
                                               FStar_Pervasives_Native.Some
                                                 uu____10228
                                                in
                                             let uu____10252 =
                                               let uu____10261 =
                                                 FStar_Syntax_Subst.close_univ_vars
                                                   uvs lift_wp1
                                                  in
                                               (uvs, uu____10261)  in
                                             (uu____10217, uu____10252))))))
                       in
                    (match uu____9651 with
                     | (lift,lift_wp) ->
                         let env1 =
                           let uu___1084_10325 = env  in
                           {
                             FStar_TypeChecker_Env.solver =
                               (uu___1084_10325.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (uu___1084_10325.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (uu___1084_10325.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (uu___1084_10325.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_sig =
                               (uu___1084_10325.FStar_TypeChecker_Env.gamma_sig);
                             FStar_TypeChecker_Env.gamma_cache =
                               (uu___1084_10325.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (uu___1084_10325.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (uu___1084_10325.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (uu___1084_10325.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.attrtab =
                               (uu___1084_10325.FStar_TypeChecker_Env.attrtab);
                             FStar_TypeChecker_Env.instantiate_imp =
                               (uu___1084_10325.FStar_TypeChecker_Env.instantiate_imp);
                             FStar_TypeChecker_Env.effects =
                               (uu___1084_10325.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               (uu___1084_10325.FStar_TypeChecker_Env.generalize);
                             FStar_TypeChecker_Env.letrecs =
                               (uu___1084_10325.FStar_TypeChecker_Env.letrecs);
                             FStar_TypeChecker_Env.top_level =
                               (uu___1084_10325.FStar_TypeChecker_Env.top_level);
                             FStar_TypeChecker_Env.check_uvars =
                               (uu___1084_10325.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq =
                               (uu___1084_10325.FStar_TypeChecker_Env.use_eq);
                             FStar_TypeChecker_Env.use_eq_strict =
                               (uu___1084_10325.FStar_TypeChecker_Env.use_eq_strict);
                             FStar_TypeChecker_Env.is_iface =
                               (uu___1084_10325.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (uu___1084_10325.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax = true;
                             FStar_TypeChecker_Env.lax_universes =
                               (uu___1084_10325.FStar_TypeChecker_Env.lax_universes);
                             FStar_TypeChecker_Env.phase1 =
                               (uu___1084_10325.FStar_TypeChecker_Env.phase1);
                             FStar_TypeChecker_Env.failhard =
                               (uu___1084_10325.FStar_TypeChecker_Env.failhard);
                             FStar_TypeChecker_Env.nosynth =
                               (uu___1084_10325.FStar_TypeChecker_Env.nosynth);
                             FStar_TypeChecker_Env.uvar_subtyping =
                               (uu___1084_10325.FStar_TypeChecker_Env.uvar_subtyping);
                             FStar_TypeChecker_Env.tc_term =
                               (uu___1084_10325.FStar_TypeChecker_Env.tc_term);
                             FStar_TypeChecker_Env.type_of =
                               (uu___1084_10325.FStar_TypeChecker_Env.type_of);
                             FStar_TypeChecker_Env.universe_of =
                               (uu___1084_10325.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.check_type_of =
                               (uu___1084_10325.FStar_TypeChecker_Env.check_type_of);
                             FStar_TypeChecker_Env.use_bv_sorts =
                               (uu___1084_10325.FStar_TypeChecker_Env.use_bv_sorts);
                             FStar_TypeChecker_Env.qtbl_name_and_index =
                               (uu___1084_10325.FStar_TypeChecker_Env.qtbl_name_and_index);
                             FStar_TypeChecker_Env.normalized_eff_names =
                               (uu___1084_10325.FStar_TypeChecker_Env.normalized_eff_names);
                             FStar_TypeChecker_Env.fv_delta_depths =
                               (uu___1084_10325.FStar_TypeChecker_Env.fv_delta_depths);
                             FStar_TypeChecker_Env.proof_ns =
                               (uu___1084_10325.FStar_TypeChecker_Env.proof_ns);
                             FStar_TypeChecker_Env.synth_hook =
                               (uu___1084_10325.FStar_TypeChecker_Env.synth_hook);
                             FStar_TypeChecker_Env.try_solve_implicits_hook =
                               (uu___1084_10325.FStar_TypeChecker_Env.try_solve_implicits_hook);
                             FStar_TypeChecker_Env.splice =
                               (uu___1084_10325.FStar_TypeChecker_Env.splice);
                             FStar_TypeChecker_Env.mpreprocess =
                               (uu___1084_10325.FStar_TypeChecker_Env.mpreprocess);
                             FStar_TypeChecker_Env.postprocess =
                               (uu___1084_10325.FStar_TypeChecker_Env.postprocess);
                             FStar_TypeChecker_Env.is_native_tactic =
                               (uu___1084_10325.FStar_TypeChecker_Env.is_native_tactic);
                             FStar_TypeChecker_Env.identifier_info =
                               (uu___1084_10325.FStar_TypeChecker_Env.identifier_info);
                             FStar_TypeChecker_Env.tc_hooks =
                               (uu___1084_10325.FStar_TypeChecker_Env.tc_hooks);
                             FStar_TypeChecker_Env.dsenv =
                               (uu___1084_10325.FStar_TypeChecker_Env.dsenv);
                             FStar_TypeChecker_Env.nbe =
                               (uu___1084_10325.FStar_TypeChecker_Env.nbe);
                             FStar_TypeChecker_Env.strict_args_tab =
                               (uu___1084_10325.FStar_TypeChecker_Env.strict_args_tab);
                             FStar_TypeChecker_Env.erasable_types_tab =
                               (uu___1084_10325.FStar_TypeChecker_Env.erasable_types_tab)
                           }  in
                         let lift1 =
                           match lift with
                           | FStar_Pervasives_Native.None  ->
                               FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some (uvs,lift1) ->
                               let uu____10358 =
                                 let uu____10363 =
                                   FStar_Syntax_Subst.univ_var_opening uvs
                                    in
                                 match uu____10363 with
                                 | (usubst,uvs1) ->
                                     let uu____10386 =
                                       FStar_TypeChecker_Env.push_univ_vars
                                         env1 uvs1
                                        in
                                     let uu____10387 =
                                       FStar_Syntax_Subst.subst usubst lift1
                                        in
                                     (uu____10386, uu____10387)
                                  in
                               (match uu____10358 with
                                | (env2,lift2) ->
                                    let uu____10392 =
                                      let uu____10399 =
                                        FStar_TypeChecker_Env.lookup_effect_lid
                                          env2
                                          sub1.FStar_Syntax_Syntax.source
                                         in
                                      monad_signature env2
                                        sub1.FStar_Syntax_Syntax.source
                                        uu____10399
                                       in
                                    (match uu____10392 with
                                     | (a1,wp_a_src1) ->
                                         let wp_a =
                                           FStar_Syntax_Syntax.new_bv
                                             FStar_Pervasives_Native.None
                                             wp_a_src1
                                            in
                                         let a_typ =
                                           FStar_Syntax_Syntax.bv_to_name a1
                                            in
                                         let wp_a_typ =
                                           FStar_Syntax_Syntax.bv_to_name
                                             wp_a
                                            in
                                         let repr_f =
                                           repr_type
                                             sub1.FStar_Syntax_Syntax.source
                                             a_typ wp_a_typ
                                            in
                                         let repr_result =
                                           let lift_wp1 =
                                             FStar_TypeChecker_Normalize.normalize
                                               [FStar_TypeChecker_Env.EraseUniverses;
                                               FStar_TypeChecker_Env.AllowUnboundUniverses]
                                               env2
                                               (FStar_Pervasives_Native.snd
                                                  lift_wp)
                                              in
                                           let lift_wp_a =
                                             let uu____10425 =
                                               FStar_TypeChecker_Env.get_range
                                                 env2
                                                in
                                             let uu____10426 =
                                               let uu____10433 =
                                                 let uu____10434 =
                                                   let uu____10451 =
                                                     let uu____10462 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         a_typ
                                                        in
                                                     let uu____10471 =
                                                       let uu____10482 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           wp_a_typ
                                                          in
                                                       [uu____10482]  in
                                                     uu____10462 ::
                                                       uu____10471
                                                      in
                                                   (lift_wp1, uu____10451)
                                                    in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____10434
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____10433
                                                in
                                             uu____10426
                                               FStar_Pervasives_Native.None
                                               uu____10425
                                              in
                                           repr_type
                                             sub1.FStar_Syntax_Syntax.target
                                             a_typ lift_wp_a
                                            in
                                         let expected_k1 =
                                           let uu____10530 =
                                             let uu____10539 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 a1
                                                in
                                             let uu____10546 =
                                               let uu____10555 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   wp_a
                                                  in
                                               let uu____10562 =
                                                 let uu____10571 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     repr_f
                                                    in
                                                 [uu____10571]  in
                                               uu____10555 :: uu____10562  in
                                             uu____10539 :: uu____10546  in
                                           let uu____10602 =
                                             FStar_Syntax_Syntax.mk_Total
                                               repr_result
                                              in
                                           FStar_Syntax_Util.arrow
                                             uu____10530 uu____10602
                                            in
                                         let uu____10605 =
                                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                             env2 expected_k1
                                            in
                                         (match uu____10605 with
                                          | (expected_k2,uu____10615,uu____10616)
                                              ->
                                              let lift3 =
                                                if
                                                  (FStar_List.length uvs) =
                                                    Prims.int_zero
                                                then
                                                  check_and_gen1 env2 lift2
                                                    expected_k2
                                                else
                                                  (let lift3 =
                                                     FStar_TypeChecker_TcTerm.tc_check_trivial_guard
                                                       env2 lift2 expected_k2
                                                      in
                                                   let uu____10624 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs lift3
                                                      in
                                                   (uvs, uu____10624))
                                                 in
                                              FStar_Pervasives_Native.Some
                                                lift3)))
                            in
                         ((let uu____10632 =
                             let uu____10634 =
                               let uu____10636 =
                                 FStar_All.pipe_right lift_wp
                                   FStar_Pervasives_Native.fst
                                  in
                               FStar_All.pipe_right uu____10636
                                 FStar_List.length
                                in
                             uu____10634 <> Prims.int_one  in
                           if uu____10632
                           then
                             let uu____10659 =
                               let uu____10665 =
                                 let uu____10667 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.source
                                    in
                                 let uu____10669 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.target
                                    in
                                 let uu____10671 =
                                   let uu____10673 =
                                     let uu____10675 =
                                       FStar_All.pipe_right lift_wp
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_All.pipe_right uu____10675
                                       FStar_List.length
                                      in
                                   FStar_All.pipe_right uu____10673
                                     FStar_Util.string_of_int
                                    in
                                 FStar_Util.format3
                                   "Sub effect wp must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____10667 uu____10669 uu____10671
                                  in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____10665)
                                in
                             FStar_Errors.raise_error uu____10659 r
                           else ());
                          (let uu____10702 =
                             (FStar_Util.is_some lift1) &&
                               (let uu____10705 =
                                  let uu____10707 =
                                    let uu____10710 =
                                      FStar_All.pipe_right lift1
                                        FStar_Util.must
                                       in
                                    FStar_All.pipe_right uu____10710
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____10707
                                    FStar_List.length
                                   in
                                uu____10705 <> Prims.int_one)
                              in
                           if uu____10702
                           then
                             let uu____10749 =
                               let uu____10755 =
                                 let uu____10757 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.source
                                    in
                                 let uu____10759 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.target
                                    in
                                 let uu____10761 =
                                   let uu____10763 =
                                     let uu____10765 =
                                       let uu____10768 =
                                         FStar_All.pipe_right lift1
                                           FStar_Util.must
                                          in
                                       FStar_All.pipe_right uu____10768
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_All.pipe_right uu____10765
                                       FStar_List.length
                                      in
                                   FStar_All.pipe_right uu____10763
                                     FStar_Util.string_of_int
                                    in
                                 FStar_Util.format3
                                   "Sub effect lift must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____10757 uu____10759 uu____10761
                                  in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____10755)
                                in
                             FStar_Errors.raise_error uu____10749 r
                           else ());
                          (let uu___1121_10810 = sub1  in
                           {
                             FStar_Syntax_Syntax.source =
                               (uu___1121_10810.FStar_Syntax_Syntax.source);
                             FStar_Syntax_Syntax.target =
                               (uu___1121_10810.FStar_Syntax_Syntax.target);
                             FStar_Syntax_Syntax.lift_wp =
                               (FStar_Pervasives_Native.Some lift_wp);
                             FStar_Syntax_Syntax.lift = lift1
                           })))))
  
let (tc_effect_abbrev :
  FStar_TypeChecker_Env.env ->
    (FStar_Ident.lident * FStar_Syntax_Syntax.univ_names *
      FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) ->
      FStar_Range.range ->
        (FStar_Ident.lident * FStar_Syntax_Syntax.univ_names *
          FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp))
  =
  fun env  ->
    fun uu____10841  ->
      fun r  ->
        match uu____10841 with
        | (lid,uvs,tps,c) ->
            let env0 = env  in
            let uu____10864 =
              if (FStar_List.length uvs) = Prims.int_zero
              then (env, uvs, tps, c)
              else
                (let uu____10892 = FStar_Syntax_Subst.univ_var_opening uvs
                    in
                 match uu____10892 with
                 | (usubst,uvs1) ->
                     let tps1 = FStar_Syntax_Subst.subst_binders usubst tps
                        in
                     let c1 =
                       let uu____10923 =
                         FStar_Syntax_Subst.shift_subst
                           (FStar_List.length tps1) usubst
                          in
                       FStar_Syntax_Subst.subst_comp uu____10923 c  in
                     let uu____10932 =
                       FStar_TypeChecker_Env.push_univ_vars env uvs1  in
                     (uu____10932, uvs1, tps1, c1))
               in
            (match uu____10864 with
             | (env1,uvs1,tps1,c1) ->
                 let env2 = FStar_TypeChecker_Env.set_range env1 r  in
                 let uu____10952 = FStar_Syntax_Subst.open_comp tps1 c1  in
                 (match uu____10952 with
                  | (tps2,c2) ->
                      let uu____10967 =
                        FStar_TypeChecker_TcTerm.tc_tparams env2 tps2  in
                      (match uu____10967 with
                       | (tps3,env3,us) ->
                           let uu____10985 =
                             FStar_TypeChecker_TcTerm.tc_comp env3 c2  in
                           (match uu____10985 with
                            | (c3,u,g) ->
                                (FStar_TypeChecker_Rel.force_trivial_guard
                                   env3 g;
                                 (let expected_result_typ =
                                    match tps3 with
                                    | (x,uu____11011)::uu____11012 ->
                                        FStar_Syntax_Syntax.bv_to_name x
                                    | uu____11031 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                            "Effect abbreviations must bind at least the result type")
                                          r
                                     in
                                  let def_result_typ =
                                    FStar_Syntax_Util.comp_result c3  in
                                  let uu____11039 =
                                    let uu____11041 =
                                      FStar_TypeChecker_Rel.teq_nosmt_force
                                        env3 expected_result_typ
                                        def_result_typ
                                       in
                                    Prims.op_Negation uu____11041  in
                                  if uu____11039
                                  then
                                    let uu____11044 =
                                      let uu____11050 =
                                        let uu____11052 =
                                          FStar_Syntax_Print.term_to_string
                                            expected_result_typ
                                           in
                                        let uu____11054 =
                                          FStar_Syntax_Print.term_to_string
                                            def_result_typ
                                           in
                                        FStar_Util.format2
                                          "Result type of effect abbreviation `%s` does not match the result type of its definition `%s`"
                                          uu____11052 uu____11054
                                         in
                                      (FStar_Errors.Fatal_EffectAbbreviationResultTypeMismatch,
                                        uu____11050)
                                       in
                                    FStar_Errors.raise_error uu____11044 r
                                  else ());
                                 (let tps4 =
                                    FStar_Syntax_Subst.close_binders tps3  in
                                  let c4 =
                                    FStar_Syntax_Subst.close_comp tps4 c3  in
                                  let uu____11062 =
                                    let uu____11063 =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_arrow
                                           (tps4, c4))
                                        FStar_Pervasives_Native.None r
                                       in
                                    FStar_TypeChecker_Util.generalize_universes
                                      env0 uu____11063
                                     in
                                  match uu____11062 with
                                  | (uvs2,t) ->
                                      let uu____11092 =
                                        let uu____11097 =
                                          let uu____11110 =
                                            let uu____11111 =
                                              FStar_Syntax_Subst.compress t
                                               in
                                            uu____11111.FStar_Syntax_Syntax.n
                                             in
                                          (tps4, uu____11110)  in
                                        match uu____11097 with
                                        | ([],FStar_Syntax_Syntax.Tm_arrow
                                           (uu____11126,c5)) -> ([], c5)
                                        | (uu____11168,FStar_Syntax_Syntax.Tm_arrow
                                           (tps5,c5)) -> (tps5, c5)
                                        | uu____11207 ->
                                            failwith
                                              "Impossible (t is an arrow)"
                                         in
                                      (match uu____11092 with
                                       | (tps5,c5) ->
                                           (if
                                              (FStar_List.length uvs2) <>
                                                Prims.int_one
                                            then
                                              (let uu____11239 =
                                                 FStar_Syntax_Subst.open_univ_vars
                                                   uvs2 t
                                                  in
                                               match uu____11239 with
                                               | (uu____11244,t1) ->
                                                   let uu____11246 =
                                                     let uu____11252 =
                                                       let uu____11254 =
                                                         FStar_Syntax_Print.lid_to_string
                                                           lid
                                                          in
                                                       let uu____11256 =
                                                         FStar_All.pipe_right
                                                           (FStar_List.length
                                                              uvs2)
                                                           FStar_Util.string_of_int
                                                          in
                                                       let uu____11260 =
                                                         FStar_Syntax_Print.term_to_string
                                                           t1
                                                          in
                                                       FStar_Util.format3
                                                         "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                         uu____11254
                                                         uu____11256
                                                         uu____11260
                                                        in
                                                     (FStar_Errors.Fatal_TooManyUniverse,
                                                       uu____11252)
                                                      in
                                                   FStar_Errors.raise_error
                                                     uu____11246 r)
                                            else ();
                                            (lid, uvs2, tps5, c5)))))))))
  
let (tc_polymonadic_bind :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Ident.lident ->
        FStar_Ident.lident ->
          FStar_Syntax_Syntax.tscheme ->
            (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.tscheme))
  =
  fun env  ->
    fun m  ->
      fun n1  ->
        fun p  ->
          fun ts  ->
            let eff_name =
              let uu____11302 = FStar_Ident.string_of_lid m  in
              let uu____11304 = FStar_Ident.string_of_lid n1  in
              let uu____11306 = FStar_Ident.string_of_lid p  in
              FStar_Util.format3 "(%s, %s) |> %s)" uu____11302 uu____11304
                uu____11306
               in
            let r = (FStar_Pervasives_Native.snd ts).FStar_Syntax_Syntax.pos
               in
            let uu____11314 =
              check_and_gen env eff_name "polymonadic_bind"
                (Prims.of_int (2)) ts
               in
            match uu____11314 with
            | (us,t,ty) ->
                let uu____11330 = FStar_Syntax_Subst.open_univ_vars us ty  in
                (match uu____11330 with
                 | (us1,ty1) ->
                     let env1 = FStar_TypeChecker_Env.push_univ_vars env us1
                        in
                     (check_no_subtyping_for_layered_combinator env1 ty1
                        FStar_Pervasives_Native.None;
                      (let uu____11343 =
                         let uu____11348 = FStar_Syntax_Util.type_u ()  in
                         FStar_All.pipe_right uu____11348
                           (fun uu____11365  ->
                              match uu____11365 with
                              | (t1,u) ->
                                  let uu____11376 =
                                    let uu____11377 =
                                      FStar_Syntax_Syntax.gen_bv "a"
                                        FStar_Pervasives_Native.None t1
                                       in
                                    FStar_All.pipe_right uu____11377
                                      FStar_Syntax_Syntax.mk_binder
                                     in
                                  (uu____11376, u))
                          in
                       match uu____11343 with
                       | (a,u_a) ->
                           let uu____11385 =
                             let uu____11390 = FStar_Syntax_Util.type_u ()
                                in
                             FStar_All.pipe_right uu____11390
                               (fun uu____11407  ->
                                  match uu____11407 with
                                  | (t1,u) ->
                                      let uu____11418 =
                                        let uu____11419 =
                                          FStar_Syntax_Syntax.gen_bv "b"
                                            FStar_Pervasives_Native.None t1
                                           in
                                        FStar_All.pipe_right uu____11419
                                          FStar_Syntax_Syntax.mk_binder
                                         in
                                      (uu____11418, u))
                              in
                           (match uu____11385 with
                            | (b,u_b) ->
                                let rest_bs =
                                  let uu____11436 =
                                    let uu____11437 =
                                      FStar_Syntax_Subst.compress ty1  in
                                    uu____11437.FStar_Syntax_Syntax.n  in
                                  match uu____11436 with
                                  | FStar_Syntax_Syntax.Tm_arrow
                                      (bs,uu____11449) when
                                      (FStar_List.length bs) >=
                                        (Prims.of_int (4))
                                      ->
                                      let uu____11477 =
                                        FStar_Syntax_Subst.open_binders bs
                                         in
                                      (match uu____11477 with
                                       | (a',uu____11487)::(b',uu____11489)::bs1
                                           ->
                                           let uu____11519 =
                                             let uu____11520 =
                                               FStar_All.pipe_right bs1
                                                 (FStar_List.splitAt
                                                    ((FStar_List.length bs1)
                                                       - (Prims.of_int (2))))
                                                in
                                             FStar_All.pipe_right uu____11520
                                               FStar_Pervasives_Native.fst
                                              in
                                           let uu____11586 =
                                             let uu____11599 =
                                               let uu____11602 =
                                                 let uu____11603 =
                                                   let uu____11610 =
                                                     let uu____11613 =
                                                       FStar_All.pipe_right a
                                                         FStar_Pervasives_Native.fst
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____11613
                                                       FStar_Syntax_Syntax.bv_to_name
                                                      in
                                                   (a', uu____11610)  in
                                                 FStar_Syntax_Syntax.NT
                                                   uu____11603
                                                  in
                                               let uu____11626 =
                                                 let uu____11629 =
                                                   let uu____11630 =
                                                     let uu____11637 =
                                                       let uu____11640 =
                                                         FStar_All.pipe_right
                                                           b
                                                           FStar_Pervasives_Native.fst
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____11640
                                                         FStar_Syntax_Syntax.bv_to_name
                                                        in
                                                     (b', uu____11637)  in
                                                   FStar_Syntax_Syntax.NT
                                                     uu____11630
                                                    in
                                                 [uu____11629]  in
                                               uu____11602 :: uu____11626  in
                                             FStar_Syntax_Subst.subst_binders
                                               uu____11599
                                              in
                                           FStar_All.pipe_right uu____11519
                                             uu____11586)
                                  | uu____11661 ->
                                      let uu____11662 =
                                        let uu____11668 =
                                          let uu____11670 =
                                            FStar_Syntax_Print.tag_of_term
                                              ty1
                                             in
                                          let uu____11672 =
                                            FStar_Syntax_Print.term_to_string
                                              ty1
                                             in
                                          FStar_Util.format3
                                            "Type of %s is not an arrow with >= 4 binders (%s::%s)"
                                            eff_name uu____11670 uu____11672
                                           in
                                        (FStar_Errors.Fatal_UnexpectedEffect,
                                          uu____11668)
                                         in
                                      FStar_Errors.raise_error uu____11662 r
                                   in
                                let bs = a :: b :: rest_bs  in
                                let uu____11705 =
                                  let uu____11716 =
                                    let uu____11721 =
                                      FStar_TypeChecker_Env.push_binders env1
                                        bs
                                       in
                                    let uu____11722 =
                                      let uu____11723 =
                                        FStar_All.pipe_right a
                                          FStar_Pervasives_Native.fst
                                         in
                                      FStar_All.pipe_right uu____11723
                                        FStar_Syntax_Syntax.bv_to_name
                                       in
                                    FStar_TypeChecker_Util.fresh_effect_repr_en
                                      uu____11721 r m u_a uu____11722
                                     in
                                  match uu____11716 with
                                  | (repr,g) ->
                                      let uu____11744 =
                                        let uu____11751 =
                                          FStar_Syntax_Syntax.gen_bv "f"
                                            FStar_Pervasives_Native.None repr
                                           in
                                        FStar_All.pipe_right uu____11751
                                          FStar_Syntax_Syntax.mk_binder
                                         in
                                      (uu____11744, g)
                                   in
                                (match uu____11705 with
                                 | (f,guard_f) ->
                                     let uu____11783 =
                                       let x_a =
                                         let uu____11801 =
                                           let uu____11802 =
                                             let uu____11803 =
                                               FStar_All.pipe_right a
                                                 FStar_Pervasives_Native.fst
                                                in
                                             FStar_All.pipe_right uu____11803
                                               FStar_Syntax_Syntax.bv_to_name
                                              in
                                           FStar_Syntax_Syntax.gen_bv "x"
                                             FStar_Pervasives_Native.None
                                             uu____11802
                                            in
                                         FStar_All.pipe_right uu____11801
                                           FStar_Syntax_Syntax.mk_binder
                                          in
                                       let uu____11819 =
                                         let uu____11824 =
                                           FStar_TypeChecker_Env.push_binders
                                             env1
                                             (FStar_List.append bs [x_a])
                                            in
                                         let uu____11843 =
                                           let uu____11844 =
                                             FStar_All.pipe_right b
                                               FStar_Pervasives_Native.fst
                                              in
                                           FStar_All.pipe_right uu____11844
                                             FStar_Syntax_Syntax.bv_to_name
                                            in
                                         FStar_TypeChecker_Util.fresh_effect_repr_en
                                           uu____11824 r n1 u_b uu____11843
                                          in
                                       match uu____11819 with
                                       | (repr,g) ->
                                           let uu____11865 =
                                             let uu____11872 =
                                               let uu____11873 =
                                                 let uu____11874 =
                                                   let uu____11877 =
                                                     let uu____11880 =
                                                       FStar_TypeChecker_Env.new_u_univ
                                                         ()
                                                        in
                                                     FStar_Pervasives_Native.Some
                                                       uu____11880
                                                      in
                                                   FStar_Syntax_Syntax.mk_Total'
                                                     repr uu____11877
                                                    in
                                                 FStar_Syntax_Util.arrow
                                                   [x_a] uu____11874
                                                  in
                                               FStar_Syntax_Syntax.gen_bv "g"
                                                 FStar_Pervasives_Native.None
                                                 uu____11873
                                                in
                                             FStar_All.pipe_right uu____11872
                                               FStar_Syntax_Syntax.mk_binder
                                              in
                                           (uu____11865, g)
                                        in
                                     (match uu____11783 with
                                      | (g,guard_g) ->
                                          let uu____11924 =
                                            let uu____11929 =
                                              FStar_TypeChecker_Env.push_binders
                                                env1 bs
                                               in
                                            let uu____11930 =
                                              let uu____11931 =
                                                FStar_All.pipe_right b
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              FStar_All.pipe_right
                                                uu____11931
                                                FStar_Syntax_Syntax.bv_to_name
                                               in
                                            FStar_TypeChecker_Util.fresh_effect_repr_en
                                              uu____11929 r p u_b uu____11930
                                             in
                                          (match uu____11924 with
                                           | (repr,guard_repr) ->
                                               let uu____11946 =
                                                 let uu____11951 =
                                                   FStar_TypeChecker_Env.push_binders
                                                     env1 bs
                                                    in
                                                 let uu____11952 =
                                                   FStar_Util.format1
                                                     "implicit for pure_wp in checking %s"
                                                     eff_name
                                                    in
                                                 pure_wp_uvar uu____11951
                                                   repr uu____11952 r
                                                  in
                                               (match uu____11946 with
                                                | (pure_wp_uvar1,g_pure_wp_uvar)
                                                    ->
                                                    let k =
                                                      let uu____11964 =
                                                        let uu____11967 =
                                                          let uu____11968 =
                                                            let uu____11969 =
                                                              FStar_TypeChecker_Env.new_u_univ
                                                                ()
                                                               in
                                                            [uu____11969]  in
                                                          let uu____11970 =
                                                            let uu____11981 =
                                                              FStar_All.pipe_right
                                                                pure_wp_uvar1
                                                                FStar_Syntax_Syntax.as_arg
                                                               in
                                                            [uu____11981]  in
                                                          {
                                                            FStar_Syntax_Syntax.comp_univs
                                                              = uu____11968;
                                                            FStar_Syntax_Syntax.effect_name
                                                              =
                                                              FStar_Parser_Const.effect_PURE_lid;
                                                            FStar_Syntax_Syntax.result_typ
                                                              = repr;
                                                            FStar_Syntax_Syntax.effect_args
                                                              = uu____11970;
                                                            FStar_Syntax_Syntax.flags
                                                              = []
                                                          }  in
                                                        FStar_Syntax_Syntax.mk_Comp
                                                          uu____11967
                                                         in
                                                      FStar_Syntax_Util.arrow
                                                        (FStar_List.append bs
                                                           [f; g])
                                                        uu____11964
                                                       in
                                                    let guard_eq =
                                                      FStar_TypeChecker_Rel.teq
                                                        env1 ty1 k
                                                       in
                                                    (FStar_List.iter
                                                       (FStar_TypeChecker_Rel.force_trivial_guard
                                                          env1)
                                                       [guard_f;
                                                       guard_g;
                                                       guard_repr;
                                                       g_pure_wp_uvar;
                                                       guard_eq];
                                                     (let uu____12041 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env1)
                                                          FStar_Options.Extreme
                                                         in
                                                      if uu____12041
                                                      then
                                                        let uu____12045 =
                                                          FStar_Syntax_Print.tscheme_to_string
                                                            (us1, t)
                                                           in
                                                        let uu____12051 =
                                                          FStar_Syntax_Print.tscheme_to_string
                                                            (us1, k)
                                                           in
                                                        FStar_Util.print3
                                                          "Polymonadic bind %s after typechecking (%s::%s)\n"
                                                          eff_name
                                                          uu____12045
                                                          uu____12051
                                                      else ());
                                                     (let uu____12061 =
                                                        let uu____12067 =
                                                          FStar_Util.format1
                                                            "Polymonadic binds (%s in this case) is a bleeding edge F* feature;it is subject to some redesign in the future. Please keep us informed (on github etc.) about how you are using it"
                                                            eff_name
                                                           in
                                                        (FStar_Errors.Warning_BleedingEdge_Feature,
                                                          uu____12067)
                                                         in
                                                      FStar_Errors.log_issue
                                                        r uu____12061);
                                                     (let uu____12071 =
                                                        let uu____12072 =
                                                          let uu____12075 =
                                                            FStar_All.pipe_right
                                                              k
                                                              (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                                 env1)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____12075
                                                            (FStar_Syntax_Subst.close_univ_vars
                                                               us1)
                                                           in
                                                        (us1, uu____12072)
                                                         in
                                                      ((us1, t), uu____12071)))))))))))
  
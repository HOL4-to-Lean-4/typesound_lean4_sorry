/-
  Helper lemmas for TypeSysProps (prover B): combined induction principles for the
  mutually inductive typing relations.
-/
import LeanTypeSound.BAux1

open HOL4

namespace BAux

theorem type_p_ind {tvs : Nat} {tenv : type_env}
    {M1 : pat → sem_t → List (varN × sem_t) → Prop}
    {M2 : List pat → List sem_t → List (varN × sem_t) → Prop}
    (pany : ∀ t, check_freevars tvs [] t → M1 .Pany t [])
    (pvar : ∀ n t, check_freevars tvs [] t → M1 (.Pvar n) t [(n, t)])
    (plit_int : ∀ n, M1 (.Plit (.IntLit n)) Tint [])
    (plit_char : ∀ c, M1 (.Plit (.Char c)) Tchar [])
    (plit_str : ∀ s, M1 (.Plit (.StrLit s)) Tstring [])
    (plit_word8 : ∀ w, M1 (.Plit (.Word8 w)) Tword8 [])
    (plit_word64 : ∀ w, M1 (.Plit (.Word64 w)) Tword64 [])
    (pcon_some : ∀ cn ps ts' tvs' ts tn bindings,
      (∀ t', t' ∈ ts' → check_freevars tvs [] t') →
      ts'.length = tvs'.length →
      type_ps tvs tenv ps (ts.map (type_subst (Finmap.alist_to_fmap (tvs'.zip ts')))) bindings →
      nsLookup tenv.c cn = some (tvs', ts, tn) →
      M2 ps (ts.map (type_subst (Finmap.alist_to_fmap (tvs'.zip ts')))) bindings →
      M1 (.Pcon (some cn) ps) (.Tapp ts' tn) bindings)
    (pcon_none : ∀ ps ts bindings,
      type_ps tvs tenv ps ts bindings → M2 ps ts bindings →
      M1 (.Pcon none ps) (Ttup ts) bindings)
    (pref : ∀ p t bindings,
      type_p tvs tenv p t bindings → M1 p t bindings →
      M1 (.Pref p) (Tref t) bindings)
    (pas : ∀ p t bindings v_,
      type_p tvs tenv p t bindings → M1 p t bindings →
      M1 (.Pas p v_) t (bindings ++ [(v_, t)]))
    (ptannot : ∀ p t bindings,
      check_freevars_ast [] t →
      check_type_names tenv.t t →
      type_p tvs tenv p (type_name_subst tenv.t t) bindings →
      M1 p (type_name_subst tenv.t t) bindings →
      M1 (.Ptannot p t) (type_name_subst tenv.t t) bindings)
    (nil : M2 [] [] [])
    (cons : ∀ p t bindings ps ts bindings',
      type_p tvs tenv p t bindings →
      type_ps tvs tenv ps ts bindings' →
      M1 p t bindings → M2 ps ts bindings' →
      M2 (p :: ps) (t :: ts) (bindings' ++ bindings)) :
    (∀ p t b, type_p tvs tenv p t b → M1 p t b) ∧
    (∀ ps ts b, type_ps tvs tenv ps ts b → M2 ps ts b) :=
  ⟨fun _ _ _ h => type_p.rec (motive_1 := fun p t b _ => M1 p t b)
      (motive_2 := fun ps ts b _ => M2 ps ts b)
      pany pvar plit_int plit_char plit_str plit_word8 plit_word64 pcon_some pcon_none pref pas
      ptannot nil cons h,
   fun _ _ _ h => type_ps.rec (motive_1 := fun p t b _ => M1 p t b)
      (motive_2 := fun ps ts b _ => M2 ps ts b)
      pany pvar plit_int plit_char plit_str plit_word8 plit_word64 pcon_some pcon_none pref pas
      ptannot nil cons h⟩

theorem type_e_ind {tenv : type_env}
    {M1 : tenv_val_exp → exp → sem_t → Prop}
    {M2 : tenv_val_exp → List exp → List sem_t → Prop}
    {M3 : tenv_val_exp → List (varN × varN × exp) → List (varN × sem_t) → Prop}
    (lit_int : ∀ tenvE n, M1 tenvE (.Lit (.IntLit n)) Tint)
    (lit_char : ∀ tenvE c, M1 tenvE (.Lit (.Char c)) Tchar)
    (lit_str : ∀ tenvE s, M1 tenvE (.Lit (.StrLit s)) Tstring)
    (lit_word8 : ∀ tenvE w, M1 tenvE (.Lit (.Word8 w)) Tword8)
    (lit_word64 : ∀ tenvE w, M1 tenvE (.Lit (.Word64 w)) Tword64)
    (lit_float64 : ∀ tenvE w, M1 tenvE (.Lit (.Float64 w)) Tdouble)
    (raise : ∀ tenvE e t,
      check_freevars (num_tvs tenvE) [] t →
      type_e tenv tenvE e Texn → M1 tenvE e Texn →
      M1 tenvE (.Raise e) t)
    (handle : ∀ tenvE e t pes (bindings_of : (pat × exp) → List (varN × sem_t)),
      type_e tenv tenvE e t → pes ≠ [] →
      (∀ pe, pe ∈ pes → ALL_DISTINCT (pat_bindings pe.1 [])) →
      (∀ pe, pe ∈ pes → type_p (num_tvs tenvE) tenv pe.1 Texn (bindings_of pe)) →
      (∀ pe, pe ∈ pes → type_e tenv (bind_var_list 0 (bindings_of pe) tenvE) pe.2 t) →
      M1 tenvE e t →
      (∀ pe, pe ∈ pes → M1 (bind_var_list 0 (bindings_of pe) tenvE) pe.2 t) →
      M1 tenvE (.Handle e pes) t)
    (con_some : ∀ tenvE cn es ts' tvs ts tn,
      (∀ t', t' ∈ ts' → check_freevars (num_tvs tenvE) [] t') →
      tvs.length = ts'.length →
      type_es tenv tenvE es (ts.map (type_subst (Finmap.alist_to_fmap (tvs.zip ts')))) →
      nsLookup tenv.c cn = some (tvs, ts, tn) →
      M2 tenvE es (ts.map (type_subst (Finmap.alist_to_fmap (tvs.zip ts')))) →
      M1 tenvE (.Con (some cn) es) (.Tapp ts' tn))
    (con_none : ∀ tenvE es ts,
      type_es tenv tenvE es ts → M2 tenvE es ts →
      M1 tenvE (.Con none es) (Ttup ts))
    (var : ∀ tenvE n tvs t targs,
      tvs = targs.length →
      (∀ ta, ta ∈ targs → check_freevars (num_tvs tenvE) [] ta) →
      lookup_var n tenvE tenv = some (tvs, t) →
      M1 tenvE (.Var n) (deBruijn_subst 0 targs t))
    (fun_ : ∀ tenvE n e t1 t2,
      check_freevars (num_tvs tenvE) [] t1 →
      type_e tenv (.Bind_name n 0 t1 tenvE) e t2 →
      M1 (.Bind_name n 0 t1 tenvE) e t2 →
      M1 tenvE (.Fun n e) (Tfn t1 t2))
    (app : ∀ tenvE o_ es ts t,
      type_es tenv tenvE es ts →
      type_op o_ ts t →
      check_freevars (num_tvs tenvE) [] t →
      M2 tenvE es ts →
      M1 tenvE (.App o_ es) t)
    (log : ∀ tenvE l e1 e2,
      type_e tenv tenvE e1 Tbool →
      type_e tenv tenvE e2 Tbool →
      M1 tenvE e1 Tbool → M1 tenvE e2 Tbool →
      M1 tenvE (.Log l e1 e2) Tbool)
    (if_ : ∀ tenvE e1 e2 e3 t,
      type_e tenv tenvE e1 Tbool →
      type_e tenv tenvE e2 t →
      type_e tenv tenvE e3 t →
      M1 tenvE e1 Tbool → M1 tenvE e2 t → M1 tenvE e3 t →
      M1 tenvE (.If e1 e2 e3) t)
    (mat : ∀ tenvE e t1 t2 pes (bindings_of : (pat × exp) → List (varN × sem_t)),
      type_e tenv tenvE e t1 → pes ≠ [] →
      (∀ pe, pe ∈ pes → ALL_DISTINCT (pat_bindings pe.1 [])) →
      (∀ pe, pe ∈ pes → type_p (num_tvs tenvE) tenv pe.1 t1 (bindings_of pe)) →
      (∀ pe, pe ∈ pes → type_e tenv (bind_var_list 0 (bindings_of pe) tenvE) pe.2 t2) →
      M1 tenvE e t1 →
      (∀ pe, pe ∈ pes → M1 (bind_var_list 0 (bindings_of pe) tenvE) pe.2 t2) →
      M1 tenvE (.Mat e pes) t2)
    (let_ : ∀ tenvE n e1 t1 e2 t2,
      type_e tenv tenvE e1 t1 →
      type_e tenv (opt_bind_name n 0 t1 tenvE) e2 t2 →
      M1 tenvE e1 t1 → M1 (opt_bind_name n 0 t1 tenvE) e2 t2 →
      M1 tenvE (.Let n e1 e2) t2)
    (letrec : ∀ tenvE funs bindings e t,
      type_funs tenv (bind_var_list 0 bindings tenvE) funs bindings →
      type_e tenv (bind_var_list 0 bindings tenvE) e t →
      M3 (bind_var_list 0 bindings tenvE) funs bindings →
      M1 (bind_var_list 0 bindings tenvE) e t →
      M1 tenvE (.Letrec funs e) t)
    (tannot : ∀ tenvE e t,
      check_freevars_ast [] t →
      check_type_names tenv.t t →
      type_e tenv tenvE e (type_name_subst tenv.t t) →
      M1 tenvE e (type_name_subst tenv.t t) →
      M1 tenvE (.Tannot e t) (type_name_subst tenv.t t))
    (lannot : ∀ tenvE e t l,
      type_e tenv tenvE e t → M1 tenvE e t →
      M1 tenvE (.Lannot e l) t)
    (es_nil : ∀ tenvE, M2 tenvE [] [])
    (es_cons : ∀ tenvE e t es ts,
      type_e tenv tenvE e t →
      type_es tenv tenvE es ts →
      M1 tenvE e t → M2 tenvE es ts →
      M2 tenvE (e :: es) (t :: ts))
    (funs_nil : ∀ tenvE, M3 tenvE [] [])
    (funs_cons : ∀ tenvE fn n e t1 t2 funs bindings,
      check_freevars (num_tvs tenvE) [] (Tfn t1 t2) →
      type_e tenv (.Bind_name n 0 t1 tenvE) e t2 →
      type_funs tenv tenvE funs bindings →
      ALOOKUP bindings fn = none →
      M1 (.Bind_name n 0 t1 tenvE) e t2 → M3 tenvE funs bindings →
      M3 tenvE ((fn, n, e) :: funs) ((fn, Tfn t1 t2) :: bindings)) :
    (∀ tenvE e t, type_e tenv tenvE e t → M1 tenvE e t) ∧
    (∀ tenvE es ts, type_es tenv tenvE es ts → M2 tenvE es ts) ∧
    (∀ tenvE funs env, type_funs tenv tenvE funs env → M3 tenvE funs env) :=
  ⟨fun _ _ _ h => type_e.rec (motive_1 := fun tenvE e t _ => M1 tenvE e t)
      (motive_2 := fun tenvE es ts _ => M2 tenvE es ts)
      (motive_3 := fun tenvE funs env _ => M3 tenvE funs env)
      lit_int lit_char lit_str lit_word8 lit_word64 lit_float64 raise handle con_some con_none
      var fun_ app log if_ mat let_ letrec tannot lannot es_nil es_cons funs_nil funs_cons h,
   fun _ _ _ h => type_es.rec (motive_1 := fun tenvE e t _ => M1 tenvE e t)
      (motive_2 := fun tenvE es ts _ => M2 tenvE es ts)
      (motive_3 := fun tenvE funs env _ => M3 tenvE funs env)
      lit_int lit_char lit_str lit_word8 lit_word64 lit_float64 raise handle con_some con_none
      var fun_ app log if_ mat let_ letrec tannot lannot es_nil es_cons funs_nil funs_cons h,
   fun _ _ _ h => type_funs.rec (motive_1 := fun tenvE e t _ => M1 tenvE e t)
      (motive_2 := fun tenvE es ts _ => M2 tenvE es ts)
      (motive_3 := fun tenvE funs env _ => M3 tenvE funs env)
      lit_int lit_char lit_str lit_word8 lit_word64 lit_float64 raise handle con_some con_none
      var fun_ app log if_ mat let_ letrec tannot lannot es_nil es_cons funs_nil funs_cons h⟩

theorem type_d_ind {extra_checks : Bool}
    {M1 : type_env → dec → Set type_ident → type_env → Prop}
    {M2 : type_env → List dec → Set type_ident → type_env → Prop}
    (hd : ∀ tenv d decls tenv', type_d extra_checks tenv d decls tenv' →
      (∀ mn ds, d = .Dmod mn ds → False) → (∀ lds ds, d = .Dlocal lds ds → False) →
      M1 tenv d decls tenv')
    (dmod : ∀ tenv mn ds decls tenv',
      type_ds extra_checks tenv ds decls tenv' → M2 tenv ds decls tenv' →
      M1 tenv (.Dmod mn ds) decls (tenvLift mn tenv'))
    (dlocal : ∀ tenv lds ds decls1 tenv1 decls2 tenv2,
      type_ds extra_checks tenv lds decls1 tenv1 →
      type_ds extra_checks (extend_dec_tenv tenv1 tenv) ds decls2 tenv2 →
      Set.Disjoint decls1 decls2 →
      M2 tenv lds decls1 tenv1 → M2 (extend_dec_tenv tenv1 tenv) ds decls2 tenv2 →
      M1 tenv (.Dlocal lds ds) (decls1 ∪ decls2) tenv2)
    (nil : ∀ tenv, M2 tenv [] ∅ { v := nsEmpty, c := nsEmpty, t := nsEmpty })
    (cons : ∀ tenv d ds decls1 tenv1 decls2 tenv2,
      type_d extra_checks tenv d decls1 tenv1 →
      type_ds extra_checks (extend_dec_tenv tenv1 tenv) ds decls2 tenv2 →
      Set.Disjoint decls1 decls2 →
      M1 tenv d decls1 tenv1 → M2 (extend_dec_tenv tenv1 tenv) ds decls2 tenv2 →
      M2 tenv (d :: ds) (decls1 ∪ decls2) (extend_dec_tenv tenv2 tenv1)) :
    (∀ tenv d decls tenv', type_d extra_checks tenv d decls tenv' → M1 tenv d decls tenv') ∧
    (∀ tenv ds decls tenv', type_ds extra_checks tenv ds decls tenv' → M2 tenv ds decls tenv') :=
  ⟨fun _ _ _ _ h => type_d.rec (motive_1 := fun tenv d decls tenv' _ => M1 tenv d decls tenv')
      (motive_2 := fun tenv ds decls tenv' _ => M2 tenv ds decls tenv')
      (fun tenv locs p e tvs t bindings a1 a2 a3 a4 a5 =>
        hd _ _ _ _ (type_d.dlet_poly extra_checks tenv locs p e tvs t bindings a1 a2 a3 a4 a5)
          (by intro _ _ h; cases h) (by intro _ _ h; cases h))
      (fun tenv locs p e t bindings a1 a2 a3 a4 =>
        hd _ _ _ _ (type_d.dlet_mono extra_checks tenv locs p e t bindings a1 a2 a3 a4)
          (by intro _ _ h; cases h) (by intro _ _ h; cases h))
      (fun tenv locs funs tvs bindings a1 a2 =>
        hd _ _ _ _ (type_d.dletrec extra_checks tenv locs funs tvs bindings a1 a2)
          (by intro _ _ h; cases h) (by intro _ _ h; cases h))
      (fun tenv locs tdefs tids tenvT a1 a2 a3 a4 a5 =>
        hd _ _ _ _ (type_d.dtype extra_checks tenv locs tdefs tids tenvT a1 a2 a3 a4 a5)
          (by intro _ _ h; cases h) (by intro _ _ h; cases h))
      (fun tenv locs tvs tn t a1 a2 a3 =>
        hd _ _ _ _ (type_d.dtabbrev extra_checks tenv locs tvs tn t a1 a2 a3)
          (by intro _ _ h; cases h) (by intro _ _ h; cases h))
      (fun tenv locs cn ts a1 a2 =>
        hd _ _ _ _ (type_d.dexn extra_checks tenv locs cn ts a1 a2)
          (by intro _ _ h; cases h) (by intro _ _ h; cases h))
      dmod dlocal nil cons h,
   fun _ _ _ _ h => type_ds.rec (motive_1 := fun tenv d decls tenv' _ => M1 tenv d decls tenv')
      (motive_2 := fun tenv ds decls tenv' _ => M2 tenv ds decls tenv')
      (fun tenv locs p e tvs t bindings a1 a2 a3 a4 a5 =>
        hd _ _ _ _ (type_d.dlet_poly extra_checks tenv locs p e tvs t bindings a1 a2 a3 a4 a5)
          (by intro _ _ h; cases h) (by intro _ _ h; cases h))
      (fun tenv locs p e t bindings a1 a2 a3 a4 =>
        hd _ _ _ _ (type_d.dlet_mono extra_checks tenv locs p e t bindings a1 a2 a3 a4)
          (by intro _ _ h; cases h) (by intro _ _ h; cases h))
      (fun tenv locs funs tvs bindings a1 a2 =>
        hd _ _ _ _ (type_d.dletrec extra_checks tenv locs funs tvs bindings a1 a2)
          (by intro _ _ h; cases h) (by intro _ _ h; cases h))
      (fun tenv locs tdefs tids tenvT a1 a2 a3 a4 a5 =>
        hd _ _ _ _ (type_d.dtype extra_checks tenv locs tdefs tids tenvT a1 a2 a3 a4 a5)
          (by intro _ _ h; cases h) (by intro _ _ h; cases h))
      (fun tenv locs tvs tn t a1 a2 a3 =>
        hd _ _ _ _ (type_d.dtabbrev extra_checks tenv locs tvs tn t a1 a2 a3)
          (by intro _ _ h; cases h) (by intro _ _ h; cases h))
      (fun tenv locs cn ts a1 a2 =>
        hd _ _ _ _ (type_d.dexn extra_checks tenv locs cn ts a1 a2)
          (by intro _ _ h; cases h) (by intro _ _ h; cases h))
      dmod dlocal nil cons h⟩

end BAux

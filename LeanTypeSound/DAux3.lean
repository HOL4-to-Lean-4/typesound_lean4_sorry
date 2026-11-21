import LeanTypeSound.DAux2
open HOL4
namespace DAux

theorem fce {ffi : Type} (st : cml_state ffi) (env : sem_env) (es : List exp) :
    fix_clock st (evaluate st env es) = evaluate st env es :=
  (fix_clock_evaluate st env es []).1

theorem ev_nil {ffi : Type} (st : cml_state ffi) (env : sem_env) :
    evaluate st env [] = (st, .Rval []) := by
  rw [evaluate]

theorem ev_lit {ffi : Type} (st : cml_state ffi) (env : sem_env) (l : lit)  :
    evaluate st env [.Lit l] = (st, .Rval [.Litv l]) := by
  rw [evaluate]

theorem ev_raise {ffi : Type} (st : cml_state ffi) (env : sem_env) (e : exp)  :
    evaluate st env [.Raise e] =
    (match evaluate st env [e] with
    | (st', .Rval vs) => (st', .Rerr (.Rraise vs.head!))
    | (st', .Rerr e) => (st', .Rerr e)) := by
  rw [evaluate]; rfl

theorem ev_handle {ffi : Type} (st : cml_state ffi) (env : sem_env) (e : exp) (pes : List (pat × exp)) :
    evaluate st env [.Handle e pes] =
    (match evaluate st env [e] with
    | (st', .Rval v') => (st', .Rval v')
    | (st', .Rerr (.Rraise val_)) =>
      if can_pmatch_all env.c st'.refs (pes.map Prod.fst) val_ then
        evaluate_match st' env val_ pes val_
      else (st', .Rerr (.Rabort .Rtype_error))
    | (st', .Rerr (.Rabort a)) => (st', .Rerr (.Rabort a))) := by
  rw [evaluate]
  split <;> rename_i heq <;> rw [fce] at heq <;> rw [heq]

theorem ev_con {ffi : Type} (st : cml_state ffi) (env : sem_env) (cn : Option (cml_id modN conN)) (es' : List exp) :
    evaluate st env [.Con cn es'] =
    (if do_con_check env.c cn es'.length then
      match evaluate st env es'.reverse with
      | (st', .Rval vs) =>
        match build_conv env.c cn vs.reverse with
        | none => (st', .Rerr (.Rabort .Rtype_error))
        | some v' => (st', .Rval [v'])
      | (st', .Rerr e) => (st', .Rerr e)
    else (st, .Rerr (.Rabort .Rtype_error))) := by
  rw [evaluate]; rfl

theorem ev_var {ffi : Type} (st : cml_state ffi) (env : sem_env) (n : cml_id modN varN) :
    evaluate st env [.Var n] =
    (match nsLookup env.v_ n with
    | none => (st, .Rerr (.Rabort .Rtype_error))
    | some v' => (st, .Rval [v'])) := by
  rw [evaluate]; rfl

theorem ev_fun {ffi : Type} (st : cml_state ffi) (env : sem_env) (x : varN) (e : exp) :
    evaluate st env [.Fun x e] = (st, .Rval [.Closure env x e]) := by
  rw [evaluate]

theorem ev_app_err {ffi : Type} (st : cml_state ffi) (env : sem_env) (o_ : op) (es' : List exp)
    {st' : cml_state ffi} {err : error_result v}
    (h : evaluate st env es'.reverse = (st', .Rerr err)) :
    evaluate st env [.App o_ es'] = (st', .Rerr err) := by
  rw [evaluate]
  split <;> rename_i heq <;> rw [fce, h] at heq <;> cases heq
  rfl

theorem ev_app_funapp {ffi : Type} (st : cml_state ffi) (env : sem_env) (o_ : op) (es' : List exp)
    {st' : cml_state ffi} {vs : List v}
    (h : evaluate st env es'.reverse = (st', .Rval vs)) (hop : getOpClass o_ = .FunApp) :
    evaluate st env [.App o_ es'] =
      (match do_opapp vs.reverse with
        | some (env', e) =>
          if st'.clock == 0 then (st', .Rerr (.Rabort .Rtimeout_error))
          else evaluate (dec_clock st') env' [e]
        | none => (st', .Rerr (.Rabort .Rtype_error))) := by
  rw [evaluate]
  split <;> rename_i heq <;> rw [fce, h] at heq <;> cases heq
  simp only [hop]
  split <;> rename_i h2 <;> simp [h2]

theorem ev_app_simple {ffi : Type} (st : cml_state ffi) (env : sem_env) (o_ : op) (es' : List exp)
    {st' : cml_state ffi} {vs : List v}
    (h : evaluate st env es'.reverse = (st', .Rval vs)) (hop : getOpClass o_ = .Simple) :
    evaluate st env [.App o_ es'] =
      (match do_app (st'.refs, st'.ffi) o_ vs.reverse with
        | none => (st', .Rerr (.Rabort .Rtype_error))
        | some ((refs, ffi_), r) =>
          ({ st' with refs := refs, ffi := ffi_ }, list_result r)) := by
  rw [evaluate]
  split <;> rename_i heq <;> rw [fce, h] at heq <;> cases heq
  simp only [hop]
  rfl

theorem ev_log {ffi : Type} (st : cml_state ffi) (env : sem_env) (l : lop) (e1 e2 : exp) :
    evaluate st env [.Log l e1 e2] =
    (match evaluate st env [e1] with
    | (st', .Rval v1) =>
      match do_log l v1.head! e2 with
      | none => (st', .Rerr (.Rabort .Rtype_error))
      | some (.Exp e) => evaluate st' env [e]
      | some (.Val v') => (st', .Rval [v'])
    | (st', .Rerr e) => (st', .Rerr e)) := by
  rw [evaluate]
  split <;> rename_i heq <;> rw [fce] at heq <;> rw [heq]
  simp only []
  split <;> rename_i h2 <;> rw [h2]

theorem ev_if {ffi : Type} (st : cml_state ffi) (env : sem_env) (e1 e2 e3 : exp) :
    evaluate st env [.If e1 e2 e3] =
    (match evaluate st env [e1] with
    | (st', .Rval v') =>
      match do_if v'.head! e2 e3 with
      | none => (st', .Rerr (.Rabort .Rtype_error))
      | some e => evaluate st' env [e]
    | (st', .Rerr e) => (st', .Rerr e)) := by
  rw [evaluate]
  split <;> rename_i heq <;> rw [fce] at heq <;> rw [heq]
  simp only []
  split <;> rename_i h2 <;> rw [h2]

theorem ev_mat {ffi : Type} (st : cml_state ffi) (env : sem_env) (e : exp) (pes : List (pat × exp)) :
    evaluate st env [.Mat e pes] =
    (match evaluate st env [e] with
    | (st', .Rval v') =>
      if can_pmatch_all env.c st'.refs (pes.map Prod.fst) v'.head! then
        evaluate_match st' env v'.head! pes bind_exn_v
      else (st', .Rerr (.Rabort .Rtype_error))
    | (st', .Rerr e) => (st', .Rerr e)) := by
  rw [evaluate]
  split <;> rename_i heq <;> rw [fce] at heq <;> rw [heq]

theorem ev_let {ffi : Type} (st : cml_state ffi) (env : sem_env) (xo : Option varN) (e1 e2 : exp) :
    evaluate st env [.Let xo e1 e2] =
    (match evaluate st env [e1] with
    | (st', .Rval v') =>
      evaluate st' (.mk (nsOptBind xo v'.head! env.v_) env.c) [e2]
    | (st', .Rerr e) => (st', .Rerr e)) := by
  rw [evaluate]
  split <;> rename_i heq <;> rw [fce] at heq <;> rw [heq]

theorem ev_letrec {ffi : Type} (st : cml_state ffi) (env : sem_env) (funs : List (varN × varN × exp)) (e : exp) :
    evaluate st env [.Letrec funs e] =
    (if ALL_DISTINCT (funs.map fun (x, _, _) => x) then
      evaluate st (.mk (build_rec_env funs env env.v_) env.c) [e]
    else (st, .Rerr (.Rabort .Rtype_error))) := by
  rw [evaluate]

theorem ev_tannot {ffi : Type} (st : cml_state ffi) (env : sem_env) (e : exp) (t : ast_t) :
    evaluate st env [.Tannot e t] = evaluate st env [e] := by
  rw [evaluate]

theorem ev_lannot {ffi : Type} (st : cml_state ffi) (env : sem_env) (e : exp) (l : locs) :
    evaluate st env [.Lannot e l] = evaluate st env [e] := by
  rw [evaluate]

theorem ev_cons {ffi : Type} (st : cml_state ffi) (env : sem_env) (e1 e2 : exp) (es : List exp) :
    evaluate st env (e1 :: e2 :: es) =
    (match evaluate st env [e1] with
    | (st', .Rval v1) =>
      match evaluate st' env (e2 :: es) with
      | (st'', .Rval vs) => (st'', .Rval (v1.head! :: vs))
      | (st'', .Rerr e) => (st'', .Rerr e)
    | (st', .Rerr e) => (st', .Rerr e)) := by
  rw [evaluate]
  split <;> rename_i heq <;> rw [fce] at heq <;> rw [heq] <;> rfl

theorem ev_match_nil {ffi : Type} (st : cml_state ffi) (env : sem_env) (val_ err_v : v) :
    evaluate_match st env val_ [] err_v = (st, .Rerr (.Rraise err_v)) := by
  rw [evaluate_match]

theorem ev_match_cons {ffi : Type} (st : cml_state ffi) (env : sem_env) (val_ err_v : v) (p : pat) (e : exp)
    (pes' : List (pat × exp)) :
    evaluate_match st env val_ ((p, e) :: pes') err_v =
    if ALL_DISTINCT (pat_bindings p []) then
      match pmatch env.c st.refs p val_ [] with
      | .No_match => evaluate_match st env val_ pes' err_v
      | .Match_type_error => (st, .Rerr (.Rabort .Rtype_error))
      | .Match env_v' =>
        evaluate st (.mk (nsAppend (alist_to_ns env_v') env.v_) env.c) [e]
    else (st, .Rerr (.Rabort .Rtype_error)) := by
  rw [evaluate_match]; rfl

def res1 (c : ctMap) (tenvS' : tenv_store) (tvs : Nat) (ts : List sem_t) :
    result (List v) v → Prop
  | .Rval vs => LIST_REL (type_v tvs c tenvS') vs ts
  | .Rerr (.Rraise val_) => type_v 0 c tenvS' val_ Texn
  | .Rerr (.Rabort .Rtimeout_error) => True
  | .Rerr (.Rabort (.Rffi_error _)) => True
  | .Rerr (.Rabort .Rtype_error) => False

def R1 (c : ctMap) (tenvS : tenv_store) (tvs : Nat) (ts : List sem_t) {ffi : Type}
    (st s' : cml_state ffi) (r : result (List v) v) : Prop :=
  ∃ tenvS', type_s c s'.refs tenvS' ∧ ste tenvS tenvS' ∧
    s'.next_type_stamp = st.next_type_stamp ∧ s'.next_exn_stamp = st.next_exn_stamp ∧
    res1 c tenvS' tvs ts r

def envOK (c : ctMap) (tenvS : tenv_store) (env : sem_env) (tenv : type_env)
    (tenvE : tenv_val_exp) : Prop :=
  tenv_ok tenv ∧ tenv_val_exp_ok tenvE ∧ num_tvs tenvE = 0 ∧
  type_all_env c tenvS env { tenv with v := add_tenvE tenvE tenv.v }

def M1 (c : ctMap) {ffi : Type} (st : cml_state ffi) (env : sem_env) (es : List exp) : Prop :=
  ∀ (r : result (List v) v) (s' : cml_state ffi) (tenv : type_env) (tenvE : tenv_val_exp)
    (ts : List sem_t) (tvs : Nat) (tenvS : tenv_store),
    evaluate st env es = (s', r) → envOK c tenvS env tenv tenvE → type_s c st.refs tenvS →
    (tvs ≠ 0 → EVERY is_value es = true) → type_es tenv (bind_tvar tvs tenvE) es ts →
    R1 c tenvS tvs ts st s' r

def M3 (c : ctMap) {ffi : Type} (st : cml_state ffi) (env : sem_env) (val_ : v)
    (pes : List (pat × exp)) (err_v : v) : Prop :=
  ∀ (r : result (List v) v) (s' : cml_state ffi) (tenv : type_env) (tenvE : tenv_val_exp)
    (t1 t2 : sem_t) (tvs : Nat) (tenvS : tenv_store),
    evaluate_match st env val_ pes err_v = (s', r) → envOK c tenvS env tenv tenvE →
    type_s c st.refs tenvS → type_v tvs c tenvS val_ t1 → type_v 0 c tenvS err_v Texn →
    type_pes tvs tvs tenv tenvE pes t1 t2 →
    R1 c tenvS tvs [t2] st s' r

theorem res1_err {c : ctMap} {s : tenv_store} {tvs tvs' : Nat} {ts ts' : List sem_t}
    {e : error_result v} (h : res1 c s tvs ts (.Rerr e)) : res1 c s tvs' ts' (.Rerr e) := by
  cases e with
  | Rraise x => exact h
  | Rabort a => cases a <;> exact h

theorem envOK_weak {c : ctMap} {s s' : tenv_store} {env : sem_env} {tenv : type_env}
    {tenvE : tenv_val_exp} (h : envOK c s env tenv tenvE) (he : ste s s') :
    envOK c s' env tenv tenvE :=
  ⟨h.1, h.2.1, h.2.2.1, type_all_env_weakening c s _ env c s' ⟨weakCT_refl c, ste_weakS he, h.2.2.2⟩⟩

theorem type_v_ste {c : ctMap} {s s' : tenv_store} {tvs : Nat} {x : v} {t : sem_t}
    (h : type_v tvs c s x t) (he : ste s s') : type_v tvs c s' x t :=
  type_v_weakening tvs c s x t h tvs c s' ⟨.inr rfl, weakCT_refl c, ste_weakS he⟩

theorem type_v_ste0 {c : ctMap} {s s' : tenv_store} {tvs : Nat} {x : v} {t : sem_t}
    (h : type_v 0 c s x t) (he : ste s s') : type_v tvs c s' x t :=
  type_v_weakening 0 c s x t h tvs c s' ⟨.inl rfl, weakCT_refl c, ste_weakS he⟩

theorem R1_trans {c : ctMap} {s s1 : tenv_store} {tvs : Nat} {ts : List sem_t} {ffi : Type}
    {st st1 s' : cml_state ffi} {r : result (List v) v}
    (he : ste s s1) (hn1 : st1.next_type_stamp = st.next_type_stamp)
    (hn2 : st1.next_exn_stamp = st.next_exn_stamp)
    (h : R1 c s1 tvs ts st1 s' r) : R1 c s tvs ts st s' r := by
  obtain ⟨s2, h1, h2, h3, h4, h5⟩ := h
  exact ⟨s2, h1, ste_trans he h2, h3.trans hn1, h4.trans hn2, h5⟩

theorem type_es_sing_inv {tenv : type_env} {E : tenv_val_exp} {e : exp} {ts : List sem_t}
    (h : type_es tenv E [e] ts) : ∃ t, ts = [t] ∧ type_e tenv E e t := by
  cases h
  cases ‹type_es _ _ [] _›
  exact ⟨_, rfl, ‹type_e _ _ _ _›⟩

theorem type_es_sing {tenv : type_env} {E : tenv_val_exp} {e : exp} {t : sem_t}
    (h : type_e tenv E e t) : type_es tenv E [e] [t] :=
  .cons _ _ _ _ _ _ h (.nil _ _)

theorem tvs0_of_nonvalue {tvs : Nat} {e : exp} (h : tvs ≠ 0 → EVERY is_value [e] = true)
    (hv : is_value e = false) : tvs = 0 := by
  by_cases h0 : tvs = 0
  · exact h0
  · have := h h0
    simp [EVERY, hv] at this

section
variable {ffi : Type} {c : ctMap}

theorem es_nil {st : cml_state ffi} {env : sem_env} : M1 c st env [] := by
  intro r s' tenv tenvE ts tvs tenvS heval henv hs hval hty
  rw [ev_nil] at heval
  cases heval
  cases hty
  exact ⟨tenvS, hs, ste_refl _, rfl, rfl, .nil⟩

theorem es_lit {st : cml_state ffi} {env : sem_env} {l : lit} : M1 c st env [.Lit l] := by
  intro r s' tenv tenvE ts tvs tenvS heval henv hs hval hty
  rw [ev_lit] at heval
  cases heval
  obtain ⟨t, rfl, hte⟩ := type_es_sing_inv hty
  refine ⟨tenvS, hs, ste_refl _, rfl, rfl, ?_⟩
  cases hte <;> exact .cons _ _ _ _ (by constructor) .nil

theorem es_raise {st : cml_state ffi} {env : sem_env} {e : exp}
    (ih : M1 c st env [e]) : M1 c st env [.Raise e] := by
  intro r s' tenv tenvE ts tvs tenvS heval henv hs hval hty
  have htvs := tvs0_of_nonvalue hval (by simp [is_value])
  subst htvs
  rw [bind_tvar0] at hty
  obtain ⟨t, rfl, hte⟩ := type_es_sing_inv hty
  cases hte
  have he : type_e tenv tenvE e Texn := by assumption
  rw [ev_raise] at heval
  cases h1 : evaluate st env [e] with
  | mk st1 r1 =>
    rw [h1] at heval
    obtain ⟨tenvS1, hs1, hste, hn1, hn2, hres⟩ :=
      ih r1 st1 tenv tenvE [Texn] 0 tenvS h1 henv hs (by simp) (by rw [bind_tvar0]; exact type_es_sing he)
    cases r1 with
    | Rval vs =>
      simp only [] at heval
      cases heval
      obtain ⟨v1, rfl, hv1⟩ := lr1 hres
      exact ⟨tenvS1, hs1, hste, hn1, hn2, hv1⟩
    | Rerr err =>
      simp only [] at heval
      cases heval
      exact ⟨tenvS1, hs1, hste, hn1, hn2, res1_err hres⟩

theorem es_var (hg : good_ctMap c) {st : cml_state ffi} {env : sem_env} {n : cml_id modN varN} :
    M1 c st env [.Var n] := by
  intro r s' tenv tenvE ts tvs tenvS heval henv hs hval hty
  obtain ⟨t, rfl, hte⟩ := type_es_sing_inv hty
  cases hte
  rename_i tvs' t targs htv hf hl
  subst htv
  have hnt : num_tvs (bind_tvar tvs tenvE) = tvs := by
    rw [bind_tvar_rewrites.2.1, henv.2.2.1]; simp
  rw [hnt] at hf
  obtain ⟨val_, hlk, hv⟩ := lookup_var_sound' n tvs tenvE targs t c tenvS env tenv
    ⟨hl, hg.1, henv.2.1, henv.2.2.1, EVERY_iff.mpr (by simpa using hf), henv.2.2.2⟩
  rw [ev_var, hlk] at heval
  cases heval
  exact ⟨tenvS, hs, ste_refl _, rfl, rfl, .cons _ _ _ _ hv .nil⟩

theorem es_fun {st : cml_state ffi} {env : sem_env} {x : varN} {e : exp} :
    M1 c st env [.Fun x e] := by
  intro r s' tenv tenvE ts tvs tenvS heval henv hs hval hty
  obtain ⟨t, rfl, hte⟩ := type_es_sing_inv hty
  cases hte
  rename_i t1 t2 hf he
  have hnt : num_tvs (bind_tvar tvs tenvE) = tvs := by
    rw [bind_tvar_rewrites.2.1, henv.2.2.1]; simp
  rw [hnt] at hf
  rw [ev_fun] at heval
  cases heval
  exact ⟨tenvS, hs, ste_refl _, rfl, rfl,
    .cons _ _ _ _ (type_v_closure_intro henv.1 henv.2.1 henv.2.2.1 henv.2.2.2 hf he) .nil⟩

theorem es_tannot {st : cml_state ffi} {env : sem_env} {e : exp} {a : ast_t}
    (ih : M1 c st env [e]) : M1 c st env [.Tannot e a] := by
  intro r s' tenv tenvE ts tvs tenvS heval henv hs hval hty
  obtain ⟨t, rfl, hte⟩ := type_es_sing_inv hty
  cases hte
  rw [ev_tannot] at heval
  exact ih r s' tenv tenvE _ tvs tenvS heval henv hs
    (by intro h; have := hval h; simpa [EVERY, is_value] using this) (type_es_sing ‹_›)

theorem es_lannot {st : cml_state ffi} {env : sem_env} {e : exp} {a : locs}
    (ih : M1 c st env [e]) : M1 c st env [.Lannot e a] := by
  intro r s' tenv tenvE ts tvs tenvS heval henv hs hval hty
  obtain ⟨t, rfl, hte⟩ := type_es_sing_inv hty
  cases hte
  rw [ev_lannot] at heval
  exact ih r s' tenv tenvE _ tvs tenvS heval henv hs
    (by intro h; have := hval h; simpa [EVERY, is_value] using this) (type_es_sing ‹_›)

theorem es_cons {st : cml_state ffi} {env : sem_env} {e1 e2 : exp} {es : List exp}
    (ih1 : M1 c st env [e1])
    (ih2 : ∀ st' vs, evaluate st env [e1] = (st', .Rval vs) → M1 c st' env (e2 :: es)) :
    M1 c st env (e1 :: e2 :: es) := by
  intro r s' tenv tenvE ts tvs tenvS heval henv hs hval hty
  cases hty
  rename_i t1 ts hte1 htes
  rw [ev_cons] at heval
  cases h1 : evaluate st env [e1] with
  | mk st1 r1 =>
    rw [h1] at heval
    obtain ⟨tenvS1, hs1, hste, hn1, hn2, hres⟩ :=
      ih1 r1 st1 tenv tenvE [t1] tvs tenvS h1 henv hs
        (by intro h; have := hval h; simp [EVERY] at this ⊢; exact this.1) (type_es_sing hte1)
    cases r1 with
    | Rval vs =>
      simp only [] at heval
      obtain ⟨v1, rfl, hv1⟩ := lr1 hres
      cases h2 : evaluate st1 env (e2 :: es) with
      | mk st2 r2 =>
        rw [h2] at heval
        obtain ⟨tenvS2, hs2, hste2, hm1, hm2, hres2⟩ :=
          ih2 st1 [v1] h1 r2 st2 tenv tenvE ts tvs tenvS1 h2 (envOK_weak henv hste) hs1
            (by intro h; have := hval h; simp [EVERY] at this ⊢; exact this.2) htes
        cases r2 with
        | Rval vs2 =>
          simp only [] at heval
          cases heval
          exact ⟨tenvS2, hs2, ste_trans hste hste2, hm1.trans hn1, hm2.trans hn2,
            .cons _ _ _ _ (type_v_ste hv1 hste2) hres2⟩
        | Rerr err =>
          simp only [] at heval
          cases heval
          exact ⟨tenvS2, hs2, ste_trans hste hste2, hm1.trans hn1, hm2.trans hn2, res1_err hres2⟩
    | Rerr err =>
      simp only [] at heval
      cases heval
      exact ⟨tenvS1, hs1, hste, hn1, hn2, res1_err hres⟩

end

theorem type_op_simple {o_ : op} {ts : List sem_t} {t : sem_t} (h : type_op o_ ts t)
    (hne : o_ ≠ .Opapp) : getOpClass o_ = .Simple := by
  cases o_ <;> first
    | rfl
    | exact absurd rfl hne
    | (exfalso; rw [type_op_cases_thm] at h; simp at h)

theorem do_log_Boolv (l : lop) (b : Bool) (e : exp) :
    do_log l (Boolv b) e = some (.Exp e) ∨ do_log l (Boolv b) e = some (.Val (Boolv b)) := by
  cases l <;> cases b <;> simp [do_log, Boolv_beq]

theorem do_if_Boolv (b : Bool) (e1 e2 : exp) :
    do_if (Boolv b) e1 e2 = some e1 ∨ do_if (Boolv b) e1 e2 = some e2 := by
  cases b <;> simp [do_if, Boolv_beq]

theorem type_v_conv_none_intro {tvs : Nat} {c : ctMap} {s : tenv_store} {vs : List v}
    {ts : List sem_t} (h : LIST_REL (type_v tvs c s) vs ts) :
    type_v tvs c s (.Conv none vs) (Ttup ts) :=
  .conv_none _ _ _ _ _ (LIST_REL_length h) (LIST_REL_getElem h)

theorem is_value_con {cn : Option (cml_id modN conN)} {es : List exp}
    (h : is_value (.Con cn es) = true) : ∀ e, e ∈ es → is_value e = true := by
  simpa [is_value] using h

theorem R1_tvs0 {c : ctMap} {s : tenv_store} {tvs : Nat} {ts : List sem_t} {ffi : Type}
    {st s' : cml_state ffi} {r : result (List v) v}
    (h : R1 c s 0 ts st s' r) : R1 c s tvs ts st s' r := by
  obtain ⟨s2, h1, h2, h3, h4, h5⟩ := h
  refine ⟨s2, h1, h2, h3, h4, ?_⟩
  cases r with
  | Rval vs => exact LIST_REL_mono (fun x y hxy => type_v_ste0 hxy (ste_refl _)) h5
  | Rerr e => exact res1_err h5

theorem envOK_bvl {c : ctMap} {s : tenv_store} {env : sem_env} {tenv : type_env}
    {tenvE : tenv_val_exp} {tvs : Nat} {bs : List (varN × v)} {tbs : List (varN × sem_t)}
    (h : envOK c s env tenv tenvE) (hok : tenv_val_exp_ok (bind_var_list tvs tbs tenvE))
    (hrel : LIST_REL (bindR tvs c s) bs tbs) :
    envOK c s (.mk (nsAppend (alist_to_ns bs) env.v_) env.c) tenv (bind_var_list tvs tbs tenvE) := by
  refine ⟨h.1, hok, by rw [num_tvs_bind_var_list]; exact h.2.2.1, h.2.2.2.1, ?_⟩
  show nsAll2 _ (nsAppend (alist_to_ns bs) env.v_) (add_tenvE (bind_var_list tvs tbs tenvE) tenv.v)
  rw [add_tenvE_bvl, nsAppend_to_nsBindList]
  apply nsAll2_nsBindList
  refine ⟨?_, h.2.2.2.2⟩
  rw [LIST_REL_map_right]
  exact LIST_REL_mono (fun a b hab => hab) hrel

theorem envOK_optbind {c : ctMap} {s : tenv_store} {env : sem_env} {tenv : type_env}
    {tenvE : tenv_val_exp} {xo : Option varN} {v1 : v} {t1 : sem_t}
    (h : envOK c s env tenv tenvE) (hv : type_v 0 c s v1 t1) (hf : check_freevars 0 [] t1) :
    envOK c s (.mk (nsOptBind xo v1 env.v_) env.c) tenv (opt_bind_name xo 0 t1 tenvE) := by
  cases xo with
  | none => exact h
  | some x =>
    refine ⟨h.1, ⟨by simpa [h.2.2.1] using hf, h.2.1⟩, h.2.2.1, h.2.2.2.1, ?_⟩
    exact nsAll2_nsBind _ x v1 (0, t1) _ _ ⟨hv, h.2.2.2.2⟩

theorem pmatch_ok {c : ctMap} {s : tenv_store} {tenv : type_env} {cenv : env_ctor}
    {st : store v} {val_ : v} {t1 : sem_t} {pes : List (pat × exp)}
    {bindings_of : (pat × exp) → List (varN × sem_t)}
    (hc : ctMap_ok c) (hall : nsAll2 (type_ctor c) cenv tenv.c) (hv : type_v 0 c s val_ t1)
    (hs : type_s c st s)
    (hp : ∀ pe, pe ∈ pes → type_p 0 tenv pe.1 t1 (bindings_of pe)) :
    can_pmatch_all cenv st (pes.map Prod.fst) val_ = true := by
  rw [can_pmatch_all_EVERY]
  intro p hmem
  simp only [List.mem_map] at hmem
  obtain ⟨pe, hpe, rfl⟩ := hmem
  rcases pat_sound1 (hp pe hpe) cenv st val_ [] c [] s hc hall hv hs .nil with h | ⟨b, h, _⟩ <;>
    rw [h] <;> simp

section
variable {ffi : Type} {c : ctMap}

theorem es_let {st : cml_state ffi} {env : sem_env} {xo : Option varN} {e1 e2 : exp}
    (ih1 : M1 c st env [e1])
    (ih2 : ∀ st' vs, evaluate st env [e1] = (st', .Rval vs) →
      M1 c st' (.mk (nsOptBind xo vs.head! env.v_) env.c) [e2]) :
    M1 c st env [.Let xo e1 e2] := by
  intro r s' tenv tenvE ts tvs tenvS heval henv hs hval hty
  have htvs := tvs0_of_nonvalue hval (by simp [is_value])
  subst htvs
  rw [bind_tvar0] at hty
  obtain ⟨t, rfl, hte⟩ := type_es_sing_inv hty
  cases hte
  rename_i t1 hte1 hte2
  rw [ev_let] at heval
  cases h1 : evaluate st env [e1] with
  | mk st1 r1 =>
    rw [h1] at heval
    obtain ⟨tenvS1, hs1, hste, hn1, hn2, hres⟩ :=
      ih1 r1 st1 tenv tenvE [t1] 0 tenvS h1 henv hs (by simp) (by rw [bind_tvar0]; exact type_es_sing hte1)
    cases r1 with
    | Rval vs =>
      simp only [] at heval
      obtain ⟨v1, rfl, hv1⟩ := lr1 hres
      have hf : check_freevars 0 [] t1 := by
        have := type_e_freevars.1 tenv tenvE e1 t1 hte1 ⟨henv.2.1, henv.1.1⟩
        rwa [henv.2.2.1] at this
      have henv2 := envOK_optbind (xo := xo) (envOK_weak henv hste) hv1 hf
      exact R1_trans hste hn1 hn2
        (ih2 st1 [v1] h1 r s' tenv (opt_bind_name xo 0 t1 tenvE) [t] 0 tenvS1 heval henv2 hs1
          (by simp) (by rw [bind_tvar0]; exact type_es_sing hte2))
    | Rerr err =>
      simp only [] at heval
      cases heval
      exact ⟨tenvS1, hs1, hste, hn1, hn2, res1_err hres⟩

theorem es_letrec {st : cml_state ffi} {env : sem_env} {funs : List (varN × varN × exp)} {e : exp}
    (ih : M1 c st (.mk (build_rec_env funs env env.v_) env.c) [e]) :
    M1 c st env [.Letrec funs e] := by
  intro r s' tenv tenvE ts tvs tenvS heval henv hs hval hty
  have htvs := tvs0_of_nonvalue hval (by simp [is_value])
  subst htvs
  rw [bind_tvar0] at hty
  obtain ⟨t, rfl, hte⟩ := type_es_sing_inv hty
  cases hte
  rename_i bindings hfuns hte
  have hd := type_funs_distinct _ _ _ _ hfuns
  rw [ev_letrec, if_pos hd] at heval
  have hrel := type_recfun_env' funs c tenvS 0 tenv tenvE env bindings
    ⟨henv.1, henv.2.2.2, henv.2.1, henv.2.2.1, by rw [bind_tvar0]; exact hfuns, hd⟩
  rw [LIST_REL_map_right] at hrel
  have henv2 : envOK c tenvS (.mk (build_rec_env funs env env.v_) env.c) tenv
      (bind_var_list 0 bindings tenvE) := by
    rw [build_rec_env_merge]
    exact envOK_bvl (tvs := 0) (tbs := bindings) henv
      (tenv_val_exp_ok_bvl_funs funs bindings tenv bindings tenv.v tenvE ⟨hfuns, henv.2.1⟩)
      (LIST_REL_mono (fun a b hab => hab) hrel)
  exact ih r s' tenv (bind_var_list 0 bindings tenvE) [t] 0 tenvS heval henv2 hs (by simp)
    (by rw [bind_tvar0]; exact type_es_sing hte)

theorem es_log (hg : good_ctMap c) {st : cml_state ffi} {env : sem_env} {l : lop} {e1 e2 : exp}
    (ih1 : M1 c st env [e1])
    (ih2 : ∀ st' vs, evaluate st env [e1] = (st', .Rval vs) → M1 c st' env [e2]) :
    M1 c st env [.Log l e1 e2] := by
  intro r s' tenv tenvE ts tvs tenvS heval henv hs hval hty
  have htvs := tvs0_of_nonvalue hval (by simp [is_value])
  subst htvs
  rw [bind_tvar0] at hty
  obtain ⟨t, rfl, hte⟩ := type_es_sing_inv hty
  cases hte
  rename_i hte1 hte2
  rw [ev_log] at heval
  cases h1 : evaluate st env [e1] with
  | mk st1 r1 =>
    rw [h1] at heval
    obtain ⟨tenvS1, hs1, hste, hn1, hn2, hres⟩ :=
      ih1 r1 st1 tenv tenvE [Tbool] 0 tenvS h1 henv hs (by simp) (by rw [bind_tvar0]; exact type_es_sing hte1)
    cases r1 with
    | Rval vs =>
      simp only [] at heval
      obtain ⟨v1, rfl, hv1⟩ := lr1 hres
      obtain ⟨b, rfl⟩ := canon_Tbool hv1 hg.1 hg.2.1
      have hh : ([Boolv b] : List v).head! = Boolv b := rfl
      rw [hh] at heval
      rcases do_log_Boolv l b e2 with h | h
      · rw [h] at heval
        simp only [] at heval
        exact R1_trans hste hn1 hn2
          (ih2 st1 [Boolv b] h1 r s' tenv tenvE [Tbool] 0 tenvS1 heval (envOK_weak henv hste) hs1
            (by simp) (by rw [bind_tvar0]; exact type_es_sing hte2))
      · rw [h] at heval
        simp only [] at heval
        cases heval
        exact ⟨tenvS1, hs1, hste, hn1, hn2, .cons _ _ _ _ hv1 .nil⟩
    | Rerr err =>
      simp only [] at heval
      cases heval
      exact ⟨tenvS1, hs1, hste, hn1, hn2, res1_err hres⟩

theorem es_if (hg : good_ctMap c) {st : cml_state ffi} {env : sem_env} {e1 e2 e3 : exp}
    (ih1 : M1 c st env [e1])
    (ih2 : ∀ st' vs, evaluate st env [e1] = (st', .Rval vs) → M1 c st' env [e2])
    (ih3 : ∀ st' vs, evaluate st env [e1] = (st', .Rval vs) → M1 c st' env [e3]) :
    M1 c st env [.If e1 e2 e3] := by
  intro r s' tenv tenvE ts tvs tenvS heval henv hs hval hty
  have htvs := tvs0_of_nonvalue hval (by simp [is_value])
  subst htvs
  rw [bind_tvar0] at hty
  obtain ⟨t, rfl, hte⟩ := type_es_sing_inv hty
  cases hte
  rename_i hte1 hte2 hte3
  rw [ev_if] at heval
  cases h1 : evaluate st env [e1] with
  | mk st1 r1 =>
    rw [h1] at heval
    obtain ⟨tenvS1, hs1, hste, hn1, hn2, hres⟩ :=
      ih1 r1 st1 tenv tenvE [Tbool] 0 tenvS h1 henv hs (by simp) (by rw [bind_tvar0]; exact type_es_sing hte1)
    cases r1 with
    | Rval vs =>
      simp only [] at heval
      obtain ⟨v1, rfl, hv1⟩ := lr1 hres
      obtain ⟨b, rfl⟩ := canon_Tbool hv1 hg.1 hg.2.1
      have hh : ([Boolv b] : List v).head! = Boolv b := rfl
      rw [hh] at heval
      rcases do_if_Boolv b e2 e3 with h | h
      · rw [h] at heval
        simp only [] at heval
        exact R1_trans hste hn1 hn2
          (ih2 st1 [Boolv b] h1 r s' tenv tenvE [t] 0 tenvS1 heval (envOK_weak henv hste) hs1
            (by simp) (by rw [bind_tvar0]; exact type_es_sing hte2))
      · rw [h] at heval
        simp only [] at heval
        exact R1_trans hste hn1 hn2
          (ih3 st1 [Boolv b] h1 r s' tenv tenvE [t] 0 tenvS1 heval (envOK_weak henv hste) hs1
            (by simp) (by rw [bind_tvar0]; exact type_es_sing hte3))
    | Rerr err =>
      simp only [] at heval
      cases heval
      exact ⟨tenvS1, hs1, hste, hn1, hn2, res1_err hres⟩

theorem es_mat (hg : good_ctMap c) {st : cml_state ffi} {env : sem_env} {e : exp}
    {pes : List (pat × exp)}
    (ih1 : M1 c st env [e])
    (ih3 : ∀ st' vs, evaluate st env [e] = (st', .Rval vs) → M3 c st' env vs.head! pes bind_exn_v) :
    M1 c st env [.Mat e pes] := by
  intro r s' tenv tenvE ts tvs tenvS heval henv hs hval hty
  have htvs := tvs0_of_nonvalue hval (by simp [is_value])
  subst htvs
  rw [bind_tvar0] at hty
  obtain ⟨t, rfl, hte⟩ := type_es_sing_inv hty
  cases hte
  rename_i t1 bindings_of hte1 hne hd hp hb
  rw [henv.2.2.1] at hp
  rw [ev_mat] at heval
  cases h1 : evaluate st env [e] with
  | mk st1 r1 =>
    rw [h1] at heval
    obtain ⟨tenvS1, hs1, hste, hn1, hn2, hres⟩ :=
      ih1 r1 st1 tenv tenvE [t1] 0 tenvS h1 henv hs (by simp) (by rw [bind_tvar0]; exact type_es_sing hte1)
    cases r1 with
    | Rval vs =>
      simp only [] at heval
      obtain ⟨v1, rfl, hv1⟩ := lr1 hres
      have hh : ([v1] : List v).head! = v1 := rfl
      rw [hh] at heval
      have henv1 := envOK_weak henv hste
      rw [if_pos (pmatch_ok (tenv := tenv) (cenv := env.c) hg.1 henv1.2.2.2.1 hv1 hs1 hp)] at heval
      exact R1_trans hste hn1 hn2
        (ih3 st1 [v1] h1 r s' tenv tenvE t1 t 0 tenvS1 heval henv1 hs1 hv1
          (type_v_exn' 0 c tenvS1 hg.2.2.1).2.2.1
          (fun pe hm => ⟨bindings_of pe, hd pe hm, hp pe hm, hb pe hm⟩))
    | Rerr err =>
      simp only [] at heval
      cases heval
      exact ⟨tenvS1, hs1, hste, hn1, hn2, res1_err hres⟩

theorem es_handle (hg : good_ctMap c) {st : cml_state ffi} {env : sem_env} {e : exp}
    {pes : List (pat × exp)}
    (ih1 : M1 c st env [e])
    (ih3 : ∀ st' val_, evaluate st env [e] = (st', .Rerr (.Rraise val_)) →
      M3 c st' env val_ pes val_) :
    M1 c st env [.Handle e pes] := by
  intro r s' tenv tenvE ts tvs tenvS heval henv hs hval hty
  have htvs := tvs0_of_nonvalue hval (by simp [is_value])
  subst htvs
  rw [bind_tvar0] at hty
  obtain ⟨t, rfl, hte⟩ := type_es_sing_inv hty
  cases hte
  rename_i bindings_of hne hd hp hte1 hb
  rw [henv.2.2.1] at hp
  rw [ev_handle] at heval
  cases h1 : evaluate st env [e] with
  | mk st1 r1 =>
    rw [h1] at heval
    obtain ⟨tenvS1, hs1, hste, hn1, hn2, hres⟩ :=
      ih1 r1 st1 tenv tenvE [t] 0 tenvS h1 henv hs (by simp) (by rw [bind_tvar0]; exact type_es_sing hte1)
    cases r1 with
    | Rval vs =>
      simp only [] at heval
      cases heval
      exact ⟨tenvS1, hs1, hste, hn1, hn2, hres⟩
    | Rerr err =>
      cases err with
      | Rraise val_ =>
        simp only [] at heval
        have hv1 : type_v 0 c tenvS1 val_ Texn := hres
        have henv1 := envOK_weak henv hste
        rw [if_pos (pmatch_ok (tenv := tenv) (cenv := env.c) hg.1 henv1.2.2.2.1 hv1 hs1 hp)] at heval
        exact R1_trans hste hn1 hn2
          (ih3 st1 val_ h1 r s' tenv tenvE Texn t 0 tenvS1 heval henv1 hs1 hv1 hv1
            (fun pe hm => ⟨bindings_of pe, hd pe hm, hp pe hm, hb pe hm⟩))
      | Rabort a =>
        simp only [] at heval
        cases heval
        exact ⟨tenvS1, hs1, hste, hn1, hn2, res1_err hres⟩

theorem em_nil {st : cml_state ffi} {env : sem_env} {val_ err_v : v} :
    M3 c st env val_ [] err_v := by
  intro r s' tenv tenvE t1 t2 tvs tenvS heval henv hs hv herr hpes
  rw [ev_match_nil] at heval
  cases heval
  exact ⟨tenvS, hs, ste_refl _, rfl, rfl, herr⟩

theorem em_cons (hg : good_ctMap c) {st : cml_state ffi} {env : sem_env} {val_ err_v : v}
    {p : pat} {e : exp} {pes' : List (pat × exp)}
    (ih1 : ∀ env_v', pmatch env.c st.refs p val_ [] = .Match env_v' →
      M1 c st (.mk (nsAppend (alist_to_ns env_v') env.v_) env.c) [e])
    (ih3 : M3 c st env val_ pes' err_v) :
    M3 c st env val_ ((p, e) :: pes') err_v := by
  intro r s' tenv tenvE t1 t2 tvs tenvS heval henv hs hv herr hpes
  obtain ⟨bindings, hd, hp, he⟩ := hpes (p, e) (by simp)
  rw [ev_match_cons, if_pos hd] at heval
  rcases pat_sound1 hp env.c st.refs val_ [] c [] tenvS hg.1 henv.2.2.2.1 hv hs .nil with
    hno | ⟨env_v', hm, hrel⟩
  · rw [hno] at heval
    simp only [] at heval
    exact ih3 r s' tenv tenvE t1 t2 tvs tenvS heval henv hs hv herr
      (fun pe hm => hpes pe (by simp [hm]))
  · rw [hm] at heval
    simp only [] at heval
    have henv2 := envOK_bvl (tvs := tvs) (tbs := bindings) henv
      (type_p_bvl.1 tvs tenv p t1 bindings hp tenvE henv.2.1) (by simpa using hrel)
    exact R1_tvs0
      (ih1 env_v' hm r s' tenv (bind_var_list tvs bindings tenvE) [t2] 0 tenvS heval henv2 hs
        (by simp) (by rw [bind_tvar0]; exact type_es_sing he))

end

section
variable {ffi : Type} {c : ctMap}

theorem es_con (hg : good_ctMap c) {st : cml_state ffi} {env : sem_env}
    {cn : Option (cml_id modN conN)} {es' : List exp}
    (ih : M1 c st env es'.reverse) : M1 c st env [.Con cn es'] := by
  intro r s' tenv tenvE ts tvs tenvS heval henv hs hval hty
  obtain ⟨t, rfl, hte⟩ := type_es_sing_inv hty
  have hval' : tvs ≠ 0 → EVERY is_value es'.reverse = true := by
    intro h
    have := hval h
    simp only [EVERY, List.all_cons, List.all_nil, Bool.and_true] at this
    have h2 := is_value_con this
    rw [EVERY_iff]
    intro x hx
    exact h2 x (by simpa using hx)
  have hall : nsAll2 (type_ctor c) env.c tenv.c := henv.2.2.2.1
  rw [ev_con] at heval
  cases hte
  · rename_i cn ts' tvs_ ts tn hlen hl hf htes
    obtain ⟨_, stmp, hlk, _⟩ := (type_env_conv_thm' c env.c tenv.c hall cn tvs_ ts tn tn).1 hl
    have hlen2 : es'.length = ts.length := by
      have := type_es_length _ _ _ _ htes
      simpa using this
    have hchk : do_con_check env.c (some cn) es'.length = true := by
      simp [do_con_check, hlk, hlen2]
    rw [if_pos hchk] at heval
    have htes' : type_es tenv (bind_tvar tvs tenvE) es'.reverse
        (ts.map (type_subst (Finmap.alist_to_fmap (tvs_.zip ts')))).reverse := by
      rw [type_es_list_rel] at htes ⊢
      exact LIST_REL_reverse htes
    cases h1 : evaluate st env es'.reverse with
    | mk st1 r1 =>
      rw [h1] at heval
      obtain ⟨tenvS1, hs1, hste, hn1, hn2, hres⟩ :=
        ih r1 st1 tenv tenvE _ tvs tenvS h1 henv hs hval' htes'
      cases r1 with
      | Rval vs =>
        simp only [] at heval
        obtain ⟨val_, hbc, hv⟩ := build_conv_type_sound' env.c cn vs tvs ts c tenvS1 ts' tn tenv.c
          tvs_ tenvE es'.length ⟨hall, hchk, henv.2.2.1, EVERY_iff.mpr (by simpa using hf), hlen, hres, hl⟩
        rw [hbc] at heval
        simp only [] at heval
        cases heval
        exact ⟨tenvS1, hs1, hste, hn1, hn2, .cons _ _ _ _ hv .nil⟩
      | Rerr err =>
        simp only [] at heval
        cases heval
        exact ⟨tenvS1, hs1, hste, hn1, hn2, res1_err hres⟩
  · rename_i ts htes
    have hchk : do_con_check env.c none es'.length = true := by
      simp [do_con_check]
    rw [if_pos hchk] at heval
    have htes' : type_es tenv (bind_tvar tvs tenvE) es'.reverse ts.reverse := by
      rw [type_es_list_rel] at htes ⊢
      exact LIST_REL_reverse htes
    cases h1 : evaluate st env es'.reverse with
    | mk st1 r1 =>
      rw [h1] at heval
      obtain ⟨tenvS1, hs1, hste, hn1, hn2, hres⟩ :=
        ih r1 st1 tenv tenvE _ tvs tenvS h1 henv hs hval' htes'
      cases r1 with
      | Rval vs =>
        simp only [build_conv] at heval
        cases heval
        have hres' : LIST_REL (type_v tvs c tenvS1) vs.reverse ts := by
          have := LIST_REL_reverse (show LIST_REL (type_v tvs c tenvS1) vs ts.reverse from hres)
          simpa using this
        exact ⟨tenvS1, hs1, hste, hn1, hn2, .cons _ _ _ _ (type_v_conv_none_intro hres') .nil⟩
      | Rerr err =>
        simp only [] at heval
        cases heval
        exact ⟨tenvS1, hs1, hste, hn1, hn2, res1_err hres⟩

theorem es_app (hg : good_ctMap c) {st : cml_state ffi} {env : sem_env} {o_ : op}
    {es' : List exp}
    (ih1 : M1 c st env es'.reverse)
    (ih2 : ∀ st' vs env' e, evaluate st env es'.reverse = (st', .Rval vs) →
      do_opapp vs.reverse = some (env', e) → st'.clock ≠ 0 → M1 c (dec_clock st') env' [e]) :
    M1 c st env [.App o_ es'] := by
  intro r s' tenv tenvE ts tvs tenvS heval henv hs hval hty
  have htvs := tvs0_of_nonvalue hval (by simp [is_value])
  subst htvs
  rw [bind_tvar0] at hty
  obtain ⟨t, rfl, hte⟩ := type_es_sing_inv hty
  cases hte
  rename_i ts htes hf htop
  rw [henv.2.2.1] at hf
  have htes' : type_es tenv (bind_tvar 0 tenvE) es'.reverse ts.reverse := by
    rw [bind_tvar0]
    rw [type_es_list_rel] at htes ⊢
    exact LIST_REL_reverse htes
  cases h1 : evaluate st env es'.reverse with
  | mk st1 r1 =>
    obtain ⟨tenvS1, hs1, hste, hn1, hn2, hres⟩ :=
      ih1 r1 st1 tenv tenvE _ 0 tenvS h1 henv hs (by simp) htes'
    cases r1 with
    | Rerr err =>
      rw [ev_app_err _ _ _ _ h1] at heval
      cases heval
      exact ⟨tenvS1, hs1, hste, hn1, hn2, res1_err hres⟩
    | Rval vs =>
      have hvs : LIST_REL (type_v 0 c tenvS1) vs ts.reverse := hres
      by_cases hop : o_ = .Opapp
      · subst hop
        rw [ev_app_funapp _ _ _ _ h1 rfl] at heval
        have hvs' : LIST_REL (type_v 0 c tenvS1) vs.reverse ts := by
          have := LIST_REL_reverse hvs
          simpa using this
        obtain ⟨env', e, tenv', tenvE', h_ok, h_eok, h_nt, h_all, h_te, h_do⟩ :=
          opapp_type_sound' c tenvS1 vs.reverse ts t ⟨hg.1, htop, hvs'⟩
        rw [h_do] at heval
        simp only [] at heval
        by_cases hclk : st1.clock = 0
        · simp [hclk] at heval
          obtain ⟨rfl, rfl⟩ := heval
          exact ⟨tenvS1, hs1, hste, hn1, hn2, trivial⟩
        · simp [hclk] at heval
          exact R1_trans hste hn1 hn2
            (ih2 st1 vs env' e h1 h_do hclk r s' tenv' tenvE' [t] 0 tenvS1 heval
              ⟨h_ok, h_eok, h_nt, h_all⟩ hs1 (by simp) (by rw [bind_tvar0]; exact type_es_sing h_te))
      · rw [ev_app_simple _ _ _ _ h1 (type_op_simple htop hop)] at heval
        obtain ⟨tenvS2, store', ffi', r', hste2, hs2, hdo, hmatch⟩ :=
          op_type_sound' c tenvS1 vs o_ ts t st1.refs st1.ffi ⟨hg, hop, hs1, htop, hf, hvs⟩
        rw [hdo] at heval
        simp only [] at heval
        cases heval
        refine ⟨tenvS2, hs2, ste_trans hste hste2, hn1, hn2, ?_⟩
        cases r' with
        | Rval x => exact .cons _ _ _ _ hmatch .nil
        | Rerr err =>
          cases err with
          | Rraise x => exact hmatch
          | Rabort a => cases a <;> first | exact hmatch | exact trivial

end

section
variable {ffi : Type} {c : ctMap}

theorem ev_clock {st st' : cml_state ffi} {env : sem_env} {es : List exp} {r : result (List v) v}
    (h : evaluate st env es = (st', r)) : st'.clock ≤ st.clock :=
  evaluate_clock.1 st env es st' r h

theorem es_main (hg : good_ctMap c) : ∀ (k sz : Nat),
    (∀ (st : cml_state ffi) (env : sem_env) (es : List exp),
      st.clock = k → sizeOf es = sz → M1 c st env es) ∧
    (∀ (st : cml_state ffi) (env : sem_env) (val_ : v) (pes : List (pat × exp)) (err : v),
      st.clock = k → sizeOf pes = sz → M3 c st env val_ pes err) := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ihk =>
    intro sz
    induction sz using Nat.strongRecOn with
    | _ sz ihsz =>
      have IHa : ∀ (st2 : cml_state ffi) (env : sem_env) (es : List exp),
          st2.clock ≤ k → (st2.clock < k ∨ sizeOf es < sz) → M1 c st2 env es := by
        intro st2 env es hle hlt
        by_cases h : st2.clock < k
        · exact (ihk st2.clock h (sizeOf es)).1 st2 env es rfl rfl
        · have h2 : sizeOf es < sz := by omega
          exact (ihsz (sizeOf es) h2).1 st2 env es (by omega) rfl
      have IHb : ∀ (st2 : cml_state ffi) (env : sem_env) (val_ : v) (pes : List (pat × exp))
          (err : v), st2.clock ≤ k → (st2.clock < k ∨ sizeOf pes < sz) → M3 c st2 env val_ pes err := by
        intro st2 env val_ pes err hle hlt
        by_cases h : st2.clock < k
        · exact (ihk st2.clock h (sizeOf pes)).2 st2 env val_ pes err rfl rfl
        · have h2 : sizeOf pes < sz := by omega
          exact (ihsz (sizeOf pes) h2).2 st2 env val_ pes err (by omega) rfl
      constructor
      · intro st env es hk hsz
        subst hk hsz
        cases es with
        | nil => exact es_nil
        | cons e1 rest =>
          cases rest with
          | cons e2 es' =>
            exact es_cons (IHa st env [e1] (Nat.le_refl _)
                (.inr (by have := list_sizeOf_pos es'; simp; omega)))
              (fun st' vs h => IHa st' env (e2 :: es') (ev_clock h)
                (.inr (by simp only [List.cons.sizeOf_spec]; omega)))
          | nil =>
            cases e1 with
            | Raise e =>
              exact es_raise (IHa st env [e] (Nat.le_refl _) (.inr (by simp)))
            | Handle e pes =>
              exact es_handle hg (IHa st env [e] (Nat.le_refl _) (.inr (by simp; omega)))
                (fun st' val_ h => IHb st' env val_ pes val_ (ev_clock h) (.inr (by simp; omega)))
            | Lit l => exact es_lit
            | Con cn es' =>
              exact es_con hg (IHa st env es'.reverse (Nat.le_refl _)
                (.inr (by rw [list_sizeOf_reverse]; simp; omega)))
            | Var n => exact es_var hg
            | Fun x e => exact es_fun
            | App o_ es' =>
              exact es_app hg (IHa st env es'.reverse (Nat.le_refl _)
                (.inr (by rw [list_sizeOf_reverse]; simp; omega)))
                (fun st' vs env' e h _ hclk => IHa (dec_clock st') env' [e]
                  (by have := ev_clock h; simp [dec_clock]; omega)
                  (.inl (by have := ev_clock h; simp [dec_clock]; omega)))
            | Log l e1 e2 =>
              exact es_log hg (IHa st env [e1] (Nat.le_refl _) (.inr (by simp; omega)))
                (fun st' vs h => IHa st' env [e2] (ev_clock h) (.inr (by simp; omega)))
            | If e1 e2 e3 =>
              exact es_if hg (IHa st env [e1] (Nat.le_refl _) (.inr (by simp; omega)))
                (fun st' vs h => IHa st' env [e2] (ev_clock h) (.inr (by simp; omega)))
                (fun st' vs h => IHa st' env [e3] (ev_clock h) (.inr (by simp; omega)))
            | Mat e pes =>
              exact es_mat hg (IHa st env [e] (Nat.le_refl _) (.inr (by simp; omega)))
                (fun st' vs h => IHb st' env _ pes _ (ev_clock h) (.inr (by simp; omega)))
            | Let xo e1 e2 =>
              exact es_let (IHa st env [e1] (Nat.le_refl _) (.inr (by simp; omega)))
                (fun st' vs h => IHa st' _ [e2] (ev_clock h) (.inr (by simp; omega)))
            | Letrec funs e =>
              exact es_letrec (IHa st _ [e] (Nat.le_refl _) (.inr (by simp; omega)))
            | Tannot e a =>
              exact es_tannot (IHa st env [e] (Nat.le_refl _) (.inr (by simp; omega)))
            | Lannot e a =>
              exact es_lannot (IHa st env [e] (Nat.le_refl _) (.inr (by simp; omega)))
      · intro st env val_ pes err hk hsz
        subst hk hsz
        cases pes with
        | nil => exact em_nil
        | cons pe pes' =>
          obtain ⟨p, e⟩ := pe
          exact em_cons hg
            (fun env_v' _ => IHa st _ [e] (Nat.le_refl _)
              (.inr (by have := list_sizeOf_pos pes'; simp; omega)))
            (IHb st env val_ pes' err (Nat.le_refl _) (.inr (by simp; omega)))

theorem exp_type_sound' :
    ∀ (ctMap_ : ctMap),
    (∀ {ffi : Type} (s : cml_state ffi) (env : sem_env) (es : List exp)
       (r : result (List v) v) (s' : cml_state ffi) (tenv : type_env)
       (tenvE : tenv_val_exp) (ts : List sem_t) (tvs : Nat) (tenvS : tenv_store),
      evaluate s env es = (s', r) ∧
      tenv_ok tenv ∧
      tenv_val_exp_ok tenvE ∧
      good_ctMap ctMap_ ∧
      num_tvs tenvE = 0 ∧
      type_all_env ctMap_ tenvS env { tenv with v := add_tenvE tenvE tenv.v } ∧
      type_s ctMap_ s.refs tenvS ∧
      (tvs ≠ 0 → EVERY is_value es) ∧
      type_es tenv (bind_tvar tvs tenvE) es ts →
      ∃ (tenvS' : tenv_store),
        type_s ctMap_ s'.refs tenvS' ∧
        ste tenvS tenvS' ∧
        s'.next_type_stamp = s.next_type_stamp ∧
        s'.next_exn_stamp = s.next_exn_stamp ∧
        match r with
        | .Rval vs => LIST_REL (type_v tvs ctMap_ tenvS') vs ts
        | .Rerr (.Rraise val_) => type_v 0 ctMap_ tenvS' val_ Texn
        | .Rerr (.Rabort .Rtimeout_error) => True
        | .Rerr (.Rabort (.Rffi_error _)) => True
        | .Rerr (.Rabort .Rtype_error) => False) ∧
    (∀ {ffi : Type} (s : cml_state ffi) (env : sem_env) (val_ : v)
       (pes : List (pat × exp)) (err_v : v) (r : result (List v) v)
       (s' : cml_state ffi) (tenv : type_env) (tenvE : tenv_val_exp)
       (t1 t2 : sem_t) (tvs : Nat) (tenvS : tenv_store),
      evaluate_match s env val_ pes err_v = (s', r) ∧
      tenv_ok tenv ∧
      tenv_val_exp_ok tenvE ∧
      good_ctMap ctMap_ ∧
      num_tvs tenvE = 0 ∧
      type_all_env ctMap_ tenvS env { tenv with v := add_tenvE tenvE tenv.v } ∧
      type_s ctMap_ s.refs tenvS ∧
      type_v tvs ctMap_ tenvS val_ t1 ∧
      type_v 0 ctMap_ tenvS err_v Texn ∧
      type_pes tvs tvs tenv tenvE pes t1 t2 →
      ∃ (tenvS' : tenv_store),
        type_s ctMap_ s'.refs tenvS' ∧
        ste tenvS tenvS' ∧
        s'.next_type_stamp = s.next_type_stamp ∧
        s'.next_exn_stamp = s.next_exn_stamp ∧
        match r with
        | .Rval vs => type_v tvs ctMap_ tenvS' vs.head! t2
        | .Rerr (.Rraise val_) => type_v 0 ctMap_ tenvS' val_ Texn
        | .Rerr (.Rabort .Rtimeout_error) => True
        | .Rerr (.Rabort (.Rffi_error _)) => True
        | .Rerr (.Rabort .Rtype_error) => False) := by
  intro c
  constructor
  · intro ffi s env es r s' tenv tenvE ts tvs tenvS ⟨heval, h1, h2, hg, h3, h4, hs, hval, hty⟩
    obtain ⟨tenvS', a1, a2, a3, a4, a5⟩ :=
      (es_main hg s.clock (sizeOf es)).1 s env es rfl rfl r s' tenv tenvE ts tvs tenvS heval
        ⟨h1, h2, h3, h4⟩ hs hval hty
    refine ⟨tenvS', a1, a2, a3, a4, ?_⟩
    cases r with
    | Rval vs => exact a5
    | Rerr e =>
      cases e with
      | Rraise x => exact a5
      | Rabort a => cases a <;> exact a5
  · intro ffi s env val_ pes err_v r s' tenv tenvE t1 t2 tvs tenvS
      ⟨heval, h1, h2, hg, h3, h4, hs, hv, herr, hpes⟩
    obtain ⟨tenvS', a1, a2, a3, a4, a5⟩ :=
      (es_main hg s.clock (sizeOf pes)).2 s env val_ pes err_v rfl rfl r s' tenv tenvE t1 t2 tvs
        tenvS heval ⟨h1, h2, h3, h4⟩ hs hv herr hpes
    refine ⟨tenvS', a1, a2, a3, a4, ?_⟩
    cases r with
    | Rval vs =>
      obtain ⟨x, rfl, hx⟩ := lr1 a5
      exact hx
    | Rerr e =>
      cases e with
      | Rraise x => exact a5
      | Rabort a => cases a <;> exact a5

end

end DAux

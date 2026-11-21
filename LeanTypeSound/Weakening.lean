/-
  Translation of weakeningScript.sml
  Weakening lemmas used in type soundness.
-/
import LeanTypeSound.HOL4Prelude
import LeanTypeSound.Ast
import LeanTypeSound.TypeSystem
import LeanTypeSound.TypeSysProps
import LeanTypeSound.NamespaceProps
import LeanTypeSound.SemanticPrimitives
import LeanTypeSound.TypeSoundInvariants

open HOL4

-- ============================================================
-- Definitions
-- ============================================================

/- HOL4:
Definition weak_tenvE_def:
weak_tenvE tenv tenv' =
  (num_tvs tenv ≥ num_tvs tenv' ∧
   ∀n inc tvs t.
    (tveLookup n inc tenv' = SOME (tvs,t)) ⇔
    (tveLookup n inc tenv = SOME (tvs,t)))
End
-/
def weak_tenvE (tenvE tenvE' : tenv_val_exp) : Prop :=
  num_tvs tenvE ≥ num_tvs tenvE' ∧
  ∀ n inc tvs t,
    (tveLookup n inc tenvE' = some (tvs, t)) ↔
    (tveLookup n inc tenvE = some (tvs, t))

/- HOL4:
Definition weakS_def:
weakS tenvS tenvS' ⇔ tenvS' SUBMAP tenvS
End
-/
def weakS (tenvS tenvS' : tenv_store) : Prop :=
  Finmap.SUBMAP tenvS' tenvS

/- HOL4:
Definition weak_def:
weak tenv' tenv ⇔
  tenv'.t = tenv.t ∧ weak_tenv tenv' tenv
End
-/
def weak (tenv' tenv : type_env) : Prop :=
  tenv'.t = tenv.t ∧ weak_tenv tenv' tenv

/- HOL4:
Definition weakCT_def:
weakCT cenv_impl cenv_spec ⇔ cenv_spec SUBMAP cenv_impl
End
-/
def weakCT (cenv_impl cenv_spec : ctMap) : Prop :=
  Finmap.SUBMAP cenv_spec cenv_impl

-- ============================================================
-- Theorems
-- ============================================================

/- HOL4:
Theorem weak_tenv_refl:
   !tenv. tenv_val_ok tenv.v ⇒ weak_tenv tenv tenv
-/
theorem weak_tenv_refl :
    ∀ (tenv : type_env), tenv_val_ok tenv.v → weak_tenv tenv tenv := by
  intro tenv h
  refine ⟨?_, ?_⟩
  · refine nsSub_refl (fun (_ : cml_id modN varN) (p : Nat × sem_t) => check_freevars p.1 [] p.2 = true) tscheme_inst2 ?_ tenv.v h
    intro n ⟨tvs, t⟩ hx
    refine ⟨GENLIST (fun i => sem_t.Tvar_db i) tvs, ?_, hx, ?_, ?_⟩
    · simp [GENLIST]
    · intro s hs
      simp [GENLIST] at hs
      obtain ⟨a, ha, rfl⟩ := hs
      simp [check_freevars, ha]
    · exact deBruijn_subst_id.1 t tvs hx
  · exact nsSub_refl (fun _ _ => True) _ (fun _ _ _ => rfl) tenv.c (eALL_T _)
/- HOL4:
Theorem weakS_refl:
   !tenvS. weakS tenvS tenvS
-/
theorem weakS_refl :
    ∀ (tenvS : tenv_store), weakS tenvS tenvS := by
  intro tenvS k v h; exact h
/- HOL4:
Theorem weak_tenvE_freevars[local]:
  !tenv tenv' tvs t.
  weak_tenvE tenv' tenv ∧
  check_freevars (num_tvs tenv) tvs t ⇒
  check_freevars (num_tvs tenv') tvs t
-/
theorem weak_tenvE_freevars :
    ∀ (tenvE tenvE' : tenv_val_exp) (tvs : List tvarN) (t : sem_t),
      weak_tenvE tenvE' tenvE ∧ check_freevars (num_tvs tenvE) tvs t →
      check_freevars (num_tvs tenvE') tvs t := by
  intro tenvE tenvE' tvs t ⟨h1, h2⟩
  exact check_freevars_add _ _ _ h2 _ h1.1
/- HOL4:
Theorem weak_tenvE_bind[local]:
  !tenv tenv' n tvs t.
  weak_tenvE tenv' tenv ⇒
  weak_tenvE (Bind_name n tvs t tenv') (Bind_name n tvs t tenv)
-/
theorem weak_tenvE_bind :
    ∀ (tenvE tenvE' : tenv_val_exp) (n : mlstring) (tvs : Nat) (t : sem_t),
      weak_tenvE tenvE' tenvE →
      weak_tenvE (.Bind_name n tvs t tenvE') (.Bind_name n tvs t tenvE) := by
  intro tenvE tenvE' n tvs t ⟨h1, h2⟩
  refine ⟨by simpa [num_tvs] using h1, ?_⟩
  intro n' inc tvs' t'
  simp only [tveLookup]
  split
  · exact Iff.rfl
  · exact h2 _ _ _ _
/- HOL4:
Theorem weak_tenvE_opt_bind[local]:
  !tenv tenv' n tvs t.
  weak_tenvE tenv' tenv ⇒
  weak_tenvE (opt_bind_name n tvs t tenv') (opt_bind_name n tvs t tenv)
-/
theorem weak_tenvE_opt_bind :
    ∀ (tenvE tenvE' : tenv_val_exp) (n : Option mlstring) (tvs : Nat) (t : sem_t),
      weak_tenvE tenvE' tenvE →
      weak_tenvE (opt_bind_name n tvs t tenvE') (opt_bind_name n tvs t tenvE) := by
  intro tenvE tenvE' n tvs t h
  cases n with
  | none => exact h
  | some n => exact weak_tenvE_bind _ _ _ _ _ h
/- HOL4:
Theorem weak_tenvE_bind_tvar[local]:
  !tenv tenv' tvs.
  weak_tenvE tenv' tenv ⇒
  weak_tenvE (bind_tvar tvs tenv') (bind_tvar tvs tenv)
-/
theorem weak_tenvE_bind_tvar :
    ∀ (tenvE tenvE' : tenv_val_exp) (tvs : Nat),
      weak_tenvE tenvE' tenvE →
      weak_tenvE (bind_tvar tvs tenvE') (bind_tvar tvs tenvE) := by
  intro tenvE tenvE' tvs h
  unfold bind_tvar
  split
  · exact h
  · obtain ⟨h1, h2⟩ := h
    refine ⟨by simp only [num_tvs]; omega, ?_⟩
    intro n inc tvs' t'
    simp only [tveLookup]
    exact h2 _ _ _ _
/- HOL4:
Theorem weak_tenvE_bind_tvar2[local]:
  !tenv tenv' n tvs t.
  tenv_val_exp_ok tenv ∧
  num_tvs tenv = 0 ∧
  weak_tenvE tenv' tenv ⇒
  weak_tenvE (bind_tvar tvs tenv') (bind_tvar 0 tenv)
-/
theorem weak_tenvE_bind_tvar2 :
    ∀ (tenvE tenvE' : tenv_val_exp) (tvs : Nat),
      tenv_val_exp_ok tenvE ∧ num_tvs tenvE = 0 ∧ weak_tenvE tenvE' tenvE →
      weak_tenvE (bind_tvar tvs tenvE') (bind_tvar 0 tenvE) := by
  intro tenvE tenvE' tvs ⟨hok, h0, h1, h2⟩
  have e0 : bind_tvar 0 tenvE = tenvE := by simp [bind_tvar]
  rw [e0]
  refine ⟨by omega, ?_⟩
  intro n inc tvs' t'
  have key : ∀ i, tveLookup n i tenvE' = some (tvs', t') ↔ tveLookup n inc tenvE = some (tvs', t') := by
    intro i
    rw [← h2 n i tvs' t', tveLookup_no_tvs i tvs' tenvE n t' ⟨hok, h0⟩, tveLookup_no_tvs inc tvs' tenvE n t' ⟨hok, h0⟩]
  unfold bind_tvar
  split
  · exact (key _).symm
  · simp only [tveLookup]; exact (key _).symm
/- HOL4:
Theorem weak_tenvE_bind_var_list[local]:
  !bindings tenvE tenvE' n tvs t .
  weak_tenvE tenvE' tenvE ⇒
  weak_tenvE (bind_var_list tvs bindings tenvE') (bind_var_list tvs bindings tenvE)
-/
theorem weak_tenvE_bind_var_list :
    ∀ (bindings : List (mlstring × sem_t)) (tenvE tenvE' : tenv_val_exp) (tvs : Nat),
      weak_tenvE tenvE' tenvE →
      weak_tenvE (bind_var_list tvs bindings tenvE') (bind_var_list tvs bindings tenvE) := by
  intro bindings tenvE tenvE' tvs h
  induction bindings with
  | nil => exact h
  | cons b bs ih =>
    obtain ⟨n, t⟩ := b
    exact weak_tenvE_bind _ _ _ _ _ ih
/- HOL4:
Theorem eLookupC_weak[local]:
  ∀cn tenv tenv' tvs ts tn.
    weak_tenv tenv' tenv ∧
    nsLookup tenv.c cn = SOME (tvs,ts,tn)
    ⇒
    nsLookup tenv'.c cn = SOME (tvs,ts,tn)
-/
theorem eLookupC_weak :
    ∀ (cn : cml_id modN conN) (tenv tenv' : type_env)
      (tvs : List tvarN) (ts : List sem_t) (tn : type_ident),
      weak_tenv tenv' tenv ∧ nsLookup tenv.c cn = some (tvs, ts, tn) →
      nsLookup tenv'.c cn = some (tvs, ts, tn) := by
  intro cn tenv tenv' tvs ts tn ⟨⟨_, h1, _⟩, h2⟩
  obtain ⟨v2, hv, rfl⟩ := h1 _ _ h2
  exact hv
/- HOL4:
Theorem eLookupV_weak[local]:
  ∀n tenv tenv' tvs t.
    weak_tenv tenv' tenv ∧
    nsLookup tenv.v n = SOME (tvs,t)
    ⇒
    ∃tvs' t'. nsLookup tenv'.v n = SOME (tvs',t') ∧ tscheme_inst (tvs,t) (tvs',t')
-/
theorem eLookupV_weak :
    ∀ (n : cml_id modN varN) (tenv tenv' : type_env) (tvs : Nat) (t : sem_t),
      weak_tenv tenv' tenv ∧ nsLookup tenv.v n = some (tvs, t) →
      ∃ (tvs' : Nat) (t' : sem_t),
        nsLookup tenv'.v n = some (tvs', t') ∧ tscheme_inst (tvs, t) (tvs', t') := by
  intro n tenv tenv' tvs t ⟨⟨⟨h1, _⟩, _⟩, h2⟩
  obtain ⟨⟨tvs', t'⟩, hv, hr⟩ := h1 _ _ h2
  exact ⟨tvs', t', hv, hr⟩
mutual
theorem type_p_weak_aux {tvs : Nat} {tenv : type_env} {p : pat} {t : sem_t}
    {bindings : List (varN × sem_t)} (h : type_p tvs tenv p t bindings)
    (tenv' : type_env) (tvs' : Nat) (h1 : tvs' ≥ tvs) (h2 : weak tenv' tenv) :
    type_p tvs' tenv' p t bindings := by
  cases h with
  | pany _ hc => exact .pany _ _ _ (check_freevars_add _ _ _ hc _ h1)
  | pvar _ _ hc => exact .pvar _ _ _ _ (check_freevars_add _ _ _ hc _ h1)
  | plit_int => exact .plit_int ..
  | plit_char => exact .plit_char ..
  | plit_str => exact .plit_str ..
  | plit_word8 => exact .plit_word8 ..
  | plit_word64 => exact .plit_word64 ..
  | pcon_some cn ps ts' tvs'' ts tn _ hc hl hps hlk =>
    exact .pcon_some _ _ _ _ _ _ _ _ _ (fun t' ht' => check_freevars_add _ _ _ (hc t' ht') _ h1) hl
      (type_ps_weak_aux hps tenv' tvs' h1 h2) (eLookupC_weak _ _ _ _ _ _ ⟨h2.2, hlk⟩)
  | pcon_none _ _ _ hps => exact .pcon_none _ _ _ _ _ (type_ps_weak_aux hps tenv' tvs' h1 h2)
  | pref _ _ _ hp => exact .pref _ _ _ _ _ (type_p_weak_aux hp tenv' tvs' h1 h2)
  | pas _ _ _ _ hp => exact .pas _ _ _ _ _ _ (type_p_weak_aux hp tenv' tvs' h1 h2)
  | ptannot _ t0 _ ha hn hp =>
    have ht : tenv'.t = tenv.t := h2.1
    rw [← ht] at hn hp ⊢
    exact .ptannot _ _ _ _ _ ha hn (type_p_weak_aux hp tenv' tvs' h1 h2)
theorem type_ps_weak_aux {tvs : Nat} {tenv : type_env} {ps : List pat} {ts : List sem_t}
    {bindings : List (varN × sem_t)} (h : type_ps tvs tenv ps ts bindings)
    (tenv' : type_env) (tvs' : Nat) (h1 : tvs' ≥ tvs) (h2 : weak tenv' tenv) :
    type_ps tvs' tenv' ps ts bindings := by
  cases h with
  | nil => exact .nil ..
  | cons _ _ _ _ _ _ hp hps =>
    exact .cons _ _ _ _ _ _ _ _ (type_p_weak_aux hp tenv' tvs' h1 h2) (type_ps_weak_aux hps tenv' tvs' h1 h2)
end

/- HOL4:
Theorem type_p_weakening:
 (!tvs tenv p t bindings. type_p tvs tenv p t bindings ⇒
    !tenv' tvs'. tvs' ≥ tvs ∧ weak tenv' tenv ⇒ type_p tvs' tenv' p t bindings) ∧
 (!tvs tenv ps ts bindings. type_ps tvs tenv ps ts bindings ⇒
    !tenv' tvs'. tvs' ≥ tvs ∧ weak tenv' tenv ⇒ type_ps tvs' tenv' ps ts bindings)
-/
theorem type_p_weakening :
    (∀ (tvs : Nat) (tenv : type_env) (p : pat) (t : sem_t) (bindings : List (varN × sem_t)),
      type_p tvs tenv p t bindings →
      ∀ (tenv' : type_env) (tvs' : Nat),
        tvs' ≥ tvs ∧ weak tenv' tenv → type_p tvs' tenv' p t bindings) ∧
    (∀ (tvs : Nat) (tenv : type_env) (ps : List pat) (ts : List sem_t)
      (bindings : List (varN × sem_t)),
      type_ps tvs tenv ps ts bindings →
      ∀ (tenv' : type_env) (tvs' : Nat),
        tvs' ≥ tvs ∧ weak tenv' tenv → type_ps tvs' tenv' ps ts bindings) := by
  exact ⟨fun _ _ _ _ _ h tenv' tvs' hh => type_p_weak_aux h tenv' tvs' hh.1 hh.2,
         fun _ _ _ _ _ h tenv' tvs' hh => type_ps_weak_aux h tenv' tvs' hh.1 hh.2⟩
theorem weak_tenvE_lookup_varE {tenvE tenvE' : tenv_val_exp} (h2 : weak_tenvE tenvE' tenvE)
    (n : cml_id modN varN) (x : Nat × sem_t) :
    lookup_varE n tenvE' = some x ↔ lookup_varE n tenvE = some x := by
  cases n with
  | Short a => obtain ⟨a1, a2⟩ := x; simp only [lookup_varE]; exact (h2.2 a 0 a1 a2).symm
  | Long a b => simp [lookup_varE]

theorem type_e_weak_var {tenv tenv' : type_env} {tenvE tenvE' : tenv_val_exp}
    (h1 : weak tenv' tenv) (h2 : weak_tenvE tenvE' tenvE)
    (n : cml_id modN varN) (tvs : Nat) (t : sem_t) (targs : List sem_t)
    (hlen : tvs = targs.length)
    (hfv : ∀ ta, ta ∈ targs → check_freevars (num_tvs tenvE) [] ta)
    (hlk : lookup_var n tenvE tenv = some (tvs, t)) :
    type_e tenv' tenvE' (.Var n) (deBruijn_subst 0 targs t) := by
  have hfv' : ∀ ta, ta ∈ targs → check_freevars (num_tvs tenvE') [] ta :=
    fun ta hta => weak_tenvE_freevars _ _ _ _ ⟨h2, hfv ta hta⟩
  unfold lookup_var at hlk
  cases hl : lookup_varE n tenvE with
  | some x =>
    rw [hl] at hlk
    simp only [Option.some.injEq] at hlk
    subst hlk
    refine type_e.var _ _ n tvs t targs hlen hfv' ?_
    unfold lookup_var
    rw [(weak_tenvE_lookup_varE h2 n _).2 hl]
  | none =>
    rw [hl] at hlk
    simp only at hlk
    have hl' : lookup_varE n tenvE' = none := by
      cases h : lookup_varE n tenvE' with
      | none => rfl
      | some y => rw [(weak_tenvE_lookup_varE h2 n _).1 h] at hl; cases hl
    obtain ⟨tvs', t', hv, hr⟩ := eLookupV_weak n tenv tenv' tvs t ⟨h1.2, hlk⟩
    obtain ⟨subst, hsl, hfvt, hsfv, heq⟩ := hr
    have e1 := deBruijn_subst2_thm.1 t' 0 subst targs [] (by rw [hsl]; exact hfvt)
    rw [deBruijn_inc0.2 targs 0] at e1
    rw [← heq, e1]
    refine type_e.var _ _ n tvs' t' (subst.map (deBruijn_subst 0 targs)) (by simp [hsl]) ?_ ?_
    · intro ta hta
      obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hta
      refine deBruijn_subst_check_freevars2 (num_tvs tenvE') [] s targs 0 [] ⟨?_, ?_⟩
      · rw [← hlen]; exact hsfv s hs
      · simp only [EVERY, List.all_eq_true]
        exact fun x hx => hfv' x hx
    · unfold lookup_var
      rw [hl']
      exact hv

mutual
theorem type_e_weak_aux {tenv : type_env} {tenvE : tenv_val_exp} {e : exp} {t : sem_t}
    (h : type_e tenv tenvE e t) (tenv' : type_env) (tenvE' : tenv_val_exp)
    (h1 : weak tenv' tenv) (h2 : weak_tenvE tenvE' tenvE) : type_e tenv' tenvE' e t :=
  match h with
  | .lit_int _ _ _ => .lit_int ..
  | .lit_char _ _ _ => .lit_char ..
  | .lit_str _ _ _ => .lit_str ..
  | .lit_word8 _ _ _ => .lit_word8 ..
  | .lit_word64 _ _ _ => .lit_word64 ..
  | .lit_float64 _ _ _ => .lit_float64 ..
  | .raise _ _ _ _ hc he =>
    .raise _ _ _ _ (weak_tenvE_freevars _ _ _ _ ⟨h2, hc⟩) (type_e_weak_aux he _ _ h1 h2)
  | .handle _ _ _ _ _ bindings_of he hne hd hp hes =>
    .handle _ _ _ _ _ bindings_of (type_e_weak_aux he _ _ h1 h2) hne hd
      (fun pe hpe => type_p_weakening.1 _ _ _ _ _ (hp pe hpe) _ _ ⟨h2.1, h1⟩)
      (fun pe hpe => type_e_weak_aux (hes pe hpe) _ _ h1 (weak_tenvE_bind_var_list _ _ _ _ h2))
  | .con_some _ _ _ _ _ _ _ _ hc hl hes hlk =>
    .con_some _ _ _ _ _ _ _ _ (fun t' ht' => weak_tenvE_freevars _ _ _ _ ⟨h2, hc t' ht'⟩) hl
      (type_es_weak_aux hes _ _ h1 h2) (eLookupC_weak _ _ _ _ _ _ ⟨h1.2, hlk⟩)
  | .con_none _ _ _ _ hes => .con_none _ _ _ _ (type_es_weak_aux hes _ _ h1 h2)
  | .var _ _ n tvs t targs hlen hfv hlk => type_e_weak_var h1 h2 n tvs t targs hlen hfv hlk
  | .fun_ _ _ _ _ _ _ hc he =>
    .fun_ _ _ _ _ _ _ (weak_tenvE_freevars _ _ _ _ ⟨h2, hc⟩)
      (type_e_weak_aux he _ _ h1 (weak_tenvE_bind _ _ _ _ _ h2))
  | .app _ _ _ _ _ _ hes hop hc =>
    .app _ _ _ _ _ _ (type_es_weak_aux hes _ _ h1 h2) hop (weak_tenvE_freevars _ _ _ _ ⟨h2, hc⟩)
  | .log _ _ _ _ _ he1 he2 =>
    .log _ _ _ _ _ (type_e_weak_aux he1 _ _ h1 h2) (type_e_weak_aux he2 _ _ h1 h2)
  | .if_ _ _ _ _ _ _ he1 he2 he3 =>
    .if_ _ _ _ _ _ _ (type_e_weak_aux he1 _ _ h1 h2) (type_e_weak_aux he2 _ _ h1 h2)
      (type_e_weak_aux he3 _ _ h1 h2)
  | .mat _ _ _ _ _ _ bindings_of he hne hd hp hes =>
    .mat _ _ _ _ _ _ bindings_of (type_e_weak_aux he _ _ h1 h2) hne hd
      (fun pe hpe => type_p_weakening.1 _ _ _ _ _ (hp pe hpe) _ _ ⟨h2.1, h1⟩)
      (fun pe hpe => type_e_weak_aux (hes pe hpe) _ _ h1 (weak_tenvE_bind_var_list _ _ _ _ h2))
  | .let_ _ _ _ _ _ _ _ he1 he2 =>
    .let_ _ _ _ _ _ _ _ (type_e_weak_aux he1 _ _ h1 h2)
      (type_e_weak_aux he2 _ _ h1 (weak_tenvE_opt_bind _ _ _ _ _ h2))
  | .letrec _ _ _ _ _ _ hf he =>
    .letrec _ _ _ _ _ _ (type_funs_weak_aux hf _ _ h1 (weak_tenvE_bind_var_list _ _ _ _ h2))
      (type_e_weak_aux he _ _ h1 (weak_tenvE_bind_var_list _ _ _ _ h2))
  | .tannot _ _ e0 t0 ha hn he => by
    have ih := type_e_weak_aux he tenv' tenvE' h1 h2
    have ht : tenv'.t = tenv.t := h1.1
    rw [← ht] at hn ih ⊢
    exact .tannot _ _ _ _ ha hn ih
  | .lannot _ _ _ _ _ he => .lannot _ _ _ _ _ (type_e_weak_aux he _ _ h1 h2)
theorem type_es_weak_aux {tenv : type_env} {tenvE : tenv_val_exp} {es : List exp} {ts : List sem_t}
    (h : type_es tenv tenvE es ts) (tenv' : type_env) (tenvE' : tenv_val_exp)
    (h1 : weak tenv' tenv) (h2 : weak_tenvE tenvE' tenvE) : type_es tenv' tenvE' es ts :=
  match h with
  | .nil _ _ => .nil ..
  | .cons _ _ _ _ _ _ he hes =>
    .cons _ _ _ _ _ _ (type_e_weak_aux he _ _ h1 h2) (type_es_weak_aux hes _ _ h1 h2)
theorem type_funs_weak_aux {tenv : type_env} {tenvE : tenv_val_exp}
    {funs : List (varN × varN × exp)} {bindings : List (varN × sem_t)}
    (h : type_funs tenv tenvE funs bindings) (tenv' : type_env) (tenvE' : tenv_val_exp)
    (h1 : weak tenv' tenv) (h2 : weak_tenvE tenvE' tenvE) : type_funs tenv' tenvE' funs bindings :=
  match h with
  | .nil _ _ => .nil ..
  | .cons _ _ _ _ _ _ _ _ _ hc he hf hal =>
    .cons _ _ _ _ _ _ _ _ _ (weak_tenvE_freevars _ _ _ _ ⟨h2, hc⟩)
      (type_e_weak_aux he _ _ h1 (weak_tenvE_bind _ _ _ _ _ h2))
      (type_funs_weak_aux hf _ _ h1 h2) hal
end

/- HOL4:
Theorem type_e_weakening_lem[local]:
  (!tenv tenvE e t. type_e tenv tenvE e t ⇒
    ∀tenv' tenvE'. weak tenv' tenv ∧ weak_tenvE tenvE' tenvE ⇒ type_e tenv' tenvE' e t) ∧
 (!tenv tenvE es ts. type_es tenv tenvE es ts ⇒
    ∀tenv' tenvE'. weak tenv' tenv ∧ weak_tenvE tenvE' tenvE ⇒ type_es tenv' tenvE' es ts) ∧
 (!tenv tenvE funs bindings. type_funs tenv tenvE funs bindings ⇒
    ∀tenv' tenvE'. weak tenv' tenv ∧ weak_tenvE tenvE' tenvE ⇒ type_funs tenv' tenvE' funs bindings)
-/
theorem type_e_weakening_lem :
    (∀ (tenv : type_env) (tenvE : tenv_val_exp) (e : exp) (t : sem_t),
      type_e tenv tenvE e t →
      ∀ (tenv' : type_env) (tenvE' : tenv_val_exp),
        weak tenv' tenv ∧ weak_tenvE tenvE' tenvE → type_e tenv' tenvE' e t) ∧
    (∀ (tenv : type_env) (tenvE : tenv_val_exp) (es : List exp) (ts : List sem_t),
      type_es tenv tenvE es ts →
      ∀ (tenv' : type_env) (tenvE' : tenv_val_exp),
        weak tenv' tenv ∧ weak_tenvE tenvE' tenvE → type_es tenv' tenvE' es ts) ∧
    (∀ (tenv : type_env) (tenvE : tenv_val_exp)
      (funs : List (varN × varN × exp)) (bindings : List (varN × sem_t)),
      type_funs tenv tenvE funs bindings →
      ∀ (tenv' : type_env) (tenvE' : tenv_val_exp),
        weak tenv' tenv ∧ weak_tenvE tenvE' tenvE → type_funs tenv' tenvE' funs bindings) := by
  exact ⟨fun _ _ _ _ h _ _ hh => type_e_weak_aux h _ _ hh.1 hh.2,
         fun _ _ _ _ h _ _ hh => type_es_weak_aux h _ _ hh.1 hh.2,
         fun _ _ _ _ h _ _ hh => type_funs_weak_aux h _ _ hh.1 hh.2⟩
/- HOL4:
Theorem type_e_weakening:
 (!tenv tenvE e t tenv' tenvE'.
   type_e tenv tenvE e t ∧ weak tenv' tenv ∧ weak_tenvE tenvE' tenvE ⇒ type_e tenv' tenvE' e t) ∧
 (!tenv tenvE es ts tenv' tenvE'.
   type_es tenv tenvE es ts ∧ weak tenv' tenv ∧ weak_tenvE tenvE' tenvE ⇒ type_es tenv' tenvE' es ts) ∧
 (!tenv tenvE funs bindings tenv' tenvE'.
   type_funs tenv tenvE funs bindings ∧ weak tenv' tenv ∧ weak_tenvE tenvE' tenvE ⇒ type_funs tenv' tenvE' funs bindings)
-/
theorem type_e_weakening :
    (∀ (tenv : type_env) (tenvE : tenv_val_exp) (e : exp) (t : sem_t)
      (tenv' : type_env) (tenvE' : tenv_val_exp),
      type_e tenv tenvE e t ∧ weak tenv' tenv ∧ weak_tenvE tenvE' tenvE →
      type_e tenv' tenvE' e t) ∧
    (∀ (tenv : type_env) (tenvE : tenv_val_exp) (es : List exp) (ts : List sem_t)
      (tenv' : type_env) (tenvE' : tenv_val_exp),
      type_es tenv tenvE es ts ∧ weak tenv' tenv ∧ weak_tenvE tenvE' tenvE →
      type_es tenv' tenvE' es ts) ∧
    (∀ (tenv : type_env) (tenvE : tenv_val_exp)
      (funs : List (varN × varN × exp)) (bindings : List (varN × sem_t))
      (tenv' : type_env) (tenvE' : tenv_val_exp),
      type_funs tenv tenvE funs bindings ∧ weak tenv' tenv ∧ weak_tenvE tenvE' tenvE →
      type_funs tenv' tenvE' funs bindings) := by
  exact ⟨fun _ _ _ _ _ _ hh => type_e_weak_aux hh.1 _ _ hh.2.1 hh.2.2,
         fun _ _ _ _ _ _ hh => type_es_weak_aux hh.1 _ _ hh.2.1 hh.2.2,
         fun _ _ _ _ _ _ hh => type_funs_weak_aux hh.1 _ _ hh.2.1 hh.2.2⟩
/- HOL4:
Theorem gt_0[local]:
  !x:num.x ≥ 0
-/
theorem gt_0 :
    ∀ (x : Nat), x ≥ 0 := by
  intro x; exact Nat.zero_le x
/- HOL4:
Theorem weak_ctMap_lookup[local]:
  ∀ctMap ctMap' tvs ts stamp.
  weakCT ctMap' ctMap ∧
  FLOOKUP ctMap stamp = SOME (tvs,ts)
  ⇒
  FLOOKUP ctMap' stamp = SOME (tvs,ts)
-/
theorem weak_ctMap_lookup :
    ∀ (cm cm' : ctMap) (tvs : List tvarN) (ts : List sem_t × type_ident) (stmp : stamp),
      weakCT cm' cm ∧ Finmap.FLOOKUP cm stmp = some (tvs, ts) →
      Finmap.FLOOKUP cm' stmp = some (tvs, ts) := by
  intro cm cm' tvs ts stmp ⟨h1, h2⟩
  exact h1 _ _ h2
/- HOL4:
Theorem weakCT_refl:
 !ctMap. weakCT ctMap ctMap
-/
theorem weakCT_refl :
    ∀ (cm : ctMap), weakCT cm cm := by
  intro cm k v h; exact h
/- HOL4:
Theorem weakCT_trans:
 weakCT C1 C2 ∧ weakCT C2 C3 ⇒ weakCT C1 C3
-/
theorem weakCT_trans :
    ∀ (C1 C2 C3 : ctMap), weakCT C1 C2 ∧ weakCT C2 C3 → weakCT C1 C3 := by
  intro C1 C2 C3 ⟨h1, h2⟩ k v h
  exact h1 _ _ (h2 _ _ h)
/- HOL4:
Theorem disjoint_env_weakCT:
 !ctMap ctMap'.
  DISJOINT (FDOM ctMap') (FDOM ctMap) ⇒
  weakCT (FUNION ctMap' ctMap) ctMap
-/
theorem disjoint_env_weakCT :
    ∀ (cm cm' : ctMap),
      Set.Disjoint (Finmap.FDOM cm') (Finmap.FDOM cm) →
      weakCT (Finmap.FUNION cm' cm) cm := by
  intro cm cm' hd k v h
  have hk := hd k
  simp only [Finmap.FDOM] at hk
  simp only [Finmap.FUNION]
  cases hc : cm' k with
  | none => exact h
  | some w => exact absurd ⟨by simp [hc], by simp [h]⟩ hk
/- HOL4:
Theorem type_tenv_ctor_weakening:
 !ctMap tenvC envC ctMap'.
  weakCT ctMap' ctMap ∧
  nsAll2 (type_ctor ctMap) envC tenvC
  ⇒
  nsAll2 (type_ctor ctMap') envC tenvC
-/
theorem type_tenv_ctor_weakening :
    ∀ (cm : ctMap) (tenvC : tenv_ctor) (envC : env_ctor) (cm' : ctMap),
      weakCT cm' cm ∧ nsAll2 (type_ctor cm) envC tenvC →
      nsAll2 (type_ctor cm') envC tenvC := by
  intro cm tenvC envC cm' ⟨h1, h2⟩
  refine nsAll2_mono ?_ h2
  intro x y z ⟨ha, hb⟩
  exact ⟨h1 _ _ ha, hb⟩
/- HOL4:
Theorem type_tenv_val_weakening_lemma[local]:
  !ctMap tenvS tenvV envV ctMap' tenvS'.
  weakCT ctMap' ctMap ∧
  weakS tenvS' tenvS ∧
  nsAll2 (λi v (tvs,t).
          ∀tvs' ctMap' tenvS'.
            (tvs = 0 ∨ tvs = tvs') ∧
            weakCT ctMap' ctMap ∧
            weakS tenvS' tenvS
            ⇒
            type_v tvs' ctMap' tenvS' v t)
         envV tenvV
  ⇒
  nsAll2 (λi v (tvs,t). type_v tvs ctMap' tenvS' v t) envV tenvV
-/
theorem type_tenv_val_weakening_lemma :
    ∀ (cm : ctMap) (tenvS : tenv_store) (tenvV : tenv_val) (envV : env_val)
      (cm' : ctMap) (tenvS' : tenv_store),
      weakCT cm' cm ∧
      weakS tenvS' tenvS ∧
      nsAll2 (fun (i : cml_id modN varN) (val_ : v) (p : Nat × sem_t) =>
        ∀ (tvs' : Nat) (cm'' : ctMap) (tenvS'' : tenv_store),
          (p.1 = 0 ∨ p.1 = tvs') ∧ weakCT cm'' cm ∧ weakS tenvS'' tenvS →
          type_v tvs' cm'' tenvS'' val_ p.2) envV tenvV →
      nsAll2 (fun (_ : cml_id modN varN) (val_ : v) (p : Nat × sem_t) =>
        type_v p.1 cm' tenvS' val_ p.2) envV tenvV := by
  intro cm tenvS tenvV envV cm' tenvS' ⟨h1, h2, h3⟩
  refine nsAll2_mono ?_ h3
  intro x y z h
  exact h z.1 cm' tenvS' ⟨Or.inr rfl, h1, h2⟩
theorem weak_tenvE_refl (tenvE : tenv_val_exp) : weak_tenvE tenvE tenvE :=
  ⟨Nat.le_refl _, fun _ _ _ _ => Iff.rfl⟩

/- HOL4:
Theorem type_v_weakening:
 (!tvs ctMap tenvS v t. type_v tvs ctMap tenvS v t ⇒
    !tvs' ctMap' tenvS'.
      ((tvs = 0) ∨ (tvs = tvs')) ∧ weakCT ctMap' ctMap ∧ weakS tenvS' tenvS ⇒
      type_v tvs' ctMap' tenvS' v t)
-/
theorem type_v_weakening :
    ∀ (tvs : Nat) (cm : ctMap) (tenvS : tenv_store) (val_ : v) (t : sem_t),
      type_v tvs cm tenvS val_ t →
      ∀ (tvs' : Nat) (cm' : ctMap) (tenvS' : tenv_store),
        (tvs = 0 ∨ tvs = tvs') ∧ weakCT cm' cm ∧ weakS tenvS' tenvS →
        type_v tvs' cm' tenvS' val_ t := by
  intro tvs cm tenvS val_ t h
  induction h with
  | litv_int => intros; exact .litv_int ..
  | litv_char => intros; exact .litv_char ..
  | litv_str => intros; exact .litv_str ..
  | litv_word8 => intros; exact .litv_word8 ..
  | litv_word64 => intros; exact .litv_word64 ..
  | litv_float64 => intros; exact .litv_float64 ..
  | conv_some tvs cm tenvS ts' tvs0 vs ts ti stmp hc hl hlen hvs hlk ih =>
    intro tvs' cm' tenvS' ⟨ht, hcm, hs⟩
    refine .conv_some _ _ _ ts' tvs0 vs ts ti stmp ?_ hl hlen
      (fun i hi => ih i hi _ _ _ ⟨ht, hcm, hs⟩) (hcm _ _ hlk)
    intro t' ht'
    exact check_freevars_add _ _ _ (hc t' ht') _ (by omega)
  | conv_none tvs cm tenvS vs ts hlen hvs ih =>
    intro tvs' cm' tenvS' ⟨ht, hcm, hs⟩
    exact .conv_none _ _ _ vs ts hlen (fun i hi => ih i hi _ _ _ ⟨ht, hcm, hs⟩)
  | closure tvs cm tenvS tenv tenvE env n e t1 t2 hok heok hn0 hctor hdom hm1 hm2 hty hfv he ih =>
    intro tvs' cm' tenvS' ⟨ht, hcm, hs⟩
    refine .closure _ _ _ tenv tenvE env n e t1 t2 hok heok hn0
      (type_tenv_ctor_weakening _ _ _ _ ⟨hcm, hctor⟩) hdom hm1 hm2
      (fun id_ w p ha hb => ih id_ w p ha hb p.1 cm' tenvS' ⟨Or.inr rfl, hcm, hs⟩)
      (check_freevars_add _ _ _ hfv _ (by omega)) ?_
    rcases ht with rfl | rfl
    · exact type_e_weak_aux he tenv _ ⟨rfl, weak_tenv_refl tenv hok.1⟩
        (weak_tenvE_bind _ _ _ _ _
          (weak_tenvE_bind_tvar2 tenvE tenvE tvs' ⟨heok, hn0, weak_tenvE_refl tenvE⟩))
    · exact he
  | recclosure tvs cm tenvS tenv tenvE env n funs bindings t hok heok hn0 hctor hdom hm1 hm2 hty
      hf hal hd hmem ih =>
    intro tvs' cm' tenvS' ⟨ht, hcm, hs⟩
    refine .recclosure _ _ _ tenv tenvE env n funs bindings t hok heok hn0
      (type_tenv_ctor_weakening _ _ _ _ ⟨hcm, hctor⟩) hdom hm1 hm2
      (fun id_ w p ha hb => ih id_ w p ha hb p.1 cm' tenvS' ⟨Or.inr rfl, hcm, hs⟩)
      ?_ hal hd hmem
    rcases ht with rfl | rfl
    · exact type_funs_weak_aux hf tenv _ ⟨rfl, weak_tenv_refl tenv hok.1⟩
        (weak_tenvE_bind_var_list _ _ _ _
          (weak_tenvE_bind_tvar2 tenvE tenvE tvs' ⟨heok, hn0, weak_tenvE_refl tenvE⟩))
    · exact hf
  | loc_ref tvs cm tenvS t n hc hlk =>
    intro tvs' cm' tenvS' ⟨ht, hcm, hs⟩
    exact .loc_ref _ _ _ t n hc (hs _ _ hlk)
  | loc_w8array tvs cm tenvS n hlk =>
    intro tvs' cm' tenvS' ⟨ht, hcm, hs⟩
    exact .loc_w8array _ _ _ n (hs _ _ hlk)
  | loc_varray tvs cm tenvS t n hc hlk =>
    intro tvs' cm' tenvS' ⟨ht, hcm, hs⟩
    exact .loc_varray _ _ _ t n hc (hs _ _ hlk)
  | vectorv tvs cm tenvS t vs hc hvs ih =>
    intro tvs' cm' tenvS' ⟨ht, hcm, hs⟩
    exact .vectorv _ _ _ t vs hc (fun w hw => ih w hw _ _ _ ⟨ht, hcm, hs⟩)
/- HOL4:
Theorem type_all_env_weakening:
 !ctMap tenvS tenv env ctMap' tenvS'.
  weakCT ctMap' ctMap ∧
  weakS tenvS' tenvS ∧
  type_all_env ctMap tenvS env tenv
  ⇒
  type_all_env ctMap' tenvS' env tenv
-/
theorem type_all_env_weakening :
    ∀ (cm : ctMap) (tenvS : tenv_store) (tenv : type_env) (env : sem_env)
      (cm' : ctMap) (tenvS' : tenv_store),
      weakCT cm' cm ∧ weakS tenvS' tenvS ∧ type_all_env cm tenvS env tenv →
      type_all_env cm' tenvS' env tenv := by
  intro cm tenvS tenv env cm' tenvS' ⟨h1, h2, h3, h4⟩
  refine ⟨type_tenv_ctor_weakening _ _ _ _ ⟨h1, h3⟩, ?_⟩
  refine nsAll2_mono ?_ h4
  intro x y z h
  exact type_v_weakening _ _ _ _ _ h _ _ _ ⟨Or.inr rfl, h1, h2⟩
/- HOL4:
Theorem type_sv_weakening:
 !ctMap tenvS st sv ctMap' tenvS'.
  type_sv ctMap tenvS sv st ∧
  weakCT ctMap' ctMap ∧
  weakS tenvS' tenvS
  ⇒
  type_sv ctMap' tenvS' sv st
-/
theorem type_sv_weakening :
    ∀ (cm : ctMap) (tenvS : tenv_store) (st : store_t) (sv : store_v v)
      (cm' : ctMap) (tenvS' : tenv_store),
      type_sv cm tenvS sv st ∧ weakCT cm' cm ∧ weakS tenvS' tenvS →
      type_sv cm' tenvS' sv st := by
  intro cm tenvS st sv cm' tenvS' ⟨h1, h2, h3⟩
  cases sv <;> cases st <;> simp only [type_sv] at h1 ⊢
  · exact type_v_weakening _ _ _ _ _ h1 _ _ _ ⟨Or.inl rfl, h2, h3⟩
  · intro w hw
    exact type_v_weakening _ _ _ _ _ (h1 w hw) _ _ _ ⟨Or.inl rfl, h2, h3⟩
/- HOL4:
Theorem type_s_weakening:
 !ctMap tenvS st ctMap'.
  type_s ctMap tenvS st ∧
  weakCT ctMap' ctMap
  ⇒
  type_s ctMap' tenvS st
-/
theorem type_s_weakening :
    ∀ (cm : ctMap) (tenvS : tenv_store) (st : store v) (cm' : ctMap),
      type_s cm st tenvS ∧ weakCT cm' cm →
      type_s cm' st tenvS := by
  intro cm tenvS st cm' ⟨h1, h2⟩ l
  refine ⟨(h1 l).1, ?_⟩
  intro st' sv hh
  exact type_sv_weakening _ _ _ _ _ _ ⟨(h1 l).2 st' sv hh, h2, weakS_refl _⟩
/- HOL4:
Theorem weak_tenv_extend_dec_tenv:
   !tenv1 tenv2 tenv3.
    tenv_val_ok tenv1.v ∧
    weak_tenv tenv2 tenv3 ⇒
    weak_tenv (extend_dec_tenv tenv1 tenv2) (extend_dec_tenv tenv1 tenv3)
-/
theorem weak_tenv_extend_dec_tenv :
    ∀ (tenv1 tenv2 tenv3 : type_env),
      tenv_val_ok tenv1.v ∧ weak_tenv tenv2 tenv3 →
      weak_tenv (extend_dec_tenv tenv1 tenv2) (extend_dec_tenv tenv1 tenv3) := by
  intro tenv1 tenv2 tenv3 ⟨h1, h2, h3⟩
  have hr := weak_tenv_refl tenv1 h1
  exact ⟨nsSub_nsAppend2 _ _ _ _ ⟨hr.1, h2⟩, nsSub_nsAppend2 _ _ _ _ ⟨hr.2, h3⟩⟩

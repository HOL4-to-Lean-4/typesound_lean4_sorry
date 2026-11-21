/-
  Translation of typeSysPropsScript.sml
  Theorems about the type system.
-/
import LeanTypeSound.HOL4Prelude
import LeanTypeSound.Ast
import LeanTypeSound.Namespace
import LeanTypeSound.TypeSystem
import LeanTypeSound.TypeSoundInvariants
import LeanTypeSound.NamespaceProps
import LeanTypeSound.SemanticPrimitivesProps
import LeanTypeSound.BAux1
import LeanTypeSound.BAux2

open HOL4

-- ============================================================
-- Definitions
-- ============================================================

/- HOL4:
Definition type_pes_def:
  type_pes tvs tvs' tenv tenvE pes t1 t2 ⇔
    (∀(p,e)::set pes.
      ∃bindings.
        ALL_DISTINCT (pat_bindings p []) ∧
        type_p tvs tenv p t1 bindings ∧
        type_e tenv (bind_var_list tvs' bindings tenvE) e t2)
End
-/
def type_pes (tvs tvs' : Nat) (tenv : type_env) (tenvE : tenv_val_exp)
    (pes : List (pat × exp)) (t1 t2 : sem_t) : Prop :=
  ∀ pe, pe ∈ pes →
    ∃ bindings,
      ALL_DISTINCT (pat_bindings pe.1 []) ∧
      type_p tvs tenv pe.1 t1 bindings ∧
      type_e tenv (bind_var_list tvs' bindings tenvE) pe.2 t2

/- HOL4:
Definition deBruijn_subst_tenvE_def:
(deBruijn_subst_tenvE targs Empty = Empty) ∧
(deBruijn_subst_tenvE targs (Bind_tvar tvs env) =
  Bind_tvar tvs (deBruijn_subst_tenvE targs env)) ∧
(deBruijn_subst_tenvE targs (Bind_name x tvs t env) =
  Bind_name x tvs (deBruijn_subst (tvs + num_tvs env)
                                  (MAP (deBruijn_inc 0 (tvs + num_tvs env)) targs)
                                  t)
       (deBruijn_subst_tenvE targs env))
End
-/
def deBruijn_subst_tenvE (targs : List sem_t) : tenv_val_exp → tenv_val_exp
  | .Empty => .Empty
  | .Bind_tvar tvs env => .Bind_tvar tvs (deBruijn_subst_tenvE targs env)
  | .Bind_name x tvs t env =>
    .Bind_name x tvs
      (deBruijn_subst (tvs + num_tvs env)
        (targs.map (deBruijn_inc 0 (tvs + num_tvs env))) t)
      (deBruijn_subst_tenvE targs env)

/- HOL4:
Definition db_merge_def:
(db_merge Empty e = e) ∧
(db_merge (Bind_tvar tvs e1) e2 = Bind_tvar tvs (db_merge e1 e2)) ∧
(db_merge (Bind_name x tvs t e1) e2 = Bind_name x tvs t (db_merge e1 e2))
End
-/
def db_merge : tenv_val_exp → tenv_val_exp → tenv_val_exp
  | .Empty, e => e
  | .Bind_tvar tvs e1, e2 => .Bind_tvar tvs (db_merge e1 e2)
  | .Bind_name x tvs t e1, e2 => .Bind_name x tvs t (db_merge e1 e2)

/- HOL4:
Definition type_def_to_ctMap_def:
  (type_def_to_ctMap tenvT next_stamp [] [] = []) ∧
  (type_def_to_ctMap tenvT next_stamp ((tvs,tn,ctors)::tds) (id::ids) =
    type_def_to_ctMap tenvT (next_stamp + 1) tds ids ++
    REVERSE
      (MAP (\(cn,ts).
        (TypeStamp cn next_stamp, (tvs, MAP (type_name_subst tenvT) ts, id)))
        ctors))
End
-/
def type_def_to_ctMap (tenvT : tenv_abbrev) (next_stamp : Nat) :
    List (List tvarN × mlstring × List (conN × List ast_t)) →
    List type_ident → List (stamp × (List tvarN × List sem_t × type_ident))
  | [], [] => []
  | (tvs, _, ctors) :: tds, id_ :: ids =>
    type_def_to_ctMap tenvT (next_stamp + 1) tds ids ++
    (ctors.map fun (cn, ts) =>
      (stamp.TypeStamp cn next_stamp, (tvs, ts.map (type_name_subst tenvT), id_))).reverse
  | _, _ => []

/- HOL4:
Definition tenv_names_def[simp]:
  (tenv_names Empty = {}) ∧
  (tenv_names (Bind_tvar _ e) = tenv_names e) ∧
  (tenv_names (Bind_name n _ _ e) = n INSERT tenv_names e)
End
-/
def tenv_names : tenv_val_exp → Set mlstring
  | .Empty => ∅
  | .Bind_tvar _ e => tenv_names e
  | .Bind_name n _ _ e => {n} ∪ tenv_names e

-- ============================================================
-- Theorem stubs
-- ============================================================

attribute [local simp] BAux.check_freevars_Tvar BAux.check_freevars_Tvar_db
  BAux.check_freevars_Tapp BAux.EVERY_eq

/- HOL4:
Theorem unchanged_tenv[simp]:
  !(tenv : type_env).
  <| v := tenv.v; c := tenv.c; t := tenv.t |> = tenv
-/
theorem unchanged_tenv :
    ∀ (tenv : type_env),
      { v := tenv.v, c := tenv.c, t := tenv.t : type_env} = tenv := by
  intro tenv; rfl
/- HOL4:
Theorem extend_dec_tenv_assoc[simp]:
   !tenv1 tenv2 tenv3.
    extend_dec_tenv tenv1 (extend_dec_tenv tenv2 tenv3)
    =
    extend_dec_tenv (extend_dec_tenv tenv1 tenv2) tenv3
-/
theorem extend_dec_tenv_assoc_thm :
    ∀ (tenv1 tenv2 tenv3 : type_env),
      extend_dec_tenv tenv1 (extend_dec_tenv tenv2 tenv3) =
      extend_dec_tenv (extend_dec_tenv tenv1 tenv2) tenv3 := by
  intro t1 t2 t3
  simp [extend_dec_tenv, BAux.ns_nsAppend_assoc]
/- HOL4:
Theorem tenv_val_ok_nsEmpty[simp]:
   tenv_val_ok nsEmpty
-/
theorem tenv_val_ok_nsEmpty :
    tenv_val_ok nsEmpty := by
  unfold tenv_val_ok
  exact BAux.ns_nsAll_nsEmpty _
/- HOL4:
Theorem tenv_ctor_ok_nsEmpty[simp]:
   tenv_ctor_ok nsEmpty
-/
theorem tenv_ctor_ok_nsEmpty :
    tenv_ctor_ok nsEmpty := by
  unfold tenv_ctor_ok
  exact BAux.ns_nsAll_nsEmpty _
/- HOL4:
Theorem tenv_abbrev_ok_nsEmpty[simp]:
   tenv_abbrev_ok nsEmpty
-/
theorem tenv_abbrev_ok_nsEmpty :
    tenv_abbrev_ok nsEmpty := by
  unfold tenv_abbrev_ok
  exact BAux.ns_nsAll_nsEmpty _
/- HOL4:
Theorem tenv_ok_empty[simp]:
   tenv_ok <| v := nsEmpty; c := nsEmpty; t := nsEmpty |>
-/
theorem tenv_ok_empty :
    tenv_ok { v := nsEmpty, c := nsEmpty, t := nsEmpty } := by
  exact ⟨tenv_val_ok_nsEmpty, tenv_ctor_ok_nsEmpty, tenv_abbrev_ok_nsEmpty⟩
/- HOL4:
Theorem check_freevars_add:
 (!tvs tvs' t. check_freevars tvs tvs' t ⇒
  !tvs''. tvs'' ≥ tvs ⇒ check_freevars tvs'' tvs' t)
-/
theorem check_freevars_add :
    ∀ (tvs : Nat) (tvs' : List tvarN) (t : sem_t),
      check_freevars tvs tvs' t →
      ∀ (tvs'' : Nat), tvs'' ≥ tvs → check_freevars tvs'' tvs' t := by
  intro tvs tvs' t
  induction t using BAux.sem_t_ind with
  | hvar tv => intro h tvs'' _; simpa using h
  | hdb n => intro h tvs'' h2; simp at h ⊢; omega
  | happ ts tn ih =>
    intro h tvs'' h2
    simp at h ⊢
    intro x hx
    exact ih x hx (h x hx) tvs'' h2
/- HOL4:
Theorem check_freevars_subst_single:
 !dbmax tvs t tvs' ts.
  LENGTH tvs = LENGTH ts ∧
  check_freevars dbmax tvs t ∧
  EVERY (check_freevars dbmax tvs') ts
  ⇒
  check_freevars dbmax tvs' (type_subst (Finmap.alist_to_fmap (ZIP (tvs,ts))) t)
-/
theorem check_freevars_subst_single :
    ∀ (dbmax : Nat) (tvs : List tvarN) (t : sem_t) (tvs' : List tvarN) (ts : List sem_t),
      tvs.length = ts.length ∧
      check_freevars dbmax tvs t ∧
      EVERY (check_freevars dbmax tvs') ts →
      check_freevars dbmax tvs' (type_subst (Finmap.alist_to_fmap (ZIP (tvs, ts))) t) := by
  intro dbmax tvs t tvs' ts
  induction t using BAux.sem_t_ind with
  | hvar tv =>
    rintro ⟨hl, h, he⟩
    simp at h he
    obtain ⟨t, hm, hf⟩ := BAux.flookup_zip_mem tvs ts tv hl h
    simp [type_subst, hf]
    exact he t hm
  | hdb n => rintro ⟨hl, h, he⟩; simpa [type_subst] using h
  | happ ts' tn ih =>
    rintro ⟨hl, h, he⟩
    simp at h
    simp [type_subst]
    intro x hx
    exact ih x hx ⟨hl, h x hx, he⟩
/- HOL4:
Theorem deBruijn_inc0:
 (!t sk. deBruijn_inc sk 0 t = t) ∧
 (!ts sk. MAP (deBruijn_inc sk 0) ts = ts)
-/
theorem deBruijn_inc0 :
    (∀ (t : sem_t) (sk : Nat), deBruijn_inc sk 0 t = t) ∧
    (∀ (ts : List sem_t) (sk : Nat), ts.map (deBruijn_inc sk 0) = ts) := by
  have h1 : ∀ (t : sem_t) (sk : Nat), deBruijn_inc sk 0 t = t := by
    intro t
    induction t using BAux.sem_t_ind with
    | hvar tv => intro sk; simp [deBruijn_inc]
    | hdb n => intro sk; simp [deBruijn_inc]
    | happ ts tn ih =>
      intro sk
      simp [deBruijn_inc]
      exact BAux.map_eq_self _ _ (fun x hx => ih x hx sk)
  exact ⟨h1, fun ts sk => BAux.map_eq_self _ _ (fun x _ => h1 x sk)⟩
/- HOL4:
Theorem deBruijn_inc_deBruijn_inc:
 !sk i2 t i1.
  deBruijn_inc sk i1 (deBruijn_inc sk i2 t) = deBruijn_inc sk (i1 + i2) t
-/
theorem deBruijn_inc_deBruijn_inc :
    ∀ (sk i2 : Nat) (t : sem_t) (i1 : Nat),
      deBruijn_inc sk i1 (deBruijn_inc sk i2 t) = deBruijn_inc sk (i1 + i2) t := by
  intro sk i2 t
  induction t using BAux.sem_t_ind with
  | hvar tv => intro i1; simp [deBruijn_inc]
  | hdb n =>
    intro i1
    by_cases h : n < sk
    · simp [deBruijn_inc, h]
    · have h' : ¬ (n + i2 < sk) := by omega
      simp [deBruijn_inc, h, h']; omega
  | happ ts tn ih =>
    intro i1
    simp [deBruijn_inc]
    intro x hx
    exact ih x hx i1
/- HOL4: [local]
Theorem deBuijn_inc_lem1:
  !sk i2 t i1.
  deBruijn_inc sk i1 (deBruijn_inc 0 (sk + i2) t) = deBruijn_inc 0 (i1 + (sk + i2)) t
-/
theorem deBuijn_inc_lem1 :
    ∀ (sk i2 : Nat) (t : sem_t) (i1 : Nat),
      deBruijn_inc sk i1 (deBruijn_inc 0 (sk + i2) t) = deBruijn_inc 0 (i1 + (sk + i2)) t := by
  intro sk i2 t
  induction t using BAux.sem_t_ind with
  | hvar tv => intro i1; simp [deBruijn_inc]
  | hdb n =>
    intro i1
    have h' : ¬ (n + (sk + i2) < sk) := by omega
    simp [deBruijn_inc, h']; omega
  | happ ts tn ih =>
    intro i1
    simp [deBruijn_inc]
    intro x hx
    exact ih x hx i1
/- HOL4: [local]
Theorem type_subst_deBruijn_inc_single:
  !s t ts tvs inc sk.
  (LENGTH tvs = LENGTH ts) ∧
  (s = Finmap.alist_to_fmap (ZIP (tvs,ts))) ∧
  check_freevars 0 tvs t ⇒
  (deBruijn_inc sk inc (type_subst s t) =
   type_subst (Finmap.alist_to_fmap (ZIP (tvs, MAP (\t. deBruijn_inc sk inc t) ts))) t)
-/
theorem type_subst_deBruijn_inc_single :
    ∀ (s : Finmap tvarN sem_t) (t : sem_t) (ts : List sem_t) (tvs : List tvarN) (inc sk : Nat),
      tvs.length = ts.length ∧
      s = Finmap.alist_to_fmap (ZIP (tvs, ts)) ∧
      check_freevars 0 tvs t →
      deBruijn_inc sk inc (type_subst s t) =
      type_subst (Finmap.alist_to_fmap (ZIP (tvs, ts.map (fun t => deBruijn_inc sk inc t)))) t := by
  intro s t ts tvs inc sk
  induction t using BAux.sem_t_ind with
  | hvar tv =>
    rintro ⟨hl, rfl, h⟩
    simp only [type_subst]
    have := BAux.flookup_zip_map (fun t => deBruijn_inc sk inc t) tvs ts tv
    rw [this]
    cases hf : Finmap.FLOOKUP (Finmap.alist_to_fmap (ZIP (tvs, ts))) tv with
    | none => simp [deBruijn_inc]
    | some t => simp
  | hdb n => rintro ⟨hl, rfl, h⟩; simp at h
  | happ ts' tn ih =>
    rintro ⟨hl, rfl, h⟩
    simp at h
    simp [type_subst, deBruijn_inc]
    intro x hx
    exact ih x hx ⟨hl, rfl, h x hx⟩
/- HOL4:
Theorem type_subst_deBruijn_inc_list:
 !ts' ts tvs inc sk.
  (LENGTH tvs = LENGTH ts) ∧
  EVERY (check_freevars 0 tvs) ts' ⇒
  (MAP (deBruijn_inc sk inc) (MAP (type_subst (Finmap.alist_to_fmap (ZIP (tvs,ts)))) ts') =
   MAP (type_subst (Finmap.alist_to_fmap (ZIP (tvs, MAP (\t. deBruijn_inc sk inc t) ts)))) ts')
-/
theorem type_subst_deBruijn_inc_list :
    ∀ (ts' ts : List sem_t) (tvs : List tvarN) (inc sk : Nat),
      tvs.length = ts.length ∧
      EVERY (check_freevars 0 tvs) ts' →
      (ts'.map (type_subst (Finmap.alist_to_fmap (ZIP (tvs, ts))))).map (deBruijn_inc sk inc) =
      ts'.map (type_subst (Finmap.alist_to_fmap (ZIP (tvs, ts.map (fun t => deBruijn_inc sk inc t))))) := by
  intro ts' ts tvs inc sk ⟨hl, h⟩
  simp at h
  simp
  intro x hx
  exact type_subst_deBruijn_inc_single _ x ts tvs inc sk ⟨hl, rfl, h x hx⟩
/- HOL4: [local]
Theorem check_freevars_deBruijn_inc:
  !tvs tvs' t. check_freevars tvs tvs' t ⇒
  !n n'. check_freevars (n+tvs) tvs' (deBruijn_inc n' n t)
-/
theorem check_freevars_deBruijn_inc :
    ∀ (tvs : Nat) (tvs' : List tvarN) (t : sem_t),
      check_freevars tvs tvs' t →
      ∀ (n n' : Nat), check_freevars (n + tvs) tvs' (deBruijn_inc n' n t) := by
  intro tvs tvs' t
  induction t using BAux.sem_t_ind with
  | hvar tv => intro h n n'; simpa [deBruijn_inc] using h
  | hdb m =>
    intro h n n'
    simp at h
    by_cases hm : m < n'
    · simp [deBruijn_inc, hm]; omega
    · simp [deBruijn_inc, hm]; omega
  | happ ts tn ih =>
    intro h n n'
    simp at h
    simp [deBruijn_inc]
    intro x hx
    exact ih x hx (h x hx) n n'
/- HOL4:
Theorem nil_deBruijn_inc:
 ∀skip tvs t.
  (check_freevars skip [] t ∨ check_freevars skip [] (deBruijn_inc skip tvs t))
  ⇒
  (deBruijn_inc skip tvs t = t)
-/
theorem nil_deBruijn_inc :
    ∀ (skip tvs : Nat) (t : sem_t),
      (check_freevars skip [] t ∨ check_freevars skip [] (deBruijn_inc skip tvs t)) →
      deBruijn_inc skip tvs t = t := by
  intro skip tvs t
  induction t using BAux.sem_t_ind with
  | hvar tv => intro _; simp [deBruijn_inc]
  | hdb m =>
    intro h
    by_cases hm : m < skip
    · simp [deBruijn_inc, hm]
    · simp [deBruijn_inc, hm] at h; omega
  | happ ts tn ih =>
    intro h
    simp [deBruijn_inc] at h ⊢
    apply BAux.map_eq_self
    intro x hx
    apply ih x hx
    rcases h with h | h
    · exact Or.inl (h x hx)
    · exact Or.inr (h x hx)
/- HOL4:
Theorem deBruijn_subst_check_freevars:
 !tvs tvs' t ts n.
  check_freevars tvs tvs' t ∧
  EVERY (check_freevars tvs tvs') ts
  ⇒
  check_freevars tvs tvs' (deBruijn_subst 0 ts t)
-/
theorem deBruijn_subst_check_freevars :
    ∀ (tvs : Nat) (tvs' : List tvarN) (t : sem_t) (ts : List sem_t) (n : Nat),
      check_freevars tvs tvs' t ∧
      EVERY (check_freevars tvs tvs') ts →
      check_freevars tvs tvs' (deBruijn_subst 0 ts t) := by
  intro tvs tvs' t ts _
  induction t using BAux.sem_t_ind with
  | hvar tv => rintro ⟨h, he⟩; simpa [deBruijn_subst] using h
  | hdb m =>
    rintro ⟨h, he⟩
    simp at h he
    by_cases hm : m < ts.length
    · rw [BAux.subst_db_mid 0 ts m (by omega) (by omega)]
      exact he _ (BAux.EL_mem _ _ (by omega))
    · rw [BAux.subst_db_ge 0 ts m (by omega)]
      simp; omega
  | happ ts' tn ih =>
    rintro ⟨h, he⟩
    simp at h
    simp [deBruijn_subst]
    intro x hx
    exact ih x hx ⟨h x hx, he⟩
/- HOL4:
Theorem deBruijn_subst_check_freevars2:
 !tvs tvs' t ts n tvs''.
  check_freevars (LENGTH ts) tvs' t ∧
  EVERY (check_freevars tvs tvs') ts
  ⇒
  check_freevars tvs tvs' (deBruijn_subst 0 ts t)
-/
theorem deBruijn_subst_check_freevars2 :
    ∀ (tvs : Nat) (tvs' : List tvarN) (t : sem_t) (ts : List sem_t) (n : Nat) (tvs'' : List tvarN),
      check_freevars ts.length tvs' t ∧
      EVERY (check_freevars tvs tvs') ts →
      check_freevars tvs tvs' (deBruijn_subst 0 ts t) := by
  intro tvs tvs' t ts _ _
  induction t using BAux.sem_t_ind with
  | hvar tv => rintro ⟨h, he⟩; simpa [deBruijn_subst] using h
  | hdb m =>
    rintro ⟨h, he⟩
    simp at h he
    rw [BAux.subst_db_mid 0 ts m (by omega) (by omega)]
    exact he _ (BAux.EL_mem _ _ (by omega))
  | happ ts' tn ih =>
    rintro ⟨h, he⟩
    simp at h
    simp [deBruijn_subst]
    intro x hx
    exact ih x hx ⟨h x hx, he⟩
/- HOL4:
Theorem check_freevars_subst_inc:
 ∀tvs tvs2 t.
  check_freevars tvs tvs2 t ⇒
  ∀tvs' targs tvs1.
  tvs = LENGTH targs + tvs' ∧
  EVERY (check_freevars (tvs1 + tvs') tvs2) targs
  ⇒
  check_freevars (tvs1 + tvs') tvs2
     (deBruijn_subst 0 targs (deBruijn_inc (LENGTH targs) tvs1 t))
-/
theorem check_freevars_subst_inc :
    ∀ (tvs : Nat) (tvs2 : List tvarN) (t : sem_t),
      check_freevars tvs tvs2 t →
      ∀ (tvs' : Nat) (targs : List sem_t) (tvs1 : Nat),
        tvs = targs.length + tvs' ∧
        EVERY (check_freevars (tvs1 + tvs') tvs2) targs →
        check_freevars (tvs1 + tvs') tvs2
          (deBruijn_subst 0 targs (deBruijn_inc targs.length tvs1 t)) := by
  intro tvs tvs2 t
  induction t using BAux.sem_t_ind with
  | hvar tv => intro h tvs' targs tvs1 _; simpa [deBruijn_subst, deBruijn_inc] using h
  | hdb m =>
    rintro h tvs' targs tvs1 ⟨rfl, he⟩
    simp at h he
    by_cases hm : m < targs.length
    · rw [BAux.inc_db_lt _ _ _ hm, BAux.subst_db_mid 0 targs m (by omega) (by omega)]
      exact he _ (BAux.EL_mem _ _ (by omega))
    · rw [BAux.inc_db_ge _ _ _ (by omega), BAux.subst_db_ge 0 targs _ (by omega)]
      simp; omega
  | happ ts' tn ih =>
    rintro h tvs' targs tvs1 ⟨rfl, he⟩
    simp at h
    simp [deBruijn_subst, deBruijn_inc]
    intro x hx
    exact ih x hx (h x hx) tvs' targs tvs1 ⟨rfl, he⟩
/- HOL4:
Theorem check_freevars_subst:
 ∀tvs tvs2 t.
  check_freevars tvs tvs2 t ⇒
  ∀tvs' targs tvs1.
  tvs = LENGTH targs + tvs' ∧
  EVERY (check_freevars (tvs1 + tvs') tvs2) targs
  ⇒
  check_freevars (tvs1 + tvs') tvs2 (deBruijn_subst 0 targs t)
-/
theorem check_freevars_subst :
    ∀ (tvs : Nat) (tvs2 : List tvarN) (t : sem_t),
      check_freevars tvs tvs2 t →
      ∀ (tvs' : Nat) (targs : List sem_t) (tvs1 : Nat),
        tvs = targs.length + tvs' ∧
        EVERY (check_freevars (tvs1 + tvs') tvs2) targs →
        check_freevars (tvs1 + tvs') tvs2 (deBruijn_subst 0 targs t) := by
  intro tvs tvs2 t
  induction t using BAux.sem_t_ind with
  | hvar tv => intro h tvs' targs tvs1 _; simpa [deBruijn_subst, deBruijn_inc] using h
  | hdb m =>
    rintro h tvs' targs tvs1 ⟨rfl, he⟩
    simp at h he
    by_cases hm : m < targs.length
    · rw [BAux.subst_db_mid 0 targs m (by omega) (by omega)]
      exact he _ (BAux.EL_mem _ _ (by omega))
    · rw [BAux.subst_db_ge 0 targs _ (by omega)]
      simp; omega
  | happ ts' tn ih =>
    rintro h tvs' targs tvs1 ⟨rfl, he⟩
    simp at h
    simp [deBruijn_subst, deBruijn_inc]
    intro x hx
    exact ih x hx (h x hx) tvs' targs tvs1 ⟨rfl, he⟩
/- HOL4: [local]
Theorem type_subst_deBruijn_subst_single:
  !s t tvs tvs' ts ts' inc.
  (LENGTH tvs = LENGTH ts) ∧
  check_freevars 0 tvs t ∧
  (s = Finmap.alist_to_fmap (ZIP (tvs,ts))) ⇒
  (deBruijn_subst inc ts' (type_subst (Finmap.alist_to_fmap (ZIP (tvs,ts))) t) =
   type_subst (Finmap.alist_to_fmap (ZIP (tvs,MAP (\t. deBruijn_subst inc ts' t) ts))) t)
-/
theorem type_subst_deBruijn_subst_single :
    ∀ (s : Finmap tvarN sem_t) (t : sem_t) (tvs : List tvarN) (tvs' : List tvarN)
      (ts ts' : List sem_t) (inc : Nat),
      tvs.length = ts.length ∧
      check_freevars 0 tvs t ∧
      s = Finmap.alist_to_fmap (ZIP (tvs, ts)) →
      deBruijn_subst inc ts' (type_subst (Finmap.alist_to_fmap (ZIP (tvs, ts))) t) =
      type_subst (Finmap.alist_to_fmap (ZIP (tvs, ts.map (fun t => deBruijn_subst inc ts' t)))) t := by
  intro s t tvs tvs' ts ts' inc
  induction t using BAux.sem_t_ind with
  | hvar tv =>
    rintro ⟨hl, h, rfl⟩
    simp only [type_subst]
    have := BAux.flookup_zip_map (fun t => deBruijn_subst inc ts' t) tvs ts tv
    rw [this]
    cases hf : Finmap.FLOOKUP (Finmap.alist_to_fmap (ZIP (tvs, ts))) tv with
    | none => simp [deBruijn_subst]
    | some t => simp
  | hdb n => rintro ⟨hl, h, rfl⟩; simp at h
  | happ ts'' tn ih =>
    rintro ⟨hl, h, rfl⟩
    simp at h
    simp [type_subst, deBruijn_subst]
    intro x hx
    exact ih x hx ⟨hl, h x hx, rfl⟩
/- HOL4:
Theorem type_subst_deBruijn_subst_list:
 !t tvs tvs' ts ts' ts'' inc.
  (LENGTH tvs = LENGTH ts) ∧
  EVERY (check_freevars 0 tvs) ts'' ⇒
  (MAP (deBruijn_subst inc ts') (MAP (type_subst (Finmap.alist_to_fmap (ZIP (tvs,ts)))) ts'') =
   MAP (type_subst (Finmap.alist_to_fmap (ZIP (tvs,MAP (\t. deBruijn_subst inc ts' t) ts)))) ts'')
-/
theorem type_subst_deBruijn_subst_list :
    ∀ (t_ : sem_t) (tvs : List tvarN) (tvs' : List tvarN)
      (ts ts' ts'' : List sem_t) (inc : Nat),
      tvs.length = ts.length ∧
      EVERY (check_freevars 0 tvs) ts'' →
      (ts''.map (type_subst (Finmap.alist_to_fmap (ZIP (tvs, ts))))).map (deBruijn_subst inc ts') =
      ts''.map (type_subst (Finmap.alist_to_fmap (ZIP (tvs, ts.map (fun t => deBruijn_subst inc ts' t))))) := by
  intro _ tvs tvs' ts ts' ts'' inc ⟨hl, h⟩
  simp at h
  simp
  intro x hx
  exact type_subst_deBruijn_subst_single _ x tvs tvs' ts ts' inc ⟨hl, h x hx, rfl⟩
/- HOL4: [local]
Theorem check_freevars_lem:
  !l tvs' t.
  check_freevars l tvs' t ⇒
  !targs n1 tvs.
    (l = n1 + (LENGTH targs)) ∧
    EVERY (check_freevars tvs tvs') targs
     ⇒
     check_freevars (n1 + tvs) tvs'
       (deBruijn_subst n1 (MAP (deBruijn_inc 0 n1) targs) t)
-/
theorem check_freevars_lem :
    ∀ (l : Nat) (tvs' : List tvarN) (t : sem_t),
      check_freevars l tvs' t →
      ∀ (targs : List sem_t) (n1 tvs : Nat),
        l = n1 + targs.length ∧
        EVERY (check_freevars tvs tvs') targs →
        check_freevars (n1 + tvs) tvs'
          (deBruijn_subst n1 (targs.map (deBruijn_inc 0 n1)) t) := by
  intro l tvs' t
  induction t using BAux.sem_t_ind with
  | hvar tv => intro h targs n1 tvs _; simpa [deBruijn_subst] using h
  | hdb m =>
    rintro h targs n1 tvs ⟨rfl, he⟩
    simp at h he
    by_cases hm : m < n1
    · rw [BAux.subst_db_lt _ _ _ hm]; simp; omega
    · rw [BAux.subst_db_mid _ _ _ (by omega) (by simp; omega),
        BAux.EL_map _ _ _ (by omega)]
      exact check_freevars_deBruijn_inc _ _ _ (he _ (BAux.EL_mem _ _ (by omega))) _ _
  | happ ts' tn ih =>
    rintro h targs n1 tvs ⟨rfl, he⟩
    simp at h
    simp [deBruijn_subst]
    intro x hx
    exact ih x hx (h x hx) targs n1 tvs ⟨rfl, he⟩
/- HOL4:
Theorem nil_deBruijn_subst:
 ∀skip tvs t. check_freevars skip [] t ⇒ (deBruijn_subst skip tvs t = t)
-/
theorem nil_deBruijn_subst :
    ∀ (skip : Nat) (tvs : List sem_t) (t : sem_t),
      check_freevars skip [] t →
      deBruijn_subst skip tvs t = t := by
  intro skip tvs t
  induction t using BAux.sem_t_ind with
  | hvar tv => intro _; simp [deBruijn_subst]
  | hdb m =>
    intro h
    simp at h
    exact BAux.subst_db_lt _ _ _ h
  | happ ts tn ih =>
    intro h
    simp at h
    simp [deBruijn_subst]
    exact BAux.map_eq_self _ _ (fun x hx => ih x hx (h x hx))
/- HOL4:
Theorem deBruijn_subst2:
 (!t sk targs targs' tvs'.
  check_freevars (LENGTH targs) [] t ⇒
  (deBruijn_subst sk (MAP (deBruijn_inc 0 sk) targs') (deBruijn_subst 0 targs t) =
   deBruijn_subst 0 (MAP (deBruijn_subst sk (MAP (deBruijn_inc 0 sk) targs')) targs) t)) ∧
 (!ts sk targs targs' tvs'.
  EVERY (check_freevars (LENGTH targs) []) ts ⇒
  (MAP (deBruijn_subst sk (MAP (deBruijn_inc 0 sk) targs')) (MAP (deBruijn_subst 0 targs) ts) =
  (MAP (deBruijn_subst 0 (MAP (deBruijn_subst sk (MAP (deBruijn_inc 0 sk) targs')) targs)) ts)))
-/
theorem deBruijn_subst2_thm :
    (∀ (t : sem_t) (sk : Nat) (targs targs' : List sem_t) (tvs' : List tvarN),
      check_freevars targs.length [] t →
      deBruijn_subst sk (targs'.map (deBruijn_inc 0 sk)) (deBruijn_subst 0 targs t) =
      deBruijn_subst 0 (targs.map (deBruijn_subst sk (targs'.map (deBruijn_inc 0 sk)))) t) ∧
    (∀ (ts : List sem_t) (sk : Nat) (targs targs' : List sem_t) (tvs' : List tvarN),
      EVERY (check_freevars targs.length []) ts →
      (ts.map (deBruijn_subst 0 targs)).map (deBruijn_subst sk (targs'.map (deBruijn_inc 0 sk))) =
      ts.map (deBruijn_subst 0 (targs.map (deBruijn_subst sk (targs'.map (deBruijn_inc 0 sk)))))) := by
  have h1 : ∀ (t : sem_t) (sk : Nat) (targs targs' : List sem_t) (tvs' : List tvarN),
      check_freevars targs.length [] t →
      deBruijn_subst sk (targs'.map (deBruijn_inc 0 sk)) (deBruijn_subst 0 targs t) =
      deBruijn_subst 0 (targs.map (deBruijn_subst sk (targs'.map (deBruijn_inc 0 sk)))) t := by
    intro t sk targs targs' _
    induction t using BAux.sem_t_ind with
    | hvar tv => intro h; simp at h
    | hdb m =>
      intro h
      simp at h
      rw [BAux.subst_db_mid 0 targs m (by omega) (by omega),
        BAux.subst_db_mid 0 _ m (by omega) (by simp; omega), BAux.EL_map _ _ _ (by omega)]
    | happ ts tn ih =>
      intro h
      simp at h
      simp [deBruijn_subst]
      intro x hx
      exact ih x hx (h x hx)
  refine ⟨h1, ?_⟩
  intro ts sk targs targs' tvs' h
  simp at h
  simp
  intro x hx
  exact h1 x sk targs targs' tvs' (h x hx)
/- HOL4:
Theorem type_e_subst_lem3:
 ∀tvs tvs2 t.
  check_freevars tvs tvs2 t ⇒
  ∀tvs' targs n.
  (tvs = n + LENGTH targs) ∧
  EVERY (check_freevars tvs' tvs2) targs
  ⇒
  check_freevars (n + tvs') tvs2
     (deBruijn_subst n (MAP (deBruijn_inc 0 n) targs) t)
-/
theorem type_e_subst_lem3 :
    ∀ (tvs : Nat) (tvs2 : List tvarN) (t : sem_t),
      check_freevars tvs tvs2 t →
      ∀ (tvs' : Nat) (targs : List sem_t) (n : Nat),
        tvs = n + targs.length ∧
        EVERY (check_freevars tvs' tvs2) targs →
        check_freevars (n + tvs') tvs2
          (deBruijn_subst n (targs.map (deBruijn_inc 0 n)) t) := by
  intro tvs tvs2 t h tvs' targs n hh
  exact check_freevars_lem tvs tvs2 t h targs n tvs' hh
/- HOL4: [local]
Theorem type_e_subst_lem5:
  (!t n inc n' targs.
   deBruijn_inc n inc
         (deBruijn_subst (n + n') (MAP (deBruijn_inc 0 (n + n')) targs) t) =
   deBruijn_subst (n + inc + n') (MAP (deBruijn_inc 0 (n + inc + n')) targs)
         (deBruijn_inc n inc t)) ∧
 (!ts n inc n' targs.
   MAP (deBruijn_inc n inc)
         (MAP (deBruijn_subst (n + n') (MAP (deBruijn_inc 0 (n + n')) targs)) ts) =
   MAP (deBruijn_subst (n + inc + n') (MAP (deBruijn_inc 0 (n + inc + n')) targs))
         (MAP (deBruijn_inc n inc) ts))
-/
theorem type_e_subst_lem5 :
    (∀ (t : sem_t) (n inc n' : Nat) (targs : List sem_t),
      deBruijn_inc n inc
        (deBruijn_subst (n + n') (targs.map (deBruijn_inc 0 (n + n'))) t) =
      deBruijn_subst (n + inc + n') (targs.map (deBruijn_inc 0 (n + inc + n')))
        (deBruijn_inc n inc t)) ∧
    (∀ (ts : List sem_t) (n inc n' : Nat) (targs : List sem_t),
      (ts.map (deBruijn_subst (n + n') (targs.map (deBruijn_inc 0 (n + n'))))).map (deBruijn_inc n inc) =
      (ts.map (deBruijn_inc n inc)).map (deBruijn_subst (n + inc + n') (targs.map (deBruijn_inc 0 (n + inc + n'))))) := by
  have h1 : ∀ (t : sem_t) (n inc n' : Nat) (targs : List sem_t),
      deBruijn_inc n inc
        (deBruijn_subst (n + n') (targs.map (deBruijn_inc 0 (n + n'))) t) =
      deBruijn_subst (n + inc + n') (targs.map (deBruijn_inc 0 (n + inc + n')))
        (deBruijn_inc n inc t) := by
    intro t n inc n' targs
    induction t using BAux.sem_t_ind with
    | hvar tv => simp [deBruijn_subst, deBruijn_inc]
    | hdb m =>
      by_cases h1 : m < n
      · rw [BAux.subst_db_lt _ _ _ (by omega), BAux.inc_db_lt _ _ _ h1,
          BAux.subst_db_lt _ _ _ (by omega)]
      · by_cases h2 : m < n + n'
        · rw [BAux.subst_db_lt _ _ _ (by omega), BAux.inc_db_ge _ _ _ (by omega),
            BAux.subst_db_lt _ _ _ (by omega)]
        · by_cases h3 : m < targs.length + (n + n')
          · rw [BAux.subst_db_mid _ _ _ (by omega) (by simp; omega),
              BAux.inc_db_ge _ _ _ (by omega),
              BAux.subst_db_mid _ _ _ (by omega) (by simp; omega),
              BAux.EL_map _ _ _ (by omega), BAux.EL_map _ _ _ (by omega),
              deBuijn_inc_lem1]
            have e1 : m + inc - (n + inc + n') = m - (n + n') := by omega
            have e2 : inc + (n + n') = n + inc + n' := by omega
            rw [e1, e2]
          · rw [BAux.subst_db_ge _ _ _ (by simp; omega), BAux.inc_db_ge _ _ _ (by simp; omega),
              BAux.inc_db_ge _ _ _ (by omega), BAux.subst_db_ge _ _ _ (by simp; omega)]
            simp; omega
    | happ ts tn ih =>
      simp [deBruijn_subst, deBruijn_inc]
      intro x hx
      exact ih x hx
  refine ⟨h1, ?_⟩
  intro ts n inc n' targs
  simp
  intro x hx
  exact h1 x n inc n' targs
/- HOL4:
Theorem subst_inc_cancel:
 (!t ts inc.
  deBruijn_subst 0 ts (deBruijn_inc 0 (inc + LENGTH ts) t)
  =
  deBruijn_inc 0 inc t) ∧
 (!ts' ts inc.
  MAP (deBruijn_subst 0 ts) (MAP (deBruijn_inc 0 (inc + LENGTH ts)) ts')
  =
  MAP (deBruijn_inc 0 inc) ts')
-/
theorem subst_inc_cancel :
    (∀ (t : sem_t) (ts : List sem_t) (inc : Nat),
      deBruijn_subst 0 ts (deBruijn_inc 0 (inc + ts.length) t) =
      deBruijn_inc 0 inc t) ∧
    (∀ (ts' ts : List sem_t) (inc : Nat),
      (ts'.map (deBruijn_inc 0 (inc + ts.length))).map (deBruijn_subst 0 ts) =
      ts'.map (deBruijn_inc 0 inc)) := by
  have h1 : ∀ (t : sem_t) (ts : List sem_t) (inc : Nat),
      deBruijn_subst 0 ts (deBruijn_inc 0 (inc + ts.length) t) =
      deBruijn_inc 0 inc t := by
    intro t ts inc
    induction t using BAux.sem_t_ind with
    | hvar tv => simp [deBruijn_subst, deBruijn_inc]
    | hdb m =>
      rw [BAux.inc_db_ge _ _ _ (by omega), BAux.inc_db_ge _ _ _ (by omega),
        BAux.subst_db_ge _ _ _ (by omega)]
      simp; omega
    | happ ts' tn ih =>
      simp [deBruijn_subst, deBruijn_inc]
      intro x hx
      exact ih x hx
  refine ⟨h1, ?_⟩
  intro ts' ts inc
  simp
  intro x hx
  exact h1 x ts inc
/- HOL4: [local]
Theorem type_e_subst_lem7:
  (!t sk targs targs' tvs' tvs''.
  (deBruijn_subst sk (MAP (deBruijn_inc 0 sk) targs') (deBruijn_subst 0 targs t) =
   deBruijn_subst 0 (MAP (deBruijn_subst sk (MAP (deBruijn_inc 0 sk) targs')) targs)
     (deBruijn_subst (LENGTH targs + sk) (MAP (deBruijn_inc 0 (LENGTH targs + sk)) targs') t))) ∧
 (!ts sk targs targs' tvs' tvs''.
  (MAP (deBruijn_subst sk (MAP (deBruijn_inc 0 sk) targs')) (MAP (deBruijn_subst 0 targs) ts) =
  (MAP (deBruijn_subst 0 (MAP (deBruijn_subst sk (MAP (deBruijn_inc 0 sk) targs')) targs))
       (MAP (deBruijn_subst (LENGTH targs + sk) (MAP (deBruijn_inc 0 (LENGTH targs + sk)) targs')) ts))))
-/
theorem type_e_subst_lem7 :
    (∀ (t : sem_t) (sk : Nat) (targs targs' : List sem_t) (tvs' tvs'' : List tvarN),
      deBruijn_subst sk (targs'.map (deBruijn_inc 0 sk)) (deBruijn_subst 0 targs t) =
      deBruijn_subst 0 (targs.map (deBruijn_subst sk (targs'.map (deBruijn_inc 0 sk))))
        (deBruijn_subst (targs.length + sk) (targs'.map (deBruijn_inc 0 (targs.length + sk))) t)) ∧
    (∀ (ts : List sem_t) (sk : Nat) (targs targs' : List sem_t) (tvs' tvs'' : List tvarN),
      (ts.map (deBruijn_subst 0 targs)).map (deBruijn_subst sk (targs'.map (deBruijn_inc 0 sk))) =
      (ts.map (deBruijn_subst (targs.length + sk) (targs'.map (deBruijn_inc 0 (targs.length + sk))))).map
        (deBruijn_subst 0 (targs.map (deBruijn_subst sk (targs'.map (deBruijn_inc 0 sk)))))) := by
  have h1 : ∀ (t : sem_t) (sk : Nat) (targs targs' : List sem_t) (tvs' tvs'' : List tvarN),
      deBruijn_subst sk (targs'.map (deBruijn_inc 0 sk)) (deBruijn_subst 0 targs t) =
      deBruijn_subst 0 (targs.map (deBruijn_subst sk (targs'.map (deBruijn_inc 0 sk))))
        (deBruijn_subst (targs.length + sk) (targs'.map (deBruijn_inc 0 (targs.length + sk))) t) := by
    intro t sk targs targs' _ _
    induction t using BAux.sem_t_ind with
    | hvar tv => simp [deBruijn_subst]
    | hdb m =>
      by_cases h1 : m < targs.length
      · rw [BAux.subst_db_mid 0 targs m (by omega) (by omega),
          BAux.subst_db_lt _ _ _ (by omega),
          BAux.subst_db_mid 0 _ m (by omega) (by simp; omega), BAux.EL_map _ _ _ (by omega)]
      · by_cases h2 : m < targs.length + sk
        · rw [BAux.subst_db_ge 0 targs m (by omega), BAux.subst_db_lt _ _ _ (by omega),
            BAux.subst_db_lt _ _ _ (by omega), BAux.subst_db_ge 0 _ m (by simp; omega)]
          simp
        · by_cases h3 : m < targs'.length + (targs.length + sk)
          · rw [BAux.subst_db_ge 0 targs m (by omega),
              BAux.subst_db_mid _ _ _ (by omega) (by simp; omega),
              BAux.subst_db_mid _ _ _ (by omega) (by simp; omega),
              BAux.EL_map _ _ _ (by omega), BAux.EL_map _ _ _ (by omega)]
            have e1 : m - targs.length - sk = m - (targs.length + sk) := by omega
            rw [e1]
            have h := subst_inc_cancel.1 (EL (m - (targs.length + sk)) targs')
              (targs.map (deBruijn_subst sk (targs'.map (deBruijn_inc 0 sk)))) sk
            rw [List.length_map, Nat.add_comm sk targs.length] at h
            exact h.symm
          · rw [BAux.subst_db_ge 0 targs m (by omega),
              BAux.subst_db_ge _ _ _ (by simp; omega),
              BAux.subst_db_ge _ _ _ (by simp; omega),
              BAux.subst_db_ge 0 _ _ (by simp; omega)]
            simp; omega
    | happ ts tn ih =>
      simp [deBruijn_subst]
      intro x hx
      exact ih x hx
  refine ⟨h1, ?_⟩
  intro ts sk targs targs' tvs' tvs''
  simp
  intro x hx
  exact h1 x sk targs targs' tvs' tvs''
/- HOL4:
Theorem deBruijn_subst_id:
 (!t n. check_freevars n [] t ⇒ (deBruijn_subst 0 (MAP Tvar_db (COUNT_LIST n)) t = t)) ∧
 (!ts n. EVERY (check_freevars n []) ts ⇒ (MAP (deBruijn_subst 0 (MAP Tvar_db (COUNT_LIST n))) ts = ts))
-/
theorem deBruijn_subst_id :
    (∀ (t : sem_t) (n : Nat),
      check_freevars n [] t →
      deBruijn_subst 0 (GENLIST (fun i => sem_t.Tvar_db i) n) t = t) ∧
    (∀ (ts : List sem_t) (n : Nat),
      EVERY (check_freevars n []) ts →
      ts.map (deBruijn_subst 0 (GENLIST (fun i => sem_t.Tvar_db i) n)) = ts) := by
  have h1 : ∀ (t : sem_t) (n : Nat),
      check_freevars n [] t →
      deBruijn_subst 0 (GENLIST (fun i => sem_t.Tvar_db i) n) t = t := by
    intro t n
    induction t using BAux.sem_t_ind with
    | hvar tv => intro h; simp at h
    | hdb m =>
      intro h
      simp at h
      rw [BAux.subst_db_mid 0 _ m (by omega) (by simp [GENLIST]; omega)]
      simp [GENLIST, EL, h]
    | happ ts tn ih =>
      intro h
      simp at h
      simp [deBruijn_subst]
      exact BAux.map_eq_self _ _ (fun x hx => ih x hx (h x hx))
  refine ⟨h1, ?_⟩
  intro ts n h
  simp at h
  exact BAux.map_eq_self _ _ (fun x hx => h1 x n (h x hx))
/- HOL4:
Theorem deBruijn_subst_freevars:
 !skip targs t tvs.
  skip = 0 ∧
  EVERY (check_freevars tvs []) targs ∧
  check_freevars (LENGTH targs) [] t
  ⇒
  check_freevars tvs [] (deBruijn_subst skip targs t)
-/
theorem deBruijn_subst_freevars :
    ∀ (skip : Nat) (targs : List sem_t) (t : sem_t) (tvs : Nat),
      skip = 0 ∧
      EVERY (check_freevars tvs []) targs ∧
      check_freevars targs.length [] t →
      check_freevars tvs [] (deBruijn_subst skip targs t) := by
  rintro skip targs t tvs ⟨rfl, he, h⟩
  exact deBruijn_subst_check_freevars2 tvs [] t targs 0 [] ⟨h, he⟩
/- HOL4:
Theorem tenv_abbrev_ok_lookup:
 !tenvT tn tvs t.
  tenv_abbrev_ok tenvT ∧
  nsLookup tenvT tn = SOME (tvs,t)
  ⇒
  check_freevars 0 tvs t
-/
theorem tenv_abbrev_ok_lookup :
    ∀ (tenvT : tenv_abbrev) (tn : cml_id modN typeN) (tvs : List tvarN) (t : sem_t),
      tenv_abbrev_ok tenvT ∧
      nsLookup tenvT tn = some (tvs, t) →
      check_freevars 0 tvs t := by
  rintro tenvT tn tvs t ⟨h1, h2⟩
  exact h1 tn (tvs, t) h2
/- HOL4:
Theorem check_freevars_type_name_subst:
 !tvs t dbmax tenvT.
  tenv_abbrev_ok tenvT ∧
  check_type_names tenvT t ∧
  check_freevars_ast tvs t
  ⇒
  check_freevars dbmax tvs (type_name_subst tenvT t)
-/
theorem check_freevars_type_name_subst :
    ∀ (tvs : List tvarN) (t : ast_t) (dbmax : Nat) (tenvT : tenv_abbrev),
      tenv_abbrev_ok tenvT ∧
      check_type_names tenvT t ∧
      check_freevars_ast tvs t →
      check_freevars dbmax tvs (type_name_subst tenvT t) := by
  intro tvs t dbmax tenvT
  induction t using BAux.ast_t_ind with
  | hvar tv =>
    rintro ⟨h1, h2, h3⟩
    simpa [type_name_subst, BAux.check_freevars_ast_Atvar] using h3
  | hfun t1 t2 ih1 ih2 =>
    rintro ⟨h1, h2, h3⟩
    simp [BAux.check_freevars_ast_Atfun, BAux.check_type_names_Atfun] at h2 h3
    simp [type_name_subst, Tfn]
    exact ⟨ih1 ⟨h1, h2.1, h3.1⟩, ih2 ⟨h1, h2.2, h3.2⟩⟩
  | htup ts ih =>
    rintro ⟨h1, h2, h3⟩
    simp [BAux.check_freevars_ast_Attup, BAux.check_type_names_Attup] at h2 h3
    simp [type_name_subst, Ttup]
    intro x hx
    exact ih x hx ⟨h1, h2 x hx, h3 x hx⟩
  | happ ts tn ih =>
    rintro ⟨h1, h2, h3⟩
    rw [BAux.check_type_names_Atapp] at h2
    simp [BAux.check_freevars_ast_Atapp] at h3
    obtain ⟨⟨tvs', t, hl, hlen⟩, h2⟩ := h2
    simp only [type_name_subst, hl]
    apply check_freevars_subst_single dbmax tvs' t tvs (ts.map (type_name_subst tenvT))
    refine ⟨by simpa using hlen, ?_, ?_⟩
    · exact check_freevars_add 0 tvs' t (h1 tn (tvs', t) hl) dbmax (by omega)
    · simp
      intro x hx
      exact ih x hx ⟨h1, h2 x hx, h3 x hx⟩
/- HOL4:
Theorem tenv_ctor_ok_merge[simp]:
   !tenvC1 tenvC2.
    tenv_ctor_ok tenvC1 ∧ tenv_ctor_ok tenvC2
    ⇒
    tenv_ctor_ok (nsAppend tenvC1 tenvC2)
-/
theorem tenv_ctor_ok_merge :
    ∀ (tenvC1 tenvC2 : tenv_ctor),
      tenv_ctor_ok tenvC1 ∧ tenv_ctor_ok tenvC2 →
      tenv_ctor_ok (nsAppend tenvC1 tenvC2) := by
  intro c1 c2 h
  exact BAux.ns_nsAll_nsAppend _ c1 c2 h
/- HOL4:
Theorem tenv_ctor_ok_lookup:
   !tenvC cn tvs ts tn.
    tenv_ctor_ok tenvC ∧ nsLookup tenvC cn = SOME (tvs,ts,tn)
    ⇒
    EVERY (check_freevars 0 tvs) ts
-/
theorem tenv_ctor_ok_lookup :
    ∀ (tenvC : tenv_ctor) (cn : cml_id modN conN) (tvs : List tvarN) (ts : List sem_t) (tn : type_ident),
      tenv_ctor_ok tenvC ∧ nsLookup tenvC cn = some (tvs, ts, tn) →
      EVERY (check_freevars 0 tvs) ts := by
  rintro tenvC cn tvs ts tn ⟨h1, h2⟩
  exact h1 cn (tvs, ts, tn) h2
/- HOL4:
Theorem bind_tvar_rewrites[simp]:
   (!tvs e1 e2. db_merge (bind_tvar tvs e1) e2 = bind_tvar tvs (db_merge e1 e2)) ∧
   (!tvs e. num_tvs (bind_tvar tvs e) = tvs + num_tvs e) ∧
   (!tvs e. num_tvs (Bind_tvar tvs e) = tvs + num_tvs e) ∧
   (!tvs n t e. num_tvs (Bind_name n tvs t e) = num_tvs e) ∧
   (!tvs e. num_tvs Empty = 0) ∧
   (!n inc tvs e. tveLookup n inc (bind_tvar tvs e) = tveLookup n (inc+tvs) e) ∧
   (!tvs e. tenv_val_exp_ok (bind_tvar tvs e) ⇔ tenv_val_exp_ok e) ∧
   (!targs tvs e.
     deBruijn_subst_tenvE targs (bind_tvar tvs e) =
     bind_tvar tvs (deBruijn_subst_tenvE targs e))
-/
theorem bind_tvar_rewrites :
    (∀ (tvs : Nat) (e1 e2 : tenv_val_exp),
      db_merge (bind_tvar tvs e1) e2 = bind_tvar tvs (db_merge e1 e2)) ∧
    (∀ (tvs : Nat) (e : tenv_val_exp),
      num_tvs (bind_tvar tvs e) = tvs + num_tvs e) ∧
    (∀ (tvs : Nat) (e : tenv_val_exp),
      num_tvs (.Bind_tvar tvs e) = tvs + num_tvs e) ∧
    (∀ (n : mlstring) (tvs : Nat) (t : sem_t) (e : tenv_val_exp),
      num_tvs (.Bind_name n tvs t e) = num_tvs e) ∧
    (num_tvs .Empty = 0) ∧
    (∀ (n : mlstring) (inc tvs : Nat) (e : tenv_val_exp),
      tveLookup n inc (bind_tvar tvs e) = tveLookup n (inc + tvs) e) ∧
    (∀ (tvs : Nat) (e : tenv_val_exp),
      tenv_val_exp_ok (bind_tvar tvs e) ↔ tenv_val_exp_ok e) ∧
    (∀ (targs : List sem_t) (tvs : Nat) (e : tenv_val_exp),
      deBruijn_subst_tenvE targs (bind_tvar tvs e) =
      bind_tvar tvs (deBruijn_subst_tenvE targs e)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro tvs e1 e2
    by_cases h : tvs = 0 <;> simp [bind_tvar, h, db_merge]
  · intro tvs e
    by_cases h : tvs = 0 <;> simp [bind_tvar, h, num_tvs]
  · intro tvs e; simp [num_tvs]
  · intro n tvs t e; simp [num_tvs]
  · simp [num_tvs]
  · intro n inc tvs e
    by_cases h : tvs = 0 <;> simp [bind_tvar, h, tveLookup]
  · intro tvs e
    by_cases h : tvs = 0 <;> simp [bind_tvar, h, tenv_val_exp_ok]
  · intro targs tvs e
    by_cases h : tvs = 0 <;> simp [bind_tvar, h, deBruijn_subst_tenvE]
/- HOL4:
Theorem bind_tvar0[simp]:
 !x. bind_tvar 0 x = x
-/
theorem bind_tvar0 :
    ∀ (x : tenv_val_exp), bind_tvar 0 x = x := by
  intro x; simp [bind_tvar]
/- HOL4:
Theorem tveLookup_subst_none:
 !n inc e.
 tveLookup n inc (deBruijn_subst_tenvE targs e) = NONE ⇔
 tveLookup n inc e = NONE
-/
theorem tveLookup_subst_none :
    ∀ (targs : List sem_t) (n : mlstring) (inc : Nat) (e : tenv_val_exp),
      tveLookup n inc (deBruijn_subst_tenvE targs e) = none ↔
      tveLookup n inc e = none := by
  intro targs n inc e
  induction e generalizing inc with
  | Empty => simp [deBruijn_subst_tenvE, tveLookup]
  | Bind_tvar tvs e ih => simp [deBruijn_subst_tenvE, tveLookup, ih]
  | Bind_name n' tvs t e ih =>
    by_cases h : n' = n <;> simp [deBruijn_subst_tenvE, tveLookup, h, ih]
/- HOL4:
Theorem tveLookup_db_merge_none:
 !n inc e1 e2.
  tveLookup n inc (db_merge e1 e2) = NONE
  ⇔
  tveLookup n inc e1 = NONE ∧ tveLookup n (num_tvs e1 + inc) e2 = NONE
-/
theorem tveLookup_db_merge_none :
    ∀ (n : mlstring) (inc : Nat) (e1 e2 : tenv_val_exp),
      tveLookup n inc (db_merge e1 e2) = none ↔
      tveLookup n inc e1 = none ∧ tveLookup n (num_tvs e1 + inc) e2 = none := by
  intro n inc e1 e2
  induction e1 generalizing inc with
  | Empty => simp [db_merge, tveLookup, num_tvs]
  | Bind_tvar tvs e ih =>
    simp only [db_merge, tveLookup, num_tvs, ih]
    have : tvs + num_tvs e + inc = num_tvs e + (inc + tvs) := by omega
    rw [this]
  | Bind_name n' tvs t e ih =>
    by_cases h : n' = n <;> simp [db_merge, tveLookup, num_tvs, h, ih]
/- HOL4:
Theorem tveLookup_inc_none:
 !n inc e.
  tveLookup n inc e = NONE
  ⇔
  tveLookup n 0 e = NONE
-/
theorem tveLookup_inc_none :
    ∀ (n : mlstring) (inc : Nat) (e : tenv_val_exp),
      tveLookup n inc e = none ↔
      tveLookup n 0 e = none := by
  intro n inc e
  induction e generalizing inc with
  | Empty => simp [tveLookup]
  | Bind_tvar tvs e ih =>
    simp only [tveLookup]
    rw [ih (inc + tvs), ih (0 + tvs)]
  | Bind_name n' tvs t e ih =>
    by_cases h : n' = n
    · simp [tveLookup, h]
    · simp [tveLookup, h]; exact ih inc
/- HOL4:
Theorem tveLookup_freevars:
   !n tvs tenvE tvs' t.
    tenv_val_exp_ok tenvE ∧
    num_tvs tenvE = 0 ∧
    tveLookup n tvs tenvE = SOME (tvs',t)
    ⇒
    check_freevars tvs' [] t
-/
theorem tveLookup_freevars_thm :
    ∀ (n : mlstring) (tvs : Nat) (tenvE : tenv_val_exp) (tvs' : Nat) (t : sem_t),
      tenv_val_exp_ok tenvE ∧
      num_tvs tenvE = 0 ∧
      tveLookup n tvs tenvE = some (tvs', t) →
      check_freevars tvs' [] t := by
  intro n tvs tenvE tvs' t
  induction tenvE generalizing tvs with
  | Empty => simp [tveLookup]
  | Bind_tvar k e ih =>
    rintro ⟨h1, h2, h3⟩
    simp [tenv_val_exp_ok, num_tvs, tveLookup] at h1 h2 h3
    exact ih (tvs + k) ⟨h1, h2.2, h3⟩
  | Bind_name n' k t' e ih =>
    rintro ⟨h1, h2, h3⟩
    simp [tenv_val_exp_ok, num_tvs] at h1 h2
    by_cases h : n' = n
    · simp [tveLookup, h] at h3
      obtain ⟨rfl, rfl⟩ := h3
      rw [h2] at h1
      have := nil_deBruijn_inc k tvs t' (Or.inl h1.1)
      rw [this]; exact h1.1
    · simp [tveLookup, h] at h3
      exact ih tvs ⟨h1.2, h2, h3⟩
/- HOL4: [local]
Theorem tveLookup_freevars:
  !e n inc t tvs.
  tenv_val_exp_ok e ∧
  tveLookup n inc e = SOME (tvs, t)
  ⇒
  check_freevars (tvs+inc+num_tvs e) [] t
-/
theorem tveLookup_freevars_local :
    ∀ (e : tenv_val_exp) (n : mlstring) (inc : Nat) (t : sem_t) (tvs : Nat),
      tenv_val_exp_ok e ∧
      tveLookup n inc e = some (tvs, t) →
      check_freevars (tvs + inc + num_tvs e) [] t := by
  intro e n inc t tvs
  induction e generalizing inc with
  | Empty => simp [tveLookup]
  | Bind_tvar k e ih =>
    rintro ⟨h1, h3⟩
    simp [tenv_val_exp_ok, tveLookup] at h1 h3
    have := ih (inc + k) ⟨h1, h3⟩
    simp only [num_tvs]
    have e : tvs + inc + (k + num_tvs e) = tvs + (inc + k) + num_tvs e := by omega
    rw [e]; exact this
  | Bind_name n' k t' e ih =>
    rintro ⟨h1, h3⟩
    simp [tenv_val_exp_ok] at h1
    by_cases h : n' = n
    · simp [tveLookup, h] at h3
      obtain ⟨rfl, rfl⟩ := h3
      have := check_freevars_deBruijn_inc _ _ _ h1.1 inc k
      simp only [num_tvs]
      have e : k + inc + num_tvs e = inc + (k + num_tvs e) := by omega
      rw [e]; exact this
    · simp [tveLookup, h] at h3
      simp only [num_tvs]
      exact ih inc ⟨h1.2, h3⟩
/- HOL4:
Theorem bind_var_list_append:
 !n te1 te2 te3.
  bind_var_list n (te1++te2) te3 = bind_var_list n te1 (bind_var_list n te2 te3)
-/
theorem bind_var_list_append :
    ∀ (n : Nat) (te1 te2 : List (mlstring × sem_t)) (te3 : tenv_val_exp),
      bind_var_list n (te1 ++ te2) te3 = bind_var_list n te1 (bind_var_list n te2 te3) := by
  intro n te1 te2 te3
  induction te1 with
  | nil => simp [bind_var_list]
  | cons a te1 ih => obtain ⟨x, t⟩ := a; simp [bind_var_list, ih]
/- HOL4:
Theorem num_tvs_bind_var_list[simp]:
 !tvs env tenvE. num_tvs (bind_var_list tvs env tenvE) = num_tvs tenvE
-/
theorem num_tvs_bind_var_list :
    ∀ (tvs : Nat) (env : List (mlstring × sem_t)) (tenvE : tenv_val_exp),
      num_tvs (bind_var_list tvs env tenvE) = num_tvs tenvE := by
  intro tvs env tenvE
  induction env with
  | nil => simp [bind_var_list]
  | cons a env ih => obtain ⟨x, t⟩ := a; simp [bind_var_list, num_tvs, ih]
/- HOL4:
Theorem tenv_val_exp_ok_bvl:
 !tenvE env.
  tenv_val_exp_ok tenvE ∧ EVERY (check_freevars (num_tvs tenvE) []) (MAP SND env)
  ⇒
  tenv_val_exp_ok (bind_var_list 0 env tenvE)
-/
theorem tenv_val_exp_ok_bvl :
    ∀ (tenvE : tenv_val_exp) (env : List (mlstring × sem_t)),
      tenv_val_exp_ok tenvE ∧ EVERY (check_freevars (num_tvs tenvE) []) (env.map Prod.snd) →
      tenv_val_exp_ok (bind_var_list 0 env tenvE) := by
  intro tenvE env
  induction env with
  | nil => rintro ⟨h1, h2⟩; simpa [bind_var_list] using h1
  | cons a env ih =>
    obtain ⟨x, t⟩ := a
    rintro ⟨h1, h2⟩
    simp at h2
    simp [bind_var_list, tenv_val_exp_ok, num_tvs_bind_var_list]
    refine ⟨h2.1, ih ⟨h1, ?_⟩⟩
    simp
    exact h2.2
/- HOL4:
Theorem tveLookup_subst_some:
   ∀n e targs tvs t inc.
    tveLookup n inc e = SOME (tvs,t)
    ⇒
    tveLookup n inc (deBruijn_subst_tenvE targs e) =
      SOME (tvs, deBruijn_subst (tvs+inc+num_tvs e) (MAP (deBruijn_inc 0 (tvs+inc+num_tvs e)) targs) t)
-/
theorem tveLookup_subst_some :
    ∀ (n : mlstring) (e : tenv_val_exp) (targs : List sem_t) (tvs : Nat) (t : sem_t) (inc : Nat),
      tveLookup n inc e = some (tvs, t) →
      tveLookup n inc (deBruijn_subst_tenvE targs e) =
        some (tvs, deBruijn_subst (tvs + inc + num_tvs e)
          (targs.map (deBruijn_inc 0 (tvs + inc + num_tvs e))) t) := by
  intro n e targs tvs t inc
  induction e generalizing inc with
  | Empty => simp [tveLookup]
  | Bind_tvar k e ih =>
    intro h
    simp [tveLookup] at h
    have := ih (inc + k) h
    simp only [deBruijn_subst_tenvE, tveLookup, num_tvs, this]
    have e1 : tvs + inc + (k + num_tvs e) = tvs + (inc + k) + num_tvs e := by omega
    rw [e1]
  | Bind_name n' k t' e ih =>
    intro h
    by_cases hn : n' = n
    · simp [tveLookup, hn] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [deBruijn_subst_tenvE, tveLookup, num_tvs, hn]
      simp
      exact type_e_subst_lem5.1 t' k inc (num_tvs e) targs
    · simp [tveLookup, hn] at h
      simp only [deBruijn_subst_tenvE, tveLookup, num_tvs]
      simp [hn]
      exact ih inc h
/- HOL4:
Theorem num_tvs_db_merge[simp]:
 !e1 e2. num_tvs (db_merge e1 e2) = num_tvs e1 + num_tvs e2
-/
theorem num_tvs_db_merge :
    ∀ (e1 e2 : tenv_val_exp),
      num_tvs (db_merge e1 e2) = num_tvs e1 + num_tvs e2 := by
  intro e1 e2
  induction e1 with
  | Empty => simp [db_merge, num_tvs]
  | Bind_tvar k e ih => simp [db_merge, num_tvs, ih]; omega
  | Bind_name n' k t' e ih => simp [db_merge, num_tvs, ih]
/- HOL4:
Theorem num_tvs_deBruijn_subst_tenvE[simp]:
 !targs tenvE. num_tvs (deBruijn_subst_tenvE targs tenvE) = num_tvs tenvE
-/
theorem num_tvs_deBruijn_subst_tenvE :
    ∀ (targs : List sem_t) (tenvE : tenv_val_exp),
      num_tvs (deBruijn_subst_tenvE targs tenvE) = num_tvs tenvE := by
  intro targs e
  induction e with
  | Empty => simp [deBruijn_subst_tenvE, num_tvs]
  | Bind_tvar k e ih => simp [deBruijn_subst_tenvE, num_tvs, ih]
  | Bind_name n' k t' e ih => simp [deBruijn_subst_tenvE, num_tvs, ih]
/- HOL4:
Theorem tveLookup_inc_some:
 !n inc e tvs t inc2.
   tveLookup n inc e = SOME (tvs, t)
   ⇒
   ?t'. (t = deBruijn_inc tvs inc t') ∧
        (tveLookup n inc2 e = SOME (tvs, deBruijn_inc tvs inc2 t'))
-/
theorem tveLookup_inc_some :
    ∀ (n : mlstring) (inc : Nat) (e : tenv_val_exp) (tvs : Nat) (t : sem_t) (inc2 : Nat),
      tveLookup n inc e = some (tvs, t) →
      ∃ (t' : sem_t),
        t = deBruijn_inc tvs inc t' ∧
        tveLookup n inc2 e = some (tvs, deBruijn_inc tvs inc2 t') := by
  intro n inc e tvs t inc2
  induction e generalizing inc inc2 with
  | Empty => simp [tveLookup]
  | Bind_tvar k e ih =>
    intro h
    simp [tveLookup] at h
    obtain ⟨t'', rfl, h2⟩ := ih (inc + k) (inc2 + k) h
    refine ⟨deBruijn_inc tvs k t'', ?_, ?_⟩
    · rw [deBruijn_inc_deBruijn_inc]
    · simp only [tveLookup, h2]
      rw [deBruijn_inc_deBruijn_inc]
  | Bind_name n' k t' e ih =>
    intro h
    by_cases hn : n' = n
    · simp [tveLookup, hn] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨t', rfl, by simp [tveLookup, hn]⟩
    · simp [tveLookup, hn] at h
      obtain ⟨t'', rfl, h2⟩ := ih inc inc2 h
      exact ⟨t'', rfl, by simp [tveLookup, hn, h2]⟩
/- HOL4:
Theorem tveLookup_freevars_subst:
   !tenvE targs n t inc.
    EVERY (check_freevars (inc + num_tvs tenvE) []) targs ∧
    tveLookup n inc tenvE = SOME (LENGTH targs,t) ∧
    tenv_val_exp_ok tenvE
    ⇒
    check_freevars (inc + num_tvs tenvE) [] (deBruijn_subst 0 targs t)
-/
theorem tveLookup_freevars_subst :
    ∀ (tenvE : tenv_val_exp) (targs : List sem_t) (n : mlstring) (t : sem_t) (inc : Nat),
      EVERY (check_freevars (inc + num_tvs tenvE) []) targs ∧
      tveLookup n inc tenvE = some (targs.length, t) ∧
      tenv_val_exp_ok tenvE →
      check_freevars (inc + num_tvs tenvE) [] (deBruijn_subst 0 targs t) := by
  rintro tenvE targs n t inc ⟨h1, h2, h3⟩
  have h4 := tveLookup_freevars_local tenvE n inc t targs.length ⟨h3, h2⟩
  have := check_freevars_subst _ [] t h4 (inc + num_tvs tenvE) targs 0
    ⟨by omega, by simpa using h1⟩
  simpa using this
/- HOL4:
Theorem tenv_val_exp_ok_db_merge:
 !e1 e2. tenv_val_exp_ok (db_merge e1 e2) ⇒ tenv_val_exp_ok e2
-/
theorem tenv_val_exp_ok_db_merge :
    ∀ (e1 e2 : tenv_val_exp),
      tenv_val_exp_ok (db_merge e1 e2) → tenv_val_exp_ok e2 := by
  intro e1 e2
  induction e1 with
  | Empty => simp [db_merge]
  | Bind_tvar k e ih => simpa [db_merge, tenv_val_exp_ok] using ih
  | Bind_name n' k t' e ih =>
    intro h
    simp [db_merge, tenv_val_exp_ok] at h
    exact ih h.2
/- HOL4:
Theorem tveLookup_no_tvs:
 !tvs l tenv n t.
  tenv_val_exp_ok tenv ∧
  num_tvs tenv = 0
  ⇒
  (tveLookup n tvs tenv = SOME (l,t)
   ⇔
   tveLookup n 0 tenv = SOME (l,t))
-/
theorem B_tveLookup_no_tvs_aux (n : mlstring) (tenv : tenv_val_exp) :
    tenv_val_exp_ok tenv → num_tvs tenv = 0 → ∀ inc, tveLookup n inc tenv = tveLookup n 0 tenv := by
  induction tenv with
  | Empty => simp [tveLookup]
  | Bind_tvar k e ih =>
    intro h1 h2 inc
    simp [tenv_val_exp_ok, num_tvs] at h1 h2
    simp only [tveLookup]
    rw [ih h1 h2.2 (inc + k), ih h1 h2.2 (0 + k)]
  | Bind_name n' k t' e ih =>
    intro h1 h2 inc
    simp [tenv_val_exp_ok, num_tvs] at h1 h2
    rw [h2] at h1
    by_cases hn : n' = n
    · simp [tveLookup, hn]
      rw [nil_deBruijn_inc k inc t' (Or.inl h1.1), nil_deBruijn_inc k 0 t' (Or.inl h1.1)]
    · simp [tveLookup, hn]
      exact ih h1.2 h2 inc
theorem tveLookup_no_tvs :
    ∀ (tvs : Nat) (l : Nat) (tenv : tenv_val_exp) (n : mlstring) (t : sem_t),
      tenv_val_exp_ok tenv ∧
      num_tvs tenv = 0 →
      (tveLookup n tvs tenv = some (l, t) ↔
       tveLookup n 0 tenv = some (l, t)) := by
  rintro tvs l tenv n t ⟨h1, h2⟩
  rw [B_tveLookup_no_tvs_aux n tenv h1 h2 tvs]
/- HOL4:
Theorem deBruijn_subst_E_bvl:
 !tenv1 tenv2 tvs.
  deBruijn_subst_tenvE targs (bind_var_list tvs tenv1 tenv2)
  =
  bind_var_list tvs
          (MAP (\(x,t). (x, deBruijn_subst (tvs + num_tvs tenv2) (MAP (deBruijn_inc 0 (tvs + num_tvs tenv2)) targs) t)) tenv1)
          (deBruijn_subst_tenvE targs tenv2)
-/
theorem deBruijn_subst_E_bvl :
    ∀ (targs : List sem_t) (tenv1 : List (mlstring × sem_t)) (tenv2 : tenv_val_exp) (tvs : Nat),
      deBruijn_subst_tenvE targs (bind_var_list tvs tenv1 tenv2) =
      bind_var_list tvs
        (tenv1.map (fun (x, t) => (x, deBruijn_subst (tvs + num_tvs tenv2)
          (targs.map (deBruijn_inc 0 (tvs + num_tvs tenv2))) t)))
        (deBruijn_subst_tenvE targs tenv2) := by
  intro targs tenv1 tenv2 tvs
  induction tenv1 with
  | nil => simp [bind_var_list]
  | cons a tenv1 ih =>
    obtain ⟨x, t⟩ := a
    simp [bind_var_list, deBruijn_subst_tenvE, num_tvs_bind_var_list, ih]
/- HOL4:
Theorem db_merge_bvl:
 !tenv1 tenv2 tenv3 tvs.
  db_merge (bind_var_list tvs tenv1 tenv2) tenv3
  =
  bind_var_list tvs tenv1 (db_merge tenv2 tenv3)
-/
theorem db_merge_bvl :
    ∀ (tenv1 : List (mlstring × sem_t)) (tenv2 tenv3 : tenv_val_exp) (tvs : Nat),
      db_merge (bind_var_list tvs tenv1 tenv2) tenv3 =
      bind_var_list tvs tenv1 (db_merge tenv2 tenv3) := by
  intro tenv1 tenv2 tenv3 tvs
  induction tenv1 with
  | nil => simp [bind_var_list]
  | cons a tenv1 ih =>
    obtain ⟨x, t⟩ := a
    simp [bind_var_list, db_merge, ih]
/- HOL4:
Theorem tveLookup_db_merge_some:
   !n inc tenvE1 tenvE2 tvs t.
    tveLookup n inc (db_merge tenvE1 tenvE2) = SOME (tvs,t)
    ⇔
    tveLookup n inc tenvE1 = SOME (tvs,t) ∨
    (tveLookup n inc tenvE1 = NONE ∧
     tveLookup n (num_tvs tenvE1 + inc) tenvE2 = SOME (tvs, t))
-/
theorem tveLookup_db_merge_some :
    ∀ (n : mlstring) (inc : Nat) (tenvE1 tenvE2 : tenv_val_exp) (tvs : Nat) (t : sem_t),
      tveLookup n inc (db_merge tenvE1 tenvE2) = some (tvs, t) ↔
      tveLookup n inc tenvE1 = some (tvs, t) ∨
      (tveLookup n inc tenvE1 = none ∧
       tveLookup n (num_tvs tenvE1 + inc) tenvE2 = some (tvs, t)) := by
  intro n inc e1 e2 tvs t
  induction e1 generalizing inc with
  | Empty => simp [db_merge, tveLookup, num_tvs]
  | Bind_tvar k e ih =>
    simp only [db_merge, tveLookup, num_tvs, ih]
    have : k + num_tvs e + inc = num_tvs e + (inc + k) := by omega
    rw [this]
  | Bind_name n' k t' e ih =>
    by_cases h : n' = n <;> simp [db_merge, tveLookup, num_tvs, h, ih]
/- HOL4: Theorem type_op_cases:
   Computed by HOL4 from type_op_def (SIMP_CONV with type_op_def, the case_eq
   theorems, DNF_ss, and PULL_EXISTS). Written here as that case expansion. -/
theorem type_op_cases_thm :
    ∀ (op_ : op) (ts : List sem_t) (t3 : sem_t),
      type_op op_ ts t3 ↔
        (∃ u1 u2, op_ = .Opapp ∧ ts = [u1, u2] ∧ u1 = Tfn u2 t3) ∨
        (∃ sh n u1, op_ = .Shift .W8 sh n ∧ ts = [u1] ∧ u1 = Tword8 ∧ t3 = Tword8) ∨
        (∃ sh n u1, op_ = .Shift .W64 sh n ∧ ts = [u1] ∧ u1 = Tword64 ∧ t3 = Tword64) ∨
        (∃ u1 u2, op_ = .Equality ∧ ts = [u1, u2] ∧ u1 = u2 ∧ t3 = Tbool) ∨
        (∃ a ty, op_ = .Arith a ty ∧ (∀ arg, arg ∈ ts → arg = t_of ty) ∧ t3 = t_of ty ∧
          supported_arith a ty = some ts.length) ∨
        (∃ ty1 ty2 u1, op_ = .FromTo ty1 ty2 ∧ ts = [u1] ∧ u1 = t_of ty1 ∧ t3 = t_of ty2 ∧
          supported_conversion ty1 ty2 = true) ∨
        (∃ tst ty u1 u2, op_ = .Test tst ty ∧ ts = [u1, u2] ∧ u1 = u2 ∧ t3 = Tbool ∧
          u1 = t_of ty ∧ supported_test tst ty = true) ∨
        (∃ u1 u2, op_ = .Opassign ∧ ts = [u1, u2] ∧ u1 = Tref u2 ∧ t3 = Ttup []) ∨
        (∃ u1, op_ = .Opref ∧ ts = [u1] ∧ t3 = Tref u1) ∨
        (∃ u1, op_ = .Opderef ∧ ts = [u1] ∧ u1 = Tref t3) ∨
        (∃ u1 u2, op_ = .Aw8alloc ∧ ts = [u1, u2] ∧ u1 = Tint ∧ u2 = Tword8 ∧ t3 = Tword8array) ∨
        (∃ u1 u2, op_ = .Aw8sub ∧ ts = [u1, u2] ∧ u1 = Tword8array ∧ u2 = Tint ∧ t3 = Tword8) ∨
        (∃ u1, op_ = .Aw8length ∧ ts = [u1] ∧ u1 = Tword8array ∧ t3 = Tint) ∨
        (∃ u1 u2 u3, op_ = .Aw8update ∧ ts = [u1, u2, u3] ∧ u1 = Tword8array ∧ u2 = Tint ∧
          u3 = Tword8 ∧ t3 = Ttup []) ∨
        (∃ u1 u2 u3, op_ = .CopyStrStr ∧ ts = [u1, u2, u3] ∧ u1 = Tstring ∧ u2 = Tint ∧
          u3 = Tint ∧ t3 = Tstring) ∨
        (∃ u1 u2 u3 u4 u5, op_ = .CopyStrAw8 ∧ ts = [u1, u2, u3, u4, u5] ∧ u1 = Tstring ∧
          u2 = Tint ∧ u3 = Tint ∧ u4 = Tword8array ∧ u5 = Tint ∧ t3 = Ttup []) ∨
        (∃ u1 u2 u3, op_ = .CopyAw8Str ∧ ts = [u1, u2, u3] ∧ u1 = Tword8array ∧ u2 = Tint ∧
          u3 = Tint ∧ t3 = Tstring) ∨
        (∃ u1 u2 u3 u4 u5, op_ = .CopyAw8Aw8 ∧ ts = [u1, u2, u3, u4, u5] ∧ u1 = Tword8array ∧
          u2 = Tint ∧ u3 = Tint ∧ u4 = Tword8array ∧ u5 = Tint ∧ t3 = Ttup []) ∨
        (∃ u1, op_ = .Implode ∧ ts = [u1] ∧ u1 = Tlist Tchar ∧ t3 = Tstring) ∨
        (∃ u1, op_ = .Explode ∧ ts = [u1] ∧ u1 = Tstring ∧ t3 = Tlist Tchar) ∨
        (∃ u1 u2, op_ = .Strsub ∧ ts = [u1, u2] ∧ u1 = Tstring ∧ u2 = Tint ∧ t3 = Tchar) ∨
        (∃ u1, op_ = .Strlen ∧ ts = [u1] ∧ u1 = Tstring ∧ t3 = Tint) ∨
        (∃ u1, op_ = .Strcat ∧ ts = [u1] ∧ u1 = Tlist Tstring ∧ t3 = Tstring) ∨
        (∃ u1 ctor, op_ = .VfromList ∧ ts = [.Tapp [u1] ctor] ∧ ctor = Tlist_num ∧
          t3 = Tvector u1) ∨
        (∃ u1 u2, op_ = .Vsub ∧ ts = [u1, u2] ∧ u2 = Tint ∧ Tvector t3 = u1) ∨
        (∃ u1 ctor, op_ = .Vlength ∧ ts = [.Tapp [u1] ctor] ∧ ctor = Tvector_num ∧ t3 = Tint) ∨
        (∃ u1 u2, op_ = .Aalloc ∧ ts = [u1, u2] ∧ u1 = Tint ∧ t3 = Tarray u2) ∨
        (∃ u1, op_ = .AallocEmpty ∧ ts = [u1] ∧ u1 = Ttup [] ∧ ∃ u2, t3 = Tarray u2) ∨
        (∃ u1 u2, op_ = .Asub ∧ ts = [u1, u2] ∧ u2 = Tint ∧ Tarray t3 = u1) ∨
        (∃ u1 ctor, op_ = .Alength ∧ ts = [.Tapp [u1] ctor] ∧ ctor = Tarray_num ∧ t3 = Tint) ∨
        (∃ u1 u2 u3, op_ = .Aupdate ∧ ts = [u1, u2, u3] ∧ u1 = Tarray u3 ∧ u2 = Tint ∧
          t3 = Ttup []) ∨
        (∃ u1 u2, op_ = .ConfigGC ∧ ts = [u1, u2] ∧ u1 = Tint ∧ u2 = Tint ∧ t3 = Ttup []) ∨
        (∃ nm u1 u2, op_ = .FFI nm ∧ ts = [u1, u2] ∧ u1 = Tstring ∧ u2 = Tword8array ∧
          t3 = Ttup []) ∨
        (∃ u1 ctor u2, op_ = .ListAppend ∧ ts = [.Tapp [u1] ctor, u2] ∧ ctor = Tlist_num ∧
          u2 = sem_t.Tapp [u1] ctor ∧ t3 = u2) := by
  intro op_ ts t3
  unfold type_op
  split <;> simp_all [and_assoc]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (intros; subst_vars; simp_all)
  rename_i h
  exact absurd rfl (h _ _ _ _ rfl rfl rfl)
/- HOL4:
Theorem type_ps_length:
 ∀tvs tenvC ps ts tenv.
  type_ps tvs tenvC ps ts tenv ⇒ (LENGTH ps = LENGTH ts)
-/
theorem type_ps_length :
    ∀ (tvs : Nat) (tenvC : type_env) (ps : List pat) (ts : List sem_t) (tenv : List (varN × sem_t)),
      type_ps tvs tenvC ps ts tenv → ps.length = ts.length := by
  intro tvs tenvC ps
  induction ps with
  | nil => intro ts tenv h; cases h; rfl
  | cons p ps ih =>
    intro ts tenv h
    cases h
    rename_i h1 h2
    simp
    exact ih _ _ h2
/- HOL4:
Theorem type_p_freevars:
 (!tvs tenvC p t env'.
   type_p tvs tenvC p t env' ⇒
   check_freevars tvs [] t ∧
   EVERY (check_freevars tvs []) (MAP SND env')) ∧
 (!tvs tenvC ps ts env'.
   type_ps tvs tenvC ps ts env' ⇒
   EVERY (check_freevars tvs []) ts ∧
   EVERY (check_freevars tvs []) (MAP SND env'))
-/
theorem type_p_freevars :
    (∀ (tvs : Nat) (tenvC : type_env) (p : pat) (t : sem_t) (env' : List (varN × sem_t)),
      type_p tvs tenvC p t env' →
      check_freevars tvs [] t ∧
      EVERY (check_freevars tvs []) (env'.map Prod.snd)) ∧
    (∀ (tvs : Nat) (tenvC : type_env) (ps : List pat) (ts : List sem_t) (env' : List (varN × sem_t)),
      type_ps tvs tenvC ps ts env' →
      EVERY (check_freevars tvs []) ts ∧
      EVERY (check_freevars tvs []) (env'.map Prod.snd)) := by
  have H : ∀ (tvs : Nat) (tenvC : type_env),
      (∀ p t env', type_p tvs tenvC p t env' →
        check_freevars tvs [] t ∧ EVERY (check_freevars tvs []) (env'.map Prod.snd)) ∧
      (∀ ps ts env', type_ps tvs tenvC ps ts env' →
        EVERY (check_freevars tvs []) ts ∧ EVERY (check_freevars tvs []) (env'.map Prod.snd)) := by
    intro tvs tenvC
    apply BAux.type_p_ind
    case pany => intro t h; simp [h]
    case pvar => intro n t h; simp [h]
    case plit_int => intro n; simp [Tint]
    case plit_char => intro n; simp [Tchar]
    case plit_str => intro n; simp [Tstring]
    case plit_word8 => intro n; simp [Tword8]
    case plit_word64 => intro n; simp [Tword64]
    case pcon_some =>
      intro cn ps ts' tvs' ts tn bindings h1 h2 h3 h4 ih
      simp at ih ⊢
      exact ⟨h1, ih.2⟩
    case pcon_none =>
      intro ps ts bindings h ih
      simp [Ttup] at ih ⊢
      exact ih
    case pref =>
      intro p t bindings h ih
      simp [Tref] at ih ⊢
      exact ih
    case pas =>
      intro p t bindings v_ h ih
      simp at ih ⊢
      exact ⟨ih.1, ih.2, ih.1⟩
    case ptannot =>
      intro p t bindings h1 h2 h3 ih
      exact ih
    case nil => simp
    case cons =>
      intro p t bindings ps ts bindings' h1 h2 ih1 ih2
      simp at ih1 ih2 ⊢
      exact ⟨⟨ih1.1, ih2.1⟩, ih2.2, ih1.2⟩
  exact ⟨fun tvs tenvC p t env' h => (H tvs tenvC).1 p t env' h,
    fun tvs tenvC ps ts env' h => (H tvs tenvC).2 ps ts env' h⟩
/- HOL4:
Theorem type_p_subst:
 (!n tenv p t new_bindings. type_p n tenv p t new_bindings ⇒
    !targs' inc tvs targs.
    tenv_abbrev_ok tenv.t ∧
    tenv_ctor_ok tenv.c ∧
    (n = inc + LENGTH targs) ∧
    EVERY (check_freevars tvs []) targs ∧
    (targs' = MAP (deBruijn_inc 0 inc) targs)
    ⇒
    type_p (inc + tvs) tenv
           p
           (deBruijn_subst inc targs' t)
           (MAP (\(x,t). (x, deBruijn_subst inc targs' t)) new_bindings)) ∧
 (!n tenv ps ts new_bindings. type_ps n tenv ps ts new_bindings ⇒
    !targs' inc targs tvs.
    tenv_abbrev_ok tenv.t ∧
    tenv_ctor_ok tenv.c ∧
    (n = inc + LENGTH targs) ∧
    EVERY (check_freevars tvs []) targs ∧
    (targs' = MAP (deBruijn_inc 0 inc) targs)
    ⇒
    type_ps (inc +  tvs) tenv
           ps
           (MAP (deBruijn_subst inc targs') ts)
           (MAP (\(x,t). (x, deBruijn_subst inc targs' t)) new_bindings))
-/
theorem type_p_subst :
    (∀ (n : Nat) (tenv : type_env) (p : pat) (t : sem_t) (new_bindings : List (varN × sem_t)),
      type_p n tenv p t new_bindings →
      ∀ (targs' : List sem_t) (inc : Nat) (tvs : Nat) (targs : List sem_t),
        tenv_abbrev_ok tenv.t ∧
        tenv_ctor_ok tenv.c ∧
        n = inc + targs.length ∧
        EVERY (check_freevars tvs []) targs ∧
        targs' = targs.map (deBruijn_inc 0 inc) →
        type_p (inc + tvs) tenv p
          (deBruijn_subst inc targs' t)
          (new_bindings.map (fun (x, t) => (x, deBruijn_subst inc targs' t)))) ∧
    (∀ (n : Nat) (tenv : type_env) (ps : List pat) (ts : List sem_t) (new_bindings : List (varN × sem_t)),
      type_ps n tenv ps ts new_bindings →
      ∀ (targs' : List sem_t) (inc : Nat) (targs : List sem_t) (tvs : Nat),
        tenv_abbrev_ok tenv.t ∧
        tenv_ctor_ok tenv.c ∧
        n = inc + targs.length ∧
        EVERY (check_freevars tvs []) targs ∧
        targs' = targs.map (deBruijn_inc 0 inc) →
        type_ps (inc + tvs) tenv ps
          (ts.map (deBruijn_subst inc targs'))
          (new_bindings.map (fun (x, t) => (x, deBruijn_subst inc targs' t)))) := by
  have H : ∀ (n : Nat) (tenv : type_env),
      (∀ p t nb, type_p n tenv p t nb →
        ∀ (targs' : List sem_t) (inc tvs : Nat) (targs : List sem_t),
          tenv_abbrev_ok tenv.t ∧ tenv_ctor_ok tenv.c ∧ n = inc + targs.length ∧
          EVERY (check_freevars tvs []) targs ∧ targs' = targs.map (deBruijn_inc 0 inc) →
          type_p (inc + tvs) tenv p (deBruijn_subst inc targs' t)
            (nb.map (fun (x, t) => (x, deBruijn_subst inc targs' t)))) ∧
      (∀ ps ts nb, type_ps n tenv ps ts nb →
        ∀ (targs' : List sem_t) (inc tvs : Nat) (targs : List sem_t),
          tenv_abbrev_ok tenv.t ∧ tenv_ctor_ok tenv.c ∧ n = inc + targs.length ∧
          EVERY (check_freevars tvs []) targs ∧ targs' = targs.map (deBruijn_inc 0 inc) →
          type_ps (inc + tvs) tenv ps (ts.map (deBruijn_subst inc targs'))
            (nb.map (fun (x, t) => (x, deBruijn_subst inc targs' t)))) := by
    intro n tenv
    apply BAux.type_p_ind
    case pany =>
      rintro t h targs' inc tvs targs ⟨h1, h2, rfl, h4, rfl⟩
      exact type_p.pany _ _ _ (check_freevars_lem _ _ _ h targs inc tvs ⟨rfl, h4⟩)
    case pvar =>
      rintro x t h targs' inc tvs targs ⟨h1, h2, rfl, h4, rfl⟩
      exact type_p.pvar _ _ _ _ (check_freevars_lem _ _ _ h targs inc tvs ⟨rfl, h4⟩)
    case plit_int =>
      rintro k targs' inc tvs targs _
      simpa [Tint, deBruijn_subst] using type_p.plit_int (inc + tvs) tenv k
    case plit_char =>
      rintro k targs' inc tvs targs _
      simpa [Tchar, deBruijn_subst] using type_p.plit_char (inc + tvs) tenv k
    case plit_str =>
      rintro k targs' inc tvs targs _
      simpa [Tstring, deBruijn_subst] using type_p.plit_str (inc + tvs) tenv k
    case plit_word8 =>
      rintro k targs' inc tvs targs _
      simpa [Tword8, deBruijn_subst] using type_p.plit_word8 (inc + tvs) tenv k
    case plit_word64 =>
      rintro k targs' inc tvs targs _
      simpa [Tword64, deBruijn_subst] using type_p.plit_word64 (inc + tvs) tenv k
    case pcon_some =>
      rintro cn ps ts' tvs' ts tn bindings hfv hlen hps hlook ih targs' inc tvs targs ⟨h1, h2, rfl, h4, rfl⟩
      simp only [deBruijn_subst]
      have ih' := ih _ inc tvs targs ⟨h1, h2, rfl, h4, rfl⟩
      have hts : EVERY (check_freevars 0 tvs') ts := tenv_ctor_ok_lookup _ _ _ _ _ ⟨h2, hlook⟩
      have e := type_subst_deBruijn_subst_list default tvs' [] ts'
        (targs.map (deBruijn_inc 0 inc)) ts inc ⟨hlen.symm, hts⟩
      simp only [ZIP] at e
      rw [e] at ih'
      refine type_p.pcon_some _ _ cn ps (ts'.map (deBruijn_subst inc _)) tvs' ts tn _ ?_
        (by simpa using hlen) ih' hlook
      intro t' ht'
      simp at ht'
      obtain ⟨a, ha, rfl⟩ := ht'
      exact check_freevars_lem _ _ _ (hfv a ha) targs inc tvs ⟨rfl, h4⟩
    case pcon_none =>
      rintro ps ts bindings h ih targs' inc tvs targs hh
      have := ih targs' inc tvs targs hh
      simp only [Ttup, deBruijn_subst]
      exact type_p.pcon_none _ _ _ _ _ this
    case pref =>
      rintro p t bindings h ih targs' inc tvs targs hh
      have := ih targs' inc tvs targs hh
      simp only [Tref, deBruijn_subst, List.map]
      exact type_p.pref _ _ _ _ _ this
    case pas =>
      rintro p t bindings v_ h ih targs' inc tvs targs hh
      have := ih targs' inc tvs targs hh
      simp only [List.map_append, List.map]
      exact type_p.pas _ _ _ _ _ _ this
    case ptannot =>
      rintro p t bindings h1 h2 h3 ih targs' inc tvs targs ⟨g1, g2, rfl, g4, rfl⟩
      have ih' := ih _ inc tvs targs ⟨g1, g2, rfl, g4, rfl⟩
      have hfv := check_freevars_type_name_subst [] t inc tenv.t ⟨g1, h2, h1⟩
      rw [nil_deBruijn_subst inc _ _ hfv] at ih' ⊢
      exact type_p.ptannot _ _ _ _ _ h1 h2 ih'
    case nil => intro targs' inc tvs targs _; exact type_ps.nil _ _
    case cons =>
      rintro p t bindings ps ts bindings' h1 h2 ih1 ih2 targs' inc tvs targs hh
      have a := ih1 targs' inc tvs targs hh
      have b := ih2 targs' inc tvs targs hh
      simp only [List.map_append, List.map]
      exact type_ps.cons _ _ _ _ _ _ _ _ a b
  exact ⟨fun n tenv p t nb h => (H n tenv).1 p t nb h,
    fun n tenv ps ts nb h targs' inc targs tvs hh => (H n tenv).2 ps ts nb h targs' inc tvs targs hh⟩
/- HOL4:
Theorem type_p_bvl:
   (!tvs tenvC p t bindings. type_p tvs tenvC p t bindings ⇒
    !tenv'. tenv_val_exp_ok tenv' ⇒ tenv_val_exp_ok (bind_var_list tvs bindings tenv')) ∧
   (!tvs tenvC ps ts bindings. type_ps tvs tenvC ps ts bindings ⇒
    !tenv'. tenv_val_exp_ok tenv' ⇒ tenv_val_exp_ok (bind_var_list tvs bindings tenv'))
-/
theorem type_p_bvl :
    (∀ (tvs : Nat) (tenvC : type_env) (p : pat) (t : sem_t) (bindings : List (varN × sem_t)),
      type_p tvs tenvC p t bindings →
      ∀ (tenv' : tenv_val_exp), tenv_val_exp_ok tenv' → tenv_val_exp_ok (bind_var_list tvs bindings tenv')) ∧
    (∀ (tvs : Nat) (tenvC : type_env) (ps : List pat) (ts : List sem_t) (bindings : List (varN × sem_t)),
      type_ps tvs tenvC ps ts bindings →
      ∀ (tenv' : tenv_val_exp), tenv_val_exp_ok tenv' → tenv_val_exp_ok (bind_var_list tvs bindings tenv')) := by
  have key : ∀ (tvs : Nat) (bindings : List (varN × sem_t)),
      EVERY (check_freevars tvs []) (bindings.map Prod.snd) →
      ∀ tenv', tenv_val_exp_ok tenv' → tenv_val_exp_ok (bind_var_list tvs bindings tenv') := by
    intro tvs bindings
    induction bindings with
    | nil => intro _ tenv' h; simpa [bind_var_list] using h
    | cons a bs ih =>
      obtain ⟨x, t⟩ := a
      intro h tenv' h'
      simp at h
      simp only [bind_var_list, tenv_val_exp_ok]
      exact ⟨check_freevars_add _ _ _ h.1 _ (by omega), ih (by simpa using h.2) tenv' h'⟩
  exact ⟨fun tvs tenvC p t b h => key tvs b (type_p_freevars.1 tvs tenvC p t b h).2,
    fun tvs tenvC ps ts b h => key tvs b (type_p_freevars.2 tvs tenvC ps ts b h).2⟩
/- HOL4:
Theorem type_p_tenvV_indep:
 (!p tvs tenv t bindings tenvV.
  type_p tvs tenv p t bindings = type_p tvs (tenv with v := tenvV) p t bindings) ∧
 (!ps tvs tenv t bindings tenvV.
  type_ps tvs tenv ps t bindings = type_ps tvs (tenv with v := tenvV) ps t bindings)
-/
theorem type_p_tenvV_indep :
    (∀ (p : pat) (tvs : Nat) (tenv : type_env) (t : sem_t) (bindings : List (varN × sem_t)) (tenvV : tenv_val),
      type_p tvs tenv p t bindings = type_p tvs { tenv with v := tenvV } p t bindings) ∧
    (∀ (ps : List pat) (tvs : Nat) (tenv : type_env) (t : List sem_t) (bindings : List (varN × sem_t)) (tenvV : tenv_val),
      type_ps tvs tenv ps t bindings = type_ps tvs { tenv with v := tenvV } ps t bindings) := by
  have H : ∀ (tvs : Nat) (tenv tenv' : type_env), tenv'.c = tenv.c → tenv'.t = tenv.t →
      (∀ p t b, type_p tvs tenv p t b → type_p tvs tenv' p t b) ∧
      (∀ ps ts b, type_ps tvs tenv ps ts b → type_ps tvs tenv' ps ts b) := by
    intro tvs tenv tenv' hc ht
    apply BAux.type_p_ind
    case pany => intro t h; exact type_p.pany _ _ _ h
    case pvar => intro n t h; exact type_p.pvar _ _ _ _ h
    case plit_int => intro n; exact type_p.plit_int _ _ _
    case plit_char => intro n; exact type_p.plit_char _ _ _
    case plit_str => intro n; exact type_p.plit_str _ _ _
    case plit_word8 => intro n; exact type_p.plit_word8 _ _ _
    case plit_word64 => intro n; exact type_p.plit_word64 _ _ _
    case pcon_some =>
      intro cn ps ts' tvs' ts tn bindings h1 h2 h3 h4 ih
      exact type_p.pcon_some _ _ _ _ _ _ _ _ _ h1 h2 ih (by rw [hc]; exact h4)
    case pcon_none => intro ps ts bindings h ih; exact type_p.pcon_none _ _ _ _ _ ih
    case pref => intro p t bindings h ih; exact type_p.pref _ _ _ _ _ ih
    case pas => intro p t bindings v_ h ih; exact type_p.pas _ _ _ _ _ _ ih
    case ptannot =>
      intro p t bindings h1 h2 h3 ih
      rw [← ht] at h2 ih ⊢
      exact type_p.ptannot _ _ _ _ _ h1 h2 ih
    case nil => exact type_ps.nil _ _
    case cons =>
      intro p t bindings ps ts bindings' h1 h2 ih1 ih2
      exact type_ps.cons _ _ _ _ _ _ _ _ ih1 ih2
  exact ⟨fun p tvs tenv t b tenvV => propext
      ⟨(H tvs tenv { tenv with v := tenvV } rfl rfl).1 p t b,
       (H tvs { tenv with v := tenvV } tenv rfl rfl).1 p t b⟩,
    fun ps tvs tenv t b tenvV => propext
      ⟨(H tvs tenv { tenv with v := tenvV } rfl rfl).2 ps t b,
       (H tvs { tenv with v := tenvV } tenv rfl rfl).2 ps t b⟩⟩
/- HOL4:
Theorem type_es_list_rel:
 !es ts tenv tenvE. type_es tenv tenvE es ts = LIST_REL (type_e tenv tenvE) es ts
-/
theorem type_es_list_rel :
    ∀ (es : List exp) (ts : List sem_t) (tenv : type_env) (tenvE : tenv_val_exp),
      type_es tenv tenvE es ts = LIST_REL (type_e tenv tenvE) es ts := by
  intro es ts tenv tenvE
  apply propext
  constructor
  · intro h
    induction es generalizing ts with
    | nil => cases h; exact LIST_REL.nil
    | cons e es ih =>
      cases h
      rename_i h1 h2
      exact LIST_REL.cons _ _ _ _ h1 (ih _ h2)
  · intro h
    induction h with
    | nil => exact type_es.nil _ _
    | cons x y xs ys h1 h2 ih => exact type_es.cons _ _ _ _ _ _ h1 ih
/- HOL4:
Theorem type_es_length:
 ∀tenv tenvE es ts.
  type_es tenv tenvE es ts ⇒ (LENGTH es = LENGTH ts)
-/
theorem type_es_length :
    ∀ (tenv : type_env) (tenvE : tenv_val_exp) (es : List exp) (ts : List sem_t),
      type_es tenv tenvE es ts → es.length = ts.length := by
  intro tenv tenvE es
  induction es with
  | nil => intro ts h; cases h; rfl
  | cons e es ih =>
    intro ts h
    cases h
    rename_i h1 h2
    simp
    exact ih _ h2
/- HOL4:
Theorem tenv_val_exp_ok_bvl_funs:
   !funs env tenv bindings tenv_val tenvE.
    type_funs tenv (bind_var_list 0 bindings tenvE) funs env ∧
    tenv_val_exp_ok tenvE
    ⇒
    tenv_val_exp_ok (bind_var_list 0 env tenvE)
-/
theorem B_type_funs_freevars_aux (tenv : type_env) (E : tenv_val_exp) :
    ∀ (funs : List (varN × varN × exp)) (env : List (varN × sem_t)),
      type_funs tenv E funs env →
      EVERY (check_freevars (num_tvs E) []) (env.map Prod.snd) := by
  intro funs
  induction funs with
  | nil => intro env h; cases h; simp
  | cons f funs ih =>
    intro env h
    cases h
    rename_i ha hc he hf
    have := ih _ hf
    simp at this hc ⊢
    exact ⟨hc, this⟩
theorem tenv_val_exp_ok_bvl_funs :
    ∀ (funs : List (varN × varN × exp)) (env : List (varN × sem_t))
      (tenv : type_env) (bindings : List (varN × sem_t))
      (tenv_val_ : tenv_val) (tenvE : tenv_val_exp),
      type_funs tenv (bind_var_list 0 bindings tenvE) funs env ∧
      tenv_val_exp_ok tenvE →
      tenv_val_exp_ok (bind_var_list 0 env tenvE) := by
  rintro funs env tenv bindings _ tenvE ⟨h1, h2⟩
  have := B_type_funs_freevars_aux _ _ _ _ h1
  rw [num_tvs_bind_var_list] at this
  exact tenv_val_exp_ok_bvl tenvE env ⟨h2, this⟩
/- HOL4:
Theorem type_e_freevars:
 (!tenv tenvE e t.
   type_e tenv tenvE e t ⇒
   tenv_val_exp_ok tenvE ∧ tenv_val_ok tenv.v ⇒
   check_freevars (num_tvs tenvE) [] t) ∧
 (!tenv tenvE es ts.
   type_es tenv tenvE es ts ⇒
   tenv_val_exp_ok tenvE ∧ tenv_val_ok tenv.v ⇒
   EVERY (check_freevars (num_tvs tenvE) []) ts) ∧
 (!tenv tenvE funs env.
   type_funs tenv tenvE funs env ⇒
   tenv_val_exp_ok tenvE ∧ tenv_val_ok tenv.v ⇒
   EVERY (check_freevars (num_tvs tenvE) []) (MAP SND env))
-/
theorem type_e_freevars :
    (∀ (tenv : type_env) (tenvE : tenv_val_exp) (e : exp) (t : sem_t),
      type_e tenv tenvE e t →
      tenv_val_exp_ok tenvE ∧ tenv_val_ok tenv.v →
      check_freevars (num_tvs tenvE) [] t) ∧
    (∀ (tenv : type_env) (tenvE : tenv_val_exp) (es : List exp) (ts : List sem_t),
      type_es tenv tenvE es ts →
      tenv_val_exp_ok tenvE ∧ tenv_val_ok tenv.v →
      EVERY (check_freevars (num_tvs tenvE) []) ts) ∧
    (∀ (tenv : type_env) (tenvE : tenv_val_exp) (funs : List (varN × varN × exp))
       (env : List (varN × sem_t)),
      type_funs tenv tenvE funs env →
      tenv_val_exp_ok tenvE ∧ tenv_val_ok tenv.v →
      EVERY (check_freevars (num_tvs tenvE) []) (env.map Prod.snd)) := by
  have H : ∀ (tenv : type_env),
      (∀ tenvE e t, type_e tenv tenvE e t →
        tenv_val_exp_ok tenvE ∧ tenv_val_ok tenv.v → check_freevars (num_tvs tenvE) [] t) ∧
      (∀ tenvE es ts, type_es tenv tenvE es ts →
        tenv_val_exp_ok tenvE ∧ tenv_val_ok tenv.v →
        EVERY (check_freevars (num_tvs tenvE) []) ts) ∧
      (∀ tenvE funs env, type_funs tenv tenvE funs env →
        tenv_val_exp_ok tenvE ∧ tenv_val_ok tenv.v →
        EVERY (check_freevars (num_tvs tenvE) []) (env.map Prod.snd)) := by
    intro tenv
    apply BAux.type_e_ind
    case lit_int => intro tenvE n _; simp [Tint]
    case lit_char => intro tenvE n _; simp [Tchar]
    case lit_str => intro tenvE n _; simp [Tstring]
    case lit_word8 => intro tenvE n _; simp [Tword8]
    case lit_word64 => intro tenvE n _; simp [Tword64]
    case lit_float64 => intro tenvE n _; simp [Tdouble]
    case raise => intro tenvE e t h1 h2 ih _; exact h1
    case handle => intro tenvE e t pes bo h1 h2 h3 h4 h5 ih1 ih2 hh; exact ih1 hh
    case con_some =>
      intro tenvE cn es ts' tvs ts tn h1 h2 h3 h4 ih hh
      simp; exact h1
    case con_none =>
      intro tenvE es ts h ih hh
      have := ih hh
      simpa [Ttup] using this
    case var =>
      rintro tenvE n tvs t targs rfl h2 h3 ⟨hok, hv⟩
      unfold lookup_var at h3
      cases hl : lookup_varE n tenvE with
      | some x =>
        rw [hl] at h3
        simp at h3
        subst h3
        cases n with
        | Short x' =>
          simp [lookup_varE] at hl
          have := tveLookup_freevars_subst tenvE targs x' t 0 ⟨by simpa using h2, hl, hok⟩
          simpa using this
        | Long mn id => simp [lookup_varE] at hl
      | none =>
        rw [hl] at h3
        simp at h3
        have hfv : check_freevars targs.length [] t := hv n (targs.length, t) h3
        exact deBruijn_subst_check_freevars2 _ [] t targs 0 [] ⟨hfv, by simpa using h2⟩
    case fun_ =>
      rintro tenvE n e t1 t2 h1 h2 ih ⟨hok, hv⟩
      have := ih ⟨by simp [tenv_val_exp_ok]; exact ⟨h1, hok⟩, hv⟩
      simp [Tfn, num_tvs] at this ⊢
      exact ⟨h1, this⟩
    case app => intro tenvE o es ts t h1 h2 h3 ih hh; exact h3
    case log => intros; simp [Tbool]
    case if_ => intro tenvE e1 e2 e3 t h1 h2 h3 ih1 ih2 ih3 hh; exact ih2 hh
    case mat =>
      rintro tenvE e t1 t2 pes bo h1 h2 h3 h4 h5 ih1 ih2 ⟨hok, hv⟩
      cases pes with
      | nil => exact absurd rfl h2
      | cons pe pes =>
        have hm : pe ∈ pe :: pes := by simp
        have hp := (type_p_freevars.1 _ _ _ _ _ (h4 pe hm)).2
        have := ih2 pe hm ⟨tenv_val_exp_ok_bvl tenvE _ ⟨hok, hp⟩, hv⟩
        rw [num_tvs_bind_var_list] at this
        exact this
    case let_ =>
      rintro tenvE n e1 t1 e2 t2 h1 h2 ih1 ih2 ⟨hok, hv⟩
      have a := ih1 ⟨hok, hv⟩
      cases n with
      | none => exact ih2 ⟨hok, hv⟩
      | some x =>
        have := ih2 ⟨by simp [opt_bind_name, tenv_val_exp_ok]; exact ⟨a, hok⟩, hv⟩
        simpa [opt_bind_name, num_tvs] using this
    case letrec =>
      rintro tenvE funs bindings e t h1 h2 ih1 ih2 ⟨hok, hv⟩
      have := ih2 ⟨tenv_val_exp_ok_bvl_funs funs bindings tenv bindings tenv.v tenvE ⟨h1, hok⟩, hv⟩
      rw [num_tvs_bind_var_list] at this
      exact this
    case tannot => intro tenvE e t h1 h2 h3 ih hh; exact ih hh
    case lannot => intro tenvE e t l h ih hh; exact ih hh
    case es_nil => intro tenvE _; simp
    case es_cons =>
      intro tenvE e t es ts h1 h2 ih1 ih2 hh
      have a := ih1 hh
      have b := ih2 hh
      simp at b ⊢
      exact ⟨a, b⟩
    case funs_nil => intro tenvE _; simp
    case funs_cons =>
      intro tenvE fn n e t1 t2 funs bindings h1 h2 h3 h4 ih1 ih2 hh
      have b := ih2 hh
      simp at b h1 ⊢
      exact ⟨h1, b⟩
  exact ⟨fun tenv tenvE e t h => (H tenv).1 tenvE e t h,
    fun tenv tenvE es ts h => (H tenv).2.1 tenvE es ts h,
    fun tenv tenvE funs env h => (H tenv).2.2 tenvE funs env h⟩
/- HOL4:
Theorem type_e_subst:
 (!tenv tenvE e t. type_e tenv tenvE e t ⇒
    !tenvE1 targs tvs targs'.
      num_tvs tenvE2 = 0 ∧ ...
  (three-part mutual induction on type_e / type_es / type_funs)
  with free variable tenvE2
-/
theorem B_type_op_subst_aux (f : sem_t → sem_t)
    (hf : ∀ ts tn, f (.Tapp ts tn) = .Tapp (ts.map f) tn)
    (o : op) (ts : List sem_t) (t : sem_t) :
    type_op o ts t → type_op o (ts.map f) (f t) := by
  have hft : ∀ ty, f (t_of ty) = t_of ty := by
    intro ty
    cases ty with
    | WordT ws => cases ws <;> simp [t_of, Tword8, Tword64, hf]
    | _ => simp [t_of, Tbool, Tint, Tchar, Tstring, Tdouble, hf]
  intro h
  unfold type_op at h
  split at h <;>
    simp_all [type_op, hf, hft, Tfn, Tref, Tbool, Tint, Tchar, Tstring, Tword8, Tword64,
      Tword8array, Tdouble, Ttup, Tlist, Tvector, Tarray]
  all_goals first
    | (intro a ha; rw [h.1 a ha]; exact hft _)
    | (obtain ⟨rfl, _, rfl, _⟩ := h; exact hft _)
    | (rw [← h.2, hf]; simp)
    | (obtain ⟨_, t2, rfl⟩ := h; exact ⟨f t2, by simp [hf]⟩)

theorem B_ALOOKUP_map_aux (f : sem_t → sem_t) (bindings : List (varN × sem_t)) (fn : varN) :
    ALOOKUP (bindings.map (fun (x, t) => (x, f t))) fn = (ALOOKUP bindings fn).map f := by
  induction bindings with
  | nil => simp [ALOOKUP]
  | cons a bs ih =>
    obtain ⟨x, t⟩ := a
    by_cases h : x = fn <;> simp [ALOOKUP, h, ih]

theorem B_num_tvs_merge_aux (tenvE1 tenvE2 : tenv_val_exp) (k : Nat) (h0 : num_tvs tenvE2 = 0) :
    num_tvs (db_merge tenvE1 (bind_tvar k tenvE2)) = num_tvs tenvE1 + k := by
  rw [num_tvs_db_merge, bind_tvar_rewrites.2.1, h0]; simp

theorem B_num_tvs_merge_aux' (targs : List sem_t) (tenvE1 tenvE2 : tenv_val_exp) (k : Nat)
    (h0 : num_tvs tenvE2 = 0) :
    num_tvs (db_merge (deBruijn_subst_tenvE targs tenvE1) (bind_tvar k tenvE2)) =
      num_tvs tenvE1 + k := by
  rw [num_tvs_db_merge, bind_tvar_rewrites.2.1, h0, num_tvs_deBruijn_subst_tenvE]; simp

theorem B_type_e_subst_var_aux (tenvE2 : tenv_val_exp) (tenv : type_env) (tenvE1 : tenv_val_exp)
    (targs : List sem_t) (tvs : Nat) (n : cml_id modN varN) (tvs0 : Nat) (t : sem_t)
    (h0 : num_tvs tenvE2 = 0) (hv : tenv_val_ok tenv.v)
    (hok : tenv_val_exp_ok (db_merge tenvE1 (bind_tvar targs.length tenvE2)))
    (hl : lookup_var n (db_merge tenvE1 (bind_tvar targs.length tenvE2)) tenv = some (tvs0, t)) :
    ∃ t', lookup_var n (db_merge (deBruijn_subst_tenvE targs tenvE1) (bind_tvar tvs tenvE2)) tenv
        = some (tvs0, t') ∧
      ∀ targs0 : List sem_t, targs0.length = tvs0 →
        deBruijn_subst (num_tvs tenvE1) (targs.map (deBruijn_inc 0 (num_tvs tenvE1)))
          (deBruijn_subst 0 targs0 t) =
        deBruijn_subst 0
          (targs0.map (deBruijn_subst (num_tvs tenvE1)
            (targs.map (deBruijn_inc 0 (num_tvs tenvE1))))) t' := by
  have hok2 : tenv_val_exp_ok tenvE2 :=
    (bind_tvar_rewrites.2.2.2.2.2.2.1 _ _).1 (tenv_val_exp_ok_db_merge _ _ hok)
  have hclosed : ∀ t', check_freevars tvs0 [] t' →
      ∀ targs0 : List sem_t, targs0.length = tvs0 →
        deBruijn_subst (num_tvs tenvE1) (targs.map (deBruijn_inc 0 (num_tvs tenvE1)))
          (deBruijn_subst 0 targs0 t') =
        deBruijn_subst 0
          (targs0.map (deBruijn_subst (num_tvs tenvE1)
            (targs.map (deBruijn_inc 0 (num_tvs tenvE1))))) t' := by
    intro t' hfv targs0 hlen
    subst hlen
    exact deBruijn_subst2_thm.1 t' (num_tvs tenvE1) targs0 targs [] hfv
  unfold lookup_var at hl ⊢
  cases n with
  | Long mn id =>
    simp only [lookup_varE] at hl ⊢
    exact ⟨t, hl, hclosed t (hv _ (tvs0, t) hl)⟩
  | Short x =>
    simp only [lookup_varE] at hl ⊢
    cases hlk : tveLookup x 0 (db_merge tenvE1 (bind_tvar targs.length tenvE2)) with
    | none =>
      rw [hlk] at hl
      simp only at hl
      rw [tveLookup_db_merge_none, bind_tvar_rewrites.2.2.2.2.2.1] at hlk
      have hlk2 := (tveLookup_inc_none x _ tenvE2).1 hlk.2
      have hnone : tveLookup x 0 (db_merge (deBruijn_subst_tenvE targs tenvE1)
          (bind_tvar tvs tenvE2)) = none := by
        rw [tveLookup_db_merge_none, bind_tvar_rewrites.2.2.2.2.2.1, tveLookup_subst_none]
        exact ⟨hlk.1, (tveLookup_inc_none x _ tenvE2).2 hlk2⟩
      rw [hnone]
      exact ⟨t, hl, hclosed t (hv _ (tvs0, t) hl)⟩
    | some p =>
      rw [hlk] at hl
      simp only [Option.some.injEq] at hl
      subst hl
      rw [tveLookup_db_merge_some] at hlk
      rcases hlk with hlk | ⟨hlk1, hlk2⟩
      · have h1 := tveLookup_subst_some x tenvE1 targs tvs0 t 0 hlk
        have h2 := (tveLookup_db_merge_some x 0 (deBruijn_subst_tenvE targs tenvE1)
          (bind_tvar tvs tenvE2) tvs0 _).2 (Or.inl h1)
        rw [h2]
        refine ⟨_, rfl, ?_⟩
        intro targs0 hlen
        subst hlen
        have := type_e_subst_lem7.1 t (num_tvs tenvE1) targs0 targs [] []
        simpa using this
      · rw [bind_tvar_rewrites.2.2.2.2.2.1, tveLookup_no_tvs _ _ _ _ _ ⟨hok2, h0⟩] at hlk2
        have h2 := (tveLookup_db_merge_some x 0 (deBruijn_subst_tenvE targs tenvE1)
          (bind_tvar tvs tenvE2) tvs0 t).2 (Or.inr ⟨by rw [tveLookup_subst_none]; exact hlk1, by
            rw [bind_tvar_rewrites.2.2.2.2.2.1, tveLookup_no_tvs _ _ _ _ _ ⟨hok2, h0⟩]
            exact hlk2⟩)
        rw [h2]
        exact ⟨t, rfl, hclosed t (tveLookup_freevars_thm x 0 tenvE2 tvs0 t ⟨hok2, h0, hlk2⟩)⟩

theorem B_type_e_subst_aux (tenvE2 : tenv_val_exp) (tenv : type_env) (targs : List sem_t) (tvs : Nat)
    (h0 : num_tvs tenvE2 = 0) (hta : tenv_abbrev_ok tenv.t) (hc : tenv_ctor_ok tenv.c)
    (hv : tenv_val_ok tenv.v) (hEV : EVERY (check_freevars tvs []) targs) :
    (∀ tenvE e t, type_e tenv tenvE e t →
      ∀ tenvE1, tenv_val_exp_ok tenvE →
        tenvE = db_merge tenvE1 (bind_tvar targs.length tenvE2) →
        type_e tenv (db_merge (deBruijn_subst_tenvE targs tenvE1) (bind_tvar tvs tenvE2)) e
          (deBruijn_subst (num_tvs tenvE1) (targs.map (deBruijn_inc 0 (num_tvs tenvE1))) t)) ∧
    (∀ tenvE es ts, type_es tenv tenvE es ts →
      ∀ tenvE1, tenv_val_exp_ok tenvE →
        tenvE = db_merge tenvE1 (bind_tvar targs.length tenvE2) →
        type_es tenv (db_merge (deBruijn_subst_tenvE targs tenvE1) (bind_tvar tvs tenvE2)) es
          (ts.map (deBruijn_subst (num_tvs tenvE1) (targs.map (deBruijn_inc 0 (num_tvs tenvE1)))))) ∧
    (∀ tenvE funs env, type_funs tenv tenvE funs env →
      ∀ tenvE1, tenv_val_exp_ok tenvE →
        tenvE = db_merge tenvE1 (bind_tvar targs.length tenvE2) →
        type_funs tenv (db_merge (deBruijn_subst_tenvE targs tenvE1) (bind_tvar tvs tenvE2)) funs
          (env.map (fun (x, t) => (x, deBruijn_subst (num_tvs tenvE1)
            (targs.map (deBruijn_inc 0 (num_tvs tenvE1))) t)))) := by
  have hfv : ∀ (tenvE1 : tenv_val_exp) (t : sem_t),
      check_freevars (num_tvs (db_merge tenvE1 (bind_tvar targs.length tenvE2))) [] t →
      check_freevars (num_tvs (db_merge (deBruijn_subst_tenvE targs tenvE1) (bind_tvar tvs tenvE2))) []
        (deBruijn_subst (num_tvs tenvE1) (targs.map (deBruijn_inc 0 (num_tvs tenvE1))) t) := by
    intro tenvE1 t h
    rw [B_num_tvs_merge_aux _ _ _ h0] at h
    rw [B_num_tvs_merge_aux' _ _ _ _ h0]
    exact check_freevars_lem _ _ t h targs (num_tvs tenvE1) tvs ⟨rfl, hEV⟩
  apply BAux.type_e_ind
  case lit_int =>
    intro tenvE n tenvE1 hok heq
    simpa [Tint, deBruijn_subst] using type_e.lit_int tenv _ n
  case lit_char =>
    intro tenvE n tenvE1 hok heq
    simpa [Tchar, deBruijn_subst] using type_e.lit_char tenv _ n
  case lit_str =>
    intro tenvE n tenvE1 hok heq
    simpa [Tstring, deBruijn_subst] using type_e.lit_str tenv _ n
  case lit_word8 =>
    intro tenvE n tenvE1 hok heq
    simpa [Tword8, deBruijn_subst] using type_e.lit_word8 tenv _ n
  case lit_word64 =>
    intro tenvE n tenvE1 hok heq
    simpa [Tword64, deBruijn_subst] using type_e.lit_word64 tenv _ n
  case lit_float64 =>
    intro tenvE n tenvE1 hok heq
    simpa [Tdouble, deBruijn_subst] using type_e.lit_float64 tenv _ n
  case raise =>
    intro tenvE e t h1 h2 ih tenvE1 hok heq
    subst heq
    have := ih tenvE1 hok rfl
    simp only [Texn, deBruijn_subst, List.map] at this
    exact type_e.raise _ _ _ _ (hfv _ _ h1) this
  case handle =>
    intro tenvE e t pes bo h1 h2 h3 h4 h5 ih1 ih2 tenvE1 hok heq
    subst heq
    refine type_e.handle _ _ _ _ _
      (fun pe => (bo pe).map (fun (x, t) => (x, deBruijn_subst (num_tvs tenvE1)
        (targs.map (deBruijn_inc 0 (num_tvs tenvE1))) t)))
      (ih1 tenvE1 hok rfl) h2 h3 ?_ ?_
    · intro pe hm
      have := type_p_subst.1 _ _ _ _ _ (h4 pe hm) _ (num_tvs tenvE1) tvs targs
        ⟨hta, hc, B_num_tvs_merge_aux _ _ _ h0, hEV, rfl⟩
      rw [B_num_tvs_merge_aux' _ _ _ _ h0]
      simpa [Texn, deBruijn_subst] using this
    · intro pe hm
      have hp := (type_p_freevars.1 _ _ _ _ _ (h4 pe hm)).2
      have := ih2 pe hm (bind_var_list 0 (bo pe) tenvE1) (tenv_val_exp_ok_bvl _ _ ⟨hok, hp⟩)
        (by rw [db_merge_bvl])
      rw [deBruijn_subst_E_bvl, db_merge_bvl, num_tvs_bind_var_list] at this
      simpa using this
  case con_some =>
    intro tenvE cn es ts' tvs0 ts tn h1 h2 h3 h4 ih tenvE1 hok heq
    subst heq
    have ih' := ih tenvE1 hok rfl
    have hts : EVERY (check_freevars 0 tvs0) ts := tenv_ctor_ok_lookup _ _ _ _ _ ⟨hc, h4⟩
    have e := type_subst_deBruijn_subst_list default tvs0 [] ts'
      (targs.map (deBruijn_inc 0 (num_tvs tenvE1))) ts (num_tvs tenvE1) ⟨h2, hts⟩
    simp only [ZIP] at e
    rw [e] at ih'
    simp only [deBruijn_subst]
    refine type_e.con_some _ _ cn es (ts'.map (deBruijn_subst (num_tvs tenvE1) _)) tvs0 ts tn ?_
      (by simpa using h2) ih' h4
    intro t' ht'
    simp at ht'
    obtain ⟨a, ha, rfl⟩ := ht'
    exact hfv _ _ (h1 a ha)
  case con_none =>
    intro tenvE es ts h ih tenvE1 hok heq
    have := ih tenvE1 hok heq
    simp only [Ttup, deBruijn_subst]
    exact type_e.con_none _ _ _ _ this
  case var =>
    rintro tenvE n tvs0 t targs0 rfl h2 h3 tenvE1 hok heq
    subst heq
    obtain ⟨t', hl, heq⟩ := B_type_e_subst_var_aux tenvE2 tenv tenvE1 targs tvs n targs0.length t
      h0 hv hok h3
    rw [heq targs0 rfl]
    refine type_e.var _ _ n targs0.length t' (targs0.map _) (by simp) ?_ hl
    intro ta hta'
    simp at hta'
    obtain ⟨a, ha, rfl⟩ := hta'
    exact hfv _ _ (h2 a ha)
  case fun_ =>
    intro tenvE n e t1 t2 h1 h2 ih tenvE1 hok heq
    subst heq
    have := ih (.Bind_name n 0 t1 tenvE1) (by simp [tenv_val_exp_ok]; exact ⟨h1, hok⟩)
      (by simp [db_merge])
    simp only [deBruijn_subst_tenvE, db_merge, num_tvs, Nat.zero_add] at this
    simp only [Tfn, deBruijn_subst, List.map]
    exact type_e.fun_ _ _ _ _ _ _ (hfv _ _ h1) this
  case app =>
    intro tenvE o es ts t h1 h2 h3 ih tenvE1 hok heq
    subst heq
    exact type_e.app _ _ _ _ _ _ (ih tenvE1 hok rfl)
      (B_type_op_subst_aux _ (by intro ts tn; simp [deBruijn_subst]) _ _ _ h2) (hfv _ _ h3)
  case log =>
    intro tenvE l e1 e2 h1 h2 ih1 ih2 tenvE1 hok heq
    have a := ih1 tenvE1 hok heq
    have b := ih2 tenvE1 hok heq
    simp only [Tbool, deBruijn_subst, List.map] at a b ⊢
    exact type_e.log _ _ _ _ _ a b
  case if_ =>
    intro tenvE e1 e2 e3 t h1 h2 h3 ih1 ih2 ih3 tenvE1 hok heq
    have a := ih1 tenvE1 hok heq
    simp only [Tbool, deBruijn_subst, List.map] at a
    exact type_e.if_ _ _ _ _ _ _ a (ih2 tenvE1 hok heq) (ih3 tenvE1 hok heq)
  case mat =>
    intro tenvE e t1 t2 pes bo h1 h2 h3 h4 h5 ih1 ih2 tenvE1 hok heq
    subst heq
    refine type_e.mat _ _ _ _ _ _
      (fun pe => (bo pe).map (fun (x, t) => (x, deBruijn_subst (num_tvs tenvE1)
        (targs.map (deBruijn_inc 0 (num_tvs tenvE1))) t)))
      (ih1 tenvE1 hok rfl) h2 h3 ?_ ?_
    · intro pe hm
      have := type_p_subst.1 _ _ _ _ _ (h4 pe hm) _ (num_tvs tenvE1) tvs targs
        ⟨hta, hc, B_num_tvs_merge_aux _ _ _ h0, hEV, rfl⟩
      rw [B_num_tvs_merge_aux' _ _ _ _ h0]
      exact this
    · intro pe hm
      have hp := (type_p_freevars.1 _ _ _ _ _ (h4 pe hm)).2
      have := ih2 pe hm (bind_var_list 0 (bo pe) tenvE1) (tenv_val_exp_ok_bvl _ _ ⟨hok, hp⟩)
        (by rw [db_merge_bvl])
      rw [deBruijn_subst_E_bvl, db_merge_bvl, num_tvs_bind_var_list] at this
      simpa using this
  case let_ =>
    intro tenvE n e1 t1 e2 t2 h1 h2 ih1 ih2 tenvE1 hok heq
    subst heq
    have a := ih1 tenvE1 hok rfl
    have hfv1 := (type_e_freevars.1 _ _ _ _ h1) ⟨hok, hv⟩
    cases n with
    | none =>
      have b := ih2 tenvE1 (by simpa [opt_bind_name] using hok) (by simp [opt_bind_name])
      exact type_e.let_ _ _ none _ _ _ _ a (by simpa [opt_bind_name] using b)
    | some x =>
      have b := ih2 (.Bind_name x 0 t1 tenvE1)
        (by simp [opt_bind_name, tenv_val_exp_ok]; exact ⟨hfv1, hok⟩)
        (by simp [opt_bind_name, db_merge])
      simp only [deBruijn_subst_tenvE, db_merge, num_tvs, Nat.zero_add] at b
      exact type_e.let_ _ _ (some x) _ _ _ _ a (by simpa [opt_bind_name] using b)
  case letrec =>
    intro tenvE funs bindings e t h1 h2 ih1 ih2 tenvE1 hok heq
    subst heq
    have hok' := tenv_val_exp_ok_bvl_funs funs bindings tenv bindings tenv.v _ ⟨h1, hok⟩
    have a := ih1 (bind_var_list 0 bindings tenvE1) hok' (by rw [db_merge_bvl])
    have b := ih2 (bind_var_list 0 bindings tenvE1) hok' (by rw [db_merge_bvl])
    rw [deBruijn_subst_E_bvl, db_merge_bvl, num_tvs_bind_var_list] at a b
    simp only [Nat.zero_add] at a b
    exact type_e.letrec _ _ _ _ _ _ a b
  case tannot =>
    intro tenvE e t h1 h2 h3 ih tenvE1 hok heq
    have ih' := ih tenvE1 hok heq
    have hfvt := check_freevars_type_name_subst [] t (num_tvs tenvE1) tenv.t ⟨hta, h2, h1⟩
    rw [nil_deBruijn_subst _ _ _ hfvt] at ih' ⊢
    exact type_e.tannot _ _ _ _ h1 h2 ih'
  case lannot =>
    intro tenvE e t l h ih tenvE1 hok heq
    exact type_e.lannot _ _ _ _ _ (ih tenvE1 hok heq)
  case es_nil => intro tenvE tenvE1 hok heq; exact type_es.nil _ _
  case es_cons =>
    intro tenvE e t es ts h1 h2 ih1 ih2 tenvE1 hok heq
    simp only [List.map]
    exact type_es.cons _ _ _ _ _ _ (ih1 tenvE1 hok heq) (ih2 tenvE1 hok heq)
  case funs_nil => intro tenvE tenvE1 hok heq; exact type_funs.nil _ _
  case funs_cons =>
    intro tenvE fn n e t1 t2 funs bindings h1 h2 h3 h4 ih1 ih2 tenvE1 hok heq
    subst heq
    have h1' := hfv _ _ h1
    have hfv1 : check_freevars (num_tvs (db_merge tenvE1 (bind_tvar targs.length tenvE2))) [] t1 := by
      simp [Tfn] at h1; exact h1.1
    have a := ih1 (.Bind_name n 0 t1 tenvE1) (by simp [tenv_val_exp_ok]; exact ⟨hfv1, hok⟩)
      (by simp [db_merge])
    simp only [deBruijn_subst_tenvE, db_merge, num_tvs, Nat.zero_add] at a
    have b := ih2 tenvE1 hok rfl
    simp only [List.map, Tfn, deBruijn_subst] at h1' ⊢
    refine type_funs.cons _ _ _ _ _ _ _ _ _ h1' a b ?_
    rw [B_ALOOKUP_map_aux]
    simp [h4]
theorem type_e_subst :
    ∀ (tenvE2 : tenv_val_exp),
    (∀ (tenv : type_env) (tenvE : tenv_val_exp) (e : exp) (t : sem_t),
      type_e tenv tenvE e t →
      ∀ (tenvE1 : tenv_val_exp) (targs : List sem_t) (tvs : Nat) (targs' : List sem_t),
        num_tvs tenvE2 = 0 ∧
        tenv_abbrev_ok tenv.t ∧
        tenv_ctor_ok tenv.c ∧
        tenv_val_ok tenv.v ∧
        tenv_val_exp_ok tenvE ∧
        EVERY (check_freevars tvs []) targs ∧
        tenvE = db_merge tenvE1 (bind_tvar targs.length tenvE2) ∧
        targs' = targs.map (deBruijn_inc 0 (num_tvs tenvE1)) →
        type_e tenv (db_merge (deBruijn_subst_tenvE targs tenvE1) (bind_tvar tvs tenvE2))
          e (deBruijn_subst (num_tvs tenvE1) targs' t)) ∧
    (∀ (tenv : type_env) (tenvE : tenv_val_exp) (es : List exp) (ts : List sem_t),
      type_es tenv tenvE es ts →
      ∀ (tenvE1 : tenv_val_exp) (targs : List sem_t) (tvs : Nat) (targs' : List sem_t),
        num_tvs tenvE2 = 0 ∧
        tenv_abbrev_ok tenv.t ∧
        tenv_ctor_ok tenv.c ∧
        tenv_val_ok tenv.v ∧
        tenv_val_exp_ok tenvE ∧
        EVERY (check_freevars tvs []) targs ∧
        tenvE = db_merge tenvE1 (bind_tvar targs.length tenvE2) ∧
        targs' = targs.map (deBruijn_inc 0 (num_tvs tenvE1)) →
        type_es tenv (db_merge (deBruijn_subst_tenvE targs tenvE1) (bind_tvar tvs tenvE2))
          es (ts.map (deBruijn_subst (num_tvs tenvE1) targs'))) ∧
    (∀ (tenv : type_env) (tenvE : tenv_val_exp) (funs : List (varN × varN × exp))
       (env : List (varN × sem_t)),
      type_funs tenv tenvE funs env →
      ∀ (tenvE1 : tenv_val_exp) (targs : List sem_t) (tvs : Nat) (targs' : List sem_t),
        num_tvs tenvE2 = 0 ∧
        tenv_abbrev_ok tenv.t ∧
        tenv_ctor_ok tenv.c ∧
        tenv_val_ok tenv.v ∧
        tenv_val_exp_ok tenvE ∧
        EVERY (check_freevars tvs []) targs ∧
        tenvE = db_merge tenvE1 (bind_tvar targs.length tenvE2) ∧
        targs' = targs.map (deBruijn_inc 0 (num_tvs tenvE1)) →
        type_funs tenv (db_merge (deBruijn_subst_tenvE targs tenvE1) (bind_tvar tvs tenvE2))
          funs (env.map (fun (x, t) => (x, deBruijn_subst (num_tvs tenvE1) targs' t)))) := by
  intro tenvE2
  refine ⟨?_, ?_, ?_⟩
  · rintro tenv tenvE e t h tenvE1 targs tvs targs' ⟨h0, hta, hc, hv, hok, hEV, heq, rfl⟩
    exact (B_type_e_subst_aux tenvE2 tenv targs tvs h0 hta hc hv hEV).1 tenvE e t h tenvE1 hok heq
  · rintro tenv tenvE es ts h tenvE1 targs tvs targs' ⟨h0, hta, hc, hv, hok, hEV, heq, rfl⟩
    exact (B_type_e_subst_aux tenvE2 tenv targs tvs h0 hta hc hv hEV).2.1 tenvE es ts h tenvE1 hok heq
  · rintro tenv tenvE funs env h tenvE1 targs tvs targs' ⟨h0, hta, hc, hv, hok, hEV, heq, rfl⟩
    exact (B_type_e_subst_aux tenvE2 tenv targs tvs h0 hta hc hv hEV).2.2 tenvE funs env h tenvE1 hok heq
/- HOL4:
Theorem type_funs_Tfn:
   ∀tenv tenvE funs bindings tvs t n.
    type_funs tenv tenvE funs bindings ∧
    ALOOKUP bindings n = SOME t
    ⇒
    ∃t1 t2. (t = Tfn t1 t2) ∧ check_freevars (num_tvs tenvE) [] (Tfn t1 t2)
-/
theorem type_funs_Tfn :
    ∀ (tenv : type_env) (tenvE : tenv_val_exp) (funs : List (varN × varN × exp))
      (bindings : List (varN × sem_t)) (tvs : Nat) (t : sem_t) (n : varN),
      type_funs tenv tenvE funs bindings ∧
      ALOOKUP bindings n = some t →
      ∃ (t1 t2 : sem_t), t = Tfn t1 t2 ∧ check_freevars (num_tvs tenvE) [] (Tfn t1 t2) := by
  intro tenv tenvE funs
  induction funs with
  | nil => rintro bindings _ t n ⟨h1, h2⟩; cases h1; simp [ALOOKUP] at h2
  | cons f funs ih =>
    rintro bindings tvs t n ⟨h1, h2⟩
    cases h1
    rename_i fn' n' e' t1 t2 bindings' ha hc he hf
    by_cases hfn : fn' = n
    · simp [ALOOKUP, hfn] at h2
      subst h2
      exact ⟨_, _, rfl, hc⟩
    · simp [ALOOKUP, hfn] at h2
      exact ih _ tvs t n ⟨hf, h2⟩
/- HOL4:
Theorem type_funs_lookup:
 ∀fn tenvE funs bindings n e tenv.
  MEM (fn,n,e) funs ∧
  type_funs tenv tenvE funs bindings
  ⇒
  (∃t. ALOOKUP bindings fn = SOME t)
-/
theorem type_funs_lookup :
    ∀ (fn : varN) (tenvE : tenv_val_exp) (funs : List (varN × varN × exp))
      (bindings : List (varN × sem_t)) (n : varN) (e : exp) (tenv : type_env),
      (fn, n, e) ∈ funs ∧
      type_funs tenv tenvE funs bindings →
      ∃ (t : sem_t), ALOOKUP bindings fn = some t := by
  intro fn tenvE funs
  induction funs with
  | nil => rintro bindings n e tenv ⟨h1, _⟩; simp at h1
  | cons f funs ih =>
    rintro bindings n e tenv ⟨h1, h2⟩
    cases h2
    rename_i fn' n' e' t1 t2 bindings' ha hc he hf
    by_cases hfn : fn' = fn
    · simp [ALOOKUP, hfn]
    · simp [ALOOKUP, hfn]
      simp at h1
      rcases h1 with ⟨rfl, _⟩ | h1
      · exact absurd rfl hfn
      · exact ih _ n e tenv ⟨h1, hf⟩
/- HOL4:
Theorem type_funs_find_recfun:
 ∀fn env funs bindings e tenv tenvE t.
  ALOOKUP bindings fn = SOME t ∧
  type_funs tenv tenvE funs bindings
  ⇒
  (∃n e. find_recfun fn funs = SOME (n,e))
-/
theorem type_funs_find_recfun :
    ∀ (fn : varN) (env : List (varN × sem_t)) (funs : List (varN × varN × exp))
      (bindings : List (varN × sem_t)) (e : exp) (tenv : type_env)
      (tenvE : tenv_val_exp) (t : sem_t),
      ALOOKUP bindings fn = some t ∧
      type_funs tenv tenvE funs bindings →
      ∃ (n : varN) (e : exp), find_recfun fn funs = some (n, e) := by
  intro fn env funs
  induction funs with
  | nil => rintro bindings e tenv tenvE t ⟨h1, h2⟩; cases h2; simp [ALOOKUP] at h1
  | cons f funs ih =>
    rintro bindings e tenv tenvE t ⟨h1, h2⟩
    cases h2
    rename_i fn' n' e' t1 t2 bindings' ha hc he hf
    by_cases hfn : fn' = fn
    · simp [find_recfun, hfn]
    · simp [ALOOKUP, hfn] at h1
      simp [find_recfun, hfn]
      exact ih _ e tenv tenvE t ⟨h1, hf⟩
/- HOL4:
Theorem type_recfun_lookup:
   ∀fn funs n e tenv tenvE bindings tvs t1 t2.
    find_recfun fn funs = SOME (n,e) ∧
    type_funs tenv tenvE funs bindings ∧
    ALOOKUP bindings fn = SOME (Tfn t1 t2)
    ⇒
    type_e tenv (Bind_name n 0 t1 tenvE) e t2 ∧
    check_freevars (num_tvs tenvE) [] (Tfn t1 t2)
-/
theorem type_recfun_lookup :
    ∀ (fn : varN) (funs : List (varN × varN × exp)) (n : varN) (e : exp)
      (tenv : type_env) (tenvE : tenv_val_exp) (bindings : List (varN × sem_t))
      (tvs : Nat) (t1 t2 : sem_t),
      find_recfun fn funs = some (n, e) ∧
      type_funs tenv tenvE funs bindings ∧
      ALOOKUP bindings fn = some (Tfn t1 t2) →
      type_e tenv (.Bind_name n 0 t1 tenvE) e t2 ∧
      check_freevars (num_tvs tenvE) [] (Tfn t1 t2) := by
  intro fn funs
  induction funs with
  | nil => rintro n e tenv tenvE bindings tvs t1 t2 ⟨h1, _⟩; simp [find_recfun] at h1
  | cons f funs ih =>
    rintro n e tenv tenvE bindings tvs t1 t2 ⟨h1, h2, h3⟩
    cases h2
    rename_i fn' n' e' t1' t2' bindings' ha hc he hf
    by_cases hfn : fn' = fn
    · simp [find_recfun, hfn] at h1
      simp [ALOOKUP, hfn, Tfn] at h3
      obtain ⟨rfl, rfl⟩ := h1
      obtain ⟨rfl, rfl⟩ := h3
      exact ⟨he, hc⟩
    · simp [find_recfun, hfn] at h1
      simp [ALOOKUP, hfn] at h3
      exact ih n e tenv tenvE _ tvs t1 t2 ⟨h1, hf, h3⟩
/- HOL4:
Theorem type_funs_distinct:
 ∀tenv tenvE funs bindings .
  type_funs tenv tenvE funs bindings
  ⇒
  ALL_DISTINCT (MAP (λ(x,y,z). x) funs)
-/
theorem type_funs_distinct :
    ∀ (tenv : type_env) (tenvE : tenv_val_exp) (funs : List (varN × varN × exp))
      (bindings : List (varN × sem_t)),
      type_funs tenv tenvE funs bindings →
      ALL_DISTINCT (funs.map (fun (x, _, _) => x)) := by
  intro tenv tenvE funs
  induction funs with
  | nil => intro b h; simp [ALL_DISTINCT]
  | cons f funs ih =>
    intro b h
    cases h
    rename_i fn' n' e' t1 t2 bindings' ha hc he hf
    simp only [List.map, ALL_DISTINCT]
    simp
    refine ⟨?_, ih _ hf⟩
    intro a b c hm heq
    subst heq
    obtain ⟨t, ht⟩ := type_funs_lookup a tenvE funs bindings' b c tenv ⟨hm, hf⟩
    rw [ha] at ht
    cases ht
/- HOL4: [local]
Theorem type_e_subst_lem:
  ∀tenv tenvE e t targs tvs targs'.
  type_e tenv (Bind_name x 0 t1 (bind_tvar (LENGTH targs) tenvE)) e t ∧
  num_tvs tenvE = 0 ∧ ...
  (with free variables x and t1)
-/
theorem type_e_subst_lem :
    ∀ (x : mlstring) (t1 : sem_t)
      (tenv : type_env) (tenvE : tenv_val_exp) (e : exp) (t : sem_t)
      (targs : List sem_t) (tvs : Nat) (targs' : List sem_t),
      type_e tenv (.Bind_name x 0 t1 (bind_tvar targs.length tenvE)) e t ∧
      num_tvs tenvE = 0 ∧
      tenv_abbrev_ok tenv.t ∧
      tenv_ctor_ok tenv.c ∧
      tenv_val_ok tenv.v ∧
      tenv_val_exp_ok (bind_tvar targs.length tenvE) ∧
      EVERY (check_freevars tvs []) targs ∧
      check_freevars targs.length [] t1 →
      type_e tenv (.Bind_name x 0 (deBruijn_subst 0 targs t1) (bind_tvar tvs tenvE))
        e (deBruijn_subst 0 targs t) := by
  rintro x t1 tenv tenvE e t targs tvs targs' ⟨h, h0, hta, hc, hv, hok, hEV, hfv1⟩
  have := (type_e_subst tenvE).1 tenv _ e t h (.Bind_name x 0 t1 .Empty) targs tvs
    (targs.map (deBruijn_inc 0 0))
    ⟨h0, hta, hc, hv, by
      simp only [tenv_val_exp_ok, bind_tvar_rewrites.2.1, h0]
      exact ⟨by simpa using hfv1, hok⟩, hEV, by simp [db_merge], by simp [num_tvs]⟩
  simp only [deBruijn_subst_tenvE, db_merge, num_tvs, Nat.zero_add, deBruijn_inc0.2] at this
  exact this
/- HOL4:
Theorem mem_type_def_to_ctMap:
   !tenvT next tds ids stamp x.
    MEM (stamp,x) (type_def_to_ctMap tenvT next tds ids) ∧
    LENGTH tds = LENGTH ids
    ⇒
    ?cn i. stamp = TypeStamp cn i ∧ next ≤ i ∧ i < next + LENGTH tds
-/
theorem B_ALOOKUP_mem_aux {α β : Type} [BEq α] [LawfulBEq α] (l : List (α × β)) (k : α) (v : β) :
    ALOOKUP l k = some v → (k, v) ∈ l := by
  induction l with
  | nil => simp [ALOOKUP]
  | cons a l ih =>
    obtain ⟨k', v'⟩ := a
    by_cases h : k' = k
    · simp [ALOOKUP, h]
      intro h'; exact Or.inl h'.symm
    · simp [ALOOKUP, h]
      intro h'; exact Or.inr (ih h')

theorem B_mem_ctMap_aux (tenvT : tenv_abbrev) :
    ∀ (tds : List (List tvarN × mlstring × List (conN × List ast_t))) (next : Nat)
      (ids : List type_ident) (stmp : stamp) (tvs : List tvarN) (ts : List sem_t) (ti : type_ident),
      (stmp, (tvs, ts, ti)) ∈ type_def_to_ctMap tenvT next tds ids →
      ∃ (cn : conN) (i : Nat) (tn : mlstring) (ctors : List (conN × List ast_t)) (cts : List ast_t),
        stmp = .TypeStamp cn (next + i) ∧ i < tds.length ∧ ids[i]? = some ti ∧
        (tvs, tn, ctors) ∈ tds ∧ (cn, cts) ∈ ctors ∧ ts = cts.map (type_name_subst tenvT) := by
  intro tds
  induction tds with
  | nil => intro next ids stmp tvs ts ti h; cases ids <;> simp [type_def_to_ctMap] at h
  | cons td tds ih =>
    intro next ids stmp tvs ts ti h
    obtain ⟨tvs', tn', ctors'⟩ := td
    cases ids with
    | nil => simp [type_def_to_ctMap] at h
    | cons id_ ids =>
      simp only [type_def_to_ctMap, List.mem_append, List.mem_reverse, List.mem_map] at h
      rcases h with h | h
      · obtain ⟨cn, i, tn, ctors, cts, h1, h2, h3, h4, h5, h6⟩ := ih (next + 1) ids stmp tvs ts ti h
        refine ⟨cn, i + 1, tn, ctors, cts, ?_, by simp; omega, by simpa using h3, by simp [h4], h5, h6⟩
        rw [h1]; congr 1; omega
      · obtain ⟨⟨cn, cts⟩, hm, heq⟩ := h
        simp at heq
        obtain ⟨rfl, rfl, rfl, rfl⟩ := heq
        exact ⟨cn, 0, tn', ctors', cts, by simp, by simp, by simp, by simp, hm, rfl⟩
theorem mem_type_def_to_ctMap :
    ∀ (tenvT : tenv_abbrev) (next : Nat)
      (tds : List (List tvarN × mlstring × List (conN × List ast_t)))
      (ids : List type_ident) (stmp : stamp)
      (x : List tvarN × List sem_t × type_ident),
      (stmp, x) ∈ type_def_to_ctMap tenvT next tds ids ∧
      tds.length = ids.length →
      ∃ (cn : conN) (i : Nat), stmp = .TypeStamp cn i ∧ next ≤ i ∧ i < next + tds.length := by
  rintro tenvT next tds ids stmp ⟨tvs, ts, ti⟩ ⟨h, hl⟩
  obtain ⟨cn, i, tn, ctors, cts, h1, h2, h3, h4, h5, h6⟩ := B_mem_ctMap_aux tenvT tds next ids stmp tvs ts ti h
  exact ⟨cn, next + i, h1, by omega, by omega⟩
/- HOL4:
Theorem ctMap_ok_merge_imp:
   !ctMap1 ctMap2.
    DISJOINT (FRANGE ((SND o SND) o_f ctMap1)) (FRANGE ((SND o SND) o_f ctMap2)) ∧
    ctMap_ok ctMap1 ∧ ctMap_ok ctMap2 ⇒
    ctMap_ok (FUNION ctMap1 ctMap2)
-/
theorem ctMap_ok_merge_imp :
    ∀ (ctMap1 ctMap2 : ctMap),
      Set.Disjoint
        (Finmap.FRANGE (Finmap.o_f (fun p => p.2.2) ctMap1))
        (Finmap.FRANGE (Finmap.o_f (fun p => p.2.2) ctMap2)) ∧
      ctMap_ok ctMap1 ∧ ctMap_ok ctMap2 →
      ctMap_ok (Finmap.FUNION ctMap1 ctMap2) := by
  rintro ctMap1 ctMap2 ⟨hd, h1, h2⟩
  obtain ⟨a1, b1, c1, d1⟩ := h1
  obtain ⟨a2, b2, c2, d2⟩ := h2
  have key : ∀ k v, Finmap.FUNION ctMap1 ctMap2 k = some v →
      ctMap1 k = some v ∨ ctMap2 k = some v := by
    intro k v h
    simp only [Finmap.FUNION] at h
    cases h1 : ctMap1 k with
    | none => rw [h1] at h; exact Or.inr h
    | some w => rw [h1] at h; exact Or.inl h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k v h
    rcases key k v h with h | h
    · exact a1 k v h
    · exact a2 k v h
  · intro ex tvs ts ti h
    rcases key _ _ h with h | h
    · exact b1 ex tvs ts ti h
    · exact b2 ex tvs ts ti h
  · intro cn x tvs ts ti h
    rcases key _ _ h with h | h
    · exact c1 cn x tvs ts ti h
    · exact c2 cn x tvs ts ti h
  · rintro s1 tvs1 ts1 ti s2 tvs2 ts2 ⟨h, h'⟩
    rcases key _ _ h with h | h <;> rcases key _ _ h' with h' | h'
    · exact d1 _ _ _ _ _ _ _ ⟨h, h'⟩
    · exact absurd ⟨⟨s1, by simp [Finmap.o_f, h]⟩, ⟨s2, by simp [Finmap.o_f, h']⟩⟩ (hd ti)
    · exact absurd ⟨⟨s2, by simp [Finmap.o_f, h']⟩, ⟨s1, by simp [Finmap.o_f, h]⟩⟩ (hd ti)
    · exact d2 _ _ _ _ _ _ _ ⟨h, h'⟩
/- HOL4:
Theorem ctMap_ok_lookup:
 !ctMap cn tvs ts ti tn.
  ctMap_ok ctMap ∧ (FLOOKUP ctMap tn = SOME (tvs,ts,ti))
  ⇒
  EVERY (check_freevars 0 tvs) ts
-/
theorem ctMap_ok_lookup :
    ∀ (ctMap_ : ctMap) (cn : conN) (tvs : List tvarN) (ts : List sem_t)
      (ti : type_ident) (tn : stamp),
      ctMap_ok ctMap_ ∧ Finmap.FLOOKUP ctMap_ tn = some (tvs, ts, ti) →
      EVERY (check_freevars 0 tvs) ts := by
  rintro ctMap_ cn tvs ts ti tn ⟨h1, h2⟩
  exact h1.1 tn (tvs, ts, ti) h2
/- HOL4:
Theorem type_def_to_ctMap_mem:
   !tenvT next tds tids.
    ALOOKUP (type_def_to_ctMap tenvT next tds tids) k = SOME x ∧
    LENGTH tds = LENGTH tids
    ⇒
    MEM (SND (SND x)) tids
-/
theorem type_def_to_ctMap_mem :
    ∀ (tenvT : tenv_abbrev) (next : Nat)
      (tds : List (List tvarN × mlstring × List (conN × List ast_t)))
      (tids : List type_ident) (k : stamp) (x : List tvarN × List sem_t × type_ident),
      ALOOKUP (type_def_to_ctMap tenvT next tds tids) k = some x ∧
      tds.length = tids.length →
      x.2.2 ∈ tids := by
  rintro tenvT next tds tids k ⟨tvs, ts, ti⟩ ⟨h, hl⟩
  obtain ⟨cn, i, tn, ctors, cts, h1, h2, h3, h4, h5, h6⟩ :=
    B_mem_ctMap_aux tenvT tds next tids k tvs ts ti (B_ALOOKUP_mem_aux _ _ _ h)
  exact List.mem_of_getElem? h3
/- HOL4: [local]
Theorem fupdate2_union:
  !m a1 a2. m |++ a1 |++ a2 = FEMPTY |++ a2 ⊌ (m |++ a1)
-/
theorem fupdate2_union :
    ∀ (m : Finmap stamp (List tvarN × List sem_t × type_ident))
      (a1 a2 : List (stamp × (List tvarN × List sem_t × type_ident))),
      Finmap.FUPDATE_LIST (Finmap.FUPDATE_LIST m a1) a2 =
      Finmap.FUNION (Finmap.FUPDATE_LIST Finmap.FEMPTY a2) (Finmap.FUPDATE_LIST m a1) := by
  have gen : ∀ (a2 : List (stamp × (List tvarN × List sem_t × type_ident)))
      (m' : Finmap stamp (List tvarN × List sem_t × type_ident)),
      Finmap.FUPDATE_LIST m' a2 =
        Finmap.FUNION (Finmap.FUPDATE_LIST Finmap.FEMPTY a2) m' := by
    intro a2
    induction a2 with
    | nil => intro m'; funext x; simp [Finmap.FUPDATE_LIST, Finmap.FUNION, Finmap.FEMPTY]
    | cons kv a2 ih =>
      intro m'
      have e1 : Finmap.FUPDATE_LIST m' (kv :: a2) =
          Finmap.FUPDATE_LIST (Finmap.FUPDATE m' kv) a2 := rfl
      have e2 : Finmap.FUPDATE_LIST (Finmap.FEMPTY : Finmap stamp _) (kv :: a2) =
          Finmap.FUPDATE_LIST (Finmap.FUPDATE Finmap.FEMPTY kv) a2 := rfl
      rw [e1, e2, ih (Finmap.FUPDATE m' kv), ih (Finmap.FUPDATE Finmap.FEMPTY kv)]
      funext x
      simp only [Finmap.FUNION, Finmap.FUPDATE, Finmap.FEMPTY]
      cases h : Finmap.FUPDATE_LIST Finmap.FEMPTY a2 x with
      | some w => rfl
      | none =>
        simp only
        split <;> rfl
  intro m a1 a2
  exact gen a2 _
/- HOL4:
Theorem ctMap_ok_type_defs:
   !tenvT next tds tids.
    ALL_DISTINCT tids ∧
    DISJOINT (set tids) (set prim_type_nums) ∧
    LENGTH tds = LENGTH tids ∧
    check_ctor_tenv tenvT tds ∧
    tenv_abbrev_ok tenvT
    ⇒
    ctMap_ok
      (FEMPTY |++
        REVERSE (type_def_to_ctMap tenvT next tds tids))
-/
theorem B_flookup_fupdate_list_reverse_aux {β : Type} (l : List (stamp × β)) (k : stamp) :
    Finmap.FUPDATE_LIST Finmap.FEMPTY l.reverse k = ALOOKUP l k := by
  induction l with
  | nil => simp [Finmap.FUPDATE_LIST, Finmap.FEMPTY, ALOOKUP]
  | cons a l ih =>
    obtain ⟨k', v'⟩ := a
    simp only [List.reverse_cons, Finmap.FUPDATE_LIST, List.foldl_append, List.foldl_cons,
      List.foldl_nil, Finmap.FUPDATE, ALOOKUP]
    have ih' : List.foldl Finmap.FUPDATE Finmap.FEMPTY l.reverse k = ALOOKUP l k := ih
    rw [ih']
    by_cases h : k = k'
    · simp [h]
    · have h' : ¬ (k' = k) := fun e => h e.symm
      simp [h, h']

theorem B_check_ctor_tenv_mem_aux (tenvT : tenv_abbrev) :
    ∀ (tds : List (List tvarN × mlstring × List (conN × List ast_t))),
      check_ctor_tenv tenvT tds →
      ∀ tvs tn ctors, (tvs, tn, ctors) ∈ tds → ∀ cn cts, (cn, cts) ∈ ctors →
        ∀ t, t ∈ cts → check_freevars_ast tvs t ∧ check_type_names tenvT t := by
  intro tds
  induction tds with
  | nil => intro _ tvs tn ctors h; simp at h
  | cons td tds ih =>
    obtain ⟨tvs', tn', ctors'⟩ := td
    intro h tvs tn ctors hm cn cts hc t ht
    simp only [check_ctor_tenv, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨_, _⟩, h3⟩, _⟩, h5⟩ := h
    simp at hm
    rcases hm with ⟨rfl, rfl, rfl⟩ | hm
    · simp only [List.all_eq_true] at h3
      have := h3 (cn, cts) hc
      simp at this
      exact ⟨this.1 t ht, this.2 t ht⟩
    · exact ih h5 tvs tn ctors hm cn cts hc t ht

theorem B_ctor_fv_aux (tenvT : tenv_abbrev)
    (tds : List (List tvarN × mlstring × List (conN × List ast_t)))
    (hta : tenv_abbrev_ok tenvT) (hc : check_ctor_tenv tenvT tds)
    (tvs : List tvarN) (tn : mlstring) (ctors : List (conN × List ast_t))
    (hm : (tvs, tn, ctors) ∈ tds) (cn : conN) (cts : List ast_t) (hcm : (cn, cts) ∈ ctors) :
    EVERY (check_freevars 0 tvs) (cts.map (type_name_subst tenvT)) = true := by
  simp
  intro t ht
  have := B_check_ctor_tenv_mem_aux tenvT tds hc tvs tn ctors hm cn cts hcm t ht
  exact check_freevars_type_name_subst tvs t 0 tenvT ⟨hta, this.2, this.1⟩

theorem B_all_distinct_getElem_aux {α : Type} [BEq α] [LawfulBEq α] :
    ∀ (l : List α), ALL_DISTINCT l = true → ∀ (i j : Nat) (a : α),
      l[i]? = some a → l[j]? = some a → i = j := by
  intro l
  induction l with
  | nil => intro _ i j a h; simp at h
  | cons x l ih =>
    intro hd i j a hi hj
    simp [ALL_DISTINCT] at hd
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j =>
        simp at hi hj
        subst hi
        exact absurd rfl (hd.1 _ (List.mem_of_getElem? hj))
    | succ i =>
      cases j with
      | zero =>
        simp at hi hj
        subst hj
        exact absurd rfl (hd.1 _ (List.mem_of_getElem? hi))
      | succ j =>
        simp at hi hj
        rw [ih hd.2 i j a hi hj]
theorem ctMap_ok_type_defs :
    ∀ (tenvT : tenv_abbrev) (next : Nat)
      (tds : List (List tvarN × mlstring × List (conN × List ast_t)))
      (tids : List type_ident),
      ALL_DISTINCT tids ∧
      DISJOINT (fun x => x ∈ tids) (fun x => x ∈ prim_type_nums) ∧
      tds.length = tids.length ∧
      check_ctor_tenv tenvT tds ∧
      tenv_abbrev_ok tenvT →
      ctMap_ok (Finmap.FUPDATE_LIST Finmap.FEMPTY (type_def_to_ctMap tenvT next tds tids).reverse) := by
  rintro tenvT next tds tids ⟨hd, hdisj, hl, hc, hta⟩
  have key : ∀ k tvs ts ti,
      Finmap.FUPDATE_LIST Finmap.FEMPTY (type_def_to_ctMap tenvT next tds tids).reverse k
        = some (tvs, ts, ti) →
      ∃ (cn : conN) (i : Nat) (tn : mlstring) (ctors : List (conN × List ast_t)) (cts : List ast_t),
        k = .TypeStamp cn (next + i) ∧ i < tds.length ∧ tids[i]? = some ti ∧
        (tvs, tn, ctors) ∈ tds ∧ (cn, cts) ∈ ctors ∧ ts = cts.map (type_name_subst tenvT) := by
    intro k tvs ts ti h
    rw [B_flookup_fupdate_list_reverse_aux] at h
    exact B_mem_ctMap_aux tenvT tds next tids k tvs ts ti (B_ALOOKUP_mem_aux _ _ _ h)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro k ⟨tvs, ts, ti⟩ h
    obtain ⟨cn, i, tn, ctors, cts, h1, h2, h3, h4, h5, h6⟩ := key k tvs ts ti h
    subst h6
    exact B_ctor_fv_aux tenvT tds hta hc tvs tn ctors h4 cn cts h5
  · intro ex tvs ts ti h
    obtain ⟨cn, i, tn, ctors, cts, h1, h2, h3, h4, h5, h6⟩ := key _ tvs ts ti h
    cases h1
  · intro cn x tvs ts ti h
    obtain ⟨cn', i, tn, ctors, cts, h1, h2, h3, h4, h5, h6⟩ := key _ tvs ts ti h
    intro hmem
    exact hdisj ti ⟨List.mem_of_getElem? h3, by simpa using hmem⟩
  · rintro s1 tvs1 ts1 ti s2 tvs2 ts2 ⟨h, h'⟩
    obtain ⟨cn1, i1, tn1, ctors1, cts1, a1, a2, a3, a4, a5, a6⟩ := key _ _ _ _ h
    obtain ⟨cn2, i2, tn2, ctors2, cts2, b1, b2, b3, b4, b5, b6⟩ := key _ _ _ _ h'
    have := B_all_distinct_getElem_aux tids hd i1 i2 ti a3 b3
    subst a1 b1 this
    simp [same_type]
/- HOL4:
Theorem nsLookup_add_tenvE1:
   !tenvE tenvV n tvs t tvs2.
    check_freevars tvs2 [] t ∧
    tveLookup n tvs tenvE = SOME (tvs2,t) ⇒
    nsLookup (add_tenvE tenvE tenvV) (Short n) = SOME (tvs2,t)
-/
theorem nsLookup_add_tenvE1 :
    ∀ (tenvE : tenv_val_exp) (tenvV : tenv_val) (n : mlstring) (tvs : Nat)
      (t : sem_t) (tvs2 : Nat),
      check_freevars tvs2 [] t ∧
      tveLookup n tvs tenvE = some (tvs2, t) →
      nsLookup (add_tenvE tenvE tenvV) (.Short n) = some (tvs2, t) := by
  intro tenvE tenvV n tvs t tvs2
  induction tenvE generalizing tvs with
  | Empty => rintro ⟨_, h⟩; simp [tveLookup] at h
  | Bind_tvar k e ih =>
    rintro ⟨h1, h2⟩
    simp only [tveLookup] at h2
    simp only [add_tenvE]
    exact ih (tvs + k) ⟨h1, h2⟩
  | Bind_name n' k t' e ih =>
    rintro ⟨h1, h2⟩
    simp only [add_tenvE]
    by_cases hn : n' = n
    · simp [tveLookup, hn] at h2
      obtain ⟨rfl, rfl⟩ := h2
      subst hn
      rw [BAux.ns_nsLookup_nsBind.1, nil_deBruijn_inc k tvs t' (Or.inr h1)]
    · simp [tveLookup, hn] at h2
      rw [BAux.ns_nsLookup_nsBind.2 _ _ _ _ (by intro h; cases h; exact hn rfl)]
      exact ih tvs ⟨h1, h2⟩
/- HOL4:
Theorem nsLookup_add_tenvE2:
   !tenvE tenvV n tvs t tvs2.
    tveLookup n tvs tenvE = NONE ∧
    nsLookup tenvV (Short n) = SOME (tvs2,t) ⇒
    nsLookup (add_tenvE tenvE tenvV) (Short n) = SOME (tvs2,t)
-/
theorem nsLookup_add_tenvE2 :
    ∀ (tenvE : tenv_val_exp) (tenvV : tenv_val) (n : mlstring) (tvs : Nat)
      (t : sem_t) (tvs2 : Nat),
      tveLookup n tvs tenvE = none ∧
      nsLookup tenvV (.Short n) = some (tvs2, t) →
      nsLookup (add_tenvE tenvE tenvV) (.Short n) = some (tvs2, t) := by
  intro tenvE tenvV n tvs t tvs2
  induction tenvE generalizing tvs with
  | Empty => rintro ⟨_, h⟩; simpa [add_tenvE] using h
  | Bind_tvar k e ih =>
    rintro ⟨h1, h2⟩
    simp only [tveLookup] at h1
    simp only [add_tenvE]
    exact ih (tvs + k) ⟨h1, h2⟩
  | Bind_name n' k t' e ih =>
    rintro ⟨h1, h2⟩
    simp only [add_tenvE]
    by_cases hn : n' = n
    · simp [tveLookup, hn] at h1
    · simp [tveLookup, hn] at h1
      rw [BAux.ns_nsLookup_nsBind.2 _ _ _ _ (by intro h; cases h; exact hn rfl)]
      exact ih tvs ⟨h1, h2⟩
/- HOL4:
Theorem nsLookup_add_tenvE3:
   !tenvE tenvV n t tvs2 mn.
    nsLookup tenvV (Long mn n) = SOME (tvs2,t) ⇒
    nsLookup (add_tenvE tenvE tenvV) (Long mn n) = SOME (tvs2,t)
-/
theorem nsLookup_add_tenvE3 :
    ∀ (tenvE : tenv_val_exp) (tenvV : tenv_val) (n : cml_id modN varN) (t : sem_t)
      (tvs2 : Nat) (mn : modN),
      nsLookup tenvV (.Long mn n) = some (tvs2, t) →
      nsLookup (add_tenvE tenvE tenvV) (.Long mn n) = some (tvs2, t) := by
  intro tenvE tenvV n t tvs2 mn
  induction tenvE with
  | Empty => intro h; simpa [add_tenvE] using h
  | Bind_tvar k e ih => intro h; simp only [add_tenvE]; exact ih h
  | Bind_name n' k t' e ih =>
    intro h
    simp only [add_tenvE]
    rw [BAux.ns_nsLookup_nsBind.2 _ _ _ _ (by intro h; cases h)]
    exact ih h
/- HOL4:
Theorem add_tenvE_bvl:
   !n bindings tenvE tenvV.
    add_tenvE (bind_var_list n bindings tenvE) tenvV =
    nsBindList (MAP (\(x,t). (x, (n, t))) bindings) (add_tenvE tenvE tenvV)
-/
theorem add_tenvE_bvl :
    ∀ (n : Nat) (bindings : List (mlstring × sem_t)) (tenvE : tenv_val_exp) (tenvV : tenv_val),
      add_tenvE (bind_var_list n bindings tenvE) tenvV =
      nsBindList (bindings.map (fun (x, t) => (x, (n, t)))) (add_tenvE tenvE tenvV) := by
  intro n bindings tenvE tenvV
  induction bindings with
  | nil => simp [bind_var_list, nsBindList]
  | cons a bs ih =>
    obtain ⟨x, t⟩ := a
    simp only [bind_var_list, add_tenvE, ih]
    simp [nsBindList]
/- HOL4:
Theorem type_v_freevars:
 !tvs tenvC tenvS v t. type_v tvs tenvC tenvS v t ⇒ check_freevars tvs [] t
-/
theorem type_v_freevars :
    ∀ (tvs : Nat) (tenvC : ctMap) (tenvS : tenv_store) (v_ : v) (t : sem_t),
      type_v tvs tenvC tenvS v_ t → check_freevars tvs [] t := by
  intro tvs ctMap_ tenvS v_ t h
  induction h with
  | litv_int => simp [Tint]
  | litv_char => simp [Tchar]
  | litv_str => simp [Tstring]
  | litv_word8 => simp [Tword8]
  | litv_word64 => simp [Tword64]
  | litv_float64 => simp [Tdouble]
  | conv_some tvs ctMap_ tenvS ts' tvs' vs ts ti stmp h1 h2 h3 h4 h5 ih => simp; exact h1
  | conv_none tvs ctMap_ tenvS vs ts h1 h2 ih =>
    simp [Ttup]
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have := ih i (by omega)
    simpa [hi] using this
  | closure tvs ctMap_ tenvS tenv tenvE env n e t1 t2 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 ih =>
    have hn : num_tvs (bind_tvar tvs tenvE) = tvs := by rw [bind_tvar_rewrites.2.1, h3]; simp
    have hok : tenv_val_exp_ok (bind_tvar tvs tenvE) := (bind_tvar_rewrites.2.2.2.2.2.2.1 _ _).2 h2
    have := type_e_freevars.1 _ _ _ _ h10
      ⟨by simp only [tenv_val_exp_ok, hn]; exact ⟨by simpa using h9, hok⟩, h1.1⟩
    simp only [num_tvs, hn] at this
    simp [Tfn]
    exact ⟨h9, this⟩
  | recclosure tvs ctMap_ tenvS tenv tenvE env n funs bindings t h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 ih =>
    have hn : num_tvs (bind_tvar tvs tenvE) = tvs := by rw [bind_tvar_rewrites.2.1, h3]; simp
    obtain ⟨t1, t2, rfl, hfv⟩ := type_funs_Tfn tenv _ funs bindings 0 t n ⟨h9, h10⟩
    rw [num_tvs_bind_var_list, hn] at hfv
    exact hfv
  | loc_ref tvs ctMap_ tenvS t n h1 h2 =>
    simp [Tref]
    exact check_freevars_add 0 [] t h1 tvs (by omega)
  | loc_w8array => simp [Tword8array]
  | loc_varray tvs ctMap_ tenvS t n h1 h2 =>
    simp [Tarray]
    exact check_freevars_add 0 [] t h1 tvs (by omega)
  | vectorv tvs ctMap_ tenvS t vs h1 h2 ih =>
    simp [Tvector]
    exact check_freevars_add 0 [] t h1 tvs (by omega)
/- HOL4:
Theorem type_subst:
   !tvs ctMap tenvS v t.
     type_v tvs ctMap tenvS v t ⇒
     tvs = LENGTH targs ∧
     ctMap_ok ctMap ∧
     EVERY (check_freevars tvs' []) targs ∧
     check_freevars (LENGTH targs) [] t
     ⇒
     type_v tvs' ctMap tenvS v (deBruijn_subst 0 targs t)
  (with free variables targs and tvs')
-/
theorem B_fupdate_list_reverse_eq_alist_aux {α β : Type} [BEq α] (l : List (α × β)) :
    Finmap.FUPDATE_LIST Finmap.FEMPTY l.reverse = Finmap.alist_to_fmap l := by
  funext k
  induction l with
  | nil => simp [Finmap.FUPDATE_LIST, Finmap.FEMPTY, Finmap.alist_to_fmap]
  | cons a l ih =>
    obtain ⟨k', v'⟩ := a
    simp only [List.reverse_cons, Finmap.FUPDATE_LIST, List.foldl_append, List.foldl_cons,
      List.foldl_nil, Finmap.FUPDATE, Finmap.alist_to_fmap, List.find?_cons]
    have ih' : List.foldl Finmap.FUPDATE Finmap.FEMPTY l.reverse k =
        Option.map Prod.snd (List.find? (fun p => k == p.1) l) := ih
    rw [ih']
    cases h : (k == k') <;> simp
theorem type_subst_thm :
    ∀ (targs : List sem_t) (tvs' : Nat),
    ∀ (tvs : Nat) (ctMap_ : ctMap) (tenvS : tenv_store) (v_ : v) (t : sem_t),
      type_v tvs ctMap_ tenvS v_ t →
      tvs = targs.length ∧
      ctMap_ok ctMap_ ∧
      EVERY (check_freevars tvs' []) targs ∧
      check_freevars targs.length [] t →
      type_v tvs' ctMap_ tenvS v_ (deBruijn_subst 0 targs t) := by
  intro targs tvs' tvs ctMap_ tenvS v_ t h
  induction h with
  | litv_int tvs ctMap_ tenvS n =>
    intro _; simpa [Tint, deBruijn_subst] using type_v.litv_int tvs' ctMap_ tenvS n
  | litv_char tvs ctMap_ tenvS n =>
    intro _; simpa [Tchar, deBruijn_subst] using type_v.litv_char tvs' ctMap_ tenvS n
  | litv_str tvs ctMap_ tenvS n =>
    intro _; simpa [Tstring, deBruijn_subst] using type_v.litv_str tvs' ctMap_ tenvS n
  | litv_word8 tvs ctMap_ tenvS n =>
    intro _; simpa [Tword8, deBruijn_subst] using type_v.litv_word8 tvs' ctMap_ tenvS n
  | litv_word64 tvs ctMap_ tenvS n =>
    intro _; simpa [Tword64, deBruijn_subst] using type_v.litv_word64 tvs' ctMap_ tenvS n
  | litv_float64 tvs ctMap_ tenvS n =>
    intro _; simpa [Tdouble, deBruijn_subst] using type_v.litv_float64 tvs' ctMap_ tenvS n
  | conv_some tvs ctMap_ tenvS ts' tvs'' vs ts ti stmp h1 h2 h3 h4 h5 ih =>
    rintro ⟨rfl, hok, hEV, hfvT⟩
    simp only [deBruijn_subst]
    simp only [B_fupdate_list_reverse_eq_alist_aux] at h3 h4 ih
    simp at hfvT hEV
    have hlen : vs.length = ts.length := by simpa using h3
    have hts : EVERY (check_freevars 0 tvs'') ts := ctMap_ok_lookup ctMap_ default _ _ _ _ ⟨hok, h5⟩
    simp at hts
    refine type_v.conv_some tvs' ctMap_ tenvS (ts'.map (deBruijn_subst 0 targs)) tvs'' vs ts ti stmp
      ?_ (by simpa using h2) (by simpa using hlen) ?_ h5
    · intro t' ht'
      simp at ht'
      obtain ⟨a, ha, rfl⟩ := ht'
      exact deBruijn_subst_check_freevars2 tvs' [] a targs 0 [] ⟨hfvT a ha, by simpa using hEV⟩
    · intro i hi
      have hi' : i < ts.length := by omega
      have e1 : ∀ (f : sem_t → sem_t), (ts.map f)[i]! = f (ts[i]!) :=
        fun f => BAux.EL_map f i ts hi'
      have hmem : ts[i]! ∈ ts := BAux.EL_mem i ts hi'
      have hfvi : check_freevars targs.length [] (type_subst (Finmap.alist_to_fmap (tvs''.zip ts')) ts[i]!) := by
        have := check_freevars_subst_single targs.length tvs'' ts[i]! [] ts'
          ⟨h2, check_freevars_add 0 tvs'' _ (hts _ hmem) _ (by omega), by simpa using hfvT⟩
        simpa [ZIP] using this
      have := ih i hi ⟨trivial, hok, by simpa using hEV, by rw [e1]; exact hfvi⟩
      rw [e1] at this
      rw [B_fupdate_list_reverse_eq_alist_aux, e1]
      have e2 := type_subst_deBruijn_subst_single (Finmap.alist_to_fmap (ZIP (tvs'', ts'))) ts[i]! tvs'' []
        ts' targs 0 ⟨h2, hts _ hmem, rfl⟩
      simp only [ZIP] at e2
      rw [← e2]
      exact this
  | conv_none tvs ctMap_ tenvS vs ts h1 h2 ih =>
    rintro ⟨rfl, hok, hEV, hfvT⟩
    simp only [Ttup, deBruijn_subst]
    simp [Ttup] at hfvT
    refine type_v.conv_none tvs' ctMap_ tenvS vs (ts.map (deBruijn_subst 0 targs)) (by simpa using h1) ?_
    intro i hi
    have hi' : i < ts.length := by omega
    have e1 : ∀ (f : sem_t → sem_t), (ts.map f)[i]! = f (ts[i]!) :=
      fun f => BAux.EL_map f i ts hi'
    rw [e1]
    exact ih i hi ⟨rfl, hok, hEV, hfvT _ (BAux.EL_mem i ts hi')⟩
  | closure tvs ctMap_ tenvS tenv tenvE env n e t1 t2 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 ih =>
    rintro ⟨rfl, hok, hEV, hfvT⟩
    simp [Tfn] at hfvT
    simp only [Tfn, deBruijn_subst, List.map]
    have hokE : tenv_val_exp_ok (bind_tvar targs.length tenvE) :=
      (bind_tvar_rewrites.2.2.2.2.2.2.1 _ _).2 h2
    refine type_v.closure tvs' ctMap_ tenvS tenv tenvE env n e _ _ h1 h2 h3 h4 h5 h6 h7 h8 ?_ ?_
    · exact deBruijn_subst_check_freevars2 tvs' [] t1 targs 0 [] ⟨hfvT.1, hEV⟩
    · exact type_e_subst_lem n t1 tenv tenvE e t2 targs tvs' targs
        ⟨h10, h3, h1.2.2, h1.2.1, h1.1, hokE, hEV, hfvT.1⟩
  | recclosure tvs ctMap_ tenvS tenv tenvE env n funs bindings t h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 ih =>
    rintro ⟨rfl, hok, hEV, hfvT⟩
    have hokE : tenv_val_exp_ok (bind_tvar targs.length tenvE) :=
      (bind_tvar_rewrites.2.2.2.2.2.2.1 _ _).2 h2
    have hok' := tenv_val_exp_ok_bvl_funs funs bindings tenv bindings tenv.v _ ⟨h9, hokE⟩
    have hf := (type_e_subst tenvE).2.2 tenv _ funs bindings h9 (bind_var_list 0 bindings .Empty)
      targs tvs' (targs.map (deBruijn_inc 0 (num_tvs (bind_var_list 0 bindings .Empty))))
      ⟨h3, h1.2.2, h1.2.1, h1.1, hok', hEV, by rw [db_merge_bvl]; simp [db_merge], rfl⟩
    rw [deBruijn_subst_E_bvl, db_merge_bvl, num_tvs_bind_var_list] at hf
    simp only [num_tvs, deBruijn_subst_tenvE, db_merge, Nat.add_zero, deBruijn_inc0.2] at hf
    refine type_v.recclosure tvs' ctMap_ tenvS tenv tenvE env n funs _ _ h1 h2 h3 h4 h5 h6 h7 h8 hf ?_
      h11 h12
    rw [B_ALOOKUP_map_aux, h10]
    rfl
  | loc_ref tvs ctMap_ tenvS t n h1 h2 =>
    intro _
    simp only [Tref, deBruijn_subst, List.map]
    rw [nil_deBruijn_subst 0 targs t h1]
    exact type_v.loc_ref tvs' ctMap_ tenvS t n h1 h2
  | loc_w8array tvs ctMap_ tenvS n h =>
    intro _
    simpa [Tword8array, deBruijn_subst] using type_v.loc_w8array tvs' ctMap_ tenvS n h
  | loc_varray tvs ctMap_ tenvS t n h1 h2 =>
    intro _
    simp only [Tarray, deBruijn_subst, List.map]
    rw [nil_deBruijn_subst 0 targs t h1]
    exact type_v.loc_varray tvs' ctMap_ tenvS t n h1 h2
  | vectorv tvs ctMap_ tenvS t vs h1 h2 ih =>
    rintro ⟨rfl, hok, hEV, hfvT⟩
    simp only [Tvector, deBruijn_subst, List.map]
    rw [nil_deBruijn_subst 0 targs t h1]
    refine type_v.vectorv tvs' ctMap_ tenvS t vs h1 ?_
    intro w hw
    have := ih w hw ⟨rfl, hok, hEV, check_freevars_add 0 [] t h1 _ (by omega)⟩
    rwa [nil_deBruijn_subst 0 targs t h1] at this
/- HOL4:
Theorem check_ctor_tenv_ok:
 !tenvT tds tis.
 LENGTH tds = LENGTH tis ∧
 check_ctor_tenv tenvT tds ∧
 tenv_abbrev_ok tenvT
 ⇒
 tenv_ctor_ok (build_ctor_tenv tenvT tds tis)
-/
theorem check_ctor_tenv_ok :
    ∀ (tenvT : tenv_abbrev)
      (tds : List (List tvarN × mlstring × List (conN × List ast_t)))
      (tis : List type_ident),
      tds.length = tis.length ∧
      check_ctor_tenv tenvT tds ∧
      tenv_abbrev_ok tenvT →
      tenv_ctor_ok (build_ctor_tenv tenvT tds tis) := by
  intro tenvT tds
  induction tds with
  | nil =>
    rintro tis ⟨hl, hc, hta⟩
    unfold tenv_ctor_ok
    cases tis <;> (simp only [build_ctor_tenv]; exact BAux.ns_nsAll_alist_to_ns _ _ (by simp))
  | cons td tds ih =>
    rintro tis ⟨hl, hc, hta⟩
    obtain ⟨tvs, tn, ctors⟩ := td
    cases tis with
    | nil => simp at hl
    | cons id_ ids =>
      simp only [build_ctor_tenv]
      have hc' : check_ctor_tenv tenvT tds = true := by
        simp only [check_ctor_tenv, Bool.and_eq_true] at hc
        exact hc.2
      apply tenv_ctor_ok_merge
      refine ⟨ih ids ⟨by simpa using hl, hc', hta⟩, ?_⟩
      unfold tenv_ctor_ok
      apply BAux.ns_nsAll_alist_to_ns
      rintro ⟨cn, tvs', ts', ti⟩ hp
      simp at hp
      obtain ⟨cn', cts, hm, rfl, rfl, rfl, rfl⟩ := hp
      exact B_ctor_fv_aux tenvT ((tvs, tn, ctors) :: tds) hta hc tvs tn ctors (by simp) cn' cts hm
/- HOL4:
Theorem type_d_check_uniq:
 (!check tenv d tdecs new_tenv.
  type_d check tenv d tdecs new_tenv
  ⇒
  type_d F tenv d tdecs new_tenv) ∧
 (!check tenv d tdecs new_tenv.
  type_ds check tenv d tdecs new_tenv
  ⇒
  type_ds F tenv d tdecs new_tenv)
-/
theorem type_d_check_uniq :
    (∀ (check : Bool) (tenv : type_env) (d : dec) (tdecs : Set type_ident) (new_tenv : type_env),
      type_d check tenv d tdecs new_tenv →
      type_d false tenv d tdecs new_tenv) ∧
    (∀ (check : Bool) (tenv : type_env) (d : List dec) (tdecs : Set type_ident) (new_tenv : type_env),
      type_ds check tenv d tdecs new_tenv →
      type_ds false tenv d tdecs new_tenv) := by
  have H : ∀ check : Bool,
      (∀ tenv d decls tenv', type_d check tenv d decls tenv' → type_d false tenv d decls tenv') ∧
      (∀ tenv ds decls tenv', type_ds check tenv ds decls tenv' →
        type_ds false tenv ds decls tenv') := by
    intro check
    apply BAux.type_d_ind
    case hd =>
      intro tenv d decls tenv' h hm hl
      cases h with
      | dlet_poly _ locs p e tvs t bindings a1 a2 a3 a4 a5 =>
        exact type_d.dlet_poly false _ _ _ _ _ _ _ a1 a2 a3 a4 (by intro h; cases h)
      | dlet_mono _ locs p e t bindings a1 a2 a3 a4 =>
        exact type_d.dlet_mono false _ _ _ _ _ _ (by intro h; cases h) a2 a3 a4
      | dletrec _ locs funs tvs bindings a1 a2 =>
        exact type_d.dletrec false _ _ _ _ _ a1 (by intro h; cases h)
      | dtype _ locs tdefs tids tenvT a1 a2 a3 a4 a5 =>
        exact type_d.dtype false _ _ _ _ _ a1 a2 a3 a4 a5
      | dtabbrev _ locs tvs tn t a1 a2 a3 =>
        exact type_d.dtabbrev false _ _ _ _ _ a1 a2 a3
      | dexn _ locs cn ts a1 a2 =>
        exact type_d.dexn false _ _ _ _ a1 a2
      | dmod => exact (hm _ _ rfl).elim
      | dlocal => exact (hl _ _ rfl).elim
    case dmod =>
      intro tenv mn ds decls tenv' h ih
      exact type_d.dmod false _ _ _ _ _ ih
    case dlocal =>
      intro tenv lds ds d1 t1 d2 t2 h1 h2 hdisj ih1 ih2
      exact type_d.dlocal false _ _ _ _ _ _ _ ih1 ih2 hdisj
    case nil => intro tenv; exact type_ds.nil false tenv
    case cons =>
      intro tenv d ds d1 t1 d2 t2 h1 h2 hdisj ih1 ih2
      exact type_ds.cons false _ _ _ _ _ _ _ ih1 ih2 hdisj
  exact ⟨fun check tenv d tdecs new_tenv h => (H check).1 tenv d tdecs new_tenv h,
    fun check tenv d tdecs new_tenv h => (H check).2 tenv d tdecs new_tenv h⟩
/- HOL4:
Theorem extend_dec_tenv_ok:
   !tenv tenv'. tenv_ok tenv ∧ tenv_ok tenv' ⇒ tenv_ok (extend_dec_tenv tenv tenv')
-/
theorem extend_dec_tenv_ok :
    ∀ (tenv tenv' : type_env),
      tenv_ok tenv ∧ tenv_ok tenv' → tenv_ok (extend_dec_tenv tenv tenv') := by
  rintro tenv tenv' ⟨⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩⟩
  exact ⟨BAux.ns_nsAll_nsAppend _ _ _ ⟨a1, b1⟩, BAux.ns_nsAll_nsAppend _ _ _ ⟨a2, b2⟩,
    BAux.ns_nsAll_nsAppend _ _ _ ⟨a3, b3⟩⟩
/- HOL4:
Theorem type_d_tenv_ok_helper:
  (∀check tenv d tdecs tenv'.
   type_d check tenv d tdecs tenv' ⇒
   tenv_ok tenv
   ⇒
   tenv_ok tenv') ∧
  (∀check tenv d tdecs tenv'.
   type_ds check tenv d tdecs tenv' ⇒
   tenv_ok tenv
   ⇒
   tenv_ok tenv')
-/
theorem B_val_ok_alist_aux (tvs : Nat) (bindings : List (varN × sem_t)) :
    EVERY (check_freevars tvs []) (bindings.map Prod.snd) = true →
    tenv_val_ok (alist_to_ns (tenv_add_tvs tvs bindings)) := by
  intro h
  simp at h
  unfold tenv_val_ok
  apply BAux.ns_nsAll_alist_to_ns
  rintro ⟨x, k, t⟩ hp
  simp [tenv_add_tvs] at hp
  obtain ⟨a, b, hm, rfl, rfl, rfl⟩ := hp
  exact h a b hm

theorem B_zipWith_forall_aux {α β γ : Type} (f : α → β → γ) (P : γ → Prop)
    (h : ∀ a b, P (f a b)) : ∀ (l1 : List α) (l2 : List β) (p : γ), p ∈ List.zipWith f l1 l2 → P p := by
  intro l1
  induction l1 with
  | nil => intro l2 p hp; simp at hp
  | cons a l1 ih =>
    intro l2 p hp
    cases l2 with
    | nil => simp at hp
    | cons b l2 =>
      simp at hp
      rcases hp with rfl | hp
      · exact h a b
      · exact ih l2 p hp
theorem type_d_tenv_ok_helper :
    (∀ (check : Bool) (tenv : type_env) (d : dec) (tdecs : Set type_ident) (tenv' : type_env),
      type_d check tenv d tdecs tenv' →
      tenv_ok tenv →
      tenv_ok tenv') ∧
    (∀ (check : Bool) (tenv : type_env) (d : List dec) (tdecs : Set type_ident) (tenv' : type_env),
      type_ds check tenv d tdecs tenv' →
      tenv_ok tenv →
      tenv_ok tenv') := by
  have H : ∀ check : Bool,
      (∀ tenv d decls tenv', type_d check tenv d decls tenv' → tenv_ok tenv → tenv_ok tenv') ∧
      (∀ tenv ds decls tenv', type_ds check tenv ds decls tenv' → tenv_ok tenv → tenv_ok tenv') := by
    intro check
    apply BAux.type_d_ind
    case hd =>
      intro tenv d decls tenv' h hm hl hok
      cases h with
      | dlet_poly _ locs p e tvs t bindings a1 a2 a3 a4 a5 =>
        exact ⟨B_val_ok_alist_aux tvs bindings (type_p_freevars.1 _ _ _ _ _ a3).2,
          tenv_ctor_ok_nsEmpty, tenv_abbrev_ok_nsEmpty⟩
      | dlet_mono _ locs p e t bindings a1 a2 a3 a4 =>
        exact ⟨B_val_ok_alist_aux 0 bindings (type_p_freevars.1 _ _ _ _ _ a3).2,
          tenv_ctor_ok_nsEmpty, tenv_abbrev_ok_nsEmpty⟩
      | dletrec _ locs funs tvs bindings a1 a2 =>
        have := B_type_funs_freevars_aux _ _ _ _ a1
        rw [num_tvs_bind_var_list, bind_tvar_rewrites.2.1] at this
        simp only [num_tvs, Nat.add_zero] at this
        exact ⟨B_val_ok_alist_aux tvs bindings this, tenv_ctor_ok_nsEmpty, tenv_abbrev_ok_nsEmpty⟩
      | dtype _ locs tdefs tids tenvT a1 a2 a3 a4 a5 =>
        have habb : tenv_abbrev_ok tenvT := by
          subst a5
          unfold tenv_abbrev_ok
          apply BAux.ns_nsAll_alist_to_ns
          intro p hp
          refine B_zipWith_forall_aux _ (fun p => check_freevars 0 p.2.1 p.2.2 = true) ?_ _ _ p hp
          rintro ⟨tvs, tn, ctors⟩ i
          simp
        exact ⟨tenv_val_ok_nsEmpty,
          check_ctor_tenv_ok _ _ _ ⟨a4.symm, a3, BAux.ns_nsAll_nsAppend _ _ _ ⟨habb, hok.2.2⟩⟩, habb⟩
      | dtabbrev _ locs tvs tn t a1 a2 a3 =>
        refine ⟨tenv_val_ok_nsEmpty, tenv_ctor_ok_nsEmpty, ?_⟩
        unfold tenv_abbrev_ok
        rw [BAux.ns_nsAll_nsSing]
        exact check_freevars_type_name_subst tvs t 0 tenv.t ⟨hok.2.2, a2, a1⟩
      | dexn _ locs cn ts a1 a2 =>
        refine ⟨tenv_val_ok_nsEmpty, ?_, tenv_abbrev_ok_nsEmpty⟩
        unfold tenv_ctor_ok
        rw [BAux.ns_nsAll_nsSing]
        simp
        intro t ht
        exact check_freevars_type_name_subst [] t 0 tenv.t ⟨hok.2.2, a2 t ht, a1 t ht⟩
      | dmod => exact (hm _ _ rfl).elim
      | dlocal => exact (hl _ _ rfl).elim
    case dmod =>
      intro tenv mn ds decls tenv' h ih hok
      obtain ⟨a, b, c⟩ := ih hok
      exact ⟨(BAux.ns_nsAll_nsLift _ mn _).2 a, (BAux.ns_nsAll_nsLift _ mn _).2 b, (BAux.ns_nsAll_nsLift _ mn _).2 c⟩
    case dlocal =>
      intro tenv lds ds d1 t1 d2 t2 h1 h2 hdisj ih1 ih2 hok
      exact ih2 (extend_dec_tenv_ok _ _ ⟨ih1 hok, hok⟩)
    case nil => intro tenv hok; exact tenv_ok_empty
    case cons =>
      intro tenv d ds d1 t1 d2 t2 h1 h2 hdisj ih1 ih2 hok
      have a := ih1 hok
      have b := ih2 (extend_dec_tenv_ok _ _ ⟨a, hok⟩)
      exact extend_dec_tenv_ok _ _ ⟨b, a⟩
  exact ⟨fun check tenv d tdecs tenv' h => (H check).1 tenv d tdecs tenv' h,
    fun check tenv d tdecs tenv' h => (H check).2 tenv d tdecs tenv' h⟩
/- HOL4:
Theorem type_d_tenv_ok:
  ∀check tenv d tdecs tenv'.
   type_d check tenv d tdecs tenv' ∧
   tenv_ok tenv
   ⇒
   tenv_ok (extend_dec_tenv tenv' tenv)
-/
theorem type_d_tenv_ok :
    ∀ (check : Bool) (tenv : type_env) (d : dec) (tdecs : Set type_ident) (tenv' : type_env),
      type_d check tenv d tdecs tenv' ∧
      tenv_ok tenv →
      tenv_ok (extend_dec_tenv tenv' tenv) := by
  rintro check tenv d tdecs tenv' ⟨h1, h2⟩
  exact extend_dec_tenv_ok _ _ ⟨type_d_tenv_ok_helper.1 _ _ _ _ _ h1 h2, h2⟩
/- HOL4: (commented out)
Theorem type_d_mod -/
-- type_d_mod is commented out in the HOL4 source

/- HOL4:
Theorem type_ds_empty[simp]:
  !check tenv decls r.
  type_ds check tenv [] decls r ⇔
  decls = {} ∧ r = <| v := nsEmpty; c:= nsEmpty; t := nsEmpty |>
-/
theorem type_ds_empty :
    ∀ (check : Bool) (tenv : type_env) (decls : Set type_ident) (r : type_env),
      type_ds check tenv [] decls r ↔
      decls = ∅ ∧ r = { v := nsEmpty, c := nsEmpty, t := nsEmpty } := by
  intro check tenv decls r
  constructor
  · intro h; cases h; exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩; exact type_ds.nil _ _
/- HOL4:
Theorem type_ds_sing[simp]:
  !check tenv d decls r.
  type_ds check tenv [d] decls r ⇔ type_d check tenv d decls r
-/
theorem B_set_union_empty_aux {α : Type} (s : Set α) : s ∪ ∅ = s := by
  funext x
  apply propext
  show (s x ∨ False) ↔ s x
  simp

theorem B_extend_dec_tenv_empty_aux (tenv1 : type_env) :
    extend_dec_tenv { v := nsEmpty, c := nsEmpty, t := nsEmpty } tenv1 = tenv1 := by
  cases tenv1
  simp [extend_dec_tenv, BAux.ns_nsAppend_nsEmpty]
theorem type_ds_sing :
    ∀ (check : Bool) (tenv : type_env) (d : dec) (decls : Set type_ident) (r : type_env),
      type_ds check tenv [d] decls r ↔ type_d check tenv d decls r := by
  intro check tenv d decls r
  constructor
  · intro h
    cases h with
    | cons _ _ _ decls1 tenv1 decls2 tenv2 h1 h2 h3 =>
      cases h2
      rw [B_set_union_empty_aux, B_extend_dec_tenv_empty_aux]
      exact h1
  · intro h
    have := type_ds.cons check tenv d [] decls r ∅ { v := nsEmpty, c := nsEmpty, t := nsEmpty } h
      (type_ds.nil _ _) (by intro x hx; exact hx.2)
    rw [B_set_union_empty_aux, B_extend_dec_tenv_empty_aux] at this
    exact this
/- HOL4: (commented out)
Theorem type_ds_mod -/
-- type_ds_mod is commented out in the HOL4 source

/- HOL4: (commented out)
Theorem type_specs_no_mod -/
-- type_specs_no_mod is commented out in the HOL4 source

/- HOL4: (commented out)
Theorem type_prog_empty -/
-- type_prog_empty is commented out in the HOL4 source

/- HOL4: (commented out)
Theorem type_prog_sing -/
-- type_prog_sing is commented out in the HOL4 source

/- HOL4: (commented out, tenv_names definition and theorems below are from commented section)
Theorem lookup_tenv_names:
   ∀tenv n inc x. lookup_tenv_val n inc tenv = SOME x ⇒ n ∈ tenv_names tenv
  (uses tveLookup in our translation)
-/
theorem lookup_tenv_names :
    ∀ (tenvE : tenv_val_exp) (n : mlstring) (inc : Nat) (x : Nat × sem_t),
      tveLookup n inc tenvE = some x → n ∈ tenv_names tenvE := by
  intro tenvE n
  induction tenvE with
  | Empty => intro inc x h; simp [tveLookup] at h
  | Bind_tvar k e ih =>
    intro inc x h
    simp only [tveLookup] at h
    exact ih _ x h
  | Bind_name n' k t e ih =>
    intro inc x h
    by_cases hn : n' = n
    · exact Or.inl (Or.inl hn.symm)
    · simp [tveLookup, hn] at h
      exact Or.inr (ih inc x h)
/- HOL4: (commented out)
Theorem tenv_names_bind_var_list:
   ∀n l1 l2. tenv_names (bind_var_list n l1 l2) = set (MAP FST l1) ∪ tenv_names l2
-/
theorem tenv_names_bind_var_list :
    ∀ (n : Nat) (l1 : List (mlstring × sem_t)) (l2 : tenv_val_exp),
      tenv_names (bind_var_list n l1 l2) = Set.union (fun x => x ∈ l1.map Prod.fst) (tenv_names l2) := by
  intro n l1 l2
  induction l1 with
  | nil =>
    funext x
    apply propext
    show tenv_names l2 x ↔ (x ∈ ([] : List mlstring) ∨ tenv_names l2 x)
    simp
  | cons a l1 ih =>
    obtain ⟨y, t⟩ := a
    funext x
    apply propext
    show ((x = y ∨ False) ∨ tenv_names (bind_var_list n l1 l2) x) ↔
      (x ∈ (y :: l1.map Prod.fst) ∨ tenv_names l2 x)
    rw [ih]
    show ((x = y ∨ False) ∨ (x ∈ l1.map Prod.fst ∨ tenv_names l2 x)) ↔
      (x ∈ (y :: l1.map Prod.fst) ∨ tenv_names l2 x)
    simp [or_assoc]
/- HOL4: (commented out, bind_var_list2 not available in Lean)
Theorem tenv_names_bind_var_list2:
   ∀l1 tenv. tenv_names (bind_var_list2 l1 tenv) = set (MAP FST l1) ∪ tenv_names tenv
  Note: bind_var_list2 is not defined in the Lean translation.
-/
-- tenv_names_bind_var_list2 is not translatable (bind_var_list2 not available)

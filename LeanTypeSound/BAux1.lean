/-
  Helper lemmas for TypeSysProps (prover B).
-/
import LeanTypeSound.HOL4Prelude
import LeanTypeSound.Ast
import LeanTypeSound.Namespace
import LeanTypeSound.TypeSystem
import LeanTypeSound.TypeSoundInvariants
import LeanTypeSound.NamespaceProps

open HOL4

namespace BAux

theorem sem_t_ind {P : sem_t → Prop}
    (hvar : ∀ tv, P (.Tvar tv)) (hdb : ∀ n, P (.Tvar_db n))
    (happ : ∀ ts tn, (∀ t, t ∈ ts → P t) → P (.Tapp ts tn)) : ∀ t, P t := by
  intro t
  exact sem_t.rec (motive_1 := P) (motive_2 := fun ts => ∀ t, t ∈ ts → P t) hvar hdb
    (fun ts tn ih => happ ts tn ih) (by simp)
    (by
      intro h tl ih1 ih2 t ht
      simp at ht
      rcases ht with rfl | ht
      · exact ih1
      · exact ih2 _ ht) t

theorem check_freevars_Tvar (d : Nat) (tvs : List mlstring) (tv : tvarN) :
    check_freevars d tvs (.Tvar tv) = tvs.any (· == tv) := by
  rw [check_freevars]

theorem check_freevars_Tvar_db (d : Nat) (tvs : List mlstring) (n : Nat) :
    check_freevars d tvs (.Tvar_db n) = decide (n < d) := by
  rw [check_freevars]

theorem check_freevars_Tapp (d : Nat) (tvs : List mlstring) (ts : List sem_t) (tn : type_ident) :
    check_freevars d tvs (.Tapp ts tn) = ts.all (check_freevars d tvs) := by
  rw [check_freevars]
  simp [List.all_eq]

theorem EVERY_eq {α : Type} (P : α → Bool) (l : List α) : EVERY P l = l.all P := rfl

theorem flookup_zip_mem (tvs : List mlstring) (ts : List sem_t) (x : mlstring)
    (hl : tvs.length = ts.length) (hx : x ∈ tvs) :
    ∃ t, t ∈ ts ∧ Finmap.FLOOKUP (Finmap.alist_to_fmap (ZIP (tvs, ts))) x = some t := by
  induction tvs generalizing ts with
  | nil => simp at hx
  | cons a tvs ih =>
    cases ts with
    | nil => simp at hl
    | cons b ts =>
      simp at hl
      by_cases hxa : x = a
      · subst hxa
        exact ⟨b, by simp, by simp [Finmap.FLOOKUP, Finmap.alist_to_fmap, ZIP]⟩
      · simp [hxa] at hx
        obtain ⟨t, hm, hf⟩ := ih ts hl hx
        refine ⟨t, by simp [hm], ?_⟩
        simp [Finmap.FLOOKUP, Finmap.alist_to_fmap, ZIP, hxa] at hf ⊢
        exact hf

theorem flookup_zip_map (f : sem_t → sem_t) (tvs : List mlstring) (ts : List sem_t) (x : mlstring) :
    Finmap.FLOOKUP (Finmap.alist_to_fmap (ZIP (tvs, ts.map f))) x =
    (Finmap.FLOOKUP (Finmap.alist_to_fmap (ZIP (tvs, ts))) x).map f := by
  induction tvs generalizing ts with
  | nil => simp [Finmap.FLOOKUP, Finmap.alist_to_fmap, ZIP]
  | cons a tvs ih =>
    cases ts with
    | nil => simp [Finmap.FLOOKUP, Finmap.alist_to_fmap, ZIP]
    | cons b ts =>
      have := ih ts
      simp [Finmap.FLOOKUP, Finmap.alist_to_fmap, ZIP] at this ⊢
      by_cases hxa : x = a
      · simp [hxa]
      · simp [hxa, this]

theorem map_eq_self {α : Type} (f : α → α) (l : List α) (h : ∀ x, x ∈ l → f x = x) :
    l.map f = l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp at h ⊢
    exact ⟨h.1, ih (fun x hx => h.2 x hx)⟩

theorem EL_eq {α : Type} [Inhabited α] (n : Nat) (l : List α) (h : n < l.length) :
    EL n l = l[n] := by
  simp [EL, h]

theorem EL_mem {α : Type} [Inhabited α] (n : Nat) (l : List α) (h : n < l.length) :
    EL n l ∈ l := by
  rw [EL_eq n l h]; exact List.getElem_mem h

theorem EL_map {α β : Type} [Inhabited α] [Inhabited β] (f : α → β) (n : Nat) (l : List α)
    (h : n < l.length) : EL n (l.map f) = f (EL n l) := by
  rw [EL_eq n l h, EL_eq n (l.map f) (by simpa using h)]; simp

theorem inc_db_lt (skip n m : Nat) (h : m < skip) :
    deBruijn_inc skip n (.Tvar_db m) = .Tvar_db m := by
  simp [deBruijn_inc, h]

theorem inc_db_ge (skip n m : Nat) (h : skip ≤ m) :
    deBruijn_inc skip n (.Tvar_db m) = .Tvar_db (m + n) := by
  simp [deBruijn_inc]; omega

theorem subst_db_lt (skip : Nat) (ts : List sem_t) (n : Nat) (h : n < skip) :
    deBruijn_subst skip ts (.Tvar_db n) = .Tvar_db n := by
  simp [deBruijn_subst, h]

theorem subst_db_mid (skip : Nat) (ts : List sem_t) (n : Nat) (h1 : skip ≤ n)
    (h2 : n < ts.length + skip) :
    deBruijn_subst skip ts (.Tvar_db n) = EL (n - skip) ts := by
  simp [deBruijn_subst, h2]; omega

theorem subst_db_ge (skip : Nat) (ts : List sem_t) (n : Nat) (h : ts.length + skip ≤ n) :
    deBruijn_subst skip ts (.Tvar_db n) = .Tvar_db (n - ts.length) := by
  simp [deBruijn_subst]
  have h1 : ¬ (n < skip) := by omega
  have h2 : ¬ (n < ts.length + skip) := by omega
  simp [h1, h2]

theorem ast_t_ind {P : ast_t → Prop}
    (hvar : ∀ tv, P (.Atvar tv))
    (hfun : ∀ t1 t2, P t1 → P t2 → P (.Atfun t1 t2))
    (htup : ∀ ts, (∀ t, t ∈ ts → P t) → P (.Attup ts))
    (happ : ∀ ts tn, (∀ t, t ∈ ts → P t) → P (.Atapp ts tn)) : ∀ t, P t := by
  intro t
  exact ast_t.rec (motive_1 := P) (motive_2 := fun ts => ∀ t, t ∈ ts → P t) hvar hfun
    (fun ts ih => htup ts ih) (fun ts tn ih => happ ts tn ih) (by simp)
    (by
      intro h tl ih1 ih2 t ht
      simp at ht
      rcases ht with rfl | ht
      · exact ih1
      · exact ih2 _ ht) t

theorem check_freevars_ast_Atvar (tvs : List mlstring) (tv : tvarN) :
    check_freevars_ast tvs (.Atvar tv) = tvs.any (· == tv) := by
  rw [check_freevars_ast]

theorem check_freevars_ast_Attup (tvs : List mlstring) (ts : List ast_t) :
    check_freevars_ast tvs (.Attup ts) = ts.all (check_freevars_ast tvs) := by
  rw [check_freevars_ast]; simp [List.all_eq]

theorem check_freevars_ast_Atfun (tvs : List mlstring) (t1 t2 : ast_t) :
    check_freevars_ast tvs (.Atfun t1 t2) =
      (check_freevars_ast tvs t1 && check_freevars_ast tvs t2) := by
  rw [check_freevars_ast]

theorem check_freevars_ast_Atapp (tvs : List mlstring) (ts : List ast_t) (tn : cml_id modN typeN) :
    check_freevars_ast tvs (.Atapp ts tn) = ts.all (check_freevars_ast tvs) := by
  rw [check_freevars_ast]; simp [List.all_eq]

theorem check_type_names_Atvar (tenvT : tenv_abbrev) (tv : tvarN) :
    check_type_names tenvT (.Atvar tv) = true := by
  rw [check_type_names]

theorem check_type_names_Attup (tenvT : tenv_abbrev) (ts : List ast_t) :
    check_type_names tenvT (.Attup ts) = ts.all (check_type_names tenvT) := by
  rw [check_type_names]; simp [List.all_eq]

theorem check_type_names_Atfun (tenvT : tenv_abbrev) (t1 t2 : ast_t) :
    check_type_names tenvT (.Atfun t1 t2) =
      (check_type_names tenvT t1 && check_type_names tenvT t2) := by
  rw [check_type_names]

theorem check_type_names_Atapp (tenvT : tenv_abbrev) (ts : List ast_t) (tn : cml_id modN typeN) :
    check_type_names tenvT (.Atapp ts tn) = true ↔
      ((∃ tvs t, nsLookup tenvT tn = some (tvs, t) ∧ tvs.length = ts.length) ∧
        ∀ a, a ∈ ts → check_type_names tenvT a = true) := by
  rw [check_type_names]
  cases h : nsLookup tenvT tn with
  | none => simp
  | some p =>
    obtain ⟨tvs, t⟩ := p
    simp [List.all_eq]

-- Namespace facts (proved here directly so that TypeSysProps does not depend on
-- the unproved theorem stubs of NamespaceProps).

theorem ns_ALOOKUP_append {α β : Type} [BEq α] (l1 l2 : List (α × β)) (k : α) :
    ALOOKUP (l1 ++ l2) k = (match ALOOKUP l1 k with | some v => some v | none => ALOOKUP l2 k) := by
  induction l1 with
  | nil => simp [ALOOKUP]
  | cons a l1 ih =>
    obtain ⟨k', v'⟩ := a
    simp only [List.cons_append, ALOOKUP]
    split
    · rfl
    · exact ih

theorem ns_ALOOKUP_mem {α β : Type} [BEq α] [LawfulBEq α] (l : List (α × β)) (k : α) (v : β) :
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

theorem ns_nsAppend_assoc {m n v : Type} (e1 e2 e3 : «namespace» m n v) :
    nsAppend e1 (nsAppend e2 e3) = nsAppend (nsAppend e1 e2) e3 := by
  cases e1; cases e2; cases e3
  simp [nsAppend, List.append_assoc]

theorem ns_nsAppend_nsEmpty {m n v : Type} (env : «namespace» m n v) :
    nsAppend env nsEmpty = env ∧ nsAppend nsEmpty env = env := by
  cases env
  simp [nsAppend, nsEmpty]

theorem ns_nsLookup_nsEmpty {m n v : Type} [BEq m] [BEq n] (id : cml_id m n) :
    nsLookup (nsEmpty : «namespace» m n v) id = none := by
  cases id <;> simp [nsEmpty, nsLookup, ALOOKUP]

theorem ns_nsAll_nsEmpty {m n v : Type} [BEq m] [BEq n] (f : cml_id m n → v → Prop) :
    nsAll f nsEmpty := by
  intro id val h
  rw [ns_nsLookup_nsEmpty] at h
  cases h

theorem ns_nsLookup_nsAppend_some {m n v : Type} [BEq m] [BEq n]
    (e1 e2 : «namespace» m n v) (id : cml_id m n) (val : v) :
    nsLookup (nsAppend e1 e2) id = some val →
    nsLookup e1 id = some val ∨ nsLookup e2 id = some val := by
  cases e1 with
  | Bind v1 m1 =>
  cases e2 with
  | Bind v2 m2 =>
  cases id with
  | Short x =>
    simp only [nsAppend, nsLookup, ns_ALOOKUP_append]
    cases ALOOKUP v1 x with
    | none => intro h; exact Or.inr h
    | some w => intro h; exact Or.inl h
  | Long mn id' =>
    simp only [nsAppend, nsLookup, ns_ALOOKUP_append]
    cases ALOOKUP m1 mn with
    | none => intro h; exact Or.inr h
    | some w => intro h; exact Or.inl h

theorem ns_nsAll_nsAppend {m n v : Type} [BEq m] [BEq n]
    (f : cml_id m n → v → Prop) (e1 e2 : «namespace» m n v) :
    nsAll f e1 ∧ nsAll f e2 → nsAll f (nsAppend e1 e2) := by
  rintro ⟨h1, h2⟩ id val h
  rcases ns_nsLookup_nsAppend_some e1 e2 id val h with h | h
  · exact h1 id val h
  · exact h2 id val h

theorem ns_nsAll_alist_to_ns {m n v : Type} [BEq m] [BEq n] [LawfulBEq n]
    (R : cml_id m n → v → Prop) (l : List (n × v)) :
    (∀ (p : n × v), p ∈ l → R (cml_id.Short p.1) p.2) →
      nsAll R (alist_to_ns l : «namespace» m n v) := by
  intro h id val hl
  cases id with
  | Short x =>
    simp only [alist_to_ns, nsLookup] at hl
    exact h (x, val) (ns_ALOOKUP_mem _ _ _ hl)
  | Long mn id' => simp [alist_to_ns, nsLookup, ALOOKUP] at hl

theorem ns_nsAll_nsSing {m n v : Type} [BEq m] [BEq n] [LawfulBEq n]
    (R : cml_id m n → v → Prop) (n_ : n) (val_ : v) :
    nsAll R (nsSing n_ val_ : «namespace» m n v) ↔ R (cml_id.Short n_) val_ := by
  constructor
  · intro h
    exact h (cml_id.Short n_) val_ (by simp [nsSing, nsLookup, ALOOKUP])
  · intro h id val hl
    cases id with
    | Short x =>
      simp only [nsSing, nsLookup, ALOOKUP] at hl
      by_cases hx : n_ = x
      · subst hx
        simp at hl
        subst hl
        exact h
      · simp [hx] at hl
    | Long mn id' => simp [nsSing, nsLookup, ALOOKUP] at hl

theorem ns_nsAll_nsLift {m n v : Type} [BEq m] [LawfulBEq m] [BEq n]
    (R : cml_id m n → v → Prop) (mn : m) (e : «namespace» m n v) :
    nsAll R (nsLift mn e) ↔ nsAll (fun (id_ : cml_id m n) => R (cml_id.Long mn id_)) e := by
  constructor
  · intro h id val hl
    exact h (cml_id.Long mn id) val (by simp [nsLift, nsLookup, ALOOKUP, hl])
  · intro h id val hl
    cases id with
    | Short x => simp [nsLift, nsLookup, ALOOKUP] at hl
    | Long mn' id' =>
      simp only [nsLift, nsLookup, ALOOKUP] at hl
      by_cases hx : mn = mn'
      · subst hx
        simp at hl
        exact h id' val hl
      · simp [hx] at hl

theorem ns_nsLookup_nsBind {m n v : Type} [BEq m] [BEq n] [LawfulBEq n] :
    (∀ (n_ : n) (val_ : v) (e : «namespace» m n v),
      nsLookup (nsBind n_ val_ e) (cml_id.Short n_) = some val_) ∧
    (∀ (id_ : cml_id m n) (n_ : n) (val_ : v) (e : «namespace» m n v),
      id_ ≠ cml_id.Short n_ → nsLookup (nsBind n_ val_ e) id_ = nsLookup e id_) := by
  constructor
  · intro n_ val_ e
    cases e
    simp [nsBind, nsLookup, ALOOKUP]
  · intro id_ n_ val_ e hne
    cases e
    cases id_ with
    | Short x =>
      have hx : ¬ (n_ = x) := by intro h; subst h; exact hne rfl
      simp [nsBind, nsLookup, ALOOKUP, hx]
    | Long mn id' => simp [nsBind, nsLookup]

end BAux

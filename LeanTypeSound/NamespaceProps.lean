/-
  Translation of namespacePropsScript.sml
  Proofs about the namespace datatype.
-/
import LeanTypeSound.HOL4Prelude
import LeanTypeSound.Ast
import LeanTypeSound.Namespace

open HOL4

-- ============================================================
-- Definitions
-- ============================================================

/- HOL4:
Definition alist_rel_restr_def:
  (alist_rel_restr R l1 l2 [] ⇔ T) ∧
  (alist_rel_restr R l1 l2 (k1::keys) ⇔
    case ALOOKUP l1 k1 of
    | NONE => F
    | SOME v1 =>
      case ALOOKUP l2 k1 of
      | NONE => F
      | SOME v2 => R k1 v1 v2 ∧ alist_rel_restr R l1 l2 keys)
End
-/
def alist_rel_restr {k v1 v2 : Type} [BEq k]
    (R : k → v1 → v2 → Prop) (l1 : List (k × v1)) (l2 : List (k × v2)) :
    List k → Prop
  | [] => True
  | k1 :: keys =>
    match ALOOKUP l1 k1 with
    | none => False
    | some val1 =>
      match ALOOKUP l2 k1 with
      | none => False
      | some val2 => R k1 val1 val2 ∧ alist_rel_restr R l1 l2 keys

/- HOL4:
Definition alistSub_def:
  alistSub R e1 e2 ⇔ alist_rel_restr R e1 e2 (MAP FST e1)
End
-/
def alistSub {k v1 v2 : Type} [BEq k]
    (R : k → v1 → v2 → Prop) (e1 : List (k × v1)) (e2 : List (k × v2)) : Prop :=
  alist_rel_restr R e1 e2 (e1.map Prod.fst)

/- HOL4:
Definition nsSub_compute_def:
  nsSub_compute path R (Bind e1V e1M) (Bind e2V e2M) ⇔
    alistSub (λk v1 v2. R (mk_id (REVERSE path) k) v1 v2) e1V e2V ∧
    alistSub (λk v1 v2. nsSub_compute (k::path) R v1 v2) e1M e2M
End
-/
def nsSub_compute {m n v1 v2 : Type} [BEq m] [BEq n]
    (path : List m) (R : cml_id m n → v1 → v2 → Prop) :
    «namespace» m n v1 → «namespace» m n v2 → Prop
  | .Bind e1V e1M, .Bind e2V e2M =>
    alistSub (fun k val1 val2 => R (mk_id path.reverse k) val1 val2) e1V e2V ∧
    alistSub (fun k val1 val2 =>
      if sizeOf val1 < sizeOf («namespace».Bind e1V e1M) then
        nsSub_compute (k :: path) R val1 val2
      else False) e1M e2M
  termination_by e1 => sizeOf e1
  decreasing_by assumption

-- ============================================================
-- Theorem stubs
-- ============================================================

/- HOL4: Theorem mk_id_thm: !id. mk_id (id_to_mods id) (id_to_n id) = id -/
theorem mk_id_thm {m n : Type} :
    ∀ (id : cml_id m n), mk_id (id_to_mods id) (id_to_n id) = id := by
  intro id
  induction id with
  | Short x => rfl
  | Long mn i ih => simp [id_to_mods, id_to_n, mk_id, ih]
/- HOL4: Theorem mk_id_surj: !id. ?p n. id = mk_id p n -/
theorem mk_id_surj {m n : Type} :
    ∀ (id : cml_id m n), ∃ (p : List m) (n_ : n), id = mk_id p n_ := fun id => ⟨id_to_mods id, id_to_n id, (mk_id_thm id).symm⟩
/- HOL4: Theorem nsSub_mono[mono] -/
theorem nsSub_mono {m n v1 v2 : Type} [BEq m] [LawfulBEq m] [BEq n] [LawfulBEq n]
    {R1 R2 : cml_id m n → v1 → v2 → Prop}
    {e1 : «namespace» m n v1} {e2 : «namespace» m n v2} :
    (∀ (x : cml_id m n) (y : v1) (z : v2), R1 x y z → R2 x y z) →
    (nsSub R1 e1 e2 → nsSub R2 e1 e2) := by
  intro h ⟨h1, h2⟩
  refine ⟨fun id v hv => ?_, h2⟩
  obtain ⟨v2, hv2, hr⟩ := h1 id v hv
  exact ⟨v2, hv2, h _ _ _ hr⟩
/- HOL4: Theorem nsAll2_mono[mono] -/
theorem nsAll2_mono {m n v1 v2 : Type} [BEq m] [LawfulBEq m] [BEq n] [LawfulBEq n]
    {R1 R2 : cml_id m n → v1 → v2 → Prop}
    {e1 : «namespace» m n v1} {e2 : «namespace» m n v2} :
    (∀ (x : cml_id m n) (y : v1) (z : v2), R1 x y z → R2 x y z) →
    nsAll2 R1 e1 e2 → nsAll2 R2 e1 e2 := by
  intro h ⟨h1, h2⟩
  exact ⟨nsSub_mono h h1, nsSub_mono (fun x y z => h x z y) h2⟩
/- HOL4: Theorem nsLookup_nsEmpty[simp] -/
theorem nsLookup_nsEmpty {m n v : Type} [BEq m] [LawfulBEq m] [BEq n] [LawfulBEq n] :
    ∀ (id : cml_id m n), nsLookup (nsEmpty : «namespace» m n v) id = none := by
  intro id; cases id <;> simp [nsEmpty, nsLookup, ALOOKUP]
/- HOL4: Theorem nsLookupMod_nsEmpty[simp] -/
theorem nsLookupMod_nsEmpty {m n v : Type} [BEq m] [LawfulBEq m] :
    ∀ (x : m) (y : List m), nsLookupMod (nsEmpty : «namespace» m n v) (x :: y) = none := by
  intro x y; simp [nsEmpty, nsLookupMod, ALOOKUP]
/- HOL4: Theorem nsAppend_nsEmpty[simp] -/
theorem nsAppend_nsEmpty {m n v : Type} :
    ∀ (env : «namespace» m n v),
      nsAppend env nsEmpty = env ∧ nsAppend nsEmpty env = env := by
  intro env; cases env; simp [nsAppend, nsEmpty]
/- HOL4: Theorem alist_to_ns_nil[simp] -/
theorem alist_to_ns_nil {m n v : Type} :
    (alist_to_ns [] : «namespace» m n v) = nsEmpty := rfl
/- HOL4: Theorem nsSub_nsEmpty[simp] -/
theorem nsSub_nsEmpty {m n v1 v2 : Type} [BEq m] [LawfulBEq m] [BEq n] [LawfulBEq n] :
    ∀ (r : cml_id m n → v1 → v2 → Prop) (env : «namespace» m n v2),
      nsSub r (nsEmpty : «namespace» m n v1) env := by
  intro r env
  refine ⟨fun id v hv => ?_, fun path hp => ?_⟩
  · rw [nsLookup_nsEmpty] at hv; cases hv
  · cases path with
    | nil => cases env; simp [nsLookupMod] at hp
    | cons x y => exact nsLookupMod_nsEmpty x y
/- HOL4: Theorem nsAll_nsEmpty[simp] -/
theorem nsAll_nsEmpty {m n v : Type} [BEq m] [LawfulBEq m] [BEq n] [LawfulBEq n] :
    ∀ (f : cml_id m n → v → Prop), nsAll f nsEmpty := by
  intro f id v hv; rw [nsLookup_nsEmpty] at hv; cases hv
/- HOL4: Theorem nsAll2_nsEmpty[simp] -/
theorem nsAll2_nsEmpty {m n v1 v2 : Type} [BEq m] [LawfulBEq m] [BEq n] [LawfulBEq n] :
    ∀ (f : cml_id m n → v1 → v2 → Prop),
      nsAll2 f (nsEmpty : «namespace» m n v1) (nsEmpty : «namespace» m n v2) := fun f => ⟨nsSub_nsEmpty _ _, nsSub_nsEmpty _ _⟩
/- HOL4: Theorem alist_to_ns_cons[simp] -/
theorem alist_to_ns_cons {m n v : Type} :
    ∀ (k : n) (val_ : v) (l : List (n × v)),
      (alist_to_ns ((k, val_) :: l) : «namespace» m n v) = nsBind k val_ (alist_to_ns l) := fun _ _ _ => rfl
/- HOL4: Theorem nsAppend_nsBind[simp] -/
theorem nsAppend_nsBind {m n v : Type} :
    ∀ (k : n) (val_ : v) (e1 e2 : «namespace» m n v),
      nsAppend (nsBind k val_ e1) e2 = nsBind k val_ (nsAppend e1 e2) := by
  intro k v e1 e2; cases e1; cases e2; rfl
/- HOL4: Theorem nsAppend_assoc[simp] -/
theorem nsAppend_assoc {m n v : Type} :
    ∀ (e1 e2 e3 : «namespace» m n v),
      nsAppend e1 (nsAppend e2 e3) = nsAppend (nsAppend e1 e2) e3 := by
  intro e1 e2 e3; cases e1; cases e2; cases e3; simp [nsAppend]
/- HOL4: Theorem nsLookup_nsBind[simp] -/
theorem nsLookup_nsBind {m n v : Type} [BEq m] [LawfulBEq m] [BEq n] [LawfulBEq n] :
    (∀ (n_ : n) (val_ : v) (e : «namespace» m n v),
      nsLookup (nsBind n_ val_ e) (cml_id.Short n_) = some val_) ∧
    (∀ (id_ : cml_id m n) (n_ : n) (val_ : v) (e : «namespace» m n v),
      id_ ≠ cml_id.Short n_ → nsLookup (nsBind n_ val_ e) id_ = nsLookup e id_) := by
  constructor
  · intro n_ v e; cases e; simp [nsBind, nsLookup, ALOOKUP]
  · intro id n_ v e hne; cases e
    cases id with
    | Short x =>
      have : ¬ (n_ = x) := by rintro rfl; exact hne rfl
      simp [nsBind, nsLookup, ALOOKUP, this]
    | Long mn i => simp [nsBind, nsLookup]
/- HOL4: Theorem nsAppend_nsSing[simp] -/
theorem nsAppend_nsSing {m n v : Type} :
    ∀ (n_ : n) (x : v) (e : «namespace» m n v),
      nsAppend (nsSing n_ x) e = nsBind n_ x e := by
  intro n_ x e; cases e; rfl
/- HOL4: Theorem nsLookup_nsSing[simp] -/
theorem nsLookup_nsSing {m n v : Type} [BEq m] [LawfulBEq m] [BEq n] [LawfulBEq n] :
    ∀ (n_ : n) (val_ : v) (id_ : cml_id m n),
      nsLookup (nsSing n_ val_ : «namespace» m n v) id_ =
        if id_ == cml_id.Short n_ then some val_ else none := by
  intro n_ v id
  cases id with
  | Short x =>
    by_cases h : n_ = x
    · subst h; simp [nsSing, nsLookup, ALOOKUP]
    · have h' : ¬ (x = n_) := fun e => h e.symm
      simp [nsSing, nsLookup, ALOOKUP, h, h']
  | Long mn i => simp [nsSing, nsLookup, ALOOKUP]
/- HOL4: Theorem nsAll_nsSing[simp] -/
theorem nsAll_nsSing {m n v : Type} [BEq m] [LawfulBEq m] [BEq n] [LawfulBEq n] :
    ∀ (R : cml_id m n → v → Prop) (n_ : n) (val_ : v),
      nsAll R (nsSing n_ val_ : «namespace» m n v) ↔ R (cml_id.Short n_) val_ := by
  intro R n_ v
  constructor
  · intro h; exact h _ _ (by simp [nsLookup_nsSing])
  · intro h id v' hv
    rw [nsLookup_nsSing] at hv
    by_cases he : id = cml_id.Short n_
    · subst he; simp at hv; subst hv; exact h
    · simp [he] at hv
theorem ns_nsLookupMod_nsSing {m n v : Type} [BEq m] [LawfulBEq m] (n_ : n) (x : v) (path : List m) :
    nsLookupMod (nsSing n_ x : «namespace» m n v) path = none ↔ path ≠ [] := by
  cases path <;> simp [nsSing, nsLookupMod, ALOOKUP]

/- HOL4: Theorem nsAll2_nsSing[simp] -/
theorem nsAll2_nsSing {m n v1 v2 : Type} [BEq m] [LawfulBEq m] [BEq n] [LawfulBEq n] :
    ∀ (R : cml_id m n → v1 → v2 → Prop) (n1 : n) (v1_ : v1) (n2 : n) (v2_ : v2),
      nsAll2 R (nsSing n1 v1_ : «namespace» m n v1) (nsSing n2 v2_ : «namespace» m n v2) ↔
        n1 = n2 ∧ R (cml_id.Short n1) v1_ v2_ := by
  intro R n1 v1_ n2 v2_
  constructor
  · rintro ⟨⟨h1, -⟩, -⟩
    obtain ⟨v2', hv, hr⟩ := h1 (cml_id.Short n1) v1_ (by simp [nsLookup_nsSing])
    rw [nsLookup_nsSing] at hv
    by_cases he : n1 = n2
    · subst he; simp at hv; subst hv; exact ⟨rfl, hr⟩
    · simp [he] at hv
  · rintro ⟨rfl, hr⟩
    refine ⟨⟨fun id v hv => ?_, fun path hp => ?_⟩, ⟨fun id v hv => ?_, fun path hp => ?_⟩⟩
    · rw [nsLookup_nsSing] at hv ⊢
      by_cases he : id = cml_id.Short n1
      · subst he; simp at hv; subst hv; exact ⟨v2_, by simp, hr⟩
      · simp [he] at hv
    · rw [ns_nsLookupMod_nsSing] at hp ⊢; exact hp
    · rw [nsLookup_nsSing] at hv ⊢
      by_cases he : id = cml_id.Short n1
      · subst he; simp at hv; subst hv; exact ⟨v1_, by simp, hr⟩
      · simp [he] at hv
    · rw [ns_nsLookupMod_nsSing] at hp ⊢; exact hp
/- HOL4: Theorem nsBind_11[simp] -/
theorem nsBind_11 {m n v : Type} :
    ∀ (x : n) (y : v) (ns : «namespace» m n v) (x' : n) (y' : v) (ns' : «namespace» m n v),
      nsBind x y ns = nsBind x' y' ns' ↔ x = x' ∧ y = y' ∧ ns = ns' := by
  intro x y ns x' y' ns'; cases ns; cases ns'; simp [nsBind, and_assoc]
/- HOL4: Theorem alist_to_ns_11[simp] -/
theorem alist_to_ns_11 {m n v : Type} :
    ∀ (l1 l2 : List (n × v)),
      (alist_to_ns l1 : «namespace» m n v) = alist_to_ns l2 ↔ l1 = l2 := by
  intro l1 l2; simp [alist_to_ns]
/- HOL4: Theorem nsLookup_nsLift -/
theorem nsLookup_nsLift {m n v : Type} [BEq m] [LawfulBEq m] [BEq n] [LawfulBEq n] :
    ∀ (mn : m) (e : «namespace» m n v) (id_ : cml_id m n),
      nsLookup (nsLift mn e) id_ =
        match id_ with
        | cml_id.Long mn' id' => if mn == mn' then nsLookup e id' else none
        | cml_id.Short _ => none := by
  intro mn e id
  cases id with
  | Short x => simp [nsLift, nsLookup, ALOOKUP]
  | Long mn' i =>
    by_cases h : mn = mn'
    · subst h; simp [nsLift, nsLookup, ALOOKUP]
    · simp [nsLift, nsLookup, ALOOKUP, h]
/- HOL4: Theorem nsLookupMod_nsLift -/
theorem nsLookupMod_nsLift {m n v : Type} [BEq m] [LawfulBEq m] :
    ∀ (mn : m) (e : «namespace» m n v) (path : List m),
      nsLookupMod (nsLift mn e) path =
        match path with
        | [] => some (nsLift mn e)
        | mn' :: path' => if mn == mn' then nsLookupMod e path' else none := by
  intro mn e path
  cases path with
  | nil => simp [nsLift, nsLookupMod]
  | cons mn' p =>
    by_cases h : mn = mn'
    · subst h; simp [nsLift, nsLookupMod, ALOOKUP]
    · simp [nsLift, nsLookupMod, ALOOKUP, h]
theorem ns_ALOOKUP_append {α β : Type} [BEq α] (l1 l2 : List (α × β)) (k : α) :
    ALOOKUP (l1 ++ l2) k = match ALOOKUP l1 k with | some v => some v | none => ALOOKUP l2 k := by
  induction l1 with
  | nil => simp [ALOOKUP]
  | cons p t ih =>
    obtain ⟨a, b⟩ := p
    simp only [List.cons_append, ALOOKUP]
    split
    · rfl
    · exact ih

theorem ns_ALOOKUP_mem {α β : Type} [BEq α] [LawfulBEq α] (l : List (α × β)) (k : α) (v : β) :
    ALOOKUP l k = some v → (k, v) ∈ l := by
  induction l with
  | nil => simp [ALOOKUP]
  | cons p t ih =>
    obtain ⟨a, b⟩ := p
    simp only [ALOOKUP]
    split
    · rename_i h; intro hv; simp at h hv; subst h; subst hv; simp
    · intro hv; simp [ih hv]

/- HOL4: Theorem nsLookup_nsAppend_some -/
theorem nsLookup_nsAppend_some {m n v : Type} [BEq m] [LawfulBEq m] [BEq n] [LawfulBEq n] :
    ∀ (e1 : «namespace» m n v) (id_ : cml_id m n) (e2 : «namespace» m n v) (val_ : v),
      nsLookup (nsAppend e1 e2) id_ = some val_ ↔
        nsLookup e1 id_ = some val_ ∨
        (nsLookup e1 id_ = none ∧ nsLookup e2 id_ = some val_ ∧
         ∀ (p1 p2 : List m), p1 ≠ [] ∧ id_to_mods id_ = p1 ++ p2 →
           nsLookupMod e1 p1 = none) := by
  intro e1 id e2 v
  obtain ⟨v1, m1⟩ := e1
  obtain ⟨v2, m2⟩ := e2
  cases id with
  | Short x =>
    simp only [nsAppend, nsLookup, ns_ALOOKUP_append, id_to_mods]
    cases h : ALOOKUP v1 x with
    | none =>
      simp only []
      constructor
      · intro h2; refine Or.inr ⟨trivial, h2, ?_⟩
        rintro p1 p2 ⟨hne, hp⟩
        cases p1 with
        | nil => exact absurd rfl hne
        | cons a t => simp at hp
      · rintro (h2 | ⟨-, h2, -⟩)
        · cases h2
        · exact h2
    | some w => simp
  | Long mn i =>
    simp only [nsAppend, nsLookup, ns_ALOOKUP_append, id_to_mods]
    cases h : ALOOKUP m1 mn with
    | none =>
      simp only []
      constructor
      · intro h2; refine Or.inr ⟨trivial, h2, ?_⟩
        rintro p1 p2 ⟨hne, hp⟩
        cases p1 with
        | nil => exact absurd rfl hne
        | cons a t =>
          simp at hp
          obtain ⟨rfl, -⟩ := hp
          simp [nsLookupMod, h]
      · rintro (h2 | ⟨-, h2, -⟩)
        · cases h2
        · exact h2
    | some env =>
      simp only []
      constructor
      · intro h2; exact Or.inl h2
      · rintro (h2 | ⟨-, -, h3⟩)
        · exact h2
        · have := h3 [mn] (id_to_mods i) ⟨by simp, by simp⟩
          simp [nsLookupMod, h] at this
/- HOL4: Theorem nsAppend_to_nsBindList -/
theorem nsAppend_to_nsBindList {m n v : Type} :
    ∀ (l : List (n × v)) (e : «namespace» m n v),
      nsAppend (alist_to_ns l) e = nsBindList l e := by
  intro l e
  induction l with
  | nil => cases e; rfl
  | cons p t ih =>
    obtain ⟨a, b⟩ := p
    rw [alist_to_ns_cons, nsAppend_nsBind, ih]; rfl
/- HOL4: Theorem nsLookupMod_nsAppend_none -/
theorem nsLookupMod_nsAppend_none {m n v : Type} [BEq m] [LawfulBEq m] :
    ∀ (e1 e2 : «namespace» m n v) (path : List m),
      nsLookupMod (nsAppend e1 e2) path = none ↔
        (nsLookupMod e1 path = none ∧
         (nsLookupMod e2 path = none ∨
          ∃ (p1 p2 : List m) (e3 : «namespace» m n v),
            p1 ≠ [] ∧ path = p1 ++ p2 ∧ nsLookupMod e1 p1 = some e3)) := by
  intro e1 e2 path
  cases path with
  | nil => simp [nsLookupMod]
  | cons mn p =>
    obtain ⟨v1, m1⟩ := e1
    obtain ⟨v2, m2⟩ := e2
    simp only [nsAppend, nsLookupMod, ns_ALOOKUP_append]
    cases h : ALOOKUP m1 mn with
    | none =>
      simp only [true_and]
      constructor
      · intro h2; exact Or.inl h2
      · rintro (h2 | ⟨p1, p2, e3, hne, hp, h3⟩)
        · exact h2
        · cases p1 with
          | nil => exact absurd rfl hne
          | cons a t =>
            simp at hp
            obtain ⟨rfl, -⟩ := hp
            simp [nsLookupMod, h] at h3
    | some env =>
      simp only []
      constructor
      · intro h2; exact ⟨h2, Or.inr ⟨[mn], p, env, by simp, by simp, by simp [nsLookupMod, h]⟩⟩
      · rintro ⟨h2, -⟩; exact h2
/- HOL4: Theorem eALL_T[simp] -/
theorem eALL_T {m n v : Type} [BEq m] [LawfulBEq m] [BEq n] [LawfulBEq n] :
    ∀ (e : «namespace» m n v), nsAll (fun (_n : cml_id m n) (_x : v) => True) e := fun _ _ _ _ => trivial
/- HOL4: Theorem nsLookup_nsAll -/
theorem nsLookup_nsAll {m n v : Type} [BEq m] [LawfulBEq m] [BEq n] [LawfulBEq n] :
    ∀ (env : «namespace» m n v) (x : cml_id m n) (P : cml_id m n → v → Prop) (val_ : v),
      nsAll P env ∧ nsLookup env x = some val_ → P x val_ := fun _ x _ v ⟨h1, h2⟩ => h1 x v h2
/- HOL4: Theorem nsAll_nsAppend -/
theorem nsAll_nsAppend {m n v : Type} [BEq m] [LawfulBEq m] [BEq n] [LawfulBEq n] :
    ∀ (f : cml_id m n → v → Prop) (e1 e2 : «namespace» m n v),
      nsAll f e1 ∧ nsAll f e2 → nsAll f (nsAppend e1 e2) := by
  rintro f e1 e2 ⟨h1, h2⟩ id v hv
  rw [nsLookup_nsAppend_some] at hv
  rcases hv with hv | ⟨-, hv, -⟩
  · exact h1 _ _ hv
  · exact h2 _ _ hv
/- HOL4: Theorem nsAll_alist_to_ns -/
theorem nsAll_alist_to_ns {m n v : Type} [BEq m] [LawfulBEq m] [BEq n] [LawfulBEq n] :
    ∀ (R : cml_id m n → v → Prop) (l : List (n × v)),
      (∀ (p : n × v), p ∈ l → R (cml_id.Short p.1) p.2) →
        nsAll R (alist_to_ns l : «namespace» m n v) := by
  intro R l h id v hv
  cases id with
  | Short x =>
    simp only [alist_to_ns, nsLookup] at hv
    exact h (x, v) (ns_ALOOKUP_mem _ _ _ hv)
  | Long mn i => simp [alist_to_ns, nsLookup, ALOOKUP] at hv
/- HOL4: Theorem nsAll_nsLift[simp] -/
theorem nsAll_nsLift {m n v : Type} [BEq m] [LawfulBEq m] [BEq n] [LawfulBEq n] :
    ∀ (R : cml_id m n → v → Prop) (mn : m) (e : «namespace» m n v),
      nsAll R (nsLift mn e) ↔ nsAll (fun (id_ : cml_id m n) => R (cml_id.Long mn id_)) e := by
  intro R mn e
  constructor
  · intro h id v hv
    exact h (cml_id.Long mn id) v (by rw [nsLookup_nsLift]; simp [hv])
  · intro h id v hv
    rw [nsLookup_nsLift] at hv
    cases id with
    | Short x => simp at hv
    | Long mn' i =>
      by_cases he : mn = mn'
      · subst he; simp at hv; exact h i v hv
      · simp [he] at hv
/- HOL4: Theorem nsAll_nsAppend_left -/
theorem nsAll_nsAppend_left {m n v : Type} [BEq m] [LawfulBEq m] [BEq n] [LawfulBEq n] :
    ∀ (P : cml_id m n → v → Prop) (n1 n2 : «namespace» m n v),
      nsAll P (nsAppend n1 n2) → nsAll P n1 := by
  intro P n1 n2 h id v hv
  exact h id v ((nsLookup_nsAppend_some _ _ _ _).mpr (Or.inl hv))
/- HOL4: Theorem nsSub_conj -/
theorem nsSub_conj {m n v1 v2 : Type} [BEq m] [LawfulBEq m] [BEq n] [LawfulBEq n] :
    ∀ (P Q : cml_id m n → v1 → v2 → Prop) (e1 : «namespace» m n v1) (e2 : «namespace» m n v2),
      nsSub (fun (id_ : cml_id m n) (x : v1) (y : v2) => P id_ x y ∧ Q id_ x y) e1 e2 ↔
        nsSub P e1 e2 ∧ nsSub Q e1 e2 := by
  intro P Q e1 e2
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⟨fun id v hv => ?_, h2⟩, ⟨fun id v hv => ?_, h2⟩⟩
    · obtain ⟨w, hw, hp, hq⟩ := h1 id v hv; exact ⟨w, hw, hp⟩
    · obtain ⟨w, hw, hp, hq⟩ := h1 id v hv; exact ⟨w, hw, hq⟩
  · rintro ⟨⟨h1, h2⟩, ⟨h3, -⟩⟩
    refine ⟨fun id v hv => ?_, h2⟩
    obtain ⟨w, hw, hp⟩ := h1 id v hv
    obtain ⟨w', hw', hq⟩ := h3 id v hv
    rw [hw] at hw'; cases hw'
    exact ⟨w, hw, hp, hq⟩
/- HOL4: Theorem nsSub_refl -/
theorem nsSub_refl {m n v : Type} [BEq m] [LawfulBEq m] [BEq n] [LawfulBEq n] :
    ∀ (P : cml_id m n → v → Prop) (R : cml_id m n → v → v → Prop),
      (∀ (n_ : cml_id m n) (x : v), P n_ x → R n_ x x) →
        ∀ (e : «namespace» m n v), nsAll P e → nsSub R e e := by
  intro P R h e hall
  exact ⟨fun id v hv => ⟨v, hv, h _ _ (hall id v hv)⟩, fun _ hp => hp⟩
theorem ns_nsLookupMod_nsBind {m n v : Type} [BEq m] (k : n) (x : v) (e : «namespace» m n v) (path : List m) :
    nsLookupMod (nsBind k x e) path = none ↔ nsLookupMod e path = none := by
  cases e; cases path <;> simp [nsBind, nsLookupMod]

/- HOL4: Theorem nsSub_nsBind -/
theorem nsSub_nsBind {m n v1 v2 : Type} [BEq m] [LawfulBEq m] [BEq n] [LawfulBEq n] :
    ∀ (R : cml_id m n → v1 → v2 → Prop) (x : n) (v1_ : v1) (v2_ : v2)
      (e1 : «namespace» m n v1) (e2 : «namespace» m n v2),
      R (cml_id.Short x) v1_ v2_ ∧ nsSub R e1 e2 →
        nsSub R (nsBind x v1_ e1) (nsBind x v2_ e2) := by
  rintro R x v1_ v2_ e1 e2 ⟨hr, h1, h2⟩
  refine ⟨fun id v hv => ?_, fun path hp => ?_⟩
  · by_cases he : id = cml_id.Short x
    · subst he
      rw [nsLookup_nsBind.1] at hv ⊢; cases hv
      exact ⟨v2_, rfl, hr⟩
    · rw [nsLookup_nsBind.2 _ _ _ _ he] at hv ⊢
      exact h1 id v hv
  · rw [ns_nsLookupMod_nsBind] at hp ⊢; exact h2 path hp
/- HOL4: Theorem nsSub_nsAppend2 -/
theorem nsSub_nsAppend2 {m n v_ : Type} [BEq m] [LawfulBEq m] [BEq n] [LawfulBEq n] :
    ∀ (R : cml_id m n → v_ → v_ → Prop)
      (e1 : «namespace» m n v_) (e2 : «namespace» m n v_) (e2' : «namespace» m n v_),
      nsSub R e1 e1 ∧ nsSub R e2 e2' →
        nsSub R (nsAppend e1 e2) (nsAppend e1 e2') := by
  rintro R e1 e2 e2' ⟨⟨h1, -⟩, ⟨h3, h4⟩⟩
  refine ⟨fun id v hv => ?_, fun path hp => ?_⟩
  · rw [nsLookup_nsAppend_some] at hv
    rcases hv with hv | ⟨hn, hv, hm⟩
    · obtain ⟨w, hw, hr⟩ := h1 id v hv
      exact ⟨w, (nsLookup_nsAppend_some _ _ _ _).mpr (Or.inl hw), hr⟩
    · obtain ⟨w, hw, hr⟩ := h3 id v hv
      exact ⟨w, (nsLookup_nsAppend_some _ _ _ _).mpr (Or.inr ⟨hn, hw, hm⟩), hr⟩
  · rw [nsLookupMod_nsAppend_none] at hp ⊢
    obtain ⟨ha, hb⟩ := hp
    refine ⟨ha, ?_⟩
    rcases hb with hb | hb
    · exact Or.inl (h4 path hb)
    · exact Or.inr hb
/- HOL4: Theorem alist_rel_restr_thm -/
theorem alist_rel_restr_thm {k v1 v2 : Type} [BEq k] [LawfulBEq k] :
    ∀ (R : k → v1 → v2 → Prop) (e1 : List (k × v1)) (e2 : List (k × v2)) (keys : List k),
      alist_rel_restr R e1 e2 keys ↔
        ∀ (k_ : k), MEM k_ keys = true →
          ∃ (val1 : v1) (val2 : v2),
            ALOOKUP e1 k_ = some val1 ∧ ALOOKUP e2 k_ = some val2 ∧ R k_ val1 val2 := by
  intro R e1 e2 keys
  induction keys with
  | nil => simp [alist_rel_restr, MEM]
  | cons a t ih =>
    simp only [alist_rel_restr]
    constructor
    · intro h k_ hk
      cases h1 : ALOOKUP e1 a with
      | none => simp [h1] at h
      | some w1 =>
        cases h2 : ALOOKUP e2 a with
        | none => simp [h1, h2] at h
        | some w2 =>
          simp only [h1, h2] at h
          simp only [MEM, List.any_cons, Bool.or_eq_true, beq_iff_eq] at hk
          rcases hk with rfl | hk
          · exact ⟨w1, w2, h1, h2, h.1⟩
          · exact ih.mp h.2 k_ hk
    · intro h
      obtain ⟨w1, w2, h1, h2, hr⟩ := h a (by simp [MEM])
      simp only [h1, h2]
      refine ⟨hr, ih.mpr (fun k_ hk => h k_ ?_)⟩
      simp only [MEM, List.any_cons, Bool.or_eq_true] at hk ⊢
      exact Or.inr hk
/- HOL4: Theorem alistSub_cong -/
theorem alistSub_cong {k v1 v2 : Type} [BEq k] [LawfulBEq k] :
    ∀ (l1 l1' : List (k × v1)) (l2 l2' : List (k × v2))
      (R R' : k → v1 → v2 → Prop),
      l1 = l1' ∧ l2 = l2' ∧
        (∀ (n_ : k) (x : v1) (y : v2),
          ALOOKUP l1' n_ = some x ∧ ALOOKUP l2' n_ = some y → R n_ x y = R' n_ x y) →
        (alistSub R l1 l2 ↔ alistSub R' l1' l2') := by
  rintro l1 l1' l2 l2' R R' ⟨rfl, rfl, h⟩
  simp only [alistSub, alist_rel_restr_thm]
  constructor
  · intro h1 k_ hk
    obtain ⟨w1, w2, a, b, c⟩ := h1 k_ hk
    exact ⟨w1, w2, a, b, (h k_ w1 w2 ⟨a, b⟩) ▸ c⟩
  · intro h1 k_ hk
    obtain ⟨w1, w2, a, b, c⟩ := h1 k_ hk
    exact ⟨w1, w2, a, b, (h k_ w1 w2 ⟨a, b⟩).symm ▸ c⟩
/- HOL4: Theorem nsLookup_FOLDR_nsLift -/
theorem nsLookup_FOLDR_nsLift {m n v : Type} [BEq m] [LawfulBEq m] [BEq n] [LawfulBEq n] :
    ∀ (e : «namespace» m n v) (p : List m) (k : n),
      nsLookup (FOLDR nsLift e p) (mk_id p k) = nsLookup e (cml_id.Short k) := by
  intro e p k
  induction p with
  | nil => rfl
  | cons a t ih =>
    show nsLookup (nsLift a (FOLDR nsLift e t)) (cml_id.Long a (mk_id t k)) = _
    rw [nsLookup_nsLift]; simp [ih]
/- HOL4: Theorem nsLookup_FOLDR_nsLift_some -/
theorem nsLookup_FOLDR_nsLift_some {m n v : Type} [BEq m] [LawfulBEq m] [BEq n] [LawfulBEq n] :
    ∀ (e : «namespace» m n v) (p : List m) (id_ : cml_id m n) (val_ : v),
      nsLookup (FOLDR nsLift e p) id_ = some val_ ↔
        (p = [] ∧ nsLookup e id_ = some val_) ∨
        (p ≠ [] ∧ ∃ (p2 : List m) (n_ : n),
          id_ = mk_id (p ++ p2) n_ ∧ nsLookup e (mk_id p2 n_) = some val_) := by
  intro e p
  induction p with
  | nil => intro id v; simp [FOLDR]
  | cons a t ih =>
    intro id v
    show nsLookup (nsLift a (FOLDR nsLift e t)) id = some v ↔ _
    rw [nsLookup_nsLift]
    cases id with
    | Short x => simp [mk_id]
    | Long mn' i =>
      by_cases he : a = mn'
      · subst he
        simp only [beq_self_eq_true, if_true, ih, List.cons_append, mk_id]
        constructor
        · rintro (⟨rfl, h⟩ | ⟨hne, p2, n_, rfl, h⟩)
          · obtain ⟨p2, n_, rfl⟩ := mk_id_surj i
            exact Or.inr ⟨by simp, p2, n_, by simp, h⟩
          · exact Or.inr ⟨by simp, p2, n_, rfl, h⟩
        · rintro (⟨h, -⟩ | ⟨-, p2, n_, h1, h⟩)
          · cases h
          · injection h1 with _ h1
            subst h1
            cases t with
            | nil => exact Or.inl ⟨rfl, by simpa using h⟩
            | cons b t' => exact Or.inr ⟨by simp, p2, n_, rfl, h⟩
      · simp [he, mk_id]
        intro _ _ h; exact absurd h.symm he
/- HOL4: Theorem nsLookupMod_FOLDR_nsLift_none -/
theorem nsLookupMod_FOLDR_nsLift_none {m n v : Type} [BEq m] [LawfulBEq m] :
    ∀ (e : «namespace» m n v) (p1 p2 : List m),
      nsLookupMod (FOLDR nsLift e p1) p2 = none ↔
        (IS_PREFIX p1 p2 = true ∨ IS_PREFIX p2 p1 = true) →
          ∃ (p3 : List m), p2 = p1 ++ p3 ∧ nsLookupMod e p3 = none := by
  intro e p1
  induction p1 with
  | nil => intro p2; simp [FOLDR, IS_PREFIX]
  | cons a t ih =>
    intro p2
    show nsLookupMod (nsLift a (FOLDR nsLift e t)) p2 = none ↔ _
    rw [nsLookupMod_nsLift]
    cases p2 with
    | nil => simp [IS_PREFIX]
    | cons b p2' =>
      by_cases he : a = b
      · subst he
        simp only [beq_self_eq_true, if_true, ih, IS_PREFIX, List.isPrefixOf_cons₂, Bool.true_and,
          List.cons_append, List.cons.injEq, true_and]
      · have he' : ¬ (b = a) := fun h => he h.symm
        simp [he, he', IS_PREFIX]
/- HOL4: Theorem nsAll2_conj -/
theorem nsAll2_conj {m n v1 v2 : Type} [BEq m] [LawfulBEq m] [BEq n] [LawfulBEq n] :
    ∀ (P Q : cml_id m n → v1 → v2 → Prop)
      (e1 : «namespace» m n v1) (e2 : «namespace» m n v2),
      nsAll2 (fun (id_ : cml_id m n) (x : v1) (y : v2) => P id_ x y ∧ Q id_ x y) e1 e2 ↔
        nsAll2 P e1 e2 ∧ nsAll2 Q e1 e2 := by
  intro P Q e1 e2
  unfold nsAll2
  have h1 := nsSub_conj P Q e1 e2
  have h2 := nsSub_conj (fun x y z => P x z y) (fun x y z => Q x z y) e2 e1
  constructor
  · rintro ⟨a, b⟩; exact ⟨⟨(h1.mp a).1, (h2.mp b).1⟩, ⟨(h1.mp a).2, (h2.mp b).2⟩⟩
  · rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩; exact ⟨h1.mpr ⟨a, c⟩, h2.mpr ⟨b, d⟩⟩
/- HOL4: Theorem nsAll2_nsLookup2 -/
theorem nsAll2_nsLookup2 {m n v1 v2 : Type} [BEq m] [LawfulBEq m] [BEq n] [LawfulBEq n] :
    ∀ (R : cml_id m n → v1 → v2 → Prop)
      (e1 : «namespace» m n v1) (e2 : «namespace» m n v2) (n_ : cml_id m n) (v2_ : v2),
      nsLookup e2 n_ = some v2_ ∧ nsAll2 R e1 e2 →
        ∃ (v1_ : v1), nsLookup e1 n_ = some v1_ ∧ R n_ v1_ v2_ := by
  rintro R e1 e2 n_ v2_ ⟨h, -, ⟨h2, -⟩⟩
  exact h2 n_ v2_ h
/- HOL4: Theorem nsAll2_nsLookup_none -/
theorem nsAll2_nsLookup_none {m n v1 v2 : Type} [BEq m] [LawfulBEq m] [BEq n] [LawfulBEq n] :
    ∀ (R : cml_id m n → v1 → v2 → Prop)
      (e1 : «namespace» m n v1) (e2 : «namespace» m n v2) (n_ : cml_id m n),
      nsAll2 R e1 e2 →
        (nsLookup e1 n_ = none ↔ nsLookup e2 n_ = none) := by
  rintro R e1 e2 n_ ⟨⟨h1, -⟩, ⟨h2, -⟩⟩
  constructor
  · intro h
    cases h' : nsLookup e2 n_ with
    | none => rfl
    | some w => obtain ⟨w', hw, -⟩ := h2 n_ w h'; rw [h] at hw; cases hw
  · intro h
    cases h' : nsLookup e1 n_ with
    | none => rfl
    | some w => obtain ⟨w', hw, -⟩ := h1 n_ w h'; rw [h] at hw; cases hw
/- HOL4: Theorem nsAll2_nsBind -/
theorem nsAll2_nsBind {m n v1 v2 : Type} [BEq m] [LawfulBEq m] [BEq n] [LawfulBEq n] :
    ∀ (R : cml_id m n → v1 → v2 → Prop) (x : n) (v1_ : v1) (v2_ : v2)
      (e1 : «namespace» m n v1) (e2 : «namespace» m n v2),
      R (cml_id.Short x) v1_ v2_ ∧ nsAll2 R e1 e2 →
        nsAll2 R (nsBind x v1_ e1) (nsBind x v2_ e2) := by
  rintro R x v1_ v2_ e1 e2 ⟨hr, h1, h2⟩
  exact ⟨nsSub_nsBind R x v1_ v2_ e1 e2 ⟨hr, h1⟩,
    nsSub_nsBind (fun a b c => R a c b) x v2_ v1_ e2 e1 ⟨hr, h2⟩⟩
/- HOL4: Theorem nsAll2_nsBindList -/
theorem nsAll2_nsBindList {m n v1 v2 : Type} [BEq m] [LawfulBEq m] [BEq n] [LawfulBEq n] :
    ∀ (R : cml_id m n → v1 → v2 → Prop)
      (l1 : List (n × v1)) (l2 : List (n × v2))
      (e1 : «namespace» m n v1) (e2 : «namespace» m n v2),
      LIST_REL (fun (p1 : n × v1) (p2 : n × v2) =>
        p1.1 = p2.1 ∧ R (cml_id.Short p1.1) p1.2 p2.2) l1 l2 ∧
      nsAll2 R e1 e2 →
        nsAll2 R (nsBindList l1 e1) (nsBindList l2 e2) := by
  rintro R l1 l2 e1 e2 ⟨hl, he⟩
  induction hl with
  | nil => exact he
  | cons x y xs ys hxy _ ih =>
    obtain ⟨a, b⟩ := x
    obtain ⟨c, d⟩ := y
    obtain ⟨h1, h2⟩ := hxy
    simp only at h1 h2
    subst h1
    exact nsAll2_nsBind R a b d _ _ ⟨h2, ih⟩
theorem ns_nsSub_nsAppend {m n v1 v2 : Type} [BEq m] [LawfulBEq m] [BEq n] [LawfulBEq n]
    (R : cml_id m n → v1 → v2 → Prop) (R' : cml_id m n → v2 → v1 → Prop)
    (e1 : «namespace» m n v1) (e2 : «namespace» m n v2)
    (e1' : «namespace» m n v1) (e2' : «namespace» m n v2) :
    nsSub R e1 e2 → nsSub R' e2 e1 → nsSub R e1' e2' →
      nsSub R (nsAppend e1 e1') (nsAppend e2 e2') := by
  rintro ⟨h1, h2⟩ ⟨h3, h4⟩ ⟨h5, h6⟩
  refine ⟨fun id v hv => ?_, fun path hp => ?_⟩
  · rw [nsLookup_nsAppend_some] at hv
    rcases hv with hv | ⟨hn, hv, hm⟩
    · obtain ⟨w, hw, hr⟩ := h1 id v hv
      exact ⟨w, (nsLookup_nsAppend_some _ _ _ _).mpr (Or.inl hw), hr⟩
    · obtain ⟨w, hw, hr⟩ := h5 id v hv
      refine ⟨w, (nsLookup_nsAppend_some _ _ _ _).mpr (Or.inr ⟨?_, hw, ?_⟩), hr⟩
      · cases h' : nsLookup e2 id with
        | none => rfl
        | some u => obtain ⟨u', hu, -⟩ := h3 id u h'; rw [hn] at hu; cases hu
      · intro p1 p2 hp; exact h4 p1 (hm p1 p2 hp)
  · rw [nsLookupMod_nsAppend_none] at hp ⊢
    obtain ⟨ha, hb⟩ := hp
    refine ⟨h2 path ha, ?_⟩
    rcases hb with hb | ⟨p1, p2, e3, hne, hp, h3'⟩
    · exact Or.inl (h6 path hb)
    · cases h' : nsLookupMod e1 p1 with
      | none => have := h4 p1 h'; rw [h3'] at this; cases this
      | some e3' => exact Or.inr ⟨p1, p2, e3', hne, hp, h'⟩

/- HOL4: Theorem nsAll2_nsAppend -/
theorem nsAll2_nsAppend {m n v1 v2 : Type} [BEq m] [LawfulBEq m] [BEq n] [LawfulBEq n] :
    ∀ (R : cml_id m n → v1 → v2 → Prop)
      (e1 : «namespace» m n v1) (e2 : «namespace» m n v2)
      (e1' : «namespace» m n v1) (e2' : «namespace» m n v2),
      nsAll2 R e1 e2 ∧ nsAll2 R e1' e2' →
        nsAll2 R (nsAppend e1 e1') (nsAppend e2 e2') := by
  rintro R e1 e2 e1' e2' ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
  exact ⟨ns_nsSub_nsAppend _ _ _ _ _ _ h1 h2 h3, ns_nsSub_nsAppend _ _ _ _ _ _ h2 h1 h4⟩
/- HOL4: Theorem nsAll2_alist_to_ns -/
theorem nsAll2_alist_to_ns {m n v1 v2 : Type} [BEq m] [LawfulBEq m] [BEq n] [LawfulBEq n] :
    ∀ (R : cml_id m n → v1 → v2 → Prop) (l1 : List (n × v1)) (l2 : List (n × v2)),
      LIST_REL (fun (p1 : n × v1) (p2 : n × v2) =>
        p1.1 = p2.1 ∧ R (cml_id.Short p1.1) p1.2 p2.2) l1 l2 →
        nsAll2 R (alist_to_ns l1 : «namespace» m n v1) (alist_to_ns l2 : «namespace» m n v2) := by
  intro R l1 l2 h
  have := nsAll2_nsBindList R l1 l2 nsEmpty nsEmpty ⟨h, nsAll2_nsEmpty R⟩
  rw [← nsAppend_to_nsBindList, ← nsAppend_to_nsBindList, (nsAppend_nsEmpty _).1, (nsAppend_nsEmpty _).1] at this
  exact this
theorem ns_nsSub_nsLift {m n v1 v2 : Type} [BEq m] [LawfulBEq m] [BEq n] [LawfulBEq n]
    (R : cml_id m n → v1 → v2 → Prop) (mn : m)
    (e1 : «namespace» m n v1) (e2 : «namespace» m n v2) :
    nsSub R (nsLift mn e1) (nsLift mn e2) ↔
      nsSub (fun (id_ : cml_id m n) => R (cml_id.Long mn id_)) e1 e2 := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun id v hv => ?_, fun path hp => ?_⟩
    · obtain ⟨w, hw, hr⟩ := h1 (cml_id.Long mn id) v (by rw [nsLookup_nsLift]; simp [hv])
      rw [nsLookup_nsLift] at hw; simp at hw
      exact ⟨w, hw, hr⟩
    · have := h2 (mn :: path) (by rw [nsLookupMod_nsLift]; simp [hp])
      rw [nsLookupMod_nsLift] at this; simpa using this
  · rintro ⟨h1, h2⟩
    refine ⟨fun id v hv => ?_, fun path hp => ?_⟩
    · rw [nsLookup_nsLift] at hv ⊢
      cases id with
      | Short x => simp at hv
      | Long mn' i =>
        by_cases he : mn = mn'
        · subst he; simp at hv ⊢; exact h1 i v hv
        · simp [he] at hv
    · rw [nsLookupMod_nsLift] at hp ⊢
      cases path with
      | nil => simp at hp
      | cons mn' p =>
        by_cases he : mn = mn'
        · subst he; simp at hp ⊢; exact h2 p hp
        · simp [he]

/- HOL4: Theorem nsAll2_nsLift[simp] -/
theorem nsAll2_nsLift {m n v1 v2 : Type} [BEq m] [LawfulBEq m] [BEq n] [LawfulBEq n] :
    ∀ (R : cml_id m n → v1 → v2 → Prop) (mn : m)
      (e1 : «namespace» m n v1) (e2 : «namespace» m n v2),
      nsAll2 R (nsLift mn e1) (nsLift mn e2) ↔
        nsAll2 (fun (id_ : cml_id m n) => R (cml_id.Long mn id_)) e1 e2 := by
  intro R mn e1 e2
  unfold nsAll2
  rw [ns_nsSub_nsLift, ns_nsSub_nsLift]

/-
  Translation of miscScript.sml
  Miscellaneous definitions and minor lemmas.
-/
import LeanTypeSound.HOL4Prelude
import LeanTypeSound.LprefixLub

open HOL4

/- HOL4:
Definition the_def:
  the _ (SOME x) = x ∧
  the x NONE = x
End
-/
def the {α : Type} (d : α) : Option α → α
  | some x => x
  | none => d

/- HOL4:
Datatype:
  app_list = List ('a list) | Append app_list app_list | Nil
End
-/
inductive app_list (α : Type) where
  | List : List α → app_list α
  | Append : app_list α → app_list α → app_list α
  | Nil : app_list α

/- HOL4:
Definition append_aux_def:
  (append_aux Nil aux = aux) /\
  (append_aux (List xs) aux = xs ++ aux) /\
  (append_aux (Append l1 l2) aux = append_aux l1 (append_aux l2 aux))
End
-/
def append_aux {α : Type} : app_list α → List α → List α
  | .Nil, aux => aux
  | .List xs, aux => xs ++ aux
  | .Append l1 l2, aux => append_aux l1 (append_aux l2 aux)

/- HOL4:
Definition append_def:
  append l = append_aux l []
End
-/
def cml_append {α : Type} (l : app_list α) : List α :=
  append_aux l []

/- HOL4:
Definition MAP3_def[simp]:
  (MAP3 f [] [] [] = []) /\
  (MAP3 f (h1::t1) (h2::t2) (h3::t3) = f h1 h2 h3::MAP3 f t1 t2 t3)
End
-/
def MAP3 {α β γ δ : Type} (f : α → β → γ → δ) : List α → List β → List γ → List δ
  | [], [], [] => []
  | h1 :: t1, h2 :: t2, h3 :: t3 => f h1 h2 h3 :: MAP3 f t1 t2 t3
  | _, _, _ => []

/- HOL4:
Definition tlookup_def:
  tlookup m k = case lookup k m of NONE => k | SOME k => k
End
-/
def tlookup (m : Sptree Nat) (k : Nat) : Nat :=
  match Sptree.lookup k m with
  | none => k
  | some k' => k'

/- HOL4:
Definition max3_def[simp]:
  max3 (x:num) y z = ...
End
-/
def max3 (x y z : Nat) : Nat :=
  if x > y then (if z > x then z else x)
  else (if z > y then z else y)

/- HOL4:
Type num_set = ``:unit spt``
-/
abbrev num_set := Sptree Unit

/- HOL4:
Type num_map = ``:'a spt``
-/
abbrev num_map (α : Type) := Sptree α

/- HOL4:
Definition find_index_def:
  (find_index _ [] _ = NONE) ∧
  (find_index y (x::xs) n = if x = y then SOME n else find_index y xs (n+1))
End
-/
def find_index {α : Type} [BEq α] (y : α) : List α → Nat → Option Nat
  | [], _ => none
  | x :: xs, n => if x == y then some n else find_index y xs (n + 1)

/- HOL4:
Definition between_def:
  between x y z ⇔ x:num ≤ z ∧ z < y
End
-/
def between (x y z : Nat) : Prop :=
  x ≤ z ∧ z < y

/- HOL4:
Definition enumerate_def:
  (enumerate n [] = []) ∧
  (enumerate n (x::xs) = (n,x)::enumerate (n+1) xs)
End
-/
def enumerate {α : Type} (n : Nat) : List α → List (Nat × α)
  | [] => []
  | x :: xs => (n, x) :: enumerate (n + 1) xs

/- HOL4:
Definition UPDATE_LIST_def:
  UPDATE_LIST = FOLDL (combin$C (UNCURRY UPDATE))
End
-/
def UPDATE_LIST {α : Type} (f : Nat → α) (updates : List (Nat × α)) : Nat → α :=
  updates.foldl (fun g (k, v) => fun n => if n == k then v else g n) f

/- HOL4:
Definition lookup_vars_def:
  (lookup_vars [] env = SOME []) /\
  (lookup_vars (v::vs) env =
     if v < LENGTH env then
       case lookup_vars vs env of
       | SOME xs => SOME (EL v env :: xs)
       | NONE => NONE
     else NONE)
End
-/
def lookup_vars {α : Type} [Inhabited α] : List Nat → List α → Option (List α)
  | [], _ => some []
  | v :: vs, env =>
    if v < env.length then
      match lookup_vars vs env with
      | some xs => some (EL v env :: xs)
      | none => none
    else none

/- HOL4:
Definition range_def:
  range s = {v | ∃n. lookup n s = SOME v}
End
-/
def range {α : Type} (s : Sptree α) : Set α :=
  fun v => ∃ n, Sptree.lookup n s = some v

-- ============================================================
-- Theorem stubs
-- ============================================================

theorem misc_nodup_cover {α : Type} (m : List α) :
    ∃ d : List α, d.Nodup ∧ (∀ a, a ∈ d ↔ a ∈ m) ∧ d.length ≤ m.length ∧
      (d.length = m.length → m.Nodup) := by
  induction m with
  | nil => exact ⟨[], by simp⟩
  | cons a t ih =>
    obtain ⟨d, hd, hmem, hlen, hnd⟩ := ih
    by_cases ha : a ∈ t
    · refine ⟨d, hd, ?_, by simp; omega, ?_⟩
      · intro x; simp [hmem]; intro h; subst h; exact ha
      · intro h; simp at h; omega
    · refine ⟨a :: d, ?_, ?_, by simp; omega, ?_⟩
      · simp [hd, hmem, ha]
      · intro x; simp [hmem]
      · intro h; simp at h; simp [ha, hnd h]

theorem misc_nodup_length_le {α : Type} (d : List α) : ∀ (l : List α), d.Nodup → (∀ a, a ∈ d → a ∈ l) →
    d.length ≤ l.length := by
  classical
  induction d with
  | nil => intro l _ _; simp
  | cons x d ih =>
    intro l hnd hsub
    simp at hnd
    have hx : x ∈ l := hsub x (by simp)
    have := ih (l.erase x) hnd.2 (fun b hb => by
      have hne : b ≠ x := by rintro rfl; exact hnd.1 hb
      exact (List.mem_erase_of_ne hne).mpr (hsub b (by simp [hb])))
    rw [List.length_erase_of_mem hx] at this
    have : 0 < l.length := List.length_pos_of_mem hx
    simp; omega

theorem misc_lookup_BN_even {α : Type} (t1 t2 : Sptree α) (k : Nat) :
    Sptree.lookup (2 * k + 2) (.BN t1 t2) = Sptree.lookup k t1 := by
  simp only [Sptree.lookup]
  rw [if_neg (by omega), if_pos (by omega)]; congr 1; omega

theorem misc_lookup_BN_odd {α : Type} (t1 t2 : Sptree α) (k : Nat) :
    Sptree.lookup (2 * k + 1) (.BN t1 t2) = Sptree.lookup k t2 := by
  simp only [Sptree.lookup]
  rw [if_neg (by omega), if_neg (by omega)]; congr 1; omega

theorem misc_lookup_BS_even {α : Type} (t1 t2 : Sptree α) (x : α) (k : Nat) :
    Sptree.lookup (2 * k + 2) (.BS t1 x t2) = Sptree.lookup k t1 := by
  simp only [Sptree.lookup]
  rw [if_neg (by omega), if_pos (by omega)]; congr 1; omega

theorem misc_lookup_BS_odd {α : Type} (t1 t2 : Sptree α) (x : α) (k : Nat) :
    Sptree.lookup (2 * k + 1) (.BS t1 x t2) = Sptree.lookup k t2 := by
  simp only [Sptree.lookup]
  rw [if_neg (by omega), if_neg (by omega)]; congr 1; omega

theorem misc_CARD_eq {α : Type} {s : Set α} {l : List α} (hl : l.Nodup) (hs : ∀ a, s a ↔ a ∈ l) :
    CARD s = l.length := by
  unfold CARD
  have h : ∃ l : List α, l.Nodup ∧ ∀ a, s a ↔ a ∈ l := ⟨l, hl, hs⟩
  rw [dif_pos h]
  have h2 := Classical.choose_spec h
  apply Nat.le_antisymm
  · exact misc_nodup_length_le _ l h2.1 (fun a ha => (hs a).mp ((h2.2 a).mpr ha))
  · exact misc_nodup_length_le _ _ hl (fun a ha => (h2.2 a).mp ((hs a).mpr ha))

theorem misc_nodup_subset_full {α : Type} (d : List α) : ∀ (l : List α), d.Nodup → (∀ a, a ∈ d → a ∈ l) →
    l.length ≤ d.length → ∀ a, a ∈ l → a ∈ d := by
  classical
  induction d with
  | nil => intro l _ _ hlen a ha; cases l <;> simp_all
  | cons x d ih =>
    intro l hnd hsub hlen a ha
    simp at hnd
    have hx : x ∈ l := hsub x (by simp)
    have := ih (l.erase x) hnd.2 (fun b hb => by
      have hne : b ≠ x := by rintro rfl; exact hnd.1 hb
      exact (List.mem_erase_of_ne hne).mpr (hsub b (by simp [hb])))
      (by rw [List.length_erase_of_mem hx]; simp at hlen; omega)
    by_cases hax : a = x
    · simp [hax]
    · simp [hax]; exact this a ((List.mem_erase_of_ne hax).mpr ha)

theorem misc_pairwise_inj {α β : Type} (f : α → β) (l : List α) (h : (l.map f).Nodup) :
    ∀ a1 a2, a1 ∈ l → a2 ∈ l → f a1 = f a2 → a1 = a2 := by
  induction l with
  | nil => simp
  | cons x t ih =>
    simp at h
    intro a1 a2 h1 h2 he
    simp at h1 h2
    rcases h1 with rfl | h1 <;> rcases h2 with rfl | h2
    · rfl
    · exact absurd he.symm (h.1 a2 h2)
    · exact absurd he (h.1 a1 h1)
    · exact ih h.2 a1 a2 h1 h2 he

/- HOL4:
Theorem CARD_IMAGE_ID_BIJ:
   ∀s. FINITE s ⇒ (∀x. x ∈ s ⇒ f x ∈ s) ∧ CARD (IMAGE f s) = CARD s ⇒ BIJ f s s
-/
theorem CARD_IMAGE_ID_BIJ {α : Type} {f : α → α} {s : Set α} :
    FINITE s →
    (∀ x, x ∈ s → f x ∈ s) ∧ CARD (IMAGE f s) = CARD s →
    BIJ f s s := by
  rintro ⟨l0, hl0⟩ ⟨hclosed, hcard⟩
  obtain ⟨l, hlnd, hlmem, -, -⟩ := misc_nodup_cover l0
  have hs : ∀ a, s a ↔ a ∈ l := fun a => by rw [hl0, hlmem]
  obtain ⟨d, hdnd, hdmem, hdlen, hdfull⟩ := misc_nodup_cover (l.map f)
  have himg : ∀ a, IMAGE f s a ↔ a ∈ d := by
    intro a; rw [hdmem]; simp only [IMAGE, Set.image, List.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, (hs x).mp hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, (hs x).mpr hx, rfl⟩
  rw [misc_CARD_eq hdnd himg, misc_CARD_eq hlnd hs] at hcard
  have hmapnd : (l.map f).Nodup := hdfull (by simp [hcard])
  refine ⟨hclosed, ?_, ?_⟩
  · intro a1 a2 h1 h2
    exact misc_pairwise_inj f l hmapnd a1 a2 ((hs a1).mp h1) ((hs a2).mp h2)
  · intro b hb
    have := misc_nodup_subset_full (l.map f) l hmapnd (by
      intro a ha
      simp only [List.mem_map] at ha
      obtain ⟨x, hx, rfl⟩ := ha
      exact (hs _).mp (hclosed x ((hs x).mpr hx))) (by simp) b ((hs b).mp hb)
    simp only [List.mem_map] at this
    obtain ⟨x, hx, rfl⟩ := this
    exact ⟨x, (hs x).mpr hx, rfl⟩
def misc_keys {α : Type} : Sptree α → List Nat
  | .LN => []
  | .LS _ => [0]
  | .BN t1 t2 => (misc_keys t1).map (fun n => 2 * n + 2) ++ (misc_keys t2).map (fun n => 2 * n + 1)
  | .BS t1 _ t2 => 0 :: ((misc_keys t1).map (fun n => 2 * n + 2) ++ (misc_keys t2).map (fun n => 2 * n + 1))

theorem misc_domain_lookup {α : Type} (t : Sptree α) : ∀ k, Sptree.domain t k ↔ ∃ v, Sptree.lookup k t = some v := by
  induction t with
  | LN => intro k; simp [Sptree.domain, Sptree.lookup]; exact fun h => h
  | LS a => intro k; simp [Sptree.domain, Sptree.lookup, Set.insert]; intro h; exact h.elim
  | BN t1 t2 ih1 ih2 =>
    intro k
    show (Set.image (fun n => 2 * n + 2) (Sptree.domain t1) k ∨ Set.image (fun n => 2 * n + 1) (Sptree.domain t2) k) ↔ _
    simp only [Set.image, Sptree.lookup, ih1, ih2]
    constructor
    · rintro (⟨a, ⟨v, hv⟩, rfl⟩ | ⟨a, ⟨v, hv⟩, rfl⟩)
      · exact ⟨v, by rw [← hv]; exact misc_lookup_BN_even t1 t2 a⟩
      · exact ⟨v, by rw [← hv]; exact misc_lookup_BN_odd t1 t2 a⟩
    · rintro ⟨v, hv⟩
      by_cases h0 : k = 0
      · simp [h0] at hv
      · by_cases h2 : k % 2 = 0
        · simp [h0, h2] at hv
          exact Or.inl ⟨(k-1)/2, ⟨v, hv⟩, by omega⟩
        · simp [h0, h2] at hv
          exact Or.inr ⟨(k-1)/2, ⟨v, hv⟩, by omega⟩
  | BS t1 x t2 ih1 ih2 =>
    intro k
    show ((Set.insert 0 Set.empty k ∨ Set.image (fun n => 2 * n + 2) (Sptree.domain t1) k) ∨ Set.image (fun n => 2 * n + 1) (Sptree.domain t2) k) ↔ _
    simp only [Set.image, Sptree.lookup, ih1, ih2, Set.insert, Set.empty]
    constructor
    · rintro ((h | ⟨a, ⟨v, hv⟩, rfl⟩) | ⟨a, ⟨v, hv⟩, rfl⟩)
      · rcases h with h | h
        · simp [h]
        · exact h.elim
      · exact ⟨v, by rw [← hv]; exact misc_lookup_BS_even t1 t2 x a⟩
      · exact ⟨v, by rw [← hv]; exact misc_lookup_BS_odd t1 t2 x a⟩
    · rintro ⟨v, hv⟩
      by_cases h0 : k = 0
      · exact Or.inl (Or.inl (Or.inl h0))
      · by_cases h2 : k % 2 = 0
        · simp [h0, h2] at hv
          exact Or.inl (Or.inr ⟨(k-1)/2, ⟨v, hv⟩, by omega⟩)
        · simp [h0, h2] at hv
          exact Or.inr ⟨(k-1)/2, ⟨v, hv⟩, by omega⟩

theorem misc_keys_domain {α : Type} (t : Sptree α) : ∀ k, Sptree.domain t k ↔ k ∈ misc_keys t := by
  induction t with
  | LN => intro k; simp [Sptree.domain, misc_keys]; exact fun h => h
  | LS a => intro k; simp [Sptree.domain, misc_keys, Set.insert]; intro h; exact h.elim
  | BN t1 t2 ih1 ih2 =>
    intro k
    show (Set.image (fun n => 2 * n + 2) (Sptree.domain t1) k ∨ Set.image (fun n => 2 * n + 1) (Sptree.domain t2) k) ↔ _
    simp only [Set.image, ih1, ih2, misc_keys, List.mem_append, List.mem_map]
  | BS t1 x t2 ih1 ih2 =>
    intro k
    show ((Set.insert 0 Set.empty k ∨ Set.image (fun n => 2 * n + 2) (Sptree.domain t1) k) ∨ Set.image (fun n => 2 * n + 1) (Sptree.domain t2) k) ↔ _
    simp only [Set.image, ih1, ih2, misc_keys, List.mem_append, List.mem_map, List.mem_cons, Set.insert, Set.empty, or_false, or_assoc]

theorem misc_lookup_BN {α : Type} (t1 t2 : Sptree α) (v : α) :
    (∃ k, Sptree.lookup k (.BN t1 t2) = some v) ↔ (∃ k, Sptree.lookup k t1 = some v) ∨ (∃ k, Sptree.lookup k t2 = some v) := by
  constructor
  · rintro ⟨k, hk⟩
    simp only [Sptree.lookup] at hk
    by_cases h0 : k = 0
    · simp [h0] at hk
    · by_cases h2 : k % 2 = 0
      · simp [h0, h2] at hk; exact Or.inl ⟨_, hk⟩
      · simp [h0, h2] at hk; exact Or.inr ⟨_, hk⟩
  · rintro (⟨k, hk⟩ | ⟨k, hk⟩)
    · exact ⟨2 * k + 2, by rw [misc_lookup_BN_even, hk]⟩
    · exact ⟨2 * k + 1, by rw [misc_lookup_BN_odd, hk]⟩

theorem misc_lookup_BS {α : Type} (t1 t2 : Sptree α) (x v : α) :
    (∃ k, Sptree.lookup k (.BS t1 x t2) = some v) ↔ v = x ∨ (∃ k, Sptree.lookup k t1 = some v) ∨ (∃ k, Sptree.lookup k t2 = some v) := by
  constructor
  · rintro ⟨k, hk⟩
    simp only [Sptree.lookup] at hk
    by_cases h0 : k = 0
    · simp [h0] at hk; exact Or.inl hk.symm
    · by_cases h2 : k % 2 = 0
      · simp [h0, h2] at hk; exact Or.inr (Or.inl ⟨_, hk⟩)
      · simp [h0, h2] at hk; exact Or.inr (Or.inr ⟨_, hk⟩)
  · rintro (rfl | ⟨k, hk⟩ | ⟨k, hk⟩)
    · exact ⟨0, by simp [Sptree.lookup]⟩
    · exact ⟨2 * k + 2, by rw [misc_lookup_BS_even, hk]⟩
    · exact ⟨2 * k + 1, by rw [misc_lookup_BS_odd, hk]⟩

theorem misc_mem_toListA {α : Type} (t : Sptree α) : ∀ (acc : List α) (v : α),
    v ∈ Sptree.toListA acc t ↔ v ∈ acc ∨ ∃ k, Sptree.lookup k t = some v := by
  induction t with
  | LN => intro acc v; simp [Sptree.toListA, Sptree.lookup]
  | LS a => intro acc v; simp [Sptree.toListA, Sptree.lookup]; constructor
            · rintro (h | h); exact Or.inr h.symm; exact Or.inl h
            · rintro (h | h); exact Or.inr h; exact Or.inl h.symm
  | BN t1 t2 ih1 ih2 =>
    intro acc v
    rw [misc_lookup_BN]; simp only [Sptree.toListA, ih1, ih2]
    constructor
    · rintro ((h | h) | h) <;> simp [h]
    · rintro (h | h | h) <;> simp [h]
  | BS t1 x t2 ih1 ih2 =>
    intro acc v
    rw [misc_lookup_BS]; simp only [Sptree.toListA, ih1, ih2, List.mem_cons]
    constructor
    · rintro ((h | h | h) | h) <;> simp [h]
    · rintro (h | h | h | h) <;> simp [h]

theorem misc_mem_toList {α : Type} (t : Sptree α) (v : α) :
    v ∈ Sptree.toList t ↔ ∃ k, Sptree.lookup k t = some v := by
  simp [Sptree.toList, misc_mem_toListA]

/- HOL4:
Theorem tlookup_bij_suff:
   set (toList names) = domain names ⇒ BIJ (tlookup names) UNIV UNIV
-/
theorem tlookup_bij_suff {names : Sptree Nat} :
    (fun x => x ∈ Sptree.toList names) = Sptree.domain names →
    BIJ (tlookup names) Set.univ Set.univ := by
  intro heq
  have hval : ∀ x, x ∈ Sptree.toList names ↔ Sptree.domain names x := fun x => by
    have := congrFun heq x; exact this ▸ Iff.rfl
  have hin : ∀ k, Sptree.domain names k → Sptree.domain names (tlookup names k) := by
    intro k hk
    obtain ⟨v, hv⟩ := (misc_domain_lookup names k).mp hk
    simp only [tlookup, hv]
    exact (hval v).mp ((misc_mem_toList names v).mpr ⟨k, hv⟩)
  have hout : ∀ k, ¬ Sptree.domain names k → tlookup names k = k := by
    intro k hk
    cases hv : Sptree.lookup k names with
    | none => simp [tlookup, hv]
    | some v => exact absurd ((misc_domain_lookup names k).mpr ⟨v, hv⟩) hk
  have himg : IMAGE (tlookup names) (Sptree.domain names) = Sptree.domain names := by
    funext b
    apply propext
    constructor
    · rintro ⟨a, ha, rfl⟩; exact hin a ha
    · intro hb
      obtain ⟨k, hk⟩ := (misc_mem_toList names b).mp ((hval b).mpr hb)
      exact ⟨k, (misc_domain_lookup names k).mpr ⟨b, hk⟩, by simp [tlookup, hk]⟩
  have hbij : BIJ (tlookup names) (Sptree.domain names) (Sptree.domain names) :=
    CARD_IMAGE_ID_BIJ ⟨misc_keys names, misc_keys_domain names⟩ ⟨hin, by rw [himg]⟩
  obtain ⟨-, hinj, hsurj⟩ := hbij
  refine ⟨fun _ _ => trivial, ?_, ?_⟩
  · intro a1 a2 _ _ he
    by_cases h1 : Sptree.domain names a1 <;> by_cases h2 : Sptree.domain names a2
    · exact hinj a1 a2 h1 h2 he
    · rw [hout a2 h2] at he; exact absurd (he ▸ hin a1 h1) h2
    · rw [hout a1 h1] at he; exact absurd (he ▸ hin a2 h2) h1
    · rw [hout a1 h1, hout a2 h2] at he; exact he
  · intro b _
    by_cases hb : Sptree.domain names b
    · obtain ⟨a, _, ha⟩ := hsurj b hb; exact ⟨a, trivial, ha⟩
    · exact ⟨b, trivial, hout b hb⟩
/- HOL4:
Theorem tlookup_bij_iff:
   BIJ (tlookup names) UNIV UNIV ⇔ set (toList names) = domain names
-/
theorem tlookup_bij_iff {names : Sptree Nat} :
    BIJ (tlookup names) Set.univ Set.univ ↔
    (fun x => x ∈ Sptree.toList names) = Sptree.domain names := by
  refine ⟨?_, tlookup_bij_suff⟩
  rintro ⟨-, hinj, hsurj⟩
  have hout : ∀ k, ¬ Sptree.domain names k → tlookup names k = k := by
    intro k hk
    cases hv : Sptree.lookup k names with
    | none => simp [tlookup, hv]
    | some v => exact absurd ((misc_domain_lookup names k).mpr ⟨v, hv⟩) hk
  funext b
  apply propext
  constructor
  · intro hb
    obtain ⟨k, hk⟩ := (misc_mem_toList names b).mp hb
    have hfk : tlookup names k = b := by simp [tlookup, hk]
    apply Classical.byContradiction
    intro hnb
    have := hinj b k trivial trivial (by rw [hout b hnb, hfk])
    subst this
    exact hnb ((misc_domain_lookup names b).mpr ⟨b, hk⟩)
  · intro hb
    obtain ⟨a, _, ha⟩ := hsurj b trivial
    by_cases hd : Sptree.domain names a
    · obtain ⟨v, hv⟩ := (misc_domain_lookup names a).mp hd
      have : v = b := by simpa [tlookup, hv] using ha
      exact (misc_mem_toList names b).mpr ⟨a, this ▸ hv⟩
    · rw [hout a hd] at ha; subst ha; exact absurd hb hd
/- HOL4:
Theorem find_index_LESS_LENGTH:
   ∀ls n m i. (find_index n ls m = SOME i) ⇒ (m <= i) ∧ (i < m + LENGTH ls)
-/
theorem find_index_LESS_LENGTH {α : Type} [BEq α] [LawfulBEq α]
    (ls : List α) (n : α) (m i : Nat) :
    find_index n ls m = some i → m ≤ i ∧ i < m + ls.length := by
  induction ls generalizing m with
  | nil => simp [find_index]
  | cons x xs ih =>
    simp only [find_index]
    split
    · intro h; simp at h; subst h; simp
    · intro h; have := ih _ h; simp; omega
theorem misc_ALOOKUP_find_index_aux {α β : Type} [BEq α] [LawfulBEq α] [Inhabited α] [Inhabited β]
    {env : List (α × β)} {k : α} {val_ : β} (m : Nat) :
    ALOOKUP env k = some val_ →
    ∃ i, find_index k (env.map Prod.fst) m = some (m + i) ∧
      i < env.length ∧ val_ = (EL i env).2 := by
  induction env generalizing m with
  | nil => simp [ALOOKUP]
  | cons p ps ih =>
    obtain ⟨a, b⟩ := p
    simp only [ALOOKUP, List.map_cons, find_index]
    split
    · intro h; simp at h; subst h; exact ⟨0, by simp [EL]⟩
    · intro h
      obtain ⟨i, h1, h2, h3⟩ := ih (m+1) h
      refine ⟨i+1, ?_, by simp; omega, ?_⟩
      · rw [h1]; congr 1; omega
      · rw [h3]; simp [EL]

/- HOL4:
Theorem ALOOKUP_find_index_SOME:
   (ALOOKUP env k = SOME v) ⇒
    ∃i. (find_index k (MAP FST env) 0 = SOME i) ∧ i < LENGTH env ∧ (v = SND (EL i env))
-/
theorem ALOOKUP_find_index_SOME {α β : Type} [BEq α] [LawfulBEq α] [Inhabited α] [Inhabited β]
    {env : List (α × β)} {k : α} {val_ : β} :
    ALOOKUP env k = some val_ →
    ∃ i, find_index k (env.map Prod.fst) 0 = some i ∧
      i < env.length ∧ val_ = (EL i env).2 := by
  intro h
  obtain ⟨i, h1, h2, h3⟩ := misc_ALOOKUP_find_index_aux 0 h
  exact ⟨i, by simpa using h1, h2, h3⟩
/- HOL4:
Theorem IS_PREFIX_THM:
  !l2 l1. IS_PREFIX l1 l2 <=> (LENGTH l2 <= LENGTH l1) /\ !n. n < LENGTH l2 ==> (EL n l2 = EL n l1)
-/
theorem IS_PREFIX_THM {α : Type} [BEq α] [LawfulBEq α] [Inhabited α]
    (l2 l1 : List α) :
    IS_PREFIX l1 l2 = true ↔
    l2.length ≤ l1.length ∧ ∀ n, n < l2.length → EL n l2 = EL n l1 := by
  unfold IS_PREFIX
  induction l2 generalizing l1 with
  | nil => simp
  | cons x xs ih =>
    cases l1 with
    | nil => simp
    | cons y ys =>
      simp only [List.isPrefixOf_cons₂, Bool.and_eq_true, ih, List.length_cons, beq_iff_eq]
      constructor
      · rintro ⟨rfl, h1, h2⟩
        refine ⟨by omega, ?_⟩
        intro n hn
        cases n with
        | zero => simp [EL]
        | succ n => have := h2 n (by omega); simpa [EL] using this
      · rintro ⟨h1, h2⟩
        refine ⟨?_, by omega, ?_⟩
        · have := h2 0 (by omega); simpa [EL] using this
        · intro n hn; have := h2 (n+1) (by omega); simpa [EL] using this
/- HOL4:
Theorem FST_pair:
  (λ(n,v). n) = FST
-/
theorem FST_pair {α β : Type} :
    (fun (p : α × β) => p.1) = Prod.fst := rfl
/- HOL4:
Theorem LESS_1[simp]:
  x < 1 ⇔ (x = 0:num)
-/
theorem LESS_1 {x : Nat} :
    x < 1 ↔ x = 0 := by omega
/- HOL4:
Theorem map_some_eq:
  !l1 l2. (MAP SOME l1 = MAP SOME l2) ⇔ (l1 = l2)
-/
theorem map_some_eq {α : Type} (l1 l2 : List α) :
    l1.map some = l2.map some ↔ l1 = l2 := by
  constructor
  · intro h
    induction l1 generalizing l2 with
    | nil => cases l2 <;> simp_all
    | cons a t ih =>
      cases l2 with
      | nil => simp at h
      | cons b t2 => simp at h; rw [h.1, ih _ h.2]
  · rintro rfl; rfl
/- HOL4:
Theorem map_some_eq_append:
  !l1 l2 l3. (MAP SOME l1 ++ MAP SOME l2 = MAP SOME l3) ⇔ (l1 ++ l2 = l3)
-/
theorem map_some_eq_append {α : Type} (l1 l2 l3 : List α) :
    l1.map some ++ l2.map some = l3.map some ↔ l1 ++ l2 = l3 := by
  rw [← List.map_append, map_some_eq]
/- HOL4:
Theorem MAP_EQ_MAP_IMP:
   !xs ys f. (!x y. MEM x xs /\ MEM y ys /\ (f x = f y) ==> (x = y)) ==>
     (MAP f xs = MAP f ys) ==> (xs = ys)
-/
theorem MAP_EQ_MAP_IMP {α β : Type} (xs ys : List α) (f : α → β) :
    (∀ x y, x ∈ xs ∧ y ∈ ys ∧ f x = f y → x = y) →
    xs.map f = ys.map f → xs = ys := by
  induction xs generalizing ys with
  | nil => intro _ h; cases ys <;> simp_all
  | cons a t ih =>
    intro hinj h
    cases ys with
    | nil => simp at h
    | cons b t2 =>
      simp at h
      have := hinj a b ⟨by simp, by simp, h.1⟩
      subst this
      congr 1
      exact ih t2 (fun x y ⟨h1, h2, h3⟩ => hinj x y ⟨by simp [h1], by simp [h2], h3⟩) h.2
/- HOL4:
Theorem FDOM_FLOOKUP:
   x ∈ FDOM f ⇔ ∃v. FLOOKUP f x = SOME v
-/
theorem FDOM_FLOOKUP {α β : Type} {x : α} {f : Finmap α β} :
    x ∈ Finmap.FDOM f ↔ ∃ val_, Finmap.FLOOKUP f x = some val_ := by
  show (f x).isSome = true ↔ ∃ val_, f x = some val_
  exact Option.isSome_iff_exists
/- HOL4:
Theorem DROP_EMPTY:
   !ls n. (DROP n ls = []) ==> (n >= LENGTH ls)
-/
theorem DROP_EMPTY {α : Type} (ls : List α) (n : Nat) :
    DROP n ls = [] → n ≥ ls.length := by
  unfold DROP; intro h; exact List.drop_eq_nil_iff.mp h
/- HOL4:
Theorem plus_0_I[simp]:
   $+ 0n = I
-/
theorem plus_0_I :
    (fun (n : Nat) => 0 + n) = id := by
  funext n; simp

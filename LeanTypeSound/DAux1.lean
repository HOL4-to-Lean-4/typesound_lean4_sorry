/-
  Helper lemmas for TypeSound (prover D), part 1: lists, finite maps, canonical forms.
-/
import LeanTypeSound.HOL4Prelude
import LeanTypeSound.Ast
import LeanTypeSound.TypeSystem
import LeanTypeSound.SemanticPrimitives
import LeanTypeSound.FpSem
import LeanTypeSound.Evaluate
import LeanTypeSound.NamespaceProps
import LeanTypeSound.SemanticPrimitivesProps
import LeanTypeSound.EvaluateProps
import LeanTypeSound.Weakening
import LeanTypeSound.TypeSysProps
import LeanTypeSound.TypeSoundInvariants
import LeanTypeSound.SemanticsMin

open HOL4

namespace DAux

-- ============================================================
-- LIST_REL
-- ============================================================

theorem LIST_REL_length {α β : Type} {R : α → β → Prop} {l1 : List α} {l2 : List β}
    (h : LIST_REL R l1 l2) : l1.length = l2.length := by
  induction h with
  | nil => rfl
  | cons x y xs ys _ _ ih => simp [ih]

theorem LIST_REL_nil_left {α β : Type} {R : α → β → Prop} {l2 : List β} :
    LIST_REL R [] l2 ↔ l2 = [] := by
  constructor
  · intro h; cases h; rfl
  · intro h; subst h; exact .nil

theorem LIST_REL_nil_right {α β : Type} {R : α → β → Prop} {l1 : List α} :
    LIST_REL R l1 [] ↔ l1 = [] := by
  constructor
  · intro h; cases h; rfl
  · intro h; subst h; exact .nil

theorem LIST_REL_cons_iff {α β : Type} {R : α → β → Prop} {x : α} {y : β} {l1 : List α} {l2 : List β} :
    LIST_REL R (x :: l1) (y :: l2) ↔ R x y ∧ LIST_REL R l1 l2 := by
  constructor
  · intro h; cases h with | cons _ _ _ _ h1 h2 => exact ⟨h1, h2⟩
  · intro ⟨h1, h2⟩; exact .cons _ _ _ _ h1 h2

theorem LIST_REL_cons_left {α β : Type} {R : α → β → Prop} {x : α} {l1 : List α} {l2 : List β} :
    LIST_REL R (x :: l1) l2 ↔ ∃ y l2', l2 = y :: l2' ∧ R x y ∧ LIST_REL R l1 l2' := by
  constructor
  · intro h; cases h with | cons _ y _ ys h1 h2 => exact ⟨y, ys, rfl, h1, h2⟩
  · intro ⟨y, l2', e, h1, h2⟩; subst e; exact .cons _ _ _ _ h1 h2

theorem LIST_REL_cons_right {α β : Type} {R : α → β → Prop} {y : β} {l1 : List α} {l2 : List β} :
    LIST_REL R l1 (y :: l2) ↔ ∃ x l1', l1 = x :: l1' ∧ R x y ∧ LIST_REL R l1' l2 := by
  constructor
  · intro h; cases h with | cons x _ xs _ h1 h2 => exact ⟨x, xs, rfl, h1, h2⟩
  · intro ⟨x, l1', e, h1, h2⟩; subst e; exact .cons _ _ _ _ h1 h2

theorem LIST_REL_mono {α β : Type} {R S : α → β → Prop} {l1 : List α} {l2 : List β}
    (hRS : ∀ x y, R x y → S x y) (h : LIST_REL R l1 l2) : LIST_REL S l1 l2 := by
  induction h with
  | nil => exact .nil
  | cons x y xs ys h1 _ ih => exact .cons _ _ _ _ (hRS _ _ h1) ih

theorem LIST_REL_mono_mem {α β : Type} {R S : α → β → Prop} {l1 : List α} {l2 : List β}
    (h : LIST_REL R l1 l2) (hRS : ∀ x y, x ∈ l1 → y ∈ l2 → R x y → S x y) : LIST_REL S l1 l2 := by
  induction h with
  | nil => exact .nil
  | cons x y xs ys h1 _ ih =>
    exact .cons _ _ _ _ (hRS _ _ (by simp) (by simp) h1)
      (ih (fun a b ha hb => hRS a b (by simp [ha]) (by simp [hb])))

theorem LIST_REL_append {α β : Type} {R : α → β → Prop} {l1 l1' : List α} {l2 l2' : List β}
    (h : LIST_REL R l1 l2) (h' : LIST_REL R l1' l2') : LIST_REL R (l1 ++ l1') (l2 ++ l2') := by
  induction h with
  | nil => simpa using h'
  | cons x y xs ys h1 _ ih => exact .cons _ _ _ _ h1 ih

theorem LIST_REL_reverse {α β : Type} {R : α → β → Prop} {l1 : List α} {l2 : List β}
    (h : LIST_REL R l1 l2) : LIST_REL R l1.reverse l2.reverse := by
  induction h with
  | nil => exact .nil
  | cons x y xs ys h1 _ ih =>
    simp only [List.reverse_cons]
    exact LIST_REL_append ih (.cons _ _ _ _ h1 .nil)

theorem LIST_REL_reverse_iff {α β : Type} {R : α → β → Prop} {l1 : List α} {l2 : List β} :
    LIST_REL R l1.reverse l2.reverse ↔ LIST_REL R l1 l2 := by
  constructor
  · intro h; have := LIST_REL_reverse h; simpa using this
  · exact LIST_REL_reverse

theorem LIST_REL_append_right {α β : Type} {R : α → β → Prop} {l : List α} {l2 l2' : List β}
    (h : LIST_REL R l (l2 ++ l2')) :
    ∃ l1 l1', l = l1 ++ l1' ∧ LIST_REL R l1 l2 ∧ LIST_REL R l1' l2' := by
  induction l2 generalizing l with
  | nil => exact ⟨[], l, rfl, .nil, by simpa using h⟩
  | cons y ys ih =>
    simp only [List.cons_append] at h
    obtain ⟨x, l1', e, h1, h2⟩ := LIST_REL_cons_right.mp h
    obtain ⟨a, b, e', ha, hb⟩ := ih h2
    exact ⟨x :: a, b, by simp [e, e'], .cons _ _ _ _ h1 ha, hb⟩

theorem LIST_REL_getElem {α β : Type} [Inhabited α] [Inhabited β] {R : α → β → Prop}
    {l1 : List α} {l2 : List β} (h : LIST_REL R l1 l2) :
    ∀ i, i < l1.length → R l1[i]! l2[i]! := by
  induction h with
  | nil => intro i hi; simp at hi
  | cons x y xs ys h1 _ ih =>
    intro i hi
    cases i with
    | zero => simpa using h1
    | succ j =>
      have := ih j (by simpa using hi)
      simpa using this

theorem LIST_REL_of_getElem {α β : Type} [Inhabited α] [Inhabited β] {R : α → β → Prop}
    {l1 : List α} {l2 : List β} (hlen : l1.length = l2.length)
    (h : ∀ i, i < l1.length → R l1[i]! l2[i]!) : LIST_REL R l1 l2 := by
  induction l1 generalizing l2 with
  | nil =>
    cases l2 with
    | nil => exact .nil
    | cons _ _ => simp at hlen
  | cons x xs ih =>
    cases l2 with
    | nil => simp at hlen
    | cons y ys =>
      refine .cons _ _ _ _ ?_ (ih (by simpa using hlen) ?_)
      · simpa using h 0 (by simp)
      · intro i hi
        have := h (i + 1) (by simpa using hi)
        simpa using this

theorem LIST_REL_iff_getElem {α β : Type} [Inhabited α] [Inhabited β] {R : α → β → Prop}
    {l1 : List α} {l2 : List β} :
    LIST_REL R l1 l2 ↔ l1.length = l2.length ∧ ∀ i, i < l1.length → R l1[i]! l2[i]! :=
  ⟨fun h => ⟨LIST_REL_length h, LIST_REL_getElem h⟩, fun ⟨h1, h2⟩ => LIST_REL_of_getElem h1 h2⟩

theorem LIST_REL_replicate {α β : Type} {R : α → β → Prop} {l : List α} {y : β} :
    LIST_REL R l (List.replicate l.length y) ↔ ∀ x, x ∈ l → R x y := by
  induction l with
  | nil => simp [LIST_REL_nil_left]
  | cons a l ih =>
    simp only [List.length_cons, List.replicate_succ, LIST_REL_cons_iff, ih, List.mem_cons,
      forall_eq_or_imp]

theorem LIST_REL_map_left {α β γ : Type} {R : γ → β → Prop} {f : α → γ} {l1 : List α} {l2 : List β} :
    LIST_REL R (l1.map f) l2 ↔ LIST_REL (fun a b => R (f a) b) l1 l2 := by
  induction l1 generalizing l2 with
  | nil => simp [LIST_REL_nil_left]
  | cons a l ih =>
    cases l2 with
    | nil => simp [LIST_REL_nil_right]
    | cons b l2 => simp [LIST_REL_cons_iff, ih]

theorem LIST_REL_map_right {α β γ : Type} {R : α → γ → Prop} {f : β → γ} {l1 : List α} {l2 : List β} :
    LIST_REL R l1 (l2.map f) ↔ LIST_REL (fun a b => R a (f b)) l1 l2 := by
  induction l1 generalizing l2 with
  | nil => simp [LIST_REL_nil_left]
  | cons a l ih =>
    cases l2 with
    | nil => simp [LIST_REL_nil_right]
    | cons b l2 => simp [LIST_REL_cons_iff, ih]

theorem LIST_REL_mem_right {α β : Type} {R : α → β → Prop} {l1 : List α} {l2 : List β}
    (h : LIST_REL R l1 l2) : ∀ y, y ∈ l2 → ∃ x, x ∈ l1 ∧ R x y := by
  induction h with
  | nil => intro y hy; simp at hy
  | cons x y xs ys h1 _ ih =>
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨x, by simp, h1⟩
    · obtain ⟨a, ha, hr⟩ := ih b hb
      exact ⟨a, by simp [ha], hr⟩

theorem LIST_REL_mem_left {α β : Type} {R : α → β → Prop} {l1 : List α} {l2 : List β}
    (h : LIST_REL R l1 l2) : ∀ x, x ∈ l1 → ∃ y, y ∈ l2 ∧ R x y := by
  induction h with
  | nil => intro y hy; simp at hy
  | cons x y xs ys h1 _ ih =>
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨y, by simp, h1⟩
    · obtain ⟨a, ha, hr⟩ := ih b hb
      exact ⟨a, by simp [ha], hr⟩

-- ============================================================
-- EVERY
-- ============================================================

theorem EVERY_iff {α : Type} {P : α → Bool} {l : List α} :
    EVERY P l = true ↔ ∀ x, x ∈ l → P x = true := by
  simp [EVERY]

-- ============================================================
-- Finite maps
-- ============================================================

theorem FUPDATE_LIST_reverse_eq_alist_to_fmap {α β : Type} [BEq α] (l : List (α × β)) :
    Finmap.FUPDATE_LIST Finmap.FEMPTY l.reverse = Finmap.alist_to_fmap l := by
  induction l with
  | nil => funext k; simp [Finmap.FUPDATE_LIST, Finmap.alist_to_fmap, Finmap.FEMPTY]
  | cons a l ih =>
    funext k
    have : Finmap.FUPDATE_LIST Finmap.FEMPTY (a :: l).reverse =
        Finmap.FUPDATE (Finmap.FUPDATE_LIST Finmap.FEMPTY l.reverse) a := by
      simp [Finmap.FUPDATE_LIST, List.foldl_append]
    rw [this, ih]
    simp only [Finmap.FUPDATE, Finmap.alist_to_fmap, List.find?_cons]
    cases h : k == a.1 <;> simp

theorem sing_list' {α : Type} :
    ∀ (l : List α), l.length = 1 ↔ ∃ (x : α), l = [x] := by
  intro l
  cases l with
  | nil => simp
  | cons a l => cases l <;> simp

theorem ctMap_prim_absurd {c : ctMap} {stmp : stamp} {tvs : List tvarN} {ts : List sem_t} {ti : type_ident}
    (hc : ctMap_ok c) (hl : Finmap.FLOOKUP c stmp = some (tvs, ts, ti))
    (hp : prim_type_nums.elem ti = true) (hne : ti ≠ Texn_num) : False := by
  obtain ⟨_, h2, h3, _⟩ := hc
  cases stmp with
  | TypeStamp cn x => exact h3 cn x tvs ts ti hl hp
  | ExnStamp ex => exact hne (h2 ex tvs ts ti hl).2

theorem recclosure_Tfn {tenv : type_env} {tenvE : tenv_val_exp} {funs : List (varN × varN × exp)}
    {bindings : List (varN × sem_t)} {n : varN} {ts : List sem_t} {ti : type_ident}
    (hf : type_funs tenv tenvE funs bindings) (hl : ALOOKUP bindings n = some (.Tapp ts ti)) :
    ti = Tfn_num ∧ ∃ t1 t2, ts = [t1, t2] := by
  obtain ⟨t1, t2, e, _⟩ := type_funs_Tfn tenv tenvE funs bindings 0 _ n ⟨hf, hl⟩
  simp only [Tfn, sem_t.Tapp.injEq] at e
  exact ⟨e.2, t1, t2, e.1⟩

/-- closes canonical-form side goals -/
macro "canon_absurd" hc:ident : tactic => `(tactic| first
  | exact (ctMap_prim_absurd $hc ‹Finmap.FLOOKUP _ _ = some _› (by decide) (by decide)).elim
  | exact absurd (recclosure_Tfn ‹type_funs _ _ _ _› ‹ALOOKUP _ _ = some _›).1 (by decide))

theorem canon_Tint {tvs : Nat} {c : ctMap} {s : tenv_store} {val_ : v}
    (h : type_v tvs c s val_ Tint) (hc : ctMap_ok c) : ∃ n, val_ = .Litv (.IntLit n) := by
  cases h <;> first | exact ⟨_, rfl⟩ | canon_absurd hc

theorem canon_Tchar {tvs : Nat} {c : ctMap} {s : tenv_store} {val_ : v}
    (h : type_v tvs c s val_ Tchar) (hc : ctMap_ok c) : ∃ n, val_ = .Litv (.Char n) := by
  cases h <;> first | exact ⟨_, rfl⟩ | canon_absurd hc

theorem canon_Tstring {tvs : Nat} {c : ctMap} {s : tenv_store} {val_ : v}
    (h : type_v tvs c s val_ Tstring) (hc : ctMap_ok c) : ∃ n, val_ = .Litv (.StrLit n) := by
  cases h <;> first | exact ⟨_, rfl⟩ | canon_absurd hc

theorem canon_Tword8 {tvs : Nat} {c : ctMap} {s : tenv_store} {val_ : v}
    (h : type_v tvs c s val_ Tword8) (hc : ctMap_ok c) : ∃ n, val_ = .Litv (.Word8 n) := by
  cases h <;> first | exact ⟨_, rfl⟩ | canon_absurd hc

theorem canon_Tword64 {tvs : Nat} {c : ctMap} {s : tenv_store} {val_ : v}
    (h : type_v tvs c s val_ Tword64) (hc : ctMap_ok c) : ∃ n, val_ = .Litv (.Word64 n) := by
  cases h <;> first | exact ⟨_, rfl⟩ | canon_absurd hc

theorem canon_Tdouble {tvs : Nat} {c : ctMap} {s : tenv_store} {val_ : v}
    (h : type_v tvs c s val_ Tdouble) (hc : ctMap_ok c) : ∃ n, val_ = .Litv (.Float64 n) := by
  cases h <;> first | exact ⟨_, rfl⟩ | canon_absurd hc

theorem canon_Ttup {tvs : Nat} {c : ctMap} {s : tenv_store} {val_ : v} {ts : List sem_t}
    (h : type_v tvs c s val_ (Ttup ts)) (hc : ctMap_ok c) :
    ∃ vs, val_ = .Conv none vs ∧ LIST_REL (type_v tvs c s) vs ts := by
  cases h
  · canon_absurd hc
  · exact ⟨_, rfl, LIST_REL_of_getElem ‹_› ‹_›⟩
  · canon_absurd hc

theorem canon_Tfn {tvs : Nat} {c : ctMap} {s : tenv_store} {val_ : v} {t1 t2 : sem_t}
    (h : type_v tvs c s val_ (Tfn t1 t2)) (hc : ctMap_ok c) :
    (∃ env n e, val_ = .Closure env n e) ∨ (∃ env funs n, val_ = .Recclosure env funs n) := by
  cases h
  · canon_absurd hc
  · exact .inl ⟨_, _, _, rfl⟩
  · exact .inr ⟨_, _, _, rfl⟩

theorem canon_Tvector {tvs : Nat} {c : ctMap} {s : tenv_store} {val_ : v} {t : sem_t}
    (h : type_v tvs c s val_ (Tvector t)) (hc : ctMap_ok c) :
    ∃ vs, val_ = .Vectorv vs ∧ (∀ v_, v_ ∈ vs → type_v tvs c s v_ t) := by
  cases h
  · canon_absurd hc
  · canon_absurd hc
  · exact ⟨_, rfl, ‹_›⟩

theorem canon_Tref {tvs : Nat} {c : ctMap} {s : tenv_store} {val_ : v} {t : sem_t}
    (h : type_v tvs c s val_ (Tref t)) (hc : ctMap_ok c) :
    ∃ n, val_ = .Loc true n ∧ Finmap.FLOOKUP s n = some (.Ref_t t) := by
  cases h
  · canon_absurd hc
  · canon_absurd hc
  · exact ⟨_, rfl, ‹_›⟩

theorem canon_Tword8array {tvs : Nat} {c : ctMap} {s : tenv_store} {val_ : v}
    (h : type_v tvs c s val_ Tword8array) (hc : ctMap_ok c) :
    ∃ n, val_ = .Loc true n ∧ Finmap.FLOOKUP s n = some .W8array_t := by
  cases h
  · canon_absurd hc
  · canon_absurd hc
  · exact ⟨_, rfl, ‹_›⟩

theorem canon_Tarray {tvs : Nat} {c : ctMap} {s : tenv_store} {val_ : v} {t : sem_t}
    (h : type_v tvs c s val_ (Tarray t)) (hc : ctMap_ok c) :
    ∃ n, val_ = .Loc true n ∧ Finmap.FLOOKUP s n = some (.Varray_t t) := by
  cases h
  · canon_absurd hc
  · canon_absurd hc
  · exact ⟨_, rfl, ‹_›⟩

theorem type_s_lookup {c : ctMap} {envS : List (store_v v)} {s : tenv_store} {n : Nat} {st : store_t}
    (hs : type_s c envS s) (hl : Finmap.FLOOKUP s n = some st) :
    ∃ sv, store_lookup n envS = some sv ∧ type_sv c s sv st := by
  obtain ⟨h1, h2⟩ := hs n
  obtain ⟨sv, hsv⟩ := h1.mp ⟨st, hl⟩
  exact ⟨sv, hsv, h2 st sv ⟨hl, hsv⟩⟩

theorem type_s_Ref {c : ctMap} {envS : List (store_v v)} {s : tenv_store} {n : Nat} {t : sem_t}
    (hs : type_s c envS s) (hl : Finmap.FLOOKUP s n = some (.Ref_t t)) :
    ∃ v2, store_lookup n envS = some (.Refv v2) ∧ type_v 0 c s v2 t := by
  obtain ⟨sv, h1, h2⟩ := type_s_lookup hs hl
  cases sv <;> simp [type_sv] at h2
  exact ⟨_, h1, h2⟩

theorem type_s_W8 {c : ctMap} {envS : List (store_v v)} {s : tenv_store} {n : Nat}
    (hs : type_s c envS s) (hl : Finmap.FLOOKUP s n = some .W8array_t) :
    ∃ ws, store_lookup n envS = some (.W8array ws) := by
  obtain ⟨sv, h1, h2⟩ := type_s_lookup hs hl
  cases sv <;> simp [type_sv] at h2
  exact ⟨_, h1⟩

theorem type_s_Varray {c : ctMap} {envS : List (store_v v)} {s : tenv_store} {n : Nat} {t : sem_t}
    (hs : type_s c envS s) (hl : Finmap.FLOOKUP s n = some (.Varray_t t)) :
    ∃ vs, store_lookup n envS = some (.Varray vs) ∧ (∀ v_, v_ ∈ vs → type_v 0 c s v_ t) := by
  obtain ⟨sv, h1, h2⟩ := type_s_lookup hs hl
  cases sv <;> simp [type_sv] at h2
  exact ⟨_, h1, h2⟩

theorem prim_canonical_values_thm' :
    ∀ (tvs : Nat) (ctMap_ : ctMap) (tenvS : tenv_store) (val_ : v)
      (envS : List (store_v v)) (ts : List sem_t) (t1 t2 t : sem_t),
    (type_v tvs ctMap_ tenvS val_ Tint ∧ ctMap_ok ctMap_ →
      ∃ (n : Int), val_ = .Litv (.IntLit n)) ∧
    (type_v tvs ctMap_ tenvS val_ Tchar ∧ ctMap_ok ctMap_ →
      ∃ (c : Char), val_ = .Litv (.Char c)) ∧
    (type_v tvs ctMap_ tenvS val_ Tstring ∧ ctMap_ok ctMap_ →
      ∃ (s : mlstring), val_ = .Litv (.StrLit s)) ∧
    (type_v tvs ctMap_ tenvS val_ Tword8 ∧ ctMap_ok ctMap_ →
      ∃ (n : word8), val_ = .Litv (.Word8 n)) ∧
    (type_v tvs ctMap_ tenvS val_ Tword64 ∧ ctMap_ok ctMap_ →
      ∃ (n : word64), val_ = .Litv (.Word64 n)) ∧
    (type_v tvs ctMap_ tenvS val_ Tdouble ∧ ctMap_ok ctMap_ →
      ∃ (n : word64), val_ = .Litv (.Float64 n)) ∧
    (type_v tvs ctMap_ tenvS val_ (Ttup ts) ∧ ctMap_ok ctMap_ →
      ∃ (vs : List v), val_ = .Conv none vs ∧ ts.length = vs.length) ∧
    (type_v tvs ctMap_ tenvS val_ (Tfn t1 t2) ∧ ctMap_ok ctMap_ →
      (∃ (env : sem_env) (n : varN) (e : exp), val_ = .Closure env n e) ∨
      (∃ (env : sem_env) (funs : List (varN × varN × exp)) (n : varN),
        val_ = .Recclosure env funs n)) ∧
    (type_v tvs ctMap_ tenvS val_ (Tref t1) ∧ ctMap_ok ctMap_ ∧ type_s ctMap_ envS tenvS →
      ∃ (n : Nat) (v2 : v),
        val_ = .Loc true n ∧ store_lookup n envS = some (.Refv v2) ∧
        type_v 0 ctMap_ tenvS v2 t1) ∧
    (type_v tvs ctMap_ tenvS val_ Tword8array ∧ ctMap_ok ctMap_ ∧ type_s ctMap_ envS tenvS →
      ∃ (n : Nat) (ws : List word8),
        val_ = .Loc true n ∧ store_lookup n envS = some (.W8array ws) ∧
        Finmap.FLOOKUP tenvS n = some .W8array_t) ∧
    (type_v tvs ctMap_ tenvS val_ (Tarray t) ∧ ctMap_ok ctMap_ ∧ type_s ctMap_ envS tenvS →
      ∃ (n : Nat) (vs : List v),
        val_ = .Loc true n ∧ store_lookup n envS = some (.Varray vs) ∧
        (∀ (v_ : v), v_ ∈ vs → type_v 0 ctMap_ tenvS v_ t) ∧
        Finmap.FLOOKUP tenvS n = some (.Varray_t t)) ∧
    (type_v tvs ctMap_ tenvS val_ (Tvector t) ∧ ctMap_ok ctMap_ →
      ∃ (vs : List v),
        val_ = .Vectorv vs ∧ (∀ (v_ : v), v_ ∈ vs → type_v tvs ctMap_ tenvS v_ t)) := by
  intro tvs c s val_ envS ts t1 t2 t
  refine ⟨fun h => canon_Tint h.1 h.2, fun h => canon_Tchar h.1 h.2, fun h => canon_Tstring h.1 h.2,
    fun h => canon_Tword8 h.1 h.2, fun h => canon_Tword64 h.1 h.2, fun h => canon_Tdouble h.1 h.2,
    ?_, fun h => canon_Tfn h.1 h.2, ?_, ?_, ?_, fun h => canon_Tvector h.1 h.2⟩
  · intro h
    obtain ⟨vs, e, hr⟩ := canon_Ttup h.1 h.2
    exact ⟨vs, e, (LIST_REL_length hr).symm⟩
  · intro ⟨h, hc, hs⟩
    obtain ⟨n, e, hl⟩ := canon_Tref h hc
    obtain ⟨v2, h1, h2⟩ := type_s_Ref hs hl
    exact ⟨n, v2, e, h1, h2⟩
  · intro ⟨h, hc, hs⟩
    obtain ⟨n, e, hl⟩ := canon_Tword8array h hc
    obtain ⟨ws, h1⟩ := type_s_W8 hs hl
    exact ⟨n, ws, e, h1, hl⟩
  · intro ⟨h, hc, hs⟩
    obtain ⟨n, e, hl⟩ := canon_Tarray h hc
    obtain ⟨vs, h1, h2⟩ := type_s_Varray hs hl
    exact ⟨n, vs, e, h1, h2, hl⟩

theorem type_v_conv_some_intro {tvs : Nat} {c : ctMap} {s : tenv_store} {ts' : List sem_t}
    {tvs' : List tvarN} {vs : List v} {ts : List sem_t} {ti : type_ident} {stmp : stamp}
    (h1 : ∀ t', t' ∈ ts' → check_freevars tvs [] t') (h2 : tvs'.length = ts'.length)
    (h3 : LIST_REL (type_v tvs c s) vs (ts.map (type_subst (Finmap.alist_to_fmap (tvs'.zip ts')))))
    (h4 : Finmap.FLOOKUP c stmp = some (tvs', ts, ti)) :
    type_v tvs c s (.Conv (some stmp) vs) (.Tapp ts' ti) := by
  refine type_v.conv_some tvs c s ts' tvs' vs ts ti stmp h1 h2 ?_ ?_ h4
  · rw [FUPDATE_LIST_reverse_eq_alist_to_fmap]; exact LIST_REL_length h3
  · rw [FUPDATE_LIST_reverse_eq_alist_to_fmap]; exact LIST_REL_getElem h3

theorem type_v_conv_some_inv {tvs : Nat} {c : ctMap} {s : tenv_store} {ts' : List sem_t}
    {vs : List v} {ti : type_ident} {stmp : stamp}
    (h : type_v tvs c s (.Conv (some stmp) vs) (.Tapp ts' ti)) :
    ∃ tvs' ts, (∀ t', t' ∈ ts' → check_freevars tvs [] t') ∧ tvs'.length = ts'.length ∧
      LIST_REL (type_v tvs c s) vs (ts.map (type_subst (Finmap.alist_to_fmap (tvs'.zip ts')))) ∧
      Finmap.FLOOKUP c stmp = some (tvs', ts, ti) := by
  cases h
  rename_i tvs' ts h2 h1 h3 h4 h5
  rw [FUPDATE_LIST_reverse_eq_alist_to_fmap] at h3 h4
  exact ⟨tvs', ts, h1, h2, LIST_REL_of_getElem h3 h4, h5⟩

theorem type_v_Tapp_conv {tvs : Nat} {c : ctMap} {s : tenv_store} {ts' : List sem_t}
    {val_ : v} {ti : type_ident}
    (h : type_v tvs c s val_ (.Tapp ts' ti)) (hp : prim_type_nums.elem ti = false) :
    ∃ stmp vs, val_ = .Conv (some stmp) vs := by
  cases h <;> first
    | exact ⟨_, _, rfl⟩
    | exact absurd hp (by decide)
    | (have := (recclosure_Tfn ‹type_funs _ _ _ _› ‹ALOOKUP _ _ = some _›).1
       subst this; exact absurd hp (by decide))

theorem same_type_refl' : ∀ (t : stamp), same_type t t := by
  intro t; cases t <;> simp [same_type]

theorem same_type_TypeStamp {stmp : stamp} {cn : conN} {n : Nat}
    (h : same_type stmp (.TypeStamp cn n) = true) : ∃ cn', stmp = .TypeStamp cn' n := by
  cases stmp with
  | TypeStamp cn' m => simp [same_type] at h; exact ⟨cn', by rw [h]⟩
  | ExnStamp m => simp [same_type] at h

theorem ctMap_ok_same_type {c : ctMap} {s1 s2 : stamp} {tvs1 tvs2 : List tvarN} {ts1 ts2 : List sem_t}
    {ti : type_ident} (hc : ctMap_ok c)
    (h1 : Finmap.FLOOKUP c s1 = some (tvs1, ts1, ti)) (h2 : Finmap.FLOOKUP c s2 = some (tvs2, ts2, ti)) :
    same_type s1 s2 = true :=
  hc.2.2.2 s1 tvs1 ts1 ti s2 tvs2 ts2 ⟨h1, h2⟩

theorem canon_Tbool {tvs : Nat} {c : ctMap} {s : tenv_store} {val_ : v}
    (h : type_v tvs c s val_ Tbool) (hc : ctMap_ok c) (hb : ctMap_has_bools c) :
    ∃ b, val_ = Boolv b := by
  obtain ⟨hT, hF, hN⟩ := hb
  obtain ⟨stmp, vs, rfl⟩ := type_v_Tapp_conv h (by decide)
  obtain ⟨tvs', ts, _, _, hr, h5⟩ := type_v_conv_some_inv h
  obtain ⟨cn, rfl⟩ := same_type_TypeStamp (ctMap_ok_same_type hc h5 hT)
  by_cases e1 : cn = mlstring.strlit "True"
  · subst e1
    rw [hT] at h5
    simp only [Option.some.injEq, Prod.mk.injEq] at h5
    obtain ⟨rfl, rfl, _⟩ := h5
    simp [LIST_REL_nil_right] at hr
    subst hr
    exact ⟨true, by simp [Boolv]⟩
  · by_cases e2 : cn = mlstring.strlit "False"
    · subst e2
      rw [hF] at h5
      simp only [Option.some.injEq, Prod.mk.injEq] at h5
      obtain ⟨rfl, rfl, _⟩ := h5
      simp [LIST_REL_nil_right] at hr
      subst hr
      exact ⟨false, by simp [Boolv]⟩
    · rw [hN cn ⟨e1, e2⟩] at h5; simp at h5

theorem type_v_Boolv' {tvs : Nat} {c : ctMap} {s : tenv_store} (b : Bool)
    (hb : ctMap_has_bools c) : type_v tvs c s (Boolv b) Tbool := by
  obtain ⟨hT, hF, _⟩ := hb
  cases b
  · simp only [Boolv, Bool.false_eq_true, if_false]
    exact type_v_conv_some_intro (ts := []) (tvs' := []) (by simp) rfl (by simpa using LIST_REL.nil) hF
  · simp only [Boolv, if_true]
    exact type_v_conv_some_intro (ts := []) (tvs' := []) (by simp) rfl (by simpa using LIST_REL.nil) hT

theorem type_v_nil {tvs : Nat} {c : ctMap} {s : tenv_store} {t : sem_t}
    (hl : ctMap_has_lists c) (hf : check_freevars tvs [] t) :
    type_v tvs c s (.Conv (some (.TypeStamp (mlstring.strlit "[]") list_type_num)) []) (Tlist t) := by
  exact type_v_conv_some_intro (ts := []) (tvs' := [mlstring.strlit "'a"]) (by simpa using hf) rfl
    (by simpa using LIST_REL.nil) hl.1

theorem subst_a (t : sem_t) :
    type_subst (Finmap.alist_to_fmap ([mlstring.strlit "'a"].zip [t])) (.Tvar (mlstring.strlit "'a")) = t := by
  simp [type_subst, Finmap.alist_to_fmap, Finmap.FLOOKUP]

theorem subst_a_list (t : sem_t) :
    type_subst (Finmap.alist_to_fmap ([mlstring.strlit "'a"].zip [t])) (Tlist (.Tvar (mlstring.strlit "'a"))) = Tlist t := by
  simp [type_subst, Finmap.alist_to_fmap, Finmap.FLOOKUP, Tlist]

theorem type_v_cons {tvs : Nat} {c : ctMap} {s : tenv_store} {t : sem_t} {v1 v2 : v}
    (hl : ctMap_has_lists c) (hf : check_freevars tvs [] t)
    (h1 : type_v tvs c s v1 t) (h2 : type_v tvs c s v2 (Tlist t)) :
    type_v tvs c s (.Conv (some (.TypeStamp (mlstring.strlit "::") list_type_num)) [v1, v2]) (Tlist t) := by
  refine type_v_conv_some_intro (tvs' := [mlstring.strlit "'a"]) (by simpa using hf) rfl ?_ hl.2.1
  simp only [List.map_cons, List.map_nil, subst_a, subst_a_list]
  exact .cons _ _ _ _ h1 (.cons _ _ _ _ h2 .nil)

/-- inversion for list-typed values -/
theorem type_v_Tlist_inv {tvs : Nat} {c : ctMap} {s : tenv_store} {val_ : v} {t : sem_t}
    (h : type_v tvs c s val_ (Tlist t)) (hc : ctMap_ok c) (hl : ctMap_has_lists c) :
    val_ = .Conv (some (.TypeStamp (mlstring.strlit "[]") list_type_num)) [] ∨
    ∃ v1 v2, val_ = .Conv (some (.TypeStamp (mlstring.strlit "::") list_type_num)) [v1, v2] ∧
      type_v tvs c s v1 t ∧ type_v tvs c s v2 (Tlist t) := by
  obtain ⟨hN, hC, hO⟩ := hl
  obtain ⟨stmp, vs, rfl⟩ := type_v_Tapp_conv h (by decide)
  obtain ⟨tvs', ts, _, _, hr, h5⟩ := type_v_conv_some_inv h
  obtain ⟨cn, rfl⟩ := same_type_TypeStamp (ctMap_ok_same_type hc h5 hN)
  by_cases e1 : cn = mlstring.strlit "[]"
  · subst e1
    rw [hN] at h5
    simp only [Option.some.injEq, Prod.mk.injEq] at h5
    obtain ⟨rfl, rfl, _⟩ := h5
    simp [LIST_REL_nil_right] at hr
    exact .inl (by rw [hr])
  · by_cases e2 : cn = mlstring.strlit "::"
    · subst e2
      rw [hC] at h5
      simp only [Option.some.injEq, Prod.mk.injEq] at h5
      obtain ⟨rfl, rfl, _⟩ := h5
      simp only [List.map_cons, List.map_nil, subst_a, subst_a_list] at hr
      obtain ⟨v1, l1, rfl, hv1, hr⟩ := LIST_REL_cons_right.mp hr
      obtain ⟨v2, l2, rfl, hv2, hr⟩ := LIST_REL_cons_right.mp hr
      rw [LIST_REL_nil_right] at hr
      subst hr
      exact .inr ⟨v1, v2, rfl, hv1, hv2⟩
    · rw [hO cn ⟨e2, e1⟩] at h5; simp at h5

theorem has_lists_v_to_list_aux {c : ctMap} {tvs : Nat} {s : tenv_store} {t3 : sem_t}
    (hc : ctMap_ok c) (hl : ctMap_has_lists c) :
    ∀ (n : Nat) (val_ : v), sizeOf val_ ≤ n → type_v tvs c s val_ (Tlist t3) →
      ∃ (vs : List v),
        v_to_list val_ = some vs ∧
        (∀ (v_ : v), v_ ∈ vs → type_v tvs c s v_ t3) ∧
        (t3 = Tchar → ∃ (vs' : List Char), v_to_char_list val_ = some vs') ∧
        (t3 = Tstring → ∃ (str : mlstring), vs_to_string vs = some str) := by
  intro n
  induction n with
  | zero => intro val_ hs; cases val_ <;> simp at hs
  | succ n ih =>
    intro val_ hs h
    rcases type_v_Tlist_inv h hc hl with rfl | ⟨v1, v2, rfl, h1, h2⟩
    · exact ⟨[], by simp [v_to_list], by simp, fun _ => ⟨[], by simp [v_to_char_list]⟩,
        fun _ => by simp [vs_to_string]⟩
    · obtain ⟨vs, e1, e2, e3, e4⟩ := ih v2 (by simp at hs; omega) h2
      refine ⟨v1 :: vs, by simp [v_to_list, e1], ?_, ?_, ?_⟩
      · intro w hw
        rcases List.mem_cons.mp hw with rfl | hw
        · exact h1
        · exact e2 w hw
      · intro e
        subst e
        obtain ⟨ch, rfl⟩ := canon_Tchar h1 hc
        obtain ⟨cs, hcs⟩ := e3 rfl
        exact ⟨ch :: cs, by simp [v_to_char_list, hcs]⟩
      · intro e
        subst e
        obtain ⟨st, rfl⟩ := canon_Tstring h1 hc
        obtain ⟨str, hstr⟩ := e4 rfl
        simp [vs_to_string, hstr]

theorem has_lists_v_to_list' :
    ∀ (ctMap_ : ctMap) (tvs : Nat) (tenvS : tenv_store) (t3 : sem_t) (val_ : v),
      ctMap_ok ctMap_ ∧
      ctMap_has_lists ctMap_ ∧
      type_v tvs ctMap_ tenvS val_ (Tlist t3) →
      ∃ (vs : List v),
        v_to_list val_ = some vs ∧
        (∀ (v_ : v), v_ ∈ vs → type_v tvs ctMap_ tenvS v_ t3) ∧
        (t3 = Tchar → ∃ (vs' : List Char), v_to_char_list val_ = some vs') ∧
        (t3 = Tstring → ∃ (str : mlstring), vs_to_string vs = some str) :=
  fun _ _ _ _ val_ ⟨hc, hl, h⟩ => has_lists_v_to_list_aux hc hl _ val_ (Nat.le_refl _) h

theorem ctor_canonical_3 {tvs : Nat} {c : ctMap} {s : tenv_store} {val_ : v}
    {ts : List sem_t} {ti : type_ident} {stmp : stamp} {tvs' : List tvarN} {ts' : List sem_t}
    (h : type_v tvs c s val_ (.Tapp ts ti)) (hc : ctMap_ok c)
    (hl : Finmap.FLOOKUP c stmp = some (tvs', ts', ti)) :
    (∃ (cn : conN) (n : Nat) (vs : List v),
        same_type stmp (.TypeStamp cn n) ∧ val_ = .Conv (some (.TypeStamp cn n)) vs) ∨
      (∃ (n : Nat) (vs : List v),
        same_type stmp (.ExnStamp n) ∧ val_ = .Conv (some (.ExnStamp n)) vs) := by
  have hp : prim_type_nums.elem ti = false ∨ ti = Texn_num := by
    cases hpe : prim_type_nums.elem ti
    · exact .inl rfl
    · by_cases hne : ti = Texn_num
      · exact .inr hne
      · exact (ctMap_prim_absurd hc hl hpe hne).elim
  have hconv : ∃ stmp2 vs, val_ = .Conv (some stmp2) vs := by
    rcases hp with hp | rfl
    · exact type_v_Tapp_conv h hp
    · cases h <;> first
        | exact ⟨_, _, rfl⟩
        | (have := (recclosure_Tfn ‹type_funs _ _ _ _› ‹ALOOKUP _ _ = some _›).1
           exact absurd this (by decide))
  obtain ⟨stmp2, vs, rfl⟩ := hconv
  obtain ⟨_, _, _, _, _, h5⟩ := type_v_conv_some_inv h
  have hst := ctMap_ok_same_type hc hl h5
  cases stmp2 with
  | TypeStamp cn n => exact .inl ⟨cn, n, vs, hst, rfl⟩
  | ExnStamp n => exact .inr ⟨n, vs, hst, rfl⟩

theorem type_env_conv_thm' :
    ∀ (ctMap_ : ctMap) (envC : env_ctor) (tenvC : tenv_ctor),
      nsAll2 (type_ctor ctMap_) envC tenvC →
      ∀ (cn : cml_id modN conN) (tvs' : List tvarN) (ts : List sem_t) (tn : type_ident) (ti : type_ident),
        (nsLookup tenvC cn = some (tvs', ts, tn) →
          ∃ (cn' : conN) (stmp : stamp),
            nsLookup envC cn = some (ts.length, stmp) ∧
            Finmap.FLOOKUP ctMap_ stmp = some (tvs', ts, tn)) ∧
        (nsLookup tenvC cn = none → nsLookup envC cn = none) := by
  intro c envC tenvC ⟨h1, h2⟩ cn tvs' ts tn ti
  constructor
  · intro hl
    obtain ⟨⟨n, stmp⟩, hl2, hf, hlen⟩ := h2.1 cn _ hl
    simp only at hf hlen
    subst hlen
    exact ⟨default, stmp, hl2, hf⟩
  · intro hl
    cases hl2 : nsLookup envC cn with
    | none => rfl
    | some x =>
      obtain ⟨y, hy, _⟩ := h1.1 cn x hl2
      rw [hl] at hy; simp at hy

theorem type_funs_fst' :
    ∀ (tenv : type_env) (tenvE : tenv_val_exp) (funs : List (varN × varN × exp))
      (tenv' : List (varN × sem_t)),
      type_funs tenv tenvE funs tenv' →
      funs.map Prod.fst = tenv'.map Prod.fst := by
  intro tenv tenvE funs
  induction funs with
  | nil => intro tenv' h; cases h; rfl
  | cons a funs ih =>
    intro tenv' h
    cases h
    simp [ih _ ‹type_funs _ _ _ _›]

theorem EVERY_LIST_REL_local' {α β : Type} :
    ∀ (f : α → β → Prop) (y : β) (l : List α),
      (∀ (x : α), x ∈ l → f x y) ↔ LIST_REL (fun x y => f x y) l (REPLICATE l.length y) := by
  intro f y l
  exact (LIST_REL_replicate (R := fun x y => f x y)).symm

theorem do_eq_list_ok : ∀ (vs1 vs2 : List v),
    (∀ i, i < vs1.length → i < vs2.length → do_eq vs1[i]! vs2[i]! ≠ .Eq_type_error) →
    do_eq_list vs1 vs2 ≠ .Eq_type_error := by
  intro vs1
  induction vs1 with
  | nil => intro vs2 _; cases vs2 <;> simp [do_eq_list]
  | cons a vs1 ih =>
    intro vs2 h
    cases vs2 with
    | nil => simp [do_eq_list]
    | cons b vs2 =>
      simp only [do_eq_list]
      have h0 := h 0 (by simp) (by simp)
      simp at h0
      split
      · split
        · simp
        · exact ih vs2 (fun i h1 h2 => by simpa using h (i+1) (by simpa using h1) (by simpa using h2))
      · rename_i he; exact absurd he h0

macro "recc_absurd" hc:ident : tactic => `(tactic|
  (have hTfn := (recclosure_Tfn ‹type_funs _ _ _ _› ‹ALOOKUP _ _ = some _›).1
   subst hTfn
   exact (ctMap_prim_absurd $hc ‹Finmap.FLOOKUP _ _ = some _› (by decide) (by decide)).elim))

theorem eq_same_type_1 {c : ctMap} (hc : ctMap_ok c) {tvs : Nat} {s : tenv_store} :
    ∀ {v1 : v} {t : sem_t}, type_v tvs c s v1 t → ∀ {v2 : v}, type_v tvs c s v2 t →
      do_eq v1 v2 ≠ .Eq_type_error := by
  intro v1 t h1
  induction h1 with
  | conv_some tvs c s ts' tvs' vs ts ti stmp h1 h2 h3 h4 h5 ih =>
    intro v2 hv2
    have : (∃ stmp2 vs2, v2 = .Conv (some stmp2) vs2) := by
      cases hv2 <;> first | exact ⟨_, _, rfl⟩ | canon_absurd hc | recc_absurd hc
    obtain ⟨stmp2, vs2, rfl⟩ := this
    obtain ⟨tvs2', ts2, _, _, hr, h5'⟩ := type_v_conv_some_inv hv2
    rw [FUPDATE_LIST_reverse_eq_alist_to_fmap] at ih h3
    have hst := ctMap_ok_same_type hc h5 h5'
    simp only [do_eq]
    split
    · rename_i hcond
      simp only [Bool.and_eq_true, beq_iff_eq, Option.some.injEq] at hcond
      obtain ⟨rfl, hlen⟩ := hcond
      rw [h5] at h5'
      simp only [Option.some.injEq, Prod.mk.injEq] at h5'
      obtain ⟨rfl, rfl, _⟩ := h5'
      apply do_eq_list_ok
      intro i hi1 hi2
      exact ih i hi1 hc (LIST_REL_getElem hr i hi2)
    · simp [ctor_same_type, hst]
  | conv_none tvs c s vs ts h1 h2 ih =>
    intro v2 hv2
    obtain ⟨vs2, rfl, hr⟩ := canon_Ttup hv2 hc
    simp only [do_eq]
    split
    · apply do_eq_list_ok
      intro i hi1 hi2
      exact ih i hi1 hc (LIST_REL_getElem hr i hi2)
    · simp [ctor_same_type]
  | vectorv tvs c s t vs h1 h2 ih =>
    intro v2 hv2
    obtain ⟨vs2, rfl, hr⟩ := canon_Tvector hv2 hc
    simp only [do_eq]
    split
    · apply do_eq_list_ok
      intro i hi1 hi2
      have hm1 : vs[i]! ∈ vs := by simp [hi1]
      have hm2 : vs2[i]! ∈ vs2 := by simp [hi2]
      exact ih _ hm1 hc (hr _ hm2)
    · simp
  | _ =>
    intro v2 h2
    cases h2 <;> first
      | (simp [do_eq, lit_same_type]; done)
      | canon_absurd hc
      | recc_absurd hc

theorem eq_same_type' :
    (∀ (v1 v2 : v) (tvs : Nat) (ctMap_ : ctMap) (cns : env_ctor) (tenvS : tenv_store) (t : sem_t),
      ctMap_ok ctMap_ ∧
      type_v tvs ctMap_ tenvS v1 t ∧
      type_v tvs ctMap_ tenvS v2 t →
      do_eq v1 v2 ≠ .Eq_type_error) ∧
    (∀ (vs1 vs2 : List v) (tvs : Nat) (ctMap_ : ctMap) (cns : env_ctor) (tenvS : tenv_store) (ts : List sem_t),
      ctMap_ok ctMap_ ∧
      LIST_REL (type_v tvs ctMap_ tenvS) vs1 ts ∧
      LIST_REL (type_v tvs ctMap_ tenvS) vs2 ts →
      do_eq_list vs1 vs2 ≠ .Eq_type_error) := by
  refine ⟨fun v1 v2 tvs c _ s t ⟨hc, h1, h2⟩ => eq_same_type_1 hc h1 h2, ?_⟩
  intro vs1 vs2 tvs c _ s ts ⟨hc, h1, h2⟩
  apply do_eq_list_ok
  intro i hi1 hi2
  exact eq_same_type_1 hc (LIST_REL_getElem h1 i hi1) (LIST_REL_getElem h2 i hi2)

-- ============================================================
-- environments
-- ============================================================

theorem ALOOKUP_some_mem {α β : Type} [BEq α] [LawfulBEq α] {l : List (α × β)} {k : α} {x : β}
    (h : ALOOKUP l k = some x) : k ∈ l.map Prod.fst := by
  induction l with
  | nil => simp [ALOOKUP] at h
  | cons a l ih =>
    obtain ⟨a1, a2⟩ := a
    simp only [ALOOKUP] at h
    split at h
    · rename_i he; simp at he; simp [he]
    · simp [ih h]

theorem ALOOKUP_cons {α β : Type} [BEq α] (k k' : α) (x : β) (l : List (α × β)) :
    ALOOKUP ((k, x) :: l) k' = if k == k' then some x else ALOOKUP l k' := rfl

theorem nsAll2_expand {m n v1 v2 : Type} [BEq m] [LawfulBEq m] [BEq n] [LawfulBEq n]
    {R : cml_id m n → v1 → v2 → Prop} {e1 : «namespace» m n v1} {e2 : «namespace» m n v2}
    (h : nsAll2 R e1 e2) :
    (∀ id_, nsLookup e1 id_ = none ↔ nsLookup e2 id_ = none) ∧
    (∀ path, nsLookupMod e2 path = none → nsLookupMod e1 path = none) ∧
    (∀ path, nsLookupMod e1 path = none → nsLookupMod e2 path = none) ∧
    (∀ id_ a b, nsLookup e1 id_ = some a → nsLookup e2 id_ = some b → R id_ a b) := by
  refine ⟨fun id_ => nsAll2_nsLookup_none R e1 e2 id_ h, h.1.2, h.2.2, ?_⟩
  intro id_ a b ha hb
  obtain ⟨b', hb', hr⟩ := h.1.1 id_ a ha
  rw [hb] at hb'
  simp at hb'
  subst hb'
  exact hr

theorem nsAll2_of_expand {m n v1 v2 : Type} [BEq m] [BEq n]
    {R : cml_id m n → v1 → v2 → Prop} {e1 : «namespace» m n v1} {e2 : «namespace» m n v2}
    (h1 : ∀ id_, nsLookup e1 id_ = none ↔ nsLookup e2 id_ = none)
    (h2 : ∀ path, nsLookupMod e2 path = none → nsLookupMod e1 path = none)
    (h3 : ∀ path, nsLookupMod e1 path = none → nsLookupMod e2 path = none)
    (h4 : ∀ id_ a b, nsLookup e1 id_ = some a → nsLookup e2 id_ = some b → R id_ a b) :
    nsAll2 R e1 e2 := by
  refine ⟨⟨?_, h2⟩, ⟨?_, h3⟩⟩
  · intro id_ a ha
    cases hb : nsLookup e2 id_ with
    | none => rw [(h1 id_).mpr hb] at ha; simp at ha
    | some b => exact ⟨b, rfl, h4 id_ a b ha hb⟩
  · intro id_ b hb
    cases ha : nsLookup e1 id_ with
    | none => rw [(h1 id_).mp ha] at hb; simp at hb
    | some a => exact ⟨a, rfl, h4 id_ a b ha hb⟩

theorem type_v_recclosure_intro {tvs : Nat} {c : ctMap} {s : tenv_store} {tenv : type_env}
    {tenvE : tenv_val_exp} {env : sem_env} {n : varN} {funs : List (varN × varN × exp)}
    {bindings : List (varN × sem_t)} {t : sem_t}
    (h1 : tenv_ok tenv) (h2 : tenv_val_exp_ok tenvE) (h3 : num_tvs tenvE = 0)
    (h4 : type_all_env c s env { tenv with v := add_tenvE tenvE tenv.v })
    (h5 : type_funs tenv (bind_var_list 0 bindings (bind_tvar tvs tenvE)) funs bindings)
    (h6 : ALOOKUP bindings n = some t) (h7 : ALL_DISTINCT (funs.map Prod.fst))
    (h8 : n ∈ funs.map Prod.fst) :
    type_v tvs c s (.Recclosure env funs n) t := by
  obtain ⟨a, b, c', d⟩ := nsAll2_expand h4.2
  exact type_v.recclosure tvs c s tenv tenvE env n funs bindings t h1 h2 h3 h4.1 a b c' d h5 h6 h7 h8

theorem type_v_closure_intro {tvs : Nat} {c : ctMap} {s : tenv_store} {tenv : type_env}
    {tenvE : tenv_val_exp} {env : sem_env} {n : varN} {e : exp} {t1 t2 : sem_t}
    (h1 : tenv_ok tenv) (h2 : tenv_val_exp_ok tenvE) (h3 : num_tvs tenvE = 0)
    (h4 : type_all_env c s env { tenv with v := add_tenvE tenvE tenv.v })
    (h5 : check_freevars tvs [] t1)
    (h6 : type_e tenv (.Bind_name n 0 t1 (bind_tvar tvs tenvE)) e t2) :
    type_v tvs c s (.Closure env n e) (Tfn t1 t2) := by
  obtain ⟨a, b, c', d⟩ := nsAll2_expand h4.2
  exact type_v.closure tvs c s tenv tenvE env n e t1 t2 h1 h2 h3 h4.1 a b c' d h5 h6

theorem type_recfun_env_help' :
    ∀ (fn_ : varN) (funs funs' : List (varN × varN × exp)) (ctMap_ : ctMap)
      (tenv : type_env) (bindings : List (varN × sem_t)) (tenvE : tenv_val_exp)
      (env : sem_env) (tenvS : tenv_store) (tvs : Nat) (bindings' : List (varN × sem_t)),
      ALL_DISTINCT (funs'.map Prod.fst) ∧
      tenv_ok tenv ∧
      type_all_env ctMap_ tenvS env { tenv with v := add_tenvE tenvE tenv.v } ∧
      tenv_val_exp_ok tenvE ∧
      num_tvs tenvE = 0 ∧
      (∀ (fn_ : varN) (t : sem_t), ALOOKUP bindings fn_ = some t → ALOOKUP bindings' fn_ = some t) ∧
      type_funs tenv (bind_var_list 0 bindings' (bind_tvar tvs tenvE)) funs' bindings' ∧
      type_funs tenv (bind_var_list 0 bindings' (bind_tvar tvs tenvE)) funs bindings →
      LIST_REL (fun (p1 : varN × v) (p2 : varN × Nat × sem_t) =>
                  p1.1 = p2.1 ∧ type_v p2.2.1 ctMap_ tenvS p1.2 p2.2.2)
        (funs.map (fun (p : varN × varN × exp) => (p.1, v.Recclosure env funs' p.1)))
        (bindings.map (fun (p : varN × sem_t) => (p.1, tvs, p.2))) := by
  intro _ funs
  induction funs with
  | nil =>
    intro funs' c tenv bindings tenvE env s tvs bindings' ⟨_, _, _, _, _, _, _, h⟩
    cases h
    exact .nil
  | cons a funs ih =>
    intro funs' c tenv bindings tenvE env s tvs bindings' ⟨hd, hok, henv, hEok, hnum, hsub, hf', h⟩
    cases h
    rename_i fn n e t1 t2 bindings _ _ _ _
    have hfs : type_funs tenv (bind_var_list 0 bindings' (bind_tvar tvs tenvE)) funs bindings := by assumption
    have hnone : ALOOKUP bindings fn = none := by assumption
    simp only [List.map_cons]
    refine .cons _ _ _ _ ⟨rfl, ?_⟩ ?_
    · have hl : ALOOKUP bindings' fn = some (Tfn t1 t2) := hsub fn _ (by simp [ALOOKUP_cons])
      refine type_v_recclosure_intro hok hEok hnum henv hf' hl hd ?_
      rw [type_funs_fst' _ _ _ _ hf']
      exact ALOOKUP_some_mem hl
    · refine ih funs' c tenv bindings tenvE env s tvs bindings' ⟨hd, hok, henv, hEok, hnum, ?_, hf', hfs⟩
      intro fn' t hl
      apply hsub
      rw [ALOOKUP_cons]
      split
      · rename_i he; simp at he; subst he; rw [hnone] at hl; simp at hl
      · exact hl

theorem type_recfun_env' :
    ∀ (funs : List (varN × varN × exp)) (ctMap_ : ctMap) (tenvS : tenv_store)
      (tvs : Nat) (tenv : type_env) (tenvE : tenv_val_exp) (env : sem_env)
      (bindings : List (varN × sem_t)),
      tenv_ok tenv ∧
      type_all_env ctMap_ tenvS env { tenv with v := add_tenvE tenvE tenv.v } ∧
      tenv_val_exp_ok tenvE ∧
      num_tvs tenvE = 0 ∧
      type_funs tenv (bind_var_list 0 bindings (bind_tvar tvs tenvE)) funs bindings ∧
      ALL_DISTINCT (funs.map Prod.fst) →
      LIST_REL (fun (p1 : varN × v) (p2 : varN × Nat × sem_t) =>
                  p1.1 = p2.1 ∧ type_v p2.2.1 ctMap_ tenvS p1.2 p2.2.2)
        (funs.map (fun (p : varN × varN × exp) => (p.1, v.Recclosure env funs p.1)))
        (bindings.map (fun (p : varN × sem_t) => (p.1, tvs, p.2))) := by
  intro funs c s tvs tenv tenvE env bindings ⟨h1, h2, h3, h4, h5, h6⟩
  exact type_recfun_env_help' default funs funs c tenv bindings tenvE env s tvs bindings
    ⟨h6, h1, h2, h3, h4, fun _ _ h => h, h5, h5⟩

theorem type_v_exn' :
    ∀ (tvs : Nat) (cenv : ctMap) (senv : tenv_store),
      ctMap_has_exns cenv →
      type_v tvs cenv senv (.Conv (some chr_stamp) []) Texn ∧
      type_v tvs cenv senv (.Conv (some subscript_stamp) []) Texn ∧
      type_v tvs cenv senv (.Conv (some bind_stamp) []) Texn ∧
      type_v tvs cenv senv (.Conv (some div_stamp) []) Texn := by
  intro tvs c s ⟨h1, h2, h3, h4⟩
  have key : ∀ stmp, Finmap.FLOOKUP c stmp = some ([], [], Texn_num) →
      type_v tvs c s (.Conv (some stmp) []) Texn := fun stmp h =>
    type_v_conv_some_intro (ts := []) (tvs' := []) (by simp) rfl (by simpa using LIST_REL.nil) h
  exact ⟨key _ h2, key _ h4, key _ h1, key _ h3⟩

theorem check_freevars_Tapp (n : Nat) (tvs : List mlstring) (ts : List sem_t) (tn : type_ident) :
    check_freevars n tvs (.Tapp ts tn) = true ↔ ∀ t, t ∈ ts → check_freevars n tvs t = true := by
  rw [check_freevars]
  simp

theorem type_all_env_of_expand {c : ctMap} {s : tenv_store} {env : sem_env} {tenv : type_env}
    {tenvE : tenv_val_exp}
    (h0 : nsAll2 (type_ctor c) (sem_env_c env) tenv.c)
    (h1 : ∀ (id_ : cml_id modN varN),
      (nsLookup (sem_env_v env) id_ = none ↔ nsLookup (add_tenvE tenvE tenv.v) id_ = none))
    (h2 : ∀ (path : List modN),
      nsLookupMod (add_tenvE tenvE tenv.v) path = none → nsLookupMod (sem_env_v env) path = none)
    (h3 : ∀ (path : List modN),
      nsLookupMod (sem_env_v env) path = none → nsLookupMod (add_tenvE tenvE tenv.v) path = none)
    (h4 : ∀ (id_ : cml_id modN varN) (val_ : v) (p : Nat × sem_t),
      nsLookup (sem_env_v env) id_ = some val_ →
      nsLookup (add_tenvE tenvE tenv.v) id_ = some p →
      type_v p.1 c s val_ p.2) :
    type_all_env c s env { tenv with v := add_tenvE tenvE tenv.v } :=
  ⟨h0, nsAll2_of_expand h1 h2 h3 h4⟩

theorem type_v_closure_inv {tvs : Nat} {c : ctMap} {s : tenv_store} {env : sem_env} {n : varN}
    {e : exp} {t : sem_t} (h : type_v tvs c s (.Closure env n e) t) :
    ∃ tenv tenvE t1 t2, t = Tfn t1 t2 ∧ tenv_ok tenv ∧ tenv_val_exp_ok tenvE ∧ num_tvs tenvE = 0 ∧
      type_all_env c s env { tenv with v := add_tenvE tenvE tenv.v } ∧ check_freevars tvs [] t1 ∧
      type_e tenv (.Bind_name n 0 t1 (bind_tvar tvs tenvE)) e t2 := by
  cases h
  rename_i tenv tenvE t1 t2 _ _ _ _ _ _ _ _ _ _
  exact ⟨tenv, tenvE, t1, t2, rfl, by assumption, by assumption, by assumption,
    type_all_env_of_expand (by assumption) (by assumption) (by assumption) (by assumption)
      (by assumption), by assumption, by assumption⟩

theorem type_v_recclosure_inv {tvs : Nat} {c : ctMap} {s : tenv_store} {env : sem_env} {n : varN}
    {funs : List (varN × varN × exp)} {t : sem_t} (h : type_v tvs c s (.Recclosure env funs n) t) :
    ∃ tenv tenvE bindings, tenv_ok tenv ∧ tenv_val_exp_ok tenvE ∧ num_tvs tenvE = 0 ∧
      type_all_env c s env { tenv with v := add_tenvE tenvE tenv.v } ∧
      type_funs tenv (bind_var_list 0 bindings (bind_tvar tvs tenvE)) funs bindings ∧
      ALOOKUP bindings n = some t ∧ ALL_DISTINCT (funs.map Prod.fst) ∧ n ∈ funs.map Prod.fst := by
  cases h
  rename_i tenv tenvE bindings _ _ _ _ _ _ _ _ _ _ _ _
  exact ⟨tenv, tenvE, bindings, by assumption, by assumption, by assumption,
    type_all_env_of_expand (by assumption) (by assumption) (by assumption) (by assumption)
      (by assumption), by assumption, by assumption, by assumption, by assumption⟩

theorem type_op_Opapp {ts : List sem_t} {t : sem_t} (h : type_op .Opapp ts t) :
    ∃ t2, ts = [Tfn t2 t, t2] := by
  match ts, h with
  | [t1, t2], h => simp [type_op] at h; exact ⟨t2, by rw [h]⟩

theorem fst3_eq : (fun (x : varN × varN × exp) => match x with | (f, _, _) => f) = Prod.fst := rfl

theorem opapp_type_sound' :
    ∀ (ctMap_ : ctMap) (tenvS : tenv_store) (vs : List v) (ts : List sem_t) (t : sem_t),
      ctMap_ok ctMap_ ∧
      type_op .Opapp ts t ∧
      LIST_REL (type_v 0 ctMap_ tenvS) vs ts →
      ∃ (env : sem_env) (e : exp) (tenv : type_env) (tenvE : tenv_val_exp),
        tenv_ok tenv ∧
        tenv_val_exp_ok tenvE ∧
        num_tvs tenvE = 0 ∧
        type_all_env ctMap_ tenvS env { tenv with v := add_tenvE tenvE tenv.v } ∧
        type_e tenv tenvE e t ∧
        do_opapp vs = some (env, e) := by
  intro c s vs ts t ⟨hc, hop, hr⟩
  obtain ⟨t2, rfl⟩ := type_op_Opapp hop
  obtain ⟨v1, l1, rfl, hv1, hr⟩ := LIST_REL_cons_right.mp hr
  obtain ⟨v2, l2, rfl, hv2, hr⟩ := LIST_REL_cons_right.mp hr
  rw [LIST_REL_nil_right] at hr
  subst hr
  rcases canon_Tfn hv1 hc with ⟨env, n, e, rfl⟩ | ⟨env, funs, n, rfl⟩
  · -- closure
    obtain ⟨tenv, tenvE, t1', t2', heq, h1, h2, h3, hall, h7, h8⟩ := type_v_closure_inv hv1
    simp only [Tfn, sem_t.Tapp.injEq, List.cons.injEq, and_true] at heq
    obtain ⟨rfl, rfl⟩ := heq
    rw [bind_tvar0] at h8
    refine ⟨.mk (nsBind n v2 env.v_) env.c, e, tenv, .Bind_name n 0 t2 tenvE, h1, ?_, ?_, ?_, h8, ?_⟩
    · simp only [tenv_val_exp_ok, h3]
      exact ⟨by simpa using h7, h2⟩
    · simpa [num_tvs] using h3
    · refine ⟨hall.1, ?_⟩
      exact nsAll2_nsBind _ n v2 (0, t2) _ _ ⟨hv2, hall.2⟩
    · simp [do_opapp]
  · -- recclosure
    obtain ⟨tenv, tenvE, bindings, h1, h2, h3, hall, hfuns, hlook, hdist, hmem⟩ :=
      type_v_recclosure_inv hv1
    rw [bind_tvar0] at hfuns
    obtain ⟨x, e, hfind⟩ := type_funs_find_recfun n bindings funs bindings default tenv _ _ ⟨hlook, hfuns⟩
    obtain ⟨he, hfv⟩ := type_recfun_lookup n funs x e tenv _ bindings 0 t2 t ⟨hfind, hfuns, hlook⟩
    rw [num_tvs_bind_var_list, h3] at hfv
    have hfv2 : check_freevars 0 [] t2 = true := by
      rw [Tfn, check_freevars_Tapp] at hfv
      exact hfv t2 (by simp)
    have hrec := type_recfun_env' funs c s 0 tenv tenvE env bindings
      ⟨h1, hall, h2, h3, by rw [bind_tvar0]; exact hfuns, hdist⟩
    refine ⟨.mk (nsBind x v2 (build_rec_env funs env env.v_)) env.c, e, tenv,
      .Bind_name x 0 t2 (bind_var_list 0 bindings tenvE), h1, ?_, ?_, ?_, he, ?_⟩
    · simp only [tenv_val_exp_ok, num_tvs_bind_var_list, h3]
      exact ⟨by simpa using hfv2,
        tenv_val_exp_ok_bvl_funs funs bindings tenv bindings tenv.v tenvE ⟨hfuns, h2⟩⟩
    · simpa [num_tvs, num_tvs_bind_var_list] using h3
    · refine ⟨hall.1, ?_⟩
      show nsAll2 _ (nsBind x v2 (build_rec_env funs env env.v_))
        (nsBind x (0, t2) (add_tenvE (bind_var_list 0 bindings tenvE) tenv.v))
      refine nsAll2_nsBind _ x v2 (0, t2) _ _ ⟨hv2, ?_⟩
      rw [build_rec_env_merge, nsAppend_to_nsBindList, add_tenvE_bvl]
      refine nsAll2_nsBindList _ _ _ _ _ ⟨?_, hall.2⟩
      exact hrec
    · have hd' : ALL_DISTINCT (funs.map fun (f, _, _) => f) = true := hdist
      simp [do_opapp, hd', hfind]

-- ============================================================
-- store typing
-- ============================================================

/-- copy of `store_type_extension` (which is defined in TypeSound.lean) -/
def ste (tenvS1 tenvS2 : tenv_store) : Prop :=
  ∃ tenvS',
    tenvS2 = Finmap.FUNION tenvS' tenvS1 ∧
    (∀ l, Finmap.FLOOKUP tenvS' l = none ∨ Finmap.FLOOKUP tenvS1 l = none)

theorem ste_weakS {s1 s2 : tenv_store} (h : ste s1 s2) : weakS s2 s1 := by
  obtain ⟨s', e, hd⟩ := h
  intro k x hk
  subst e
  rcases hd k with h | h
  · simp only [Finmap.FLOOKUP] at h
    simp [Finmap.FUNION, h, hk]
  · simp only [Finmap.FLOOKUP] at h
    rw [h] at hk; simp at hk

theorem ste_refl (s : tenv_store) : ste s s :=
  ⟨Finmap.FEMPTY, by funext k; simp [Finmap.FUNION, Finmap.FEMPTY], fun _ => .inl rfl⟩

theorem ste_trans {s1 s2 s3 : tenv_store} (h1 : ste s1 s2) (h2 : ste s2 s3) : ste s1 s3 := by
  obtain ⟨a, rfl, ha⟩ := h1
  obtain ⟨b, rfl, hb⟩ := h2
  refine ⟨Finmap.FUNION b a, ?_, ?_⟩
  · funext k
    simp only [Finmap.FUNION]
    cases b k <;> simp
  · intro l
    simp only [Finmap.FLOOKUP, Finmap.FUNION] at ha hb ⊢
    rcases ha l with h | h
    · rcases hb l with h' | h'
      · simp [h, h']
      · rw [h] at h'; simp only at h'; exact .inr h'
    · exact .inr h

theorem store_lookup_some_iff {α : Type} (l : Nat) (st : List (store_v α)) :
    (∃ x, store_lookup l st = some x) ↔ l < st.length := by
  simp only [store_lookup]
  split <;> simp_all

theorem type_sv_same_type {c : ctMap} {s : tenv_store} {sv1 sv2 : store_v v} {st : store_t}
    (h1 : type_sv c s sv1 st) (h2 : type_sv c s sv2 st) : store_v_same_type sv1 sv2 = true := by
  cases st <;> cases sv1 <;> simp [type_sv] at h1 <;> cases sv2 <;> simp [type_sv] at h2 <;>
    simp [store_v_same_type]

theorem store_assign_type_sound' :
    ∀ (ctMap_ : ctMap) (tenvS : tenv_store) (store_ : List (store_v v))
      (sv : store_v v) (st : store_t) (l : Nat),
      type_s ctMap_ store_ tenvS ∧
      Finmap.FLOOKUP tenvS l = some st ∧
      type_sv ctMap_ tenvS sv st →
      ∃ (store' : List (store_v v)),
        store_assign l sv store_ = some store' ∧
        type_s ctMap_ store' tenvS := by
  intro c s store_ sv st l ⟨hs, hl, hsv⟩
  obtain ⟨sv0, hl0, hsv0⟩ := type_s_lookup hs hl
  have hlt : l < store_.length := (store_lookup_some_iff l store_).mp ⟨sv0, hl0⟩
  have hel : EL l store_ = sv0 := by
    simp only [store_lookup, hlt, if_true, Option.some.injEq] at hl0; exact hl0
  refine ⟨LUPDATE sv l store_, ?_, ?_⟩
  · simp [store_assign, hlt, hel, type_sv_same_type hsv0 hsv]
  · intro l'
    obtain ⟨h1, h2⟩ := hs l'
    constructor
    · rw [h1, store_lookup_some_iff, store_lookup_some_iff]; simp [LUPDATE]
    · intro st' sv' ⟨hst', hsv'⟩
      simp only [store_lookup, LUPDATE, List.length_set, EL] at hsv'
      split at hsv'
      · rename_i hlt'
        simp only [Option.some.injEq] at hsv'
        by_cases e : l' = l
        · subst e
          rw [hl] at hst'
          simp at hst'; subst hst'
          simp [hlt] at hsv'
          subst hsv'
          exact hsv
        · have : (store_.set l sv)[l']! = store_[l']! := by
            simp [List.getElem!_eq_getElem?_getD, Ne.symm e]
          rw [this] at hsv'
          apply h2 st' sv' ⟨hst', ?_⟩
          rw [← hsv']
          simp [store_lookup, hlt', EL]
      · simp at hsv'

theorem store_alloc_type_sound' :
    ∀ (ctMap_ : ctMap) (tenvS : tenv_store) (store_ : List (store_v v))
      (sv : store_v v) (st : store_t),
      ctMap_ok ctMap_ ∧
      type_s ctMap_ store_ tenvS ∧
      type_sv ctMap_ tenvS sv st →
      ∃ (store' : List (store_v v)) (tenvS' : tenv_store) (n : Nat),
        ste tenvS tenvS' ∧
        store_alloc sv store_ = (store', n) ∧
        type_s ctMap_ store' tenvS' ∧
        Finmap.FLOOKUP tenvS' n = some st := by
  intro c s store_ sv st ⟨hc, hs, hsv⟩
  have hnone : s store_.length = none := by
    cases h : s store_.length with
    | none => rfl
    | some x =>
      have := ((hs store_.length).1.mp ⟨x, h⟩)
      rw [store_lookup_some_iff] at this
      omega
  let s1 : tenv_store := fun k => if k = store_.length then some st else none
  have hext : ste s (Finmap.FUNION s1 s) := by
    refine ⟨s1, rfl, ?_⟩
    intro l
    by_cases e : l = store_.length
    · subst e; exact .inr hnone
    · exact .inl (by simp [Finmap.FLOOKUP, s1, e])
  have hweak := ste_weakS hext
  refine ⟨store_ ++ [sv], Finmap.FUNION s1 s, store_.length, hext, rfl, ?_, ?_⟩
  · intro l
    obtain ⟨h1, h2⟩ := hs l
    constructor
    · rw [store_lookup_some_iff]
      by_cases e : l = store_.length
      · subst e
        simp [Finmap.FLOOKUP, Finmap.FUNION, s1]
      · have : (∃ st_1, Finmap.FLOOKUP (Finmap.FUNION s1 s) l = some st_1) ↔
            (∃ st_1, Finmap.FLOOKUP s l = some st_1) := by
          simp [Finmap.FLOOKUP, Finmap.FUNION, s1, e]
        rw [this, h1, store_lookup_some_iff]
        simp; omega
    · intro st' sv' ⟨hst', hsv'⟩
      by_cases e : l = store_.length
      · subst e
        simp [Finmap.FLOOKUP, Finmap.FUNION, s1] at hst'
        subst hst'
        simp [store_lookup, EL] at hsv'
        subst hsv'
        exact type_sv_weakening c s _ _ c _ ⟨hsv, weakCT_refl c, hweak⟩
      · simp [Finmap.FLOOKUP, Finmap.FUNION, s1, e] at hst'
        have hlt : l < store_.length := by
          have := (h1.mp ⟨st', hst'⟩)
          rwa [store_lookup_some_iff] at this
        simp [store_lookup, EL] at hsv'
        have hlt' : l < store_.length + 1 := by omega
        simp [hlt', List.getElem_append_left hlt] at hsv'
        refine type_sv_weakening c s _ _ c _ ⟨h2 st' sv' ⟨hst', ?_⟩, weakCT_refl c, hweak⟩
        simp [store_lookup, EL, hlt, hsv']
  · simp [Finmap.FLOOKUP, Finmap.FUNION, s1]

theorem v_to_list_list_to_v : ∀ (n : Nat) (x : v) (xs : List v), sizeOf x ≤ n →
    v_to_list x = some xs → list_to_v xs = x := by
  intro n
  induction n with
  | zero => intro x xs hs; cases x <;> simp at hs
  | succ n ih =>
    intro x xs hs h
    unfold v_to_list at h
    split at h
    · split at h
      · rename_i he; simp at he h; subst he; subst h; simp [list_to_v]
      · simp at h
    · split at h
      · rename_i stmp v1 v2 he
        simp at he; subst he
        cases h2 : v_to_list v2 with
        | none => simp [h2] at h
        | some vs =>
          simp [h2] at h
          subst h
          have := ih v2 vs (by simp at hs; omega) h2
          simp [list_to_v, this]
      · simp at h
    · simp at h

theorem type_v_list_to_v' :
    ∀ (n : Nat) (ctMap_ : ctMap) (tenvS : tenv_store) (x : v) (xs : List v) (t : sem_t),
      type_v n ctMap_ tenvS x t ∧
      v_to_list x = some xs →
      type_v n ctMap_ tenvS (list_to_v xs) t := by
  intro n c s x xs t ⟨h1, h2⟩
  rw [v_to_list_list_to_v _ x xs (Nat.le_refl _) h2]
  exact h1

theorem type_v_list_to_v_all {tvs : Nat} {c : ctMap} {s : tenv_store} {t : sem_t}
    (hl : ctMap_has_lists c) (hf : check_freevars tvs [] t) :
    ∀ (xs : List v), (∀ x, x ∈ xs → type_v tvs c s x t) → type_v tvs c s (list_to_v xs) (Tlist t) := by
  intro xs
  induction xs with
  | nil => intro _; exact type_v_nil hl hf
  | cons a xs ih =>
    intro h
    exact type_v_cons hl hf (h a (by simp)) (ih (fun x hx => h x (by simp [hx])))

theorem type_v_list_to_v_APPEND' :
    ∀ (ctMap_ : ctMap) (tenvS : tenv_store) (xs ys : List v) (t : sem_t),
      ctMap_has_lists ctMap_ ∧
      type_v 0 ctMap_ tenvS (list_to_v xs) (.Tapp [t] Tlist_num) ∧
      type_v 0 ctMap_ tenvS (list_to_v ys) (.Tapp [t] Tlist_num) →
      type_v 0 ctMap_ tenvS (list_to_v (xs ++ ys)) (.Tapp [t] Tlist_num) := by
  intro c s xs ys t ⟨hl, h1, h2⟩
  induction xs with
  | nil => simpa using h2
  | cons a xs ih =>
    simp only [list_to_v] at h1
    obtain ⟨tvs', ts, hfv, _, hr, h5⟩ := type_v_conv_some_inv h1
    rw [hl.2.1] at h5
    simp only [Option.some.injEq, Prod.mk.injEq] at h5
    obtain ⟨rfl, rfl, _⟩ := h5
    simp only [List.map_cons, List.map_nil, subst_a, subst_a_list] at hr
    obtain ⟨ha, hr⟩ := LIST_REL_cons_iff.mp hr
    obtain ⟨hxs, _⟩ := LIST_REL_cons_iff.mp hr
    exact type_v_cons hl (hfv t (by simp)) ha (ih hxs)

theorem do_eq_Boolv' : ∀ (b b' : Bool), do_eq (Boolv b) (Boolv b') = .Eq_val (b == b') := by
  intro b b'
  cases b <;> cases b' <;> simp [Boolv, do_eq, do_eq_list, ctor_same_type, same_type]

theorem prim_canonical_Boolv_cases' :
    ∀ (tvs : Nat) (ctMap_ : ctMap) (tenvS : tenv_store) (val_ : v),
      type_v tvs ctMap_ tenvS val_ (.Tapp [] Tbool_num) ∧
      ctMap_ok ctMap_ ∧
      ctMap_has_bools ctMap_ →
      val_ = Boolv true ∨ val_ = Boolv false := by
  intro tvs c s val_ ⟨h, hc, hb⟩
  obtain ⟨b, rfl⟩ := canon_Tbool h hc hb
  cases b <;> simp

theorem same_ctor_and_same_tid' :
    ∀ (stamp1 stamp2 : stamp),
      same_ctor stamp1 stamp2 ∧ same_type stamp1 stamp2 →
      stamp1 = stamp2 := by
  intro s1 s2 ⟨h, _⟩
  simpa [same_ctor] using h

theorem EVERY_REPLICATE' :
    ∀ (tvs : Nat) (ctMap_ : ctMap) (tenv : tenv_store) (t' : sem_t) (vs : List v),
      (∀ (x : v), x ∈ vs → type_v tvs ctMap_ tenv x t') ↔
      (∀ (x : v × sem_t), x ∈ vs.zip (REPLICATE vs.length t') → type_v tvs ctMap_ tenv x.1 x.2) := by
  intro tvs c s t' vs
  induction vs with
  | nil => simp [REPLICATE]
  | cons a vs ih =>
    simp only [REPLICATE] at ih
    simp only [List.mem_cons, forall_eq_or_imp, REPLICATE, List.length_cons, List.replicate_succ,
      List.zip_cons_cons, ih]

theorem type_all_env_extend' :
    ∀ (ctMap_ : ctMap) (tenvS : tenv_store) (env1 env2 : sem_env)
      (tenv1 tenv2 : type_env),
      type_all_env ctMap_ tenvS env1 tenv1 ∧
      type_all_env ctMap_ tenvS env2 tenv2 →
      type_all_env ctMap_ tenvS (extend_dec_env env1 env2)
        (extend_dec_tenv tenv1 tenv2) := by
  intro c s env1 env2 tenv1 tenv2 ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
  exact ⟨nsAll2_nsAppend _ _ _ _ _ ⟨h1, h3⟩, nsAll2_nsAppend _ _ _ _ _ ⟨h2, h4⟩⟩

theorem check_ctor_tenv_dups' :
    ∀ (tenvT : tenv_abbrev) (tds : type_def),
      check_ctor_tenv tenvT tds → EVERY check_dup_ctors tds := by
  intro tenvT tds
  induction tds with
  | nil => intro _; rfl
  | cons a tds ih =>
    obtain ⟨tvs, tn, ctors⟩ := a
    intro h
    simp only [check_ctor_tenv, Bool.and_eq_true] at h
    simp only [EVERY, List.all_cons, Bool.and_eq_true]
    exact ⟨h.1.1.1.1, ih h.2⟩

theorem type_sound_invariant_union' :
    ∀ {ffi : Type} (st : cml_state ffi) (env : sem_env) (ctMap_ : ctMap)
      (tenvS : tenv_store) (tids1 tids2 : Set type_ident) (tenv : type_env),
      type_sound_invariant st env ctMap_ tenvS (tids1 ∪ tids2) tenv →
      type_sound_invariant st env ctMap_ tenvS tids1 tenv := by
  intro ffi st env c s tids1 tids2 tenv ⟨h1, h2, ⟨h3, h3'⟩, h4, h5⟩
  exact ⟨h1, h2, ⟨fun x ⟨hx1, hx2⟩ => h3 x ⟨.inl hx1, hx2⟩, h3'⟩, h4, h5⟩

theorem lookup_var_sound' :
    ∀ (n : cml_id modN varN) (tvs : Nat) (tenvE : tenv_val_exp)
      (targs : List sem_t) (t : sem_t) (ctMap_ : ctMap) (tenvS : tenv_store)
      (env : sem_env) (tenv : type_env),
      lookup_var n (bind_tvar tvs tenvE) tenv = some (targs.length, t) ∧
      ctMap_ok ctMap_ ∧
      tenv_val_exp_ok tenvE ∧
      num_tvs tenvE = 0 ∧
      EVERY (check_freevars tvs []) targs ∧
      type_all_env ctMap_ tenvS env { tenv with v := add_tenvE tenvE tenv.v } →
      ∃ (val_ : v),
        nsLookup env.v_ n = some val_ ∧
        type_v tvs ctMap_ tenvS val_ (deBruijn_subst 0 targs t) := by
  intro n tvs tenvE targs t c s env tenv ⟨hl, hc, hok, hnum, hta, hall⟩
  have key : nsLookup (add_tenvE tenvE tenv.v) n = some (targs.length, t) := by
    simp only [lookup_var] at hl
    split at hl
    · rename_i x hx
      simp only [Option.some.injEq] at hl
      subst hl
      cases n with
      | Short x =>
        simp only [lookup_varE] at hx
        rw [bind_tvar_rewrites.2.2.2.2.2.1] at hx
        have hx0 := (tveLookup_no_tvs (0 + tvs) _ tenvE x t ⟨hok, hnum⟩).mp hx
        have hfv := tveLookup_freevars_thm x 0 tenvE _ t ⟨hok, hnum, hx0⟩
        exact nsLookup_add_tenvE1 tenvE tenv.v x 0 t _ ⟨hfv, hx0⟩
      | Long mn id => simp [lookup_varE] at hx
    · rename_i hx
      cases n with
      | Short x =>
        simp only [lookup_varE] at hx
        rw [bind_tvar_rewrites.2.2.2.2.2.1] at hx
        exact nsLookup_add_tenvE2 tenvE tenv.v x (0 + tvs) t _ ⟨hx, hl⟩
      | Long mn id => exact nsLookup_add_tenvE3 tenvE tenv.v id t _ mn hl
  obtain ⟨val_, hv1, hv2⟩ := nsAll2_nsLookup2 _ _ _ n _ ⟨key, hall.2⟩
  refine ⟨val_, hv1, ?_⟩
  simp only at hv2
  exact type_subst_thm targs tvs _ c s val_ t hv2 ⟨rfl, hc, hta, type_v_freevars _ _ _ _ _ hv2⟩

theorem build_conv_type_sound' :
    ∀ (envC : env_ctor) (cn : cml_id modN conN) (vs : List v) (tvs : Nat)
      (ts : List sem_t) (ctMap_ : ctMap) (tenvS : tenv_store) (ts' : List sem_t)
      (tn : type_ident) (tenvC : tenv_ctor) (tvs' : List tvarN)
      (tenvE : tenv_val_exp) (l : Nat),
      nsAll2 (type_ctor ctMap_) envC tenvC ∧
      do_con_check envC (some cn) l ∧
      num_tvs tenvE = 0 ∧
      EVERY (check_freevars (num_tvs (bind_tvar tvs tenvE)) []) ts' ∧
      tvs'.length = ts'.length ∧
      LIST_REL (type_v tvs ctMap_ tenvS) vs
        (ts.map (type_subst (Finmap.alist_to_fmap (tvs'.zip ts')))).reverse ∧
      nsLookup tenvC cn = some (tvs', ts, tn) →
      ∃ (val_ : v),
        build_conv envC (some cn) vs.reverse = some val_ ∧
        type_v tvs ctMap_ tenvS val_ (.Tapp ts' tn) := by
  intro envC cn vs tvs ts c s ts' tn tenvC tvs' tenvE l ⟨hall, _, hnum, hfv, hlen, hr, hl⟩
  obtain ⟨_, stmp, h1, h2⟩ := (type_env_conv_thm' c envC tenvC hall cn tvs' ts tn tn).1 hl
  refine ⟨.Conv (some stmp) vs.reverse, by simp [build_conv, h1], ?_⟩
  refine type_v_conv_some_intro ?_ hlen ?_ h2
  · rw [bind_tvar_rewrites.2.1, hnum] at hfv
    simpa [EVERY] using hfv
  · have := LIST_REL_reverse hr
    simpa using this

abbrev bindR (tvs : Nat) (c : ctMap) (s : tenv_store) : (varN × v) → (varN × sem_t) → Prop :=
  fun p1 p2 => p1.1 = p2.1 ∧ type_v tvs c s p1.2 p2.2

theorem pmatch_lit_ok (cenv : env_ctor) (st : store v) (l l' : lit) (env : alist varN v)
    (h : lit_same_type l l' = true) :
    pmatch cenv st (.Plit l) (.Litv l') env = .No_match ∨
    pmatch cenv st (.Plit l) (.Litv l') env = .Match env := by
  simp only [pmatch]
  split
  · exact .inr rfl
  · simp [h]

mutual
theorem pat_sound1 : ∀ {tvs : Nat} {tenv : type_env} {p : pat} {t : sem_t} {nb : List (varN × sem_t)},
    type_p tvs tenv p t nb →
    ∀ (cenv : env_ctor) (st : store v) (val_ : v) (bindings : List (varN × v)) (c : ctMap)
      (tbindings : List (varN × sem_t)) (s : tenv_store),
      ctMap_ok c → nsAll2 (type_ctor c) cenv tenv.c → type_v tvs c s val_ t → type_s c st s →
      LIST_REL (bindR tvs c s) bindings tbindings →
      pmatch cenv st p val_ bindings = .No_match ∨
      ∃ bindings', pmatch cenv st p val_ bindings = .Match bindings' ∧
        LIST_REL (bindR tvs c s) bindings' (nb ++ tbindings)
  | _, _, _, _, _, .pany .., cenv, st, val_, bindings, c, tb, s, hc, hall, hv, hs, hb => by
    exact .inr ⟨bindings, by simp [pmatch], by simpa using hb⟩
  | _, _, _, _, _, .pvar _ _ n t _, cenv, st, val_, bindings, c, tb, s, hc, hall, hv, hs, hb => by
    exact .inr ⟨(n, val_) :: bindings, by simp [pmatch], .cons _ _ _ _ ⟨rfl, hv⟩ hb⟩
  | _, _, _, _, _, .plit_int _ _ n, cenv, st, val_, bindings, c, tb, s, hc, hall, hv, hs, hb => by
    obtain ⟨m, rfl⟩ := canon_Tint hv hc
    rcases pmatch_lit_ok cenv st (.IntLit n) (.IntLit m) bindings rfl with h | h
    · exact .inl h
    · exact .inr ⟨bindings, h, by simpa using hb⟩
  | _, _, _, _, _, .plit_char _ _ n, cenv, st, val_, bindings, c, tb, s, hc, hall, hv, hs, hb => by
    obtain ⟨m, rfl⟩ := canon_Tchar hv hc
    rcases pmatch_lit_ok cenv st (.Char n) (.Char m) bindings rfl with h | h
    · exact .inl h
    · exact .inr ⟨bindings, h, by simpa using hb⟩
  | _, _, _, _, _, .plit_str _ _ n, cenv, st, val_, bindings, c, tb, s, hc, hall, hv, hs, hb => by
    obtain ⟨m, rfl⟩ := canon_Tstring hv hc
    rcases pmatch_lit_ok cenv st (.StrLit n) (.StrLit m) bindings rfl with h | h
    · exact .inl h
    · exact .inr ⟨bindings, h, by simpa using hb⟩
  | _, _, _, _, _, .plit_word8 _ _ n, cenv, st, val_, bindings, c, tb, s, hc, hall, hv, hs, hb => by
    obtain ⟨m, rfl⟩ := canon_Tword8 hv hc
    rcases pmatch_lit_ok cenv st (.Word8 n) (.Word8 m) bindings rfl with h | h
    · exact .inl h
    · exact .inr ⟨bindings, h, by simpa using hb⟩
  | _, _, _, _, _, .plit_word64 _ _ n, cenv, st, val_, bindings, c, tb, s, hc, hall, hv, hs, hb => by
    obtain ⟨m, rfl⟩ := canon_Tword64 hv hc
    rcases pmatch_lit_ok cenv st (.Word64 n) (.Word64 m) bindings rfl with h | h
    · exact .inl h
    · exact .inr ⟨bindings, h, by simpa using hb⟩
  | _, _, _, _, _, .pcon_some tvs tenv cn ps ts' tvs' ts tn nb h1 h2 h3 h4, cenv, st, val_, bindings, c, tb, s, hc, hall, hv, hs, hb => by
    obtain ⟨_, stmp, hl1, hl2⟩ := (type_env_conv_thm' c cenv tenv.c hall cn tvs' ts tn tn).1 h4
    have hconv : ∃ stmp2 vs, val_ = .Conv (some stmp2) vs := by
      rcases ctor_canonical_3 hv hc hl2 with ⟨cn', n, vs, _, rfl⟩ | ⟨n, vs, _, rfl⟩
      · exact ⟨_, _, rfl⟩
      · exact ⟨_, _, rfl⟩
    obtain ⟨stmp2, vs, rfl⟩ := hconv
    obtain ⟨tvs2, ts2, _, _, hr, hl3⟩ := type_v_conv_some_inv hv
    have hst := ctMap_ok_same_type hc hl2 hl3
    have hlen : ps.length = ts.length := by
      simpa using type_ps_length _ _ _ _ _ h3
    simp only [pmatch, hl1, hst, hlen, beq_self_eq_true, Bool.and_self, if_true]
    by_cases hsc : same_ctor stmp stmp2 = true
    · simp only [hsc, if_true]
      simp only [same_ctor, beq_iff_eq] at hsc
      subst hsc
      rw [hl2] at hl3
      simp only [Option.some.injEq, Prod.mk.injEq] at hl3
      obtain ⟨rfl, rfl, _⟩ := hl3
      have hlen2 : vs.length = ts.length := by simpa using LIST_REL_length hr
      simp only [hlen2, beq_self_eq_true, if_true]
      exact pat_sound2 h3 cenv st vs bindings c tb s hc hall hr hs hb
    · simp [hsc]
  | _, _, _, _, _, .pcon_none tvs tenv ps ts nb h, cenv, st, val_, bindings, c, tb, s, hc, hall, hv, hs, hb => by
    obtain ⟨vs, rfl, hr⟩ := canon_Ttup hv hc
    have hlen : ps.length = vs.length := by
      rw [type_ps_length _ _ _ _ _ h, LIST_REL_length hr]
    simp only [pmatch, hlen, beq_self_eq_true, if_true]
    exact pat_sound2 h cenv st vs bindings c tb s hc hall hr hs hb
  | _, _, _, _, _, .pref tvs tenv p t nb h, cenv, st, val_, bindings, c, tb, s, hc, hall, hv, hs, hb => by
    obtain ⟨n, rfl, hl⟩ := canon_Tref hv hc
    obtain ⟨v2, hl2, hv2⟩ := type_s_Ref hs hl
    simp only [pmatch, hl2]
    refine pat_sound1 h cenv st v2 bindings c tb s hc hall ?_ hs hb
    exact type_v_weakening 0 c s v2 t hv2 tvs c s ⟨.inl rfl, weakCT_refl c, weakS_refl s⟩
  | _, _, _, _, _, .pas tvs tenv p t nb i h, cenv, st, val_, bindings, c, tb, s, hc, hall, hv, hs, hb => by
    simp only [pmatch]
    have := pat_sound1 h cenv st val_ ((i, val_) :: bindings) c ((i, t) :: tb) s hc hall hv hs
      (.cons _ _ _ _ ⟨rfl, hv⟩ hb)
    simpa using this
  | _, _, _, _, _, .ptannot tvs tenv p t nb _ _ h, cenv, st, val_, bindings, c, tb, s, hc, hall, hv, hs, hb => by
    simp only [pmatch]
    exact pat_sound1 h cenv st val_ bindings c tb s hc hall hv hs hb
theorem pat_sound2 : ∀ {tvs : Nat} {tenv : type_env} {ps : List pat} {ts : List sem_t} {nb : List (varN × sem_t)},
    type_ps tvs tenv ps ts nb →
    ∀ (cenv : env_ctor) (st : store v) (vs : List v) (bindings : List (varN × v)) (c : ctMap)
      (tbindings : List (varN × sem_t)) (s : tenv_store),
      ctMap_ok c → nsAll2 (type_ctor c) cenv tenv.c → LIST_REL (type_v tvs c s) vs ts → type_s c st s →
      LIST_REL (bindR tvs c s) bindings tbindings →
      pmatch_list cenv st ps vs bindings = .No_match ∨
      ∃ bindings', pmatch_list cenv st ps vs bindings = .Match bindings' ∧
        LIST_REL (bindR tvs c s) bindings' (nb ++ tbindings)
  | _, _, _, _, _, .nil .., cenv, st, vs, bindings, c, tb, s, hc, hall, hv, hs, hb => by
    rw [LIST_REL_nil_right] at hv
    subst hv
    exact .inr ⟨bindings, by simp [pmatch_list], by simpa using hb⟩
  | _, _, _, _, _, .cons tvs tenv p t nb ps ts nb' h1 h2, cenv, st, vs, bindings, c, tb, s, hc, hall, hv, hs, hb => by
    obtain ⟨v1, vs', rfl, hv1, hvs⟩ := LIST_REL_cons_right.mp hv
    simp only [pmatch_list]
    rcases pat_sound1 h1 cenv st v1 bindings c tb s hc hall hv1 hs hb with h | ⟨b', h, hb'⟩
    · rw [h]
      rcases pat_sound2 h2 cenv st vs' bindings c tb s hc hall hvs hs hb with h' | ⟨b'', h', _⟩
      · simp [h']
      · simp [h']
    · rw [h]
      have := pat_sound2 h2 cenv st vs' b' c (nb ++ tb) s hc hall hvs hs hb'
      simpa using this
end

theorem pat_type_sound' :
    (∀ (cenv : env_ctor) (st : store v) (p : pat) (val_ : v)
       (bindings : List (varN × v)) (tenv : type_env) (ctMap_ : ctMap)
       (tbindings : List (varN × sem_t)) (t : sem_t)
       (new_tbindings : List (varN × sem_t)) (tenvS : tenv_store) (tvs : Nat),
      ctMap_ok ctMap_ ∧
      nsAll2 (type_ctor ctMap_) cenv tenv.c ∧
      type_v tvs ctMap_ tenvS val_ t ∧
      type_p tvs tenv p t new_tbindings ∧
      type_s ctMap_ st tenvS ∧
      LIST_REL (fun (p1 : varN × v) (p2 : varN × sem_t) =>
        p1.1 = p2.1 ∧ type_v tvs ctMap_ tenvS p1.2 p2.2) bindings tbindings →
      pmatch cenv st p val_ bindings = .No_match ∨
      ∃ (bindings' : List (varN × v)),
        pmatch cenv st p val_ bindings = .Match bindings' ∧
        LIST_REL (fun (p1 : varN × v) (p2 : varN × sem_t) =>
          p1.1 = p2.1 ∧ type_v tvs ctMap_ tenvS p1.2 p2.2) bindings'
          (new_tbindings ++ tbindings)) ∧
    (∀ (cenv : env_ctor) (st : store v) (ps : List pat) (vs : List v)
       (bindings : List (varN × v)) (tenv : type_env) (ctMap_ : ctMap)
       (tbindings : List (varN × sem_t)) (new_tbindings : List (varN × sem_t))
       (ts : List sem_t) (tenvS : tenv_store) (tvs : Nat),
      ctMap_ok ctMap_ ∧
      nsAll2 (type_ctor ctMap_) cenv tenv.c ∧
      LIST_REL (type_v tvs ctMap_ tenvS) vs ts ∧
      type_ps tvs tenv ps ts new_tbindings ∧
      type_s ctMap_ st tenvS ∧
      LIST_REL (fun (p1 : varN × v) (p2 : varN × sem_t) =>
        p1.1 = p2.1 ∧ type_v tvs ctMap_ tenvS p1.2 p2.2) bindings tbindings →
      pmatch_list cenv st ps vs bindings = .No_match ∨
      ∃ (bindings' : List (varN × v)),
        pmatch_list cenv st ps vs bindings = .Match bindings' ∧
        LIST_REL (fun (p1 : varN × v) (p2 : varN × sem_t) =>
          p1.1 = p2.1 ∧ type_v tvs ctMap_ tenvS p1.2 p2.2) bindings'
          (new_tbindings ++ tbindings)) :=
  ⟨fun cenv st _ val_ bindings _ c tb _ _ s _ ⟨h1, h2, h3, h4, h5, h6⟩ =>
      pat_sound1 h4 cenv st val_ bindings c tb s h1 h2 h3 h5 h6,
   fun cenv st _ vs bindings _ c tb _ _ s _ ⟨h1, h2, h3, h4, h5, h6⟩ =>
      pat_sound2 h4 cenv st vs bindings c tb s h1 h2 h3 h5 h6⟩

theorem every_exp_Raise (p : exp → Bool) (e : exp) :
    every_exp p (.Raise e) = (p (.Raise e) && every_exp p e) := by rw [every_exp]
theorem every_exp_Handle (p : exp → Bool) (e : exp) (pes : List (pat × exp)) :
    every_exp p (.Handle e pes) = true ↔
      p (.Handle e pes) = true ∧ every_exp p e = true ∧ ∀ pe, pe ∈ pes → every_exp p pe.2 = true := by
  rw [every_exp]; simp [and_assoc]
theorem every_exp_Lit (p : exp → Bool) (l : lit) : every_exp p (.Lit l) = p (.Lit l) := by rw [every_exp]
theorem every_exp_Con (p : exp → Bool) (cn : Option (cml_id modN conN)) (es : List exp) :
    every_exp p (.Con cn es) = true ↔ p (.Con cn es) = true ∧ ∀ e, e ∈ es → every_exp p e = true := by
  rw [every_exp]; simp
theorem every_exp_Var (p : exp → Bool) (n : cml_id modN varN) : every_exp p (.Var n) = p (.Var n) := by rw [every_exp]
theorem every_exp_Fun (p : exp → Bool) (x : varN) (e : exp) :
    every_exp p (.Fun x e) = (p (.Fun x e) && every_exp p e) := by rw [every_exp]
theorem every_exp_App (p : exp → Bool) (o : op) (es : List exp) :
    every_exp p (.App o es) = true ↔ p (.App o es) = true ∧ ∀ e, e ∈ es → every_exp p e = true := by
  rw [every_exp]; simp
theorem every_exp_Log (p : exp → Bool) (l : lop) (e1 e2 : exp) :
    every_exp p (.Log l e1 e2) = (p (.Log l e1 e2) && every_exp p e1 && every_exp p e2) := by rw [every_exp]
theorem every_exp_If (p : exp → Bool) (e1 e2 e3 : exp) :
    every_exp p (.If e1 e2 e3) = (p (.If e1 e2 e3) && every_exp p e1 && every_exp p e2 && every_exp p e3) := by
  rw [every_exp]
theorem every_exp_Mat (p : exp → Bool) (e : exp) (pes : List (pat × exp)) :
    every_exp p (.Mat e pes) = true ↔
      p (.Mat e pes) = true ∧ every_exp p e = true ∧ ∀ pe, pe ∈ pes → every_exp p pe.2 = true := by
  rw [every_exp]; simp [and_assoc]
theorem every_exp_Let (p : exp → Bool) (x : Option varN) (e1 e2 : exp) :
    every_exp p (.Let x e1 e2) = (p (.Let x e1 e2) && every_exp p e1 && every_exp p e2) := by rw [every_exp]
theorem every_exp_Letrec (p : exp → Bool) (funs : List (varN × varN × exp)) (e : exp) :
    every_exp p (.Letrec funs e) = true ↔
      p (.Letrec funs e) = true ∧ every_exp p e = true ∧ ∀ f, f ∈ funs → every_exp p f.2.2 = true := by
  rw [every_exp]; simp [and_assoc]
theorem every_exp_Tannot (p : exp → Bool) (e : exp) (a : ast_t) :
    every_exp p (.Tannot e a) = (p (.Tannot e a) && every_exp p e) := by rw [every_exp]
theorem every_exp_Lannot (p : exp → Bool) (e : exp) (a : locs) :
    every_exp p (.Lannot e a) = (p (.Lannot e a) && every_exp p e) := by rw [every_exp]

mutual
theorem con_check1 (c : ctMap) (envc : env_ctor) (tenv : type_env)
    (ha : nsAll2 (type_ctor c) envc tenv.c) :
    ∀ {tenvE : tenv_val_exp} {e : exp} {t : sem_t},
      type_e tenv tenvE e t →
      every_exp (one_con_check envc) e = true
  | _, _, _, .lit_int .. => by simp [every_exp_Lit, one_con_check]
  | _, _, _, .lit_char .. => by simp [every_exp_Lit, one_con_check]
  | _, _, _, .lit_str .. => by simp [every_exp_Lit, one_con_check]
  | _, _, _, .lit_word8 .. => by simp [every_exp_Lit, one_con_check]
  | _, _, _, .lit_word64 .. => by simp [every_exp_Lit, one_con_check]
  | _, _, _, .lit_float64 .. => by simp [every_exp_Lit, one_con_check]
  | _, _, _, .raise _ _ _ _ _ h => by
    simp [every_exp_Raise, one_con_check, con_check1 c envc tenv ha h]
  | _, _, _, .handle _ _ _ _ pes _ h1 _ _ _ he => by
    rw [every_exp_Handle]
    exact ⟨rfl, con_check1 c envc tenv ha h1, fun pe hpe => con_check1 c envc tenv ha (he pe hpe)⟩
  | _, _, _, .con_some _ _ cn es ts' tvs ts tn _ _ hes hl => by
    rw [every_exp_Con]
    refine ⟨?_, ?_⟩
    · obtain ⟨_, stmp, hl1, _⟩ := (type_env_conv_thm' c envc tenv.c ha cn tvs ts tn tn).1 hl
      have := type_es_length _ _ _ _ hes
      simp only [List.length_map] at this
      simp [one_con_check, do_con_check, hl1, this]
    · have := con_check2 c envc tenv ha hes
      simpa [EVERY] using this
  | _, _, _, .con_none _ _ _ _ hes => by
    rw [every_exp_Con]
    refine ⟨by simp [one_con_check, do_con_check], ?_⟩
    have := con_check2 c envc tenv ha hes
    simpa [EVERY] using this
  | _, _, _, .var .. => by simp [every_exp_Var, one_con_check]
  | _, _, _, .fun_ _ _ _ _ _ _ _ h => by
    simp [every_exp_Fun, one_con_check, con_check1 c envc tenv ha h]
  | _, _, _, .app _ _ _ _ _ _ hes _ _ => by
    rw [every_exp_App]
    refine ⟨rfl, ?_⟩
    have := con_check2 c envc tenv ha hes
    simpa [EVERY] using this
  | _, _, _, .log _ _ _ _ _ h1 h2 => by
    simp [every_exp_Log, one_con_check, con_check1 c envc tenv ha h1, con_check1 c envc tenv ha h2]
  | _, _, _, .if_ _ _ _ _ _ _ h1 h2 h3 => by
    simp [every_exp_If, one_con_check, con_check1 c envc tenv ha h1, con_check1 c envc tenv ha h2,
      con_check1 c envc tenv ha h3]
  | _, _, _, .mat _ _ _ _ _ pes _ h1 _ _ _ he => by
    rw [every_exp_Mat]
    exact ⟨rfl, con_check1 c envc tenv ha h1, fun pe hpe => con_check1 c envc tenv ha (he pe hpe)⟩
  | _, _, _, .let_ _ _ _ _ _ _ _ h1 h2 => by
    simp [every_exp_Let, one_con_check, con_check1 c envc tenv ha h1, con_check1 c envc tenv ha h2]
  | _, _, _, .letrec _ _ _ _ _ _ hf he => by
    rw [every_exp_Letrec]
    refine ⟨rfl, con_check1 c envc tenv ha he, ?_⟩
    have := con_check3 c envc tenv ha hf
    simpa [EVERY] using this
  | _, _, _, .tannot _ _ _ _ _ _ h => by
    simp [every_exp_Tannot, one_con_check, con_check1 c envc tenv ha h]
  | _, _, _, .lannot _ _ _ _ _ h => by
    simp [every_exp_Lannot, one_con_check, con_check1 c envc tenv ha h]
theorem con_check2 (c : ctMap) (envc : env_ctor) (tenv : type_env)
    (ha : nsAll2 (type_ctor c) envc tenv.c) :
    ∀ {tenvE : tenv_val_exp} {es : List exp} {ts : List sem_t},
      type_es tenv tenvE es ts →
      EVERY (every_exp (one_con_check envc)) es = true
  | _, _, _, .nil .. => rfl
  | _, _, _, .cons _ _ _ _ _ _ h1 h2 => by
    have a := con_check1 c envc tenv ha h1
    have b := con_check2 c envc tenv ha h2
    simp only [EVERY, List.all_cons, Bool.and_eq_true] at b ⊢
    exact ⟨a, b⟩
theorem con_check3 (c : ctMap) (envc : env_ctor) (tenv : type_env)
    (ha : nsAll2 (type_ctor c) envc tenv.c) :
    ∀ {tenvE : tenv_val_exp} {funs : List (varN × varN × exp)}
      {env_ : List (varN × sem_t)},
      type_funs tenv tenvE funs env_ →
      EVERY (fun (p : varN × varN × exp) => every_exp (one_con_check envc) p.2.2) funs = true
  | _, _, _, .nil .. => rfl
  | _, _, _, .cons _ _ _ _ _ _ _ _ _ _ h1 h2 _ => by
    have a := con_check1 c envc tenv ha h1
    have b := con_check3 c envc tenv ha h2
    simp only [EVERY, List.all_cons, Bool.and_eq_true] at b ⊢
    exact ⟨a, b⟩
end

end DAux

/-
  HOL4 Prelude - Library shim providing HOL4 primitives not in Lean stdlib.
  This module defines types and functions that serve as Lean counterparts
  for standard HOL4 library constructs.
-/

import Init.Data.List.Perm
import Batteries.Data.List.Basic

-- ============================================================
-- Set type (not in Lean 4 stdlib, normally from Mathlib)
-- ============================================================

def Set (α : Type) := α → Prop

namespace Set

instance {α : Type} : Membership α (Set α) := ⟨fun s a => s a⟩

def empty {α : Type} : Set α := fun _ => False
instance {α : Type} : EmptyCollection (Set α) := ⟨empty⟩

def univ {α : Type} : Set α := fun _ => True

def insert {α : Type} (a : α) (s : Set α) : Set α := fun x => x = a ∨ s x

def union {α : Type} (s1 s2 : Set α) : Set α := fun x => s1 x ∨ s2 x
instance {α : Type} : Union (Set α) := ⟨union⟩

def inter {α : Type} (s1 s2 : Set α) : Set α := fun x => s1 x ∧ s2 x
instance {α : Type} : Inter (Set α) := ⟨inter⟩

def sdiff {α : Type} (s1 s2 : Set α) : Set α := fun x => s1 x ∧ ¬s2 x
instance {α : Type} : SDiff (Set α) := ⟨sdiff⟩

def image {α β : Type} (f : α → β) (s : Set α) : Set β := fun b => ∃ a, s a ∧ f a = b

def sUnion {α : Type} (ss : Set (Set α)) : Set α := fun x => ∃ s, ss s ∧ s x

def Disjoint {α : Type} (s1 s2 : Set α) : Prop := ∀ x, ¬(s1 x ∧ s2 x)

def subset {α : Type} (s1 s2 : Set α) : Prop := ∀ x, s1 x → s2 x
instance {α : Type} : HasSubset (Set α) := ⟨subset⟩

end Set

-- Notation for set operations
notation:65 f " '' " s => Set.image f s
notation "⋃₀ " ss => Set.sUnion ss
notation "{" a "}" => Set.insert a Set.empty

namespace HOL4

-- ============================================================
-- Basic list operations
-- ============================================================

/- HOL4: ALOOKUP -/
def ALOOKUP {α β : Type} [BEq α] : List (α × β) → α → Option β
  | [], _ => none
  | (k, v) :: rest, key => if k == key then some v else ALOOKUP rest key

/- HOL4: LUPDATE -/
def LUPDATE {α : Type} (x : α) (n : Nat) (l : List α) : List α :=
  l.set n x

/- HOL4: EL n l - element at index n -/
def EL {α : Type} [Inhabited α] (n : Nat) (l : List α) : α :=
  l[n]!

/- HOL4: TAKE -/
def TAKE {α : Type} (n : Nat) (l : List α) : List α :=
  l.take n

/- HOL4: DROP -/
def DROP {α : Type} (n : Nat) (l : List α) : List α :=
  l.drop n

/- HOL4: GENLIST f n -/
def GENLIST {α : Type} (f : Nat → α) (n : Nat) : List α :=
  (List.range n).map f

/- HOL4: ZIP -/
def ZIP {α β : Type} : List α × List β → List (α × β)
  | (l1, l2) => l1.zip l2

/- HOL4: UNZIP -/
def UNZIP {α β : Type} : List (α × β) → List α × List β
  | [] => ([], [])
  | (a, b) :: rest =>
    let (as_, bs) := UNZIP rest
    (a :: as_, b :: bs)

/- HOL4: EVERY -/
def EVERY {α : Type} (P : α → Bool) (l : List α) : Bool :=
  l.all P

/- HOL4: EXISTS -/
def EXISTS_ {α : Type} (P : α → Bool) (l : List α) : Bool :=
  l.any P

/- HOL4: ALL_DISTINCT -/
def ALL_DISTINCT {α : Type} [BEq α] : List α → Bool
  | [] => true
  | x :: xs => !(xs.any (· == x)) && ALL_DISTINCT xs

/- HOL4: LIST_REL -/
inductive LIST_REL {α β : Type} (R : α → β → Prop) : List α → List β → Prop where
  | nil : LIST_REL R [] []
  | cons : ∀ (x : α) (y : β) (xs : List α) (ys : List β),
    R x y → LIST_REL R xs ys → LIST_REL R (x :: xs) (y :: ys)

/- HOL4: PERM - permutation relation. Translated as `List.Perm`. -/
def PERM {α : Type} [BEq α] (l1 l2 : List α) : Prop := List.Perm l1 l2

/- HOL4: REPLICATE -/
def REPLICATE {α : Type} (n : Nat) (x : α) : List α :=
  List.replicate n x

/- HOL4: FLAT -/
def FLAT {α : Type} (l : List (List α)) : List α :=
  l.flatten

/- HOL4: MAP2 -/
def MAP2 {α β γ : Type} (f : α → β → γ) : List α → List β → List γ
  | [], _ => []
  | _, [] => []
  | x :: xs, y :: ys => f x y :: MAP2 f xs ys

/- HOL4: FILTER -/
def FILTER {α : Type} (P : α → Bool) (l : List α) : List α :=
  l.filter P

/- HOL4: nub (remove duplicates) -/
def nub {α : Type} [BEq α] : List α → List α
  | [] => []
  | x :: xs => if xs.any (· == x) then nub xs else x :: nub xs

/- HOL4: MEM -/
def MEM {α : Type} [BEq α] (x : α) (l : List α) : Bool :=
  l.any (· == x)

/- HOL4: SNOC -/
def SNOC {α : Type} (x : α) (l : List α) : List α :=
  l ++ [x]

/- HOL4: REVERSE -/
def REVERSE {α : Type} (l : List α) : List α :=
  l.reverse

/- HOL4: IS_PREFIX l1 l2 means "l2 is a prefix of l1" (l2 ≼ l1) -/
def IS_PREFIX {α : Type} [BEq α] (l1 l2 : List α) : Bool :=
  l2.isPrefixOf l1

/- HOL4: oEL n l - optional element at index n -/
def oEL {α : Type} (n : Nat) (l : List α) : Option α :=
  l[n]?

-- ============================================================
-- Option operations
-- ============================================================

/- HOL4: OPT_MMAP -/
def OPT_MMAP {α β : Type} (f : α → Option β) : List α → Option (List β)
  | [] => some []
  | x :: xs => do
    let y ← f x
    let ys ← OPT_MMAP f xs
    return y :: ys

/- HOL4: IS_SOME -/
def IS_SOME {α : Type} : Option α → Bool
  | some _ => true
  | none => false

/- HOL4: IS_NONE -/
def IS_NONE {α : Type} : Option α → Bool
  | some _ => false
  | none => true

/- HOL4: THE -/
def THE {α : Type} [Inhabited α] : Option α → α
  | some x => x
  | none => default

-- ============================================================
-- Finite maps
-- Represented concretely as a partial function `α → Option β`.
-- HOL4's `('a, 'b) fmap` is set-theoretically a partial function with
-- finite support; in this development the finiteness side condition is
-- not required by any client, so we model the API using the underlying
-- partial function directly.
-- ============================================================

/- HOL4: ('a, 'b) fmap -/
def Finmap (α : Type) (β : Type) : Type := α → Option β

namespace Finmap

/- HOL4: FEMPTY -/
def FEMPTY {α β : Type} : Finmap α β := fun _ => none

/- HOL4: FLOOKUP -/
def FLOOKUP {α β : Type} (m : Finmap α β) (k : α) : Option β := m k

/- HOL4: FUPDATE — point update at key `kv.1`. Requires `BEq α` so the
   update is computable. -/
def FUPDATE {α β : Type} [BEq α] (m : Finmap α β) (kv : α × β) : Finmap α β :=
  fun x => if x == kv.1 then some kv.2 else m x

/- HOL4: FDOM -/
def FDOM {α β : Type} (m : Finmap α β) : Set α := fun a => (m a).isSome

/- HOL4: FRANGE -/
def FRANGE {α β : Type} (m : Finmap α β) : Set β := fun b => ∃ a, m a = some b

/- HOL4: FEVERY -/
def FEVERY {α β : Type} (P : α × β → Prop) (m : Finmap α β) : Prop :=
  ∀ k val_, m k = some val_ → P (k, val_)

/- HOL4: FUPDATE_LIST -/
def FUPDATE_LIST {α β : Type} [BEq α] (m : Finmap α β) (l : List (α × β)) : Finmap α β :=
  l.foldl FUPDATE m

/- HOL4: o_f (map over values) -/
def o_f {α β γ : Type} (f : β → γ) (m : Finmap α β) : Finmap α γ :=
  fun x => (m x).map f

/- HOL4: alist_to_fmap — earliest binding wins. -/
def alist_to_fmap {α β : Type} [BEq α] (l : List (α × β)) : Finmap α β :=
  fun k => (l.find? (fun p => k == p.1)).map Prod.snd

/- HOL4: SUBMAP -/
def SUBMAP {α β : Type} (m1 m2 : Finmap α β) : Prop :=
  ∀ k val_, m1 k = some val_ → m2 k = some val_

/- HOL4: FUNION (left-biased union) -/
def FUNION {α β : Type} (m1 m2 : Finmap α β) : Finmap α β :=
  fun x => match m1 x with
    | some v => some v
    | none => m2 x

end Finmap

-- ============================================================
-- Sptree (num-keyed maps)
-- HOL4's `'a spt` (src/finite_maps/sptreeScript.sml), ported as the same
-- datatype with the same functions. A key `k` sits at the root when `k = 0`,
-- otherwise in the left subtree (even `k`) or the right subtree (odd `k`)
-- under the key `(k - 1) / 2`. A key therefore has exactly one position,
-- and a tree cannot hold a key twice.
-- ============================================================

/- HOL4: Datatype: spt = LN | LS 'a | BN spt spt | BS spt 'a spt End -/
inductive Sptree (α : Type) : Type where
  | LN : Sptree α
  | LS : α → Sptree α
  | BN : Sptree α → Sptree α → Sptree α
  | BS : Sptree α → α → Sptree α → Sptree α
deriving Repr, Inhabited

namespace Sptree

/- HOL4:
Definition wf_def:
  (wf LN <=> T) /\
  (wf (LS a) <=> T) /\
  (wf (BN t1 t2) <=> wf t1 /\ wf t2 /\ ~(isEmpty t1 /\ isEmpty t2)) /\
  (wf (BS t1 a t2) <=> wf t1 /\ wf t2 /\ ~(isEmpty t1 /\ isEmpty t2))
End
-/
def wf {α : Type} : Sptree α → Prop
  | LN => True
  | LS _ => True
  | BN t1 t2 => wf t1 ∧ wf t2 ∧ ¬(t1 = LN ∧ t2 = LN)
  | BS t1 _ t2 => wf t1 ∧ wf t2 ∧ ¬(t1 = LN ∧ t2 = LN)

/- HOL4:
Definition lookup_def:
  (lookup k LN = NONE) /\
  (lookup k (LS a) = if k = 0 then SOME a else NONE) /\
  (lookup k (BN t1 t2) =
     if k = 0 then NONE
     else lookup ((k - 1) DIV 2) (if EVEN k then t1 else t2)) /\
  (lookup k (BS t1 a t2) =
     if k = 0 then SOME a
     else lookup ((k - 1) DIV 2) (if EVEN k then t1 else t2))
End
   The conditional on the subtree is pushed outside the recursive call
   (`if EVEN k then lookup _ t1 else lookup _ t2`), which is the same
   function and lets Lean see structural recursion on the tree. -/
def lookup {α : Type} (k : Nat) : Sptree α → Option α
  | LN => none
  | LS a => if k = 0 then some a else none
  | BN t1 t2 =>
      if k = 0 then none
      else if k % 2 = 0 then lookup ((k - 1) / 2) t1 else lookup ((k - 1) / 2) t2
  | BS t1 a t2 =>
      if k = 0 then some a
      else if k % 2 = 0 then lookup ((k - 1) / 2) t1 else lookup ((k - 1) / 2) t2

/- HOL4:
Definition insert_def:
  (insert k a LN = if k = 0 then LS a
                     else if EVEN k then BN (insert ((k-1) DIV 2) a LN) LN
                     else BN LN (insert ((k-1) DIV 2) a LN)) /\
  (insert k a (LS a') =
     if k = 0 then LS a
     else if EVEN k then BS (insert ((k-1) DIV 2) a LN) a' LN
     else BS LN a' (insert ((k-1) DIV 2) a LN)) /\
  (insert k a (BN t1 t2) =
     if k = 0 then BS t1 a t2
     else if EVEN k then BN (insert ((k - 1) DIV 2) a t1) t2
     else BN t1 (insert ((k - 1) DIV 2) a t2)) /\
  (insert k a (BS t1 a' t2) =
     if k = 0 then BS t1 a t2
     else if EVEN k then BS (insert ((k - 1) DIV 2) a t1) a' t2
     else BS t1 a' (insert ((k - 1) DIV 2) a t2))
End
-/
def insert {α : Type} (k : Nat) (a : α) : Sptree α → Sptree α
  | LN =>
      if k = 0 then LS a
      else if k % 2 = 0 then BN (insert ((k - 1) / 2) a LN) LN
      else BN LN (insert ((k - 1) / 2) a LN)
  | LS a' =>
      if k = 0 then LS a
      else if k % 2 = 0 then BS (insert ((k - 1) / 2) a LN) a' LN
      else BS LN a' (insert ((k - 1) / 2) a LN)
  | BN t1 t2 =>
      if k = 0 then BS t1 a t2
      else if k % 2 = 0 then BN (insert ((k - 1) / 2) a t1) t2
      else BN t1 (insert ((k - 1) / 2) a t2)
  | BS t1 a' t2 =>
      if k = 0 then BS t1 a t2
      else if k % 2 = 0 then BS (insert ((k - 1) / 2) a t1) a' t2
      else BS t1 a' (insert ((k - 1) / 2) a t2)
termination_by t => (k, sizeOf t)
decreasing_by all_goals (apply Prod.Lex.left; omega)

/- HOL4:
Definition mk_BN_def:
  (mk_BN LN LN = LN) /\
  (mk_BN t1 t2 = BN t1 t2)
End
-/
def mk_BN {α : Type} : Sptree α → Sptree α → Sptree α
  | LN, LN => LN
  | t1, t2 => BN t1 t2

/- HOL4:
Definition mk_BS_def:
  (mk_BS LN x LN = LS x) /\
  (mk_BS t1 x t2 = BS t1 x t2)
End
-/
def mk_BS {α : Type} : Sptree α → α → Sptree α → Sptree α
  | LN, x, LN => LS x
  | t1, x, t2 => BS t1 x t2

/- HOL4:
Definition delete_def:
  (delete k LN = LN) /\
  (delete k (LS a) = if k = 0 then LN else LS a) /\
  (delete k (BN t1 t2) =
     if k = 0 then BN t1 t2
     else if EVEN k then
       mk_BN (delete ((k - 1) DIV 2) t1) t2
     else
       mk_BN t1 (delete ((k - 1) DIV 2) t2)) /\
  (delete k (BS t1 a t2) =
     if k = 0 then BN t1 t2
     else if EVEN k then
       mk_BS (delete ((k - 1) DIV 2) t1) a t2
     else
       mk_BS t1 a (delete ((k - 1) DIV 2) t2))
End
-/
def delete {α : Type} (k : Nat) : Sptree α → Sptree α
  | LN => LN
  | LS a => if k = 0 then LN else LS a
  | BN t1 t2 =>
      if k = 0 then BN t1 t2
      else if k % 2 = 0 then mk_BN (delete ((k - 1) / 2) t1) t2
      else mk_BN t1 (delete ((k - 1) / 2) t2)
  | BS t1 a t2 =>
      if k = 0 then BN t1 t2
      else if k % 2 = 0 then mk_BS (delete ((k - 1) / 2) t1) a t2
      else mk_BS t1 a (delete ((k - 1) / 2) t2)

/- HOL4:
Definition fromAList_def:
  (fromAList [] = LN) /\
  (fromAList ((x,y)::xs) = insert x y (fromAList xs))
End
-/
def fromAList {α : Type} : List (Nat × α) → Sptree α
  | [] => LN
  | (x, y) :: xs => insert x y (fromAList xs)

/- HOL4:
Definition domain_def:
  domain LN = {} /\
  domain (LS _) = {0} /\
  domain (BN t1 t2) =
     IMAGE (\n. 2 * n + 2) (domain t1) UNION
     IMAGE (\n. 2 * n + 1) (domain t2) /\
  domain (BS t1 _ t2) =
     {0} UNION IMAGE (\n. 2 * n + 2) (domain t1) UNION
     IMAGE (\n. 2 * n + 1) (domain t2)
End
-/
def domain {α : Type} : Sptree α → Set Nat
  | LN => ∅
  | LS _ => {0}
  | BN t1 t2 =>
      Set.image (fun n => 2 * n + 2) (domain t1) ∪ Set.image (fun n => 2 * n + 1) (domain t2)
  | BS t1 _ t2 =>
      ({0} ∪ Set.image (fun n => 2 * n + 2) (domain t1)) ∪
        Set.image (fun n => 2 * n + 1) (domain t2)

/- HOL4:
Definition toListA_def:
  (toListA acc LN = acc) /\
  (toListA acc (LS a) = a::acc) /\
  (toListA acc (BN t1 t2) = toListA (toListA acc t2) t1) /\
  (toListA acc (BS t1 a t2) = toListA (a :: toListA acc t2) t1)
End
-/
def toListA {α : Type} (acc : List α) : Sptree α → List α
  | LN => acc
  | LS a => a :: acc
  | BN t1 t2 => toListA (toListA acc t2) t1
  | BS t1 a t2 => toListA (a :: toListA acc t2) t1

/- HOL4: Definition toList_def: toList m = toListA [] m End -/
def toList {α : Type} (t : Sptree α) : List α := toListA [] t

/- HOL4:
Definition lrnext_def:
  lrnext n = if n = 0 then 1 else 2 * lrnext ((n - 1) DIV 2)
End
-/
def lrnext (n : Nat) : Nat := if n = 0 then 1 else 2 * lrnext ((n - 1) / 2)
termination_by n
decreasing_by omega

/- HOL4:
Definition foldi_def:
  (foldi f i acc LN = acc) /\
  (foldi f i acc (LS a) = f i a acc) /\
  (foldi f i acc (BN t1 t2) =
     let inc = lrnext i
     in
       foldi f (i + inc) (foldi f (i + 2 * inc) acc t1) t2) /\
  (foldi f i acc (BS t1 a t2) =
     let inc = lrnext i
     in
       foldi f (i + inc) (f i a (foldi f (i + 2 * inc) acc t1)) t2)
End
-/
def foldi {α β : Type} (f : Nat → α → β → β) (i : Nat) (acc : β) : Sptree α → β
  | LN => acc
  | LS a => f i a acc
  | BN t1 t2 =>
      let inc := lrnext i
      foldi f (i + inc) (foldi f (i + 2 * inc) acc t1) t2
  | BS t1 a t2 =>
      let inc := lrnext i
      foldi f (i + inc) (f i a (foldi f (i + 2 * inc) acc t1)) t2

/- HOL4: Definition toAList_def: toAList = foldi (\k v a. (k,v)::a) 0 [] End -/
def toAList {α : Type} (t : Sptree α) : List (Nat × α) := foldi (fun k v a => (k, v) :: a) 0 [] t

end Sptree

-- ============================================================
-- LazyList (potentially infinite lists)
-- HOL4's `'a llist` is a coinductive lazy list; we represent it as a
-- partial indexing function `Nat → Option α`, where a `none` at position
-- `n` indicates the list has ended by index `n`. (The intended invariant
-- is that `none` is downward-closed; this invariant is not enforced at
-- the type level but is preserved by `fromList`.)
-- ============================================================

/- HOL4: 'a llist -/
def LazyList (α : Type) : Type := Nat → Option α

namespace LazyList

open Classical

/- HOL4: LPREFIX l1 l2 — l1 is a prefix of l2. Every position present
   in l1 is present in l2 with the same value. -/
def LPREFIX {α : Type} (l1 l2 : LazyList α) : Prop :=
  ∀ n x, l1 n = some x → l2 n = some x

/- HOL4: fromList -/
def fromList {α : Type} (l : List α) : LazyList α := fun n => l[n]?

/- HOL4: toList — returns `some l` when the lazy list is finite (i.e.
   has a least index after which it is empty), otherwise `none`.
   Defined classically since the predicate is undecidable in general. -/
noncomputable def toList {α : Type} (ll : LazyList α) : Option (List α) :=
  if h : ∃ N, ∀ n, n ≥ N → ll n = none then
    let N := Classical.choose h
    some ((List.range N).filterMap ll)
  else
    none

end LazyList

-- ============================================================
-- Set operations
-- ============================================================

/- HOL4: DISJOINT -/
def DISJOINT {α : Type} (s1 s2 : Set α) : Prop :=
  Set.Disjoint s1 s2

/- HOL4: IMAGE -/
def IMAGE {α β : Type} (f : α → β) (s : Set α) : Set β :=
  Set.image f s

/- HOL4: BIGUNION -/
def BIGUNION {α : Type} (ss : Set (Set α)) : Set α :=
  Set.sUnion ss

/- HOL4: FINITE — there is a list enumerating exactly the elements of `s`. -/
def FINITE {α : Type} (s : Set α) : Prop :=
  ∃ l : List α, ∀ a, s a ↔ a ∈ l

/- HOL4: CARD — cardinality of a finite set. Defined classically: when
   `s` is enumerated by a duplicate-free list, returns the length of such a
   list (all such lists are permutations of each other, so this is
   well-defined); otherwise 0. -/
open Classical in
noncomputable def CARD {α : Type} (s : Set α) : Nat :=
  if h : ∃ l : List α, l.Nodup ∧ ∀ a, s a ↔ a ∈ l then
    (Classical.choose h).length
  else
    0

/- HOL4: BIJ f s t — f restricted to s is a bijection onto t. -/
def BIJ {α β : Type} (f : α → β) (s : Set α) (t : Set β) : Prop :=
  (∀ a, s a → t (f a)) ∧
  (∀ a1 a2, s a1 → s a2 → f a1 = f a2 → a1 = a2) ∧
  (∀ b, t b → ∃ a, s a ∧ f a = b)

/- HOL4: TOKENS — tokenize a list by a separator predicate, dropping
   empty groups. -/
def TOKENS {α : Type} [BEq α] (P : α → Bool) (l : List α) : List (List α) :=
  (l.splitOnP P).filter (fun g => !g.isEmpty)

-- ============================================================
-- Word types (opaque stubs)
-- ============================================================

/- HOL4: word8 -/
abbrev word8 := UInt8

/- HOL4: word64 -/
abbrev word64 := UInt64

/- HOL4: word_add, word_sub, etc. for word8 -/
def word_add_8 (a b : word8) : word8 := a + b
def word_sub_8 (a b : word8) : word8 := a - b
def word_and_8 (a b : word8) : word8 := a &&& b
def word_or_8 (a b : word8) : word8 := a ||| b
def word_xor_8 (a b : word8) : word8 := a ^^^ b
def word_lsl_8 (a : word8) (n : Nat) : word8 := a <<< n.toUInt8
def word_lsr_8 (a : word8) (n : Nat) : word8 := a >>> n.toUInt8
/- Arithmetic right shift: sign-extend. UInt8 has no native ASR; emulate
   by sign-extending the top bit. -/
def word_asr_8 (a : word8) (n : Nat) : word8 :=
  let signMask : word8 := if a &&& 0x80 != 0 then
      ((0xFF : word8) <<< (8 - min 8 n).toUInt8)
    else 0
  (a >>> n.toUInt8) ||| signMask
/- Rotate right. -/
def word_ror_8 (a : word8) (n : Nat) : word8 :=
  let m := n % 8
  (a >>> m.toUInt8) ||| (a <<< (8 - m).toUInt8)

/- HOL4: word_add, word_sub, etc. for word64 -/
def word_add_64 (a b : word64) : word64 := a + b
def word_sub_64 (a b : word64) : word64 := a - b
def word_and_64 (a b : word64) : word64 := a &&& b
def word_or_64 (a b : word64) : word64 := a ||| b
def word_xor_64 (a b : word64) : word64 := a ^^^ b
def word_lsl_64 (a : word64) (n : Nat) : word64 := a <<< n.toUInt64
def word_lsr_64 (a : word64) (n : Nat) : word64 := a >>> n.toUInt64
/- Arithmetic right shift on 64-bit. -/
def word_asr_64 (a : word64) (n : Nat) : word64 :=
  let signMask : word64 :=
    if a &&& 0x8000000000000000 != 0 then
      ((0xFFFFFFFFFFFFFFFF : word64) <<< (64 - min 64 n).toUInt64)
    else 0
  (a >>> n.toUInt64) ||| signMask
/- Rotate right on 64-bit. -/
def word_ror_64 (a : word64) (n : Nat) : word64 :=
  let m := n % 64
  (a >>> m.toUInt64) ||| (a <<< (64 - m).toUInt64)

/- HOL4: w2n -/
def w2n_8 (w : word8) : Nat := w.toNat
def w2n_64 (w : word64) : Nat := w.toNat

/- HOL4: n2w -/
def n2w_8 (n : Nat) : word8 := n.toUInt8
def n2w_64 (n : Nat) : word64 := n.toUInt64

/- HOL4: i2w — convert an integer to a machine word, taking the result
   modulo `2^width`. Negative integers are represented in two's complement. -/
def i2w_8 (i : Int) : word8 := (i % 256 + 256).toNat.toUInt8
def i2w_64 (i : Int) : word64 := (i % (2^64 : Int) + (2^64 : Int)).toNat.toUInt64

-- ============================================================
-- IEEE754 floating point (opaque stubs)
-- ============================================================

/- HOL4: fp64 ops — IEEE 754 binary64 operations. The HOL4 development
   models fp64 values as 64-bit words and operates on them through
   IEEE-aware functions. We delegate to Lean's `Float` (which is binary64)
   via `Float.ofBits` / `Float.toBits`. The rounding-mode argument is
   ignored (Lean uses round-to-nearest-even). -/
private def fpOfBits (a : word64) : Float := Float.ofBits a
private def fpToBits (f : Float) : word64 := f.toBits

def fp64_lessThan (a b : word64) : Bool := decide (fpOfBits a < fpOfBits b)
def fp64_lessEqual (a b : word64) : Bool := decide (fpOfBits a ≤ fpOfBits b)
def fp64_greaterThan (a b : word64) : Bool := decide (fpOfBits b < fpOfBits a)
def fp64_greaterEqual (a b : word64) : Bool := decide (fpOfBits b ≤ fpOfBits a)
def fp64_equal (a b : word64) : Bool := fpOfBits a == fpOfBits b
def fp64_abs (a : word64) : word64 := fpToBits (fpOfBits a).abs
def fp64_negate (a : word64) : word64 := fpToBits (-(fpOfBits a))
def fp64_sqrt (_rm : Unit) (a : word64) : word64 := fpToBits (fpOfBits a).sqrt
def fp64_add (_rm : Unit) (a b : word64) : word64 := fpToBits (fpOfBits a + fpOfBits b)
def fp64_sub (_rm : Unit) (a b : word64) : word64 := fpToBits (fpOfBits a - fpOfBits b)
def fp64_mul (_rm : Unit) (a b : word64) : word64 := fpToBits (fpOfBits a * fpOfBits b)
def fp64_div (_rm : Unit) (a b : word64) : word64 := fpToBits (fpOfBits a / fpOfBits b)
/- Note: this is not a true fused multiply-add (no FMA primitive in Lean
   core); we compute `a*b + c` with two roundings. This is a translation
   gap relative to HOL4's `fp64_mul_add` which uses a single FMA rounding. -/
def fp64_mul_add (_rm : Unit) (a b c : word64) : word64 :=
  fpToBits (fpOfBits a * fpOfBits b + fpOfBits c)
def roundTiesToEven : Unit := ()

-- ============================================================
-- Comparison type
-- ============================================================

/- HOL4: ordering (LESS | EQUAL | GREATER) -/
inductive ordering where
  | LESS
  | EQUAL
  | GREATER
deriving Repr, BEq, ReflBEq, LawfulBEq, Inhabited

-- ============================================================
-- Char operations
-- ============================================================

/- HOL4: ORD -/
def ORD (c : Char) : Nat := c.toNat

/- HOL4: CHR -/
def CHR (n : Nat) : Char := Char.ofNat n

-- ============================================================
-- FOLDR / FOLDL
-- ============================================================

/- HOL4: FOLDR -/
def FOLDR {α β : Type} (f : α → β → β) (b : β) (l : List α) : β :=
  l.foldr f b

/- HOL4: FOLDL -/
def FOLDL {α β : Type} (f : β → α → β) (b : β) (l : List α) : β :=
  l.foldl f b

/- HOL4: RTC (reflexive transitive closure) -/
inductive RTC {α : Type} (R : α → α → Prop) : α → α → Prop where
  | refl : ∀ (x : α), RTC R x x
  | step : ∀ (x y z : α), R x y → RTC R y z → RTC R x z

end HOL4

open HOL4

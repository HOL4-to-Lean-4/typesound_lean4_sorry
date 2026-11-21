/-
  Translation of mlstringScript.sml
  Pure functions for the String module.
  Defines mlstring as a separate type from string.
-/
import LeanTypeSound.HOL4Prelude
import LeanTypeSound.Misc
import LeanTypeSound.Mllist

open HOL4

/- HOL4:
Datatype:
  mlstring = strlit string
End
-/
inductive mlstring where
  | strlit : String → mlstring
deriving Repr, BEq, ReflBEq, LawfulBEq, Inhabited

/- HOL4:
Definition implode_def:
  implode = strlit
End
-/
def implode (s : String) : mlstring := .strlit s

/- HOL4:
Definition strlen_def[simp]:
  strlen (strlit s) = LENGTH s
End
-/
def strlen : mlstring → Nat
  | .strlit s => s.length

/- HOL4:
Definition strsub_def[simp]:
  strsub (strlit s) n = EL n s
End
-/
def strsub : mlstring → Nat → Char
  | .strlit s, n => s.toList[n]!

/- HOL4:
Definition concat_def:
  concat l = strlit (FLAT (MAP (λs. case s of strlit x => x) l))
End
-/
def concat (l : List mlstring) : mlstring :=
  .strlit (String.join (l.map fun | .strlit x => x))

/- HOL4:
Definition explode_aux_def[simp]:
  (explode_aux s n 0 = []) ∧
  (explode_aux s n (SUC len) = strsub s n :: (explode_aux s (n + 1) len))
End
-/
def explode_aux (s : mlstring) (n : Nat) : Nat → List Char
  | 0 => []
  | len + 1 => strsub s n :: explode_aux s (n + 1) len

/- HOL4:
Definition explode_def:
  explode s = explode_aux s 0 (strlen s)
End
-/
def explode (s : mlstring) : List Char :=
  explode_aux s 0 (strlen s)

/- HOL4:
Definition strcat_def:
  strcat s1 s2 = concat [s1; s2]
End
-/
def strcat (s1 s2 : mlstring) : mlstring :=
  concat [s1, s2]

/- HOL4:
Definition str_def:
  str (c: char) = implode [c]
End
-/
def str (c : Char) : mlstring :=
  implode (String.singleton c)

/- HOL4:
Definition tokens_aux_def: ...
End
-/
def tokens_aux (f : Char → Bool) (s : mlstring) : List Char → Nat → Nat → List mlstring
  | acc, _, 0 => match acc with
    | [] => []
    | _ => [implode (String.ofList acc.reverse)]
  | [], n, len + 1 =>
    if f (strsub s n) then tokens_aux f s [] (n + 1) len
    else tokens_aux f s [strsub s n] (n + 1) len
  | h :: t, n, len + 1 =>
    if f (strsub s n) then
      implode (String.ofList (h :: t).reverse) :: tokens_aux f s [] (n + 1) len
    else tokens_aux f s (strsub s n :: h :: t) (n + 1) len

/- HOL4:
Definition tokens_def:
  tokens f s = tokens_aux f s [] 0 (strlen s)
End
-/
def tokens (f : Char → Bool) (s : mlstring) : List mlstring :=
  tokens_aux f s [] 0 (strlen s)

/- HOL4:
Definition isStringThere_aux_def: ...
End
-/
def isStringThere_aux (s1 s2 : mlstring) (s1i s2i : Nat) : Nat → Bool
  | 0 => true
  | len + 1 =>
    if strsub s1 s1i == strsub s2 s2i then
      isStringThere_aux s1 s2 (s1i + 1) (s2i + 1) len
    else false

/- HOL4:
Definition isSubstring_aux_def: ...
End
-/
def isSubstring_aux (s1 s2 : mlstring) (lens1 n : Nat) : Nat → Bool
  | 0 => false
  | len + 1 =>
    if isStringThere_aux s1 s2 0 n lens1 then true
    else isSubstring_aux s1 s2 lens1 (n + 1) len

/- HOL4:
Definition isSubstring_def: ...
End
-/
def isSubstring (s1 s2 : mlstring) : Bool :=
  if strlen s1 ≤ strlen s2 then
    isSubstring_aux s1 s2 (strlen s1) 0 (strlen s2 - strlen s1 + 1)
  else false

/- HOL4:
Definition compare_aux_def: ...
End
-/
def compare_aux (s1 s2 : mlstring) (ord : ordering) (start : Nat) : Nat → ordering
  | 0 => ord
  | len + 1 =>
    if strsub s2 start < strsub s1 start then .GREATER
    else if strsub s1 start < strsub s2 start then .LESS
    else compare_aux s1 s2 ord (start + 1) len

/- HOL4:
Definition compare_def: ...
End
-/
def compare (s1 s2 : mlstring) : ordering :=
  if strlen s1 < strlen s2 then
    compare_aux s1 s2 .LESS 0 (strlen s1)
  else if strlen s2 < strlen s1 then
    compare_aux s1 s2 .GREATER 0 (strlen s2)
  else compare_aux s1 s2 .EQUAL 0 (strlen s2)

/- HOL4:
Definition mlstring_lt_def:
  mlstring_lt s1 s2 ⇔ (compare s1 s2 = LESS)
End
-/
def mlstring_lt (s1 s2 : mlstring) : Bool := compare s1 s2 == .LESS

/- HOL4:
Definition mlstring_le_def:
  mlstring_le s1 s2 ⇔ (compare s1 s2 ≠ GREATER)
End
-/
def mlstring_le (s1 s2 : mlstring) : Bool := !(compare s1 s2 == .GREATER)

/- HOL4:
Definition mlstring_gt_def:
  mlstring_gt s1 s2 ⇔ (compare s1 s2 = GREATER)
End
-/
def mlstring_gt (s1 s2 : mlstring) : Bool := compare s1 s2 == .GREATER

/- HOL4:
Definition mlstring_ge_def:
  mlstring_ge s1 s2 ⇔ (compare s1 s2 <> LESS)
End
-/
def mlstring_ge (s1 s2 : mlstring) : Bool := !(compare s1 s2 == .LESS)

/- HOL4:
Definition collate_aux_def: ...
End
-/
def collate_aux (f : Char → Char → ordering) (s1 s2 : mlstring) (ord : ordering) (n : Nat) :
    Nat → ordering
  | 0 => ord
  | len + 1 =>
    if f (strsub s1 n) (strsub s2 n) == .EQUAL then
      collate_aux f s1 s2 ord (n + 1) len
    else f (strsub s1 n) (strsub s2 n)

/- HOL4:
Definition collate_def:
  collate f s1 s2 = ...
End
-/
def mlstring_collate (f : Char → Char → ordering) (s1 s2 : mlstring) : ordering :=
  if strlen s1 < strlen s2 then
    collate_aux f s1 s2 .LESS 0 (strlen s1)
  else if strlen s2 < strlen s1 then
    collate_aux f s1 s2 .GREATER 0 (strlen s2)
  else collate_aux f s1 s2 .EQUAL 0 (strlen s2)

/- HOL4:
Datatype:
  app_list_ann = BigList ('a list)
               | BigAppend app_list_ann app_list_ann
               | Small ('a app_list)
End
-/
inductive app_list_ann (α : Type) where
  | BigList : List α → app_list_ann α
  | BigAppend : app_list_ann α → app_list_ann α → app_list_ann α
  | Small : app_list α → app_list_ann α

/- HOL4:
Definition char_to_word8_def[simp]:
  char_to_word8 (c:char) = n2w (ORD c) :word8
End
-/
def char_to_word8 (c : Char) : word8 := n2w_8 (ORD c)

/- HOL4:
Definition word8_to_char_def[simp]:
  word8_to_char (w:word8) = CHR (w2n w) : char
End
-/
def word8_to_char (w : word8) : Char := CHR (w2n_8 w)

/- HOL4:
Definition empty_ffi_def:
  empty_ffi (s:mlstring) = ()
End
-/
def empty_ffi (_ : mlstring) : Unit := ()

-- ============================================================
-- Theorem stubs
-- ============================================================

/- HOL4:
Theorem explode_aux_thm:
   ∀max n ls. (n + max = LENGTH ls) ⇒ (explode_aux (strlit ls) n max = DROP n ls)
   Note: HOL4 string = char list; Lean mlstring wraps String
-/
theorem explode_aux_thm (max n : Nat) (ls : String) :
    n + max = ls.data.length →
    explode_aux (.strlit ls) n max = HOL4.DROP n ls.data := by
  induction max generalizing n with
  | zero => intro h; simp [explode_aux, DROP]; show ls.toList.length ≤ n; show ls.data.length ≤ n; omega
  | succ k ih =>
    intro h
    simp only [explode_aux, strsub]
    rw [ih (n+1) (by omega)]
    show ls.toList[n]! :: List.drop (n+1) ls.toList = List.drop n ls.toList
    have hn : n < ls.toList.length := by show n < ls.data.length; omega
    rw [List.drop_eq_getElem_cons hn, getElem!_pos ls.toList n hn]
/- HOL4:
Theorem explode_thm[simp]:
   explode (strlit ls) = ls
-/
theorem explode_thm (ls : String) :
    explode (.strlit ls) = ls.data := by
  unfold explode
  rw [explode_aux_thm]
  · simp [DROP]
  · simp [strlen]; rfl
/- HOL4:
Theorem explode_implode[simp]:
   ∀x. explode (implode x) = x
-/
theorem explode_implode (x : String) :
    explode (implode x) = x.data := explode_thm x
/- HOL4:
Theorem implode_explode[simp]:
   ∀x. implode (explode x) = x
-/
theorem implode_explode (x : mlstring) :
    implode (String.ofList (explode x)) = x := by
  cases x with
  | strlit s => rw [explode_thm]; show mlstring.strlit (String.ofList s.toList) = _; rw [String.ofList_toList]
/- HOL4:
Theorem explode_11[simp]:
   ∀s1 s2. (explode s1 = explode s2) ⇔ (s1 = s2)
-/
theorem explode_11 (s1 s2 : mlstring) :
    explode s1 = explode s2 ↔ s1 = s2 := by
  constructor
  · intro h
    cases s1 with
    | strlit a =>
      cases s2 with
      | strlit b =>
        rw [explode_thm, explode_thm] at h
        have : a = b := String.toList_inj.mp h
        rw [this]
  · rintro rfl; rfl
theorem mlstring_explode_implode_ofList (l : List Char) :
    explode (implode (String.ofList l)) = l := by
  rw [explode_implode]; exact String.toList_ofList

theorem mlstring_go_shape {α : Type} (P : α → Bool) (rest : List α) :
    ∃ H T, List.splitOnP.go P rest [] = H :: T ∧
      ∀ acc, List.splitOnP.go P rest acc = (acc.reverse ++ H) :: T := by
  induction rest with
  | nil => exact ⟨[], [], by simp [List.splitOnP.go], by simp [List.splitOnP.go]⟩
  | cons a t ih =>
    obtain ⟨H, T, h1, h2⟩ := ih
    by_cases hP : P a = true
    · exact ⟨[], List.splitOnP.go P t [], by simp [List.splitOnP.go, hP], by simp [List.splitOnP.go, hP]⟩
    · refine ⟨a :: H, T, ?_, ?_⟩
      · simp [List.splitOnP.go, hP, h2]
      · intro acc; simp [List.splitOnP.go, hP, h2]

theorem mlstring_tokens_aux_go (P : Char → Bool) (s : String) :
    ∀ (len n : Nat) (ss : List Char), n + len = s.toList.length →
    (tokens_aux P (.strlit s) ss n len).map explode =
      (List.splitOnP.go P (s.toList.drop n) ss).filter (fun g => !g.isEmpty) := by
  intro len
  induction len with
  | zero =>
    intro n ss h
    rw [List.drop_eq_nil_iff.mpr (by omega)]
    cases ss with
    | nil => simp [tokens_aux, List.splitOnP.go]
    | cons a t =>
      simp only [tokens_aux, List.splitOnP.go, List.map_cons, List.map_nil, mlstring_explode_implode_ofList]
      simp
  | succ k ih =>
    intro n ss h
    have hn : n < s.toList.length := by omega
    rw [List.drop_eq_getElem_cons hn]
    have hsub : strsub (.strlit s) n = s.toList[n] := by simp only [strsub]; exact getElem!_pos s.toList n hn
    cases ss with
    | nil =>
      simp only [tokens_aux, List.splitOnP.go, hsub]
      by_cases hP : P s.toList[n] = true
      · simp only [hP, if_true]; rw [ih (n+1) [] (by omega)]; simp
      · simp only [hP, Bool.false_eq_true, if_false]; rw [ih (n+1) _ (by omega)]
    | cons a t =>
      simp only [tokens_aux, List.splitOnP.go, hsub]
      by_cases hP : P s.toList[n] = true
      · simp only [hP, if_true, List.map_cons, mlstring_explode_implode_ofList]; rw [ih (n+1) [] (by omega)]; simp
      · simp only [hP, Bool.false_eq_true, if_false]; rw [ih (n+1) _ (by omega)]

/- HOL4:
Theorem TOKENS_eq_tokens_aux:
   !P ls ss n len. (n + len = LENGTH (explode ls)) ==>
      (MAP explode (tokens_aux P ls ss n len) = case ss of
        | (h::t) => if (len <> 0) /\ (~ (P (EL n (explode ls)))) then
          (REVERSE (h::t) ++ HD (TOKENS P (DROP n (explode ls))))
            :: TL (TOKENS P (DROP n (explode ls)))
           else if (len <> 0) then
              REVERSE (h::t) :: (TOKENS P (DROP n (explode ls)))
           else [REVERSE(h::t)]
        | [] => (TOKENS P (DROP n (explode ls))))
-/
theorem TOKENS_eq_tokens_aux (P : Char → Bool) (ls : mlstring) (ss : List Char)
    (n len : Nat) :
    n + len = (explode ls).length →
    (tokens_aux P ls ss n len).map explode =
    match ss with
    | h :: t =>
      if len ≠ 0 ∧ ¬ P (HOL4.EL n (explode ls)) then
        ((h :: t).reverse ++ (HOL4.TOKENS P (HOL4.DROP n (explode ls))).head!) ::
          (HOL4.TOKENS P (HOL4.DROP n (explode ls))).tail
      else if len ≠ 0 then
        (h :: t).reverse :: HOL4.TOKENS P (HOL4.DROP n (explode ls))
      else [(h :: t).reverse]
    | [] => HOL4.TOKENS P (HOL4.DROP n (explode ls)) := by
  intro hlen
  cases ls with
  | strlit s =>
  rw [explode_thm] at hlen ⊢
  rw [mlstring_tokens_aux_go P s len n ss hlen]
  show _ = match ss with
    | h :: t =>
      if len ≠ 0 ∧ ¬ P (s.toList[n]!) then
        ((h :: t).reverse ++ (HOL4.TOKENS P (s.toList.drop n)).head!) ::
          (HOL4.TOKENS P (s.toList.drop n)).tail
      else if len ≠ 0 then
        (h :: t).reverse :: HOL4.TOKENS P (s.toList.drop n)
      else [(h :: t).reverse]
    | [] => HOL4.TOKENS P (s.toList.drop n)
  cases ss with
  | nil => rfl
  | cons h t =>
    simp only []
    cases len with
    | zero =>
      rw [List.drop_eq_nil_iff.mpr (by show s.toList.length ≤ n; show s.data.length ≤ n; omega)]
      simp [List.splitOnP.go]
    | succ k =>
      have hn : n < s.toList.length := by show n < s.data.length; omega
      rw [List.drop_eq_getElem_cons hn, getElem!_pos s.toList n hn]
      simp only [TOKENS, List.splitOnP, List.splitOnP.go]
      obtain ⟨H, T, h1, h2⟩ := mlstring_go_shape P (s.toList.drop (n+1))
      by_cases hP : P s.toList[n] = true
      · simp [hP]
      · simp [hP, h2]; rfl
/- HOL4:
Theorem TOKENS_eq_tokens:
   !P ls.(MAP explode (tokens P ls) = TOKENS P (explode ls))
-/
theorem TOKENS_eq_tokens (P : Char → Bool) (ls : mlstring) :
    (tokens P ls).map explode = HOL4.TOKENS P (explode ls) := by
  unfold tokens
  rw [TOKENS_eq_tokens_aux P ls [] 0 (strlen ls)]
  · simp [DROP]
  · cases ls with
    | strlit s => rw [explode_thm]; simp [strlen]; rfl

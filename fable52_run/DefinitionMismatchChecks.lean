import LeanTypeSound
open HOL4
-- 1. integer division: HOL4 gives 7 / ~3 = ~3 and 7 % ~3 = ~2
example : do_arith .Div .IntT [.Litv (.IntLit 7), .Litv (.IntLit (-3))]
    = some (.inr (.Litv (.IntLit (-2)))) := by rfl
example : do_arith .Mod .IntT [.Litv (.IntLit 7), .Litv (.IntLit (-3))]
    = some (.inr (.Litv (.IntLit 1))) := by rfl
-- 2. a Char outside 0..255 exists and is truncated
#eval (ORD (Char.ofNat 955), (char_to_word8 (Char.ofNat 955)).toNat, (char_to_word8 (Char.ofNat 187)).toNat)
example : char_to_word8 (Char.ofNat 955) = char_to_word8 (Char.ofNat 187) := by decide
-- 4. a gapped LazyList
noncomputable example : LazyList Nat := fun n => if n = 1 then some 7 else none

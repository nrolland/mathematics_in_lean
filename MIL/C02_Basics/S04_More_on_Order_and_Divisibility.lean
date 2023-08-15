import Mathlib.Tactic
import Mathlib.Data.Real.Basic

namespace C02S04

section
variable (a b c d : ℝ)

#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)


example : min a b = min b a := by
  apply le_antisymm
  · show min a b ≤ min b a
    exact (min_le_right a b) |> le_min <| (min_le_left a b)
  · show min b a ≤ min a b
    apply le_min
    · apply min_le_right
    apply min_le_left

example : min a b = min b a := by
  have h : ∀ x y : ℝ, min x y ≤ min y x := by
    intro x y
    apply le_min
    apply min_le_right
    apply min_le_left
  apply le_antisymm
  apply h
  apply h

example : min a b = min b a := by
  apply le_antisymm
  repeat
    apply le_min
    apply min_le_right
    apply min_le_left

#check max_le -- : (h₁ : a ≤ c) (h₂ : b ≤ c) : max a b ≤ c
#check le_max_left  --  :  (a b : α) : a ≤ max a b

example : max a b = max b a := by
  apply ge_antisymm
  repeat
    apply max_le
    apply le_max_right
    apply le_max_left

example : max a b = max b a := by
  have h : max a b <= max b a :=
    (sorry : a ≤ max b a) |> max_le <| (sorry :b ≤ max b a)
  sorry

example : max a b = max b a := by
  have h : ∀ x y : ℝ, max x y <= max y x := by
    intro x y
    exact (le_max_right _ _ |> max_le <| le_max_left _ _ )
  apply ge_antisymm
  repeat apply h

example : min (min a b) c = min a (min b c) := by
  have h : min (min a b) c <= min a (min b c) :=
    have h1 : min (min a b) c ≤ a := (min_le_left _ _ |> le_trans <| min_le_left _ _ : min (min a b) c ≤ a)
    have h2 : min (min a b) c ≤ min b c := le_min (min_le_left _ _ |> le_trans <| min_le_right _ _) (min_le_right _ _)
    h1 |> le_min <| h2
  have h' : min a (min b c)  <= min (min a b) c :=
    (le_min (min_le_left _ _) (min_le_right _  _ |> le_trans <| min_le_left _ _ ) : min a (min b c) ≤ min a b)
    |> le_min <|
    (min_le_right _ _ |> le_trans <| min_le_right _ _ : min a (min b c)  <= c )
  apply le_antisymm
    h
    h'


example : min (min a b) c = min a (min b c) := by
  apply le_antisymm
  . show  min (min a b) c <= min a (min b c)
    have h1 : min (min a b) c ≤ a := (min_le_left _ _ |> le_trans <| min_le_left _ _ : min (min a b) c ≤ a)
    have h2 : min (min a b) c ≤ min b c := le_min (min_le_left _ _ |> le_trans <| min_le_right _ _) (min_le_right _ _)
    exact h1 |> le_min <| h2
  . show   min a (min b c) <= min (min a b) c
    sorry


example : min (min a b) c = min a (min b c) := by
  apply le_antisymm
  . show  min (min a b) c <= min a (min b c)
    apply le_min
    . show  min (min a b) c ≤   a
      apply le_trans
      repeat apply min_le_left
    . show min (min a b) c ≤ min b c
      apply le_min
      . show  min (min a b) c ≤ b
        apply le_trans
        apply min_le_left
        apply min_le_right
      apply min_le_right
  . show   min a (min b c) <= min (min a b) c
    apply le_min
    . show  min a (min b c) ≤  min a b
      apply le_min
      . show min a (min b c) <= a
        apply min_le_left
      . show min a (min b c) ≤ b
        apply le_trans
        apply min_le_right
        apply min_le_left
    . show min a (min b c) ≤ c
      apply le_trans
      repeat apply min_le_right

#check  neg_add_cancel_right
#check add_neg_cancel_right
#check  add_neg_cancel_left
#check  add_le_add_right



theorem aux : min a b + c ≤ min (a + c) (b + c) := by
  apply le_min
  apply add_le_add_right (min_le_left _ _)
  apply add_le_add_right (min_le_right _ _)

example : min a b + c = min (a + c) (b + c) := by
  apply le_antisymm
  apply aux
  have h : min (a + c) (b + c)  ≤ min (a + c + -c) (b + c + -c) + c := by
    rw [<- neg_add_cancel_right (min (a + c) (b + c)) ]
    apply add_le_add_right (aux _ _ _)
  have h' : min (a + c + -c) (b + c + -c) + c = min a b  + c := by
    rw [add_neg_cancel_right a c , add_neg_cancel_right b c]
  linarith

#check (abs_add : ∀ a b : ℝ, |a + b| ≤ |a| + |b|)

example : |a| - |b| ≤ |a - b| :=
  sorry
end

section
variable (w x y z : ℕ)

example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
  dvd_trans h₀ h₁

example : x ∣ y * x * z := by
  apply dvd_mul_of_dvd_left
  apply dvd_mul_left

example : x ∣ x ^ 2 := by
   apply dvd_mul_left

example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
  sorry
end

section
variable (m n : ℕ)

#check (Nat.gcd_zero_right n : Nat.gcd n 0 = n)
#check (Nat.gcd_zero_left n : Nat.gcd 0 n = n)
#check (Nat.lcm_zero_right n : Nat.lcm n 0 = 0)
#check (Nat.lcm_zero_left n : Nat.lcm 0 n = 0)

example : Nat.gcd m n = Nat.gcd n m := by
  sorry
end

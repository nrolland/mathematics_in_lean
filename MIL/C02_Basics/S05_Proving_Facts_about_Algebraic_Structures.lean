import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Basic

section
variable {α : Type _} [PartialOrder α]
variable (x y z : α)

#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)

#check x < y
#check (lt_irrefl x : ¬ (x < x))
#check (lt_trans : x < y → y < z → x < z)
#check (lt_of_le_of_lt : x ≤ y → y < z → x < z)
#check (lt_of_lt_of_le : x < y → y ≤ z → x < z)

example : x < y ↔ x ≤ y ∧ x ≠ y :=
  lt_iff_le_and_ne

end


#check two_mul

section
variable (α : Type _)
variable [Lattice α]
variable (x y z : α)

#check x ⊓ y

#check (inf_le_left : x ⊓ y ≤ x)
#check (inf_le_right : x ⊓ y ≤ y)
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)
#check x ⊔ y
#check (le_sup_left : x ≤ x ⊔ y)
#check (le_sup_right : y ≤ x ⊔ y)
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)

example : x ⊓ y = y ⊓ x := by
  have h : ∀ a b : α, a ⊓ b <= b ⊓ a := by
    intro a b
    apply le_inf
    exact inf_le_right
    exact inf_le_left
  apply le_antisymm
  repeat apply h

example : x ⊓ y = y ⊓ x := by
  apply le_antisymm
  simp
  simp

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  apply le_antisymm
  have h := le_inf ((inf_le_left  |> le_trans <| inf_le_left) :  (x ⊓ y) ⊓ z <= x)
               (by apply le_inf (inf_le_left |> le_trans <| inf_le_right : (x ⊓ y) ⊓ z <= y )
                                (inf_le_right : (x ⊓ y) ⊓ z <= z )
          :  (x ⊓ y) ⊓ z <= y ⊓ z)

  have h := le_inf (inf_le_of_left_le inf_le_left)
                (by apply le_inf  (inf_le_of_left_le inf_le_right : (x ⊓ y) ⊓ z <= y )
                                  (inf_le_of_right_le (le_refl _) : (x ⊓ y) ⊓ z <= z ) )
  . show  x ⊓ y ⊓ z <= x ⊓ (y ⊓ z)
    refine h
  . show x ⊓ (y ⊓ z) ≤ x ⊓ y ⊓ z
    apply le_inf
          (inf_le_inf_left x inf_le_left : x ⊓ (y ⊓ z) ≤ x ⊓ y)
          (inf_le_of_right_le inf_le_right : x ⊓ (y ⊓ z) ≤ z)


example : x ⊔ y = y ⊔ x := by
  apply ge_antisymm
  simp
  simp

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  sorry


#check inf_comm --
#check inf_assoc--
#check sup_comm --
#check sup_assoc

theorem absorb1 : x ⊓ (x ⊔ y) = x := by
  apply le_antisymm
  . show x ⊓ (x ⊔ y) <= x
    exact inf_le_left
  . show x <= x ⊓ (x ⊔ y)
    apply le_inf
    exact le_refl _
    exact le_sup_left

theorem absorb2 : x ⊔ (x ⊓ y) = x := by
  apply le_antisymm
  . show x ⊔ (x ⊓ y) <= x
    apply sup_le
    exact le_refl _
    exact inf_le_left
  . show x <= x ⊔ (x ⊓ y)
    exact le_sup_left
end

#check inf_sup_self --a ⊓ (a ⊔ b) = a
#check  sup_inf_self -- a ⊔ a ⊓ b = a

section
variable {α : Type _} [DistribLattice α]
variable (x y z : α)

#check (inf_sup_left : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z)
#check (inf_sup_right : (x ⊔ y) ⊓ z = x ⊓ z ⊔ y ⊓ z)
#check (sup_inf_left : x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z))
#check (sup_inf_right : x ⊓ y ⊔ z = (x ⊔ z) ⊓ (y ⊔ z))
end

section



variable {α : Type _} [Lattice α]
variable (a b c : α)


#check sup_assoc --sup_assoc.{u} {α : Type u} [inst✝ : SemilatticeSup α] {a b c : α} : (a ⊔ b) ⊔ c = a ⊔ (b ⊔ c)
#check inf_sup_self
#check  sup_inf_self -- .{u} {α : Type u} [inst : Lattice α] {a b : α} : a ⊔ a ⊓ b = a

#check inf_sup_self --a ⊓ (a ⊔ b) = a
#check  sup_inf_self -- a ⊔ a ⊓ b = a
#check inf_comm

-- x ⊓ y = x ⊓ (y ⊔ (y ⊓ z)) = (x ⊓ y) ⊔ (x ⊓ (y ⊓ z))

example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z)) : a ⊔ (b ⊓ c) = (a ⊔ b) ⊓ (a ⊔ c) :=   by
 exact calc
  a ⊔ (b ⊓ c) = (a ⊔ (a ⊓ c)) ⊔ (b ⊓ c)  := by rw [sup_inf_self]
            _ = a  ⊔  ((a ⊓ c) ⊔ (b ⊓ c))  := by rw [sup_assoc]
            _ = a  ⊔  ((c ⊓ a) ⊔ (b ⊓ c))  := by rw [inf_comm]
            _ = a  ⊔  ((c ⊓ a) ⊔ (c ⊓ b))  := by rw [@inf_comm _ _ b]
            _ = a  ⊔  (c ⊓ (a ⊔ b))   := by rw [h]
            _ = a  ⊔  ((a ⊔ b) ⊓ c)  := by rw [inf_comm]
            _ = (a ⊓ (a ⊔ b)) ⊔  ((a ⊔ b) ⊓ c)  := by rw [inf_sup_self]
            _ = ((a ⊔ b) ⊓ a) ⊔  ((a ⊔ b) ⊓ c)  := by  rw [inf_comm ]
            _ = (a ⊔ b) ⊓ (a ⊔ c)  := by rw [h]


example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z)) : a ⊔ (b ⊓ c) = (a ⊔ b) ⊓ (a ⊔ c) := calc
  a ⊔ (b ⊓ c) = (a ⊔ (a ⊓ c)) ⊔ (b ⊓ c)         := by rw [sup_inf_self]
            _ = a  ⊔ ((c ⊓ a) ⊔ (c ⊓ b))        := by simp only [sup_assoc, inf_comm]
            _ = a  ⊔ (c ⊓ (a ⊔ b))              := by rw [h]
            _ = ((a ⊔ b) ⊓ a) ⊔  ((a ⊔ b) ⊓ c)  := by simp only [inf_comm , inf_sup_self]
            _ = (a ⊔ b) ⊓ (a ⊔ c)               := by rw [h]


example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  sorry



end

section
variable {R : Type _} [StrictOrderedRing R]
variable (a b c : R)

#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)

#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)


#check add_right_neg a
#check add_le_add_right

example : a ≤ b → 0 ≤ b - a := by
  intro h
  -- have g := @add_le_add_right _ _ _ _ a b h
  -- have k : a + -a ≤ b + -a := g (-a)
  calc
    0 ≤ 0 := le_refl _
    _  ≤ a + -a := by rw [add_right_neg a]
    _  ≤ b + -a := add_le_add_right h _
    _  ≤ b - a := by rw [sub_eq_add_neg]

#check le_add_of_nonneg_right
#check sub_add_cancel -- :  a - b + b = a
#check add_assoc -- : (a + b) + c = a + (b + c)

example : 0 ≤ b - a → a ≤ b := by
  intro h
  calc
    a <= a + (b - a) := le_add_of_nonneg_right h
    _ <= (b - a) + a := by rw [add_comm]
    _ <= b := by rw [sub_add_cancel]

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  sorry

end

section
variable {X : Type _} [MetricSpace X]
variable (x y z : X)

#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)

#check nonneg_of_mul_nonneg_left -- (h : 0 ≤ a * b) (hb : 0 < b) :   0 ≤ a
#check mul_add --(a b c : R) a * (b + c) = a * b + a * c
#check neg_neg


example (x y : X) : 0 ≤ dist x y := by
  have h : 0 ≤ dist x y * 2 :=
    calc
      0 ≤ dist x x := by rw [dist_self]
      _ ≤ dist x y + dist y x := dist_triangle _ _ _
      _ ≤ dist x y + dist x y := by rw [dist_comm]
      -- _ ≤ 1 * dist x y +  1 * dist x y := by rw [one_mul]
      -- _ ≤ (1 + 1) * dist x y := by rw [add_mul _ _ _]
      -- _ ≤ 2 * dist x y := by norm_num
      _ ≤ 2 * dist x y := by rw [two_mul]
      _ ≤ dist x y * 2  := by rw [mul_comm]
  exact nonneg_of_mul_nonneg_left h two_pos

end

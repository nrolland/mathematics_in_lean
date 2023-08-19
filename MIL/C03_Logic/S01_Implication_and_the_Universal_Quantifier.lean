import Mathlib.Tactic
import Mathlib.Data.Real.Basic

namespace C03S01

#check ∀ x : ℝ, 0 ≤ x → |x| = x

#check ∀ x y ε : ℝ, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε

theorem my_lemma : ∀ x y ε : ℝ, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε :=
  by sorry

section
variable (a b δ : ℝ)
variable (h₀ : 0 < δ) (h₁ : δ ≤ 1)
variable (ha : |a| < δ) (hb : |b| < δ)

#check my_lemma a b δ
#check my_lemma a b δ h₀ h₁
#check my_lemma a b δ h₀ h₁ ha hb

end

theorem my_lemma2 : ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε :=
  sorry

section
variable (a b δ : ℝ)
variable (h₀ : 0 < δ) (h₁ : δ ≤ 1)
variable (ha : |a| < δ) (hb : |b| < δ)

#check my_lemma2 h₀ h₁ ha hb
#check @my_lemma2 a b δ h₀ h₁ ha hb

end

theorem my_lemma3 :
    ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intro x y ε epos ele1 xlt ylt
  sorry

#check abs_nonneg
#check mul_le_mul_left
#check mul_le_mul_of_nonneg_left
#check le_of_lt

#check mul_lt_mul_of_pos_right


theorem my_lemma4 :
    ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intro x y ε epos ele1 xlt ylt
  have g := mul_le_mul_of_nonneg_left (le_of_lt ylt) (abs_nonneg x)
  have g  : |x| * ε < 1 * ε := mul_lt_mul_of_pos_right (by linarith) epos
  calc
    |x * y| = |x| * |y| := abs_mul _ _
    _ ≤ |x| * ε := mul_le_mul_of_nonneg_left (le_of_lt ylt) (abs_nonneg x)
    _ < 1 * ε := mul_lt_mul_of_pos_right (by linarith) epos
    _ = ε := by rw [one_mul] --linarith

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

section
variable (f g : ℝ → ℝ) (a b : ℝ)

example (hfa : FnUb f a) (hgb : FnUb g b) : FnUb (fun x ↦ f x + g x) (a + b) := by
  intro x
  dsimp
  apply add_le_add
  . apply hfa
  . apply hgb

example (hfa : FnLb f a) (hgb : FnLb g b) : FnLb (fun x ↦ f x + g x) (a + b) := fun x ↦
  (hfa x) |> add_le_add <| (hgb x)

example (nnf : FnLb f 0) (nng : FnLb g 0) : FnLb (fun x ↦ f x * g x) 0 := fun x ↦
  nnf x |> mul_nonneg <| nng x

example (hfa : FnUb f a) (hgb : FnUb g b) (nng : FnLb g 0) (nna : 0 ≤ a) :
    FnUb (fun x ↦ f x * g x) (a * b) := fun x ↦
      by
        have h1 : f x * g x ≤ a * g x :=  mul_le_mul_of_nonneg_right (hfa x) (nng x)
        have h2 : a * g x ≤ a * b :=  mul_le_mul_of_nonneg_left (hgb x) nna
        have h3 : f x * g x ≤ a * b :=  h1 |> le_trans <| h2
        exact h3



example (hfa : FnUb f a) (hgb : FnUb g b) (nng : FnLb g 0) (nna : 0 ≤ a) :
    FnUb (fun x ↦ f x * g x) (a * b) := fun x ↦ by
    calc
      f x * g x  <= a * g x := by exact mul_le_mul_of_nonneg_right (hfa x) (nng x)
               _ <= a * b :=  mul_le_mul_of_nonneg_left (hgb x) nna


#check add_le_add


end


section
variable {α : Type _} {R : Type _} [OrderedCancelAddCommMonoid R]

#check add_le_add

def FnUb' (f : α → R) (a : R) : Prop :=
  ∀ x, f x ≤ a

theorem fnUb_add {f g : α → R} {a b : R} (hfa : FnUb' f a) (hgb : FnUb' g b) :
    FnUb' (fun x ↦ f x + g x) (a + b) := fun x ↦ add_le_add (hfa x) (hgb x)

end

example (f : ℝ → ℝ) (h : Monotone f) : ∀ {a b}, a ≤ b → f a ≤ f b :=
  @h

section
variable (f g : ℝ → ℝ)

example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f x + g x := by
  intro a b aleb
  apply add_le_add
  apply mf aleb
  apply mg aleb

example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f x + g x :=
  fun a b aleb ↦ add_le_add (mf aleb) (mg aleb)

example {c : ℝ} (mf : Monotone f) (nnc : 0 ≤ c) : Monotone fun x ↦ c * f x :=
  fun a b aleb ↦ mul_le_mul_of_nonneg_left (mf aleb) nnc

example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f (g x) :=
  fun a b aleb ↦ mf (mg aleb) -- function composition = ??

def FnEven (f : ℝ → ℝ) : Prop :=
  ∀ x, f x = f (-x)

def FnOdd (f : ℝ → ℝ) : Prop :=
  ∀ x, f x = -f (-x)

example (ef : FnEven f) (eg : FnEven g) : FnEven fun x ↦ f x + g x := by
  intro x
  calc
    (fun x ↦ f x + g x) x = f x + g x := rfl
    _ = f (-x) + g (-x) := by rw [ef, eg]


example (of : FnOdd f) (og : FnOdd g) : FnEven fun x ↦ f x * g x := by
  sorry

example (ef : FnEven f) (og : FnOdd g) : FnOdd fun x ↦ f x * g x := by
  sorry

example (ef : FnEven f) (og : FnOdd g) : FnEven fun x ↦ f (g x) := by
  sorry

end

section

variable {α : Type _} (r s t : Set α)

-- s ⊆ t is defined to mean ∀ {x : α}, x ∈ s → x ∈ t

example : s ⊆ s := by
  intro x xs
  exact xs

theorem Subset.refl : s ⊆ s := fun x xs ↦ xs

theorem Subset.trans : r ⊆ s → s ⊆ t → r ⊆ t := fun rs st x xr ↦
  st (rs xr)

section
variable {α : Type _} [PartialOrder α]
variable (s : Set α) (a b : α)

def SetUb (s : Set α) (a : α) :=
  ∀ x, x ∈ s → x ≤ a

example (h : SetUb s a) (h' : a ≤ b) : SetUb s b := fun x xs ↦ by
    calc
       x <= a :=  h _ xs
       _ <= b := h'

end

section

open Function


/-
@add_left_inj : ∀ {G : Type u_1} [inst : Add G] [inst_1 : IsRightCancelAdd G] (a : G) {b c : G}, b + a = c + a ↔ b = c
-/
#check @add_left_inj

example (c : ℝ) : Injective fun x ↦ x + c := by
  have g : ∀ a b : ℝ , a + c = b + c -> a = b := fun a b ↦ ((@add_left_inj _ _ _ c).mp)
  have g : ∀ a b : ℝ , a + c = b + c -> a = b := fun a b ↦ ((add_left_inj c).mp)
  have g : ∀ {a b : ℝ} , a + c = b + c -> a = b := (add_left_inj c).mp
  intro x₁ x₂ h
  exact g  (h : x₁ + c = x₂ + c)

example {c : ℝ} (h : c ≠ 0) : Injective fun x ↦ c * x := by
  sorry

variable {α : Type _} {β : Type _} {γ : Type _}
variable {g : β → γ} {f : α → β}

example (injg : Injective g) (injf : Injective f) : Injective fun x ↦ g (f x) := fun _ _ h ↦
  injf (injg h)

end

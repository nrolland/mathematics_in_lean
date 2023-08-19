import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Nat.Parity
import Mathlib.Tactic

section
variable {α : Type _}
variable (s t u : Set α)
open Set

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  rw [subset_def, inter_def, inter_def]
  rw [subset_def] at h
  simp only [mem_setOf]
  rintro x ⟨xs, xu⟩
  exact ⟨h _ xs, xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  simp only [subset_def, mem_inter_iff] at *
  rintro x ⟨xs, xu⟩
  exact ⟨h _ xs, xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  intro x xsu
  exact ⟨h xsu.1, xsu.2⟩

theorem foo (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
  fun x ⟨xs, xu⟩ ↦ ⟨h xs, xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
  fun x ⟨xs, xu⟩ ↦ ⟨h xs, xu⟩

example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  intro x hx
  have xs : x ∈ s := hx.1
  have xtu : x ∈ t ∪ u := hx.2
  rcases xtu with xt | xu
  · left
    show x ∈ s ∩ t
    exact ⟨xs, xt⟩
  . right
    show x ∈ s ∩ u
    exact ⟨xs, xu⟩

example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  rintro x ⟨xs, xt | xu⟩
  · left; exact ⟨xs, xt⟩
  . right
    exact ⟨xs, xu⟩

example : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  rintro x ( ⟨xs,xt⟩ | ⟨xs,xu⟩ )
  {.  exact ⟨xs , by left; exact xt⟩}
  exact ⟨xs, by right; exact xu⟩


example : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  rintro x ( ⟨xs,xt⟩ | ⟨xs,xu⟩ )
  {.  use xs
      left; exact xt}
  use xs
  right; exact xu



example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  intro x xstu
  have xs : x ∈ s := xstu.1.1
  have xnt : x ∉ t := xstu.1.2
  have xnu : x ∉ u := xstu.2
  constructor
  · exact xs
  intro xtu
  -- x ∈ t ∨ x ∈ u
  rcases xtu with xt | xu
  · show False; exact xnt xt
  . show False; exact xnu xu

example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  rintro x ⟨⟨xs, xnt⟩, xnu⟩
  use xs
  rintro (xt | xu) <;> contradiction

example : s \ (t ∪ u) ⊆ (s \ t) \ u := by
  rintro x ⟨xs, xntu ⟩
  have g : x ∈ s \ t := by use xs; rintro xt;
                           have xtu : x ∈ t ∪ u := by left; exact xt
                           contradiction
  use g
  rintro xnu
  have k : x ∉ u := sorry
  contradiction

example : s \ (t ∪ u) ⊆ (s \ t) \ u := by
  rintro x ⟨xs, xntu ⟩
  have g : x ∈ s \ t := by use xs
                           rintro xt;
                           exact (by left; exact xt) |> xntu
  use g
  rintro xu
  exact xntu (by right; exact xu)


#check (_ ∘ _)

#check (_ >>> _)



example : s \ (t ∪ u) ⊆ (s \ t) \ u := by
  rintro x ⟨xs, xntu ⟩
  constructor
  . use xs; exact xntu ∘ Or.inl
  . exact xntu ∘ Or.inr


example : s ∩ t = t ∩ s := by
  ext x
  -- simp only [mem_inter_iff]
  constructor
  · rintro ⟨xs, xt⟩; exact ⟨xt, xs⟩
  . rintro ⟨xt, xs⟩; exact ⟨xs, xt⟩

example : s ∩ t = t ∩ s :=
  Set.ext fun x ↦ ⟨fun ⟨xs, xt⟩ ↦ ⟨xt, xs⟩, fun ⟨xt, xs⟩ ↦ ⟨xs, xt⟩⟩

example : s ∩ t = t ∩ s := by ext x; simp [and_comm]

example : s ∩ t = t ∩ s := by
  apply Subset.antisymm
  · rintro x ⟨xs, xt⟩; exact ⟨xt, xs⟩
  . rintro x ⟨xt, xs⟩; exact ⟨xs, xt⟩

example : s ∩ t = t ∩ s :=
    have h : ∀ {a b : Set α}, a ∩ b ⊆ b ∩ a := by
          intro a b x ⟨xa, xb⟩
          exact ⟨xb, xa⟩
    have gi : ∀ {a b : Set α}, a ∩ b ⊆ b ∩ a :=  fun {a b x} ⟨xa, xb⟩ ↦ ⟨xb, xa⟩
    have ge : ∀ a b : Set α, a ∩ b ⊆ b ∩ a :=  fun a b x ⟨xa, xb⟩  ↦ ⟨xb, xa⟩
    have k : s ∩ t ⊆ t ∩ s := fun x ⟨xs, xt ⟩  ↦ ⟨xt,xs⟩
    Subset.antisymm (ge s t) (@gi t s)
    -- Subset.antisymm (by apply ge) (by apply gi)

example : s ∩ t = t ∩ s :=
    have ge : ∀ a b : Set α, a ∩ b ⊆ b ∩ a :=  fun a b x ⟨xa, xb⟩  ↦ ⟨xb, xa⟩
    Subset.antisymm (ge s t) (ge t s)

example : s ∩ t = t ∩ s :=
    Subset.antisymm (fun x ⟨xa, xb⟩  ↦ ⟨xb, xa⟩) (fun x ⟨xa, xb⟩  ↦ ⟨xb, xa⟩)
    -- Subset.antisymm (by apply ge) (by apply gi)



example : s ∩ (s ∪ t) = s :=
 Subset.antisymm (fun x ⟨xs, _⟩ ↦ xs ) (fun x xs ↦ ⟨xs, Or.inl xs⟩)


example : s ∪ s ∩ t = s :=
  Subset.antisymm (fun x ↦ by rintro (xs | ⟨xs, _⟩) <;> exact xs)
                  (fun x xs ↦ Or.inl xs)

example : s \ t ∪ t = s ∪ t :=
  Subset.antisymm
  (fun x ↦ by rintro ( ⟨xs, xnt ⟩ | xt) ; exact Or.inl xs ; exact Or.inr xt)
  (fun x ↦ by rintro (xs | xt)
              . { by_cases h : x ∈ t
                  exact Or.inr h
                  exact Or.inl ⟨xs, h⟩}
              exact Or.inr xt)

example : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) :=
  Subset.antisymm
  (fun x ↦ by rintro ( ⟨ xs, xnt⟩ | ⟨xt, xns ⟩ )
              use Or.inl xs
              exact xnt ∘ And.right
              use Or.inr xt
              exact xns ∘ And.left  )
  (fun x ↦ by rintro ⟨xsort, xnst⟩
              show x ∈ s \ t ∪ t \ s
              rcases xsort with xs | xt
              . left
                use xs
                exact xnst ∘ And.intro xs
              right
              use xt
              exact xnst ∘ (And.intro . xt))



def evens : Set ℕ :=
  { n | Even n }

def odds : Set ℕ :=
  { n | ¬Even n }

example : evens ∪ odds = univ := by
  rw [evens, odds]
  ext n
  simp
  apply Classical.em

example (x : ℕ) (h : x ∈ (∅ : Set ℕ)) : False :=
  h

example (x : ℕ) : x ∈ (univ : Set ℕ) :=
  trivial

example : { n | Nat.Prime n } ∩ { n | n > 2 } ⊆ { n | ¬Even n } := by
  sorry

#print Prime

#print Nat.Prime

example (n : ℕ) : Prime n ↔ Nat.Prime n :=
  Nat.prime_iff.symm

example (n : ℕ) (h : Prime n) : Nat.Prime n := by
  rw [Nat.prime_iff]
  exact h

example (n : ℕ) (h : Prime n) : Nat.Prime n := by
  rwa [Nat.prime_iff]

end

section

variable (s t : Set ℕ)

example (h₀ : ∀ x ∈ s, ¬Even x) (h₁ : ∀ x ∈ s, Prime x) : ∀ x ∈ s, ¬Even x ∧ Prime x := by
  intro x xs
  constructor
  · apply h₀ x xs
  apply h₁ x xs

example (h : ∃ x ∈ s, ¬Even x ∧ Prime x) : ∃ x ∈ s, Prime x := by
  rcases h with ⟨x, xs, _, prime_x⟩
  use x, xs
  exact prime_x

section
variable (ssubt : s ⊆ t)

example (h₀ : ∀ x ∈ t, ¬Even x) (h₁ : ∀ x ∈ t, Prime x) : ∀ x ∈ s, ¬Even x ∧ Prime x := by
  sorry

example (h : ∃ x ∈ s, ¬Even x ∧ Prime x) : ∃ x ∈ t, Prime x := by
  sorry

end

end

section
variable {α I : Type _}
variable (A B : I → Set α)
variable (s : Set α)

open Set

example : (s ∩ ⋃ i, A i) = ⋃ i, A i ∩ s := by
  ext x
  simp only [mem_inter_iff, mem_iUnion]
  constructor
  · rintro ⟨xs, ⟨i, xAi⟩⟩
    exact ⟨i, xAi, xs⟩
  rintro ⟨i, xAi, xs⟩
  exact ⟨xs, ⟨i, xAi⟩⟩

example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ ⋂ i, B i := by
  ext x
  simp only [mem_inter_iff, mem_iInter]
  constructor
  · intro h
    constructor
    · intro i
      exact (h i).1
    intro i
    exact (h i).2
  rintro ⟨h1, h2⟩ i
  constructor
  · exact h1 i
  exact h2 i


example : (s ∪ ⋂ i, A i) = ⋂ i, A i ∪ s := by
  sorry

def primes : Set ℕ :=
  { x | Nat.Prime x }

example : (⋃ p ∈ primes, { x | p ^ 2 ∣ x }) = { x | ∃ p ∈ primes, p ^ 2 ∣ x } :=by
  ext
  rw [mem_iUnion₂]
  simp

example : (⋃ p ∈ primes, { x | p ^ 2 ∣ x }) = { x | ∃ p ∈ primes, p ^ 2 ∣ x } := by
  ext
  simp

example : (⋂ p ∈ primes, { x | ¬p ∣ x }) ⊆ { x | x = 1 } := by
  intro x
  contrapose!
  simp
  apply Nat.exists_prime_and_dvd

example : (⋃ p ∈ primes, { x | x ≤ p }) = univ := by
  sorry

end

section

open Set

variable {α : Type _} (s : Set (Set α))

example : ⋃₀ s = ⋃ t ∈ s, t := by
  ext x
  rw [mem_iUnion₂]
  simp

example : ⋂₀ s = ⋂ t ∈ s, t := by
  ext x
  rw [mem_iInter₂]
  rfl

end

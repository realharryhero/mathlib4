import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

-- Following proof from https://pommetatin.be/files/zsigmondy_en.pdf

theorem helpful_lemma1
    {R : Type*} [Ring R] : True := ⟨⟩

theorem monomial_minus_one_double_root_mod_prime
    {p : ℕ} [Fact p.Prime]
    {n : ℕ} {a : ℤ} {f : Polynomial (ZMod p)}
    (h : Polynomial.monomial n (1 : ZMod p) - 1 =
          ((Polynomial.X : Polynomial (ZMod p)) - a) ^ 2 * f) :
    p ∣ n := by
  by_cases h₀ : a ≡ 0 [ZMOD p]
  · simp only [Int.ModEq, EuclideanDomain.zero_mod, EuclideanDomain.mod_eq_zero] at h₀

    sorry
  · sorry

theorem zsigmondy_theorem
    {a b : ℕ} (h₁ : a > b) (h₂ : Nat.Coprime a b) {n : ℕ} (h₃ : 1 ≤ n)
    (h₄ : ¬ (n = 1 ∧ a - b = 1))
    (h₅ : ¬ (n = 2 ∧ (∃ m : ℕ, a + b = Nat.pow 2 m)))
    (h₆ : ¬ (n = 6 ∧ a = 2 ∧ b = 1)) :
    ∃ p : ℕ, Nat.Prime p ∧
             p ∣ (Nat.pow a n - Nat.pow b n) ∧
             ∀ k : ℕ, k < n → ¬ (p ∣ (Nat.pow a k - Nat.pow b k)) := by
  sorry

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

-- Following proof from https://pommetatin.be/files/zsigmondy_en.pdf

theorem helpful_lemma1
    {R : Type*} [Semiring R] [Nontrivial R]
    {m n : ℕ} (hn : n ≠ 0)
    {r₁ r₂ r₃ : R} (hr₁ : r₁ ≠ 0) (hr₂ : r₂ ≠ 0) (hr₃ : r₃ ≠ 0):
    Polynomial.C r₁ * Polynomial.monomial m (r₂ : R) + Polynomial.C r₃ ≠ 0 := by
  sorry

theorem monomial_minus_one_double_root_mod_prime
    {p : ℕ} [Fact p.Prime]
    {n : ℕ} {a : ℤ} {f : Polynomial (ZMod p)}
    (h : Polynomial.monomial n (1 : ZMod p) - 1 =
          ((Polynomial.monomial 1 (1 : ZMod p)) - a) ^ 2 * f) :
    p ∣ n := by
  have h₀ : n = 0 ∨ ¬ ↑p ∣ a := by
    rintro ⟨x, h'⟩
    simp only [h', Int.cast_mul, Int.cast_ofNat, CharP.cast_eq_zero, zero_mul, sub_zero,
      Polynomial.monomial_pow, one_mul, one_pow] at h
    sorry
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

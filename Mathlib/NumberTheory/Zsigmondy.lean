import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

-- Following proof from https://pommetatin.be/files/zsigmondy_en.pdf

theorem helpful_lemma1
    {R : Type*} [Semiring R] [Nontrivial R]
    {n₁ n₂ : ℕ} (hn : n₁ ≠ n₂) {n₃ : ℕ}
    {r₁ : R} (hr₁ : r₁ ≠ 0) {r₂ : R} (hr₂ : r₂ ≠ 0) {r₃ : R} :
    Polynomial.monomial n₁ r₁ + Polynomial.monomial n₂ r₂ ≠ Polynomial.monomial n₃ r₃ := by
  intro h
  simp only [Polynomial.ext_iff, Polynomial.coeff_add] at h
  have hn₁ := h n₁
  simp only [Polynomial.coeff_monomial, ↓reduceIte] at hn₁
  rw [ite_cond_eq_false r₂ 0 (by
    simp only [eq_iff_iff, iff_false]; exact fun h' => hn h'.symm), add_zero] at hn₁
  simp_all only [ne_eq, ite_eq_right_iff, not_forall, exists_prop, ite_true]
  have hn₂ := h n₂
  simp only [Polynomial.coeff_monomial, hn, ↓reduceIte, zero_add] at hn₂
  exact hr₂ hn₂

theorem helpful_lemma2
    {R : Type*} [Semiring R] [Nontrivial R] {f g: Polynomial R} {r : R} (hr : r ≠ 0) :
    f * Polynomial.X + Polynomial.C r ≠ g * Polynomial.X := by
  intro h
  simp only [Polynomial.ext_iff, Polynomial.coeff_add] at h
  have h₁ := h 0
  simp only [Polynomial.mul_coeff_zero, Polynomial.coeff_X_zero, mul_zero, Polynomial.coeff_C_zero,
    zero_add] at h₁
  exact hr h₁

theorem monomial_minus_one_double_root_mod_prime
    {p : ℕ} [Fact p.Prime]
    {n : ℕ} (h₀ : n ≠ 0)
    {a : ℤ} {f : Polynomial (ZMod p)}
    (h₁ : Polynomial.monomial n (1 : ZMod p) - 1 =
          f * ((Polynomial.monomial 1 (1 : ZMod p)) - a) ^ 2) :
    p ∣ n := by
  have h₀ : ¬ ↑p ∣ a := by
    rintro ⟨x, h'⟩
    simp only [h', Int.cast_mul, Int.cast_ofNat, CharP.cast_eq_zero, zero_mul, sub_zero,
      Polynomial.monomial_pow, one_mul, one_pow] at h₁
    have h₂ := Polynomial.monomial_mul_monomial 1 1 (1 : ZMod p) (1 : ZMod p)
    simp only [Nat.reduceAdd, mul_one] at h₂
    rw [← h₂, ← mul_assoc] at h₁
    have := @helpful_lemma2 (ZMod p) _ _ (Polynomial.monomial n 1) (f * (Polynomial.monomial 1 1)) (p - 1)
      (by simp only [CharP.cast_eq_zero, zero_sub, ne_eq, neg_eq_zero, one_ne_zero,
        not_false_eq_true])
    apply this
    rw [← Polynomial.monomial_one_one_eq_X]
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

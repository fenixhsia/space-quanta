/-
  Formal core of Theorem 21 (defect gas) in "Causal Sets by Dynamical Densification".
  (1) Product formula: Σ_{configurations} e^{iβ Σ_s δ(s, j_s)} = ∏_s Σ_j e^{iβ δ(s, j)} (any finite sites and options).
  (2) Jensen (K = 1): the circle average of log‖z + 1‖ over the unit circle is 0.
  (3) Inner Jensen: the circle average of log‖z + w‖ equals log⁺‖w‖ (the key step for positivity when K ≥ 2).
  (4) Phase-lock window: ‖1 + e^{ix}‖ < 1 ⟺ cos x < −1/2 (the origin of the KR threshold).
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.PosLog
import Mathlib.Algebra.BigOperators.Ring.Finset

open Complex Real

noncomputable section

namespace CausalDensification.DefectGasAlgebra

/-- (1) Product formula for the defect gas. -/
theorem defect_product {M K : ℕ} (β : ℝ) (δ : Fin M → Fin (K + 1) → ℝ) :
    ∑ x : Fin M → Fin (K + 1), Complex.exp (I * β * ∑ s, δ s (x s)) =
      ∏ s, ∑ j, Complex.exp (I * β * δ s j) := by
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  push_cast
  rw [Finset.mul_sum, Complex.exp_sum]

/-- (2) Jensen: m(1 + x) = 0. -/
theorem jensen_one_plus_x : circleAverage (fun z : ℂ => Real.log ‖z + 1‖) 0 1 = 0 := by
  simp

/-- (3) Inner Jensen: for every w, the circle average of log‖z + w‖ is log⁺‖w‖.
    Hence m(1 + x₁ + Q) = E_Q[log⁺‖1 + Q‖] ≥ 0, and for K ≥ 2 the event ‖1 + Q‖ > 1 has positive probability, so m > 0. -/
theorem jensen_inner (w : ℂ) : circleAverage (fun z : ℂ => Real.log ‖z + w‖) 0 1 = log⁺ ‖w‖ := by
  simp

/-- (4) Phase-lock window of a single site: |1 + e^{ix}| < 1 ⟺ cos x < −1/2. -/
theorem lock_window (x : ℝ) : ‖1 + Complex.exp (x * I)‖ < 1 ↔ Real.cos x < -1 / 2 := by
  have hsq : ‖1 + Complex.exp (x * I)‖ ^ 2 = 2 + 2 * Real.cos x := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    nlinarith [Real.sin_sq_add_cos_sq x]
  have hn : 0 ≤ ‖1 + Complex.exp (x * I)‖ := norm_nonneg _
  constructor
  · intro h
    have : ‖1 + Complex.exp (x * I)‖ ^ 2 < 1 := by nlinarith
    linarith
  · intro h
    have : ‖1 + Complex.exp (x * I)‖ ^ 2 < 1 := by linarith
    nlinarith

end CausalDensification.DefectGasAlgebra

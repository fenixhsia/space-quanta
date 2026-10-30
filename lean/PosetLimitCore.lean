/-
  Formal checks for Theorems 17, 19 and 20 of "Causal Sets by Dynamical Densification".
  (1) Core of Theorem 17 (k = 2, order fraction): μ_n ⇒ μ and (μ⊗μ)(null ∪ diagonal) = 0 ⟹ (μ_n⊗μ_n)(causal) → (μ⊗μ)(causal).
      Proved in full on Minkowski space ℝ × ℝ³ (the boundary of the causal set is contained in the null pairs).
  (2) Analytic part of Theorem 19 ((H1), α > 0): the drift Σ m^{-5/4} and the martingale L² term Σ 1/m² are summable.
  (3) Elementary part of Theorem 20 ((H2), α > 0):
      the one-step conditional-expectation identity of the Pólya urn, the closed form and uniqueness of the second moment, P(same class) ≤ 2/(M+1);
      shell volume ≤ 8π(r+ε)²ε; cancellation of the hyperbolic polar Jacobian and the density bound; optimisation of M ~ ε^{-1/2}.
  Not formalised: autonomy of the time process, the probabilistic parts (conditional expectation, martingale convergence), the minimum-image distance on the torus.
-/
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

open MeasureTheory Filter Topology Real TopologicalSpace

noncomputable section

namespace CausalDensification.PosetLimitCore

/-! ## (1) Core of Theorem 17 (k = 2) -/

/-- Abstract version: for a set C whose boundary lies in Z, the product measures converge if the limit product measure does not charge Z. -/
theorem pair_measure_tendsto {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]
    [SecondCountableTopology Ω] [PseudoMetrizableSpace Ω] [OpensMeasurableSpace Ω]
    {μ : ProbabilityMeasure Ω} {μs : ℕ → ProbabilityMeasure Ω} (hlim : Tendsto μs atTop (𝓝 μ))
    {C Z : Set (Ω × Ω)} (hfr : frontier C ⊆ Z) (hZ : (μ.prod μ : Measure (Ω × Ω)) Z = 0) :
    Tendsto (fun n => ((μs n).prod (μs n) : Measure (Ω × Ω)) C) atTop
      (𝓝 ((μ.prod μ : Measure (Ω × Ω)) C)) := by
  have h2 : Tendsto (fun n => (μs n).prod (μs n)) atTop (𝓝 (μ.prod μ)) := by
    have hc := (ProbabilityMeasure.continuous_prod (α := Ω) (β := Ω)).tendsto (μ, μ)
    exact hc.comp (hlim.prodMk_nhds hlim)
  exact ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' h2
    (measure_mono_null hfr hZ)

instance : MeasurableSpace (EuclideanSpace ℝ (Fin 3)) := borel _
instance : BorelSpace (EuclideanSpace ℝ (Fin 3)) := ⟨rfl⟩

/-- Minkowski space ℝ × ℝ³. -/
abbrev E := ℝ × EuclideanSpace ℝ (Fin 3)

/-- Causal relation x ≺ y: Δt > |Δy|. -/
def causal : Set (E × E) := {p | ‖(p.2 - p.1).2‖ < (p.2 - p.1).1}

/-- Null pairs (including the diagonal): Δt = |Δy|. -/
def nullOrDiag : Set (E × E) := {p | (p.2 - p.1).1 = ‖(p.2 - p.1).2‖}

lemma frontier_causal_subset : frontier causal ⊆ nullOrDiag := by
  have hf : Continuous fun p : E × E => ‖(p.2 - p.1).2‖ := by fun_prop
  have hg : Continuous fun p : E × E => (p.2 - p.1).1 := by fun_prop
  have hopen : IsOpen causal := isOpen_lt hf hg
  rw [hopen.frontier_eq]
  rintro p ⟨hcl, hnot⟩
  have hle := closure_lt_subset_le hf hg hcl
  simp only [causal, Set.mem_ofPred_eq, not_lt] at hnot hle
  exact le_antisymm hnot hle

/-- Theorem 17 (k = 2): under (H1) μ_n ⇒ μ and (H2) (μ⊗μ)(null ∪ diagonal) = 0, the order fraction converges. -/
theorem ordering_fraction_tendsto {μ : ProbabilityMeasure E} {μs : ℕ → ProbabilityMeasure E}
    (hH1 : Tendsto μs atTop (𝓝 μ)) (hH2 : (μ.prod μ : Measure (E × E)) nullOrDiag = 0) :
    Tendsto (fun n => ((μs n).prod (μs n) : Measure (E × E)) causal) atTop
      (𝓝 ((μ.prod μ : Measure (E × E)) causal)) :=
  pair_measure_tendsto hH1 frontier_causal_subset hH2

/-! ## (2) Theorem 19: drift and martingale terms are summable -/

/-- Drift: Σ m^{-5/4} < ∞ (D_m ∝ m^{-1/4}, times 1/m). -/
lemma drift_summable : Summable (fun m : ℕ => ((m : ℝ) ^ (5 / 4 : ℝ))⁻¹) :=
  Real.summable_nat_rpow_inv.mpr (by norm_num)

/-- Martingale L² bound: Σ 1/m² < ∞. -/
lemma martingale_L2_summable : Summable (fun m : ℕ => 1 / (m : ℝ) ^ 2) :=
  Real.summable_one_div_nat_pow.mpr (by norm_num)

/-! ## (3) Elementary part of Theorem 20 -/

/-- One Pólya-urn step: class counts c_k, total s, class k drawn with probability c_k/s;
    E[Σ c_k²]_{next step} = (1 + 2/s) Σ c_k² + 1. -/
lemma polya_step {M : ℕ} (c : Fin M → ℝ) (s : ℝ) (hs : s ≠ 0) (hsum : ∑ k, c k = s) :
    ∑ k, ((c k / s) * (c k + 1) ^ 2 + (1 - c k / s) * c k ^ 2) =
      (1 + 2 / s) * ∑ k, c k ^ 2 + 1 := by
  have h : ∀ k, (c k / s) * (c k + 1) ^ 2 + (1 - c k / s) * c k ^ 2 =
      c k ^ 2 + (2 / s) * c k ^ 2 + c k / s := by
    intro k; field_simp; ring
  simp_rw [h, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div, hsum]
  field_simp

/-- Closed form of the second moment: S(s) = 2s(s+1)/(M+1) − s. -/
def S (M s : ℝ) : ℝ := 2 * s * (s + 1) / (M + 1) - s

lemma S_init (M : ℝ) (hM : 0 < M) : S M M = M := by
  unfold S; field_simp; ring

lemma S_rec (M s : ℝ) (hM : 0 < M) (hs : 0 < s) : S M (s + 1) = (1 + 2 / s) * S M s + 1 := by
  unfold S; field_simp; ring

/-- Uniqueness: any sequence with initial value f(M) = M (one ball per class) satisfying the one-step recursion equals S. -/
lemma S_unique (M0 : ℕ) (hM : 0 < M0) (f : ℕ → ℝ) (h0 : f M0 = M0)
    (hrec : ∀ s ≥ M0, f (s + 1) = (1 + 2 / (s : ℝ)) * f s + 1) :
    ∀ s ≥ M0, f s = S M0 s := by
  have hM' : (0 : ℝ) < M0 := by exact_mod_cast hM
  intro s hs
  induction s, hs using Nat.le_induction with
  | base => rw [h0, S_init _ hM']
  | succ n hn ih =>
    have hn' : (0 : ℝ) < n := by
      have : (M0 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    rw [hrec n hn, ih]
    push_cast
    rw [S_rec _ _ hM' hn']

/-- Probability that two distinct random elements share an M-ancestor class = (S − s)/(s(s−1)) = 2(s−M)/((M+1)(s−1)) ≤ 2/(M+1), where s = N. -/
lemma same_class_bound (M s : ℝ) (hM : 1 ≤ M) (hs : M ≤ s) (hs2 : 1 < s) :
    (S M s - s) / (s * (s - 1)) = 2 * (s - M) / ((M + 1) * (s - 1)) ∧
      (S M s - s) / (s * (s - 1)) ≤ 2 / (M + 1) := by
  have hs1 : 0 < s - 1 := by linarith
  have hs0 : 0 < s := by linarith
  have hM1 : 0 < M + 1 := by linarith
  have h1 : (S M s - s) / (s * (s - 1)) = 2 * (s - M) / ((M + 1) * (s - 1)) := by
    unfold S
    rw [div_eq_div_iff (by positivity) (by positivity)]
    field_simp
    ring
  refine ⟨h1, ?_⟩
  rw [h1, div_le_div_iff₀ (by positivity) hM1]
  nlinarith

/-- Shell volume: (4/3)π((r+ε)³ − max(r−ε,0)³) ≤ 8π(r+ε)²ε. -/
lemma shell_volume (r ε : ℝ) (hr : 0 ≤ r) (hε : 0 ≤ ε) :
    4 / 3 * π * ((r + ε) ^ 3 - (max (r - ε) 0) ^ 3) ≤ 8 * π * (r + ε) ^ 2 * ε := by
  have hπ := Real.pi_pos
  rcases le_total ε r with h | h
  · rw [max_eq_left (by linarith)]
    have key : 4 / 3 * ((r + ε) ^ 3 - (r - ε) ^ 3) ≤ 8 * (r + ε) ^ 2 * ε := by
      nlinarith [mul_nonneg hr hε, mul_nonneg (mul_nonneg hr hε) hε, pow_nonneg hε 3]
    nlinarith [mul_le_mul_of_nonneg_left key hπ.le]
  · rw [max_eq_right (by linarith)]
    have h2 : r + ε ≤ 2 * ε := by linarith
    have hsq : 0 ≤ (r + ε) ^ 2 := sq_nonneg _
    have key : 4 / 3 * ((r + ε) ^ 3 - 0 ^ 3) ≤ 8 * (r + ε) ^ 2 * ε := by
      have : (r + ε) ^ 3 ≤ (r + ε) ^ 2 * (2 * ε) := by
        rw [pow_succ]; exact mul_le_mul_of_nonneg_left h2 hsq
      nlinarith [mul_nonneg hsq hε]
    nlinarith [mul_le_mul_of_nonneg_left key hπ.le]

/-- Hyperbolic polar coordinates: the density f_τ f_η /(4π) of (τ, η, ω) divided by the Jacobian τ³ sinh²η,
    with f_τ = (4τ³/λ) e^{−τ⁴/λ} (E ~ Exp(1)) and f_η = sinh²η e^{−α cosh η}/c. -/
lemma jacobian_cancel (τ η lam c α : ℝ) (hτ : 0 < τ) (hη : sinh η ≠ 0) (hl : 0 < lam)
    (hc : 0 < c) :
    ((4 * τ ^ 3 / lam) * exp (-(τ ^ 4) / lam)) * (sinh η ^ 2 * exp (-(α * cosh η)) / c) /
        (4 * π) / (τ ^ 3 * sinh η ^ 2) =
      exp (-(τ ^ 4) / lam - α * cosh η) / (π * lam * c) := by
  have hπ := Real.pi_pos
  rw [show -(τ ^ 4) / lam - α * cosh η = -(τ ^ 4) / lam + -(α * cosh η) by ring, Real.exp_add]
  field_simp

/-- The single-step 4D displacement density is bounded: ≤ e^{−α}/(πλc). -/
lemma density_bound (τ η lam c α : ℝ) (hl : 0 < lam) (hc : 0 < c) (hα : 0 ≤ α) :
    exp (-(τ ^ 4) / lam - α * cosh η) / (π * lam * c) ≤ exp (-α) / (π * lam * c) := by
  have hπ := Real.pi_pos
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Real.exp_le_exp.mpr
  have h1 := Real.one_le_cosh η
  have h2 : 0 ≤ τ ^ 4 / lam := by positivity
  have h3 : -(τ ^ 4) / lam = -(τ ^ 4 / lam) := by ring
  nlinarith

/-- Step 6: with M = ⌈ε^{-1/2}⌉, 2/(M+1) + CεM ≤ (2 + 2C)√ε. -/
lemma optimize_M (C ε : ℝ) (hC : 0 ≤ C) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ M : ℕ, 1 ≤ M ∧ 2 / ((M : ℝ) + 1) + C * ε * M ≤ (2 + 2 * C) * Real.sqrt ε := by
  set r := Real.sqrt ε with hr
  have hr0 : 0 < r := Real.sqrt_pos.mpr hε0
  have hr1 : r ≤ 1 := by
    have := Real.sqrt_le_sqrt hε1
    rwa [Real.sqrt_one] at this
  have hrr : r * r = ε := Real.mul_self_sqrt hε0.le
  refine ⟨⌈1 / r⌉₊, Nat.ceil_pos.mpr (by positivity), ?_⟩
  have hM1 : 1 / r ≤ (⌈1 / r⌉₊ : ℝ) := Nat.le_ceil _
  have hM2 : (⌈1 / r⌉₊ : ℝ) < 1 / r + 1 := Nat.ceil_lt_add_one (by positivity)
  set M : ℝ := (⌈1 / r⌉₊ : ℝ)
  have hrM : 1 ≤ r * M := by
    have := mul_le_mul_of_nonneg_left hM1 hr0.le
    rwa [mul_one_div_cancel hr0.ne'] at this
  have hrM' : r * M ≤ 1 + r := by
    have := mul_le_mul_of_nonneg_left hM2.le hr0.le
    rwa [mul_add, mul_one_div_cancel hr0.ne', mul_one] at this
  have hA : 2 / (M + 1) ≤ 2 * r := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hB : C * ε * M ≤ 2 * C * r := by
    rw [← hrr]
    have : r * (r * M) ≤ r * (1 + r) := mul_le_mul_of_nonneg_left hrM' hr0.le
    have : r * (1 + r) ≤ 2 * r := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left (show r * (r * M) ≤ 2 * r by linarith) hC]
  linarith

end CausalDensification.PosetLimitCore

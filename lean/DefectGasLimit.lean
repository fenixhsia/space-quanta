import Mathlib.Analysis.SpecialFunctions.Integrals.PosLog
import Mathlib.Analysis.SpecialFunctions.Integrability.Log
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.StrongLaw

open MeasureTheory ProbabilityTheory Filter Topology Real Set
open Complex (I)
open scoped ENNReal

noncomputable section

namespace CausalDensification.DefectGasLimit

/-! ## (A) Uniform phase measure and the torus -/

/-- Uniform probability measure for one phase: (2π)⁻¹ · Lebesgue on (0, 2π]. -/
def ν : Measure ℝ := (ENNReal.ofReal (2 * π))⁻¹ • volume.restrict (Ioc 0 (2 * π))

instance : IsProbabilityMeasure ν := by
  constructor
  simp only [ν, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    Real.volume_Ioc, sub_zero, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by simp [Real.pi_pos]) ENNReal.ofReal_ne_top

/-- The K-dimensional phase torus T^K (independent uniform phases). -/
def torus (K : ℕ) : Measure (Fin K → ℝ) := Measure.pi fun _ => ν

instance (K : ℕ) : IsProbabilityMeasure (torus K) := by unfold torus; infer_instance

/-- Integrating against ν is the unit-circle average. -/
lemma integral_ν_eq_circleAverage (f : ℂ → ℝ) :
    ∫ t, f (Complex.exp (t * I)) ∂ν = circleAverage f 0 1 := by
  rw [circleAverage_def, intervalIntegral.integral_of_le (by positivity), ν,
    integral_smul_measure, ENNReal.toReal_inv, ENNReal.toReal_ofReal (by positivity)]
  simp [circleMap, smul_eq_mul]

lemma circleIntegrable_log_norm_add (w : ℂ) : CircleIntegrable (fun z => log ‖z + w‖) 0 1 := by
  have h : MeromorphicOn (fun z : ℂ => z + w) (Metric.sphere 0 |(1 : ℝ)|) :=
    fun z _ => (analyticAt_id.add analyticAt_const).meromorphicAt
  exact h.circleIntegrable_log_norm

lemma integrable_ν_of_circleIntegrable {f : ℂ → ℝ} (hf : CircleIntegrable f 0 1) :
    Integrable (fun t : ℝ => f (Complex.exp (t * I))) ν := by
  have h := (intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity : (0 : ℝ) ≤ 2 * π)).mp hf
  have : (fun t : ℝ => f (Complex.exp (t * I))) = fun t => f (circleMap 0 1 t) := by
    funext t; simp [circleMap]
  rw [this]
  exact h.smul_measure (by simp [Real.pi_pos])

/-! ## (B) The Fubini step (inner Jensen) -/

/-- Inner Jensen: ∫ log‖e^{it} + w‖ dν(t) = log⁺‖w‖. -/
theorem inner_jensen (w : ℂ) : ∫ t, log ‖Complex.exp (t * I) + w‖ ∂ν = log⁺ ‖w‖ := by
  rw [integral_ν_eq_circleAverage (fun z => log ‖z + w‖)]
  simp

/-- Uniform bound on the inner |log|: ∫ |log‖e^{it}+w‖| dν ≤ 2 log(1 + ‖w‖). -/
theorem inner_abs_bound (w : ℂ) :
    ∫ t, ‖log ‖Complex.exp (t * I) + w‖‖ ∂ν ≤ 2 * log (1 + ‖w‖) := by
  have hi := integrable_ν_of_circleIntegrable (circleIntegrable_log_norm_add w)
  have hpos : ∀ t : ℝ, log⁺ ‖Complex.exp (t * I) + w‖ ≤ log (1 + ‖w‖) := by
    intro t
    have hle : ‖Complex.exp (t * I) + w‖ ≤ 1 + ‖w‖ := by
      calc ‖Complex.exp (t * I) + w‖ ≤ ‖Complex.exp (t * I)‖ + ‖w‖ := norm_add_le _ _
        _ = 1 + ‖w‖ := by rw [Complex.norm_exp_ofReal_mul_I]
    calc log⁺ ‖Complex.exp (t * I) + w‖ ≤ log⁺ (1 + ‖w‖) :=
          posLog_le_posLog (by linarith [norm_nonneg (Complex.exp (t * I) + w)]) hle
      _ = log (1 + ‖w‖) :=
          posLog_eq_log (by rw [abs_of_nonneg (by positivity)]; linarith [norm_nonneg w])
  have hpm : Measurable fun t : ℝ => log⁺ ‖Complex.exp (t * I) + w‖ := by
    unfold posLog; fun_prop
  have hpi : Integrable (fun t : ℝ => log⁺ ‖Complex.exp (t * I) + w‖) ν :=
    Integrable.mono' (integrable_const (log (1 + ‖w‖))) hpm.aestronglyMeasurable
      (ae_of_all _ fun t => by
        rw [Real.norm_of_nonneg posLog_nonneg]; exact hpos t)
  -- |log a| = 2 log⁺ a − log a
  have hid : ∀ t : ℝ, ‖log ‖Complex.exp (t * I) + w‖‖ =
      2 * log⁺ ‖Complex.exp (t * I) + w‖ - log ‖Complex.exp (t * I) + w‖ := by
    intro t
    rw [Real.norm_eq_abs, ← half_mul_log_add_log_abs]; ring
  simp_rw [hid]
  rw [integral_sub (hpi.const_mul 2) hi, integral_const_mul, inner_jensen]
  have h1 : ∫ t, log⁺ ‖Complex.exp (t * I) + w‖ ∂ν ≤ log (1 + ‖w‖) := by
    calc ∫ t, log⁺ ‖Complex.exp (t * I) + w‖ ∂ν ≤ ∫ _t, log (1 + ‖w‖) ∂ν :=
          integral_mono hpi (integrable_const _) hpos
      _ = log (1 + ‖w‖) := by simp
  linarith [posLog_nonneg (x := ‖w‖)]

/-- **Fubini step (abstract form)**: for bounded measurable w, log‖e^{it} + w(ω)‖ is integrable on ν⊗P,
    and its integral equals E_P[log⁺‖w‖]. -/
theorem fubini_jensen {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (w : Ω → ℂ) (hw : Measurable w) (B : ℝ) (hB : ∀ ω, ‖w ω‖ ≤ B) :
    Integrable (fun p : ℝ × Ω => log ‖Complex.exp (p.1 * I) + w p.2‖) (ν.prod P) ∧
      ∫ p, log ‖Complex.exp (p.1 * I) + w p.2‖ ∂(ν.prod P) = ∫ ω, log⁺ ‖w ω‖ ∂P := by
  have hc : Continuous fun t : ℝ => Complex.exp (t * I) := by fun_prop
  have hm : Measurable fun p : ℝ × Ω => log ‖Complex.exp (p.1 * I) + w p.2‖ :=
    Real.measurable_log.comp
      (((hc.measurable.comp measurable_fst).add (hw.comp measurable_snd)).norm)
  have hint : Integrable (fun p : ℝ × Ω => log ‖Complex.exp (p.1 * I) + w p.2‖) (ν.prod P) := by
    rw [integrable_prod_iff' hm.aestronglyMeasurable]
    refine ⟨ae_of_all _ fun ω =>
      integrable_ν_of_circleIntegrable (circleIntegrable_log_norm_add (w ω)), ?_⟩
    refine Integrable.mono' (integrable_const (2 * log (1 + B)))
      (hm.norm.stronglyMeasurable.integral_prod_left').aestronglyMeasurable
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    refine (inner_abs_bound (w ω)).trans ?_
    have := hB ω
    gcongr
  refine ⟨hint, ?_⟩
  rw [integral_prod_symm _ hint]
  simp_rw [inner_jensen]

/-! ## (C) The Mahler measure on the torus -/

/-- W_K(θ) = 1 + Σ_j e^{iθ_j}. -/
def W (K : ℕ) (θ : Fin K → ℝ) : ℂ := 1 + ∑ j, Complex.exp (θ j * I)

/-- Mahler measure m(1 + x₁ + … + x_K) = ∫_{T^K} log|W_K|. -/
def mahler (K : ℕ) : ℝ := ∫ θ, log ‖W K θ‖ ∂torus K

lemma continuous_W (K : ℕ) : Continuous (W K) := by
  unfold W; fun_prop

lemma measurable_logW (K : ℕ) : Measurable fun θ => log ‖W K θ‖ :=
  Real.measurable_log.comp (continuous_W K).measurable.norm

lemma norm_W_le (K : ℕ) (θ : Fin K → ℝ) : ‖W K θ‖ ≤ 1 + K := by
  unfold W
  calc ‖1 + ∑ j, Complex.exp (θ j * I)‖ ≤ ‖(1 : ℂ)‖ + ‖∑ j, Complex.exp (θ j * I)‖ :=
        norm_add_le _ _
    _ ≤ 1 + ∑ j : Fin K, ‖Complex.exp (θ j * I)‖ := by
        rw [norm_one]; gcongr; exact norm_sum_le _ _
    _ = 1 + K := by simp [Complex.norm_exp_ofReal_mul_I]

lemma W_succ (K : ℕ) (θ : Fin (K + 1) → ℝ) :
    W (K + 1) θ = Complex.exp (θ 0 * I) + W K (fun j => θ (Fin.succ j)) := by
  unfold W; rw [Fin.sum_univ_succ]; ring

/-- Split off phase 0: T^{K+1} ≅ T¹ × T^K (measure preserving). -/
lemma split_preserving (K : ℕ) :
    MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (K + 1) => ℝ) 0)
      (torus (K + 1)) (ν.prod (torus K)) :=
  measurePreserving_piFinSuccAbove (fun _ : Fin (K + 1) => ν) 0

lemma logW_succ_eq (K : ℕ) :
    (fun θ => log ‖W (K + 1) θ‖) =
      (fun p : ℝ × (Fin K → ℝ) => log ‖Complex.exp (p.1 * I) + W K p.2‖) ∘
        MeasurableEquiv.piFinSuccAbove (fun _ : Fin (K + 1) => ℝ) 0 := by
  funext θ
  simp only [Function.comp_apply, W_succ]
  rfl

/-- **Fubini step of Theorem 21**: m(1 + x₀ + … + x_K) = ∫_{T^K} log⁺|1 + x₁ + … + x_K|,
    and the integrand is integrable. -/
theorem mahler_succ (K : ℕ) :
    Integrable (fun θ => log ‖W (K + 1) θ‖) (torus (K + 1)) ∧
      mahler (K + 1) = ∫ θ, log⁺ ‖W K θ‖ ∂torus K := by
  obtain ⟨hI, hE⟩ := fubini_jensen (torus K) (W K) (continuous_W K).measurable (1 + K)
    (norm_W_le K)
  have e := split_preserving K
  constructor
  · rw [logW_succ_eq]
    exact (e.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).mpr hI
  · unfold mahler
    rw [logW_succ_eq]
    exact (e.integral_comp' _).trans hE

/-- log|W_K| is integrable on T^K (every K). -/
theorem integrable_logW (K : ℕ) : Integrable (fun θ => log ‖W K θ‖) (torus K) := by
  cases K with
  | zero => simp [W]
  | succ K => exact (mahler_succ K).1

/-- K = 1: Jensen gives m(1 + x) = 0 (random-phase level: neither extra cancellation nor growth). -/
theorem mahler_one : mahler 1 = 0 := by
  rw [(mahler_succ 0).2]
  simp [W]

/-- K ≥ 2: m(1 + x₁ + … + x_K) > 0. -/
theorem mahler_pos {K : ℕ} (hK : 2 ≤ K) : 0 < mahler K := by
  obtain ⟨K, rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
  have hK1 : 1 ≤ K := by omega
  have : Nonempty (Fin K) := ⟨⟨0, hK1⟩⟩
  rw [(mahler_succ K).2]
  have hmeas : Measurable fun θ => log⁺ ‖W K θ‖ := by
    have := (continuous_W K).measurable.norm
    unfold posLog
    exact measurable_const.max (Real.measurable_log.comp this)
  have hint : Integrable (fun θ => log⁺ ‖W K θ‖) (torus K) :=
    Integrable.mono' (integrable_const (log (1 + K))) hmeas.aestronglyMeasurable
      (ae_of_all _ fun θ => by
        rw [Real.norm_of_nonneg posLog_nonneg]
        calc log⁺ ‖W K θ‖ ≤ log⁺ (1 + K) :=
              posLog_le_posLog (by linarith [norm_nonneg (W K θ)]) (norm_W_le K θ)
          _ = log (1 + K) := posLog_eq_log (by rw [abs_of_nonneg (by positivity)]; linarith))
  rw [integral_pos_iff_support_of_nonneg (fun _ => posLog_nonneg) hint]
  -- the box (0, π/2)^K, on which Re W > 1
  set B : Set (Fin K → ℝ) := univ.pi fun _ => Ioo 0 (π / 2)
  have hB : B ⊆ Function.support fun θ => log⁺ ‖W K θ‖ := by
    intro θ hθ
    simp only [B, Set.mem_pi, mem_univ, forall_const] at hθ
    have hcos : ∀ j, 0 < Real.cos (θ j) := fun j =>
      Real.cos_pos_of_mem_Ioo ⟨by linarith [(hθ j).1, Real.pi_pos], (hθ j).2⟩
    have hre : (W K θ).re = 1 + ∑ j, Real.cos (θ j) := by
      simp [W, Complex.re_sum, Complex.exp_ofReal_mul_I_re]
    have hsum : 0 < ∑ j, Real.cos (θ j) := Finset.sum_pos (fun j _ => hcos j) Finset.univ_nonempty
    have h1 : 1 < ‖W K θ‖ := lt_of_lt_of_le (by linarith) (hre ▸ Complex.re_le_norm (W K θ))
    simp only [Function.mem_support, ne_eq, posLog_eq_zero_iff, abs_norm, not_le]
    exact h1
  refine lt_of_lt_of_le ?_ (measure_mono hB)
  rw [torus, Measure.pi_pi]
  refine pos_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun j _ => ?_)
  have hsub : Ioo 0 (π / 2) ⊆ Ioc 0 (2 * π) := fun x hx =>
    ⟨hx.1, by linarith [hx.2, Real.pi_pos]⟩
  simp only [ν, Measure.smul_apply, Measure.restrict_apply measurableSet_Ioo,
    inter_eq_left.mpr hsub, Real.volume_Ioo, smul_eq_mul, ne_eq, mul_eq_zero,
    ENNReal.inv_eq_zero, ENNReal.ofReal_ne_top, ENNReal.ofReal_eq_zero, not_le, false_or]
  linarith [Real.pi_pos]

/-! ## (C') The zero set is null -/

lemma slice_null (c : ℂ) : ν {t | Complex.exp (t * I) = c} = 0 := by
  rw [ν, Measure.smul_apply, Measure.restrict_apply' measurableSet_Ioc]
  suffices h : ({t : ℝ | Complex.exp (t * I) = c} ∩ Ioc 0 (2 * π)).Subsingleton by
    rw [h.measure_zero]; simp
  rintro a ⟨ha, ha0, ha1⟩ b ⟨hb, hb0, hb1⟩
  have hab : Complex.exp (a * I) = Complex.exp (b * I) := ha.trans hb.symm
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hab
  have him := congrArg Complex.im hn
  simp at him
  have h1 : (n : ℝ) < 1 := by nlinarith [Real.pi_pos]
  have h2 : (-1 : ℝ) < n := by nlinarith [Real.pi_pos]
  have hn1 : n < 1 := by exact_mod_cast h1
  have hn2 : -1 < n := by exact_mod_cast h2
  have : n = 0 := by omega
  subst this
  simpa using him

/-- W_K(θ) ≠ 0 almost everywhere. -/
theorem W_ne_zero_ae (K : ℕ) : ∀ᵐ θ ∂torus K, W K θ ≠ 0 := by
  cases K with
  | zero => exact ae_of_all _ fun θ => by simp [W]
  | succ K =>
    have e := split_preserving K
    set F : ℝ × (Fin K → ℝ) → ℂ := fun p => Complex.exp (p.1 * I) + W K p.2
    have hF : Measurable F := by
      have hc : Continuous fun t : ℝ => Complex.exp (t * I) := by fun_prop
      exact (hc.measurable.comp measurable_fst).add ((continuous_W K).measurable.comp measurable_snd)
    have hZ : MeasurableSet (F ⁻¹' {0}) := hF (measurableSet_singleton 0)
    have hnull : (ν.prod (torus K)) (F ⁻¹' {0}) = 0 := by
      rw [Measure.prod_apply_symm hZ]
      have hs : ∀ y, ν ((fun x : ℝ => (x, y)) ⁻¹' (F ⁻¹' {0})) = 0 := fun y => by
        have : (fun x : ℝ => (x, y)) ⁻¹' (F ⁻¹' {0}) = {t : ℝ | Complex.exp (t * I) = -W K y} := by
          ext t; simp [F, eq_neg_iff_add_eq_zero]
        rw [this]; exact slice_null _
      simp [hs]
    have hset : {θ | ¬W (K + 1) θ ≠ 0} =
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (K + 1) => ℝ) 0) ⁻¹' (F ⁻¹' {0}) := by
      ext θ
      simp only [mem_ofPred_eq, not_not, mem_preimage, mem_singleton_iff, F, W_succ]
      rfl
    rw [ae_iff, hset, e.measure_preimage hZ.nullMeasurableSet, hnull]

/-! ## (D) Factorisation + strong law of large numbers ⟹ Theorem 21 -/

/-- Exact factorisation of Theorem 21 (same as DefectGasAlgebra.defect_product). -/
theorem defect_product {M K : ℕ} (β : ℝ) (δ : Fin M → Fin (K + 1) → ℝ) :
    ∑ x : Fin M → Fin (K + 1), Complex.exp (I * β * ∑ s, δ s (x s)) =
      ∏ s, ∑ j, Complex.exp (I * β * δ s j) := by
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  push_cast
  rw [Finset.mul_sum, Complex.exp_sum]

/-- Single site: |Σ_j e^{iβδ_j}| = |W_K(θ)| with θ_j = β(δ_{j+1} − δ_0). -/
lemma norm_site {K : ℕ} (β : ℝ) (δ : Fin (K + 1) → ℝ) :
    ‖∑ j, Complex.exp (I * β * δ j)‖ = ‖W K (fun j => β * (δ j.succ - δ 0))‖ := by
  have key : ∑ j, Complex.exp (I * β * δ j) =
      Complex.exp (↑(β * δ 0) * I) * W K (fun j => β * (δ j.succ - δ 0)) := by
    rw [Fin.sum_univ_succ, W, mul_add, mul_one, Finset.mul_sum]
    congr 1
    · congr 1; push_cast; ring
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [key, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- If every site factor is nonzero: log|Σ_{configurations} e^{iβS}| = Σ_s log|P_s|. -/
lemma log_partition {M K : ℕ} (β : ℝ) (δ : Fin M → Fin (K + 1) → ℝ)
    (h : ∀ s, ∑ j, Complex.exp (I * β * δ s j) ≠ 0) :
    log ‖∑ x : Fin M → Fin (K + 1), Complex.exp (I * β * ∑ s, δ s (x s))‖ =
      ∑ s, log ‖∑ j, Complex.exp (I * β * δ s j)‖ := by
  rw [defect_product, norm_prod, Real.log_prod]
  intro s _; exact norm_ne_zero_iff.mpr (h s)

/-- **Strong-law substitution** (general law L): θ_s i.i.d. with law L and log|W| ∈ L¹(L) ⟹
    M⁻¹ Σ_{s<M} log|W(θ_s)| → ∫ log|W| dL a.s. -/
theorem slln_rate {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {K : ℕ} (L : Measure (Fin K → ℝ)) (θ : ℕ → Ω → Fin K → ℝ) (hmeas : ∀ s, Measurable (θ s))
    (hind : Pairwise fun i j => θ i ⟂ᵢ[P] θ j) (hlaw : ∀ s, P.map (θ s) = L)
    (hint : Integrable (fun φ => log ‖W K φ‖) L) :
    ∀ᵐ ω ∂P, Tendsto (fun M : ℕ => (M : ℝ)⁻¹ * ∑ s ∈ Finset.range M, log ‖W K (θ s ω)‖)
      atTop (𝓝 (∫ φ, log ‖W K φ‖ ∂L)) := by
  set g : (Fin K → ℝ) → ℝ := fun φ => log ‖W K φ‖ with hg_def
  have hg : Measurable g := measurable_logW K
  have hident : ∀ s, IdentDistrib (θ s) (θ 0) P P :=
    fun s => ⟨(hmeas s).aemeasurable, (hmeas 0).aemeasurable, by rw [hlaw, hlaw]⟩
  have hint0 : Integrable (g ∘ θ 0) P :=
    (integrable_map_measure hg.aestronglyMeasurable (hmeas 0).aemeasurable).mp
      (by rw [hlaw]; exact hint)
  have hlim : P[g ∘ θ 0] = ∫ φ, g φ ∂L := by
    rw [← hlaw 0, integral_map (hmeas 0).aemeasurable hg.aestronglyMeasurable]; rfl
  have h := strong_law_ae (fun s => g ∘ θ s) hint0 (fun i j hij => (hind hij).comp hg hg)
    (fun i => (hident i).comp hg)
  rw [hlim] at h
  filter_upwards [h] with ω hω
  simpa [smul_eq_mul, g] using hω

/-- Phase vector: θ_s = (β(δ_{s,j+1} − δ_{s,0}))_j. -/
def phase {Ω : Type*} {K : ℕ} (β : ℝ) (δ : ℕ → Ω → Fin (K + 1) → ℝ) (s : ℕ) (ω : Ω) :
    Fin K → ℝ := fun j => β * (δ s ω j.succ - δ s ω 0)

/-- Partition sum of order M: Z_M = Σ_{configurations} e^{iβ Σ_s δ_s}. -/
def Z {Ω : Type*} {K : ℕ} (β : ℝ) (δ : ℕ → Ω → Fin (K + 1) → ℝ) (M : ℕ) (ω : Ω) : ℂ :=
  ∑ x : Fin M → Fin (K + 1), Complex.exp (I * β * ∑ s : Fin M, δ s ω (x s))

/-- **Theorem 21 (defect gas)**: if the phase vectors of the sites are i.i.d. uniform on T^K, then almost surely
    (i) every Z_M ≠ 0, and (ii) M⁻¹ log|Z_M| → m(1 + x₁ + … + x_K). -/
theorem theorem21 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {K : ℕ} (β : ℝ) (δ : ℕ → Ω → Fin (K + 1) → ℝ)
    (hmeas : ∀ s, Measurable (phase β δ s))
    (hind : Pairwise fun i j => phase β δ i ⟂ᵢ[P] phase β δ j)
    (hlaw : ∀ s, P.map (phase β δ s) = torus K) :
    ∀ᵐ ω ∂P, (∀ M, Z β δ M ω ≠ 0) ∧
      Tendsto (fun M : ℕ => (M : ℝ)⁻¹ * log ‖Z β δ M ω‖) atTop (𝓝 (mahler K)) := by
  have hslln := slln_rate (torus K) (phase β δ) hmeas hind hlaw (integrable_logW K)
  have hnz : ∀ᵐ ω ∂P, ∀ s, W K (phase β δ s ω) ≠ 0 := by
    rw [ae_all_iff]
    intro s
    have := W_ne_zero_ae K
    rw [← hlaw s] at this
    exact ae_of_ae_map (hmeas s).aemeasurable this
  filter_upwards [hslln, hnz] with ω hω hnzω
  have hsite : ∀ s, ∑ j, Complex.exp (I * β * δ s ω j) ≠ 0 := fun s => by
    rw [← norm_ne_zero_iff, norm_site]; exact norm_ne_zero_iff.mpr (hnzω s)
  have hlog : ∀ M, log ‖Z β δ M ω‖ = ∑ s ∈ Finset.range M, log ‖W K (phase β δ s ω)‖ := by
    intro M
    rw [Z, log_partition β (fun s : Fin M => δ s ω) (fun s => hsite s)]
    rw [← Fin.sum_univ_eq_sum_range (fun s => log ‖W K (phase β δ s ω)‖) M]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [norm_site]; rfl
  refine ⟨fun M => ?_, ?_⟩
  · rw [Z, defect_product]
    exact Finset.prod_ne_zero_iff.mpr fun s _ => hsite s
  · simp_rw [hlog]; exact hω

/-- Corollary: the growth rate is 0 for K = 1 and > 0 for K ≥ 2 (defects are not cancelled by the phase). -/
theorem theorem21_dichotomy : mahler 1 = 0 ∧ ∀ K, 2 ≤ K → 0 < mahler K :=
  ⟨mahler_one, fun _ hK => mahler_pos hK⟩

end CausalDensification.DefectGasLimit

#print axioms CausalDensification.DefectGasLimit.theorem21
#print axioms CausalDensification.DefectGasLimit.theorem21_dichotomy
#print axioms CausalDensification.DefectGasLimit.mahler_succ
#print axioms CausalDensification.DefectGasLimit.fubini_jensen

/-
  Abstract measure-theoretic framework for Theorems 17–20 of "Causal Sets by Dynamical Densification".
  (A) Theorem 17 for general k-element suborders: continuity of the product measure pi + portmanteau; two-coordinate marginals = μ⊗μ;
      the boundary of the induced-suborder set A_Q ⊆ ⋃_{i≠j} {(x_i, x_j) null}.
  (B) Torus: the minimum-image-distance version on slab × (ℝ/ℤ)³.
  (C) Deterministic step of Theorem 20: (μ⊗μ)(Z) ≤ liminf (μ_N⊗μ_N)(Z_ε).
  (D) Step 6 of Theorem 18: summable L² along a subsequence ⟹ a.s. convergence; oscillation of averages between subsequence points.
  (E) Doeblin ⟹ uniform geometric ergodicity (Markov kernels on a general measurable space, functional form).
  (F) Probabilistic core of Theorem 19: bounded martingale differences + summable drift ⟹ a.s. convergence (via Mathlib's submartingale convergence theorem).
  (G) Step 3 of Theorem 18: the telescoping identity Φ − Φ∞ = Σ A⋯(A_i − B_i)B⋯ in a noncommutative ring.
-/
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Martingale.Convergence
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Analysis.PSeries
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.NoncommRing

open MeasureTheory Filter Topology Real TopologicalSpace Set ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace CausalDensification.PosetLimitFramework


/-! ## General topological lemmas -/

/-- The boundary of {f < g} is contained in {f = g}. -/
lemma frontier_lt_subset_eq {X : Type*} [TopologicalSpace X] {f g : X → ℝ}
    (hf : Continuous f) (hg : Continuous g) : frontier {p | f p < g p} ⊆ {p | f p = g p} := by
  rw [(isOpen_lt hf hg).frontier_eq]
  rintro p ⟨hcl, hnot⟩
  have hle := closure_lt_subset_le hf hg hcl
  simp only [Set.mem_ofPred_eq, not_lt] at hnot hle
  exact le_antisymm hle hnot

/-- If points near x have the same membership in A as x, then x is not on the boundary of A. -/
lemma not_mem_frontier_of_eventually {X : Type*} [TopologicalSpace X] {A : Set X} {x : X}
    (h : ∀ᶠ y in 𝓝 x, (y ∈ A ↔ x ∈ A)) : x ∉ frontier A := by
  intro hx
  by_cases hxA : x ∈ A
  · have : A ∈ 𝓝 x := by filter_upwards [h] with y hy using hy.mpr hxA
    exact hx.2 (mem_interior_iff_mem_nhds.mpr this)
  · have : Aᶜ ∈ 𝓝 x := by filter_upwards [h] with y hy using fun hyA => hxA (hy.mp hyA)
    exact (mem_closure_iff_nhds.mp hx.1 _ this).elim fun y hy => hy.1 hy.2

/-- Near a point off the boundary, membership is constant. -/
lemma eventually_of_not_mem_frontier {X : Type*} [TopologicalSpace X] {A : Set X} {x : X}
    (h : x ∉ frontier A) : ∀ᶠ y in 𝓝 x, (y ∈ A ↔ x ∈ A) := by
  by_cases hxA : x ∈ A
  · have hint : x ∈ interior A := by
      by_contra hn; exact h ⟨subset_closure hxA, hn⟩
    filter_upwards [mem_interior_iff_mem_nhds.mp hint] with y hy
    exact ⟨fun _ => hxA, fun _ => hy⟩
  · have hcl : x ∉ closure A := fun hc => h ⟨hc, fun hi => hxA (interior_subset hi)⟩
    have : Aᶜ ∈ 𝓝 x := by
      rw [← mem_interior_iff_mem_nhds, interior_compl]
      exact hcl
    filter_upwards [this] with y hy
    exact ⟨fun hyA => (hy hyA).elim, fun hxA' => (hxA hxA').elim⟩

/-! ## (A) General k: two-coordinate marginals and boundaries -/

section Marginal
variable {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}

/-- The marginal of a product probability measure on two distinct coordinates is μ⊗μ. -/
lemma pi_map_pair (μ : Measure Ω) [IsProbabilityMeasure μ] {i j : Fin k} (hij : i ≠ j) :
    (Measure.pi fun _ : Fin k => μ).map (fun x => (x i, x j)) = μ.prod μ := by
  have hmeas : Measurable (fun x : Fin k → Ω => (x i, x j)) :=
    (measurable_pi_apply i).prodMk (measurable_pi_apply j)
  symm
  apply Measure.prod_eq
  intro s t hs ht
  rw [Measure.map_apply hmeas (hs.prod ht)]
  classical
  let g : Fin k → Set Ω := fun l => if l = i then s else if l = j then t else univ
  have hset : (fun x : Fin k → Ω => (x i, x j)) ⁻¹' (s ×ˢ t) = univ.pi g := by
    ext x
    simp only [mem_preimage, mem_prod, mem_univ_pi, g]
    constructor
    · rintro ⟨h1, h2⟩ l
      by_cases hl : l = i
      · subst hl; simpa using h1
      · by_cases hl' : l = j
        · subst hl'; simp [hl, h2]
        · simp [hl, hl']
    · intro h
      refine ⟨by simpa using h i, ?_⟩
      have := h j
      simpa [Ne.symm hij] using this
  rw [hset, Measure.pi_pi]
  rw [← Finset.mul_prod_erase Finset.univ (fun l => μ (g l)) (Finset.mem_univ i)]
  rw [← Finset.mul_prod_erase (Finset.univ.erase i) (fun l => μ (g l))
    (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩)]
  have hrest : ∏ l ∈ (Finset.univ.erase i).erase j, μ (g l) = 1 := by
    apply Finset.prod_eq_one
    intro l hl
    have h1 : l ≠ j := (Finset.mem_erase.mp hl).1
    have h2 : l ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hl).2).1
    simp [g, h1, h2]
  rw [hrest, mul_one]
  simp [g, Ne.symm hij]

/-- k-tuples whose two coordinates lie in a μ⊗μ-null set form a pi μ-null set. -/
lemma pi_pair_null (μ : Measure Ω) [IsProbabilityMeasure μ] {i j : Fin k} (hij : i ≠ j)
    {Z : Set (Ω × Ω)} (hZm : MeasurableSet Z) (hZ : (μ.prod μ) Z = 0) :
    (Measure.pi fun _ : Fin k => μ) {x | (x i, x j) ∈ Z} = 0 := by
  have hmeas : Measurable (fun x : Fin k → Ω => (x i, x j)) :=
    (measurable_pi_apply i).prodMk (measurable_pi_apply j)
  have := Measure.map_apply hmeas hZm (μ := Measure.pi fun _ : Fin k => μ)
  rw [pi_map_pair μ hij] at this
  rw [show {x : Fin k → Ω | (x i, x j) ∈ Z} = (fun x => (x i, x j)) ⁻¹' Z from rfl, ← this, hZ]

end Marginal

section Induced
variable {Ω : Type*} [TopologicalSpace Ω] {k : ℕ}

/-- Induced-suborder set: k-tuples whose pairwise relations are exactly Q. -/
def inducedSet (R : Set (Ω × Ω)) (Q : Fin k → Fin k → Prop) : Set (Fin k → Ω) :=
  {x | ∀ i j, ((x i, x j) ∈ R ↔ Q i j)}

/-- If R is constant on the diagonal, the boundary of A_Q ⊆ ⋃_{i≠j} {(x_i,x_j) ∈ frontier R}. -/
lemma frontier_inducedSet_subset (R : Set (Ω × Ω)) (Q : Fin k → Fin k → Prop)
    (hdiag : ∀ x : Ω, (x, x) ∉ R) :
    frontier (inducedSet R Q) ⊆ ⋃ i, ⋃ j, ⋃ (_ : i ≠ j), {x | (x i, x j) ∈ frontier R} := by
  intro x hx
  by_contra hnot
  simp only [mem_iUnion, not_exists, mem_ofPred_eq] at hnot
  refine not_mem_frontier_of_eventually ?_ hx
  have hpair : ∀ i j, ∀ᶠ y in 𝓝 x, ((y i, y j) ∈ R ↔ (x i, x j) ∈ R) := by
    intro i j
    by_cases hij : i = j
    · subst hij
      exact Eventually.of_forall fun y => ⟨fun h => (hdiag _ h).elim, fun h => (hdiag _ h).elim⟩
    · have hc : Continuous fun y : Fin k → Ω => (y i, y j) :=
        (continuous_apply i).prodMk (continuous_apply j)
      exact (hc.tendsto x).eventually (eventually_of_not_mem_frontier (hnot i j hij))
  have hall : ∀ᶠ y in 𝓝 x, ∀ i j, ((y i, y j) ∈ R ↔ (x i, x j) ∈ R) := by
    rw [eventually_all]; intro i; rw [eventually_all]; exact hpair i
  filter_upwards [hall] with y hy
  simp only [inducedSet, mem_ofPred_eq]
  constructor
  · intro h i j; rw [← hy i j]; exact h i j
  · intro h i j; rw [hy i j]; exact h i j

end Induced

/-- Theorem 17 (general k): if pi μ does not charge the boundary of A, then pi μ_n (A) → pi μ (A). -/
theorem tuple_measure_tendsto {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]
    [SecondCountableTopology Ω] [PseudoMetrizableSpace Ω] [OpensMeasurableSpace Ω] {k : ℕ}
    {μ : ProbabilityMeasure Ω} {μs : ℕ → ProbabilityMeasure Ω} (hlim : Tendsto μs atTop (𝓝 μ))
    {A : Set (Fin k → Ω)}
    (hfr : (ProbabilityMeasure.pi (fun _ : Fin k => μ) : Measure (Fin k → Ω)) (frontier A) = 0) :
    Tendsto (fun n => (ProbabilityMeasure.pi (fun _ : Fin k => μs n) : Measure (Fin k → Ω)) A)
      atTop (𝓝 ((ProbabilityMeasure.pi (fun _ : Fin k => μ) : Measure (Fin k → Ω)) A)) := by
  have h : Tendsto (fun n => ProbabilityMeasure.pi (fun _ : Fin k => μs n)) atTop
      (𝓝 (ProbabilityMeasure.pi fun _ : Fin k => μ)) := by
    have hc := (ProbabilityMeasure.continuous_pi (α := fun _ : Fin k => Ω)).tendsto
      (fun _ => μ)
    exact hc.comp (tendsto_pi_nhds.mpr fun _ => hlim)
  exact ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' h hfr

/-- Theorem 17 (general k, full form): (H1) + (H2) ⟹ the density of every k-element induced suborder converges. -/
theorem induced_density_tendsto {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]
    [SecondCountableTopology Ω] [PseudoMetrizableSpace Ω] [BorelSpace Ω] {k : ℕ}
    {μ : ProbabilityMeasure Ω} {μs : ℕ → ProbabilityMeasure Ω} (hH1 : Tendsto μs atTop (𝓝 μ))
    (R Z : Set (Ω × Ω)) (hdiag : ∀ x : Ω, (x, x) ∉ R) (hfr : frontier R ⊆ Z)
    (hZm : MeasurableSet Z) (hH2 : ((μ : Measure Ω).prod (μ : Measure Ω)) Z = 0)
    (Q : Fin k → Fin k → Prop) :
    Tendsto (fun n => (ProbabilityMeasure.pi (fun _ : Fin k => μs n) : Measure (Fin k → Ω))
        (inducedSet R Q)) atTop
      (𝓝 ((ProbabilityMeasure.pi (fun _ : Fin k => μ) : Measure (Fin k → Ω)) (inducedSet R Q))) := by
  apply tuple_measure_tendsto hH1
  apply measure_mono_null (frontier_inducedSet_subset R Q hdiag)
  rw [ProbabilityMeasure.toMeasure_pi]
  apply (measure_iUnion_null_iff).mpr; intro i
  apply (measure_iUnion_null_iff).mpr; intro j
  apply (measure_iUnion_null_iff).mpr; intro hij
  apply measure_mono_null _ (pi_pair_null (μ : Measure Ω) hij hZm hH2)
  intro x hx; exact hfr hx

/-! ## (B) Torus slab × (ℝ/ℤ)³ -/

instance : MeasurableSpace (AddCircle (1 : ℝ)) := borel _
instance : BorelSpace (AddCircle (1 : ℝ)) := ⟨rfl⟩

abbrev Torus3 := Fin 3 → AddCircle (1 : ℝ)

/-- Minimum-image Euclidean distance √(Σ_k ‖Δy_k‖²), where ‖·‖ is the distance to the nearest integer. -/
def minImage (y y' : Torus3) : ℝ := Real.sqrt (∑ l, ‖y' l - y l‖ ^ 2)

abbrev Slab := ℝ × Torus3

def causalT : Set (Slab × Slab) := {p | minImage p.1.2 p.2.2 < p.2.1 - p.1.1}
def nullT : Set (Slab × Slab) := {p | minImage p.1.2 p.2.2 = p.2.1 - p.1.1}

lemma continuous_minImage : Continuous fun p : Slab × Slab => minImage p.1.2 p.2.2 := by
  unfold minImage; fun_prop

lemma frontier_causalT : frontier causalT ⊆ nullT :=
  frontier_lt_subset_eq continuous_minImage (by fun_prop)

lemma causalT_irrefl (x : Slab) : (x, x) ∉ causalT := by
  simp only [causalT, mem_ofPred_eq, sub_self, not_lt]
  exact Real.sqrt_nonneg _

lemma measurableSet_nullT : MeasurableSet nullT :=
  measurableSet_eq_fun continuous_minImage.measurable (by fun_prop)

/-- Theorem 17 on slab × torus: the density of every k-element induced suborder converges. -/
theorem induced_density_torus {k : ℕ} {μ : ProbabilityMeasure Slab}
    {μs : ℕ → ProbabilityMeasure Slab} (hH1 : Tendsto μs atTop (𝓝 μ))
    (hH2 : ((μ : Measure Slab).prod (μ : Measure Slab)) nullT = 0) (Q : Fin k → Fin k → Prop) :
    Tendsto (fun n => (ProbabilityMeasure.pi (fun _ : Fin k => μs n) : Measure (Fin k → Slab))
        (inducedSet causalT Q)) atTop
      (𝓝 ((ProbabilityMeasure.pi (fun _ : Fin k => μ) : Measure (Fin k → Slab))
        (inducedSet causalT Q))) :=
  induced_density_tendsto hH1 causalT nullT causalT_irrefl frontier_causalT measurableSet_nullT
    hH2 Q




/-! ## (C) Deterministic and Fatou steps of Theorem 20 -/

/-- Portmanteau (open sets): Z ⊆ G open ⟹ (μ⊗μ)(Z) ≤ liminf (μ_n⊗μ_n)(G). -/
theorem pair_le_liminf_open {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]
    [SecondCountableTopology Ω] [PseudoMetrizableSpace Ω] [OpensMeasurableSpace Ω]
    {μ : ProbabilityMeasure Ω} {μs : ℕ → ProbabilityMeasure Ω} (hlim : Tendsto μs atTop (𝓝 μ))
    {Z G : Set (Ω × Ω)} (hZG : Z ⊆ G) (hG : IsOpen G) :
    (μ.prod μ : Measure (Ω × Ω)) Z ≤
      atTop.liminf (fun n => ((μs n).prod (μs n) : Measure (Ω × Ω)) G) := by
  have h2 : Tendsto (fun n => (μs n).prod (μs n)) atTop (𝓝 (μ.prod μ)) := by
    have hc := (ProbabilityMeasure.continuous_prod (α := Ω) (β := Ω)).tendsto (μ, μ)
    exact hc.comp (hlim.prodMk_nhds hlim)
  exact (measure_mono hZG).trans (ProbabilityMeasure.le_liminf_measure_open_of_tendsto h2 hG)

/-- Fatou step: if a ≤ liminf b^ε_n (for every ε > 0) and ∫ b^ε_n ≤ δ(ε) → 0, then a = 0 a.e.
    Use: a(ω) = (μ∞⊗μ∞)(Z), b^ε_n(ω) = (μ_n⊗μ_n)(Z_ε). -/
theorem ae_zero_of_fatou {Ω' : Type*} [MeasurableSpace Ω'] (P : Measure Ω') (a : Ω' → ℝ≥0∞)
    (b : ℝ → ℕ → Ω' → ℝ≥0∞) (hb : ∀ ε n, Measurable (b ε n)) (ha : Measurable a)
    (hle : ∀ ε > 0, ∀ ω, a ω ≤ atTop.liminf (fun n => b ε n ω))
    (δ : ℝ → ℝ≥0∞) (hδ : Tendsto δ (𝓝[>] 0) (𝓝 0))
    (hbd : ∀ ε > 0, ∀ n, ∫⁻ ω, b ε n ω ∂P ≤ δ ε) : ∀ᵐ ω ∂P, a ω = 0 := by
  have key : ∀ ε > 0, ∫⁻ ω, a ω ∂P ≤ δ ε := by
    intro ε hε
    calc ∫⁻ ω, a ω ∂P ≤ ∫⁻ ω, atTop.liminf (fun n => b ε n ω) ∂P :=
          lintegral_mono fun ω => hle ε hε ω
      _ ≤ atTop.liminf (fun n => ∫⁻ ω, b ε n ω ∂P) := lintegral_liminf_le (hb ε)
      _ ≤ δ ε := liminf_le_of_frequently_le' (Frequently.of_forall fun n => hbd ε hε n)
  have h0 : ∫⁻ ω, a ω ∂P ≤ 0 := by
    apply ge_of_tendsto hδ
    filter_upwards [self_mem_nhdsWithin] with ε hε using key ε hε
  have : ∫⁻ ω, a ω ∂P = 0 := le_antisymm h0 zero_le
  exact (lintegral_eq_zero_iff ha).mp this

/-! ## (D) Step 6 of Theorem 18 -/

/-- If Σ_k E[Y_k²] < ∞ then Y_k → 0 a.s. (replaces Chebyshev + Borel–Cantelli). -/
theorem ae_tendsto_zero_of_summable_sq {Ω' : Type*} [MeasurableSpace Ω'] (P : Measure Ω')
    (Y : ℕ → Ω' → ℝ) (hY : ∀ k, AEMeasurable (Y k) P) (a : ℕ → ℝ) (ha0 : ∀ k, 0 ≤ a k)
    (ha : Summable a) (hbd : ∀ k, ∫⁻ ω, ENNReal.ofReal (Y k ω ^ 2) ∂P ≤ ENNReal.ofReal (a k)) :
    ∀ᵐ ω ∂P, Tendsto (fun k => Y k ω) atTop (𝓝 0) := by
  have hm : ∀ k, AEMeasurable (fun ω => ENNReal.ofReal (Y k ω ^ 2)) P :=
    fun k => ((hY k).pow_const 2).ennreal_ofReal
  have hint : ∫⁻ ω, ∑' k, ENNReal.ofReal (Y k ω ^ 2) ∂P ≠ ∞ := by
    rw [lintegral_tsum hm]
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hbd)
    rw [← ENNReal.ofReal_tsum_of_nonneg ha0 ha]
    exact ENNReal.ofReal_ne_top
  have hae := ae_lt_top' (AEMeasurable.ennreal_tsum hm) hint
  filter_upwards [hae] with ω hω
  have h1 := ENNReal.tendsto_atTop_zero_of_tsum_ne_top hω.ne
  have h2 : Tendsto (fun k => Y k ω ^ 2) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
    simpa [Function.comp_def, ENNReal.toReal_ofReal (sq_nonneg _)] using this
  have h3 : Tendsto (fun k => |Y k ω|) atTop (𝓝 0) := by
    have := (continuous_sqrt.tendsto 0).comp h2
    simpa [Function.comp_def, Real.sqrt_sq_eq_abs] using this
  exact (tendsto_zero_iff_abs_tendsto_zero _).mpr h3

/-- Along the geometric subsequence N_k = (1+δ)^k, N_k^{-p} is summable. -/
lemma summable_geom_rpow (δ p : ℝ) (hδ : 0 < δ) (hp : 0 < p) :
    Summable (fun k : ℕ => (((1 + δ) ^ k : ℝ) ^ (-p))) := by
  have h1 : 0 < 1 + δ := by linarith
  have e : (fun k : ℕ => (((1 + δ) ^ k : ℝ) ^ (-p))) = fun k : ℕ => ((1 + δ) ^ (-p)) ^ k := by
    funext k
    rw [← Real.rpow_natCast, ← Real.rpow_mul h1.le, mul_comm, Real.rpow_mul h1.le,
      Real.rpow_natCast]
  rw [e]
  apply summable_geometric_of_lt_one (by positivity)
  exact Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by linarith)

/-- Oscillation between subsequence points: |avg_N − avg_M| ≤ 2B(N − M)/N. -/
lemma avg_osc (a : ℕ → ℝ) (B : ℝ) (hB : ∀ i, |a i| ≤ B) (M N : ℕ) (hM : 0 < M) (hMN : M ≤ N) :
    |(∑ i ∈ Finset.range N, a i) / N - (∑ i ∈ Finset.range M, a i) / M| ≤
      2 * B * ((N : ℝ) - M) / N := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hN' : (0 : ℝ) < N := by exact_mod_cast lt_of_lt_of_le hM hMN
  have hMN' : (M : ℝ) ≤ N := by exact_mod_cast hMN
  have hsplit := Finset.sum_range_add_sum_Ico a hMN
  set SM := ∑ i ∈ Finset.range M, a i
  set SI := ∑ i ∈ Finset.Ico M N, a i
  have hSI : |SI| ≤ B * ((N : ℝ) - M) := by
    calc |SI| ≤ ∑ i ∈ Finset.Ico M N, |a i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ Finset.Ico M N, B := Finset.sum_le_sum fun i _ => hB i
      _ = B * ((N : ℝ) - M) := by
        rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hMN]; ring
  have hSM : |SM| ≤ B * M := by
    calc |SM| ≤ ∑ i ∈ Finset.range M, |a i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ Finset.range M, B := Finset.sum_le_sum fun i _ => hB i
      _ = B * M := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  rw [← hsplit]
  have e : (SM + SI) / N - SM / M = SI / N + SM * (M - N) / (M * N) := by
    field_simp; ring
  rw [e]
  have t1 : |SI / N| ≤ B * ((N : ℝ) - M) / N := by
    rw [abs_div, abs_of_pos hN']; exact div_le_div_of_nonneg_right hSI hN'.le
  have t2 : |SM * (M - N) / (M * N)| ≤ B * ((N : ℝ) - M) / N := by
    rw [abs_div, abs_mul, abs_of_pos (mul_pos hM' hN'),
      abs_of_nonpos (show (M : ℝ) - N ≤ 0 by linarith), div_le_div_iff₀ (mul_pos hM' hN') hN']
    have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 0)
    nlinarith [mul_le_mul_of_nonneg_right hSM (show (0 : ℝ) ≤ (N - M) * N by nlinarith)]
  calc _ ≤ |SI / N| + |SM * (M - N) / (M * N)| := abs_add_le _ _
    _ ≤ B * ((N : ℝ) - M) / N + B * ((N : ℝ) - M) / N := add_le_add t1 t2
    _ = 2 * B * ((N : ℝ) - M) / N := by ring




/-! ## (E) Doeblin ⟹ uniform geometric ergodicity (general measurable space) -/

section Doeblin
variable {α : Type*} [MeasurableSpace α]

lemma integrable_of_bounds (R : Measure α) [IsFiniteMeasure R] {f : α → ℝ} (hf : Measurable f)
    {a b : ℝ} (hab : ∀ x, a ≤ f x ∧ f x ≤ b) : Integrable f R := by
  refine Integrable.of_bound hf.aestronglyMeasurable (max |a| |b|)
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · have := (hab x).1; have := neg_abs_le a; have := le_max_left |a| |b|; linarith
  · have := (hab x).2; have := le_abs_self b; have := le_max_right |a| |b|; linarith

lemma integral_bounds (R : Measure α) [IsFiniteMeasure R] {f : α → ℝ} (hf : Measurable f)
    {a b : ℝ} (hab : ∀ x, a ≤ f x ∧ f x ≤ b) :
    a * R.real univ ≤ ∫ x, f x ∂R ∧ ∫ x, f x ∂R ≤ b * R.real univ := by
  have hi := integrable_of_bounds R hf hab
  constructor
  · have := integral_mono (integrable_const a) hi (fun x => (hab x).1)
    rwa [integral_const, smul_eq_mul, mul_comm] at this
  · have := integral_mono hi (integrable_const b) (fun x => (hab x).2)
    rwa [integral_const, smul_eq_mul, mul_comm] at this

/-- One-step contraction: if P, Q ≥ c·L then ∫f dP − ∫f dQ ≤ (1−c)(b−a). -/
lemma doeblin_one_step (P Q L : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    [IsProbabilityMeasure L] (c : ℝ≥0) (hc : c ≤ 1) (hP : c • L ≤ P) (hQ : c • L ≤ Q)
    {f : α → ℝ} (hf : Measurable f) {a b : ℝ} (hab : ∀ x, a ≤ f x ∧ f x ≤ b) :
    ∫ x, f x ∂P - ∫ x, f x ∂Q ≤ (1 - (c : ℝ)) * (b - a) := by
  have hdec : ∀ (R : Measure α) [IsProbabilityMeasure R], c • L ≤ R →
      ∫ x, f x ∂R = ∫ x, f x ∂(R - c • L) + ∫ x, f x ∂(c • L) ∧
        (R - c • L).real univ = 1 - (c : ℝ) := by
    intro R _ hR
    constructor
    · conv_lhs => rw [← Measure.sub_add_cancel_of_le hR]
      exact integral_add_measure (integrable_of_bounds _ hf hab) (integrable_of_bounds _ hf hab)
    · have hc' : (c : ℝ≥0∞) ≤ 1 := by exact_mod_cast hc
      rw [Measure.real, Measure.sub_apply MeasurableSet.univ hR, measure_univ,
        Measure.smul_apply, measure_univ, ENNReal.smul_def, smul_eq_mul, mul_one,
        ENNReal.toReal_sub_of_le hc' ENNReal.one_ne_top]
      simp
  obtain ⟨eP, mP⟩ := hdec P hP
  obtain ⟨eQ, mQ⟩ := hdec Q hQ
  have bP := integral_bounds (P - c • L) hf hab
  have bQ := integral_bounds (Q - c • L) hf hab
  rw [mP] at bP; rw [mQ] at bQ
  rw [eP, eQ]
  nlinarith [bP.1, bP.2, bQ.1, bQ.2]

variable (κ : Kernel α α) [IsMarkovKernel κ]

/-- Transfer operator (T g)(x) = ∫ g d κ(x). -/
def Tk (g : α → ℝ) : α → ℝ := fun x => ∫ y, g y ∂(κ x)

lemma Tk_measurable {g : α → ℝ} (hg : Measurable g) : Measurable (Tk κ g) :=
  (StronglyMeasurable.integral_kernel (κ := κ) hg.stronglyMeasurable).measurable

lemma Tk_bounds {g : α → ℝ} (hg : Measurable g) {a b : ℝ} (hab : ∀ x, a ≤ g x ∧ g x ≤ b) :
    ∀ x, a ≤ Tk κ g x ∧ Tk κ g x ≤ b := by
  intro x
  have := integral_bounds (κ x) hg hab
  simpa [Tk] using this

lemma Tk_contract [Nonempty α] (L : Measure α) [IsProbabilityMeasure L] (c : ℝ≥0) (hc : c ≤ 1)
    (hmin : ∀ x, c • L ≤ κ x) {g : α → ℝ} (hg : Measurable g) {a b : ℝ}
    (hab : ∀ x, a ≤ g x ∧ g x ≤ b) :
    ∃ a' b', (∀ x, a' ≤ Tk κ g x ∧ Tk κ g x ≤ b') ∧ b' - a' ≤ (1 - (c : ℝ)) * (b - a) := by
  have hb := Tk_bounds κ hg hab
  have hdiff : ∀ x y, Tk κ g x - Tk κ g y ≤ (1 - (c : ℝ)) * (b - a) :=
    fun x y => doeblin_one_step (κ x) (κ y) L c hc (hmin x) (hmin y) hg hab
  have hbddA : BddAbove (range (Tk κ g)) := ⟨b, by rintro _ ⟨x, rfl⟩; exact (hb x).2⟩
  have hbddB : BddBelow (range (Tk κ g)) := ⟨a, by rintro _ ⟨x, rfl⟩; exact (hb x).1⟩
  refine ⟨⨅ x, Tk κ g x, ⨆ x, Tk κ g x, fun x => ⟨ciInf_le hbddB x, le_ciSup hbddA x⟩, ?_⟩
  have : ⨆ x, Tk κ g x ≤ (⨅ y, Tk κ g y) + (1 - (c : ℝ)) * (b - a) := by
    apply ciSup_le; intro x
    have : Tk κ g x - (1 - (c : ℝ)) * (b - a) ≤ ⨅ y, Tk κ g y :=
      le_ciInf fun y => by linarith [hdiff x y]
    linarith
  linarith

/-- Iteration: osc(Tⁿ g) ≤ (1−c)ⁿ (b−a). -/
theorem doeblin_iterate [Nonempty α] (L : Measure α) [IsProbabilityMeasure L] (c : ℝ≥0)
    (hc : c ≤ 1) (hmin : ∀ x, c • L ≤ κ x) (n : ℕ) {g : α → ℝ} (hg : Measurable g) {a b : ℝ}
    (hab : ∀ x, a ≤ g x ∧ g x ≤ b) :
    Measurable ((Tk κ)^[n] g) ∧ ∃ a' b', (∀ x, a' ≤ (Tk κ)^[n] g x ∧ (Tk κ)^[n] g x ≤ b') ∧
      b' - a' ≤ (1 - (c : ℝ)) ^ n * (b - a) := by
  induction n with
  | zero => exact ⟨hg, a, b, hab, by simp⟩
  | succ n ih =>
    obtain ⟨hm, a', b', hab', hlen⟩ := ih
    rw [Function.iterate_succ_apply']
    refine ⟨Tk_measurable κ hm, ?_⟩
    obtain ⟨a'', b'', hab'', hlen'⟩ := Tk_contract κ L c hc hmin hm hab'
    refine ⟨a'', b'', hab'', ?_⟩
    have h1c : (0 : ℝ) ≤ 1 - c := by
      have : (c : ℝ) ≤ 1 := by exact_mod_cast hc
      linarith
    calc b'' - a'' ≤ (1 - (c : ℝ)) * (b' - a') := hlen'
      _ ≤ (1 - (c : ℝ)) * ((1 - (c : ℝ)) ^ n * (b - a)) := mul_le_mul_of_nonneg_left hlen h1c
      _ = (1 - (c : ℝ)) ^ (n + 1) * (b - a) := by ring

/-- Doeblin ⟹ uniform geometric ergodicity: for a stationary ν, |Tⁿg(x) − ν(g)| ≤ (1−c)ⁿ (b−a). -/
theorem doeblin_ergodic [Nonempty α] (L : Measure α) [IsProbabilityMeasure L] (c : ℝ≥0)
    (hc : c ≤ 1) (hmin : ∀ x, c • L ≤ κ x) (ν : Measure α) [IsProbabilityMeasure ν]
    (hstat : ∀ g : α → ℝ, Measurable g → (∃ a b, ∀ x, a ≤ g x ∧ g x ≤ b) →
      ∫ x, Tk κ g x ∂ν = ∫ x, g x ∂ν)
    (n : ℕ) {g : α → ℝ} (hg : Measurable g) {a b : ℝ} (hab : ∀ x, a ≤ g x ∧ g x ≤ b) (x : α) :
    |(Tk κ)^[n] g x - ∫ y, g y ∂ν| ≤ (1 - (c : ℝ)) ^ n * (b - a) := by
  have hstat_n : ∀ m, ∫ y, (Tk κ)^[m] g y ∂ν = ∫ y, g y ∂ν ∧ Measurable ((Tk κ)^[m] g) ∧
      ∀ y, a ≤ (Tk κ)^[m] g y ∧ (Tk κ)^[m] g y ≤ b := by
    intro m
    induction m with
    | zero => exact ⟨rfl, hg, hab⟩
    | succ m ih =>
      obtain ⟨hi, hm, hb⟩ := ih
      rw [Function.iterate_succ_apply']
      exact ⟨by rw [hstat _ hm ⟨a, b, hb⟩, hi], Tk_measurable κ hm, Tk_bounds κ hm hb⟩
  obtain ⟨_, a', b', hab', hlen⟩ := doeblin_iterate κ L c hc hmin n hg hab
  obtain ⟨hi, hm, _⟩ := hstat_n n
  have hbd := integral_bounds ν hm hab'
  simp only [probReal_univ, mul_one] at hbd
  rw [hi] at hbd
  rw [abs_le]
  constructor <;> linarith [(hab' x).1, (hab' x).2, hbd.1, hbd.2]

end Doeblin

/-! ## (F) Probabilistic core of Theorem 19: bounded martingale differences + summable drift ⟹ a.s. convergence -/

section SA
variable {Ω' : Type*} {m0 : MeasurableSpace Ω'} (P : Measure Ω') [IsProbabilityMeasure P]

theorem sa_converges (ℱ : Filtration ℕ m0) (d : ℕ → Ω' → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hd_meas : ∀ n, StronglyMeasurable[ℱ (n + 1)] (d n))
    (hd_bdd : ∀ n ω, |d n ω| ≤ C / ((n : ℝ) + 1))
    (hd_mart : ∀ n, P[d n | ℱ n] =ᵐ[P] 0)
    (a : ℕ → Ω' → ℝ) (c : ℕ → ℝ) (ha_bdd : ∀ n ω, |a n ω| ≤ c n) (hc : Summable c) :
    ∀ᵐ ω ∂P, ∃ l, Tendsto (fun n => ∑ i ∈ Finset.range n, (a i ω + d i ω)) atTop (𝓝 l) := by
  set M : ℕ → Ω' → ℝ := fun n ω => ∑ i ∈ Finset.range n, d i ω with hMdef
  have hd_sm : ∀ n, StronglyMeasurable[m0] (d n) := fun n => (hd_meas n).mono (ℱ.le _)
  have hd_int : ∀ n, Integrable (d n) P := fun n =>
    Integrable.of_bound (hd_sm n).aestronglyMeasurable (C / ((n : ℝ) + 1))
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hd_bdd n ω)
  have hM_adapted : StronglyAdapted ℱ M := by
    intro n
    have : M n = ∑ i ∈ Finset.range n, d i := by funext ω; simp [hMdef]
    rw [this]
    apply Finset.stronglyMeasurable_sum
    intro i hi
    exact (hd_meas i).mono (ℱ.mono (Finset.mem_range.mp hi))
  have hM_int : ∀ n, Integrable (M n) P := fun n => by
    have : M n = ∑ i ∈ Finset.range n, d i := by funext ω; simp [hMdef]
    rw [this]; exact integrable_finsetSum' _ fun i _ => hd_int i
  have hmart : Martingale M ℱ P := by
    apply martingale_of_condExp_sub_eq_zero_nat hM_adapted hM_int
    intro n
    have : M (n + 1) - M n = d n := by funext ω; simp [hMdef, Finset.sum_range_succ]
    rw [this]; exact hd_mart n
  -- |M n| is bounded
  have hM_bdd : ∀ n ω, |M n ω| ≤ ∑ i ∈ Finset.range n, C / ((i : ℝ) + 1) := by
    intro n ω
    calc |M n ω| ≤ ∑ i ∈ Finset.range n, |d i ω| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := Finset.sum_le_sum fun i _ => hd_bdd i ω
  have hsq_int : ∀ n, Integrable (fun ω => M n ω ^ 2) P := fun n =>
    Integrable.of_bound ((hM_int n).aestronglyMeasurable.pow 2)
      ((∑ i ∈ Finset.range n, C / ((i : ℝ) + 1)) ^ 2)
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hM_bdd n ω) 2)
  -- orthogonality: E[M_{n+1}²] ≤ E[M_n²] + (C/(n+1))²
  have hsq : ∀ n, ∫ ω, M n ω ^ 2 ∂P ≤ ∑ i ∈ Finset.range n, (C / ((i : ℝ) + 1)) ^ 2 := by
    intro n
    induction n with
    | zero => simp [hMdef]
    | succ n ih =>
      have hprod_int : Integrable (M n * d n) P :=
        Integrable.of_bound ((hM_int n).aestronglyMeasurable.mul (hd_int n).aestronglyMeasurable)
          ((∑ i ∈ Finset.range n, C / ((i : ℝ) + 1)) * (C / ((n : ℝ) + 1)))
          (Eventually.of_forall fun ω => by
            rw [Pi.mul_apply, Real.norm_eq_abs, abs_mul]
            exact mul_le_mul (hM_bdd n ω) (hd_bdd n ω) (abs_nonneg _)
              (le_trans (abs_nonneg _) (hM_bdd n ω)))
      have hcross : ∫ ω, M n ω * d n ω ∂P = 0 := by
        have h1 := condExp_mul_of_stronglyMeasurable_left (m := ℱ n) (μ := P) (hM_adapted n)
          hprod_int (hd_int n)
        have h2 : ∫ ω, (P[M n * d n | ℱ n]) ω ∂P = ∫ ω, (M n * d n) ω ∂P :=
          integral_condExp (ℱ.le n)
        have h1' : P[M n * d n | ℱ n] =ᵐ[P] 0 := h1.trans ((hd_mart n).mono fun ω hω => by
          show M n ω * (P[d n | ℱ n]) ω = (0 : Ω' → ℝ) ω
          rw [hω]; simp)
        have h3 : ∫ ω, (P[M n * d n | ℱ n]) ω ∂P = 0 := by
          rw [integral_congr_ae h1']; simp
        rw [← h3, h2]; rfl
      have hd2_int : Integrable (fun ω => d n ω ^ 2) P :=
        Integrable.of_bound ((hd_int n).aestronglyMeasurable.pow 2) ((C / ((n : ℝ) + 1)) ^ 2)
          (Eventually.of_forall fun ω => by
            rw [Real.norm_eq_abs, abs_pow]
            exact pow_le_pow_left₀ (abs_nonneg _) (hd_bdd n ω) 2)
      have hd2 : ∫ ω, d n ω ^ 2 ∂P ≤ (C / ((n : ℝ) + 1)) ^ 2 := by
        have := integral_mono hd2_int (integrable_const ((C / ((n : ℝ) + 1)) ^ 2))
          (fun ω => by
            have h := hd_bdd n ω
            calc d n ω ^ 2 = |d n ω| ^ 2 := (sq_abs _).symm
              _ ≤ (C / ((n : ℝ) + 1)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2)
        simpa using this
      have hexp : (fun ω => M (n + 1) ω ^ 2) =
          fun ω => M n ω ^ 2 + 2 * (M n ω * d n ω) + d n ω ^ 2 := by
        funext ω; simp only [hMdef, Finset.sum_range_succ]; ring
      have i1 : Integrable (fun ω => M n ω ^ 2) P := hsq_int n
      have i2 : Integrable (fun ω => 2 * (M n ω * d n ω)) P := by
        simpa [Pi.mul_apply] using hprod_int.const_mul 2
      have i12 : Integrable (fun ω => M n ω ^ 2 + 2 * (M n ω * d n ω)) P := i1.add i2
      rw [hexp, integral_add i12 hd2_int, integral_add i1 i2, integral_const_mul,
        hcross, Finset.sum_range_succ]
      linarith
  -- L¹ bounded
  have hs : Summable (fun i : ℕ => (C / ((i : ℝ) + 1)) ^ 2) := by
    have h := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
    convert h.mul_left (C ^ 2) using 1
    funext i; push_cast; field_simp
  set S := ∑' i : ℕ, (C / ((i : ℝ) + 1)) ^ 2
  have hbdd : ∀ n, eLpNorm (M n) 1 P ≤ ENNReal.ofReal (1 + S) := by
    intro n
    rw [eLpNorm_one_eq_lintegral_enorm (hM_int n).aestronglyMeasurable]
    calc ∫⁻ ω, ‖M n ω‖ₑ ∂P ≤ ∫⁻ ω, ENNReal.ofReal (1 + M n ω ^ 2) ∂P := by
          apply lintegral_mono; intro ω
          show ‖M n ω‖ₑ ≤ ENNReal.ofReal (1 + M n ω ^ 2)
          rw [Real.enorm_eq_ofReal_abs]
          apply ENNReal.ofReal_le_ofReal
          nlinarith [abs_nonneg (M n ω), sq_abs (M n ω)]
      _ = ENNReal.ofReal (∫ ω, (1 + M n ω ^ 2) ∂P) := by
          have i3 : Integrable (fun ω => 1 + M n ω ^ 2) P := (integrable_const 1).add (hsq_int n)
          rw [ofReal_integral_eq_lintegral_ofReal i3
            (Eventually.of_forall fun ω => by positivity)]
      _ ≤ ENNReal.ofReal (1 + S) := by
          apply ENNReal.ofReal_le_ofReal
          rw [integral_add (integrable_const 1) (hsq_int n)]
          simp only [integral_const, probReal_univ, smul_eq_mul, mul_one]
          have := hsq n
          have : ∑ i ∈ Finset.range n, (C / ((i : ℝ) + 1)) ^ 2 ≤ S := by
            simpa [S] using Summable.sum_le_tsum (Finset.range n) (fun i _ => sq_nonneg _) hs
          linarith
  have hconvM := hmart.submartingale.exists_ae_tendsto_of_bdd hbdd
  filter_upwards [hconvM] with ω ⟨lM, hlM⟩
  have hsa : Summable (fun i => a i ω) :=
    Summable.of_norm_bounded hc (fun i => by rw [Real.norm_eq_abs]; exact ha_bdd i ω)
  refine ⟨(∑' i, a i ω) + lM, ?_⟩
  have e : (fun n => ∑ i ∈ Finset.range n, (a i ω + d i ω)) =
      fun n => (∑ i ∈ Finset.range n, a i ω) + M n ω := by
    funext n; simp [hMdef, Finset.sum_add_distrib]
  rw [e]
  exact hsa.hasSum.tendsto_sum_nat.add hlM

end SA


/-! ## (G) The operator identity of step 3 of Theorem 18 -/


/-- Operator identity of step 3 of Theorem 18 (noncommutative ring):
    A₀⋯A_{n−1} − B₀⋯B_{n−1} = Σ_k A₀⋯A_{k−1}(A_k − B_k)B_{k+1}⋯B_{n−1}. -/
theorem telescope {R : Type*} [Ring R] (A B : ℕ → R) : ∀ n : ℕ,
    ((List.range n).map A).prod - ((List.range n).map B).prod =
      ∑ k ∈ Finset.range n,
        ((List.range k).map A).prod * (A k - B k) * ((List.range' (k + 1) (n - k - 1)).map B).prod
  | 0 => by simp
  | n + 1 => by
    have ih := telescope A B n
    have hkey : ∀ k ∈ Finset.range n, ((List.range' (k + 1) (n + 1 - k - 1)).map B).prod =
        ((List.range' (k + 1) (n - k - 1)).map B).prod * B n := by
      intro k hk
      have hk' : k < n := Finset.mem_range.mp hk
      have e : n + 1 - k - 1 = (n - k - 1) + 1 := by omega
      rw [e, List.range'_concat, List.map_append, List.prod_append]
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      congr 2; omega
    rw [Finset.sum_range_succ, Finset.sum_congr rfl (fun k hk' => by rw [hkey k hk'])]
    have hlast : n + 1 - n - 1 = 0 := by omega
    rw [hlast, List.range'_zero, List.map_nil, List.prod_nil, mul_one]
    simp only [List.range_succ, List.map_append, List.prod_append, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one]
    have e2 : ∑ k ∈ Finset.range n, ((List.range k).map A).prod * (A k - B k) *
        (((List.range' (k + 1) (n - k - 1)).map B).prod * B n) =
        (∑ k ∈ Finset.range n, ((List.range k).map A).prod * (A k - B k) *
          ((List.range' (k + 1) (n - k - 1)).map B).prod) * B n := by
      rw [Finset.sum_mul]; congr 1; funext k; noncomm_ring
    rw [e2, ← ih]
    noncomm_ring


end CausalDensification.PosetLimitFramework

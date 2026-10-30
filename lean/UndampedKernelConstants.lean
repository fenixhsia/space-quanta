/-
  Elementary parts of the proofs of Lemmas L1/L2 (Theorem 18) in "Causal Sets by Dynamical Densification".
  Covered: (F1) bounds on Z, the integral identity and stationarity of Z; (F2) properties of the three-shell overlap length ℓ;
  the lower-bound arithmetic of L1, the Lipschitz constants of L2, and the product ≤ exp inequality of Theorem 18.
  Not covered (treated as stated hypotheses): the shell-convolution formula itself, the W^{1,1} translation estimate,
  Doeblin ⇒ geometric ergodicity, and the measure-theoretic parts of the martingale and Borel–Cantelli arguments.
  Notation: T = 1/2 is written as a number.
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Real.Pi.Bounds


open Real intervalIntegral

noncomputable section

namespace CausalDensification.UndampedKernelConstants

/-! ## Time kernel: Z(t) = ∫₀^T |x - t| dx = (t² + (T - t)²)/2 -/

/-- Normalising constant Z(t), T = 1/2. -/
def Z (t : ℝ) : ℝ := (t ^ 2 + (1 / 2 - t) ^ 2) / 2

/-- Time kernel q(x | t) = |x - t| / Z(t). -/
def q (x t : ℝ) : ℝ := |x - t| / Z t

/-- (F1) Bounds on Z: T²/4 ≤ Z ≤ T²/2. -/
lemma Z_bounds {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1 / 2) : 1 / 16 ≤ Z t ∧ Z t ≤ 1 / 8 := by
  unfold Z
  constructor <;> nlinarith [sq_nonneg (t - 1 / 4)]

lemma Z_pos {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1 / 2) : 0 < Z t := by
  have := (Z_bounds h0 h1).1; linarith

/-- (F1) q(x|t) ≥ 8 |x - t|. -/
lemma q_lower {x t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1 / 2) : 8 * |x - t| ≤ q x t := by
  have hZ := Z_bounds h0 h1
  have hp := Z_pos h0 h1
  unfold q
  rw [le_div_iff₀ hp]
  have := abs_nonneg (x - t)
  nlinarith

/-- Z is indeed ∫₀^T |x - t| dx. -/
lemma integral_abs_sub {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1 / 2) :
    ∫ x in (0 : ℝ)..(1 / 2), |x - t| = Z t := by
  have hc : Continuous fun x : ℝ => |x - t| := continuous_abs.comp (continuous_id.sub continuous_const)
  rw [← integral_add_adjacent_intervals (b := t) (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  have e1 : ∫ x in (0 : ℝ)..t, |x - t| = ∫ x in (0 : ℝ)..t, (t - x) := by
    apply integral_congr
    intro x hx
    rw [Set.uIcc_of_le h0] at hx
    simp only
    rw [abs_of_nonpos (by linarith [hx.2])]; ring
  have e2 : ∫ x in t..(1 / 2 : ℝ), |x - t| = ∫ x in t..(1 / 2 : ℝ), (x - t) := by
    apply integral_congr
    intro x hx
    rw [Set.uIcc_of_le h1] at hx
    simp only
    rw [abs_of_nonneg (by linarith [hx.1])]
  rw [e1, e2, integral_sub intervalIntegrable_const intervalIntegral.intervalIntegrable_id,
    integral_sub intervalIntegral.intervalIntegrable_id intervalIntegrable_const]
  simp only [integral_const, integral_id, smul_eq_mul]
  unfold Z; ring

/-- Stationarity: ν_T ∝ Z is stationary for the time chain, ∫ Z(t) q(x|t) dt = Z(x). -/
lemma stationary {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) :
    ∫ t in (0 : ℝ)..(1 / 2), Z t * q x t = Z x := by
  have : ∫ t in (0 : ℝ)..(1 / 2), Z t * q x t = ∫ t in (0 : ℝ)..(1 / 2), |t - x| := by
    apply integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by norm_num)] at ht
    have hp := Z_pos ht.1 ht.2
    simp only [q]
    rw [abs_sub_comm x t]
    field_simp
  rw [this, integral_abs_sub h0 h1]

/-- Normalisation: ∫₀^T Z = T³/3 = 1/24, so ν_T(t) = 24 Z(t) = 3(t² + (T-t)²)/(2T³). -/
lemma integral_Z : ∫ t in (0 : ℝ)..(1 / 2), Z t = 1 / 24 := by
  have : (fun t : ℝ => Z t) = fun t => t ^ 2 - t / 2 + 1 / 8 := by
    funext t; unfold Z; ring
  rw [this]
  rw [integral_add (by apply Continuous.intervalIntegrable; fun_prop) intervalIntegrable_const,
    integral_sub (by apply Continuous.intervalIntegrable; fun_prop) (by apply Continuous.intervalIntegrable; fun_prop)]
  simp only [integral_pow, integral_const, smul_eq_mul, integral_div, integral_id]
  norm_num

/-- (F3) E[1/ρ | t] = T / Z(t) ≤ 8. -/
lemma inv_rho_bound {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1 / 2) : (1 / 2) / Z t ≤ 8 := by
  have hZ := Z_bounds h0 h1
  rw [div_le_iff₀ (Z_pos h0 h1)]; linarith

/-! ## t-direction of L2: Lipschitz constant 80 of q(x|·) -/

lemma Z_diff (t₁ t₂ : ℝ) : Z t₁ - Z t₂ = (t₁ - t₂) * (t₁ + t₂ - 1 / 2) := by
  unfold Z; ring

lemma q_lipschitz {x t₁ t₂ : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2)
    (h10 : 0 ≤ t₁) (h11 : t₁ ≤ 1 / 2) (h20 : 0 ≤ t₂) (h21 : t₂ ≤ 1 / 2) :
    |q x t₁ - q x t₂| ≤ 80 * |t₁ - t₂| := by
  have hZ1 := Z_bounds h10 h11
  have hZ2 := Z_bounds h20 h21
  have p1 := Z_pos h10 h11
  have p2 := Z_pos h20 h21
  have key : q x t₁ - q x t₂ =
      (|x - t₁| - |x - t₂|) / Z t₁ + |x - t₂| * (Z t₂ - Z t₁) / (Z t₁ * Z t₂) := by
    unfold q; field_simp; ring
  have hA : |(|x - t₁| - |x - t₂|)| ≤ |t₁ - t₂| := by
    have := abs_abs_sub_abs_le_abs_sub (x - t₁) (x - t₂)
    rwa [show x - t₁ - (x - t₂) = -(t₁ - t₂) by ring, abs_neg] at this
  have hB : |Z t₂ - Z t₁| ≤ |t₁ - t₂| / 2 := by
    rw [abs_sub_comm, Z_diff, abs_mul]
    have : |t₁ + t₂ - 1 / 2| ≤ 1 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    nlinarith [abs_nonneg (t₁ - t₂)]
  have hx2 : |x - t₂| ≤ 1 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hD : 1 / 256 ≤ Z t₁ * Z t₂ := by nlinarith
  rw [key]
  have e1 : |(|x - t₁| - |x - t₂|) / Z t₁| ≤ 16 * |t₁ - t₂| := by
    rw [abs_div, abs_of_pos p1, div_le_iff₀ p1]
    nlinarith [abs_nonneg (t₁ - t₂)]
  have e2 : |(|x - t₂| * (Z t₂ - Z t₁) / (Z t₁ * Z t₂))| ≤ 64 * |t₁ - t₂| := by
    rw [abs_div, abs_mul, abs_abs, abs_of_pos (mul_pos p1 p2), div_le_iff₀ (mul_pos p1 p2)]
    have h3 : |x - t₂| * |Z t₂ - Z t₁| ≤ (1 / 2) * (|t₁ - t₂| / 2) :=
      mul_le_mul hx2 hB (abs_nonneg _) (by norm_num)
    nlinarith [abs_nonneg (t₁ - t₂)]
  calc _ ≤ |(|x - t₁| - |x - t₂|) / Z t₁| + |(|x - t₂| * (Z t₂ - Z t₁) / (Z t₁ * Z t₂))| :=
        abs_add_le _ _
    _ ≤ 16 * |t₁ - t₂| + 64 * |t₁ - t₂| := add_le_add e1 e2
    _ = 80 * |t₁ - t₂| := by ring

/-! ## (F2) Three-shell overlap length ℓ(s) = |[|s-c|, s+c] ∩ [|a-b|, a+b]| -/

def ell (a b c s : ℝ) : ℝ := max 0 (min (s + c) (a + b) - max |s - c| |a - b|)

lemma ell_nonneg (a b c s : ℝ) : 0 ≤ ell a b c s := le_max_left _ _

lemma ell_le_two_min (a b c s : ℝ) (hs : 0 ≤ s) (hc : 0 ≤ c) :
    ell a b c s ≤ 2 * min s c := by
  unfold ell
  apply max_le
  · have := le_min hs hc; linarith
  · have h1 : min (s + c) (a + b) ≤ s + c := min_le_left _ _
    have h2 : |s - c| ≤ max |s - c| |a - b| := le_max_left _ _
    have h3 : s + c - |s - c| = 2 * min s c := by
      rcases le_total s c with h | h
      · rw [abs_of_nonpos (by linarith), min_eq_left h]; ring
      · rw [abs_of_nonneg (by linarith), min_eq_right h]; ring
    linarith

/-- Lipschitz form of |ℓ′| ≤ 2. -/
lemma ell_lipschitz (a b c s s' : ℝ) : |ell a b c s - ell a b c s'| ≤ 2 * |s - s'| := by
  unfold ell
  have hmin : |min (s + c) (a + b) - min (s' + c) (a + b)| ≤ |s - s'| := by
    have h1 := abs_min_sub_min_le_max (s + c) (a + b) (s' + c) (a + b)
    rwa [add_sub_add_right_eq_sub, sub_self, abs_zero, max_eq_left (abs_nonneg _)] at h1
  have hmax : |(max |s - c| |a - b|) - (max |s' - c| |a - b|)| ≤ |s - s'| := by
    have h1 := abs_max_sub_max_le_max |s - c| |a - b| |s' - c| |a - b|
    rw [sub_self, abs_zero, max_eq_left (abs_nonneg (|s - c| - |s' - c|))] at h1
    have h2 := abs_abs_sub_abs_le_abs_sub (s - c) (s' - c)
    rw [sub_sub_sub_cancel_right] at h2
    exact h1.trans h2
  set u := min (s + c) (a + b) - max |s - c| |a - b|
  set u' := min (s' + c) (a + b) - max |s' - c| |a - b|
  have hu : |u - u'| ≤ 2 * |s - s'| := by
    have e : u - u' = (min (s + c) (a + b) - min (s' + c) (a + b)) -
        (max |s - c| |a - b| - max |s' - c| |a - b|) := by simp only [u, u']; ring
    rw [e]
    calc _ ≤ |min (s + c) (a + b) - min (s' + c) (a + b)| +
          |(max |s - c| |a - b|) - (max |s' - c| |a - b|)| := abs_sub _ _
      _ ≤ _ := by linarith
  have h := abs_max_sub_max_le_abs u u' 0
  rw [max_comm u 0, max_comm u' 0] at h
  exact h.trans hu

/-- Difference-quotient form of |d(ℓ/s)/ds| ≤ 4/s (gives ‖∇h‖_{L¹} ≤ (a+b+c)²/(2abc)). -/
lemma ell_div_lipschitz (a b c s s' : ℝ) (hs : 0 < s) (hs' : 0 < s') (hc : 0 ≤ c) :
    |ell a b c s / s - ell a b c s' / s'| ≤ 4 * |s - s'| / s := by
  have hl := ell_lipschitz a b c s s'
  have h0 := ell_nonneg a b c s'
  have hb : ell a b c s' ≤ 2 * s' :=
    (ell_le_two_min a b c s' hs'.le hc).trans (by have := min_le_left s' c; linarith)
  have key : ell a b c s / s - ell a b c s' / s' =
      (ell a b c s - ell a b c s') / s + ell a b c s' * (s' - s) / (s * s') := by
    field_simp; ring
  rw [key]
  have e1 : |(ell a b c s - ell a b c s') / s| ≤ 2 * |s - s'| / s := by
    rw [abs_div, abs_of_pos hs]; exact div_le_div_of_nonneg_right hl hs.le
  have e2 : |ell a b c s' * (s' - s) / (s * s')| ≤ 2 * |s - s'| / s := by
    rw [abs_div, abs_mul, abs_of_nonneg h0, abs_of_pos (mul_pos hs hs'), abs_sub_comm s' s,
      div_le_div_iff₀ (mul_pos hs hs') hs]
    have := abs_nonneg (s - s')
    nlinarith [mul_le_mul_of_nonneg_right hb (mul_nonneg this hs.le)]
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ 2 * |s - s'| / s + 2 * |s - s'| / s := add_le_add e1 e2
    _ = 4 * |s - s'| / s := by ring

/-! ## L1: lower bound on the three-shell density for radii in [2/5, 1/2] -/

/-- Three-shell density on ℝ³ (rotation invariant, as a function of the radius s): h_abc(s) = ℓ(s)/(16π abc s). -/
def hdens (a b c s : ℝ) : ℝ := ell a b c s / (16 * π * a * b * c * s)

section radii
variable {a b c s : ℝ} (ha : 2 / 5 ≤ a) (ha' : a ≤ 1 / 2) (hb : 2 / 5 ≤ b) (hb' : b ≤ 1 / 2)
  (hc : 2 / 5 ≤ c) (hc' : c ≤ 1 / 2)
include ha ha' hb hb' hc hc'

lemma ell_small (hs0 : 0 < s) (hs : s ≤ 3 / 10) : ell a b c s = 2 * s := by
  unfold ell
  have hab : |a - b| ≤ 1 / 10 := abs_le.mpr ⟨by linarith, by linarith⟩
  rw [abs_of_nonpos (by linarith : s - c ≤ 0), max_eq_left (by linarith : |a - b| ≤ -(s - c)),
    min_eq_left (by linarith : s + c ≤ a + b), max_eq_right (by linarith)]
  ring

lemma ell_mid (hs : 3 / 10 ≤ s) (hs' : s ≤ 9 / 10) : 1 / 5 ≤ ell a b c s := by
  unfold ell
  apply le_max_of_le_right
  have h1 : 7 / 10 ≤ min (s + c) (a + b) := le_min (by linarith) (by linarith)
  have h2 : max |s - c| |a - b| ≤ 1 / 2 :=
    max_le (abs_le.mpr ⟨by linarith, by linarith⟩) (abs_le.mpr ⟨by linarith, by linarith⟩)
  linarith

lemma abc_bounds : 0 < a * b * c ∧ a * b * c ≤ 1 / 8 := by
  constructor
  · have : 0 < a := by linarith
    have : 0 < b := by linarith
    have : 0 < c := by linarith
    positivity
  · have h1 : a * b ≤ 1 / 4 := by nlinarith
    nlinarith

/-- Step 3 of L1: h_abc(s) ≥ 0.035 for 0 < s ≤ 0.9. -/
lemma hdens_lower (hs0 : 0 < s) (hs : s ≤ 9 / 10) : 7 / 200 ≤ hdens a b c s := by
  obtain ⟨hp, hq⟩ := abc_bounds ha ha' hb hb' hc hc'
  have hpi := Real.pi_pos
  have hpi' := Real.pi_lt_d2
  have hD : 0 < 16 * π * a * b * c * s := by
    have : 16 * π * a * b * c * s = 16 * π * (a * b * c) * s := by ring
    rw [this]; positivity
  unfold hdens
  rw [le_div_iff₀ hD]
  have e : 16 * π * a * b * c * s = 16 * π * (a * b * c) * s := by ring
  rw [e]
  rcases le_total s (3 / 10) with h | h
  · rw [ell_small ha ha' hb hb' hc hc' hs0 h]
    have : π * (a * b * c) ≤ 3.15 * (1 / 8) := mul_le_mul hpi'.le hq hp.le (by norm_num)
    nlinarith
  · have hl := ell_mid ha ha' hb hb' hc hc' h hs
    have h1 : π * (a * b * c) ≤ 3.15 * (1 / 8) := mul_le_mul hpi'.le hq hp.le (by norm_num)
    have h2 : π * (a * b * c) * s ≤ 3.15 * (1 / 8) * (9 / 10) :=
      mul_le_mul h1 hs hs0.le (by norm_num)
    nlinarith

end radii

/-- Every point of the torus is within √3/2 < 0.9 of the nearest lattice point. -/
lemma torus_radius : Real.sqrt 3 / 2 < 9 / 10 := by
  rw [div_lt_iff₀ (by norm_num)]
  rw [Real.sqrt_lt' (by norm_num)]
  norm_num

/-- Constant of step 4 of L1: 1.6 · 3.2³ · 1.2 · δ⁴ · 0.035 ≥ 1.37×10⁻⁵ (δ = 0.05);
    per-step density lower bounds 8·(T/2-δ), 8·(T-2δ), 8·(T/2-2δ). -/
lemma doeblin_constant :
    (8 * (1 / 4 - 1 / 20)) * (8 * (1 / 2 - 2 / 20)) ^ 3 * (8 * (1 / 4 - 2 / 20)) *
      (1 / 20 : ℝ) ^ 4 * (7 / 200) ≥ 137 / 10 ^ 7 := by
  norm_num

/-! ## Constants of L2 -/

/-- (G2): ½ · (3T)²/2 · 8³ = 288. -/
lemma G2_constant : (1 / 2 : ℝ) * ((3 * (1 / 2)) ^ 2 / 2) * 8 ^ 3 = 288 := by norm_num

/-- (G3): ½ · T · 80 = 20. -/
lemma G3_constant : (1 / 2 : ℝ) * (1 / 2) * 80 = 20 := by norm_num

/-- Total: (20 + 288)·√2 ≤ 436. -/
lemma L2_constant : (20 + 288 : ℝ) * Real.sqrt 2 ≤ 436 := by
  have h : Real.sqrt 2 < 1.4143 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  nlinarith

/-! ## Step 2 of Theorem 18: E θ^D = ∏(1 - (1-θ)/(i+1)) ≤ exp(-(1-θ) Σ 1/(i+1)) -/

lemma prod_le_exp (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (j N : ℕ) :
    ∏ i ∈ Finset.Ico j N, (1 - (1 - θ) / ((i : ℝ) + 1)) ≤
      Real.exp (-(1 - θ) * ∑ i ∈ Finset.Ico j N, 1 / ((i : ℝ) + 1)) := by
  rw [Finset.mul_sum, Real.exp_sum]
  apply Finset.prod_le_prod₀
  · intro i _
    have hi : (1 : ℝ) ≤ (i : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) i; linarith
    have : (1 - θ) / ((i : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by linarith)]; linarith
    linarith
  · intro i _
    have := Real.add_one_le_exp (-(1 - θ) / ((i : ℝ) + 1))
    have e : -(1 - θ) * (1 / ((i : ℝ) + 1)) = -(1 - θ) / ((i : ℝ) + 1) := by ring
    rw [e]; linarith [show -(1 - θ) / ((i : ℝ) + 1) = -((1 - θ) / ((i : ℝ) + 1)) by ring]

end CausalDensification.UndampedKernelConstants

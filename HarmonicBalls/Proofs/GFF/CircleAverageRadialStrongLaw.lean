import HarmonicBalls.Proofs.GFF.CircleAverageGaussianTail
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-! # Strong law at geometric radii

The one-circle Gaussian laws and their variances yield summable exponential
bounds. Borel–Cantelli gives both radial limits without using independence.
Credit: the import closure contains Leonardo Bonanno's LatticeProb code.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology ProbabilityTheory

namespace HarmonicBalls

private theorem gaussian_linear_tail {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    {b a : ℝ} (hb : 0 < b) (ha : 0 < a)
    (hg : ∀ n, HasGaussianLaw (X n) P)
    (hm : ∀ n, ∫ ω, X n ω ∂P = 0)
    (hv : ∀ n, Var[X n; P] = n * b) (n : ℕ) :
    P {ω | a * n < |X n ω|} ≤
      ENNReal.ofReal (2 * Real.exp (-(a ^ 2 / (2 * b)) * n)) := by
  let v : NNReal := ((n : ℝ) * b).toNNReal
  have hv' : (v : ℝ) = (n : ℝ) * b := Real.coe_toNNReal _ (by positivity)
  have hlaw : HasLaw (X n) (gaussianReal 0 v) P :=
    ⟨(hg n).aemeasurable, by rw [(hg n).map_eq_gaussianReal, hm n, hv n]⟩
  have hint : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * X n ω)) P := by
    intro t
    have hi := integrable_exp_mul_gaussianReal (μ := 0) (v := v) t
    rw [← hlaw.map_eq] at hi
    exact (integrable_map_measure (by fun_prop) (hg n).aemeasurable).1 hi
  let s : ℝ := a / b
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hbound : Real.exp (-s * (a * n)) * Real.exp (0 * s + v * s ^ 2 / 2) =
      Real.exp (-(a ^ 2 / (2 * b)) * n) := by
    rw [← Real.exp_add, hv']
    congr 1
    dsimp [s]
    field_simp
    ring
  have hup : P.real {ω | a * n ≤ X n ω} ≤ Real.exp (-(a ^ 2 / (2 * b)) * n) := by
    refine (measure_ge_le_exp_mul_mgf (a * n) hs (hint s)).trans ?_
    rw [mgf_gaussianReal hlaw, hbound]
  have hlow : P.real {ω | X n ω ≤ -(a * n)} ≤ Real.exp (-(a ^ 2 / (2 * b)) * n) := by
    refine (measure_le_le_exp_mul_mgf (-(a * n)) (neg_nonpos.2 hs) (hint (-s))).trans ?_
    rw [mgf_gaussianReal hlaw]
    convert hbound.le using 3 <;> ring
  have hsub : {ω | a * n < |X n ω|} ⊆
      {ω | a * n ≤ X n ω} ∪ {ω | X n ω ≤ -(a * n)} := by
    intro ω hω
    change a * n < |X n ω| at hω
    rcases le_abs'.1 (le_of_lt hω) with h | h
    · exact Or.inr h
    · exact Or.inl h
  calc P {ω | a * n < |X n ω|} ≤ P {ω | a * n ≤ X n ω} + P {ω | X n ω ≤ -(a * n)} :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ = ENNReal.ofReal (P.real {ω | a * n ≤ X n ω}) +
        ENNReal.ofReal (P.real {ω | X n ω ≤ -(a * n)}) := by
        rw [ofReal_measureReal, ofReal_measureReal]
    _ ≤ ENNReal.ofReal (Real.exp (-(a ^ 2 / (2 * b)) * n)) +
        ENNReal.ofReal (Real.exp (-(a ^ 2 / (2 * b)) * n)) :=
        add_le_add (ENNReal.ofReal_le_ofReal hup) (ENNReal.ofReal_le_ofReal hlow)
    _ = _ := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring

private theorem gaussian_linear_ae_tendsto {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    {b : ℝ} (hb : 0 < b) (hg : ∀ n, HasGaussianLaw (X n) P)
    (hm : ∀ n, ∫ ω, X n ω ∂P = 0) (hv : ∀ n, Var[X n; P] = n * b) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => X n ω / n) atTop (𝓝 0) := by
  have hevent : ∀ k : ℕ, ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop,
      |X n ω| ≤ (1 / (k + 1 : ℝ)) * n := by
    intro k
    let a : ℝ := 1 / (k + 1 : ℝ)
    have ha : 0 < a := by dsimp [a]; positivity
    let c : ℝ := a ^ 2 / (2 * b)
    have hc : 0 < c := by dsimp [c]; positivity
    have hsum : (∑' n : ℕ, P {ω | a * n < |X n ω|}) ≠ ∞ := by
      refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum (gaussian_linear_tail X hb ha hg hm hv))
      have hgeom : Summable (fun n : ℕ => 2 * (Real.exp (-c)) ^ n) :=
        (summable_geometric_of_lt_one (Real.exp_pos _).le
          (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hc))).mul_left 2
      simpa only [c, ← Real.exp_nat_mul, mul_comm] using hgeom.tsum_ofReal_ne_top
    filter_upwards [ae_eventually_notMem hsum] with ω hω
    exact hω.mono fun n hn => le_of_not_gt hn
  filter_upwards [ae_all_iff.mpr hevent] with ω hω
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  filter_upwards [hω k, eventually_gt_atTop 0] with n hn hn0
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_nonneg (show (0 : ℝ) ≤ n from Nat.cast_nonneg n)]
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn0
  exact (div_le_iff₀ hnpos).2 hn |>.trans_lt hk

/-- The variance of an origin-centered circle average is the absolute logarithm
of its radius, including the normalized unit circle. -/
theorem IsWholePlaneGFF.variance_circle_origin {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) {r : ℝ} (hr : 0 < r) :
    Var[fun ω => hcirc ω r 0; P] = |Real.log r| := by
  have heq : (fun ω => hcirc ω r 0) =ᵐ[P] (fun ω => hcirc ω r 0 - hcirc ω 1 0) := by
    filter_upwards [h.ae_circleAverage_one_zero] with ω hω
    simp only [hω, sub_zero]
  rw [variance_congr heq, h.variance_circle_sub_circle hr one_pos 0, Real.log_one, sub_zero]

private theorem IsWholePlaneGFF.ae_geometric_circle_div_nat
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) {r : ℝ} (hr : 0 < r)
    (hlog : 0 < |Real.log r|) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => hcirc ω (r ^ n) 0 / n) atTop (𝓝 0) := by
  let : IsProbabilityMeasure P := h.isProbabilityMeasure
  apply gaussian_linear_ae_tendsto (fun n ω => hcirc ω (r ^ n) 0) hlog
  · intro n
    exact h.hasGaussianLaw_circle (pow_pos hr n) 0
  · intro n
    exact h.integral_eq_zero (.circle (r ^ n) 0) (pow_pos hr n)
  · intro n
    rw [h.variance_circle_origin (pow_pos hr n), Real.log_pow, abs_mul,
      abs_of_nonneg (Nat.cast_nonneg n)]

/-- For every fixed `q > 1`, normalized circle averages converge to zero at
both the outward and inverse geometric radii, on the same event. -/
theorem IsWholePlaneGFF.ae_geometric_circle_radial_strong_law
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) {q : ℝ} (hq : 1 < q) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ => hcirc ω (q ^ n) 0 / (n * Real.log q)) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => hcirc ω (q⁻¹ ^ n) 0 / (n * Real.log q)) atTop (𝓝 0) := by
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hlog : 0 < Real.log q := Real.log_pos hq
  have hlogq : 0 < |Real.log q| := abs_pos.mpr hlog.ne'
  have hlogi : 0 < |Real.log q⁻¹| := by rw [Real.log_inv, abs_neg]; exact hlogq
  filter_upwards [h.ae_geometric_circle_div_nat hq0 hlogq,
    h.ae_geometric_circle_div_nat (inv_pos.mpr hq0) hlogi] with ω ho hi
  constructor
  · simpa only [div_div, zero_div] using ho.div_const (Real.log q)
  · simpa only [div_div, zero_div] using hi.div_const (Real.log q)

#print axioms IsWholePlaneGFF.variance_circle_origin
#print axioms IsWholePlaneGFF.ae_geometric_circle_radial_strong_law

end HarmonicBalls

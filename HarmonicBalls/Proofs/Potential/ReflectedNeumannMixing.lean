import HarmonicBalls.Proofs.Potential.ReflectedClockOccupationEveryStart
import HarmonicBalls.Proofs.Potential.ReflectedClockGreenBound
import HarmonicBalls.Proofs.Potential.ReflectedHeatKernelUniqueness

/-!
# The Chapman–Kolmogorov identity and exponential mixing of the Neumann kernel of the square

For the Neumann heat kernel `k_s(x, y)` of the unit square `K₀ = [0, 1]²`, written here as the real
function `neumannKernel` of the time `s : ℝ`:

* `k_s` is jointly continuous and bounded on `[a, b] × K₀ × K₀` for `0 < a ≤ b`
  (`continuousOn_neumannKernel`, `exists_neumannKernel_le`), and `∫_{K₀} k_s(x, y) dy = 1`
  (`setIntegral_neumannKernel_eq_one`);
* the Chapman–Kolmogorov identity `k_{s+t}(x, y) = ∫_{K₀} k_s(x, z) k_t(z, y) dz` holds at every
  pair of points of `K₀` (`neumannKernel_add`): it holds for almost every `y` by the Markov
  property of reflected Brownian motion, and then everywhere by continuity, since Lebesgue measure
  charges every relative ball of `K₀`;
* `k_1 ≥ δ > 0` on `K₀ × K₀` (`exists_le_neumannKernel_one`), from the term `n = 0` of the image
  sum; Doeblin's argument then gives `|k_s(x, y) - 1| ≤ C e^{-c s}` for `s ≥ 1`
  (`exists_abs_neumannKernel_sub_one_le`): writing `k_1(x, ·) = δ + a` with `a ≥ 0` of mass
  `1 - δ`, the oscillation of `k_{s+1}(·, y)` is at most `1 - δ` times that of `k_s(·, y)`.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology MarkovProcess Metric
open scoped ENNReal NNReal

namespace HarmonicBalls

/-- The Neumann heat kernel of the unit square as a real function of the time `s : ℝ`. -/
noncomputable def neumannKernel (s : ℝ) (x y : ℂ) : ℝ :=
  (squareNeumannKernel s.toNNReal x y).toReal

theorem neumannKernel_nonneg (s : ℝ) (x y : ℂ) : 0 ≤ neumannKernel s x y :=
  ENNReal.toReal_nonneg

theorem neumannKernel_comm (s : ℝ) (x y : ℂ) : neumannKernel s x y = neumannKernel s y x := by
  unfold neumannKernel
  rw [squareNeumannKernel_comm]

theorem measurable_neumannKernel_uncurry :
    Measurable fun p : ℝ × ℂ × ℂ => neumannKernel p.1 p.2.1 p.2.2 :=
  ENNReal.measurable_toReal.comp (measurable_squareNeumannKernel_uncurry.comp
    ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd))

theorem measurable_neumannKernel (s : ℝ) (x : ℂ) : Measurable (neumannKernel s x) :=
  measurable_neumannKernel_uncurry.comp
    (measurable_const.prodMk (measurable_const.prodMk measurable_id))

theorem measurable_neumannKernel_left (s : ℝ) (y : ℂ) :
    Measurable fun z => neumannKernel s z y :=
  measurable_neumannKernel_uncurry.comp
    (measurable_const.prodMk (measurable_id.prodMk measurable_const))

theorem measurableSet_closedSquare_zero_one : MeasurableSet (closedSquare (0 : ℂ) 1) :=
  (isCompact_closedSquare 0 1).isClosed.measurableSet

theorem re_im_mem_of_mem_closedSquare_zero_one {x : ℂ} (hx : x ∈ closedSquare 0 1) :
    x.re ∈ Icc (0 : ℝ) 1 ∧ x.im ∈ Icc (0 : ℝ) 1 := by
  simpa [closedSquare, Complex.mem_reProdIm] using hx

instance isFiniteMeasure_volume_restrict_closedSquare :
    IsFiniteMeasure (volume.restrict (closedSquare (0 : ℂ) 1)) :=
  ⟨by rw [Measure.restrict_apply_univ]; exact (isCompact_closedSquare 0 1).measure_lt_top⟩

/-- The unit square has Lebesgue measure `1`. -/
theorem volume_closedSquare_zero_one : volume (closedSquare (0 : ℂ) 1) = 1 := by
  have h := setLIntegral_closedSquare_zero_one_eq (f := fun _ : ℂ => (1 : ℝ≥0∞)) measurable_const
  simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc, sub_zero,
    ENNReal.ofReal_one, one_mul] at h
  exact h

instance isProbabilityMeasure_volume_restrict_closedSquare :
    IsProbabilityMeasure (volume.restrict (closedSquare (0 : ℂ) 1)) :=
  ⟨by rw [Measure.restrict_apply_univ, volume_closedSquare_zero_one]⟩

/-- **Lebesgue measure charges every relative ball of the unit square.** -/
theorem volume_ball_inter_closedSquare_pos {y : ℂ} (hy : y ∈ closedSquare 0 1) {r : ℝ}
    (hr : 0 < r) : 0 < volume (ball y r ∩ closedSquare 0 1) := by
  have hint : interior (closedSquare (0 : ℂ) 1) = Ioo (0 : ℝ) 1 ×ℂ Ioo (0 : ℝ) 1 := by
    simp [closedSquare, Complex.interior_reProdIm]
  have hcl : y ∈ closure (interior (closedSquare (0 : ℂ) 1)) := by
    rw [hint, Complex.closure_reProdIm, closure_Ioo zero_ne_one]
    simpa [closedSquare] using hy
  obtain ⟨z, hz1, hz2⟩ := Metric.mem_closure_iff.1 hcl r hr
  have hne : (ball y r ∩ interior (closedSquare (0 : ℂ) 1)).Nonempty :=
    ⟨z, mem_ball.2 (by rw [dist_comm]; exact hz2), hz1⟩
  exact ((isOpen_ball.inter isOpen_interior).measure_pos volume hne).trans_le
    (measure_mono (inter_subset_inter_right _ interior_subset))

theorem setIntegral_const_closedSquare (c : ℝ) : ∫ _ in closedSquare (0 : ℂ) 1, c = c := by
  simp

theorem integrableOn_closedSquare_of_abs_le {f : ℂ → ℝ} (hf : AEStronglyMeasurable f
    (volume.restrict (closedSquare (0 : ℂ) 1))) {C : ℝ}
    (hC : ∀ z ∈ closedSquare 0 1, |f z| ≤ C) : IntegrableOn f (closedSquare 0 1) :=
  Integrable.of_bound hf C ((ae_restrict_iff' measurableSet_closedSquare_zero_one).2
    (Eventually.of_forall fun z hz => by rw [Real.norm_eq_abs]; exact hC z hz))

/-! ### The real kernel -/

theorem coe_toNNReal_of_pos {s : ℝ} (hs : 0 < s) : ((s.toNNReal : ℝ≥0) : ℝ) = s :=
  Real.coe_toNNReal s hs.le

theorem neumannKernel_eq {s : ℝ} (hs : 0 < s) {x y : ℂ} (hx : x ∈ closedSquare 0 1)
    (hy : y ∈ closedSquare 0 1) :
    neumannKernel s x y = intervalNeumannKernelReal s.toNNReal x.re y.re *
      intervalNeumannKernelReal s.toNNReal x.im y.im := by
  have hs0 : s.toNNReal ≠ 0 := (Real.toNNReal_pos.2 hs).ne'
  have hy' := re_im_mem_of_mem_closedSquare_zero_one hy
  have hP : 0 ≤ intervalNeumannKernelReal s.toNNReal x.re y.re *
      intervalNeumannKernelReal s.toNNReal x.im y.im :=
    mul_nonneg (tsum_nonneg (intervalNeumannTerm_nonneg _ _ _))
      (tsum_nonneg (intervalNeumannTerm_nonneg _ _ _))
  rw [neumannKernel, squareNeumannKernel_eq_ofReal hs0 hx
    ⟨by linarith [hy'.1.1], by linarith [hy'.1.2]⟩ ⟨by linarith [hy'.2.1], by linarith [hy'.2.2]⟩,
    ENNReal.toReal_ofReal hP]

theorem ofReal_neumannKernel {s : ℝ} (hs : 0 < s) {x y : ℂ} (hx : x ∈ closedSquare 0 1)
    (hy : y ∈ closedSquare 0 1) :
    ENNReal.ofReal (neumannKernel s x y) = squareNeumannKernel s.toNNReal x y := by
  have hs0 : s.toNNReal ≠ 0 := (Real.toNNReal_pos.2 hs).ne'
  have hy' := re_im_mem_of_mem_closedSquare_zero_one hy
  rw [squareNeumannKernel_eq_ofReal hs0 hx
    ⟨by linarith [hy'.1.1], by linarith [hy'.1.2]⟩ ⟨by linarith [hy'.2.1], by linarith [hy'.2.2]⟩,
    neumannKernel_eq hs hx hy]

/-- **A uniform bound for the kernel** on `[a, b] × K₀ × K₀`. -/
theorem exists_neumannKernel_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Icc a b, ∀ x ∈ closedSquare 0 1, ∀ y ∈ closedSquare 0 1,
      neumannKernel s x y ≤ C := by
  obtain ⟨C, hC, hle⟩ := exists_squareNeumannKernel_le ha hab
  refine ⟨C.toReal, ENNReal.toReal_nonneg, fun s hs x hx y hy => ?_⟩
  have hs0 : 0 < s := ha.trans_le hs.1
  exact ENNReal.toReal_mono hC (hle _ (by rw [coe_toNNReal_of_pos hs0]; exact hs.1)
    (by rw [coe_toNNReal_of_pos hs0]; exact hs.2) x hx y hy)

/-- Continuity of the interval kernel in `(s, u, v)` on `[a, b] × [0, 1] × [-1, 2]`. -/
theorem continuousOn_intervalNeumannKernelReal_uncurry {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ContinuousOn (fun p : ℝ≥0 × ℝ × ℝ => intervalNeumannKernelReal p.1 p.2.1 p.2.2)
      ({p | a ≤ (p.1 : ℝ) ∧ (p.1 : ℝ) ≤ b} ∩
        {p | p.2.1 ∈ Icc (0 : ℝ) 1 ∧ p.2.2 ∈ Icc (-1 : ℝ) 2}) := by
  unfold intervalNeumannKernelReal
  refine continuousOn_tsum (u := fun n : ℤ => 2 * ((Real.sqrt (2 * Real.pi * a))⁻¹ *
      Real.exp (3 / (2 * a)) * Real.exp (-(1 / (2 * b)) * |(n : ℝ)|))) (fun n => ?_) ?_ ?_
  · unfold intervalNeumannTerm
    have hg := continuousOn_gaussianPDFReal_zero (f := fun q : ℝ≥0 × ℝ => q.2) continuous_snd ha
    have hm : ∀ c : ℝ, MapsTo (fun p : ℝ≥0 × ℝ × ℝ => (p.1, c * p.2.2 - p.2.1 + 2 * (n : ℝ)))
        ({p : ℝ≥0 × ℝ × ℝ | a ≤ (p.1 : ℝ) ∧ (p.1 : ℝ) ≤ b} ∩
          {p | p.2.1 ∈ Icc (0 : ℝ) 1 ∧ p.2.2 ∈ Icc (-1 : ℝ) 2}) {q | a ≤ (q.1 : ℝ)} :=
      fun c p hp => hp.1.1
    have h1 := hg.comp (Continuous.continuousOn (by fun_prop)) (hm 1)
    have h2 := hg.comp (Continuous.continuousOn (by fun_prop)) (hm (-1))
    refine (h1.add h2).congr fun p _ => ?_
    simp only [Pi.add_apply, Function.comp_apply, one_mul, neg_one_mul]
  · exact ((summable_exp_neg_mul_abs_int (div_pos one_pos (mul_pos two_pos
      (lt_of_lt_of_le ha hab)))).mul_left _).mul_left _
  · rintro n p ⟨⟨h1, h2⟩, h3, h4⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (intervalNeumannTerm_nonneg _ _ _ _)]
    exact intervalNeumannTerm_le ha h1 h2 h3 h4 n

/-- **Joint continuity of the kernel** on `[a, b] × K₀ × K₀`. -/
theorem continuousOn_neumannKernel {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ContinuousOn (fun p : ℝ × ℂ × ℂ => neumannKernel p.1 p.2.1 p.2.2)
      (Icc a b ×ˢ closedSquare 0 1 ×ˢ closedSquare 0 1) := by
  have h1 := continuousOn_intervalNeumannKernelReal_uncurry ha hab
  have hmap : ∀ (f g : ℂ → ℝ), Continuous f → Continuous g →
      (∀ z ∈ closedSquare (0 : ℂ) 1, f z ∈ Icc (0 : ℝ) 1) →
      (∀ z ∈ closedSquare (0 : ℂ) 1, g z ∈ Icc (-1 : ℝ) 2) →
      ContinuousOn (fun p : ℝ × ℂ × ℂ => intervalNeumannKernelReal p.1.toNNReal (f p.2.1)
        (g p.2.2)) (Icc a b ×ˢ closedSquare 0 1 ×ˢ closedSquare 0 1) := by
    intro f g hf hg hf1 hg1
    refine h1.comp (f := fun p : ℝ × ℂ × ℂ => (p.1.toNNReal, f p.2.1, g p.2.2))
      (Continuous.continuousOn ?_) fun p hp => ?_
    · exact (continuous_real_toNNReal.comp continuous_fst).prodMk
        ((hf.comp (continuous_fst.comp continuous_snd)).prodMk
          (hg.comp (continuous_snd.comp continuous_snd)))
    · obtain ⟨hp1, hp2, hp3⟩ := hp
      have hs0 : 0 < p.1 := ha.trans_le hp1.1
      refine ⟨⟨?_, ?_⟩, hf1 _ hp2, hg1 _ hp3⟩
      · show a ≤ ((p.1.toNNReal : ℝ≥0) : ℝ)
        rw [coe_toNNReal_of_pos hs0]; exact hp1.1
      · show ((p.1.toNNReal : ℝ≥0) : ℝ) ≤ b
        rw [coe_toNNReal_of_pos hs0]; exact hp1.2
  have hre := hmap Complex.re Complex.re Complex.continuous_re Complex.continuous_re
    (fun z hz => (re_im_mem_of_mem_closedSquare_zero_one hz).1)
    (fun z hz => ⟨by linarith [(re_im_mem_of_mem_closedSquare_zero_one hz).1.1],
      by linarith [(re_im_mem_of_mem_closedSquare_zero_one hz).1.2]⟩)
  have him := hmap Complex.im Complex.im Complex.continuous_im Complex.continuous_im
    (fun z hz => (re_im_mem_of_mem_closedSquare_zero_one hz).2)
    (fun z hz => ⟨by linarith [(re_im_mem_of_mem_closedSquare_zero_one hz).2.1],
      by linarith [(re_im_mem_of_mem_closedSquare_zero_one hz).2.2]⟩)
  refine (hre.mul him).congr fun p hp => ?_
  obtain ⟨hp1, hp2, hp3⟩ := hp
  exact neumannKernel_eq (ha.trans_le hp1.1) hp2 hp3

theorem continuousOn_neumannKernel_right {s : ℝ} (hs : 0 < s) {x : ℂ}
    (hx : x ∈ closedSquare 0 1) : ContinuousOn (neumannKernel s x) (closedSquare 0 1) :=
  (continuousOn_neumannKernel hs le_rfl).comp (f := fun y : ℂ => (s, x, y))
    (Continuous.continuousOn (by fun_prop)) fun y hy => ⟨⟨le_rfl, le_rfl⟩, hx, hy⟩

/-- `∫_{K₀} k_s(x, y) dy = 1`. -/
theorem setIntegral_neumannKernel_eq_one {s : ℝ} (hs : 0 < s) {x : ℂ}
    (hx : x ∈ closedSquare 0 1) : ∫ y in closedSquare 0 1, neumannKernel s x y = 1 := by
  have h := setLIntegral_squareNeumannKernel_eq_one x (Real.toNNReal_pos.2 hs).ne'
  have hfin : ∀ᵐ y ∂volume.restrict (closedSquare (0 : ℂ) 1),
      squareNeumannKernel s.toNNReal x y < ∞ :=
    (ae_restrict_iff' measurableSet_closedSquare_zero_one).2 (Eventually.of_forall fun y hy => by
      rw [← ofReal_neumannKernel hs hx hy]; exact ENNReal.ofReal_lt_top)
  have hm : AEMeasurable (fun y => squareNeumannKernel s.toNNReal x y)
      (volume.restrict (closedSquare (0 : ℂ) 1)) :=
    ((measurable_squareNeumannKernel s.toNNReal).comp (measurable_const.prodMk measurable_id)).aemeasurable
  unfold neumannKernel
  rw [integral_toReal hm hfin, h, ENNReal.toReal_one]

theorem integrableOn_neumannKernel {s : ℝ} (hs : 0 < s) {x : ℂ} (hx : x ∈ closedSquare 0 1) :
    IntegrableOn (neumannKernel s x) (closedSquare 0 1) := by
  obtain ⟨C, -, hC⟩ := exists_neumannKernel_le hs le_rfl
  exact integrableOn_closedSquare_of_abs_le (measurable_neumannKernel s x).aestronglyMeasurable
    fun z hz => by
      rw [abs_of_nonneg (neumannKernel_nonneg _ _ _)]; exact hC s ⟨le_rfl, le_rfl⟩ x hx z hz

/-! ### The Chapman–Kolmogorov identity -/

/-- **The Chapman–Kolmogorov identity** for the Neumann kernel of the square, at every pair of
points: `k_{s+t}(x, y) = ∫_{K₀} k_s(x, z) k_t(z, y) dz`. -/
theorem neumannKernel_add {s t : ℝ} (hs : 0 < s) (ht : 0 < t) {x y : ℂ}
    (hx : x ∈ closedSquare 0 1) (hy : y ∈ closedSquare 0 1) :
    neumannKernel (s + t) x y =
      ∫ z in closedSquare 0 1, neumannKernel s x z * neumannKernel t z y := by
  have hKm : MeasurableSet (closedSquare (0 : ℂ) 1) := measurableSet_closedSquare_zero_one
  obtain ⟨Cs, hCs0, hCs⟩ := exists_neumannKernel_le hs le_rfl
  obtain ⟨Ct, hCt0, hCt⟩ := exists_neumannKernel_le ht le_rfl
  have hFm : ∀ y, Measurable fun z => neumannKernel s x z * neumannKernel t z y := fun y =>
    (measurable_neumannKernel s x).mul (measurable_neumannKernel_left t y)
  have hFb : ∀ y ∈ closedSquare (0 : ℂ) 1, ∀ z ∈ closedSquare (0 : ℂ) 1, |neumannKernel s x z * neumannKernel t z y| ≤ Cs * Ct := by
    intro y hy z hz
    rw [abs_of_nonneg (mul_nonneg (neumannKernel_nonneg _ _ _) (neumannKernel_nonneg _ _ _))]
    exact mul_le_mul (hCs s ⟨le_rfl, le_rfl⟩ x hx z hz) (hCt t ⟨le_rfl, le_rfl⟩ z hz y hy)
      (neumannKernel_nonneg _ _ _) hCs0
  have hFi : ∀ y ∈ closedSquare (0 : ℂ) 1,
      IntegrableOn (fun z => neumannKernel s x z * neumannKernel t z y) (closedSquare 0 1) :=
    fun y hy => integrableOn_closedSquare_of_abs_le (hFm y).aestronglyMeasurable (hFb y hy)
  -- continuity of the right side in `y`
  have hgc : ContinuousOn (fun y => ∫ z in closedSquare 0 1,
      neumannKernel s x z * neumannKernel t z y) (closedSquare 0 1) := by
    refine continuousOn_of_dominated (bound := fun _ => Cs * Ct)
      (fun y _ => (hFm y).aestronglyMeasurable) (fun y hy => ?_) (integrable_const _) ?_
    · exact (ae_restrict_iff' hKm).2 (Eventually.of_forall fun z hz => by
        rw [Real.norm_eq_abs]; exact hFb y hy z hz)
    · refine (ae_restrict_iff' hKm).2 (Eventually.of_forall fun z hz => ?_)
      exact continuousOn_const.mul (continuousOn_neumannKernel_right ht hz)
  have hlc : ContinuousOn (neumannKernel (s + t) x) (closedSquare 0 1) :=
    continuousOn_neumannKernel_right (add_pos hs ht) hx
  have hg0 : ∀ y ∈ closedSquare (0 : ℂ) 1,
      0 ≤ ∫ z in closedSquare 0 1, neumannKernel s x z * neumannKernel t z y := fun y _ =>
    setIntegral_nonneg hKm fun z _ => mul_nonneg (neumannKernel_nonneg _ _ _)
      (neumannKernel_nonneg _ _ _)
  -- the identity integrated over measurable sets
  have hint : ∀ S : Set ℂ, MeasurableSet S →
      ∫⁻ y in S ∩ closedSquare 0 1, ENNReal.ofReal (neumannKernel (s + t) x y) =
        ∫⁻ y in S ∩ closedSquare 0 1, ENNReal.ofReal
          (∫ z in closedSquare 0 1, neumannKernel s x z * neumannKernel t z y) := by
    intro S hS
    set s' := s.toNNReal with hs'
    set t' := t.toNNReal with ht'
    have hs'0 : s' ≠ 0 := (Real.toNNReal_pos.2 hs).ne'
    have ht'0 : t' ≠ 0 := (Real.toNNReal_pos.2 ht).ne'
    have hst : (s + t).toNNReal = s' + t' := Real.toNNReal_add hs.le ht.le
    have hst0 : s' + t' ≠ 0 := by rw [← hst]; exact (Real.toNNReal_pos.2 (add_pos hs ht)).ne'
    have hΦ : Measurable (S.indicator (1 : ℂ → ℝ≥0∞)) := measurable_one.indicator hS
    have hind : ∀ (f : ℂ → ℝ≥0∞), ∫⁻ y in closedSquare 0 1, S.indicator 1 y * f y =
        ∫⁻ y in S ∩ closedSquare 0 1, f y := by
      intro f
      rw [← Measure.restrict_restrict hS, ← lintegral_indicator hS]
      refine lintegral_congr fun y => ?_
      by_cases hyS : y ∈ S <;> simp [hyS]
    -- the law at time `s + t`, computed directly and by the Markov property at time `s`
    have h1 := lintegral_reflected_eval_eq_neumannKernel hΦ x hst0
    have h2 := lintegral_shift_eq_neumannKernel (Ψ := fun b : ContinuousPath ℂ => S.indicator 1 (b t'))
      (hΦ.comp (continuous_eval_const t').measurable) x hs'0
    simp only [ContinuousPath.shift_apply] at h2
    rw [h1] at h2
    have h3 : ∀ z, ∫⁻ b, S.indicator 1 (b t') ∂reflectedPlanarBrownianMotion 0 1 z =
        ∫⁻ y in closedSquare 0 1, S.indicator 1 y * squareNeumannKernel t' z y := fun z =>
      lintegral_reflected_eval_eq_neumannKernel hΦ z ht'0
    simp only [h3] at h2
    -- Tonelli
    have hkm : ∀ r : ℝ≥0, Measurable fun p : ℂ × ℂ => squareNeumannKernel r p.1 p.2 :=
      measurable_squareNeumannKernel
    have h4 : ∫⁻ z in closedSquare 0 1, (∫⁻ y in closedSquare 0 1,
          S.indicator 1 y * squareNeumannKernel t' z y) * squareNeumannKernel s' x z =
        ∫⁻ y in closedSquare 0 1, S.indicator 1 y * ∫⁻ z in closedSquare 0 1,
          squareNeumannKernel s' x z * squareNeumannKernel t' z y := by
      have e1 : ∀ z, (∫⁻ y in closedSquare 0 1, S.indicator 1 y * squareNeumannKernel t' z y) *
          squareNeumannKernel s' x z = ∫⁻ y in closedSquare 0 1, S.indicator 1 y *
            squareNeumannKernel t' z y * squareNeumannKernel s' x z := fun z =>
        (lintegral_mul_const _ (hΦ.mul ((hkm t').comp (measurable_const.prodMk measurable_id)))).symm
      simp only [e1]
      rw [lintegral_lintegral_swap]
      · refine lintegral_congr fun y => ?_
        have hmz : Measurable fun z => squareNeumannKernel s' x z * squareNeumannKernel t' z y :=
          ((hkm s').comp (measurable_const.prodMk measurable_id)).mul
            ((hkm t').comp (measurable_id.prodMk measurable_const))
        rw [← lintegral_const_mul _ hmz]
        refine lintegral_congr fun z => ?_
        ring
      · exact (((hΦ.comp measurable_snd).mul (hkm t')).mul
          ((hkm s').comp (measurable_const.prodMk measurable_fst))).aemeasurable
    rw [h4, hind, hind] at h2
    -- back to the real kernels
    rw [← hst] at h2
    calc ∫⁻ y in S ∩ closedSquare 0 1, ENNReal.ofReal (neumannKernel (s + t) x y)
        = ∫⁻ y in S ∩ closedSquare 0 1, squareNeumannKernel (s + t).toNNReal x y := by
          refine setLIntegral_congr_fun (hS.inter hKm) fun y hy => ?_
          exact ofReal_neumannKernel (add_pos hs ht) hx hy.2
      _ = ∫⁻ y in S ∩ closedSquare 0 1, ∫⁻ z in closedSquare 0 1,
            squareNeumannKernel s' x z * squareNeumannKernel t' z y := h2
      _ = ∫⁻ y in S ∩ closedSquare 0 1, ENNReal.ofReal
            (∫ z in closedSquare 0 1, neumannKernel s x z * neumannKernel t z y) := by
          refine setLIntegral_congr_fun (hS.inter hKm) fun y hy => ?_
          rw [ofReal_integral_eq_lintegral_ofReal (hFi y hy.2)
            ((ae_restrict_iff' hKm).2 (Eventually.of_forall fun z _ =>
              mul_nonneg (neumannKernel_nonneg _ _ _) (neumannKernel_nonneg _ _ _)))]
          refine setLIntegral_congr_fun hKm fun z hz => ?_
          rw [ENNReal.ofReal_mul (neumannKernel_nonneg _ _ _), ofReal_neumannKernel hs hx hz,
            ofReal_neumannKernel ht hz hy.2]
  exact eqOn_of_forall_setLIntegral_eq hKm (ν := volume)
    (fun y hy r hr => volume_ball_inter_closedSquare_pos hy hr)
    (fun y _ => neumannKernel_nonneg _ _ _) hg0 hlc hgc hint hy

/-! ### Doeblin's bound and exponential mixing -/

/-- **A lower bound at time `1`**: `k_1 ≥ δ > 0` on `K₀ × K₀`. -/
theorem exists_le_neumannKernel_one : ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ closedSquare 0 1,
    ∀ y ∈ closedSquare 0 1, δ ≤ neumannKernel 1 x y := by
  have hc : 0 < (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2)) := by positivity
  have h1 : ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2)) ≤ intervalNeumannKernelReal 1 u v := by
    intro u hu v hv
    have hv' : v ∈ Icc (-1 : ℝ) 2 := ⟨by linarith [hv.1], by linarith [hv.2]⟩
    have hsum := summable_intervalNeumannTerm one_ne_zero hu hv'
    refine le_trans ?_ (hsum.le_tsum 0 fun j _ => intervalNeumannTerm_nonneg _ _ _ _)
    unfold intervalNeumannTerm
    simp only [Int.cast_zero, mul_zero, add_zero]
    refine le_trans ?_ (le_add_of_nonneg_right (gaussianPDFReal_nonneg _ _ _))
    rw [gaussianPDFReal_def]
    simp only [NNReal.coe_one, mul_one, sub_zero]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
    have : (v - u) ^ 2 ≤ 1 := by nlinarith [hu.1, hu.2, hv.1, hv.2]
    linarith
  refine ⟨((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2))) *
    ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2))), by positivity, fun x hx y hy => ?_⟩
  have hx' := re_im_mem_of_mem_closedSquare_zero_one hx
  have hy' := re_im_mem_of_mem_closedSquare_zero_one hy
  rw [neumannKernel_eq one_pos hx hy, Real.toNNReal_one]
  exact mul_le_mul (h1 _ hx'.1 _ hy'.1) (h1 _ hx'.2 _ hy'.2) hc.le
    (hc.le.trans (h1 _ hx'.1 _ hy'.1))

/-- **Doeblin's contraction.** If `a, a' ≥ 0` have the same integral `m > 0` and `h(z) - h(z') ≤ E`
for almost all `z, z'`, then `∫ a h - ∫ a' h ≤ m E`. -/
theorem integral_mul_sub_integral_mul_le {μ : Measure ℂ} [IsFiniteMeasure μ] {a a' h : ℂ → ℝ}
    (ha : Integrable a μ) (ha' : Integrable a' μ) (ha0 : 0 ≤ᵐ[μ] a) (ha'0 : 0 ≤ᵐ[μ] a')
    (hah : Integrable (fun z => a z * h z) μ) (ha'h : Integrable (fun z => a' z * h z) μ)
    (hm : ∫ z, a z ∂μ = ∫ z, a' z ∂μ) (hpos : 0 < ∫ z, a z ∂μ) {E : ℝ}
    (hE : ∀ᵐ z ∂μ, ∀ᵐ z' ∂μ, h z - h z' ≤ E) :
    ∫ z, a z * h z ∂μ - ∫ z, a' z * h z ∂μ ≤ (∫ z, a z ∂μ) * E := by
  set m := ∫ z, a z ∂μ with hm_def
  set c := ∫ z, a' z * h z ∂μ with hc_def
  have hinner : ∀ z, ∫ z', a' z' * (h z - h z') ∂μ = h z * m - c := by
    intro z
    have e : (fun z' => a' z' * (h z - h z')) = fun z' => a' z' * h z - a' z' * h z' := by
      funext z'; ring
    rw [e, integral_sub (ha'.mul_const _) ha'h, integral_mul_const, ← hm]
    ring
  have hle : ∀ᵐ z ∂μ, a z * (h z * m - c) ≤ a z * (m * E) := by
    filter_upwards [ha0, hE] with z hz0 hzE
    refine mul_le_mul_of_nonneg_left ?_ hz0
    rw [← hinner z]
    have hi1 : Integrable (fun z' => a' z' * (h z - h z')) μ :=
      ((ha'.mul_const (h z)).sub ha'h).congr (Eventually.of_forall fun z' => by
        simp only [Pi.sub_apply]; ring)
    calc ∫ z', a' z' * (h z - h z') ∂μ ≤ ∫ z', a' z' * E ∂μ := by
          refine integral_mono_ae hi1 (ha'.mul_const E) ?_
          filter_upwards [ha'0, hzE] with z' hz' hz'E
          exact mul_le_mul_of_nonneg_left hz'E hz'
      _ = m * E := by rw [integral_mul_const, ← hm]
  have hint1 : Integrable (fun z => a z * (h z * m - c)) μ := by
    refine ((hah.mul_const m).sub (ha.mul_const c)).congr (Eventually.of_forall fun z => ?_)
    simp only [Pi.sub_apply]; ring
  have hmono := integral_mono_ae hint1 (ha.mul_const _) hle
  have e1 : ∫ z, a z * (h z * m - c) ∂μ = (∫ z, a z * h z ∂μ) * m - m * c := by
    have e : (fun z => a z * (h z * m - c)) = fun z => a z * h z * m - a z * c := by
      funext z; ring
    rw [e, integral_sub (hah.mul_const _) (ha.mul_const _), integral_mul_const, integral_mul_const]
  rw [e1, integral_mul_const] at hmono
  have : m * (∫ z, a z * h z ∂μ - c) ≤ m * (m * E) := by nlinarith [hmono]
  exact le_of_mul_le_mul_left this hpos

/-- **Exponential mixing of the Neumann kernel**: `|k_s(x, y) - 1| ≤ C e^{-c s}` for `s ≥ 1` and
`x, y ∈ K₀` (Doeblin's argument from `k_1 ≥ δ`). -/
theorem exists_abs_neumannKernel_sub_one_le : ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧ ∀ s : ℝ, 1 ≤ s →
    ∀ x ∈ closedSquare 0 1, ∀ y ∈ closedSquare 0 1,
      |neumannKernel s x y - 1| ≤ C * Real.exp (-(c * s)) := by
  have hKm : MeasurableSet (closedSquare (0 : ℂ) 1) := measurableSet_closedSquare_zero_one
  obtain ⟨δ, hδ, hδle⟩ := exists_le_neumannKernel_one
  set δ' := min δ (1 / 2) with hδ'
  have hδ'0 : 0 < δ' := lt_min hδ (by norm_num)
  have hδ'1 : δ' ≤ 1 / 2 := min_le_right _ _
  have hδ'δ : δ' ≤ δ := min_le_left _ _
  set ρ := 1 - δ' with hρ
  have hρ0 : 1 / 2 ≤ ρ := by linarith
  have hρ1 : ρ < 1 := by linarith
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_neumannKernel_le one_pos one_le_two
  have hmass : ∀ x ∈ closedSquare (0 : ℂ) 1,
      ∫ z in closedSquare 0 1, (neumannKernel 1 x z - δ') = ρ := by
    intro x hx
    rw [integral_sub (integrableOn_neumannKernel one_pos hx) (integrable_const _),
      setIntegral_neumannKernel_eq_one one_pos hx, setIntegral_const_closedSquare]
  -- the oscillation bound on the windows `[n + 1, n + 2]`
  have hosc : ∀ n : ℕ, ∀ s ∈ Icc (1 : ℝ) 2, ∀ x ∈ closedSquare (0 : ℂ) 1,
      ∀ x' ∈ closedSquare (0 : ℂ) 1, ∀ y ∈ closedSquare (0 : ℂ) 1,
      neumannKernel (s + n) x y - neumannKernel (s + n) x' y ≤ 2 * C₁ * ρ ^ n := by
    intro n
    induction n with
    | zero =>
      intro s hs x hx x' hx' y hy
      simp only [Nat.cast_zero, add_zero, pow_zero, mul_one]
      have h1 := hC₁ s hs x hx y hy
      have h2 := neumannKernel_nonneg s x' y
      linarith
    | succ n ih =>
      intro s hs x hx x' hx' y hy
      have hsn : 0 < s + n := by linarith [hs.1, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      have e : s + ((n + 1 : ℕ) : ℝ) = 1 + (s + n) := by push_cast; ring
      rw [e, neumannKernel_add one_pos hsn hx hy, neumannKernel_add one_pos hsn hx' hy]
      obtain ⟨Ch, -, hCh⟩ := exists_neumannKernel_le hsn le_rfl
      obtain ⟨Cw, -, hCw⟩ := exists_neumannKernel_le one_pos le_rfl
      have hhm : Measurable fun z => neumannKernel (s + n) z y := measurable_neumannKernel_left _ y
      have hhb : ∀ z ∈ closedSquare (0 : ℂ) 1, |neumannKernel (s + n) z y| ≤ Ch := fun z hz => by
        rw [abs_of_nonneg (neumannKernel_nonneg _ _ _)]; exact hCh _ ⟨le_rfl, le_rfl⟩ z hz y hy
      have hhi : IntegrableOn (fun z => neumannKernel (s + n) z y) (closedSquare 0 1) :=
        integrableOn_closedSquare_of_abs_le hhm.aestronglyMeasurable hhb
      have hai : ∀ w ∈ closedSquare (0 : ℂ) 1,
          IntegrableOn (fun z => neumannKernel 1 w z - δ') (closedSquare 0 1) := fun w hw =>
        (integrableOn_neumannKernel one_pos hw).sub (integrable_const _)
      have hahi : ∀ w ∈ closedSquare (0 : ℂ) 1, IntegrableOn
          (fun z => (neumannKernel 1 w z - δ') * neumannKernel (s + n) z y) (closedSquare 0 1) := by
        intro w hw
        refine integrableOn_closedSquare_of_abs_le
          (((measurable_neumannKernel 1 w).sub measurable_const).mul hhm).aestronglyMeasurable
          (C := (Cw + δ') * Ch) fun z hz => ?_
        have hw0 := neumannKernel_nonneg 1 w z
        have hw1 := hCw 1 ⟨le_rfl, le_rfl⟩ w hw z hz
        have hb0 : 0 ≤ Cw + δ' := by linarith
        rw [abs_mul]
        refine mul_le_mul ?_ (hhb z hz) (abs_nonneg _) hb0
        rw [abs_le]
        constructor <;> linarith
      have hsplit : ∀ w ∈ closedSquare (0 : ℂ) 1,
          ∫ z in closedSquare 0 1, neumannKernel 1 w z * neumannKernel (s + n) z y =
            (∫ z in closedSquare 0 1, (neumannKernel 1 w z - δ') * neumannKernel (s + n) z y) +
              δ' * ∫ z in closedSquare 0 1, neumannKernel (s + n) z y := by
        intro w hw
        rw [← integral_const_mul, ← integral_add (hahi w hw) (hhi.const_mul _)]
        refine integral_congr_ae (Eventually.of_forall fun z => ?_)
        ring
      rw [hsplit x hx, hsplit x' hx']
      have hdoe := integral_mul_sub_integral_mul_le (μ := volume.restrict (closedSquare 0 1))
        (h := fun z => neumannKernel (s + n) z y) (hai x hx) (hai x' hx')
        ((ae_restrict_iff' hKm).2 (Eventually.of_forall fun z hz => by
          simp only [Pi.zero_apply]; linarith [hδle x hx z hz, hδ'δ]))
        ((ae_restrict_iff' hKm).2 (Eventually.of_forall fun z hz => by
          simp only [Pi.zero_apply]; linarith [hδle x' hx' z hz, hδ'δ]))
        (hahi x hx) (hahi x' hx') (by rw [hmass x hx, hmass x' hx'])
        (by rw [hmass x hx]; linarith)
        (E := 2 * C₁ * ρ ^ n)
        ((ae_restrict_iff' hKm).2 (Eventually.of_forall fun z hz =>
          (ae_restrict_iff' hKm).2 (Eventually.of_forall fun z' hz' => ih s hs z hz z' hz' y hy)))
      rw [hmass x hx] at hdoe
      have : ρ * (2 * C₁ * ρ ^ n) = 2 * C₁ * ρ ^ (n + 1) := by ring
      linarith
  -- from the oscillation to the distance to `1`
  have hdist : ∀ n : ℕ, ∀ s ∈ Icc (1 : ℝ) 2, ∀ x ∈ closedSquare (0 : ℂ) 1,
      ∀ y ∈ closedSquare (0 : ℂ) 1, |neumannKernel (s + n) x y - 1| ≤ 2 * C₁ * ρ ^ n := by
    intro n s hs x hx y hy
    have hsn : 0 < s + n := by linarith [hs.1, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hone : ∫ x' in closedSquare 0 1, neumannKernel (s + n) x' y = 1 := by
      simp_rw [neumannKernel_comm (s + n) _ y]
      exact setIntegral_neumannKernel_eq_one hsn hy
    have hint : IntegrableOn (fun x' => neumannKernel (s + n) x' y) (closedSquare 0 1) := by
      simp_rw [neumannKernel_comm (s + n) _ y]
      exact integrableOn_neumannKernel hsn hy
    have e : neumannKernel (s + n) x y - 1 =
        ∫ x' in closedSquare 0 1, (neumannKernel (s + n) x y - neumannKernel (s + n) x' y) := by
      rw [integral_sub (integrable_const _) hint, hone, setIntegral_const_closedSquare]
    rw [e, abs_le]
    constructor
    · have hle : ∫ x' in closedSquare 0 1, (neumannKernel (s + n) x' y -
            neumannKernel (s + n) x y) ≤ ∫ _ in closedSquare (0 : ℂ) 1, 2 * C₁ * ρ ^ n :=
        setIntegral_mono_on (hint.sub (integrable_const _)) (integrable_const _) hKm
          fun x' hx' => hosc n s hs x' hx' x hx y hy
      rw [setIntegral_const_closedSquare] at hle
      have hneg : ∫ x' in closedSquare 0 1, (neumannKernel (s + n) x y -
            neumannKernel (s + n) x' y) =
          -∫ x' in closedSquare 0 1, (neumannKernel (s + n) x' y - neumannKernel (s + n) x y) := by
        rw [← integral_neg]
        refine integral_congr_ae (Eventually.of_forall fun x' => ?_)
        ring
      rw [hneg]
      linarith
    · have hle : ∫ x' in closedSquare 0 1, (neumannKernel (s + n) x y -
            neumannKernel (s + n) x' y) ≤ ∫ _ in closedSquare (0 : ℂ) 1, 2 * C₁ * ρ ^ n :=
        setIntegral_mono_on ((integrable_const _).sub hint) (integrable_const _) hKm
          fun x' hx' => hosc n s hs x hx x' hx' y hy
      rw [setIntegral_const_closedSquare] at hle
      exact hle
  -- the exponential bound
  have hlogρ : Real.log ρ < 0 := Real.log_neg (by linarith) hρ1
  refine ⟨2 * C₁ * Real.exp (-(2 * Real.log ρ)), -Real.log ρ, by positivity, by linarith,
    fun s hs x hx y hy => ?_⟩
  set n : ℕ := ⌊s⌋₊ - 1 with hn
  have hfl : (⌊s⌋₊ : ℝ) ≤ s := Nat.floor_le (by linarith)
  have hfl1 : s < ⌊s⌋₊ + 1 := Nat.lt_floor_add_one s
  have hfl0 : 1 ≤ ⌊s⌋₊ := (Nat.one_le_floor_iff s).2 hs
  have hn' : (n : ℝ) = ⌊s⌋₊ - 1 := by rw [hn, Nat.cast_sub hfl0, Nat.cast_one]
  have hsn : s - n ∈ Icc (1 : ℝ) 2 := ⟨by rw [hn']; linarith, by rw [hn']; linarith⟩
  have h := hdist n (s - n) hsn x hx y hy
  rw [sub_add_cancel] at h
  refine h.trans ?_
  have hρpos : 0 < ρ := by linarith
  have hpow : ρ ^ n = Real.exp (n * Real.log ρ) := by
    rw [← Real.exp_log (pow_pos hρpos n), Real.log_pow]
  have hexp : Real.exp (n * Real.log ρ) ≤ Real.exp (-(2 * Real.log ρ)) *
      Real.exp (-(-Real.log ρ * s)) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have : s - 2 ≤ (n : ℝ) := by rw [hn']; linarith
    nlinarith
  rw [hpow]
  have hC : 0 ≤ 2 * C₁ := by positivity
  calc 2 * C₁ * Real.exp (n * Real.log ρ) ≤ 2 * C₁ * (Real.exp (-(2 * Real.log ρ)) *
        Real.exp (-(-Real.log ρ * s))) := mul_le_mul_of_nonneg_left hexp hC
    _ = 2 * C₁ * Real.exp (-(2 * Real.log ρ)) * Real.exp (-(-Real.log ρ * s)) := by ring

end HarmonicBalls

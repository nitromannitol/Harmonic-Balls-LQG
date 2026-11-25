import HarmonicBalls.Proofs.Potential.ReflectedClockIdentification

/-!
# Lebesgue measure on the unit square is invariant for reflected Brownian motion

For the triangle wave `u = unitIntervalFold` (2-periodic, even, the identity on `[0, 1]`) and a
bounded measurable `ψ`, `∫₀¹ ψ(u(x + w)) dx + ∫₀¹ ψ(u(x - w)) dx = 2 ∫₀¹ ψ`
(`intervalIntegral_unitIntervalFold_add_add_sub`): the two integrals are the integrals of
`ψ ∘ u` over `[w - 1, w]` and `[w, w + 1]`, which together cover one period.

In two dimensions the fold `squareFold 0 1` acts coordinatewise, so for a bounded measurable `Φ`
the four integrals over `K₀ = [0, 1]²` of `Φ(fold(x + σ v))`, `σ` a coordinate sign change, add up
to `4 ∫_{K₀} Φ` (`setIntegral_closedSquare_squareFold_add_coordSign`, the one-dimensional identity
in each coordinate). Averaging over a centred planar Gaussian `v`, whose law is invariant under the
sign changes, gives `∫_{K₀} E[Φ(fold(x + √s N))] dx = ∫_{K₀} Φ`
(`setIntegral_integral_planarGaussian_squareFold`). Since the marginal of reflected Brownian motion
at time `s` is the folded Gaussian law (`reflectedPlanarBrownianMotion_zero_one_map_eval`), Lebesgue
measure on `K₀` is invariant: `∫_{K₀} Q_x(b_s ∈ S) dx = |S ∩ K₀|`
(`lintegral_reflectedPlanarBrownianMotion_eval_mem`) and `∫_{K₀} E_x[ψ(b_s)] dx = ∫_{K₀} ψ` for
measurable `ψ ≥ 0` (`lintegral_lintegral_reflectedPlanarBrownianMotion_eval`).
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Set Filter Topology MarkovProcess
open scoped ENNReal NNReal

theorem unitIntervalFold_add_two (z : ℝ) : unitIntervalFold (z + 2) = unitIntervalFold z := by
  have h := unitIntervalFold_sign_mul_sub (Or.inl rfl) (-1) z
  rw [one_mul] at h
  convert h using 2
  push_cast
  ring

theorem unitIntervalFold_neg (z : ℝ) : unitIntervalFold (-z) = unitIntervalFold z := by
  have h := unitIntervalFold_sign_mul_sub (Or.inr rfl) 0 z
  convert h using 2
  push_cast
  ring

theorem unitIntervalFold_of_mem_Icc {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) : unitIntervalFold z = z := by
  unfold unitIntervalFold
  rw [Real.arccos_cos (by nlinarith [Real.pi_pos, hz.1]) (by nlinarith [Real.pi_pos, hz.2])]
  field_simp

theorem unitIntervalFold_of_mem_Icc_one_two {z : ℝ} (hz : z ∈ Icc (1 : ℝ) 2) :
    unitIntervalFold z = 2 - z := by
  have h1 : unitIntervalFold z = unitIntervalFold (z - 2) := by
    rw [← unitIntervalFold_add_two (z - 2), sub_add_cancel]
  rw [h1, ← unitIntervalFold_neg, neg_sub]
  exact unitIntervalFold_of_mem_Icc ⟨by linarith [hz.2], by linarith [hz.1]⟩

/-- **The one-dimensional identity behind the invariance of Lebesgue measure**:
`∫₀¹ ψ(u(x + w)) dx + ∫₀¹ ψ(u(x - w)) dx = 2 ∫₀¹ ψ` for the triangle wave `u` and a bounded
measurable `ψ`. -/
theorem intervalIntegral_unitIntervalFold_add_add_sub {ψ : ℝ → ℝ} (hψ : Measurable ψ) {C : ℝ}
    (hC : ∀ y, |ψ y| ≤ C) (w : ℝ) :
    (∫ x in (0 : ℝ)..1, ψ (unitIntervalFold (x + w))) +
        ∫ x in (0 : ℝ)..1, ψ (unitIntervalFold (x - w)) = 2 * ∫ x in (0 : ℝ)..1, ψ x := by
  set φ : ℝ → ℝ := fun z => ψ (unitIntervalFold z) with hφ
  have hφm : Measurable φ := hψ.comp continuous_unitIntervalFold.measurable
  have hint : ∀ a b : ℝ, IntervalIntegrable φ volume a b := fun a b =>
    (intervalIntegrable_const (c := C)).mono_fun hφm.aestronglyMeasurable
      (Eventually.of_forall fun z => by
        simp only [Real.norm_eq_abs]
        exact (hC _).trans (le_abs_self C))
  have hper : Function.Periodic φ 2 := fun z => by simp only [hφ, unitIntervalFold_add_two]
  have heven : ∀ z, φ (-z) = φ z := fun z => by simp only [hφ, unitIntervalFold_neg]
  have h1 : (∫ x in (0 : ℝ)..1, φ (x + w)) = ∫ x in w..(w + 1), φ x := by
    rw [intervalIntegral.integral_comp_add_right, zero_add, add_comm]
  have h2 : (∫ x in (0 : ℝ)..1, φ (x - w)) = ∫ x in (w - 1)..w, φ x := by
    rw [intervalIntegral.integral_comp_sub_right]
    have h : (∫ x in (0 - w)..(1 - w), φ x) = ∫ x in (0 - w)..(1 - w), φ (-x) :=
      intervalIntegral.integral_congr fun x _ => (heven x).symm
    rw [h, intervalIntegral.integral_comp_neg, neg_sub, neg_sub, sub_zero]
  have h3 : (∫ x in (0 : ℝ)..2, φ x) = 2 * ∫ x in (0 : ℝ)..1, ψ x := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hint 0 1) (hint 1 2)]
    have ha : (∫ x in (0 : ℝ)..1, φ x) = ∫ x in (0 : ℝ)..1, ψ x := by
      refine intervalIntegral.integral_congr fun x hx => ?_
      rw [uIcc_of_le zero_le_one] at hx
      simp only [hφ, unitIntervalFold_of_mem_Icc hx]
    have hb : (∫ x in (1 : ℝ)..2, φ x) = ∫ x in (0 : ℝ)..1, ψ x := by
      have : (∫ x in (1 : ℝ)..2, φ x) = ∫ x in (1 : ℝ)..2, ψ (2 - x) := by
        refine intervalIntegral.integral_congr fun x hx => ?_
        rw [uIcc_of_le one_le_two] at hx
        simp only [hφ, unitIntervalFold_of_mem_Icc_one_two hx]
      rw [this, intervalIntegral.integral_comp_sub_left]
      norm_num
    rw [ha, hb]
    ring
  simp only [hφ] at h1 h2 h3
  rw [h1, h2, add_comm, intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _)]
  have h4 := hper.intervalIntegral_add_eq (w - 1) 0
  rw [show w - 1 + 2 = w + 1 by ring, zero_add] at h4
  simp only [hφ] at h4
  rw [h4, h3]

/-- **Invariance in one dimension**: for a bounded measurable `ψ` and every variance `s`,
`∫₀¹ E[ψ(u(x + √s N))] dx = ∫₀¹ ψ`. -/
theorem intervalIntegral_integral_gaussianReal_unitIntervalFold {ψ : ℝ → ℝ} (hψ : Measurable ψ)
    {C : ℝ} (hC : ∀ y, |ψ y| ≤ C) (s : ℝ≥0) :
    ∫ x in (0 : ℝ)..1, ∫ w, ψ (unitIntervalFold w) ∂(gaussianReal x s) =
      ∫ x in (0 : ℝ)..1, ψ x := by
  set N := gaussianReal 0 s with hN
  have hφm : Measurable fun w => ψ (unitIntervalFold w) :=
    hψ.comp continuous_unitIntervalFold.measurable
  have htr : ∀ x : ℝ, ∫ w, ψ (unitIntervalFold w) ∂(gaussianReal x s) =
      ∫ z, ψ (unitIntervalFold (x + z)) ∂N := by
    intro x
    have h : gaussianReal x s = N.map (· + x) := by rw [hN, gaussianReal_map_add_const, zero_add]
    rw [h, integral_map (measurable_add_const x).aemeasurable hφm.aestronglyMeasurable]
    simp only [add_comm]
  simp_rw [htr]
  rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one]
  have hfm : Measurable (Function.uncurry fun (x : ℝ) (z : ℝ) => ψ (unitIntervalFold (x + z))) :=
    hφm.comp measurable_add
  have hint : Integrable (Function.uncurry fun (x : ℝ) (z : ℝ) => ψ (unitIntervalFold (x + z)))
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod N) :=
    Integrable.of_bound hfm.aestronglyMeasurable C (Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs]
      exact hC _)
  rw [integral_integral_swap hint]
  set G : ℝ → ℝ := fun z => ∫ x in Ioc (0 : ℝ) 1, ψ (unitIntervalFold (x + z)) with hG
  have hGint : Integrable G N := hint.integral_prod_right
  have hNneg : N.map (fun x => -x) = N := by rw [hN, gaussianReal_map_neg, neg_zero]
  have hGneg : Integrable (fun z => G (-z)) N := by
    have h := hGint
    rw [← hNneg] at h
    exact (integrable_map_measure h.aestronglyMeasurable measurable_neg.aemeasurable).1 h
  have hsym : ∫ z, G z ∂N = ∫ z, G (-z) ∂N := by
    conv_lhs => rw [← hNneg]
    rw [integral_map measurable_neg.aemeasurable (by rw [hNneg]; exact hGint.aestronglyMeasurable)]
  have hpair : ∀ z, G z + G (-z) = 2 * ∫ x in Ioc (0 : ℝ) 1, ψ x := by
    intro z
    have h := intervalIntegral_unitIntervalFold_add_add_sub hψ hC z
    simp only [intervalIntegral.integral_of_le zero_le_one] at h ⊢
    exact h
  have h2 : 2 * ∫ z, G z ∂N = 2 * ∫ x in Ioc (0 : ℝ) 1, ψ x := by
    rw [two_mul]
    nth_rewrite 2 [hsym]
    rw [← integral_add hGint hGneg]
    simp_rw [hpair]
    rw [integral_const, probReal_univ, one_smul]
  linarith

/-! ### Two dimensions -/

theorem intervalIntegrable_of_abs_le {g : ℝ → ℝ} (hg : Measurable g) {C : ℝ} (hC : ∀ x, |g x| ≤ C)
    (a b : ℝ) : IntervalIntegrable g volume a b :=
  (intervalIntegrable_const (c := C)).mono_fun hg.aestronglyMeasurable
    (Eventually.of_forall fun z => by
      simp only [Real.norm_eq_abs]
      exact (hC _).trans (le_abs_self C))

theorem measurable_intervalIntegral_param {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g))
    (a b : ℝ) : Measurable fun r => ∫ t in a..b, g r t := by
  simp only [intervalIntegral]
  exact ((hg.stronglyMeasurable.integral_prod_right (ν := volume.restrict (Ioc a b))).measurable).sub
    ((hg.stronglyMeasurable.integral_prod_right (ν := volume.restrict (Ioc b a))).measurable)

theorem abs_intervalIntegral_zero_one_le {g : ℝ → ℝ} {C : ℝ} (hC : ∀ x, |g x| ≤ C) :
    |∫ t in (0 : ℝ)..1, g t| ≤ C := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1) (f := g) (C := C)
    (fun x _ => by rw [Real.norm_eq_abs]; exact hC x)
  rw [Real.norm_eq_abs] at h
  simpa using h

theorem measurable_complex_mk : Measurable fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ) :=
  Complex.measurableEquivRealProd.symm.measurable

/-- An integral over the unit square as an iterated interval integral. -/
theorem setIntegral_closedSquare_zero_one_eq {f : ℂ → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ z, |f z| ≤ C) :
    ∫ x in closedSquare 0 1, f x = ∫ x₁ in (0 : ℝ)..1, ∫ x₂ in (0 : ℝ)..1, f ⟨x₁, x₂⟩ := by
  have hpre : Complex.measurableEquivRealProd ⁻¹' (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) =
      closedSquare 0 1 := by
    ext z
    simp only [closedSquare, Complex.mem_reProdIm, Complex.measurableEquivRealProd, mem_preimage,
      mem_prod, Complex.zero_re, Complex.zero_im, zero_add]
    rfl
  have h1 := Complex.volume_preserving_equiv_real_prod.setIntegral_preimage_emb
    Complex.measurableEquivRealProd.measurableEmbedding (fun p : ℝ × ℝ => f ⟨p.1, p.2⟩)
    (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
  rw [hpre] at h1
  have hfm : Measurable fun p : ℝ × ℝ => f ⟨p.1, p.2⟩ := hf.comp measurable_complex_mk
  have hint : Integrable (fun p : ℝ × ℝ => f ⟨p.1, p.2⟩)
      ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict (Icc (0 : ℝ) 1))) :=
    Integrable.of_bound hfm.aestronglyMeasurable C (Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs]; exact hC _)
  calc ∫ x in closedSquare 0 1, f x
      = ∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, f ⟨p.1, p.2⟩ := h1
    _ = ∫ x₁ in Icc (0 : ℝ) 1, ∫ x₂ in Icc (0 : ℝ) 1, f ⟨x₁, x₂⟩ := by
      rw [Measure.volume_eq_prod, ← Measure.prod_restrict, integral_prod _ hint]
    _ = ∫ x₁ in (0 : ℝ)..1, ∫ x₂ in (0 : ℝ)..1, f ⟨x₁, x₂⟩ := by
      simp only [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]

theorem measurable_complex_mk_comp {α : Type*} [MeasurableSpace α] {f g : α → ℝ}
    (hf : Measurable f) (hg : Measurable g) : Measurable fun a => (⟨f a, g a⟩ : ℂ) :=
  measurable_complex_mk.comp (hf.prodMk hg)

theorem measurable_complex_mk_left (c : ℝ) : Measurable fun y : ℝ => (⟨c, y⟩ : ℂ) :=
  measurable_complex_mk_comp measurable_const measurable_id

/-- An integral over the unit square of a function of the folded translate `x + w` as an iterated
interval integral. -/
theorem setIntegral_closedSquare_squareFold_add {Φ : ℂ → ℝ} (hΦ : Measurable Φ) {C : ℝ}
    (hC : ∀ z, |Φ z| ≤ C) (w₁ w₂ : ℝ) :
    ∫ x in closedSquare 0 1, Φ (squareFold 0 1 (x + ⟨w₁, w₂⟩)) =
      ∫ x₁ in (0 : ℝ)..1, ∫ x₂ in (0 : ℝ)..1,
        Φ ⟨unitIntervalFold (x₁ + w₁), unitIntervalFold (x₂ + w₂)⟩ := by
  have hm : Measurable fun x : ℂ => Φ (squareFold 0 1 (x + ⟨w₁, w₂⟩)) :=
    hΦ.comp ((continuous_squareFold 0 1).measurable.comp (measurable_add_const _))
  rw [setIntegral_closedSquare_zero_one_eq hm (fun z => hC _)]
  simp only [squareFold_zero_one_apply, Complex.add_re, Complex.add_im]

/-- The two reflections in the second coordinate: for a bounded measurable `Φ` and reals `w₁, w₂`,
the iterated integrals of `Φ(u(x₁ + w₁) + i u(x₂ ± w₂))` add up to twice the iterated integral of
`Φ(u(x₁ + w₁) + i x₂)`. -/
theorem intervalIntegral_unitIntervalFold_snd_add_add_neg {Φ : ℂ → ℝ} (hΦ : Measurable Φ) {C : ℝ}
    (hC : ∀ z, |Φ z| ≤ C) (w₁ w₂ : ℝ) :
    (∫ x₁ in (0 : ℝ)..1, ∫ x₂ in (0 : ℝ)..1,
        Φ ⟨unitIntervalFold (x₁ + w₁), unitIntervalFold (x₂ + w₂)⟩) +
      (∫ x₁ in (0 : ℝ)..1, ∫ x₂ in (0 : ℝ)..1,
        Φ ⟨unitIntervalFold (x₁ + w₁), unitIntervalFold (x₂ + -w₂)⟩) =
      2 * ∫ x₁ in (0 : ℝ)..1, ∫ x₂ in (0 : ℝ)..1, Φ ⟨unitIntervalFold (x₁ + w₁), x₂⟩ := by
  have hu := continuous_unitIntervalFold.measurable
  have hint : ∀ w : ℝ, IntervalIntegrable (fun x₁ => ∫ x₂ in (0 : ℝ)..1,
      Φ ⟨unitIntervalFold (x₁ + w₁), unitIntervalFold (x₂ + w)⟩) volume 0 1 := by
    intro w
    refine intervalIntegrable_of_abs_le (measurable_intervalIntegral_param
      (g := fun x₁ x₂ => Φ ⟨unitIntervalFold (x₁ + w₁), unitIntervalFold (x₂ + w)⟩)
      (hΦ.comp (measurable_complex_mk_comp (hu.comp (measurable_fst.add_const w₁))
        (hu.comp (measurable_snd.add_const w)))) 0 1) (C := C) (fun x₁ => ?_) 0 1
    exact abs_intervalIntegral_zero_one_le fun _ => hC _
  rw [← intervalIntegral.integral_add (hint w₂) (hint (-w₂)),
    ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun x₁ _ => ?_
  have h := intervalIntegral_unitIntervalFold_add_add_sub (ψ := fun y => Φ ⟨unitIntervalFold (x₁ + w₁), y⟩)
    (hΦ.comp (measurable_complex_mk_left (unitIntervalFold (x₁ + w₁)))) (fun _ => hC _) w₂
  simp only [sub_eq_add_neg] at h
  exact h

/-- **Invariance of Lebesgue measure on the unit square under the folded translations, averaged over
the coordinate sign changes**: for a bounded measurable `Φ` and every `v`, the four integrals over
the unit square of `Φ(fold(x + σ v))`, `σ` a coordinate sign change, add up to four times the
integral of `Φ`. -/
theorem setIntegral_closedSquare_squareFold_add_coordSign {Φ : ℂ → ℝ} (hΦ : Measurable Φ) {C : ℝ}
    (hC : ∀ z, |Φ z| ≤ C) (v : ℂ) :
    (∫ x in closedSquare 0 1, Φ (squareFold 0 1 (x + coordSign 1 1 v))) +
        (∫ x in closedSquare 0 1, Φ (squareFold 0 1 (x + coordSign 1 (-1) v))) +
        (∫ x in closedSquare 0 1, Φ (squareFold 0 1 (x + coordSign (-1) 1 v))) +
        (∫ x in closedSquare 0 1, Φ (squareFold 0 1 (x + coordSign (-1) (-1) v))) =
      4 * ∫ x in closedSquare 0 1, Φ x := by
  have e1 : coordSign 1 1 v = ⟨v.re, v.im⟩ := by apply Complex.ext <;> simp [coordSign]
  have e2 : coordSign 1 (-1) v = ⟨v.re, -v.im⟩ := by apply Complex.ext <;> simp [coordSign]
  have e3 : coordSign (-1) 1 v = ⟨-v.re, v.im⟩ := by apply Complex.ext <;> simp [coordSign]
  have e4 : coordSign (-1) (-1) v = ⟨-v.re, -v.im⟩ := by apply Complex.ext <;> simp [coordSign]
  rw [e1, e2, e3, e4, setIntegral_closedSquare_squareFold_add hΦ hC,
    setIntegral_closedSquare_squareFold_add hΦ hC, setIntegral_closedSquare_squareFold_add hΦ hC,
    setIntegral_closedSquare_squareFold_add hΦ hC, setIntegral_closedSquare_zero_one_eq hΦ hC]
  have h1 := intervalIntegral_unitIntervalFold_snd_add_add_neg hΦ hC v.re v.im
  have h2 := intervalIntegral_unitIntervalFold_snd_add_add_neg hΦ hC (-v.re) v.im
  have hrowm : Measurable fun c : ℝ => ∫ x₂ in (0 : ℝ)..1, Φ ⟨c, x₂⟩ :=
    measurable_intervalIntegral_param (g := fun c x₂ => Φ ⟨c, x₂⟩)
      (hΦ.comp measurable_complex_mk) 0 1
  have h3 := intervalIntegral_unitIntervalFold_add_add_sub hrowm
    (fun c => abs_intervalIntegral_zero_one_le (g := fun x₂ => Φ ⟨c, x₂⟩) fun _ => hC _) v.re
  simp only [sub_eq_add_neg] at h3
  linarith

theorem coordSign_ofReal_mul (σ₁ σ₂ r : ℝ) (w : ℂ) :
    coordSign σ₁ σ₂ ((r : ℂ) * w) = (r : ℂ) * coordSign σ₁ σ₂ w := by
  apply Complex.ext <;> simp [coordSign] <;> ring

/-- Centred planar Gaussian laws are invariant under coordinate sign changes. -/
theorem planarGaussian_zero_map_coordSign {σ₁ σ₂ : ℝ} (h₁ : σ₁ = 1 ∨ σ₁ = -1)
    (h₂ : σ₂ = 1 ∨ σ₂ = -1) (t : ℝ≥0) :
    (planarGaussian 0 t).map (coordSign σ₁ σ₂) = planarGaussian 0 t := by
  rw [planarGaussian_map_coordSign h₁ h₂]
  congr 1
  apply Complex.ext <;> simp [coordSign]

/-- **Invariance of Lebesgue measure on the unit square for the folded Gaussian laws**: for a
bounded measurable `Φ` and every variance `s`, `∫_{K₀} E[Φ(fold(x + √s N))] dx = ∫_{K₀} Φ`. -/
theorem setIntegral_integral_planarGaussian_squareFold {Φ : ℂ → ℝ} (hΦ : Measurable Φ) {C : ℝ}
    (hC : ∀ z, |Φ z| ≤ C) (s : ℝ≥0) :
    ∫ x in closedSquare 0 1, ∫ w, Φ (squareFold 0 1 w) ∂(planarGaussian x s) =
      ∫ x in closedSquare 0 1, Φ x := by
  have hfold : Measurable (squareFold 0 1) := (continuous_squareFold 0 1).measurable
  have hφm : Measurable fun w => Φ (squareFold 0 1 w) := hΦ.comp hfold
  have htr : ∀ x : ℂ, ∫ w, Φ (squareFold 0 1 w) ∂(planarGaussian x s) =
      ∫ w, Φ (squareFold 0 1 (x + (Real.sqrt s : ℂ) * w)) ∂(planarGaussian 0 1) := by
    intro x
    rw [planarGaussian_eq_map_add_sqrt_mul x s, integral_map
      (show AEMeasurable (fun w : ℂ => x + (Real.sqrt s : ℂ) * w) (planarGaussian 0 1) by fun_prop)
      hφm.aestronglyMeasurable]
  simp_rw [htr]
  have : IsFiniteMeasure ((volume : Measure ℂ).restrict (closedSquare 0 1)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact (isCompact_closedSquare 0 1).measure_lt_top⟩
  have hFm : Measurable (Function.uncurry fun (x : ℂ) (w : ℂ) =>
      Φ (squareFold 0 1 (x + (Real.sqrt s : ℂ) * w))) :=
    hφm.comp (by fun_prop : Measurable fun p : ℂ × ℂ => p.1 + (Real.sqrt s : ℂ) * p.2)
  have hint : Integrable (Function.uncurry fun (x : ℂ) (w : ℂ) =>
      Φ (squareFold 0 1 (x + (Real.sqrt s : ℂ) * w)))
      (((volume : Measure ℂ).restrict (closedSquare 0 1)).prod (planarGaussian 0 1)) :=
    Integrable.of_bound hFm.aestronglyMeasurable C (Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs]
      exact hC _)
  rw [integral_integral_swap hint]
  set G : ℂ → ℝ := fun w => ∫ x in closedSquare 0 1,
    Φ (squareFold 0 1 (x + (Real.sqrt s : ℂ) * w)) with hG
  have hGint : Integrable G (planarGaussian 0 1) := hint.integral_prod_right
  have hinv : ∀ {σ₁ σ₂ : ℝ}, (σ₁ = 1 ∨ σ₁ = -1) → (σ₂ = 1 ∨ σ₂ = -1) →
      Integrable (fun w => G (coordSign σ₁ σ₂ w)) (planarGaussian 0 1) ∧
        ∫ w, G (coordSign σ₁ σ₂ w) ∂(planarGaussian 0 1) = ∫ w, G w ∂(planarGaussian 0 1) := by
    intro σ₁ σ₂ h₁ h₂
    have hmap := planarGaussian_zero_map_coordSign h₁ h₂ 1
    have hcs := (continuous_coordSign σ₁ σ₂).measurable.aemeasurable (μ := planarGaussian 0 1)
    have hG' : Integrable G ((planarGaussian 0 1).map (coordSign σ₁ σ₂)) := by
      rw [hmap]
      exact hGint
    refine ⟨(integrable_map_measure hG'.aestronglyMeasurable hcs).1 hG', ?_⟩
    conv_rhs => rw [← hmap]
    rw [integral_map hcs hG'.aestronglyMeasurable]
  obtain ⟨i1, j1⟩ := hinv (Or.inl rfl) (Or.inl rfl)
  obtain ⟨i2, j2⟩ := hinv (Or.inl rfl) (Or.inr rfl)
  obtain ⟨i3, j3⟩ := hinv (Or.inr rfl) (Or.inl rfl)
  obtain ⟨i4, j4⟩ := hinv (Or.inr rfl) (Or.inr rfl)
  have hsum : ∀ w, G (coordSign 1 1 w) + G (coordSign 1 (-1) w) + G (coordSign (-1) 1 w) +
      G (coordSign (-1) (-1) w) = 4 * ∫ x in closedSquare 0 1, Φ x := by
    intro w
    simp only [hG, ← coordSign_ofReal_mul]
    exact setIntegral_closedSquare_squareFold_add_coordSign hΦ hC _
  have hA : ∫ w, (G (coordSign 1 1 w) + G (coordSign 1 (-1) w)) ∂(planarGaussian 0 1) =
      ∫ w, G (coordSign 1 1 w) ∂(planarGaussian 0 1) +
        ∫ w, G (coordSign 1 (-1) w) ∂(planarGaussian 0 1) := integral_add i1 i2
  have hB : ∫ w, (G (coordSign (-1) 1 w) + G (coordSign (-1) (-1) w)) ∂(planarGaussian 0 1) =
      ∫ w, G (coordSign (-1) 1 w) ∂(planarGaussian 0 1) +
        ∫ w, G (coordSign (-1) (-1) w) ∂(planarGaussian 0 1) := integral_add i3 i4
  have hAB : ∫ w, ((G (coordSign 1 1 w) + G (coordSign 1 (-1) w)) +
      (G (coordSign (-1) 1 w) + G (coordSign (-1) (-1) w))) ∂(planarGaussian 0 1) =
      ∫ w, (G (coordSign 1 1 w) + G (coordSign 1 (-1) w)) ∂(planarGaussian 0 1) +
        ∫ w, (G (coordSign (-1) 1 w) + G (coordSign (-1) (-1) w)) ∂(planarGaussian 0 1) :=
    integral_add (i1.add i2) (i3.add i4)
  have hall : ∫ w, ((G (coordSign 1 1 w) + G (coordSign 1 (-1) w)) +
      (G (coordSign (-1) 1 w) + G (coordSign (-1) (-1) w))) ∂(planarGaussian 0 1) =
      4 * ∫ x in closedSquare 0 1, Φ x := by
    have hfun : (fun w => (G (coordSign 1 1 w) + G (coordSign 1 (-1) w)) +
        (G (coordSign (-1) 1 w) + G (coordSign (-1) (-1) w))) =
        fun _ => 4 * ∫ x in closedSquare 0 1, Φ x := by
      funext w
      rw [← hsum w]
      ring
    rw [hfun, integral_const, probReal_univ, one_smul]
  show ∫ w, G w ∂(planarGaussian 0 1) = _
  linarith

/-- The marginal of reflected Brownian motion in the unit square at a fixed time is the folded
planar Gaussian law. -/
theorem reflectedPlanarBrownianMotion_zero_one_map_eval (x : ℂ) (s : ℝ≥0) :
    (reflectedPlanarBrownianMotion 0 1 x).map (fun b => b s) =
      (planarGaussian x s).map (squareFold 0 1) := by
  have hev : Measurable fun b : ContinuousPath ℂ => b s :=
    (continuous_eval_const s).measurable
  have hcomp : ((fun b : ContinuousPath ℂ => b s) ∘ fun b => (squareFoldCM 0 1).comp b) =
      squareFold 0 1 ∘ fun b => b s := rfl
  rw [reflectedPlanarBrownianMotion, Kernel.map_apply _ (measurable_comp_squareFoldCM 0 1),
    Measure.map_map hev (measurable_comp_squareFoldCM 0 1), ← planarBrownianMotion_map_eval_eq,
    Measure.map_map (continuous_squareFold 0 1).measurable hev, hcomp]

/-- **Lebesgue measure on the unit square is invariant for reflected Brownian motion**: for every
time `s` and Borel `S`, `∫_{K₀} Q_x(b_s ∈ S) dx = |S ∩ K₀|`. -/
theorem lintegral_reflectedPlanarBrownianMotion_eval_mem (s : ℝ≥0) {S : Set ℂ}
    (hS : MeasurableSet S) :
    ∫⁻ x in closedSquare 0 1, reflectedPlanarBrownianMotion 0 1 x {b | b s ∈ S} =
      volume (S ∩ closedSquare 0 1) := by
  have hfold : Measurable (squareFold 0 1) := (continuous_squareFold 0 1).measurable
  have hev : Measurable fun b : ContinuousPath ℂ => b s :=
    (continuous_eval_const s).measurable
  have hpre : MeasurableSet (squareFold 0 1 ⁻¹' S) := hfold hS
  have hQ : ∀ x, reflectedPlanarBrownianMotion 0 1 x {b | b s ∈ S} =
      planarHeatKernel s x (squareFold 0 1 ⁻¹' S) := by
    intro x
    rw [planarHeatKernel_apply, ← Measure.map_apply hfold hS,
      ← reflectedPlanarBrownianMotion_zero_one_map_eval, Measure.map_apply hev hS]
    rfl
  simp_rw [hQ]
  have hmeas : Measurable fun x => planarHeatKernel s x (squareFold 0 1 ⁻¹' S) :=
    Kernel.measurable_coe _ hpre
  have : IsFiniteMeasure ((volume : Measure ℂ).restrict (closedSquare 0 1)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact (isCompact_closedSquare 0 1).measure_lt_top⟩
  have hΦ : Measurable (S.indicator fun _ => (1 : ℝ)) := measurable_const.indicator hS
  have hΦC : ∀ z, |S.indicator (fun _ => (1 : ℝ)) z| ≤ 1 := by
    intro z
    by_cases hz : z ∈ S <;> simp [hz]
  have hid := setIntegral_integral_planarGaussian_squareFold hΦ hΦC s
  have hval : ∀ x, ∫ w, S.indicator (fun _ => (1 : ℝ)) (squareFold 0 1 w) ∂(planarGaussian x s) =
      (planarHeatKernel s x (squareFold 0 1 ⁻¹' S)).toReal := by
    intro x
    have hind : (fun w => S.indicator (fun _ => (1 : ℝ)) (squareFold 0 1 w)) =
        (squareFold 0 1 ⁻¹' S).indicator 1 := by
      funext w
      by_cases hw : squareFold 0 1 w ∈ S <;> simp [hw]
    rw [hind, integral_indicator_one hpre, planarHeatKernel_apply]
    rfl
  simp_rw [hval] at hid
  have hint : Integrable (fun x => (planarHeatKernel s x (squareFold 0 1 ⁻¹' S)).toReal)
      ((volume : Measure ℂ).restrict (closedSquare 0 1)) := by
    refine Integrable.of_bound hmeas.ennreal_toReal.aestronglyMeasurable 1
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact prob_le_one)
  have hlhs : ∫⁻ x in closedSquare 0 1, planarHeatKernel s x (squareFold 0 1 ⁻¹' S) =
      ENNReal.ofReal (∫ x in closedSquare 0 1, (planarHeatKernel s x (squareFold 0 1 ⁻¹' S)).toReal) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun _ => ENNReal.toReal_nonneg)]
    refine lintegral_congr fun x => ?_
    rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rw [hlhs, hid, integral_indicator_const _ hS, smul_eq_mul, mul_one, measureReal_restrict_apply hS,
    measureReal_def, ENNReal.ofReal_toReal]
  exact (measure_mono inter_subset_right).trans_lt
    (isCompact_closedSquare 0 1).measure_lt_top |>.ne

/-- **Invariance of Lebesgue measure on the unit square, integral form**: for every time `s` and
measurable `ψ ≥ 0`, `∫_{K₀} E_x[ψ(b_s)] dx = ∫_{K₀} ψ`. -/
theorem lintegral_lintegral_reflectedPlanarBrownianMotion_eval (s : ℝ≥0) {ψ : ℂ → ℝ≥0∞}
    (hψ : Measurable ψ) :
    ∫⁻ x in closedSquare 0 1, ∫⁻ b, ψ (b s) ∂(reflectedPlanarBrownianMotion 0 1 x) =
      ∫⁻ x in closedSquare 0 1, ψ x := by
  have hev : Measurable fun b : ContinuousPath ℂ => b s :=
    (continuous_eval_const s).measurable
  set κ : Kernel ℂ ℂ := (reflectedPlanarBrownianMotion 0 1).map fun b => b s with hκ
  have hκx : ∀ x, κ x = (reflectedPlanarBrownianMotion 0 1 x).map fun b => b s :=
    fun x => Kernel.map_apply _ hev x
  have hbind : ((volume : Measure ℂ).restrict (closedSquare 0 1)).bind κ =
      (volume : Measure ℂ).restrict (closedSquare 0 1) := by
    ext S hS
    rw [Measure.bind_apply hS κ.measurable.aemeasurable, Measure.restrict_apply hS]
    simp_rw [hκx, Measure.map_apply hev hS]
    exact lintegral_reflectedPlanarBrownianMotion_eval_mem s hS
  have hl : ∀ x, ∫⁻ b, ψ (b s) ∂(reflectedPlanarBrownianMotion 0 1 x) = ∫⁻ y, ψ y ∂κ x := by
    intro x
    rw [hκx, lintegral_map hψ hev]
  simp_rw [hl]
  rw [← Measure.lintegral_bind κ.measurable.aemeasurable hψ.aemeasurable, hbind]

end HarmonicBalls


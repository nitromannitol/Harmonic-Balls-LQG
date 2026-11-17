import HarmonicBalls.Proofs.Potential.LQGClockSingularAnnularSummability

/-! # Splitting localized density increments

A localized density increment is controlled by its annular part and two
nonnegative inner occupations.
-/

open MeasureTheory Set

namespace HarmonicBalls

/-- Split a localized difference at a measurable inner set, retaining the
boundary in the complementary part. -/
theorem abs_integral_indicator_sub_le_complement_add_inner
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (E I : Set X)
    (hE : MeasurableSet E) (hI : MeasurableSet I) (f g : X → ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) :
    |∫ x, E.indicator (fun x => f x - g x) x ∂μ| ≤
      |∫ x, (E \ I).indicator (fun x => f x - g x) x ∂μ| +
      (∫ x, I.indicator f x ∂μ) + ∫ x, I.indicator g x ∂μ := by
  have hA : MeasurableSet (E \ I) := hE.diff hI
  have hJ : MeasurableSet (E ∩ I) := hE.inter hI
  have hsplit : E.indicator (fun x => f x - g x) =
      fun x => (E \ I).indicator (fun x => f x - g x) x +
        (E ∩ I).indicator (fun x => f x - g x) x := by
    funext x
    by_cases hxE : x ∈ E <;> by_cases hxI : x ∈ I <;> simp [hxE, hxI]
  have hbound : (∫ x, |(E ∩ I).indicator (fun x => f x - g x) x| ∂μ) ≤
      ∫ x, (I.indicator f x + I.indicator g x) ∂μ := by
    apply integral_mono_ae (((hf.sub hg).indicator hJ).abs)
      ((hf.indicator hI).add (hg.indicator hI))
    filter_upwards with x
    change |(E ∩ I).indicator (f-g) x| ≤ I.indicator f x + I.indicator g x
    by_cases hxE : x ∈ E <;> by_cases hxI : x ∈ I
    · have hxJ : x ∈ E ∩ I := ⟨hxE, hxI⟩
      simp only [Set.indicator_of_mem hxJ,
        Set.indicator_of_mem hxI, Pi.sub_apply]
      exact abs_le.mpr ⟨by linarith [hf0 x], by linarith [hg0 x]⟩
    · simp [hxI]
    · simpa [hxE, hxI] using add_nonneg (hf0 x) (hg0 x)
    · simp [hxI]
  calc
    _ = |(∫ x, (E \ I).indicator (fun x => f x - g x) x ∂μ) +
        ∫ x, (E ∩ I).indicator (fun x => f x - g x) x ∂μ| := by
      rw [hsplit]
      change |∫ x, ((E \ I).indicator (f-g)) x + ((E ∩ I).indicator (f-g)) x ∂μ| = _
      rw [integral_add ((hf.sub hg).indicator hA) ((hf.sub hg).indicator hJ)]
      rfl
    _ ≤ |∫ x, (E \ I).indicator (fun x => f x - g x) x ∂μ| +
        |∫ x, (E ∩ I).indicator (fun x => f x - g x) x ∂μ| := abs_add_le _ _
    _ ≤ |∫ x, (E \ I).indicator (fun x => f x - g x) x ∂μ| +
        ∫ x, (I.indicator f x + I.indicator g x) ∂μ :=
      add_le_add_right (abs_integral_le_integral_abs.trans hbound) _
    _ = _ := by rw [integral_add (hf.indicator hI) (hg.indicator hI)]; ring

/-- The strict inner ball and closed moving annulus split the closed outer
cutoff without discarding either boundary. -/
theorem abs_integral_closedBall_sub_le_annulus_add_inner
    (μ : Measure ℂ) (ε δ : ℝ) (f g : ℂ → ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hf0 : ∀ z, 0 ≤ f z) (hg0 : ∀ z, 0 ≤ g z) :
    |∫ z, {z : ℂ | ‖z‖ ≤ δ ∧ ‖z‖ ≤ 1/2}.indicator (fun z => f z - g z) z ∂μ| ≤
      |∫ z, {z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ δ ∧ ‖z‖ ≤ 1/2}.indicator
        (fun z => f z - g z) z ∂μ| +
      (∫ z, {z : ℂ | ‖z‖ < ε}.indicator f z ∂μ) +
      ∫ z, {z : ℂ | ‖z‖ < ε}.indicator g z ∂μ := by
  let E : Set ℂ := {z | ‖z‖ ≤ δ ∧ ‖z‖ ≤ 1/2}
  let I : Set ℂ := {z | ‖z‖ < ε}
  have hE : MeasurableSet E :=
    (measurableSet_le measurable_norm measurable_const).inter
      (measurableSet_le measurable_norm measurable_const)
  have hI : MeasurableSet I := measurableSet_lt measurable_norm measurable_const
  have hA : E \ I = {z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ δ ∧ ‖z‖ ≤ 1/2} := by
    ext z
    simp only [mem_sdiff, mem_ofPred_eq, not_lt, E, I]
    tauto
  have h := abs_integral_indicator_sub_le_complement_add_inner μ E I hE hI f g hf hg hf0 hg0
  rw [hA] at h
  exact h

/-- Summable inner occupations and annular increments imply summability of
the localized increments on the closed outer cutoff. -/
theorem summable_closedBall_increment_of_annulus_and_inner
    (μ : Measure ℂ) (ε : ℕ → ℝ) (δ : ℝ) (f g : ℕ → ℂ → ℝ)
    (hf : ∀ n, Integrable (f n) μ) (hg : ∀ n, Integrable (g n) μ)
    (hf0 : ∀ n z, 0 ≤ f n z) (hg0 : ∀ n z, 0 ≤ g n z)
    (ha : Summable (fun n => |∫ z, {z : ℂ | ε n ≤ ‖z‖ ∧ ‖z‖ ≤ δ ∧ ‖z‖ ≤ 1/2}.indicator
      (fun z => f n z - g n z) z ∂μ|))
    (hi : Summable (fun n => ∫ z, {z : ℂ | ‖z‖ < ε n}.indicator (f n) z ∂μ))
    (hj : Summable (fun n => ∫ z, {z : ℂ | ‖z‖ < ε n}.indicator (g n) z ∂μ)) :
    Summable (fun n => |∫ z, {z : ℂ | ‖z‖ ≤ δ ∧ ‖z‖ ≤ 1/2}.indicator
      (fun z => f n z - g n z) z ∂μ|) := by
  apply Summable.of_nonneg_of_le (fun _ => abs_nonneg _) _ ((ha.add hi).add hj)
  intro n
  exact abs_integral_closedBall_sub_le_annulus_add_inner μ (ε n) δ (f n) (g n)
    (hf n) (hg n) (hf0 n) (hg0 n)


end HarmonicBalls

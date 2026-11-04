import HarmonicBalls.Proofs.Sec9.SubharmonicUniqueness
import HarmonicBalls.Steps.SecA.Basic

/-!
# Green-potential comparison for Lemma 9.3

The auxiliary potential in the proof is nonnegative outside the harmonic ball and vanishes
outside both balls. These conclusions use only their quadrature properties and equal masses.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Laplacian

/-- The auxiliary potential in Lemma 9.3 is nonnegative outside the harmonic ball. -/
theorem IsHarmonicBallGen.greenPotential_sub_nonneg_of_isSubharmonicBall
    {μ : Measure ℂ} {A B : Set ℂ} {z : ℂ} (hA : IsHarmonicBallGen μ A z)
    (hB : IsSubharmonicBall μ B z) {R : ℝ} (hAcl : closure A ⊆ ball 0 R)
    (hBcl : closure B ⊆ ball 0 R) (hmass : μ.real A = μ.real B) {x : ℂ}
    (hx : x ∈ ball (0 : ℂ) R \ A) :
    0 ≤ (∫ y in A, greenFunction (ball 0 R) x y ∂μ) -
      ∫ y in B, greenFunction (ball 0 R) x y ∂μ := by
  have hxz : x ≠ z := fun h => hx.2 (h ▸ hA.1.2.1)
  have hAeq := hA.greenPotential_eq_of_steps greenFunctionBallSymmetric hAcl hx
  have hBle := hB.greenPotential_le_of_steps greenFunctionBallSymmetric
    negGreenFunctionMemSubharmonicBallTestClass hBcl hx.1 hxz
  rw [hmass] at hAeq
  linarith

/-- The auxiliary potential in Lemma 9.3 vanishes outside both balls. -/
theorem IsHarmonicBallGen.greenPotential_sub_eq_zero_of_isSubharmonicBall
    {μ : Measure ℂ} {A B : Set ℂ} {z : ℂ} (hA : IsHarmonicBallGen μ A z)
    (hB : IsSubharmonicBall μ B z) {R : ℝ} (hAcl : closure A ⊆ ball 0 R)
    (hBcl : closure B ⊆ ball 0 R) (hmass : μ.real A = μ.real B) {x : ℂ}
    (hx : x ∈ ball (0 : ℂ) R \ A) (hxB : x ∉ B) :
    (∫ y in A, greenFunction (ball 0 R) x y ∂μ) -
      ∫ y in B, greenFunction (ball 0 R) x y ∂μ = 0 := by
  have hAeq := hA.greenPotential_eq_of_steps greenFunctionBallSymmetric hAcl hx
  have hBeq := hB.greenPotential_eq hBcl ⟨hx.1, hxB⟩
  rw [hmass] at hAeq
  linarith

/-- At a boundary point outside the closure of the subharmonic ball, the auxiliary potential
vanishes. -/
theorem IsHarmonicBallGen.greenPotential_sub_eq_zero_on_frontier
    {μ : Measure ℂ} {A B : Set ℂ} {z : ℂ} (hA : IsHarmonicBallGen μ A z)
    (hB : IsSubharmonicBall μ B z) {R : ℝ} (hAcl : closure A ⊆ ball 0 R)
    (hBcl : closure B ⊆ ball 0 R) (hmass : μ.real A = μ.real B) {x : ℂ}
    (hx : x ∈ frontier A \ closure B) :
    (∫ y in A, greenFunction (ball 0 R) x y ∂μ) -
      ∫ y in B, greenFunction (ball 0 R) x y ∂μ = 0 := by
  have hxA : x ∉ A := by
    intro hxA
    exact (mem_frontier_iff_notMem_interior hxA).1 hx.1 (by simpa [hA.1.1.interior_eq] using hxA)
  exact hA.greenPotential_sub_eq_zero_of_isSubharmonicBall hB hAcl hBcl hmass
    ⟨hAcl (frontier_subset_closure hx.1), hxA⟩ (fun hxB => hx.2 (subset_closure hxB))

/-- A full-support measure charges the part of an open set in every open neighbourhood of
one of its boundary points. This is the measure-theoretic input in the final contradiction
of Lemma 9.3. -/
theorem IsOpen.measure_inter_pos_of_mem_frontier {μ : Measure ℂ} [μ.IsOpenPosMeasure]
    {A U : Set ℂ} (hA : IsOpen A) (hU : IsOpen U) {x : ℂ}
    (hx : x ∈ frontier A) (hxU : x ∈ U) : 0 < μ (U ∩ A) :=
  (hU.inter hA).measure_pos μ (mem_closure_iff.1 (frontier_subset_closure hx) U hU hxU)

/-- The distributional Laplacian forbids the auxiliary potential from vanishing on an open
neighbourhood of a boundary point which is disjoint from the comparison ball. -/
theorem not_eqOn_zero_of_hasLaplacian_boundary {μ : Measure ℂ} [μ.IsOpenPosMeasure]
    {A B U V : Set ℂ} {u : ℂ → ℝ} (hA : IsOpen A) (hV : IsOpen V)
    (hVU : V ⊆ U) (hVB : Disjoint V B)
    (hΔ : HasLaplacian u (μ.restrict B) (μ.restrict A) U) {x : ℂ}
    (hx : x ∈ frontier A) (hxV : x ∈ V) : ¬ EqOn u 0 V := by
  intro hu
  obtain ⟨y, hyV, hyA⟩ := mem_closure_iff.1 (frontier_subset_closure hx) V hV hxV
  obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.1 (hV.inter hA) y ⟨hyV, hyA⟩
  obtain ⟨φ, hφ, hφ0, hφy⟩ := IsTestFunction.exists_ne_zero hr hrsub
  have hφU : IsTestFunction U φ := ⟨hφ.1, hφ.2.1, hφ.2.2.trans (inter_subset_left.trans hVU)⟩
  obtain ⟨_, hiA, heq⟩ := hΔ.2 φ hφU
  have hφout : ∀ y, y ∉ V ∩ A → φ y = 0 := by
    intro y hy
    exact image_eq_zero_of_notMem_tsupport (fun h => hy (hφ.2.2 h))
  have hBzero : ∫ y in B, φ y ∂μ = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro y hyB
    exact hφout y (fun hy => (Set.disjoint_left.1 hVB) hy.1 hyB)
  have hAeq : ∫ y in A, φ y ∂μ = ∫ y, φ y ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => hφout y (fun hy' => hy hy'.2))
  have hpos : 0 < ∫ y, φ y ∂μ :=
    integral_pos_of_integrable_nonneg_nonzero hφ.1.continuous
      ((integrableOn_iff_integrable_of_support_subset
        ((subset_tsupport φ).trans (hφ.2.2.trans inter_subset_right))).mp hiA)
      hφ0 (by rw [hφy]; norm_num)
  have huφ : (∫ y, u y * Δ φ y) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards with y
    by_cases hy : y ∈ V
    · simp [hu hy]
    · have hyt : y ∉ tsupport φ := fun h => hy (hφ.2.2 h).1
      simp [laplacian_eq_zero_of_notMem_tsupport hyt]
  rw [huφ, hBzero, hAeq] at heq
  linarith

end HarmonicBalls

import HarmonicBalls.Proofs.Sec6.GreenIntegrability

/-!
# Boundedness of Green potentials on subdomains

A Green potential on an open subdomain of a ball is bounded above by the ball Green
potential. Volume growth gives continuity, hence a compact upper bound, for the latter.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set
open scoped NNReal

/-- The two conventions for the Green potential of a ball agree. -/
theorem greenPotential_ball_eq (μ : Measure ℂ) (R : ℝ) (x : ℂ) :
    greenPotential (ball 0 R) μ x = greenPotentialBall μ R x := by
  unfold greenPotential greenPotentialBall
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun y hy => greenFunction_of_notMem_right hy x)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y => greenFunction_ball_comm R x y)

/-- Hölder continuity of the restricted Green integral implies continuity of the
Green potential on the closure of the domain, since the kernel vanishes outside. -/
theorem greenPotential_continuousOn_of_holder {O : Set ℂ} (μ : Measure ℂ)
    (hholder : ∃ C r : ℝ≥0, 0 < r ∧
      HolderOnWith C r (fun x => ∫ y in O, greenFunction O x y ∂μ) (closure O)) :
    ContinuousOn (greenPotential O μ) (closure O) := by
  obtain ⟨C, r, hr, h⟩ := hholder
  have heq : (fun x => ∫ y in O, greenFunction O x y ∂μ) = greenPotential O μ := by
    funext x
    exact setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun y hy => greenFunction_of_notMem_right hy x)
  rw [heq] at h
  exact h.continuousOn hr

/-- Under volume growth, the Green potential of every open subdomain of a ball is
bounded above on the entire plane. -/
theorem greenPotential_bddAbove_of_volumeGrowth
    {μ : Measure ℂ} [IsLocallyFiniteMeasure μ] {O : Set ℂ} {R βminus βplus : ℝ}
    (hR : 0 < R) (hopen : IsOpen O) (hsub : O ⊆ ball (0 : ℂ) R)
    (hV : VolumeGrowth μ R βminus βplus) :
    ∃ M : ℝ, ∀ x, greenPotential O μ x ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) R).bddAbove_image
    (greenPotentialBall_continuousOn μ inferInstance R βminus βplus hR hV)
  refine ⟨max M 0, fun x => ?_⟩
  by_cases hx : x ∈ O
  · have hxR : x ∈ closedBall (0 : ℂ) R := ball_subset_closedBall (hsub hx)
    have hsmall := integrable_greenFunction_of_volumeGrowth hR hopen hsub hV hxR
    have hbig := integrable_greenFunction_of_volumeGrowth hR isOpen_ball
      (Set.Subset.rfl : ball (0 : ℂ) R ⊆ ball 0 R) hV hxR
    calc greenPotential O μ x ≤ greenPotential (ball 0 R) μ x :=
          integral_mono hsmall hbig (greenFunction_le_of_subset hsub isBounded_ball x)
      _ = greenPotentialBall μ R x := greenPotential_ball_eq μ R x
      _ ≤ M := hM ⟨x, hxR, rfl⟩
      _ ≤ max M 0 := le_max_left _ _
  · have hz : greenPotential O μ x = 0 := by
      simp only [greenPotential, greenFunction_of_notMem_left hx, integral_zero]
    rw [hz]
    exact le_max_right _ _

/-- The ratio of the minimum on a nonempty compact subset to the supremum on the
domain is positive when the potential is continuous on that compact set. -/
theorem greenPotential_extrema_ratio_pos_of_volumeGrowth
    {μ : Measure ℂ} [IsLocallyFiniteMeasure μ] {O K : Set ℂ} {R βminus βplus : ℝ}
    (hR : 0 < R) (hopen : IsOpen O) (hsub : O ⊆ ball (0 : ℂ) R)
    (hV : VolumeGrowth μ R βminus βplus) (hK : IsCompact K) (hKne : K.Nonempty)
    (hKO : K ⊆ O) (hcont : ContinuousOn (greenPotential O μ) K)
    (hμx : ∀ x ∈ O, μ {x} = 0)
    (hμball : ∀ x ∈ O, ∀ r > 0, 0 < μ (ball x r)) :
    0 < ((⨅ z : K, ENNReal.ofReal (greenPotential O μ z)) /
      (⨆ z : O, ENNReal.ofReal (greenPotential O μ z))).toReal := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨z, hz⟩ := hKne
  let : Nonempty K := ⟨⟨z, hz⟩⟩
  obtain ⟨M, hM⟩ := greenPotential_bddAbove_of_volumeGrowth hR hopen hsub hV
  refine potential_extrema_ratio_pos (fun z : K => greenPotential O μ z)
    (fun z : O => greenPotential O μ z) hcont.domRestrict ?_ M
    (fun z => hM z) ⟨z, hKO hz⟩ ?_
  · intro z
    have hzO : (z : ℂ) ∈ O := hKO z.property
    exact greenPotential_pos_of_volumeGrowth hR hopen hsub hV hzO
      (hμx z hzO) (hμball z hzO)
  · exact greenPotential_pos_of_volumeGrowth hR hopen hsub hV (hKO hz)
      (hμx z (hKO hz)) (hμball z (hKO hz))

end HarmonicBalls.Section6

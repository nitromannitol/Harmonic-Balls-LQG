import HarmonicBalls.Proofs.Sec6.DiscPotentialTranslation
import HarmonicBalls.Proofs.Potential.GreenPotentialHolder

/-! # Hölder regularity of Green potentials on translated discs -/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set
open scoped NNReal Topology

/-- An upper volume bound on an ambient ball gives the Green-potential clause
of Proposition 2.5 on every disc contained in it. -/
theorem greenPotential_disc_holderOnWith_of_volumeGrowth
    {μ : Measure ℂ} [IsLocallyFiniteMeasure μ] {R r βm βp : ℝ} {c : ℂ}
    (hr : 0 < r) (hV : VolumeGrowth μ R βm βp)
    (hsub : ball c r ⊆ ball 0 R) {f : ℂ → ℝ}
    (hf : MemLp f ⊤ (μ.restrict (closedBall c r))) :
    (∀ x ∈ closedBall c r,
      IntegrableOn (fun y => greenFunction (ball c r) x y * f y) (ball c r) μ) ∧
    ∃ C t : ℝ≥0, 0 < t ∧ HolderOnWith C t
      (fun x => ∫ y in ball c r, greenFunction (ball c r) x y * f y ∂μ)
      (closedBall c r) := by
  let e : ℂ ≃ᵐ ℂ := (Homeomorph.addRight (-c)).toMeasurableEquiv
  let ν := μ.map (fun z : ℂ => z - c)
  let : IsLocallyFiniteMeasure ν := isLocallyFiniteMeasure_map_sub_right inferInstance c
  have hclosed : e ⁻¹' closedBall (0 : ℂ) r = closedBall c r := by
    ext y
    change y - c ∈ closedBall (0 : ℂ) r ↔ y ∈ closedBall c r
    simp only [mem_closedBall, dist_eq_norm, sub_zero]
  have hopen : e ⁻¹' ball (0 : ℂ) r = ball c r := by
    change (fun y : ℂ => y - c) ⁻¹' ball 0 r = ball c r
    simpa only [zero_add] using preimage_ball_sub_right c 0 r
  have hrest : ν.restrict (closedBall 0 r) = (μ.restrict (closedBall c r)).map e := by
    rw [show ν = μ.map e from rfl, e.restrict_map, hclosed]
  have hf' : MemLp (fun y : ℂ => f (y + c)) ⊤ (ν.restrict (closedBall 0 r)) := by
    rw [hrest, e.memLp_map_measure_iff]
    change MemLp (fun y => f ((y - c) + c)) ⊤ (μ.restrict (closedBall c r))
    simpa only [sub_add_cancel] using hf
  obtain ⟨hi, C, t, ht, hh⟩ := greenPotential_ball_holderOnWith (μ := ν) hr
    (volumeGrowth_map_sub_right hV hsub) hf'
  have hball : (fun z : ℂ => z + c) '' ball 0 r = ball c r := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa only [mem_ball, dist_eq_norm, add_sub_cancel_right, sub_zero] using hx
    · intro hz
      exact ⟨z - c, by simpa only [mem_ball, dist_eq_norm, sub_zero] using hz, sub_add_cancel z c⟩
  have hkernel (x y : ℂ) : greenFunction (ball 0 r) (x - c) (y - c) =
      greenFunction (ball c r) x y := by
    have h := greenFunction_translate (ball 0 r) c (x - c) (y - c)
    simpa only [hball, sub_add_cancel] using h.symm
  have hx (x : ℂ) (hx : x ∈ closedBall c r) : x - c ∈ closedBall (0 : ℂ) r := by
    simpa only [mem_closedBall, dist_eq_norm, sub_zero] using hx
  have heq (x : ℂ) :
      (∫ y in ball 0 r, greenFunction (ball 0 r) (x - c) y * f (y + c) ∂ν) =
      ∫ y in ball c r, greenFunction (ball c r) x y * f y ∂μ := by
    rw [show ν = μ.map e from rfl, e.restrict_map, hopen, integral_map_equiv]
    change (∫ y in ball c r, greenFunction (ball 0 r) (x - c) (y - c) *
      f ((y - c) + c) ∂μ) = _
    simp only [sub_add_cancel, hkernel]
  refine ⟨?_, ⟨C, t, ht, ?_⟩⟩
  · intro x hx'
    have h := (integrableOn_map_equiv e).1 (hi (x - c) (hx x hx'))
    rw [hopen] at h
    change IntegrableOn (fun y => greenFunction (ball 0 r) (x - c) (y - c) *
      f ((y - c) + c)) (ball c r) μ at h
    simpa only [sub_add_cancel, hkernel] using h
  · intro x hx' y hy'
    have h := hh (x - c) (hx x hx') (y - c) (hx y hy')
    dsimp only at h
    rw [heq x, heq y] at h
    simpa only [edist_dist, dist_eq_norm, sub_sub_sub_cancel_right] using h

end HarmonicBalls.Section6

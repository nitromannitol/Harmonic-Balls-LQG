import HarmonicBalls.Proofs.Potential.LQGSingularGreenPotentialHolder
import HarmonicBalls.Proofs.Sec6.DiscPotentialHolderTranslation

/-! # Hölder Regularity of Green potentials on translated discs -/

noncomputable section

namespace HarmonicBalls

open HarmonicBalls.Section6

open MeasureTheory Metric Set
open scoped NNReal Topology ENNReal
open Filter

/-- A compact-center upper power bound gives Hölder Green potentials on a disc. -/
theorem greenPotential_disc_holder_of_ball_power
    {μ : Measure ℂ} [IsLocallyFiniteMeasure μ] {c : ℂ} {R C β r₀ : ℝ}
    (hr : 0 < R) (hC : 0 < C) (hβ : 0 < β) (hr₀ : 0 < r₀)
    (hb : ∀ z : ℂ, ‖z‖ ≤ ‖c‖ + R → ∀ s : ℝ, 0 < s → s ≤ r₀ →
      μ (ball z s) ≤ ENNReal.ofReal (C * s ^ β))
    {f : ℂ → ℝ} (hf : MemLp f ⊤ (μ.restrict (closedBall c R))) :
    (∀ x ∈ closedBall c R,
      IntegrableOn (fun y => greenFunction (ball c R) x y * f y) (ball c R) μ) ∧
    ∃ K t : ℝ≥0, 0 < t ∧ HolderOnWith K t
      (fun x => ∫ y in ball c R, greenFunction (ball c R) x y * f y ∂μ)
      (closedBall c R) := by
  let e : ℂ ≃ᵐ ℂ := (Homeomorph.addRight (-c)).toMeasurableEquiv
  let ν := μ.map (fun z : ℂ => z - c)
  let : IsLocallyFiniteMeasure ν := isLocallyFiniteMeasure_map_sub_right inferInstance c
  have hclosed : e ⁻¹' closedBall (0 : ℂ) R = closedBall c R := by
    ext y
    change y - c ∈ closedBall (0 : ℂ) R ↔ y ∈ closedBall c R
    simp only [mem_closedBall, dist_eq_norm, sub_zero]
  have hopen : e ⁻¹' ball (0 : ℂ) R = ball c R := by
    change (fun y : ℂ => y - c) ⁻¹' ball 0 R = ball c R
    simpa only [zero_add] using preimage_ball_sub_right c 0 R
  have hrest : ν.restrict (closedBall 0 R) = (μ.restrict (closedBall c R)).map e := by
    rw [show ν = μ.map e from rfl, e.restrict_map, hclosed]
  have hf' : MemLp (fun y : ℂ => f (y + c)) ⊤ (ν.restrict (closedBall 0 R)) := by
    rw [hrest, e.memLp_map_measure_iff]
    change MemLp (fun y => f ((y - c) + c)) ⊤ (μ.restrict (closedBall c R))
    simpa only [sub_add_cancel] using hf
  have hb' : ∀ z : ℂ, ‖z‖ ≤ R → ∀ s : ℝ, 0 < s → s ≤ r₀ →
      ν (ball z s) ≤ ENNReal.ofReal (C * s ^ β) := by
    intro z hz s hs hss
    rw [show ν = μ.map (fun z : ℂ => z - c) from rfl,
      Measure.map_apply (by fun_prop) measurableSet_ball, preimage_ball_sub_right]
    apply hb (z + c) _ s hs hss
    calc
      ‖z + c‖ ≤ ‖z‖ + ‖c‖ := norm_add_le _ _
      _ ≤ ‖c‖ + R := by linarith
  obtain ⟨δ, hδ, hup⟩ := small_ball_power_absorb_constant hC hβ hr₀ hb'
  set M := (eLpNorm (fun y : ℂ => f (y + c)) ⊤ (ν.restrict (closedBall 0 R))).toReal
  have hM : 0 ≤ M := ENNReal.toReal_nonneg
  have hfM' : ∀ᵐ y ∂ν.restrict (closedBall 0 R), |f (y + c)| ≤ M := by
    filter_upwards [ae_le_eLpNormEssSup (f := fun y : ℂ => f (y + c))
      (μ := ν.restrict (closedBall 0 R))] with y hy
    rw [Real.enorm_eq_ofReal_abs] at hy
    exact (ENNReal.ofReal_le_iff_le_toReal hf'.ne).1 (hy.trans eLpNormEssSup_le_eLpNorm_top)
  have hfM : ∀ᵐ y ∂ν.restrict (ball 0 R), |f (y + c)| ≤ M :=
    ae_restrict_of_ae_restrict_of_subset ball_subset_closedBall hfM'
  obtain ⟨hi, hD⟩ := greenPotential_ball_holder_of_upper hr hδ (show 0 < β / 2 by positivity)
    hup measure_ball_lt_top.ne (hf'.aestronglyMeasurable.mono_set ball_subset_closedBall) hM hfM
  let K : ℝ≥0 := ⟨greenPotentialHolderConstant (β / 2) δ (ν (ball 0 R)).toReal * M,
    mul_nonneg (greenPotentialHolderConstant_nonneg (by positivity) hδ ENNReal.toReal_nonneg) hM⟩
  let t : ℝ≥0 := ⟨greenPotentialHolderExponent (β / 2),
    (greenPotentialHolderExponent_pos (show 0 < β / 2 by positivity)).le⟩
  have ht : 0 < t := greenPotentialHolderExponent_pos (show 0 < β / 2 by positivity)
  have hh : HolderOnWith K t
      (fun x => ∫ y in ball 0 R, greenFunction (ball 0 R) x y * f (y + c) ∂ν)
      (closedBall 0 R) := by
    apply holderOnWith_of_dist_le
    intro x hx y hy
    rw [Real.dist_eq, dist_eq_norm]
    exact hD x hx y hy
  have hball : (fun z : ℂ => z + c) '' ball 0 R = ball c R := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa only [mem_ball, dist_eq_norm, add_sub_cancel_right, sub_zero] using hx
    · intro hz
      exact ⟨z - c, by simpa only [mem_ball, dist_eq_norm, sub_zero] using hz, sub_add_cancel z c⟩
  have hkernel (x y : ℂ) : greenFunction (ball 0 R) (x - c) (y - c) =
      greenFunction (ball c R) x y := by
    have h := greenFunction_translate (ball 0 R) c (x - c) (y - c)
    simpa only [hball, sub_add_cancel] using h.symm
  have hx (x : ℂ) (hx : x ∈ closedBall c R) : x - c ∈ closedBall (0 : ℂ) R := by
    simpa only [mem_closedBall, dist_eq_norm, sub_zero] using hx
  have heq (x : ℂ) :
      (∫ y in ball 0 R, greenFunction (ball 0 R) (x - c) y * f (y + c) ∂ν) =
      ∫ y in ball c R, greenFunction (ball c R) x y * f y ∂μ := by
    rw [show ν = μ.map e from rfl, e.restrict_map, hopen, integral_map_equiv]
    change (∫ y in ball c R, greenFunction (ball 0 R) (x - c) (y - c) *
      f ((y - c) + c) ∂μ) = _
    simp only [sub_add_cancel, hkernel]
  refine ⟨?_, ⟨K, t, ht, ?_⟩⟩
  · intro x hx'
    have h := (integrableOn_map_equiv e).1 (hi (x - c) (hx x hx'))
    rw [hopen] at h
    change IntegrableOn (fun y => greenFunction (ball 0 R) (x - c) (y - c) *
      f ((y - c) + c)) (ball c R) μ at h
    simpa only [sub_add_cancel, hkernel] using h
  · intro x hx' y hy'
    have h := hh (x - c) (hx x hx') (y - c) (hx y hy')
    dsimp only at h
    rw [heq x, heq y] at h
    simpa only [edist_dist, dist_eq_norm, sub_sub_sub_cancel_right] using h

/-- On one event every disc has Hölder Green potentials for bounded densities
with respect to the actual singular measure. -/
theorem IsWholePlaneGFF.ae_singular_greenPotential_disc_holder
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {γ α : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hαQ : α < lqgQ γ)
    {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ α hcirc μ) :
    ∀ᵐ ω ∂P, ∀ (c : ℂ) (R : ℝ), 0 < R → ∀ f : ℂ → ℝ,
      MemLp f ⊤ ((μ ω).restrict (closedBall c R)) →
      (∀ x ∈ closedBall c R,
        IntegrableOn (fun y => greenFunction (ball c R) x y * f y) (ball c R) (μ ω)) ∧
      ∃ C r : ℝ≥0, 0 < r ∧ HolderOnWith C r
        (fun x => ∫ y in ball c R, greenFunction (ball c R) x y * f y ∂(μ ω))
        (closedBall c R) := by
  filter_upwards [hh.ae_singular_limit_and_approximant_ball_power hγ hγ2 hαQ hμ, hμ] with ω hb hlim
  let _ := hlim.isLocallyFiniteMeasure
  intro c R hR f hf
  obtain ⟨C, β, r₀, hC, hβ, hr₀, hp⟩ := hb (‖c‖ + R)
  exact greenPotential_disc_holder_of_ball_power hR hC hβ hr₀
    (fun z hz r hr hrr => (hp z hz r hr hrr).1) hf

end HarmonicBalls

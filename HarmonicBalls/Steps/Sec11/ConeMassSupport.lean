import HarmonicBalls.Steps.Sec11.ConeOpen
import HarmonicBalls.Steps.Sec11.ConeNonzero
import HarmonicBalls.Proofs.Sec6.SimultaneousSingularMeasure

/-! # Full support in an annular cone -/

namespace HarmonicBalls

/-! The cone-probability development uses Leonardo Bonanno's
Lattice-Probability formalization, including its Cameron-Martin port through
the local smooth-shift and fixed-shift decoder developments. -/

open MeasureTheory Metric Set Filter

/-- The intersection of a cone and a positive annulus contains a nonempty
open set, including when the cone is the complement of an open cone. -/
theorem IsCone.exists_open_subset_annulus {Q : Set ℂ} (hQ : IsCone Q)
    (z : ℂ) {r : ℝ} (hr : 0 < r) :
    ∃ U : Set ℂ, IsOpen U ∧ U.Nonempty ∧ U ⊆ annulus z r (2 * r) ∩ coneAt Q z := by
  obtain ⟨V, hV, hVQ⟩ := hQ.exists_open_subcone
  let U := annulus z r (2 * r) ∩ coneAt V z
  have hopen : IsOpen U := by
    apply (isOpen_ball.sdiff isClosed_closedBall).inter
    exact (Homeomorph.addRight z).isOpenMap V hV.2.1
  have hsub : U ⊆ annulus z r (2 * r) ∩ coneAt Q z := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    obtain ⟨y, hy, rfl⟩ := hx.2
    exact ⟨y, hVQ hy, rfl⟩
  obtain ⟨x, hxann, hxcone⟩ := (show IsCone V from Or.inl hV).coneAt_inter_annulus_nonempty z
    (show 0 < r / 3 by positivity)
  have hx : x ∈ U := by
    refine ⟨⟨?_, ?_⟩, hxcone⟩
    · change dist x z < 2 * r
      have h : dist x z < 5 * (r / 3) := hxann.1
      linarith
    · change ¬ dist x z ≤ r
      have h : 4 * (r / 3) < dist x z := lt_of_not_ge hxann.2
      linarith
  exact ⟨U, hopen, ⟨x, hx⟩, hsub⟩

/-- Full support gives positive mass to each annular cone. -/
theorem IsCone.annulus_mass_pos_of_fullSupport {Q : Set ℂ} (hQ : IsCone Q)
    (μ : Measure ℂ) (hfull : ∀ U : Set ℂ, IsOpen U → U.Nonempty → 0 < μ U)
    (z : ℂ) {r : ℝ} (hr : 0 < r) :
    0 < μ (annulus z r (2 * r) ∩ coneAt Q z) := by
  obtain ⟨U, ho, hn, hsub⟩ := hQ.exists_open_subset_annulus z hr
  exact (hfull U ho hn).trans_le (measure_mono hsub)

universe u

/-- The actual singular LQG limit has positive mass in every positive
annular cone, under the scaled-ball mass and whole-plane existence inputs. -/
theorem ae_cone_annulus_mass_pos
    (hS : WholePlaneScaledBallMassStep.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hG : IsWholePlaneGFF P hC hcirc)
    (hE0 : LQGMeasureExistence P γ 0 hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ Q : Set ℂ, IsCone Q → ∀ z : ℂ, ∀ r : ℝ, 0 < r →
      0 < μ ω (annulus z r (2 * r) ∩ coneAt Q z) := by
  filter_upwards [Section6.ae_fullSupport_all_singular_limits hS P γ hγ hγ2 hC hcirc hG hE0, hμ]
    with ω hfull hlimit Q hQ z r hr
  exact hQ.annulus_mass_pos_of_fullSupport (μ ω) (hfull α₀ (μ ω) hlimit) z hr

end HarmonicBalls

import HarmonicBalls.Proofs.Sec8.SingularTypicalPointTransfer
import HarmonicBalls.Proofs.Sec8.RootedObservedBindLaw

/-! # Observed rooted laws for singular LQG measures

The Weyl identity gives mutual absolute continuity of regular and singular
measures once the relevant origin atoms vanish. This equivalence lifts to
observed rooted laws on bounded balls. The imported Section 8 development
uses Leonardo Bonanno's whole-plane GFF formalization.
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal Topology

/-- The regular measure is dominated by the singular measure if the regular
measure has no atom at the insertion point. -/
theorem regular_absolutelyContinuous_of_singular_weight
    {μ ν : Measure ℂ} {γ α : ℝ}
    (hweight : μ.restrict {0}ᶜ =
      (ν.withDensity fun x => ENNReal.ofReal (‖x‖ ^ (-(γ * α)))).restrict {0}ᶜ)
    (hzero : ν {0} = 0) : ν ≪ μ := by
  let νw := ν.withDensity (fun x => ENNReal.ofReal (‖x‖ ^ (-(γ * α))))
  have hwzero : νw {0} = 0 := (withDensity_absolutelyContinuous ν _) hzero
  have hwae : ∀ᵐ z ∂νw, z ∈ ({0} : Set ℂ)ᶜ := by simpa [ae_iff] using hwzero
  have hwrest : νw.restrict ({0} : Set ℂ)ᶜ = νw := Measure.restrict_eq_self_of_ae_mem hwae
  have hdom : ν ≪ νw := Section6.absolutelyContinuous_singularWeight hzero _
  apply hdom.trans
  rw [← hwrest, ← hweight]
  exact Measure.absolutelyContinuous_restrict

universe u

/-- Under volume growth, the regular LQG measure is absolutely continuous
with respect to the singular LQG measure of the same field. -/
theorem IsWholePlaneGFF.ae_regular_absolutelyContinuous_of_volumeGrowth
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ ν : Ω → Measure ℂ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    (hh : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hν : IsLQGMeasureOfField P γ 0 hcirc ν) : ∀ᵐ ω ∂P, ν ω ≪ μ ω := by
  have hQ : 0 < lqgQ γ := by unfold lqgQ; positivity
  have hnon := Section6.lqgMeasureNonatomic_of_volumeGrowth hgrowth P γ 0 hC hcirc
    hh hγ hγ2 hQ ν hν
  filter_upwards [hh.ae_singular_weight_of_existing_regular_measure hμ hν, hnon]
    with ω hweight hnonω
  exact regular_absolutelyContinuous_of_singular_weight hweight (hnonω 0)

/-- Positive mass of a Borel set for the regular measure implies positive
mass for the singular measure, under the same volume-growth input. -/
theorem IsWholePlaneGFF.ae_singular_mass_ne_zero_of_regular
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ ν : Ω → Measure ℂ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    (hh : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hν : IsLQGMeasureOfField P γ 0 hcirc ν) (B : Set ℂ)
    (hpos : ∀ᵐ ω ∂P, ν ω B ≠ 0) : ∀ᵐ ω ∂P, μ ω B ≠ 0 := by
  filter_upwards [hh.ae_regular_absolutelyContinuous_of_volumeGrowth hgrowth hγ hγ2 hμ hν,
    hpos] with ω hdom hνω hμω
  exact hνω (hdom hμω)

/-- Almost-sure domination of random measures lifts to their observed
unnormalized rooted laws on any measurable set of finite mass. -/
theorem observed_restricted_bind_absolutelyContinuous
    {Ω F : Type*} [MeasurableSpace Ω] [MeasurableSpace F]
    (P : Measure Ω) (μ ν : Ω → Measure ℂ)
    (hμ : AEMeasurable μ P) (hν : AEMeasurable ν P)
    (X : Ω → F) (hX : Measurable X) (B : Set ℂ) (hB : MeasurableSet B)
    (hμfin : ∀ᵐ ω ∂P, μ ω B ≠ ∞) (hνfin : ∀ᵐ ω ∂P, ν ω B ≠ ∞)
    (hdom : ∀ᵐ ω ∂P, μ ω ≪ ν ω) :
    (P.bind fun ω => ((μ ω).restrict B).map (fun z => (X ω, z))) ≪
      (P.bind fun ω => ((ν ω).restrict B).map (fun z => (X ω, z))) := by
  have hμm := aemeasurable_observed_restricted_root_kernel P μ hμ X hX B hB hμfin
  have hνm := aemeasurable_observed_restricted_root_kernel P ν hν X hX B hB hνfin
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hz
  rw [Measure.bind_apply hs hνm] at hz
  rw [Measure.bind_apply hs hμm]
  apply (lintegral_eq_zero_iff' ((Measure.measurable_coe hs).comp_aemeasurable hμm)).mpr
  have he := (lintegral_eq_zero_iff' ((Measure.measurable_coe hs).comp_aemeasurable hνm)).mp hz
  filter_upwards [hdom, he] with ω hω hωs
  exact ((hω.restrict B).map measurable_prodMk_left) hωs

/-- The observed rooted laws of the regular and singular measures on each
bounded ball have the same null sets, under volume growth. -/
theorem IsWholePlaneGFF.ae_observed_rooted_laws_equivalent
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ ν : Ω → Measure ℂ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    (hh : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hν : IsLQGMeasureOfField P γ 0 hcirc ν) (s : ℝ) :
    let X : Ω → RawMeanZeroTest → ℝ := fun ω φ => hC ω φ.1
    let A := P.bind fun ω => ((μ ω).restrict (ball 0 s)).map (fun z => (X ω, z))
    let B := P.bind fun ω => ((ν ω).restrict (ball 0 s)).map (fun z => (X ω, z))
    A ≪ B ∧ B ≪ A := by
  dsimp only
  let X : Ω → RawMeanZeroTest → ℝ := fun ω φ => hC ω φ.1
  have hX : Measurable X := by
    apply measurable_pi_iff.mpr
    intro φ
    exact hh.measurable_pairing φ.1 φ.2.1
  have hfinμ : ∀ᵐ ω ∂P, μ ω (ball 0 s) ≠ ∞ := by
    filter_upwards [hμ] with ω hω
    let : IsLocallyFiniteMeasure (μ ω) := hω.isLocallyFiniteMeasure
    exact measure_ball_ne_top
  have hfinν : ∀ᵐ ω ∂P, ν ω (ball 0 s) ≠ ∞ := by
    filter_upwards [hν] with ω hω
    let : IsLocallyFiniteMeasure (ν ω) := hω.isLocallyFiniteMeasure
    exact measure_ball_ne_top
  constructor
  · exact observed_restricted_bind_absolutelyContinuous P μ ν
      (hh.aemeasurable_lqgMeasure hμ) (hh.aemeasurable_lqgMeasure hν) X hX
      _ measurableSet_ball hfinμ hfinν
      (hh.ae_singular_absolutelyContinuous_of_volumeGrowth hgrowth hγ hγ2 hα hμ hν)
  · exact observed_restricted_bind_absolutelyContinuous P ν μ
      (hh.aemeasurable_lqgMeasure hν) (hh.aemeasurable_lqgMeasure hμ) X hX
      _ measurableSet_ball hfinν hfinμ
      (hh.ae_regular_absolutelyContinuous_of_volumeGrowth hgrowth hγ hγ2 hμ hν)

end HarmonicBalls

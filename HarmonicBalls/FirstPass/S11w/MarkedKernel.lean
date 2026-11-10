import HarmonicBalls.FirstPass.S11c.JointVersion
import HarmonicBalls.Proofs.Sec6.JointSingularMeasureMeasurability
import HarmonicBalls.Proposed.LQG
import HarmonicBalls.FirstPass.Frozen.S11c
import HarmonicBalls.FirstPass.S11w.BallFinite

/-!
# Measurability of the mu-weighted Campbell mark integral (fp-S11w; discharges `hmeas` of `FirstPass/S11i/CampbellGlue.lean:37`)

For a random Radon measure `μ` (the LQG measure of `IsLQGMeasureOfField`), the map
`ω ↦ μ_ω(B)⁻¹ * ∫_{B} 1_S(campbellMarkedObs α₀ D (hC ω) z) dμ_ω(z)` is almost surely measurable.

Route (no new Prop):
* `Section6.exists_jointly_measurable_subcritical_lqgMeasures` gives a jointly measurable family `M` of LQG measures
  (from the named existence input `LQGMeasureExistence`, `Proposed/LQG.lean`, at the subcritical insertions
  `γ`-`Q - 1/(n+1)`); `S11c.ae_eq_joint_version` identifies `μ ω = M (ω, α₀)` almost surely.
* `measurable_lintegral_of_finite_family`: for a measurable family of finite measures `ν ω` and a jointly measurable
  integrand, `ω ↦ ∫ g(ω, z) dν_ω(z)` is measurable (a Kernel-free monotone-class argument on `Measurable.ennreal_induction`).
* To have finite measures for every `ω`, the family is replaced by its restriction to the closed balls `B̄_N`,
  on the event that all their masses are finite (an event of full measure, measurable in `ω`), and by `0` elsewhere.
-/

namespace HarmonicBalls.S11w

open MeasureTheory Set Metric Filter
open scoped ENNReal

/-- Measurability of `ω ↦ ∫ g(ω, z) dν_ω(z)` for a measurable family `ν` of finite measures and a jointly measurable
integrand `g`. -/
theorem measurable_lintegral_of_finite_family {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    {ν : Ω → Measure α} (hν : Measurable ν) (hfin : ∀ ω, IsFiniteMeasure (ν ω))
    {g : Ω × α → ℝ≥0∞} (hg : Measurable g) :
    Measurable fun ω => ∫⁻ z, g (ω, z) ∂(ν ω) := by
  refine Measurable.ennreal_induction
    (motive := fun g : Ω × α → ℝ≥0∞ => Measurable fun ω => ∫⁻ z, g (ω, z) ∂(ν ω)) ?_ ?_ ?_ hg
  · intro c s hs
    have hmass : Measurable fun ω => ν ω (Prod.mk ω ⁻¹' s) :=
      ProbabilityTheory.Kernel.measurable_kernel_prodMk_left_of_finite (κ := ⟨ν, hν⟩) hs (fun ω => hfin ω)
    have heq : (fun ω => ∫⁻ z, (s.indicator fun _ => c) (ω, z) ∂(ν ω)) =
        fun ω => c * ν ω (Prod.mk ω ⁻¹' s) := by
      funext ω
      exact lintegral_indicator_const (measurable_prodMk_left hs) c
    show Measurable fun ω => ∫⁻ z, (s.indicator fun _ => c) (ω, z) ∂(ν ω)
    rw [heq]
    exact hmass.const_mul c
  · intro f g _ hf hg hfP hgP
    have heq : (fun ω => ∫⁻ z, (f + g) (ω, z) ∂(ν ω)) =
        fun ω => (∫⁻ z, f (ω, z) ∂(ν ω)) + ∫⁻ z, g (ω, z) ∂(ν ω) := by
      funext ω
      exact lintegral_add_left (hf.comp measurable_prodMk_left) _
    show Measurable fun ω => ∫⁻ z, (f + g) (ω, z) ∂(ν ω)
    rw [heq]
    exact hfP.add hgP
  · intro f hf hmono hP
    have heq : (fun ω => ∫⁻ z, (fun x => ⨆ n, f n x) (ω, z) ∂(ν ω)) =
        fun ω => ⨆ n, ∫⁻ z, f n (ω, z) ∂(ν ω) := by
      funext ω
      exact lintegral_iSup (fun n => (hf n).comp measurable_prodMk_left)
        (fun m n hmn z => hmono hmn (ω, z))
    show Measurable fun ω => ∫⁻ z, (fun x => ⨆ n, f n x) (ω, z) ∂(ν ω)
    rw [heq]
    exact Measurable.iSup fun n => hP n

/-- **Measurability of the mu-weighted Campbell mark integral.** Let `μ` be the LQG measure of the field
`h = h^ℂ - α₀ log|·|` (`IsLQGMeasureOfField`, `α₀ < Q`), with the existence input `hE` (`LQGMeasureExistence`, Proposed).
For a bounded Borel set `B` and a measurable set `S` of observations, `ω ↦ μ_ω(B)⁻¹ ∫_B 1_S(campbellMarkedObs) dμ_ω`
is almost surely measurable. -/
theorem aemeasurable_campbellMarked_mass {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {γ α₀ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα₀ : α₀ < HarmonicBalls.lqgQ γ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (hG : HarmonicBalls.IsWholePlaneGFF P hC hcirc)
    (hE : ∀ n : ℕ, HarmonicBalls.LQGMeasureExistence P γ (HarmonicBalls.lqgQ γ - 1 / ((n : ℝ) + 1)) hC hcirc)
    {μ : Ω → Measure ℂ} (hμ : HarmonicBalls.IsLQGMeasureOfField P γ α₀ hcirc μ)
    (D : Set ℂ) {B : Set ℂ} (hB : MeasurableSet B) (hBb : Bornology.IsBounded B)
    {S : Set (ℂ × ({φ : ℂ → ℝ // HarmonicBalls.IsTestFunction D φ ∧ ∫ x, φ x = 0} → ℝ))}
    (hS : MeasurableSet S) :
    AEMeasurable (fun ω => (μ ω B)⁻¹ * ∫⁻ z in B,
      S.indicator (fun _ => (1 : ℝ≥0∞)) (HarmonicBalls.campbellMarkedObs α₀ D (hC ω) z) ∂(μ ω)) P := by
  classical
  obtain ⟨M, hM, hMlim⟩ :=
    HarmonicBalls.Section6.exists_jointly_measurable_subcritical_lqgMeasures P γ hγ hγ2 hC hcirc hG hE
  have hν : Measurable fun ω => M (ω, α₀) := hM.comp (measurable_id.prodMk measurable_const)
  have hae : ∀ᵐ ω ∂P, μ ω = M (ω, α₀) := HarmonicBalls.S11c.ae_eq_joint_version hMlim hμ hα₀
  have hfinite := HarmonicBalls.S11w.ae_forall_measure_closedBall_ne_top hμ
  -- the good event: all closed-ball masses of the measurable version are finite
  have hGmeas : MeasurableSet {ω : Ω | ∀ N : ℕ, M (ω, α₀) (closedBall (0 : ℂ) (N : ℝ)) ≠ ∞} := by
    have : {ω : Ω | ∀ N : ℕ, M (ω, α₀) (closedBall (0 : ℂ) (N : ℝ)) ≠ ∞} =
        ⋂ N : ℕ, {ω : Ω | M (ω, α₀) (closedBall (0 : ℂ) (N : ℝ)) ≠ ∞} := by
      ext ω; simp
    rw [this]
    refine MeasurableSet.iInter fun N => ?_
    exact ((Measure.measurable_measure.1 hν _ measurableSet_closedBall) (measurableSet_singleton ∞)).compl
  set G : Set Ω := {ω : Ω | ∀ N : ℕ, M (ω, α₀) (closedBall (0 : ℂ) (N : ℝ)) ≠ ∞} with hGdef
  -- the modified family `ρ`, finite on every closed ball for every `ω`
  set ρ : Ω → Measure ℂ := fun ω => if ω ∈ G then M (ω, α₀) else 0 with hρdef
  have hρ : Measurable ρ := Measurable.ite hGmeas hν measurable_const
  have hρfin : ∀ ω (N : ℕ), ρ ω (closedBall (0 : ℂ) (N : ℝ)) ≠ ∞ := by
    intro ω N
    by_cases hω : ω ∈ G
    · simpa [hρdef, hω] using hω N
    · simp [hρdef, hω]
  have hρae : ∀ᵐ ω ∂P, μ ω = ρ ω := by
    filter_upwards [hae, hfinite] with ω hω hωf
    have hωG : ω ∈ G := fun N => by rw [← hω]; exact hωf N
    simp only [hρdef, hωG, ↓reduceIte]
    exact hω
  -- the bounded set `B` lies in some closed ball `B̄_N`
  obtain ⟨R, hR⟩ := hBb.subset_closedBall (0 : ℂ)
  obtain ⟨N, hN⟩ : ∃ N : ℕ, R ≤ N := exists_nat_ge R
  have hBN : B ⊆ closedBall (0 : ℂ) (N : ℝ) := hR.trans (closedBall_subset_closedBall hN)
  -- the restricted family `κ ω = (ρ ω)|_{B̄_N}`, finite for every `ω`
  have hκ : Measurable fun ω => (ρ ω).restrict (closedBall (0 : ℂ) (N : ℝ)) := by
    refine Measure.measurable_of_measurable_coe _ (fun s hs => ?_)
    simp only [Measure.restrict_apply hs]
    exact Measure.measurable_measure.1 hρ _ (hs.inter measurableSet_closedBall)
  have hκfin : ∀ ω, IsFiniteMeasure ((ρ ω).restrict (closedBall (0 : ℂ) (N : ℝ))) := fun ω =>
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 (hρfin ω N)⟩
  -- the jointly measurable integrand
  have hobs : Measurable fun p : Ω × ℂ => HarmonicBalls.campbellMarkedObs α₀ D (hC p.1) p.2 := by
    unfold HarmonicBalls.campbellMarkedObs
    refine Measurable.prodMk measurable_snd ?_
    refine Measurable.of_eval (fun φ => ?_)
    have hφ : HarmonicBalls.IsTestFunction Set.univ φ.1 :=
      ⟨φ.2.1.1, φ.2.1.2.1, Set.subset_univ _⟩
    unfold HarmonicBalls.fieldPairing
    exact ((hG.measurable_pairing φ.1 hφ).comp measurable_fst).sub measurable_const
  set H : Ω × ℂ → ℝ≥0∞ := fun p =>
    S.indicator (fun _ => (1 : ℝ≥0∞)) (HarmonicBalls.campbellMarkedObs α₀ D (hC p.1) p.2) with hHdef
  have hH : Measurable H := (measurable_const.indicator hS).comp hobs
  have hg : Measurable ((Prod.snd ⁻¹' B).indicator H) := hH.indicator (measurable_snd hB)
  have hΨ : Measurable fun ω => (ρ ω B)⁻¹ *
      ∫⁻ z, (Prod.snd ⁻¹' B).indicator H (ω, z) ∂((ρ ω).restrict (closedBall (0 : ℂ) (N : ℝ))) :=
    ((Measure.measurable_measure.1 hρ B hB).inv).mul
      (measurable_lintegral_of_finite_family hκ hκfin hg)
  refine hΨ.aemeasurable.congr ?_
  filter_upwards [hρae] with ω hω
  rw [hω]
  congr 1
  calc ∫⁻ z, (Prod.snd ⁻¹' B).indicator H (ω, z) ∂((ρ ω).restrict (closedBall (0 : ℂ) (N : ℝ)))
      = ∫⁻ z, B.indicator (fun z => H (ω, z)) z ∂((ρ ω).restrict (closedBall (0 : ℂ) (N : ℝ))) := rfl
    _ = ∫⁻ z in B, H (ω, z) ∂((ρ ω).restrict (closedBall (0 : ℂ) (N : ℝ))) :=
        lintegral_indicator hB _
    _ = ∫⁻ z in B, H (ω, z) ∂(ρ ω) := by
        rw [Measure.restrict_restrict_of_subset hBN]
    _ = ∫⁻ z in B, S.indicator (fun _ => (1 : ℝ≥0∞))
          (HarmonicBalls.campbellMarkedObs α₀ D (hC ω) z) ∂(ρ ω) := rfl

end HarmonicBalls.S11w

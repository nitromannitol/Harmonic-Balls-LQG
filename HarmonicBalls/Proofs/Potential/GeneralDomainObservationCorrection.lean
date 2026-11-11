import HarmonicBalls.Proofs.Potential.GeneralDomainFiniteSourceCorrection
import HarmonicBalls.Proofs.Potential.GeneralDomainTransposedObservationIntegrability

/-!
# Transposed Green correction for general observation measures

The potential-theoretic construction uses work of Leonardo Bonanno. The
exceptional observers depend on the domain and source. These results do not
close a numbered result.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set InnerProductSpace Filter
open scoped ENNReal

/-- A single harmonic correction works at every observer for which the literal
transposed Green and Newton kernels are integrable and the source has no atom. -/
theorem exists_harmonic_generalDomain_transposed_correction_pointwise
    {V K : Set ℂ} (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    (hK : IsCompact K) (hKV : K ⊆ V) {ν : Measure ℂ} [IsFiniteMeasure ν]
    (hν : ν Kᶜ = 0) :
    ∃ H : ℂ → ℝ, HarmonicOnNhd H V ∧
      ∀ x ∈ V, ν {x} = 0 → Integrable (fun y => newtonKernel y x) ν →
        Integrable (fun y => greenFunction V y x) ν →
        (∫ y, greenFunction V y x ∂ν) = greenPotential univ ν x - H x := by
  classical
  have hae : ∀ᵐ y ∂ν, y ∈ K := by rw [ae_iff]; exact hν
  have hex : ∃ F : ℂ → ℂ → ℝ, Measurable (Function.uncurry F) ∧
      (∀ y ∈ K, ∀ x ∈ V, (greatestHarmonicMinorant V (newtonKernelEReal y) x).toReal = F y x) ∧
      (∀ L : Set ℂ, IsCompact L → L ⊆ V → ∃ C : ℝ, ∀ y ∈ K, ∀ x ∈ L, |F y x| ≤ C) := by
    by_cases hne : K.Nonempty
    · obtain ⟨z, hz⟩ := hne
      obtain ⟨δ, hδ, hδV⟩ := hK.exists_cthickening_subset_open hV hKV
      have h3 : cthickening (3 * (δ / 3)) K ⊆ V := by
        rw [show 3 * (δ / 3) = δ by ring]
        exact hδV
      have hbal : ∀ w : ℂ, (∀ y ∈ K, δ / 3 < ‖y - w‖) →
          ∫ y, regularizedNewtonKernel (δ / 3) y w ∂(0 : Measure ℂ) =
            (0 : ℝ) * regularizedNewtonKernel (δ / 3) z w := by intros; simp
      obtain ⟨F, hFm, hFag, hFb, -⟩ :=
        greenHarmonicCorrectionBalayageStep_holds V K 0 z 0 (δ / 3) hV hK
          inferInstance (by simp) hz (by positivity) h3 hbal
      exact ⟨F, hFm, hFag, hFb⟩
    · refine ⟨fun _ _ => 0, measurable_const, ?_, ?_⟩
      · intro y hy; exact (hne ⟨y, hy⟩).elim
      · intro L hL hLV; exact ⟨0, fun y hy => (hne ⟨y, hy⟩).elim⟩
  obtain ⟨F, hFm, hFag, hFb⟩ := hex
  let G : ℂ → ℂ → ℝ := fun y x => K.indicator (fun y => F y x) y
  have hG : ∀ y, HarmonicOnNhd (G y) V := by
    intro y
    by_cases hy : y ∈ K
    · have hh := harmonicOnNhd_greatestHarmonicMinorant_newtonKernel hV hVb (hKV hy)
      intro x hx
      apply (harmonicAt_congr_nhds ?_).1 (hh x hx)
      filter_upwards [hV.mem_nhds hx] with w hw
      simpa only [G, indicator_of_mem hy] using hFag y hy w hw
    · simpa only [G, indicator_of_notMem hy] using harmonicOnNhd_const (0 : ℝ)
  have hGm : Measurable (Function.uncurry G) := by
    have heq : Function.uncurry G = (K ×ˢ (univ : Set ℂ)).indicator (Function.uncurry F) := by
      funext p
      by_cases hp : p.1 ∈ K <;> simp [G, Function.uncurry, hp]
    rw [heq]
    exact hFm.indicator (hK.measurableSet.prod MeasurableSet.univ)
  have hcont : ContinuousOn (fun x => ∫ y, G y x ∂ν) V := by
    intro x hx
    apply ContinuousAt.continuousWithinAt
    obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.mp hV x hx
    have hsub : closedBall x (δ / 2) ⊆ V :=
      (closedBall_subset_ball (by linarith)).trans hδsub
    obtain ⟨C, hC⟩ := hFb _ (isCompact_closedBall x (δ / 2)) hsub
    apply tendsto_integral_filter_of_dominated_convergence (fun _ => max C 0)
    · exact Filter.Eventually.of_forall fun w => (hGm.comp (measurable_id.prodMk (measurable_const : Measurable (fun _ : ℂ => w)))).aestronglyMeasurable
    · filter_upwards [closedBall_mem_nhds x (by linarith : 0 < δ / 2)] with w hw
      filter_upwards [hae] with y hy
      simpa only [G, indicator_of_mem hy, Real.norm_eq_abs] using (hC y hy w hw).trans (le_max_left C 0)
    · exact integrable_const _
    · filter_upwards [hae] with y hy
      exact ((hG y x hx).1.continuousAt.tendsto)
  have hharm : HarmonicOnNhd (fun x => ∫ y, G y x ∂ν) V := by
    apply Section6.harmonicOnNhd_integral_of_circle_bounds hV hG hGm hcont
    intro c r hr hsub
    obtain ⟨C, hC⟩ := hFb _ (isCompact_sphere c r) (sphere_subset_closedBall.trans hsub)
    refine ⟨max C 0, ?_⟩
    intro y z hz
    by_cases hy : y ∈ K
    · simpa only [G, indicator_of_mem hy] using (hC y hy z hz).trans (le_max_left C 0)
    · simpa only [G, indicator_of_notMem hy, abs_zero] using le_max_right C 0
  refine ⟨fun x => ∫ y, G y x ∂ν, hharm, ?_⟩
  intro x hxV hx hi hgx
  have hne : ∀ᵐ y ∂ν, y ≠ x := by
    rw [ae_iff]; simpa using hx
  have heq : (fun y => greenFunction V y x) =ᵐ[ν] fun y => newtonKernel y x - G y x := by
    filter_upwards [hae, hne] with y hy hyx
    rw [greenFunction, ite_eq_left ⟨hKV hy, hxV, hyx⟩, hFag y hy x hxV]
    simp only [G, indicator_of_mem hy]
  have hgi : Integrable (fun y => G y x) ν := by
    have : (fun y => G y x) =ᵐ[ν] fun y => newtonKernel y x - greenFunction V y x := by
      filter_upwards [heq] with y hy
      linarith
    exact (hi.sub hgx).congr this.symm
  rw [integral_congr_ae heq, integral_sub hi hgi]
  congr 1
  simp only [greenPotential, greenFunction_univ_eq_newtonKernel, newtonKernel_comm]

/-- Local positive-power observation growth yields a source-dependent null set. -/
theorem exists_harmonic_generalDomain_transposed_correction_of_local_upper_growth
    {μ ν : Measure ℂ} [IsLocallyFiniteMeasure μ] [IsFiniteMeasure ν]
    (hup : ∀ R : ℝ, 0 < R → ∃ r₀ β : ℝ, 0 < r₀ ∧ 0 < β ∧
      ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R,
        μ (ball z r) ≤ ENNReal.ofReal (r ^ β))
    {V K : Set ℂ} (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    (hK : IsCompact K) (hKV : K ⊆ V) (hν : ν Kᶜ = 0) :
    ∃ H : ℂ → ℝ, HarmonicOnNhd H V ∧ ∀ᵐ x ∂μ.restrict V,
      Integrable (fun y => greenFunction V y x) ν ∧
      Integrable (fun y => newtonKernel y x) ν ∧ ν {x} = 0 ∧
      (∫ y, greenFunction V y x ∂ν) = greenPotential univ ν x - H x := by
  obtain ⟨H, hH, heq⟩ := exists_harmonic_generalDomain_transposed_correction_pointwise hV hVb hK hKV hν
  refine ⟨H, hH, ?_⟩
  filter_upwards [ae_restrict_of_ae (ae_transposedGreen_integrable_of_local_upper_growth_global hup hV hVb hK hν),
    ae_restrict_mem hV.measurableSet] with x hx hxV
  have hi : Integrable (fun y => newtonKernel y x) ν := by
    simpa only [newtonKernel_comm] using hx.2.1
  exact ⟨hx.1, hi, hx.2.2, heq x hxV hx.2.2 hi hx.1⟩

universe u

/-- I2 supplies a probability-one event uniformly in domains and sources;
the observation null set is allowed to depend on the domain and source. -/
theorem ae_lqg_exists_harmonic_generalDomain_transposed_correction
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
      (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ (V K : Set ℂ) (ν : Measure ℂ),
      IsOpen V → Bornology.IsBounded V → IsCompact K → K ⊆ V →
      ν Kᶜ = 0 → IsFiniteMeasure ν →
      ∃ H : ℂ → ℝ, HarmonicOnNhd H V ∧ ∀ᵐ x ∂(μ ω).restrict V,
        Integrable (fun y => greenFunction V y x) ν ∧
        Integrable (fun y => newtonKernel y x) ν ∧ ν {x} = 0 ∧
        (∫ y, greenFunction V y x ∂ν) = greenPotential univ ν x - H x := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_lqg_transposedGreen_integrable hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hω
  intro V K ν hV hVb hK hKV hν hf
  let : IsFiniteMeasure ν := hf
  obtain ⟨H, hH, heq⟩ := exists_harmonic_generalDomain_transposed_correction_pointwise hV hVb hK hKV hν
  refine ⟨H, hH, ?_⟩
  filter_upwards [ae_restrict_of_ae (hω V K ν hV hVb hK hKV hν hf),
    ae_restrict_mem hV.measurableSet] with x hx hxV
  have hi : Integrable (fun y => newtonKernel y x) ν := by
    simpa only [newtonKernel_comm] using hx.2.1
  exact ⟨hx.1, hi, hx.2.2, heq x hxV hx.2.2 hi hx.1⟩


end HarmonicBalls

import HarmonicBalls.Proofs.Potential.GeneralDomainGreenProductIntegrability
import HarmonicBalls.Proofs.Potential.FiniteSourceDiscCorrection
import HarmonicBalls.Proofs.Sec5.GeneralDomainInteriorGreen

/-!
# Integrated harmonic correction on a bounded domain

The potential-theoretic construction uses work of Leonardo Bonanno. This is
an analytic result, not closure of a numbered result.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set InnerProductSpace Filter

/-- A finite compactly concentrated source admits a harmonic correction. The
Green kernel is kept in its literal source-observer order. -/
theorem exists_harmonic_generalDomain_transposed_correction
    {V K : Set ℂ} (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    (hK : IsCompact K) (hKV : K ⊆ V) {ν : Measure ℂ} [IsFiniteMeasure ν]
    (hν : ν Kᶜ = 0) :
    ∃ H : ℂ → ℝ, HarmonicOnNhd H V ∧
      ∀ᵐ x ∂volume.restrict V,
        Integrable (fun y => newtonKernel y x) ν ∧
        Integrable (fun y => greenFunction V y x) ν ∧
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
  obtain ⟨r, hr⟩ := hVb.subset_ball (0 : ℂ)
  let R := max r 1
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hsub : V ⊆ ball (0 : ℂ) R := hr.trans (ball_subset_ball (le_max_left _ _))
  have hνR : ∀ᵐ y ∂ν, y ∈ closedBall (0 : ℂ) R :=
    hae.mono fun _ hy => ball_subset_closedBall (hsub (hKV hy))
  obtain ⟨_, _, r₀, hr₀, hg⟩ := volumeGrowth_volume R
  have hup : ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R,
      volume (ball z r) ≤ ENNReal.ofReal (r ^ (1 : ℝ)) := by
    intro r hr hrr z hz
    exact (hg r hr hrr z hz).2
  have hn := ae_newtonKernel_and_atom_of_upper (ν := ν) le_rfl hR hr₀
    (by norm_num : (0 : ℝ) < 1) hup (measure_ball_lt_top (μ := volume)).ne hνR
  have hn' := hn.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
  have hb := (generalDomain_green_integrable_product_volume hV hVb
    (hae.mono fun _ hy => hKV hy)).swap.prod_right_ae
  filter_upwards [hn', hb, ae_restrict_mem hV.measurableSet] with x hx hgx hxV
  have hi : Integrable (fun y => newtonKernel y x) ν := by
    simpa only [newtonKernel_comm] using hx.1
  have hgx' : Integrable (fun y => greenFunction V y x) ν := by
    simpa only [Function.comp_apply, Prod.swap_prod_mk] using hgx
  have hne : ∀ᵐ y ∂ν, y ≠ x := by
    rw [ae_iff]; simpa using hx.2
  have heq : (fun y => greenFunction V y x) =ᵐ[ν] fun y => newtonKernel y x - G y x := by
    filter_upwards [hae, hne] with y hy hyx
    rw [greenFunction, ite_eq_left ⟨hKV hy, hxV, hyx⟩, hFag y hy x hxV]
    simp only [G, indicator_of_mem hy]
  have hgi : Integrable (fun y => G y x) ν := by
    have : (fun y => G y x) =ᵐ[ν] fun y => newtonKernel y x - greenFunction V y x := by
      filter_upwards [heq] with y hy
      linarith
    exact (hi.sub hgx').congr this.symm
  refine ⟨hi, hgx', ?_⟩
  rw [integral_congr_ae heq, integral_sub hi hgi]
  congr 1
  simp only [greenPotential, greenFunction_univ_eq_newtonKernel, newtonKernel_comm]


end HarmonicBalls

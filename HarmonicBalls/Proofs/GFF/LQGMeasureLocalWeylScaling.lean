import HarmonicBalls.Proofs.GFF.LQGMeasureRandomWeylMeasurability

/-!
# Local Weyl scaling of the LQG measure on an open set

Let `U ⊆ ℂ` be open and let `f` be continuous on `U` only, as for `f = Q log |φ'|` with `φ` a
conformal map defined on `U` (Fact 2.1 IV). The local reweighted measure is
`(μ_h|_U).withDensity (e^{γ f})`, which depends only on the values of `f` on `U`.

On one almost sure event, simultaneously for every open set `U`, every function `f` continuous
on `U` and every continuous compactly supported test `φ` with `tsupport φ ⊆ U`, the
circle-average approximations of `h + f` tested against `φ` converge at all positive radii to the
integral of `φ` against the local reweighted measure. The proof multiplies `f` by a continuous
cutoff equal to one on a closed neighbourhood of `tsupport φ` with topological support in `U`,
applies Weyl scaling for globally continuous functions (Fact 2.1 III), and observes that, for
radii smaller than the size of that neighbourhood, neither the approximations tested against `φ`
nor the limit see the values of `f` outside it.

For a random function `F` continuous on `U` with `ω ↦ F ω z` measurable for `z ∈ U`, the local
reweighted random measure is measurable when `μ` is, and almost everywhere measurable for the
LQG measure in general. The proof exhausts `U` by compact sets.
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HarmonicBalls

/-- For a compact subset `K` of an open set `U ⊆ ℂ`, there is a cutoff `χ` with topological support
in `U`, equal to one on a closed neighbourhood `cthickening δ K` of `K`, such that `χ f` is
continuous on `ℂ` for every function `f` continuous on `U`. -/
theorem exists_cutoff_continuous_mul_of_continuousOn {U K : Set ℂ} (hU : IsOpen U)
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ δ > 0, ∃ χ : ℂ → ℝ, tsupport χ ⊆ U ∧ EqOn χ 1 (cthickening δ K) ∧
      ∀ f : ℂ → ℝ, ContinuousOn f U → Continuous fun z => χ z * f z := by
  obtain ⟨δ', hδ', hsub⟩ := hK.exists_cthickening_subset_open hU hKU
  have hcl : IsCompact (closure (thickening δ' K)) :=
    hK.cthickening.of_isClosed_subset isClosed_closure (closure_thickening_subset_cthickening δ' K)
  obtain ⟨χ, hχU, hχ1, -⟩ := exists_tsupport_one_of_isOpen_isClosed isOpen_thickening hcl
    isClosed_cthickening (cthickening_subset_thickening' hδ' (half_lt_self hδ') K)
  have hχU' : tsupport χ ⊆ U := hχU.trans ((thickening_subset_cthickening δ' K).trans hsub)
  refine ⟨δ' / 2, half_pos hδ', χ, hχU', hχ1, fun f hf => ?_⟩
  refine continuous_of_tsupport fun z hz => ?_
  have hzU : z ∈ U := hχU' (tsupport_mul_subset_left hz)
  exact χ.continuous.continuousAt.mul (hf.continuousAt (hU.mem_nhds hzU))

/-- Two measures with the same restriction to a measurable set `K` give the same integral to every
function vanishing outside `K`. -/
theorem integral_eq_of_restrict_eq {ν₁ ν₂ : Measure ℂ} {K : Set ℂ} (h : ν₁.restrict K = ν₂.restrict K)
    {φ : ℂ → ℝ} (hφ : ∀ z ∉ K, φ z = 0) :
    ∫ z, φ z ∂ν₁ = ∫ z, φ z ∂ν₂ := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hφ, h,
    setIntegral_eq_integral_of_forall_compl_eq_zero hφ]

/-- Restriction to a measurable set is a measurable operation on random measures. -/
theorem measurable_restrict_of_measurable {Ω : Type*} [MeasurableSpace Ω] {m : Ω → Measure ℂ}
    (hm : Measurable m) {s : Set ℂ} (hs : MeasurableSet s) :
    Measurable fun ω => (m ω).restrict s := by
  refine Measure.measurable_of_measurable_coe _ fun t ht => ?_
  simp_rw [Measure.restrict_apply ht]
  exact (Measure.measurable_coe (ht.inter hs)).comp hm

/-- Let `m` be a measurable random measure on `ℂ`, let `U` be open, and let `G ω` be continuous on
`U` for every `ω`, with `ω ↦ G ω z` measurable for every `z ∈ U`. Then the random measure
`ω ↦ ((m ω)|_U).withDensity (G ω)` is measurable. No finiteness of `m ω` is used. -/
theorem measurable_restrict_withDensity_ofReal_of_continuousOn {Ω : Type*} [MeasurableSpace Ω]
    {m : Ω → Measure ℂ} (hm : Measurable m) {U : Set ℂ} (hU : IsOpen U) {G : Ω → ℂ → ℝ}
    (hGc : ∀ ω, ContinuousOn (G ω) U) (hGm : ∀ z ∈ U, Measurable fun ω => G ω z) :
    Measurable fun ω => ((m ω).restrict U).withDensity fun z => ENNReal.ofReal (G ω z) := by
  obtain ⟨C, hCc, hCU, hCun, hCmono⟩ := hU.exists_iUnion_isClosed
  let K : ℕ → Set ℂ := fun n => C n ∩ closedBall 0 n
  have hKc : ∀ n, IsCompact (K n) := fun n => (isCompact_closedBall 0 (n : ℝ)).inter_left (hCc n)
  have hKm : ∀ n, MeasurableSet (K n) := fun n => (hKc n).isClosed.measurableSet
  have hKU : ∀ n, K n ⊆ U := fun n => inter_subset_left.trans (hCU n)
  have hKmono : Monotone K := fun a b hab =>
    inter_subset_inter (hCmono hab) (closedBall_subset_closedBall (by exact_mod_cast hab))
  have hKun : ⋃ n, K n = U := by
    refine Subset.antisymm (iUnion_subset hKU) fun z hz => ?_
    rw [← hCun] at hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    obtain ⟨j, hj⟩ := exists_nat_ge ‖z‖
    refine mem_iUnion.mpr ⟨max i j, hCmono (le_max_left i j) hi, ?_⟩
    rw [mem_closedBall, dist_zero_right]
    exact hj.trans (by exact_mod_cast le_max_right i j)
  have hcut : ∀ n, ∃ χ : ℂ → ℝ, tsupport χ ⊆ U ∧ EqOn χ 1 (K n) ∧
      ∀ f : ℂ → ℝ, ContinuousOn f U → Continuous fun z => χ z * f z := fun n => by
    obtain ⟨δ, -, χ, hχU, hχ1, hχf⟩ :=
      exists_cutoff_continuous_mul_of_continuousOn hU (hKc n) (hKU n)
    exact ⟨χ, hχU, hχ1.mono (self_subset_cthickening _), hχf⟩
  choose χ hχU hχ1 hχf using hcut
  have hpiece : ∀ n, Measurable fun ω =>
      ((m ω).restrict (K n)).withDensity fun z => ENNReal.ofReal (G ω z) := by
    intro n
    have heq : ∀ ω, (((m ω).restrict (K n)).withDensity fun z => ENNReal.ofReal (G ω z)) =
        ((m ω).restrict (K n)).withDensity fun z => ENNReal.ofReal (χ n z * G ω z) := fun ω =>
      withDensity_congr_ae (ae_restrict_of_forall_mem (hKm n) fun z hz => by
        simp [hχ1 n hz])
    simp_rw [heq]
    refine measurable_withDensity_of_continuous (g := fun ω z => ENNReal.ofReal (χ n z * G ω z))
      (measurable_restrict_of_measurable hm (hKm n))
      (fun ω => ENNReal.continuous_ofReal.comp (hχf n (G ω) (hGc ω))) fun z => ?_
    by_cases hz : z ∈ U
    · exact (measurable_const.mul (hGm z hz)).ennreal_ofReal
    · have h0 : χ n z = 0 := image_eq_zero_of_notMem_tsupport fun h => hz (hχU n h)
      simp only [h0, zero_mul]
      exact measurable_const
  refine Measure.measurable_of_measurable_coe _ fun t ht => ?_
  have hr : ∀ ω s, MeasurableSet s →
      ((m ω).restrict s).withDensity (fun z => ENNReal.ofReal (G ω z)) t =
        (m ω).withDensity (fun z => ENNReal.ofReal (G ω z)) (t ∩ s) := fun ω s hs => by
    rw [← restrict_withDensity hs, Measure.restrict_apply ht]
  have hlim : ∀ ω, ((m ω).restrict U).withDensity (fun z => ENNReal.ofReal (G ω z)) t =
      ⨆ n, ((m ω).restrict (K n)).withDensity (fun z => ENNReal.ofReal (G ω z)) t := by
    intro ω
    have hr' : ∀ n, ((m ω).restrict (K n)).withDensity (fun z => ENNReal.ofReal (G ω z)) t =
        (m ω).withDensity (fun z => ENNReal.ofReal (G ω z)) (t ∩ K n) := fun n =>
      hr ω _ (hKm n)
    rw [hr ω U hU.measurableSet]
    simp_rw [hr']
    rw [← hKun, inter_iUnion]
    exact Monotone.measure_iUnion fun a b hab => inter_subset_inter_right t (hKmono hab)
  simp_rw [hlim]
  exact Measurable.iSup fun n => (Measure.measurable_coe ht).comp (hpiece n)

/-- The local reweighted measure `((μ ω)|_U).withDensity (e^{γ F ω})` of a measurable random
measure `μ`, for a random function `F` continuous on the open set `U`, is measurable. -/
theorem measurable_restrict_withDensity_exp_of_continuousOn {Ω : Type*} [MeasurableSpace Ω]
    {μ : Ω → Measure ℂ} (hμ : Measurable μ) {U : Set ℂ} (hU : IsOpen U) (γ : ℝ)
    {F : Ω → ℂ → ℝ} (hFc : ∀ ω, ContinuousOn (F ω) U)
    (hFm : ∀ z ∈ U, Measurable fun ω => F ω z) :
    Measurable fun ω => ((μ ω).restrict U).withDensity fun z =>
      ENNReal.ofReal (Real.exp (γ * F ω z)) :=
  measurable_restrict_withDensity_ofReal_of_continuousOn hμ hU
    (fun ω => Real.continuous_exp.comp_continuousOn (continuousOn_const.mul (hFc ω)))
    fun z hz => (measurable_const.mul (hFm z hz)).exp

/-- For the LQG measure `μ_h` of a whole-plane field, an open set `U` and a random function `F`
continuous on `U`, the local reweighted random measure `((μ_h)|_U).withDensity (e^{γ F})` is almost
everywhere measurable. No measurability of `μ` is assumed. -/
theorem IsWholePlaneGFF.aemeasurable_restrict_withDensity_exp_lqgMeasure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc) {γ α : ℝ}
    {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ α hcirc μ) {U : Set ℂ} (hU : IsOpen U)
    {F : Ω → ℂ → ℝ} (hFc : ∀ ω, ContinuousOn (F ω) U)
    (hFm : ∀ z ∈ U, Measurable fun ω => F ω z) :
    AEMeasurable (fun ω => ((μ ω).restrict U).withDensity fun z =>
      ENNReal.ofReal (Real.exp (γ * F ω z))) P := by
  have hae := hh.aemeasurable_lqgMeasure hμ
  refine ⟨fun ω => ((hae.mk μ ω).restrict U).withDensity fun z =>
      ENNReal.ofReal (Real.exp (γ * F ω z)),
    measurable_restrict_withDensity_exp_of_continuousOn hae.measurable_mk hU γ hFc hFm, ?_⟩
  filter_upwards [hae.ae_eq_mk] with ω hω
  rw [hω]

/-- For a function `f` continuous on an open set `U` and a continuous compactly supported test `φ`
with `tsupport φ ⊆ U`, the integral of `φ` against the local reweighted measure
`(ν|_U).withDensity (e^{γ f})` is the ordinary integral `∫ φ e^{γ f} dν`. -/
theorem integral_restrict_withDensity_exp_of_continuousOn (ν : Measure ℂ) (γ : ℝ) {U : Set ℂ}
    (hU : IsOpen U) {f : ℂ → ℝ} (hf : ContinuousOn f U) {φ : ℂ → ℝ} (hφc : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) :
    ∫ z, φ z ∂((ν.restrict U).withDensity fun z => ENNReal.ofReal (Real.exp (γ * f z))) =
      ∫ z, φ z * Real.exp (γ * f z) ∂ν := by
  obtain ⟨δ, -, χ, -, hχ1, hχf⟩ := exists_cutoff_continuous_mul_of_continuousOn hU hφc hφU
  have hKm : MeasurableSet (tsupport φ) := (isClosed_tsupport φ).measurableSet
  have hφ0 : ∀ z ∉ tsupport φ, φ z = 0 := fun z hz => image_eq_zero_of_notMem_tsupport hz
  have hgf : ∀ z ∈ tsupport φ, χ z * f z = f z := fun z hz => by
    simp [hχ1 (self_subset_cthickening _ hz)]
  have h1 : ∫ z, φ z ∂((ν.restrict U).withDensity fun z => ENNReal.ofReal (Real.exp (γ * f z))) =
      ∫ z, φ z ∂(ν.withDensity fun z => ENNReal.ofReal (Real.exp (γ * (χ z * f z)))) := by
    refine integral_eq_of_restrict_eq ?_ hφ0
    rw [restrict_withDensity hKm, restrict_withDensity hKm, Measure.restrict_restrict hKm,
      inter_eq_left.mpr hφU]
    exact withDensity_congr_ae (ae_restrict_of_forall_mem hKm fun z hz => by simp [hgf z hz])
  rw [h1, Section6.integral_withDensity_exp ν γ _ φ (hχf f hf)]
  congr 1 with z
  by_cases hz : z ∈ tsupport φ
  · rw [hgf z hz]
  · simp [hφ0 z hz]

/-- **Local Weyl scaling at all positive radii.** For a whole-plane field `h = h^ℂ - α log |·|` with
`0 < γ < 2` and `α < Q`, almost surely, for every open set `U`, every function `f` continuous on
`U` and every continuous compactly supported test `φ` with `tsupport φ ⊆ U`, the circle-average
approximations of `h + f` tested against `φ` converge at all positive radii to the integral of `φ`
against the local reweighted measure `((μ_h)|_U).withDensity (e^{γ f})`. -/
theorem ae_tendsto_integral_lqgApprox_local_add_continuousOn
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc)
    {γ α : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hαQ : α < lqgQ γ)
    {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ α hcirc μ) :
    ∀ᵐ ω ∂P, ∀ U : Set ℂ, IsOpen U → ∀ f : ℂ → ℝ, ContinuousOn f U →
      ∀ φ : ℂ → ℝ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ U →
        Tendsto (fun s : ℝ =>
            ∫ z, φ z ∂(lqgApprox γ (addCircleAverage (fieldCircleAverage α (hcirc ω)) f) s))
          (𝓝[>] 0)
          (𝓝 (∫ z, φ z ∂(((μ ω).restrict U).withDensity fun z =>
            ENNReal.ofReal (Real.exp (γ * f z))))) := by
  filter_upwards [ae_tendsto_integral_lqgApprox_continuum_add_continuous hh hγ0 hγ2 hαQ hμ]
    with ω hconv U hU f hf φ hφ hφc hφU
  obtain ⟨δ, hδ, χ, -, hχ1, hχf⟩ := exists_cutoff_continuous_mul_of_continuousOn hU hφc hφU
  obtain ⟨g, hg, hgf⟩ : ∃ g : ℂ → ℝ, Continuous g ∧ EqOn g f (cthickening δ (tsupport φ)) :=
    ⟨fun z => χ z * f z, hχf f hf, fun z hz => by simp [hχ1 hz]⟩
  have hKm : MeasurableSet (tsupport φ) := (isClosed_tsupport φ).measurableSet
  have hφ0 : ∀ z ∉ tsupport φ, φ z = 0 := fun z hz => image_eq_zero_of_notMem_tsupport hz
  have hlim : ∫ z, φ z ∂(((μ ω).restrict U).withDensity fun z =>
        ENNReal.ofReal (Real.exp (γ * f z))) =
      ∫ z, φ z ∂((μ ω).withDensity fun z => ENNReal.ofReal (Real.exp (γ * g z))) := by
    refine integral_eq_of_restrict_eq ?_ hφ0
    rw [restrict_withDensity hKm, restrict_withDensity hKm, Measure.restrict_restrict hKm,
      inter_eq_left.mpr hφU]
    exact withDensity_congr_ae (ae_restrict_of_forall_mem hKm fun z hz => by
      simp [hgf (self_subset_cthickening _ hz)])
  rw [hlim]
  refine (hconv g hg φ hφ hφc).congr' ?_
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), s < δ :=
    (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds
  filter_upwards [hev, self_mem_nhdsWithin] with s hsδ hs0
  refine integral_eq_of_restrict_eq ?_ hφ0
  rw [lqgApprox, lqgApprox, restrict_withDensity hKm, restrict_withDensity hKm]
  refine withDensity_congr_ae (ae_restrict_of_forall_mem hKm fun z hz => ?_)
  have hca : Real.circleAverage g z s = Real.circleAverage f z s := by
    refine Real.circleAverage_congr_sphere fun w hw => hgf ?_
    refine mem_cthickening_of_dist_le w z δ _ hz ?_
    rw [mem_sphere, abs_of_pos hs0] at hw
    exact hw.le.trans hsδ.le
  simp only [addCircleAverage, hca]

/-- **Local Weyl scaling for a random shift continuous on an open set.** Let
`h = h^ℂ - α log |·|` be a whole-plane field with `0 < γ < 2` and `α < Q`, let `μ` be its LQG
measure, measurable as a random measure, let `U` be open, and let `F` be a random function
continuous on `U`, with `ω ↦ F ω z` measurable for `z ∈ U`. Then the local reweighted random measure
`((μ_h)|_U).withDensity (e^{γ F})` is measurable, and almost surely the circle-average
approximations of `h + F`, tested against every continuous compactly supported `φ` with
`tsupport φ ⊆ U`, converge to its integral at all positive radii. -/
theorem measurable_and_ae_tendsto_integral_lqgApprox_local_add_random
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc)
    {γ α : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hαQ : α < lqgQ γ)
    {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ α hcirc μ) (hμm : Measurable μ)
    {U : Set ℂ} (hU : IsOpen U) {F : Ω → ℂ → ℝ} (hFc : ∀ ω, ContinuousOn (F ω) U)
    (hFm : ∀ z ∈ U, Measurable fun ω => F ω z) :
    Measurable (fun ω => ((μ ω).restrict U).withDensity fun z =>
        ENNReal.ofReal (Real.exp (γ * F ω z))) ∧
      ∀ᵐ ω ∂P, ∀ φ : ℂ → ℝ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ U →
        Tendsto (fun s : ℝ =>
            ∫ z, φ z ∂(lqgApprox γ (addCircleAverage (fieldCircleAverage α (hcirc ω)) (F ω)) s))
          (𝓝[>] 0)
          (𝓝 (∫ z, φ z ∂(((μ ω).restrict U).withDensity fun z =>
            ENNReal.ofReal (Real.exp (γ * F ω z))))) :=
  ⟨measurable_restrict_withDensity_exp_of_continuousOn hμm hU γ hFc hFm,
    (ae_tendsto_integral_lqgApprox_local_add_continuousOn hh hγ0 hγ2 hαQ hμ).mono
      fun ω hω => hω U hU (F ω) (hFc ω)⟩

end HarmonicBalls

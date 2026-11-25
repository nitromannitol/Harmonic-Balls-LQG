import HarmonicBalls.Proofs.Potential.ReflectedRevuzIdentification
import HarmonicBalls.Proofs.Potential.LQGActualApproximantPower
import HarmonicBalls.Proofs.Sec11.SingularCompactNull
import HarmonicBalls.Proofs.Sec5.LQGApproxDecoder

/-!
# The Revuz measure of the LQG clock of reflected Brownian motion in a square

Let `K = closedSquare a L` and let `F x` be LQG clocks of reflected Brownian motion in `K` from
every start, for the field `h = h^ℂ - α₀ log |·|` with `0 < γ < 2`, `α₀ < Q`. Almost surely the
positive continuous additive functional `A` of reflected Brownian motion in the unit square with
`F x b s = μ_h(K) A(s / L², Ψ b)` (`exists_isUnitSquarePCAF_of_isLQGClock`) has Revuz measure the
normalized LQG measure `ν = μ_h(K)⁻¹ ((z - a)/L)_* (μ_h|_K)`
(`ae_exists_isUnitSquarePCAF_revuz_eq`). This is the clock identification in the proof of
Proposition 2.6: the clock is the time change by the additive functional whose Revuz measure is
the speed measure `μ_h|_K` (consultant note on target 12; Kigami, *Time changes of the Brownian
motion*, Mem. AMS 259 (2019), Section 6; Fukushima–Oshima–Takeda, Theorem 5.1.4).

The proof applies `unitSquareRevuzMeasure_eq_of_density_clocks` to the transported circle-average
approximations, which are clocks with the densities
`ρ_k(z) = L² μ_h(K)⁻¹ ε_k^{γ²/2} e^{γ h_{ε_k}(a + L z)}` (`transportedClockApprox_eq_integral`):

* they converge to `A` uniformly on `[0, 1]` in probability from every start, by the definition of
  the LQG clock;
* their expected occupation integrals are bounded uniformly, by the Green potential bound of
  reflected Brownian motion (`lintegral_windowOccupation_reflected_le`) and the uniform power ball
  bounds of the approximations (`IsWholePlaneGFF.ae_singular_approximant_ball_power_all_disks`);
* `ρ_k dz` on the unit square converges to `ν`, by the vague convergence of the approximations,
  the change of variables `z = (y - a)/L`, and the fact that `μ_h` does not charge the frontier of
  the fixed square (`IsWholePlaneGFF.ae_lqgMeasure_frontier_closedSquare_eq_zero_of_pos`).

With Kigami's theorem and the scaling (`reflectedLBMHeatKernel_of_identification`) this proves
Proposition 2.6 up to the strict positivity of the kernel
(`reflectedLBMHeatKernel_of_kigami_of_positivity`).
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Set Filter Topology MarkovProcess Metric
open scoped ENNReal NNReal

/-! ### The LQG measure does not charge the frontier of a fixed square -/

/-- **The LQG measure does not charge the frontier of a fixed square**, for every insertion
`α₀ < Q`, also when the frontier contains the insertion point. -/
theorem IsWholePlaneGFF.ae_lqgMeasure_frontier_closedSquare_eq_zero_of_pos {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {γ α₀ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : α₀ < lqgQ γ) {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) (a : ℂ)
    {L : ℝ} (hL : 0 < L) : ∀ᵐ ω ∂P, μ ω (frontier (closedSquare a L)) = 0 := by
  by_cases h0 : (0 : ℂ) ∈ frontier (closedSquare a L)
  swap
  · exact hh.ae_lqgMeasure_frontier_closedSquare_eq_zero_of_not_mem_zero hγ hγ2 hα hμ a hL.le h0
  have hcpt : IsCompact (closedSquare a L) := isCompact_closedSquare a L
  have hfr_sub : frontier (closedSquare a L) ⊆ closedSquare a L := by
    rw [hcpt.isClosed.frontier_eq]
    exact sdiff_subset
  have hfr_cpt : IsCompact (frontier (closedSquare a L)) :=
    hcpt.of_isClosed_subset isClosed_frontier hfr_sub
  have hfr_vol : volume (frontier (closedSquare a L)) = 0 :=
    measure_mono_null (frontier_closedSquare_subset_lines a hL.le)
      (measure_union_null (measure_union_null (measure_union_null (volume_setOf_re_eq_const _)
        (volume_setOf_re_eq_const _)) (volume_setOf_im_eq_const _)) (volume_setOf_im_eq_const _))
  have hn : ∀ n : ℕ, ∀ᵐ ω ∂P,
      μ ω (frontier (closedSquare a L) \ ball 0 (1 / ((n : ℝ) + 1))) = 0 := fun n =>
    hh.ae_lqgMeasure_eq_zero_of_isCompact_not_mem_zero hγ hγ2 hα hμ (hfr_cpt.diff isOpen_ball)
      (fun h => h.2 (mem_ball_self (by positivity))) (measure_mono_null sdiff_subset hfr_vol)
  filter_upwards [ae_all_iff.2 hn, ae_forall_closedSquare_volume_bounds hγ hγ2 hα hh hμ]
    with ω hnω hvol
  obtain ⟨-, -, c₁, c₂, α₁, α₂, -, hc₂, -, hα₂, -, hb⟩ := hvol a L hL
  have h0K : (0 : ℂ) ∈ closedSquare a L := hfr_sub h0
  have hle : ∀ r : ℝ, 0 < r → r ≤ L →
      μ ω (frontier (closedSquare a L)) ≤ ENNReal.ofReal (c₂ * r ^ α₂) := by
    intro r hr hrL
    obtain ⟨n, hn'⟩ := exists_nat_one_div_lt hr
    have hsub : frontier (closedSquare a L) ⊆
        (frontier (closedSquare a L) \ ball 0 (1 / ((n : ℝ) + 1))) ∪
          (ball 0 r ∩ closedSquare a L) := by
      intro z hz
      by_cases hzb : z ∈ ball (0 : ℂ) (1 / ((n : ℝ) + 1))
      · exact Or.inr ⟨ball_subset_ball hn'.le hzb, hfr_sub hz⟩
      · exact Or.inl ⟨hz, hzb⟩
    calc μ ω (frontier (closedSquare a L))
        ≤ μ ω (frontier (closedSquare a L) \ ball 0 (1 / ((n : ℝ) + 1))) +
            μ ω (ball 0 r ∩ closedSquare a L) :=
          (measure_mono hsub).trans (measure_union_le _ _)
      _ ≤ 0 + ENNReal.ofReal (c₂ * r ^ α₂) := add_le_add (hnω n).le (hb 0 h0K r hr hrL).2
      _ = ENNReal.ofReal (c₂ * r ^ α₂) := zero_add _
  have ht : Tendsto (fun s : ℝ => ENNReal.ofReal (c₂ * s ^ α₂)) (𝓝[>] 0) (𝓝 0) := by
    have h := ((Real.continuous_rpow_const hα₂.le).tendsto 0).const_mul c₂
    rw [Real.zero_rpow hα₂.ne', mul_zero] at h
    have h' := ENNReal.tendsto_ofReal (h.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ))))
    rwa [ENNReal.ofReal_zero] at h'
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      μ ω (frontier (closedSquare a L)) ≤ ENNReal.ofReal (c₂ * s ^ α₂) := by
    filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds hL).filter_mono nhdsWithin_le_nhds]
      with s hs hsL
    exact hle s hs hsL.le
  exact le_antisymm (ge_of_tendsto ht hev) zero_le

/-! ### Integrals over a set with null frontier against vaguely convergent measures -/

/-- **Integrals over a compact set with null frontier converge under vague convergence**: if
`m_k → μ` against continuous compactly supported functions, `K` is compact with
`μ(frontier K) = 0` and `F ≥ 0` is continuous, then `∫_K F dm_k → ∫_K F dμ`. -/
theorem tendsto_setLIntegral_of_tendsto_integral {μ : Measure ℂ} [IsLocallyFiniteMeasure μ]
    {m : ℕ → Measure ℂ} [∀ k, IsLocallyFiniteMeasure (m k)]
    (hm : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      Tendsto (fun k => ∫ z, f z ∂m k) atTop (𝓝 (∫ z, f z ∂μ)))
    {K : Set ℂ} (hK : IsCompact K) (hfr : μ (frontier K) = 0) {F : ℂ → ℝ} (hF : Continuous F)
    (hF0 : ∀ z, 0 ≤ F z) :
    Tendsto (fun k => ∫⁻ z in K, ENNReal.ofReal (F z) ∂m k) atTop
      (𝓝 (∫⁻ z in K, ENNReal.ofReal (F z) ∂μ)) := by
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hKc : (Kᶜ).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty, compl_empty_iff] at h
    exact noncompact_univ ℂ (h ▸ hK)
  -- the vague convergence for nonnegative test functions, in `ℝ≥0∞`
  have hconv : ∀ φ : ℂ → ℝ, Continuous φ → HasCompactSupport φ → (∀ z, 0 ≤ φ z) →
      Tendsto (fun k => ∫⁻ z, ENNReal.ofReal (φ z) ∂m k) atTop
        (𝓝 (∫⁻ z, ENNReal.ofReal (φ z) ∂μ)) := by
    intro φ hφ hφc hφ0
    have e : ∀ ν : Measure ℂ, IsLocallyFiniteMeasure ν →
        ∫⁻ z, ENNReal.ofReal (φ z) ∂ν = ENNReal.ofReal (∫ z, φ z ∂ν) := fun ν _ =>
      (ofReal_integral_eq_lintegral_ofReal (hφ.integrable_of_hasCompactSupport hφc)
        (ae_of_all _ hφ0)).symm
    simp_rw [e _ inferInstance]
    exact ENNReal.tendsto_ofReal (hm φ hφ hφc)
  -- outer cutoffs
  have hout : ∀ n : ℕ, ∃ φ : ℂ → ℝ, Continuous φ ∧ HasCompactSupport φ ∧
      (∀ z, 0 ≤ φ z ∧ φ z ≤ 1) ∧ (∀ z ∈ K, φ z = 1) ∧
      (∀ z, z ∉ cthickening (1 / ((n : ℝ) + 1)) K → φ z = 0) := fun n => by
    obtain ⟨φ, h1, h2, h3, h4, h5, -⟩ :=
      exists_cutoff_of_isCompact hK (show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity)
    exact ⟨φ, h1, h2, h3, h4, h5⟩
  choose φo hφoc hφos hφo01 hφo1 hφo0 using hout
  -- inner cutoffs
  set φi : ℕ → ℂ → ℝ := fun n z => min 1 (((n : ℝ) + 1) * infDist z Kᶜ) with hφi
  have hφic : ∀ n, Continuous (φi n) := fun n =>
    continuous_const.min (continuous_const.mul (continuous_infDist_pt _))
  have hφi0 : ∀ n z, z ∉ K → φi n z = 0 := fun n z hz => by
    simp only [hφi, infDist_zero_of_mem (show z ∈ Kᶜ from hz), mul_zero,
      min_eq_right zero_le_one]
  have hφis : ∀ n, HasCompactSupport (φi n) := fun n =>
    HasCompactSupport.intro hK fun z hz => hφi0 n z hz
  have hφi01 : ∀ n z, 0 ≤ φi n z ∧ φi n z ≤ 1 := fun n z =>
    ⟨le_min zero_le_one (mul_nonneg (by positivity) infDist_nonneg), min_le_left _ _⟩
  -- pointwise comparisons
  set Fi : ℂ → ℝ≥0∞ := K.indicator fun z => ENNReal.ofReal (F z) with hFi
  have hind : ∀ (ν : Measure ℂ), ∫⁻ z in K, ENNReal.ofReal (F z) ∂ν = ∫⁻ z, Fi z ∂ν := fun ν =>
    (lintegral_indicator hKm _).symm
  have hlow : ∀ n z, ENNReal.ofReal (F z * φi n z) ≤ Fi z := by
    intro n z
    by_cases hz : z ∈ K
    · rw [hFi, indicator_of_mem hz]
      exact ENNReal.ofReal_le_ofReal (mul_le_of_le_one_right (hF0 z) (hφi01 n z).2)
    · rw [hFi, indicator_of_notMem hz, hφi0 n z hz, mul_zero, ENNReal.ofReal_zero]
  have hup : ∀ n z, Fi z ≤ ENNReal.ofReal (F z * φo n z) := by
    intro n z
    by_cases hz : z ∈ K
    · rw [hFi, indicator_of_mem hz, hφo1 n z hz, mul_one]
    · rw [hFi, indicator_of_notMem hz]
      exact zero_le
  have hFiK : ∫⁻ z, Fi z ∂μ ≠ ⊤ := by
    rw [← hind]
    exact (hF.continuousOn.integrableOn_compact hK).lintegral_lt_top.ne
  -- limits of the cutoff integrals against `μ`
  have hC : IsCompact (cthickening (1 : ℝ) K) := hK.cthickening
  have hCm : MeasurableSet (cthickening (1 : ℝ) K) := isClosed_cthickening.measurableSet
  have hbound_fin : ∫⁻ z, (cthickening (1 : ℝ) K).indicator (fun z => ENNReal.ofReal (F z)) z ∂μ
      ≠ ⊤ := by
    rw [lintegral_indicator hCm]
    exact (hF.continuousOn.integrableOn_compact hC).lintegral_lt_top.ne
  have hφo_lim : Tendsto (fun n => ∫⁻ z, ENNReal.ofReal (F z * φo n z) ∂μ) atTop
      (𝓝 (∫⁻ z, Fi z ∂μ)) := by
    refine tendsto_lintegral_of_dominated_convergence
      ((cthickening (1 : ℝ) K).indicator fun z => ENNReal.ofReal (F z))
      (fun n => ENNReal.measurable_ofReal.comp (hF.mul (hφoc n)).measurable)
      (fun n => ae_of_all _ fun z => ?_) hbound_fin (ae_of_all _ fun z => ?_)
    · beta_reduce
      by_cases hz : z ∈ cthickening (1 / ((n : ℝ) + 1)) K
      · have hz1 : z ∈ cthickening (1 : ℝ) K := by
          refine cthickening_mono ?_ K hz
          rw [div_le_one (by positivity)]
          linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
        rw [indicator_of_mem hz1]
        exact ENNReal.ofReal_le_ofReal (mul_le_of_le_one_right (hF0 z) (hφo01 n z).2)
      · rw [hφo0 n z hz, mul_zero, ENNReal.ofReal_zero]
        exact zero_le
    · by_cases hz : z ∈ K
      · have he : (fun n => ENNReal.ofReal (F z * φo n z)) = fun _ => Fi z := by
          funext n
          rw [hφo1 n z hz, mul_one, hFi, indicator_of_mem hz]
        rw [he]
        exact tendsto_const_nhds
      · have hcl : z ∉ closure K := by rwa [hK.isClosed.closure_eq]
        rw [closure_eq_iInter_cthickening] at hcl
        simp only [mem_iInter, not_forall] at hcl
        obtain ⟨δ, hδ, hzδ⟩ := hcl
        obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
        rw [hFi, indicator_of_notMem hz]
        refine tendsto_atTop_of_eventually_const (i₀ := N) fun n hn => ?_
        have hNn : (N : ℝ) + 1 ≤ (n : ℝ) + 1 := by
          have := (Nat.cast_le (α := ℝ)).2 hn
          linarith
        have hz' : z ∉ cthickening (1 / ((n : ℝ) + 1)) K := fun h =>
          hzδ (cthickening_mono ((one_div_le_one_div_of_le (by positivity) hNn).trans hN.le) K h)
        rw [hφo0 n z hz', mul_zero, ENNReal.ofReal_zero]
  have hint_eq : ∫⁻ z, (interior K).indicator (fun z => ENNReal.ofReal (F z)) z ∂μ =
      ∫⁻ z, Fi z ∂μ := by
    rw [lintegral_indicator isOpen_interior.measurableSet, ← hind]
    refine setLIntegral_congr ?_
    rw [ae_eq_set]
    refine ⟨by rw [sdiff_eq_empty.2 interior_subset, measure_empty], ?_⟩
    rw [← hK.isClosed.frontier_eq, hfr]
  have hφi_lim : Tendsto (fun n => ∫⁻ z, ENNReal.ofReal (F z * φi n z) ∂μ) atTop
      (𝓝 (∫⁻ z, Fi z ∂μ)) := by
    rw [← hint_eq]
    refine tendsto_lintegral_of_dominated_convergence Fi
      (fun n => ENNReal.measurable_ofReal.comp (hF.mul (hφic n)).measurable)
      (fun n => ae_of_all _ fun z => hlow n z) hFiK (ae_of_all _ fun z => ?_)
    by_cases hz : z ∈ interior K
    · have hd : 0 < infDist z Kᶜ := by
        refine (infDist_pos_iff_notMem_closure hKc).1 ?_
        rw [closure_compl]
        exact fun h => h hz
      obtain ⟨N, hN⟩ := exists_nat_one_div_lt hd
      rw [indicator_of_mem hz]
      refine tendsto_atTop_of_eventually_const (i₀ := N) fun n hn => ?_
      have hNn : (N : ℝ) + 1 ≤ (n : ℝ) + 1 := by
        have := (Nat.cast_le (α := ℝ)).2 hn
        linarith
      have h1 : 1 ≤ ((n : ℝ) + 1) * infDist z Kᶜ := by
        rw [div_lt_iff₀ (by positivity)] at hN
        nlinarith
      simp only [hφi, min_eq_left h1, mul_one]
    · have hd : infDist z Kᶜ = 0 := by
        refine (mem_closure_iff_infDist_zero hKc).1 ?_
        rw [closure_compl]
        exact hz
      rw [indicator_of_notMem hz]
      have he : (fun n => ENNReal.ofReal (F z * φi n z)) = fun _ => 0 := by
        funext n
        simp only [hφi, hd, mul_zero, min_eq_right zero_le_one, ENNReal.ofReal_zero]
      rw [he]
      exact tendsto_const_nhds
  -- the sandwich
  rw [hind μ]
  simp_rw [hind]
  refine tendsto_of_le_liminf_of_limsup_le ?_ ?_
  · refine le_of_tendsto' hφi_lim fun n => ?_
    calc ∫⁻ z, ENNReal.ofReal (F z * φi n z) ∂μ
        = liminf (fun k => ∫⁻ z, ENNReal.ofReal (F z * φi n z) ∂m k) atTop :=
          ((hconv _ (hF.mul (hφic n)) (hφis n).mul_left
            fun z => mul_nonneg (hF0 z) (hφi01 n z).1).liminf_eq).symm
      _ ≤ liminf (fun k => ∫⁻ z, Fi z ∂m k) atTop :=
          liminf_le_liminf (Eventually.of_forall fun k => lintegral_mono (hlow n))
  · refine ge_of_tendsto' hφo_lim fun n => ?_
    calc limsup (fun k => ∫⁻ z, Fi z ∂m k) atTop
        ≤ limsup (fun k => ∫⁻ z, ENNReal.ofReal (F z * φo n z) ∂m k) atTop :=
          limsup_le_limsup (Eventually.of_forall fun k => lintegral_mono (hup n))
      _ = ∫⁻ z, ENNReal.ofReal (F z * φo n z) ∂μ :=
          (hconv _ (hF.mul (hφoc n)) (hφos n).mul_left
            fun z => mul_nonneg (hF0 z) (hφo01 n z).1).limsup_eq

end HarmonicBalls

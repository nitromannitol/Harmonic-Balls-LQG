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

/-! ### The change of variables to the unit square -/

theorem map_unitSquareChart_volume (a : ℂ) {L : ℝ} (hL : 0 < L) :
    (volume : Measure ℂ).map (fun y : ℂ => (y - a) / (L : ℂ)) =
      ENNReal.ofReal (L ^ 2) • volume := by
  have h1 : (fun y : ℂ => (y - a) / (L : ℂ)) = (fun z : ℂ => L⁻¹ • z) ∘ (fun y => y - a) := by
    funext y
    simp only [Function.comp_apply, Complex.real_smul, Complex.ofReal_inv]
    rw [div_eq_inv_mul]
  rw [h1, ← Measure.map_map (measurable_const_smul _) (measurable_sub_const a),
    map_sub_right_eq_self, Measure.map_addHaar_smul volume (inv_ne_zero hL.ne'),
    Complex.finrank_real_complex]
  congr 1
  rw [inv_pow, inv_inv, abs_of_pos (by positivity)]

/-- **Change of variables from a square to the unit square.** -/
theorem setLIntegral_closedSquare_comp_unitSquareChart (a : ℂ) {L : ℝ} (hL : 0 < L)
    {G : ℂ → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ y in closedSquare a L, G ((y - a) / (L : ℂ)) =
      ENNReal.ofReal (L ^ 2) * ∫⁻ z in closedSquare 0 1, G z := by
  have hK0 : MeasurableSet (closedSquare (0 : ℂ) 1) :=
    (isCompact_closedSquare 0 1).isClosed.measurableSet
  rw [← unitSquareChart_preimage_closedSquare hL,
    ← setLIntegral_map hK0 hG (measurable_unitSquareChart a L), map_unitSquareChart_volume a hL,
    Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul]

/-! ### The approximating clocks read in the unit square -/

/-- The density `ε^{γ²/2} e^{γ h_ε(z)}` of the circle-average approximation of the LQG measure. -/
noncomputable def lqgApproxDensity (γ : ℝ) (hε : ℝ → ℂ → ℝ) (ε : ℝ) (z : ℂ) : ℝ :=
  ε ^ (γ ^ 2 / 2) * Real.exp (γ * hε ε z)

theorem lqgApprox_eq_withDensity (γ : ℝ) (hε : ℝ → ℂ → ℝ) (ε : ℝ) :
    lqgApprox γ hε ε = volume.withDensity fun z => ENNReal.ofReal (lqgApproxDensity γ hε ε z) :=
  rfl

/-- The density of the approximating clocks of the square `closedSquare a L`, read in the unit
square and divided by `M`: `ρ_k(z) = L² M⁻¹ ε_k^{γ²/2} e^{γ h_{ε_k}(a + L z)}`. -/
noncomputable def unitSquareClockDensity (γ : ℝ) (hε : ℝ → ℂ → ℝ) (a : ℂ) (L M : ℝ) (k : ℕ)
    (z : ℂ) : ℝ :=
  L ^ 2 / M * lqgApproxDensity γ hε (dyadicScale k) (a + (L : ℂ) * z)

theorem continuous_unitSquareClockDensity {γ : ℝ} {hε : ℝ → ℂ → ℝ} {k : ℕ}
    (hc : Continuous (hε (dyadicScale k))) (a : ℂ) (L M : ℝ) :
    Continuous (unitSquareClockDensity γ hε a L M k) := by
  have h : Continuous fun z : ℂ => hε (dyadicScale k) (a + (L : ℂ) * z) :=
    hc.comp (continuous_const.add (continuous_const.mul continuous_id))
  exact continuous_const.mul (continuous_const.mul (Real.continuous_exp.comp
    (continuous_const.mul h)))

theorem unitSquareClockDensity_nonneg {γ : ℝ} {hε : ℝ → ℂ → ℝ} (a : ℂ) (L : ℝ) {M : ℝ}
    (hM : 0 < M) (k : ℕ) (z : ℂ) : 0 ≤ unitSquareClockDensity γ hε a L M k z :=
  mul_nonneg (div_nonneg (sq_nonneg L) hM.le)
    (mul_nonneg (Real.rpow_nonneg (dyadicScale_pos k).le _) (Real.exp_pos _).le)

/-- **The transported approximate clocks have the densities `ρ_k`**:
`ã_k(b, u) = ∫_0^u ρ_k(b_s) ds`. -/
theorem transportedClockApprox_eq_integral (γ : ℝ) (hε : ℝ → ℂ → ℝ) (a : ℂ) {L : ℝ} (hL : 0 < L)
    (M : ℝ) (k : ℕ) (b : ContinuousPath ℂ) (u : ℝ≥0) :
    transportedClockApprox γ hε a hL M k b u =
      ∫ s in (0 : ℝ)..u, unitSquareClockDensity γ hε a L M k (b s.toNNReal) := by
  have hL2 : (0 : ℝ) < L ^ 2 := by positivity
  have hcoe : (((L ^ 2).toNNReal * u : ℝ≥0) : ℝ) = L ^ 2 * u := by
    rw [NNReal.coe_mul, Real.coe_toNNReal _ hL2.le]
  unfold transportedClockApprox lqgClockApprox
  rw [hcoe]
  have hsub := intervalIntegral.integral_comp_mul_left (a := 0) (b := (u : ℝ))
    (f := fun t : ℝ => dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * hε (dyadicScale k)
      ((unitSquarePathChart a hL).symm b t.toNNReal))) hL2.ne'
  rw [mul_zero, smul_eq_mul] at hsub
  have hpt : ∀ s ∈ uIcc (0 : ℝ) u, (dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * hε (dyadicScale k)
      ((unitSquarePathChart a hL).symm b (L ^ 2 * s).toNNReal))) * (L ^ 2 / M) =
      unitSquareClockDensity γ hε a L M k (b s.toNNReal) := by
    intro s _
    have h := eq_add_mul_unitSquarePathChart a hL ((unitSquarePathChart a hL).symm b) s.toNNReal
    rw [Homeomorph.apply_symm_apply] at h
    rw [Real.toNNReal_mul hL2.le, h, unitSquareClockDensity, lqgApproxDensity]
    ring
  have key : ∀ X : ℝ, X / M = (L ^ 2)⁻¹ * X * (L ^ 2 / M) := fun X => by
    rw [div_eq_mul_inv, div_eq_mul_inv, mul_comm (L ^ 2)⁻¹ X, mul_assoc,
      ← mul_assoc (L ^ 2)⁻¹, inv_mul_cancel₀ hL2.ne', one_mul]
  rw [← intervalIntegral.integral_congr hpt, intervalIntegral.integral_mul_const, hsub]
  exact key _

theorem transportedClockApprox_nonneg (γ : ℝ) (hε : ℝ → ℂ → ℝ) (a : ℂ) {L : ℝ} (hL : 0 < L)
    {M : ℝ} (hM : 0 < M) (k : ℕ) (b : ContinuousPath ℂ) (u : ℝ≥0) :
    0 ≤ transportedClockApprox γ hε a hL M k b u := by
  rw [transportedClockApprox_eq_integral]
  exact intervalIntegral.integral_nonneg u.coe_nonneg fun s _ =>
    unitSquareClockDensity_nonneg a L hM k _

/-- **Integrals against the clock densities on the unit square** are integrals against the
approximations of the LQG measure on the square:
`∫_{K₀} G ρ_k dz = M⁻¹ ∫_K G((y - a)/L) dμ_k(y)`. -/
theorem setLIntegral_mul_unitSquareClockDensity {γ : ℝ} {hε : ℝ → ℂ → ℝ} (a : ℂ) {L M : ℝ}
    (hL : 0 < L) (hM : 0 < M) (k : ℕ) (hc : Continuous (hε (dyadicScale k))) {G : ℂ → ℝ≥0∞}
    (hG : Measurable G) :
    ∫⁻ z in closedSquare 0 1, G z * ENNReal.ofReal (unitSquareClockDensity γ hε a L M k z) =
      ENNReal.ofReal (1 / M) *
        ∫⁻ y in closedSquare a L, G ((y - a) / (L : ℂ)) ∂lqgApprox γ hε (dyadicScale k) := by
  have hdm : Measurable fun y => ENNReal.ofReal (lqgApproxDensity γ hε (dyadicScale k) y) :=
    ENNReal.measurable_ofReal.comp (continuous_const.mul (Real.continuous_exp.comp
      (continuous_const.mul hc))).measurable
  have hρm : Measurable fun z => ENNReal.ofReal (unitSquareClockDensity γ hε a L M k z) :=
    ENNReal.measurable_ofReal.comp (continuous_unitSquareClockDensity hc a L M).measurable
  have hχ := measurable_unitSquareChart a L
  have hGχ : Measurable fun y => G ((y - a) / (L : ℂ)) := hG.comp hχ
  have hKm : MeasurableSet (closedSquare a L) := (isCompact_closedSquare a L).isClosed.measurableSet
  have hcv := setLIntegral_closedSquare_comp_unitSquareChart a hL
    (show Measurable fun z => G z * ENNReal.ofReal (unitSquareClockDensity γ hε a L M k z) from
      hG.mul hρm)
  beta_reduce at hcv
  have hL2 : ENNReal.ofReal (L ^ 2) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    positivity
  have hL2' : ENNReal.ofReal (L ^ 2) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hρχ : ∀ y : ℂ, unitSquareClockDensity γ hε a L M k ((y - a) / (L : ℂ)) =
      L ^ 2 / M * lqgApproxDensity γ hε (dyadicScale k) y := by
    intro y
    have hL' : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hL.ne'
    have : a + (L : ℂ) * ((y - a) / (L : ℂ)) = y := by
      field_simp
      ring
    rw [unitSquareClockDensity, this]
  have hsolve : ∫⁻ z in closedSquare 0 1, G z *
      ENNReal.ofReal (unitSquareClockDensity γ hε a L M k z) =
      (ENNReal.ofReal (L ^ 2))⁻¹ * ∫⁻ y in closedSquare a L, G ((y - a) / (L : ℂ)) *
        ENNReal.ofReal (unitSquareClockDensity γ hε a L M k ((y - a) / (L : ℂ))) := by
    rw [hcv, ← mul_assoc, ENNReal.inv_mul_cancel hL2 hL2', one_mul]
  have hright : ∫⁻ y in closedSquare a L, G ((y - a) / (L : ℂ)) ∂lqgApprox γ hε (dyadicScale k) =
      ∫⁻ y in closedSquare a L, ENNReal.ofReal (lqgApproxDensity γ hε (dyadicScale k) y) *
        G ((y - a) / (L : ℂ)) := by
    have h := lintegral_withDensity_eq_lintegral_mul ((volume : Measure ℂ).restrict (closedSquare a L))
      hdm hGχ
    rw [lqgApprox_eq_withDensity, restrict_withDensity hKm]
    exact h
  rw [hsolve, hright]
  have hmul : ∀ y, G ((y - a) / (L : ℂ)) *
      ENNReal.ofReal (unitSquareClockDensity γ hε a L M k ((y - a) / (L : ℂ))) =
      ENNReal.ofReal (L ^ 2 / M) * (ENNReal.ofReal (lqgApproxDensity γ hε (dyadicScale k) y) *
        G ((y - a) / (L : ℂ))) := by
    intro y
    rw [hρχ, ENNReal.ofReal_mul (div_nonneg (sq_nonneg L) hM.le)]
    ring
  simp_rw [hmul]
  rw [lintegral_const_mul _ (show Measurable fun y =>
    ENNReal.ofReal (lqgApproxDensity γ hε (dyadicScale k) y) * G ((y - a) / (L : ℂ)) from
      hdm.mul hGχ), ← mul_assoc]
  congr 1
  rw [show L ^ 2 / M = L ^ 2 * (1 / M) by ring, ENNReal.ofReal_mul (sq_nonneg L), ← mul_assoc,
    ENNReal.inv_mul_cancel hL2 hL2', one_mul]

/-- The measure `ρ_k dz` on the unit square, on a measurable set `E`, is `M⁻¹ μ_k(K ∩ χ⁻¹ E)`. -/
theorem withDensity_unitSquareClockDensity_apply {γ : ℝ} {hε : ℝ → ℂ → ℝ} (a : ℂ) {L M : ℝ}
    (hL : 0 < L) (hM : 0 < M) (k : ℕ) (hc : Continuous (hε (dyadicScale k))) {E : Set ℂ}
    (hE : MeasurableSet E) :
    ((volume.restrict (closedSquare 0 1)).withDensity fun z =>
        ENNReal.ofReal (unitSquareClockDensity γ hε a L M k z)) E =
      ENNReal.ofReal (1 / M) * lqgApprox γ hε (dyadicScale k)
        ((fun y : ℂ => (y - a) / (L : ℂ)) ⁻¹' E ∩ closedSquare a L) := by
  have hKm : MeasurableSet (closedSquare a L) := (isCompact_closedSquare a L).isClosed.measurableSet
  have hpre : MeasurableSet ((fun y : ℂ => (y - a) / (L : ℂ)) ⁻¹' E) :=
    measurable_unitSquareChart a L hE
  rw [withDensity_apply _ hE, ← lintegral_indicator hE]
  have h1 : ∀ z, E.indicator (fun z => ENNReal.ofReal (unitSquareClockDensity γ hε a L M k z)) z =
      E.indicator 1 z * ENNReal.ofReal (unitSquareClockDensity γ hε a L M k z) := fun z => by
    by_cases hz : z ∈ E <;> simp [hz]
  simp_rw [h1]
  rw [setLIntegral_mul_unitSquareClockDensity a hL hM k hc (measurable_one.indicator hE)]
  congr 1
  have h2 : ∀ y, E.indicator 1 ((y - a) / (L : ℂ)) =
      ((fun y : ℂ => (y - a) / (L : ℂ)) ⁻¹' E).indicator (1 : ℂ → ℝ≥0∞) y := fun y => by
    by_cases hy : (y - a) / (L : ℂ) ∈ E <;> simp [hy]
  simp_rw [h2]
  rw [lintegral_indicator_one hpre, Measure.restrict_apply hpre]

/-! ### The Green bound -/

/-- **Uniform Green bound for the clock densities**: if the approximations of the LQG measure
have uniform power ball bounds on discs centred in `B̄(0, R) ⊇ K` and uniformly bounded mass on
`K`, then the expected occupation integrals of `ρ_k` from every start in the unit square are
bounded uniformly in `k`. -/
theorem exists_green_bound_unitSquareClockDensity {γ : ℝ} {hε : ℝ → ℂ → ℝ} (a : ℂ) {L M : ℝ}
    (hL : 0 < L) (hM : 0 < M) (hc : ∀ k, Continuous (hε (dyadicScale k)))
    {C β r₀ R m₀ : ℝ} (hC : 0 < C) (hβ : 0 < β) (hr₀ : 0 < r₀) (hm₀ : 0 ≤ m₀)
    (hKR : closedSquare a L ⊆ closedBall 0 R)
    (hball : ∀ k : ℕ, ∀ z : ℂ, ‖z‖ ≤ R → ∀ s : ℝ, 0 < s → s ≤ r₀ →
      lqgApprox γ hε (dyadicScale k) (ball z s) ≤ ENNReal.ofReal (C * s ^ β))
    (hmass : ∀ k : ℕ, lqgApprox γ hε (dyadicScale k) (closedSquare a L) ≤ ENNReal.ofReal m₀) :
    ∃ U : ℝ≥0∞, U ≠ ⊤ ∧ ∀ k, ∀ y ∈ closedSquare 0 1,
      ∫⁻ b, windowOccupation (fun z => ENNReal.ofReal (unitSquareClockDensity γ hε a L M k z)) b
        ∂(reflectedPlanarBrownianMotion 0 1 y) ≤ U := by
  set θ : ℝ := min (β / 4) 1 with hθ
  have hθ0 : 0 < θ := lt_min (by positivity) one_pos
  have hθ1 : θ ≤ 1 := min_le_right _ _
  have hθβ : 2 * θ < β := by
    have := min_le_left (β / 4) 1
    linarith
  set m : ℝ := m₀ / M with hmdef
  have hm : 0 ≤ m := div_nonneg hm₀ hM.le
  set A : ℝ := C / M * (4 * L) ^ β + m * (4 * L / r₀) ^ β with hAdef
  have hA : 0 ≤ A := by positivity
  set ν : ℕ → Measure ℂ := fun k => (volume.restrict (closedSquare 0 1)).withDensity fun z =>
    ENNReal.ofReal (unitSquareClockDensity γ hε a L M k z) with hν
  have hνuniv : ∀ k, ν k univ ≤ ENNReal.ofReal m := by
    intro k
    rw [hν, withDensity_unitSquareClockDensity_apply a hL hM k (hc k) MeasurableSet.univ,
      preimage_univ, univ_inter, hmdef, div_eq_mul_inv m₀ M, ENNReal.ofReal_mul hm₀, mul_comm,
      one_div]
    exact mul_le_mul' (hmass k) le_rfl
  have hνball : ∀ k, ∀ z : ℂ, ∀ ρ : ℝ, 0 < ρ → ν k (closedBall z ρ) ≤ ENNReal.ofReal (A * ρ ^ β) := by
    intro k z ρ hρ
    by_cases hsmall : 4 * L * ρ ≤ r₀
    · rw [hν, withDensity_unitSquareClockDensity_apply a hL hM k (hc k) measurableSet_closedBall]
      have hsub : (fun y : ℂ => (y - a) / (L : ℂ)) ⁻¹' closedBall z ρ ∩ closedSquare a L ⊆
          ball (a + (L : ℂ) * z) (L * (2 * ρ)) ∩ closedSquare a L := by
        intro y hy
        refine ⟨?_, hy.2⟩
        rw [← unitSquareChart_preimage_ball hL]
        exact closedBall_subset_ball (by linarith) hy.1
      have hbd : lqgApprox γ hε (dyadicScale k)
          ((fun y : ℂ => (y - a) / (L : ℂ)) ⁻¹' closedBall z ρ ∩ closedSquare a L) ≤
          ENNReal.ofReal (C * (4 * L * ρ) ^ β) := by
        refine (measure_mono hsub).trans ?_
        rcases (ball (a + (L : ℂ) * z) (L * (2 * ρ)) ∩ closedSquare a L).eq_empty_or_nonempty
          with he | ⟨y₀, hy₀b, hy₀K⟩
        · rw [he, measure_empty]
          exact zero_le
        · have hy₀R : ‖y₀‖ ≤ R := by simpa using hKR hy₀K
          have hsub' : ball (a + (L : ℂ) * z) (L * (2 * ρ)) ∩ closedSquare a L ⊆
              ball y₀ (4 * L * ρ) := by
            intro y hy
            rw [mem_ball] at hy₀b ⊢
            have := hy.1
            rw [mem_ball] at this
            calc dist y y₀ ≤ dist y (a + (L : ℂ) * z) + dist y₀ (a + (L : ℂ) * z) :=
                  dist_triangle_right _ _ _
              _ < L * (2 * ρ) + L * (2 * ρ) := add_lt_add this hy₀b
              _ = 4 * L * ρ := by ring
          exact (measure_mono hsub').trans (hball k y₀ hy₀R _ (by positivity) hsmall)
      calc ENNReal.ofReal (1 / M) * lqgApprox γ hε (dyadicScale k)
            ((fun y : ℂ => (y - a) / (L : ℂ)) ⁻¹' closedBall z ρ ∩ closedSquare a L)
          ≤ ENNReal.ofReal (1 / M) * ENNReal.ofReal (C * (4 * L * ρ) ^ β) := mul_le_mul' le_rfl hbd
        _ = ENNReal.ofReal (C / M * (4 * L) ^ β * ρ ^ β) := by
            rw [← ENNReal.ofReal_mul (by positivity), Real.mul_rpow (by positivity) hρ.le]
            congr 1
            ring
        _ ≤ ENNReal.ofReal (A * ρ ^ β) := by
            refine ENNReal.ofReal_le_ofReal ?_
            rw [hAdef, add_mul]
            exact le_add_of_nonneg_right (by positivity)
    · have hbig : 1 ≤ (4 * L / r₀) ^ β * ρ ^ β := by
        rw [← Real.mul_rpow (by positivity) hρ.le]
        refine Real.one_le_rpow ?_ hβ.le
        rw [div_mul_eq_mul_div, le_div_iff₀ hr₀, one_mul]
        linarith
      calc ν k (closedBall z ρ) ≤ ν k univ := measure_mono (subset_univ _)
        _ ≤ ENNReal.ofReal m := hνuniv k
        _ ≤ ENNReal.ofReal (A * ρ ^ β) := by
            refine ENNReal.ofReal_le_ofReal ?_
            rw [hAdef, add_mul]
            refine le_add_of_nonneg_of_le (by positivity) ?_
            calc m = m * 1 := (mul_one m).symm
              _ ≤ m * ((4 * L / r₀) ^ β * ρ ^ β) := mul_le_mul_of_nonneg_left hbig hm
              _ = m * (4 * L / r₀) ^ β * ρ ^ β := by ring
  refine ⟨(2 * ENNReal.ofReal (Real.sqrt 2) * foldLatticeSum) ^ 2 *
      ENNReal.ofReal ((2 * Real.pi)⁻¹ * 2 ^ θ * (1 / θ)) *
        ENNReal.ofReal (m + A * (2 * θ / (β - 2 * θ))), ?_, fun k y hy => ?_⟩
  · refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.pow_ne_top (ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top) foldLatticeSum_lt_top.ne))
      ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top
  · exact lintegral_windowOccupation_reflected_le
      (ENNReal.measurable_ofReal.comp (continuous_unitSquareClockDensity (hc k) a L M).measurable)
      hθ0 hθ1 hθβ hm hA (hνuniv k) (hνball k) hy

/-! ### Convergence of the transported clocks -/

/-- **The transported approximate clocks converge to the unit-square clock**, uniformly on `[0, 1]`
in probability, from every start of the unit square. -/
theorem tendsto_transportedClock_sub_of_isLQGClock {γ : ℝ} {hε : ℝ → ℂ → ℝ} {a : ℂ} {L M : ℝ}
    (hL : 0 < L) (hM : 0 < M) {F : ℂ → ContinuousPath ℂ → ℝ≥0 → ℝ}
    (hF : ∀ x ∈ closedSquare a L, IsLQGClock (reflectedPlanarBrownianMotion a L) γ hε x (F x))
    {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hFA : ∀ x ∈ closedSquare a L, ∀ᵐ b ∂(reflectedPlanarBrownianMotion a L x), ∀ s : ℝ≥0,
      F x b s = M * (A (s / (L ^ 2).toNNReal) (unitSquarePathChart a hL b) : ℝ))
    {x' : ℂ} (hx' : x' ∈ closedSquare 0 1) {η : ℝ} (hη : 0 < η) :
    Tendsto (fun k => reflectedPlanarBrownianMotion 0 1 x'
      {b | ∃ t : ℝ≥0, t ≤ 1 ∧
        η ≤ |((transportedClockApprox γ hε a hL M k b t).toNNReal : ℝ) - (A t b : ℝ)|})
      atTop (𝓝 0) := by
  have hL' : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hL.ne'
  set x : ℂ := a + (L : ℂ) * x' with hx
  have hχx : (x - a) / (L : ℂ) = x' := by
    rw [hx]
    field_simp
    ring
  have hxK : x ∈ closedSquare a L := by
    have h := unitSquareChart_preimage_closedSquare (a := a) hL
    rw [← h, mem_preimage, hχx]
    exact hx'
  have hT := tendstoClockInMeasure_transported hL hM (hF x hxK)
  rw [hχx] at hT
  have hGA : ∀ᵐ b' ∂(reflectedPlanarBrownianMotion 0 1 x'), ∀ u : ℝ≥0,
      F x ((unitSquarePathChart a hL).symm b') ((L ^ 2).toNNReal * u) / M = (A u b' : ℝ) := by
    rw [← hχx, ← reflectedPlanarBrownianMotion_map_unitSquarePathChart a hL x,
      (unitSquarePathChart a hL).measurableEmbedding.ae_map_iff]
    filter_upwards [hFA x hxK] with b hb u
    rw [Homeomorph.symm_apply_apply, hb,
      mul_div_cancel_left₀ u (Real.toNNReal_pos.2 (by positivity)).ne']
    exact mul_div_cancel_left₀ _ hM.ne'
  have hN : reflectedPlanarBrownianMotion 0 1 x' {b' | ¬ ∀ u : ℝ≥0,
      F x ((unitSquarePathChart a hL).symm b') ((L ^ 2).toNNReal * u) / M = (A u b' : ℝ)} = 0 :=
    ae_iff.1 hGA
  have hsub : ∀ k, {b : ContinuousPath ℂ | ∃ t : ℝ≥0, t ≤ 1 ∧
      η ≤ |((transportedClockApprox γ hε a hL M k b t).toNNReal : ℝ) - (A t b : ℝ)|} ⊆
      {b | ∃ t ≤ (1 : ℝ≥0), η ≤ |transportedClockApprox γ hε a hL M k b t -
        F x ((unitSquarePathChart a hL).symm b) ((L ^ 2).toNNReal * t) / M|} ∪
      {b' | ¬ ∀ u : ℝ≥0,
        F x ((unitSquarePathChart a hL).symm b') ((L ^ 2).toNNReal * u) / M = (A u b' : ℝ)} := by
    intro k b hb
    obtain ⟨t, ht, h⟩ := hb
    by_cases hbN : ∀ u : ℝ≥0,
        F x ((unitSquarePathChart a hL).symm b) ((L ^ 2).toNNReal * u) / M = (A u b : ℝ)
    · left
      refine ⟨t, ht, ?_⟩
      rwa [Real.coe_toNNReal _ (transportedClockApprox_nonneg γ hε a hL hM k b t), ← hbN t] at h
    · right
      exact hbN
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (h := fun k => reflectedPlanarBrownianMotion 0 1 x' {b | ∃ t ≤ (1 : ℝ≥0),
      η ≤ |transportedClockApprox γ hε a hL M k b t -
        F x ((unitSquarePathChart a hL).symm b) ((L ^ 2).toNNReal * t) / M|} + 0)
    ?_ (fun k => zero_le) (fun k => ?_)
  · simp only [add_zero]
    exact hT 1 η hη
  · rw [← hN]
    exact (measure_mono (hsub k)).trans (measure_union_le _ _)

/-! ### The Revuz measure of the LQG clock -/

/-- **Clock identification for Proposition 2.6.** For `0 < γ < 2`, `α₀ < Q` and LQG clocks `F` of
reflected Brownian motion in `K = closedSquare a L` from every start, almost surely the positive
continuous additive functional `A` of reflected Brownian motion in the unit square with
`F x b s = μ_h(K) A(s / L², Ψ b)` has Revuz measure the normalized LQG measure of `K` carried to
the unit square. -/
theorem ae_exists_isUnitSquarePCAF_revuz_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc)
    {γ α₀ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ) {μ : Ω → Measure ℂ}
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) (a : ℂ) {L : ℝ} (hL : 0 < L)
    {F : Ω → ℂ → ContinuousPath ℂ → ℝ≥0 → ℝ}
    (hF : ∀ᵐ ω ∂P, ∀ x ∈ closedSquare a L,
      IsLQGClock (reflectedPlanarBrownianMotion a L) γ (fieldCircleAverage α₀ (hcirc ω)) x
        (F ω x)) :
    ∀ᵐ ω ∂P, ∃ A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0, IsUnitSquarePCAF A ∧
      unitSquareRevuzMeasure A = unitSquareNormalizedMeasure (μ ω) a L ∧
      ∀ x ∈ closedSquare a L, ∀ᵐ b ∂(reflectedPlanarBrownianMotion a L x), ∀ s : ℝ≥0,
        F ω x b s = (μ ω (closedSquare a L)).toReal *
          (A (s / (L ^ 2).toNNReal) (unitSquarePathChart a hL b) : ℝ) := by
  have hcont : ∀ᵐ ω ∂P, ∀ k : ℕ, Continuous (fieldCircleAverage α₀ (hcirc ω) (dyadicScale k)) :=
    ae_all_iff.2 fun k => hh.ae_continuous_fieldCircleAverage α₀ (dyadicScale_pos k)
  obtain ⟨R, hKR⟩ : ∃ R, closedSquare a L ⊆ closedBall (0 : ℂ) R :=
    (isCompact_closedSquare a L).isBounded.subset_closedBall 0
  filter_upwards [hF, hcont, hμ, ae_forall_closedSquare_volume_bounds hγ hγ2 hα hh hμ,
    ae_forall_closedSquare_kigamiVolumeBounds hγ hγ2 hα hh hμ,
    hh.ae_singular_approximant_ball_power_all_disks hγ hγ2 hα,
    hh.ae_lqgMeasure_frontier_closedSquare_eq_zero_of_pos hγ hγ2 hα hμ a hL]
    with ω hFω hcω hlim hvol hkig hballω hfr
  have hlim' : IsLQGLimit γ (fieldCircleAverage α₀ (hcirc ω)) (μ ω) := hlim
  have := hlim'.isLocallyFiniteMeasure
  obtain ⟨hKpos, hKfin, -⟩ := hvol a L hL
  have hM : 0 < (μ ω (closedSquare a L)).toReal := ENNReal.toReal_pos hKpos.ne' hKfin.ne
  obtain ⟨A, hA, hFA⟩ := exists_isUnitSquarePCAF_of_isLQGClock hcω hL hM hFω
  refine ⟨A, hA, ?_, hFA⟩
  obtain ⟨hprob, -⟩ := hkig a L hL
  have hloc : ∀ k, IsLocallyFiniteMeasure
      (lqgApprox γ (fieldCircleAverage α₀ (hcirc ω)) (dyadicScale k)) := fun k =>
    MassFunctionalDerived.isLocallyFiniteMeasure_lqgApprox γ (hcω k)
  obtain ⟨C, β, r₀, hC, hβ, hr₀, hb⟩ := hballω R
  -- uniform mass of the approximations on the square
  obtain ⟨m₀, hm₀, hmass⟩ : ∃ m₀ : ℝ, 0 ≤ m₀ ∧ ∀ k,
      lqgApprox γ (fieldCircleAverage α₀ (hcirc ω)) (dyadicScale k) (closedSquare a L) ≤
        ENNReal.ofReal m₀ := by
    obtain ⟨φ, hφc, hφs, hφ01, hφ1, -, -⟩ := exists_cutoff_of_isCompact (isCompact_closedSquare a L)
      one_pos
    have hφconv := hlim'.tendsto_integral φ hφc hφs
    obtain ⟨B, hB⟩ := isBounded_iff_forall_norm_le.1 (Metric.isBounded_range_of_tendsto _ hφconv)
    refine ⟨max B 0, le_max_right _ _, fun k => ?_⟩
    have hKm : MeasurableSet (closedSquare a L) :=
      (isCompact_closedSquare a L).isClosed.measurableSet
    calc lqgApprox γ (fieldCircleAverage α₀ (hcirc ω)) (dyadicScale k) (closedSquare a L)
        = ∫⁻ y, (closedSquare a L).indicator 1 y
            ∂lqgApprox γ (fieldCircleAverage α₀ (hcirc ω)) (dyadicScale k) :=
          (lintegral_indicator_one hKm).symm
      _ ≤ ∫⁻ y, ENNReal.ofReal (φ y)
            ∂lqgApprox γ (fieldCircleAverage α₀ (hcirc ω)) (dyadicScale k) := by
          refine lintegral_mono fun y => ?_
          by_cases hy : y ∈ closedSquare a L
          · rw [indicator_of_mem hy, Pi.one_apply, hφ1 y hy, ENNReal.ofReal_one]
          · rw [indicator_of_notMem hy]
            exact zero_le
      _ = ENNReal.ofReal (∫ y, φ y
            ∂lqgApprox γ (fieldCircleAverage α₀ (hcirc ω)) (dyadicScale k)) :=
          (ofReal_integral_eq_lintegral_ofReal (hφc.integrable_of_hasCompactSupport hφs)
            (ae_of_all _ fun y => (hφ01 y).1)).symm
      _ ≤ ENNReal.ofReal (max B 0) := by
          refine ENNReal.ofReal_le_ofReal ((le_abs_self _).trans ?_)
          rw [← Real.norm_eq_abs]
          exact (hB _ ⟨k, rfl⟩).trans (le_max_left _ _)
  obtain ⟨U, hU, hgreen⟩ := exists_green_bound_unitSquareClockDensity a hL hM hcω hC hβ hr₀ hm₀
    hKR hb hmass
  have : IsFiniteMeasure (unitSquareNormalizedMeasure (μ ω) a L) := inferInstance
  refine unitSquareRevuzMeasure_eq_of_density_clocks hA
    (ρ := unitSquareClockDensity γ (fieldCircleAverage α₀ (hcirc ω)) a L
      (μ ω (closedSquare a L)).toReal)
    (fun k => continuous_unitSquareClockDensity (hcω k) a L _)
    (fun k z => unitSquareClockDensity_nonneg a L hM k z)
    (c := fun k t b => (transportedClockApprox γ (fieldCircleAverage α₀ (hcirc ω)) a hL
      (μ ω (closedSquare a L)).toReal k b t).toNNReal)
    (fun k t b => ?_) (fun x hx η hη => tendsto_transportedClock_sub_of_isLQGClock hL hM hFω hFA hx hη)
    hU hgreen ?_
  · rw [Real.coe_toNNReal _ (transportedClockApprox_nonneg _ _ a hL hM k b t),
      transportedClockApprox_eq_integral]
  · intro f hf hfc hf0
    have hfm : Measurable fun z => ENNReal.ofReal (f z) := ENNReal.measurable_ofReal.comp hf.measurable
    have e1 : ∀ k, ∫⁻ z in closedSquare 0 1, ENNReal.ofReal (f z) *
        ENNReal.ofReal (unitSquareClockDensity γ (fieldCircleAverage α₀ (hcirc ω)) a L
          (μ ω (closedSquare a L)).toReal k z) =
        ENNReal.ofReal (1 / (μ ω (closedSquare a L)).toReal) *
          ∫⁻ y in closedSquare a L, ENNReal.ofReal (f ((y - a) / (L : ℂ)))
            ∂lqgApprox γ (fieldCircleAverage α₀ (hcirc ω)) (dyadicScale k) := fun k =>
      setLIntegral_mul_unitSquareClockDensity a hL hM k (hcω k) hfm
    simp_rw [e1]
    have e2 : ∫⁻ z, ENNReal.ofReal (f z) ∂unitSquareNormalizedMeasure (μ ω) a L =
        ENNReal.ofReal (1 / (μ ω (closedSquare a L)).toReal) *
          ∫⁻ y in closedSquare a L, ENNReal.ofReal (f ((y - a) / (L : ℂ))) ∂μ ω := by
      rw [unitSquareNormalizedMeasure, lintegral_smul_measure,
        lintegral_map hfm (measurable_unitSquareChart a L), smul_eq_mul]
      congr 1
      rw [one_div, ENNReal.ofReal_inv_of_pos hM, ENNReal.ofReal_toReal hKfin.ne]
    rw [e2]
    refine ENNReal.Tendsto.const_mul ?_ (Or.inr ENNReal.ofReal_ne_top)
    exact tendsto_setLIntegral_of_tendsto_integral
      (fun g hg hgc => hlim'.tendsto_integral g hg hgc) (isCompact_closedSquare a L) hfr
      (hf.comp ((continuous_id.sub continuous_const).div_const _)) (fun y => hf0 _)

/-- **Proposition 2.6 from Kigami's theorem and the positivity of the kernel.** For `0 < γ < 2`,
`α₀ < Q` and LQG clocks `F` of reflected Brownian motion in `K = closedSquare a L` from every
start, given Kigami's Theorem 13.1 (`kigamiHeatKernelContinuityCited`) and that every jointly
continuous heat kernel of a time change of reflected Brownian motion in the unit square by a
positive continuous additive functional with Revuz measure the normalized LQG measure is strictly
positive, almost surely the heat kernel of reflected Liouville Brownian motion in `K` with respect
to `μ_h` exists, is jointly continuous and strictly positive on `(0, ∞) × K × K`. The clock
identification is `ae_exists_isUnitSquarePCAF_revuz_eq`. -/
theorem reflectedLBMHeatKernel_of_kigami_of_positivity (hKig : kigamiHeatKernelContinuityCited)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} {γ α₀ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : α₀ < lqgQ γ) (hh : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    {a : ℂ} {L : ℝ} (hL : 0 < L) (F : Ω → ℂ → ContinuousPath ℂ → ℝ≥0 → ℝ)
    (hF : ∀ᵐ ω ∂P, ∀ x ∈ closedSquare a L,
      IsLQGClock (reflectedPlanarBrownianMotion a L) γ (fieldCircleAverage α₀ (hcirc ω)) x
        (F ω x))
    (hpos : ∀ᵐ ω ∂P, ∀ (A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0) (p' : ℝ → ℂ → ℂ → ℝ),
      IsUnitSquarePCAF A → unitSquareRevuzMeasure A = unitSquareNormalizedMeasure (μ ω) a L →
      IsLBMHeatKernel (reflectedPlanarBrownianMotion 0 1) (fun _ b t => (A t b : ℝ))
        (closedSquare 0 1) (unitSquareNormalizedMeasure (μ ω) a L) p' →
      ContinuousOn (fun s : ℝ × ℂ × ℂ => p' s.1 s.2.1 s.2.2)
        (Ioi 0 ×ˢ closedSquare 0 1 ×ˢ closedSquare 0 1) →
      ∀ t : ℝ, 0 < t → ∀ x ∈ closedSquare 0 1, ∀ y ∈ closedSquare 0 1, 0 < p' t x y) :
    ∀ᵐ ω ∂P, ∃ p : ℝ → ℂ → ℂ → ℝ,
      IsLBMHeatKernel (reflectedPlanarBrownianMotion a L) (F ω) (closedSquare a L) (μ ω) p ∧
      ContinuousOn (fun s : ℝ × ℂ × ℂ => p s.1 s.2.1 s.2.2)
        (Ioi 0 ×ˢ closedSquare a L ×ˢ closedSquare a L) ∧
      ∀ t : ℝ, 0 < t → ∀ x ∈ closedSquare a L, ∀ y ∈ closedSquare a L, 0 < p t x y :=
  reflectedLBMHeatKernel_of_identification hKig hγ hγ2 hα hh hμ hL F
    (ae_exists_isUnitSquarePCAF_revuz_eq hh hγ hγ2 hα hμ a hL hF) hpos

end HarmonicBalls

import HarmonicBalls.Proofs.Potential.LQGClockExpectationConvergence
import HarmonicBalls.Proofs.Potential.LQGClockExitQuenchedUniformIntegrability
import HarmonicBalls.Proofs.Potential.LBMExpectedClockExit
import HarmonicBalls.Proofs.Potential.LQGClockTimeChangeReduction

/-!
# Comparison of expected Liouville exit times from nested domains

Let `O ⊆ D` be smooth bounded domains and `F` an LQG clock from `x ∈ O` that is almost surely a
time-change clock. The exit time of Liouville Brownian motion from `D` is the clock value
`F(τ_D)`, which splits as `F(τ_O) + (F(τ_D) - F(τ_O))`. The clock approximations of the second
term are `∫_{τ_O}^{τ_D}` of the approximating densities, whose expectations are differences of
the Green integrals of `D` and of `O`. By Fatou's lemma along a subsequence on which the
approximations converge almost surely, the expected exit time from `D` is at most the expected
exit time from `O` plus the difference of the limits of the Green integrals. Hence an exact
identity for `D` gives the lower bound for `O`.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Real Set Filter Topology
open scoped ENNReal NNReal
namespace HarmonicBalls

/-- For nested smooth bounded domains `O ⊆ D`, the expected exit time of Liouville Brownian
motion from `D` is at most the expected exit time from `O` plus the difference of the limits of
the Green integrals of the approximating measures. -/
theorem expectedLBMExitTime_le_add_sub_of_subset {γ : ℝ} {hε : ℝ → ℂ → ℝ}
    (hεc : ∀ k : ℕ, Continuous (hε (dyadicScale k))) {O D : Set ℂ}
    (hO : IsSmoothBoundedOpen O) (hD : IsSmoothBoundedOpen D) (hOD : O ⊆ D) {x : ℂ}
    (hx : x ∈ O) {F : ContinuousPath ℂ → ℝ≥0 → ℝ}
    (hclock : IsLQGClock planarBrownianMotion γ hε x F)
    (hF : ∀ᵐ b ∂(planarBrownianMotion x), IsTimeChangeClock (F b)) {a c : ℝ≥0∞}
    (ha : Tendsto (fun k : ℕ => ∫⁻ z, ENNReal.ofReal (2 * greenFunction D x z) *
      ENNReal.ofReal (dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * hε (dyadicScale k) z)))
      atTop (𝓝 a))
    (hc : Tendsto (fun k : ℕ => ∫⁻ z, ENNReal.ofReal (2 * greenFunction O x z) *
      ENNReal.ofReal (dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * hε (dyadicScale k) z)))
      atTop (𝓝 c))
    (hcfin : c ≠ ⊤) :
    expectedLBMExitTime F D x ≤ expectedLBMExitTime F O x + (a - c) := by
  have hDo : IsOpen D := GreenGeneral.isOpen_of_isSmoothBoundedOpen hD
  have hOo : IsOpen O := GreenGeneral.isOpen_of_isSmoothBoundedOpen hO
  have hxD : x ∈ D := hOD hx
  let μ := planarBrownianMotion x
  let JD : ℕ → ContinuousPath ℂ → ℝ := fun k b =>
    lqgClockApprox γ hε (dyadicScale k) b (ContinuousPath.exitTime D b).toNNReal
  let JO : ℕ → ContinuousPath ℂ → ℝ := fun k b =>
    lqgClockApprox γ hε (dyadicScale k) b (ContinuousPath.exitTime O b).toNNReal
  have hJDm (k : ℕ) : Measurable (JD k) := measurable_lqgClockApprox_exit hDo k (hεc k)
  have hJOm (k : ℕ) : Measurable (JO k) := measurable_lqgClockApprox_exit hOo k (hεc k)
  have hJO0 (k : ℕ) (b : ContinuousPath ℂ) : 0 ≤ JO k b :=
    intervalIntegral.integral_nonneg_of_forall (NNReal.coe_nonneg _) fun _ =>
      mul_nonneg (Real.rpow_nonneg (dyadicScale_pos k).le _) (Real.exp_pos _).le
  have hfinD : ∀ᵐ b ∂μ, ContinuousPath.exitTime D b ≠ ⊤ :=
    (Section6.ae_planarBrownian_exitTime_bounded_lt_top x hD.1).mono fun _ h => h.ne
  have hfinO : ∀ᵐ b ∂μ, ContinuousPath.exitTime O b ≠ ⊤ :=
    (Section6.ae_planarBrownian_exitTime_bounded_lt_top x hO.1).mono fun _ h => h.ne
  have hnn : ∀ᵐ b ∂μ, (ContinuousPath.exitTime O b).toNNReal ≤
      (ContinuousPath.exitTime D b).toNNReal := by
    filter_upwards [hfinD] with b hb
    exact ENNReal.toNNReal_mono hb (ContinuousPath.exitTime_mono hOD b)
  have hJle : ∀ᵐ b ∂μ, ∀ k, JO k b ≤ JD k b := by
    filter_upwards [hnn] with b hb k
    exact monotone_lqgClockApprox (dyadicScale_pos k) (hεc k) b hb
  -- the clock values at the exit times
  have hval (U : Set ℂ) (hU : IsOpen U) (hUb : Bornology.IsBounded U) :
      ∀ᵐ b ∂μ, (lbmExitTime F U b).toReal = F b (ContinuousPath.exitTime U b).toNNReal ∧
        0 ≤ F b (ContinuousPath.exitTime U b).toNNReal := by
    filter_upwards [hF, Section6.ae_planarBrownian_exitTime_bounded_lt_top x hUb] with b hb hτ
    have h0 : 0 ≤ F b (ContinuousPath.exitTime U b).toNNReal := by
      rw [← hb.map_zero]
      exact hb.strictMono.monotone zero_le
    refine ⟨?_, h0⟩
    rw [lbmExitTime_eq_clockValue hU hb hτ.ne, ENNReal.coe_toReal, Real.coe_toNNReal _ h0]
  -- convergence in probability and a common almost surely convergent subsequence
  have hconvD : TendstoInMeasure μ JD atTop (fun b => (lbmExitTime F D b).toReal) := by
    apply tendstoInMeasure_iff_dist.mpr
    intro η hη
    simpa only [JD, Real.dist_eq] using
      hclock.tendsto_measure_clockApprox_lbmExitTime hDo hD.1 hF hη
  have hconvO : TendstoInMeasure μ JO atTop (fun b => (lbmExitTime F O b).toReal) := by
    apply tendstoInMeasure_iff_dist.mpr
    intro η hη
    simpa only [JO, Real.dist_eq] using
      hclock.tendsto_measure_clockApprox_lbmExitTime hOo hO.1 hF hη
  obtain ⟨n1, hn1, hn1ae⟩ := hconvD.exists_seq_tendsto_ae
  obtain ⟨n2, hn2, hn2ae⟩ := (hconvO.comp hn1.tendsto_atTop).exists_seq_tendsto_ae
  let n : ℕ → ℕ := fun j => n1 (n2 j)
  have hn : StrictMono n := hn1.comp hn2
  let fO : ContinuousPath ℂ → ℝ≥0∞ := fun b => liminf (fun j => ENNReal.ofReal (JO (n j) b)) atTop
  let fΔ : ContinuousPath ℂ → ℝ≥0∞ := fun b =>
    liminf (fun j => ENNReal.ofReal (JD (n j) b - JO (n j) b)) atTop
  have hfOm : Measurable fO := Measurable.liminf fun j => (hJOm (n j)).ennreal_ofReal
  have hfΔm : Measurable fΔ :=
    Measurable.liminf fun j => ((hJDm (n j)).sub (hJOm (n j))).ennreal_ofReal
  have hpt : ∀ᵐ b ∂μ, fO b = ENNReal.ofReal (F b (ContinuousPath.exitTime O b).toNNReal) ∧
      ENNReal.ofReal (F b (ContinuousPath.exitTime D b).toNNReal) = fO b + fΔ b := by
    filter_upwards [hn1ae, hn2ae, hval D hDo hD.1, hval O hOo hO.1, hF, hnn] with b hbD hbO hvD hvO
      hb hle
    have hD' : Tendsto (fun j => JD (n j) b) atTop
        (𝓝 (F b (ContinuousPath.exitTime D b).toNNReal)) := by
      rw [← hvD.1]
      exact hbD.comp hn2.tendsto_atTop
    have hO' : Tendsto (fun j => JO (n j) b) atTop
        (𝓝 (F b (ContinuousPath.exitTime O b).toNNReal)) := by
      rw [← hvO.1]
      exact hbO
    have hfO : fO b = ENNReal.ofReal (F b (ContinuousPath.exitTime O b).toNNReal) :=
      (ENNReal.tendsto_ofReal hO').liminf_eq
    have hfΔ : fΔ b = ENNReal.ofReal (F b (ContinuousPath.exitTime D b).toNNReal -
        F b (ContinuousPath.exitTime O b).toNNReal) :=
      (ENNReal.tendsto_ofReal (hD'.sub hO')).liminf_eq
    refine ⟨hfO, ?_⟩
    rw [hfO, hfΔ, ← ENNReal.ofReal_add hvO.2 (sub_nonneg.mpr (hb.strictMono.monotone hle)),
      add_sub_cancel]
  -- the expected exit times
  have hUD : expectedLBMExitTime F D x = ∫⁻ b, fO b ∂μ + ∫⁻ b, fΔ b ∂μ := by
    rw [expectedLBMExitTime_eq_lintegral_clockValue F D x hDo hD.1 hF,
      ← lintegral_add_left hfOm]
    exact lintegral_congr_ae (hpt.mono fun _ h => h.2)
  have hUO : expectedLBMExitTime F O x = ∫⁻ b, fO b ∂μ := by
    rw [expectedLBMExitTime_eq_lintegral_clockValue F O x hOo hO.1 hF]
    exact lintegral_congr_ae (hpt.mono fun _ h => h.1.symm)
  -- the expected increments are differences of Green integrals
  let GD : ℕ → ℝ≥0∞ := fun k => ∫⁻ z, ENNReal.ofReal (2 * greenFunction D x z) *
    ENNReal.ofReal (dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * hε (dyadicScale k) z))
  let GO : ℕ → ℝ≥0∞ := fun k => ∫⁻ z, ENNReal.ofReal (2 * greenFunction O x z) *
    ENNReal.ofReal (dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * hε (dyadicScale k) z))
  have hGD (k : ℕ) : (∫⁻ b, ENNReal.ofReal (JD k b) ∂μ) = GD k :=
    (GreenOccupation.lintegral_lqgClockApprox_exit_eq_occupation_and_green hD hxD γ
      (dyadicScale k) (dyadicScale_pos k) hε (hεc k)).2
  have hGO (k : ℕ) : (∫⁻ b, ENNReal.ofReal (JO k b) ∂μ) = GO k :=
    (GreenOccupation.lintegral_lqgClockApprox_exit_eq_occupation_and_green hO hx γ
      (dyadicScale k) (dyadicScale_pos k) hε (hεc k)).2
  have hinc (k : ℕ) (hk : GO k ≠ ⊤) :
      (∫⁻ b, ENNReal.ofReal (JD k b - JO k b) ∂μ) = GD k - GO k := by
    have hsum : (∫⁻ b, ENNReal.ofReal (JD k b) ∂μ) =
        GO k + ∫⁻ b, ENNReal.ofReal (JD k b - JO k b) ∂μ := by
      rw [← hGO k, ← lintegral_add_left (hJOm k).ennreal_ofReal]
      refine lintegral_congr_ae ?_
      filter_upwards [hJle] with b hb
      rw [← ENNReal.ofReal_add (hJO0 k b) (sub_nonneg.mpr (hb k)), add_sub_cancel]
    rw [← hGD k, hsum, ENNReal.add_sub_cancel_left hk]
  have hlimsub : Tendsto (fun k => GD k - GO k) atTop (𝓝 (a - c)) :=
    ENNReal.Tendsto.sub ha hc (Or.inr hcfin)
  have hGOfin : ∀ᶠ k in atTop, GO k ≠ ⊤ :=
    (hc.eventually (gt_mem_nhds (lt_top_iff_ne_top.mpr hcfin))).mono fun _ h => h.ne
  have hlim' : Tendsto (fun j => ∫⁻ b, ENNReal.ofReal (JD (n j) b - JO (n j) b) ∂μ) atTop
      (𝓝 (a - c)) := by
    refine (hlimsub.comp hn.tendsto_atTop).congr' ?_
    filter_upwards [hn.tendsto_atTop.eventually hGOfin] with j hj
    exact (hinc (n j) hj).symm
  have hFatou : (∫⁻ b, fΔ b ∂μ) ≤ a - c := by
    calc (∫⁻ b, fΔ b ∂μ) ≤
        liminf (fun j => ∫⁻ b, ENNReal.ofReal (JD (n j) b - JO (n j) b) ∂μ) atTop :=
          lintegral_liminf_le fun j => ((hJDm (n j)).sub (hJOm (n j))).ennreal_ofReal
      _ = a - c := hlim'.liminf_eq
  rw [hUD, hUO]
  exact add_le_add le_rfl hFatou

end HarmonicBalls

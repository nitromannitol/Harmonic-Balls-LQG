import HarmonicBalls.Proofs.Sec6.BrownianGermBlocks
import HarmonicBalls.Proofs.Sec6.BrownianScaling
import HarmonicBalls.Proofs.Brownian.PlanarBrownianMotion
import HarmonicBalls.Proofs.Brownian.PlanarHeatFeller
import MarkovProcess.Trajectory.Dynkin

/-! # Instantaneous entry into cones

Brownian scaling and the germ zero-one law turn a positive one-time
probability for a cone into almost-sure instantaneous entry.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Set Filter MarkovProcess
open scoped ENNReal NNReal Topology

/-- The one-time law of planar Brownian motion has full support. -/
theorem planarBrownian_eval_one_open_pos {K : Set ℂ} (hK : IsOpen K)
    (hne : K.Nonempty) : 0 < planarBrownianMotion 0 {ω | ω 1 ∈ K} := by
  have hmap := isFellerKernelSemigroup_planarHeatSemigroup.continuousProcess_map_eval_nnreal
    planarHeatSemigroup isConservative_planarHeatSemigroup kolmogorovRegular_planarHeatSemigroup 1
  rw [← planarBrownianMotion_eq_continuousProcess] at hmap
  have hvalue := congrArg (fun ker : ProbabilityTheory.Kernel ℂ ℂ => ker 0) hmap
  rw [ProbabilityTheory.Kernel.map_apply _ (show Measurable (fun ω : ContinuousPath ℂ => ω 1) from ContinuousPath.measurable_coordinateProcess 1),
    planarHeatSemigroup_apply] at hvalue
  have hpre : IsOpen (Complex.measurableEquivRealProd.symm ⁻¹' K) :=
    hK.preimage Complex.equivRealProdCLM.symm.continuous
  have hnon : (Complex.measurableEquivRealProd.symm ⁻¹' K).Nonempty := by
    obtain ⟨z, hz⟩ := hne
    exact ⟨Complex.measurableEquivRealProd z, by simpa using hz⟩
  have hvol : 0 < ((volume : Measure ℝ).prod volume)
      (Complex.measurableEquivRealProd.symm ⁻¹' K) := hpre.measure_pos _ hnon
  have hac : ((volume : Measure ℝ).prod volume) ≪
      (gaussianReal 0 1).prod (gaussianReal 0 1) :=
    (gaussianReal_absolutelyContinuous' 0 one_ne_zero).prod
      (gaussianReal_absolutelyContinuous' 0 one_ne_zero)
  have hp : 0 < (gaussianReal 0 1).prod (gaussianReal 0 1)
      (Complex.measurableEquivRealProd.symm ⁻¹' K) :=
    pos_iff_ne_zero.mpr (fun hz => hvol.ne' (hac hz))
  change 0 < planarBrownianMotion 0 ((fun ω : ContinuousPath ℂ => ω 1) ⁻¹' K)
  rw [← Measure.map_apply (show Measurable (fun ω : ContinuousPath ℂ => ω 1) from ContinuousPath.measurable_coordinateProcess 1) hK.measurableSet,
    hvalue, planarGaussian, Measure.map_apply Complex.measurableEquivRealProd.symm.measurable hK.measurableSet]
  simpa using hp

/-- Planar Brownian motion started at the vertex of a nonempty open cone enters
the cone instantly.
The cone is invariant under multiplication by every positive scalar. -/
theorem ae_planarBrownian_instant_hit_open_cone
    (x : ℂ) {K : Set ℂ} (hK : IsOpen K)
    (hcone : ∀ (a : ℝ), 0 < a → ∀ z : ℂ, a • z ∈ K ↔ z ∈ K)
    (hne : K.Nonempty) :
    ∀ᵐ ω ∂planarBrownianMotion x,
      ContinuousPath.exitTime {z : ℂ | z - x ∉ K} ω = 0 := by
  have hpos := planarBrownian_eval_one_open_pos hK hne
  let V : Set ℂ := {z | z - x ∈ K}
  have hV : IsOpen V := hK.preimage (by fun_prop)
  let : LocallyCompactSpace V := hV.locallyCompactSpace
  have hσ : IsSigmaCompact V := isSigmaCompact_iff_sigmaCompactSpace.mpr inferInstance
  obtain ⟨C, hC, hcover⟩ := hσ
  have hm := measurable_exitTime_compl_iUnion_compact C hC
  rw [hcover] at hm
  let τ : ContinuousPath ℂ → ℝ≥0∞ := ContinuousPath.exitTime Vᶜ
  let q : ℕ → ℝ≥0 := fun n => (1 / 2 : ℝ≥0) ^ n
  have hqpos (n : ℕ) : 0 < q n := pow_pos (by norm_num) n
  have hqanti : Antitone q := by
    apply antitone_nat_of_succ_le
    intro n
    change (1 / 2 : ℝ≥0) ^ (n + 1) ≤ (1 / 2 : ℝ≥0) ^ n
    rw [pow_succ]
    exact mul_le_of_le_one_right (by positivity) (by norm_num)
  have hqlim : Tendsto (fun n => (q n : ℝ≥0∞)) atTop (𝓝 0) := by
    have h : Tendsto q atTop (𝓝 0) := NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
    have hf := ENNReal.continuous_coe.continuousAt.tendsto.comp h
    change Tendsto (fun n => (q n : ℝ≥0∞)) atTop (𝓝 ((0 : ℝ≥0) : ℝ≥0∞)) at hf
    simpa using hf
  let A : ℕ → Set (ContinuousPath ℂ) := fun n => {ω | τ ω ≤ (q n : ℝ≥0∞)}
  have hA (n : ℕ) : MeasurableSet (A n) := measurableSet_le hm measurable_const
  have hanti : Antitone A := by
    intro m n hmn ω hω
    exact hω.trans (ENNReal.coe_le_coe.mpr (hqanti hmn))
  have hprob (n : ℕ) : planarBrownianMotion 0 {ω | ω 1 ∈ K} ≤ planarBrownianMotion x (A n) := by
    let T := scaledCenteredPlanarPath x (q n)
    let E : Set (ContinuousPath ℂ) := {ω | ω 1 ∈ K}
    have hE : MeasurableSet E := hK.measurableSet.preimage (ContinuousPath.measurable_coordinateProcess 1)
    have hmap := planarBrownianMotion_map_scaledCenteredPlanarPath x (ne_of_gt (hqpos n))
    have heq : planarBrownianMotion x (T ⁻¹' E) = planarBrownianMotion 0 E := by
      rw [← hmap, Measure.map_apply (continuous_scaledCenteredPlanarPath x (q n)).measurable hE]
    rw [← heq]
    apply measure_mono
    intro ω hω
    have hsqrt : 0 < (Real.sqrt (q n : ℝ))⁻¹ := inv_pos.mpr (Real.sqrt_pos.2 (by exact_mod_cast hqpos n))
    have hmem : ω (q n) - x ∈ K := by
      have hh : (Real.sqrt (q n : ℝ))⁻¹ • (ω (q n) - x) ∈ K := by
        simpa [T, E, scaledCenteredPlanarPath] using hω
      exact (hcone _ hsqrt _).mp hh
    exact ContinuousPath.exitTime_le_of_notMem Vᶜ ω (q n) (by simpa [V] using hmem)
  have hlim : Tendsto (fun n => planarBrownianMotion x (A n)) atTop
      (𝓝 (planarBrownianMotion x (⋂ n, A n))) :=
    tendsto_measure_iInter_atTop (fun n => (hA n).nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
  have hsub : (⋂ n, A n) ⊆ {ω | τ ω = 0} := by
    intro ω hω
    have hh : τ ω ≤ 0 := ge_of_tendsto hqlim (Eventually.of_forall fun n => mem_iInter.mp hω n)
    exact le_antisymm hh bot_le
  have hp : 0 < planarBrownianMotion x {ω | τ ω = 0} :=
    hpos.trans_le ((ge_of_tendsto hlim (Eventually.of_forall hprob)).trans (measure_mono hsub))
  have hhit := ae_instant_hit_compact_union_of_pos x C hC (by simpa [hcover, τ] using hp)
  rw [hcover] at hhit
  change ∀ᵐ ω ∂planarBrownianMotion x,
    ContinuousPath.exitTime {z : ℂ | z - x ∉ K} ω = 0 at hhit
  exact hhit

/-- A closed set with an exterior open cone is exited instantaneously by
planar Brownian motion started at the cone vertex. -/
theorem ae_planarBrownian_exitTime_closed_eq_zero_of_exterior_cone
    (x : ℂ) (F K : Set ℂ) (hK : IsOpen K) (hne : K.Nonempty)
    (hcone : ∀ (a : ℝ), 0 < a → ∀ z : ℂ, a • z ∈ K ↔ z ∈ K)
    (hexterior : ∀ z : ℂ, z - x ∈ K → z ∉ F) :
    ∀ᵐ ω ∂planarBrownianMotion x, ContinuousPath.exitTime F ω = 0 := by
  filter_upwards [ae_planarBrownian_instant_hit_open_cone x hK hcone hne] with ω hω
  have hle := ContinuousPath.exitTime_mono (show F ⊆ {z : ℂ | z - x ∉ K} from by
    intro z hz hk
    exact hexterior z hk hz) ω
  rw [hω] at hle
  exact le_antisymm hle bot_le

/-- A local exterior cone gives the same instantaneous-exit conclusion. -/
theorem ae_planarBrownian_exitTime_eq_zero_of_local_exterior_cone
    (x : ℂ) (F K : Set ℂ) (hK : IsOpen K) (hne : K.Nonempty)
    (hcone : ∀ (a : ℝ), 0 < a → ∀ z : ℂ, a • z ∈ K ↔ z ∈ K)
    {ε : ℝ} (hε : 0 < ε)
    (hexterior : ∀ z : ℂ, z - x ∈ K → dist z x < ε → z ∉ F) :
    ∀ᵐ ω ∂planarBrownianMotion x, ContinuousPath.exitTime F ω = 0 := by
  have hb : ∀ᵐ ω ∂planarBrownianMotion x,
      0 < ContinuousPath.exitTime (Metric.ball x ε) ω :=
    ae_planarBrownianMotion_exitTime_pos Metric.isOpen_ball (Metric.mem_ball_self hε)
  filter_upwards [ae_planarBrownian_instant_hit_open_cone x hK hcone hne, hb] with ω hω hbω
  have hle : min (ContinuousPath.exitTime F ω)
      (ContinuousPath.exitTime (Metric.ball x ε) ω) ≤
      ContinuousPath.exitTime {z : ℂ | z - x ∉ K} ω := by
    rw [ContinuousPath.le_exitTime_iff]
    intro t ht
    have hk : ω t - x ∈ K := by simpa using ht
    by_cases hb : ω t ∈ Metric.ball x ε
    · exact (min_le_left _ _).trans (ContinuousPath.exitTime_le_of_notMem F ω t
        (hexterior _ hk (Metric.mem_ball.mp hb)))
    · exact (min_le_right _ _).trans
        (ContinuousPath.exitTime_le_of_notMem (Metric.ball x ε) ω t hb)
  rw [hω] at hle
  by_contra hf
  exact (not_lt_of_ge hle) (lt_min (bot_lt_iff_ne_bot.mpr hf) hbω)

end HarmonicBalls.Section6

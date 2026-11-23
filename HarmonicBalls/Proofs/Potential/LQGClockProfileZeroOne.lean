import HarmonicBalls.Proofs.Potential.CameronMartinZeroOne
import HarmonicBalls.Proofs.Potential.LQGClockEveryStart
import LatticeProb.Gauss.CircleAverageCovariance
import LatticeProb.Gauss.CircleAverageApprox2
import LatticeProb.Gauss.UncorrelatedIndependence

/-! # A zero-one law for the positivity of a clock increment along a fixed path

For a fixed continuous path `w` and times `a ≤ b`, the event that the lower limit
`G_{a,b}(w) = liminf_k ∫_a^b ε^{γ²/2} e^{γ h_ε(w_v)} dv` (`ε = 2^{-k}`, `dyadicIncrementLiminf`) of
the dyadic approximants is positive has probability `0` or `1` under the law of the whole-plane
GFF.

The increment is read off the dyadic circle averages `(k, z) ↦ h_{2^{-k}}(z)`, a centred Gaussian
process indexed by `ℕ × ℂ`, through a functional `profileIncrementLiminf` of profiles
`g : ℕ × ℂ → ℝ` that is measurable for the product σ-algebra (the density at `z` is the lower limit
of its values at the simple approximations of `z`), jointly in the profile and the path, and equal
to `G_{a,b}(w)` for continuous profiles. The Cameron-Martin shifts of this process are the
covariances `(k, z) ↦ Cov(h_{2^{-k}}(z), X)` with finite combinations `X` of circle averages; they
are bounded uniformly in `k` on bounded sets of `z`, so they multiply the approximants along the
compact path range by factors in `[e^{-|γ| M}, e^{|γ| M}]`, and positivity of the lower limit is
invariant. The zero-one law for Cameron-Martin invariant events (`CameronMartinZeroOne`) gives the
dichotomy.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Real Set Filter Topology
open scoped ENNReal NNReal
open QuantumZipper.CameronMartin

namespace HarmonicBalls

theorem dyadicScale_le_one (k : ℕ) : dyadicScale k ≤ 1 := by
  unfold dyadicScale
  exact pow_le_one₀ (by norm_num) (by norm_num)

/-! ### Reading a profile at countably many points -/

/-- The simple approximation of `z ∈ ℂ` at level `n`, through which a profile is read at countably
many points. -/
noncomputable def profileRound (n : ℕ) : SimpleFunc ℂ ℂ :=
  SimpleFunc.approxOn id measurable_id Set.univ 0 (Set.mem_univ 0) n

theorem tendsto_profileRound (z : ℂ) : Tendsto (fun n => profileRound n z) atTop (𝓝 z) :=
  SimpleFunc.tendsto_approxOn measurable_id (Set.mem_univ 0) (by simp)

theorem norm_profileRound_le (n : ℕ) (z : ℂ) : ‖profileRound n z‖ ≤ 2 * ‖z‖ := by
  have h := SimpleFunc.edist_approxOn_y0_le measurable_id (Set.mem_univ (0 : ℂ)) z n
  rw [edist_dist, edist_dist, ← ENNReal.ofReal_add dist_nonneg dist_nonneg,
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
  simpa [profileRound, dist_zero_left, two_mul] using h

/-- The dyadic density `ε^{γ²/2} e^{γ (g(k, z) - α log max(ε, |z|))}` (`ε = 2^{-k}`) of a profile
`g`, read at the simple approximations of `z`. -/
noncomputable def profileDensity (γ α : ℝ) (k : ℕ) (g : ℕ × ℂ → ℝ) (z : ℂ) : ℝ≥0∞ :=
  liminf (fun n => ENNReal.ofReal (dyadicScale k ^ (γ ^ 2 / 2) *
    Real.exp (γ * (g (k, profileRound n z) - α * Real.log (max (dyadicScale k) ‖z‖))))) atTop

/-- The lower limit over the dyadic scales of the approximants `∫_a^b` of the profile densities
along a path. -/
noncomputable def profileIncrementLiminf (γ α a b : ℝ) (g : ℕ × ℂ → ℝ) (w : ContinuousPath ℂ) :
    ℝ≥0∞ :=
  liminf (fun k => ∫⁻ v in Ioc a b, profileDensity γ α k g (w v.toNNReal)) atTop

theorem measurable_profileDensity_comp (γ α : ℝ) (k : ℕ) {β : Type*} [MeasurableSpace β]
    {F : β → ℕ × ℂ → ℝ} {G : β → ℂ} (hF : Measurable F) (hG : Measurable G) :
    Measurable (fun x => profileDensity γ α k (F x) (G x)) := by
  have hm : ∀ n, Measurable (fun x => F x (k, profileRound n (G x))) := by
    intro n
    have h : Measurable (fun p : (ℕ × ℂ → ℝ) × (profileRound n).range => p.1 (k, (p.2 : ℂ))) :=
      measurable_from_prod_countable_left fun z => measurable_pi_apply (k, (z : ℂ))
    have hA : Measurable (fun x =>
        (⟨profileRound n (G x), SimpleFunc.mem_range_self _ _⟩ : (profileRound n).range)) :=
      Measurable.subtype_mk ((profileRound n).measurable.comp hG)
    exact h.comp (hF.prodMk hA)
  have hlog : Measurable (fun x => Real.log (max (dyadicScale k) ‖G x‖)) :=
    (measurable_const.max hG.norm).log
  have hn : ∀ n, Measurable (fun x => ENNReal.ofReal (dyadicScale k ^ (γ ^ 2 / 2) *
      Real.exp (γ * (F x (k, profileRound n (G x)) -
        α * Real.log (max (dyadicScale k) ‖G x‖))))) :=
    fun n => (measurable_const.mul ((measurable_const.mul
      ((hm n).sub (measurable_const.mul hlog))).exp)).ennreal_ofReal
  exact Measurable.liminf hn

/-- `profileIncrementLiminf` is measurable jointly in the profile and the path. -/
theorem measurable_profileIncrementLiminf_comp (γ α a b : ℝ) {β : Type*} [MeasurableSpace β]
    {F : β → ℕ × ℂ → ℝ} {W : β → ContinuousPath ℂ} (hF : Measurable F) (hW : Measurable W) :
    Measurable (fun x => profileIncrementLiminf γ α a b (F x) (W x)) := by
  have hk : ∀ k, Measurable (fun x =>
      ∫⁻ v in Ioc a b, profileDensity γ α k (F x) (W x v.toNNReal)) := by
    intro k
    have hpath : Measurable (fun q : β × ℝ => W q.1 q.2.toNNReal) := by
      have hc : Continuous (fun q : ContinuousPath ℂ × ℝ => q.1 q.2.toNNReal) :=
        continuous_eval.comp (continuous_id.prodMap continuous_real_toNNReal)
      exact hc.measurable.comp ((hW.comp measurable_fst).prodMk measurable_snd)
    have hint : Measurable (fun q : β × ℝ => profileDensity γ α k (F q.1) (W q.1 q.2.toNNReal)) :=
      measurable_profileDensity_comp γ α k (hF.comp measurable_fst) hpath
    exact hint.lintegral_prod_right'
  exact Measurable.liminf hk

theorem measurableSet_profileIncrementLiminf_pos (γ α a b : ℝ) (w : ContinuousPath ℂ) :
    MeasurableSet {g : ℕ × ℂ → ℝ | 0 < profileIncrementLiminf γ α a b g w} :=
  measurableSet_lt measurable_const
    (measurable_profileIncrementLiminf_comp γ α a b measurable_id measurable_const)

/-- For a profile continuous in `z`, the density is read off exactly. -/
theorem profileDensity_of_continuous {γ α : ℝ} {k : ℕ} {g : ℕ × ℂ → ℝ}
    (hg : Continuous fun z => g (k, z)) (z : ℂ) :
    profileDensity γ α k g z = ENNReal.ofReal (dyadicScale k ^ (γ ^ 2 / 2) *
      Real.exp (γ * (g (k, z) - α * Real.log (max (dyadicScale k) ‖z‖)))) := by
  apply Filter.Tendsto.liminf_eq
  exact (ENNReal.continuous_ofReal.tendsto _).comp
    (tendsto_const_nhds.mul ((Real.continuous_exp.tendsto _).comp
      (tendsto_const_nhds.mul (((hg.tendsto z).comp (tendsto_profileRound z)).sub
        tendsto_const_nhds))))

theorem fieldCircleAverage_dyadic_eq (α : ℝ) (u : ℝ → ℂ → ℝ) (k : ℕ) (z : ℂ) :
    LatticeProb.Gauss.fieldCircleAverage α u (dyadicScale k) z =
      u (dyadicScale k) z - α * Real.log (max (dyadicScale k) ‖z‖) := by
  have hlog : Real.circleAverage (fun y : ℂ => Real.log ‖y‖) z (dyadicScale k) =
      Real.log (max (dyadicScale k) ‖z‖) := by
    simpa using (LatticeProb.Gauss.circleAverage_log_norm_sub_eq z 0 (dyadicScale_pos k))
  rw [LatticeProb.Gauss.fieldCircleAverage, hlog]

/-- For profiles continuous at every dyadic scale, `profileIncrementLiminf` is the lower limit
`G_{a,b}(w)` of the dyadic approximants of the inserted field. -/
theorem profileIncrementLiminf_eq_dyadicIncrementLiminf {γ α a b : ℝ} (hab : a ≤ b)
    {u : ℝ → ℂ → ℝ} (hu : ∀ k, Continuous (u (dyadicScale k))) (w : ContinuousPath ℂ) :
    profileIncrementLiminf γ α a b (fun p => u (dyadicScale p.1) p.2) w =
      dyadicIncrementLiminf γ (LatticeProb.Gauss.fieldCircleAverage α u) a b w := by
  unfold profileIncrementLiminf dyadicIncrementLiminf
  congr 1
  funext k
  have h1 : Continuous fun z => LatticeProb.Gauss.fieldCircleAverage α u (dyadicScale k) z := by
    simp_rw [fieldCircleAverage_dyadic_eq]
    exact (hu k).sub (continuous_const.mul
      ((continuous_const.max continuous_norm).log fun z =>
        ne_of_gt (lt_of_lt_of_le (dyadicScale_pos k) (le_max_left _ _))))
  have hfc : Continuous fun v : ℝ => dyadicScale k ^ (γ ^ 2 / 2) *
      Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α u (dyadicScale k) (w v.toNNReal)) :=
    continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul
      (h1.comp (w.continuous.comp continuous_real_toNNReal))))
  have hdens : ∀ v : ℝ, profileDensity γ α k (fun p => u (dyadicScale p.1) p.2) (w v.toNNReal) =
      ENNReal.ofReal (dyadicScale k ^ (γ ^ 2 / 2) *
        Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α u (dyadicScale k) (w v.toNNReal))) := by
    intro v
    rw [profileDensity_of_continuous (g := fun p => u (dyadicScale p.1) p.2) (hu k),
      fieldCircleAverage_dyadic_eq]
  simp_rw [hdens]
  rw [dyadicIncrementApprox, intervalIntegral.integral_of_le hab,
    ofReal_integral_eq_lintegral_ofReal (hfc.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
      (Filter.Eventually.of_forall fun v =>
        mul_nonneg (Real.rpow_nonneg (dyadicScale_pos k).le _) (Real.exp_pos _).le)]

/-- A bounded perturbation of the profile on a disc containing (twice) the path range changes the
approximants by a factor at least `e^{-|γ| M}`. -/
theorem profileIncrementLiminf_add_ge {γ α a b ρ M : ℝ} {g c : ℕ × ℂ → ℝ}
    {w : ContinuousPath ℂ} (hw : ∀ v ∈ Ioc a b, ‖w v.toNNReal‖ ≤ ρ)
    (hc : ∀ k z, ‖z‖ ≤ 2 * ρ → |c (k, z)| ≤ M) :
    ENNReal.ofReal (Real.exp (-(|γ| * M))) * profileIncrementLiminf γ α a b g w ≤
      profileIncrementLiminf γ α a b (g + c) w := by
  unfold profileIncrementLiminf
  rw [← ENNReal.liminf_const_mul_of_ne_top ENNReal.ofReal_ne_top]
  refine Filter.liminf_le_liminf (Filter.Eventually.of_forall fun k => ?_)
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' measurableSet_Ioc fun v hv => ?_
  unfold profileDensity
  rw [← ENNReal.liminf_const_mul_of_ne_top ENNReal.ofReal_ne_top]
  refine Filter.liminf_le_liminf (Filter.Eventually.of_forall fun n => ?_)
  have hz : ‖profileRound n (w v.toNNReal)‖ ≤ 2 * ρ :=
    (norm_profileRound_le n _).trans (by linarith [hw v hv])
  have hcb := hc k _ hz
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
  apply ENNReal.ofReal_le_ofReal
  simp only [Pi.add_apply]
  set e := c (k, profileRound n (w v.toNNReal))
  set y := g (k, profileRound n (w v.toNNReal)) -
    α * Real.log (max (dyadicScale k) ‖w v.toNNReal‖)
  have h1 : -(|γ| * M) ≤ γ * e := by
    have h2 : |γ * e| ≤ |γ| * M := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hcb (abs_nonneg γ)
    linarith [neg_abs_le (γ * e)]
  have hA : 0 ≤ dyadicScale k ^ (γ ^ 2 / 2) := Real.rpow_nonneg (dyadicScale_pos k).le _
  calc Real.exp (-(|γ| * M)) * (dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * y))
      ≤ Real.exp (γ * e) * (dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * y)) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr h1) (by positivity)
    _ = dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * (g (k, profileRound n (w v.toNNReal)) + e -
          α * Real.log (max (dyadicScale k) ‖w v.toNNReal‖))) := by
        rw [show γ * (g (k, profileRound n (w v.toNNReal)) + e -
            α * Real.log (max (dyadicScale k) ‖w v.toNNReal‖)) = γ * e + γ * y by
          simp only [y]; ring, Real.exp_add]
        ring

theorem profileIncrementLiminf_add_pos {γ α a b ρ M : ℝ} {g c : ℕ × ℂ → ℝ}
    {w : ContinuousPath ℂ} (hw : ∀ v ∈ Ioc a b, ‖w v.toNNReal‖ ≤ ρ)
    (hc : ∀ k z, ‖z‖ ≤ 2 * ρ → |c (k, z)| ≤ M) (h : 0 < profileIncrementLiminf γ α a b g w) :
    0 < profileIncrementLiminf γ α a b (g + c) w :=
  lt_of_lt_of_le (ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne' h.ne')
    (profileIncrementLiminf_add_ge hw hc)

/-! ### Covariances of dyadic circle averages are bounded on bounded sets -/

/-- The covariance of a circle average of radius `r ≤ 1` centred in a bounded set with a fixed
circle average is bounded uniformly in `r`. -/
theorem exists_abs_wholePlaneGFFCov_circle_le {s : ℝ} (hs : 0 < s) (w₀ : ℂ) {ρ : ℝ}
    (hρ : 0 ≤ ρ) :
    ∃ M, ∀ r, 0 < r → r ≤ 1 → ∀ z : ℂ, ‖z‖ ≤ ρ →
      |LatticeProb.Gauss.wholePlaneGFFCov (.circle r z) (.circle s w₀)| ≤ M := by
  refine ⟨Real.log (ρ + 1) +
    |Real.circleAverage LatticeProb.Gauss.logMaxAbs w₀ s| + |Real.log s| +
      |Real.log (max s (ρ + 1 + ‖w₀‖))|, ?_⟩
  intro r hr hr1 z hz
  rw [LatticeProb.Gauss.wholePlaneGFFCov_circle_circle_eq hs r z w₀]
  have hsph : ∀ x ∈ Metric.sphere z |r|, ‖x‖ ≤ ρ + 1 := by
    intro x hx
    have hx' : ‖x - z‖ = r := (mem_sphere_iff_norm.1 hx).trans (abs_of_pos hr)
    have h3 : ‖x‖ ≤ ‖z‖ + ‖x - z‖ := by
      have := norm_add_le z (x - z)
      simpa using this
    linarith
  have hci : CircleIntegrable LatticeProb.Gauss.logMaxAbs z r :=
    LatticeProb.Gauss.logMaxAbs_continuous.continuousOn.circleIntegrable'
  have hA1 : 0 ≤ Real.circleAverage LatticeProb.Gauss.logMaxAbs z r :=
    Real.circleAverage_nonneg_of_nonneg fun x _ => Real.log_nonneg (le_max_right _ _)
  have hA2 : Real.circleAverage LatticeProb.Gauss.logMaxAbs z r ≤ Real.log (ρ + 1) :=
    Real.circleAverage_mono_on_of_le_circle hci fun x hx =>
      Real.log_le_log (lt_of_lt_of_le one_pos (le_max_right _ _))
        (max_le (hsph x hx) (by linarith))
  have hcp : CircleIntegrable (fun x : ℂ => Real.log (max s ‖x - w₀‖)) z r :=
    (LatticeProb.Gauss.continuous_log_max_norm_sub hs w₀).continuousOn.circleIntegrable'
  have hP1 : Real.log s ≤ LatticeProb.Gauss.circlePairPotential z r w₀ s := by
    unfold LatticeProb.Gauss.circlePairPotential
    have h := Real.circleAverage_mono (c := z) (R := r) (f₁ := fun _ : ℂ => Real.log s)
      continuous_const.continuousOn.circleIntegrable' hcp
      (fun x _ => Real.log_le_log hs (le_max_left _ _))
    rwa [Real.circleAverage_const] at h
  have hP2 : LatticeProb.Gauss.circlePairPotential z r w₀ s ≤
      Real.log (max s (ρ + 1 + ‖w₀‖)) :=
    Real.circleAverage_mono_on_of_le_circle hcp fun x hx => by
      refine Real.log_le_log (lt_of_lt_of_le hs (le_max_left _ _)) (max_le_max le_rfl ?_)
      have h1 := norm_sub_le x w₀
      linarith [hsph x hx]
  have hρ1 : 0 ≤ Real.log (ρ + 1) := Real.log_nonneg (by linarith)
  rw [abs_le]
  constructor
  · linarith [neg_abs_le (Real.circleAverage LatticeProb.Gauss.logMaxAbs w₀ s),
      le_abs_self (Real.log (max s (ρ + 1 + ‖w₀‖))), abs_nonneg (Real.log s)]
  · linarith [le_abs_self (Real.circleAverage LatticeProb.Gauss.logMaxAbs w₀ s),
      neg_abs_le (Real.log s), abs_nonneg (Real.log (max s (ρ + 1 + ‖w₀‖)))]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- The dyadic circle averages `(k, z) ↦ h_{2^{-k}}(z)` form a Gaussian process. -/
theorem isGaussianProcess_dyadicCircle (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) :
    IsGaussianProcess (fun (p : ℕ × ℂ) ω => hcirc ω (dyadicScale p.1) p.2) P :=
  LatticeProb.GaussIndep.isGaussianProcess_of_mem_span hh.isGaussianProcess fun p =>
    Submodule.subset_span ⟨⟨.circle (dyadicScale p.1) p.2, dyadicScale_pos p.1⟩, rfl⟩

/-- The Cameron-Martin shifts of the dyadic circle averages are bounded uniformly in the scale on
bounded sets of centres. -/
theorem exists_abs_covShift_dyadicCircle_le (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    (σ : (ℕ × ℂ) →₀ ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∃ M, ∀ k z, ‖z‖ ≤ ρ →
      |covShift (fun (p : ℕ × ℂ) ω => hcirc ω (dyadicScale p.1) p.2) P σ (k, z)| ≤ M := by
  have hM : ∀ i : ℕ × ℂ, ∃ M, ∀ r, 0 < r → r ≤ 1 → ∀ z : ℂ, ‖z‖ ≤ ρ →
      |LatticeProb.Gauss.wholePlaneGFFCov (.circle r z) (.circle (dyadicScale i.1) i.2)| ≤ M :=
    fun i => exists_abs_wholePlaneGFFCov_circle_le (dyadicScale_pos i.1) i.2 hρ
  choose M hM using hM
  refine ⟨∑ i ∈ σ.support, |σ i| * M i, fun k z hz => ?_⟩
  unfold covShift covK
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul, hh.covariance_circle_circle (dyadicScale_pos k) (dyadicScale_pos i.1)]
  exact mul_le_mul_of_nonneg_left
    (hM i _ (dyadicScale_pos k) (dyadicScale_le_one k) z hz) (abs_nonneg _)

/-- For almost every field all dyadic circle-average slices are continuous. -/
theorem ae_continuous_dyadic_circle (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) :
    ∀ᵐ ω ∂P, ∀ k : ℕ, Continuous (hcirc ω (dyadicScale k)) := by
  filter_upwards [hh.ae_continuousOn_circle] with ω hω k
  exact hω.comp_continuous (continuous_const.prodMk continuous_id)
    fun z => ⟨dyadicScale_pos k, Set.mem_univ _⟩

/-- **Zero-one law along a fixed path.** For every continuous path `w` and `a ≤ b`, the lower
limit `G_{a,b}(w)` of the dyadic approximants of the inserted field is positive with probability
`0` or `1`. -/
theorem measure_dyadicIncrementLiminf_pos_eq_zero_or_one
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (γ α : ℝ) {a b : ℝ} (hab : a ≤ b)
    (w : ContinuousPath ℂ) :
    P {ω | 0 < dyadicIncrementLiminf γ (LatticeProb.Gauss.fieldCircleAverage α (hcirc ω)) a b w}
        = 0 ∨
      P {ω | 0 < dyadicIncrementLiminf γ (LatticeProb.Gauss.fieldCircleAverage α (hcirc ω)) a b w}
        = 1 := by
  have hPm := hh.isProbabilityMeasure
  have hX := isGaussianProcess_dyadicCircle hh
  have hXm : ∀ p : ℕ × ℂ, Measurable (fun ω => hcirc ω (dyadicScale p.1) p.2) := fun p =>
    hh.measurable_circle _ _ (dyadicScale_pos p.1)
  have hXc : ∀ p : ℕ × ℂ, P[fun ω => hcirc ω (dyadicScale p.1) p.2] = 0 := fun p =>
    hh.integral_eq_zero (.circle (dyadicScale p.1) p.2) (dyadicScale_pos p.1)
  have hS := measurableSet_profileIncrementLiminf_pos γ α a b w
  obtain ⟨ρ, hρ0, hρ⟩ : ∃ ρ, 0 ≤ ρ ∧ ∀ v ∈ Ioc a b, ‖w v.toNNReal‖ ≤ ρ := by
    have hK : IsCompact ((fun v : ℝ => w v.toNNReal) '' Icc a b) :=
      isCompact_Icc.image (w.continuous.comp continuous_real_toNNReal)
    obtain ⟨C, hC⟩ := hK.isBounded.exists_norm_le
    exact ⟨max C 0, le_max_right _ _, fun v hv =>
      (hC _ ⟨v, Ioc_subset_Icc_self hv, rfl⟩).trans (le_max_left _ _)⟩
  have hinv : ∀ (σ : (ℕ × ℂ) →₀ ℝ) (g : ℕ × ℂ → ℝ),
      g ∈ {g : ℕ × ℂ → ℝ | 0 < profileIncrementLiminf γ α a b g w} →
        g + covShift (fun (p : ℕ × ℂ) ω => hcirc ω (dyadicScale p.1) p.2) P σ ∈
          {g : ℕ × ℂ → ℝ | 0 < profileIncrementLiminf γ α a b g w} := by
    intro σ g hg
    obtain ⟨M, hM⟩ := exists_abs_covShift_dyadicCircle_le hh σ (by linarith : (0 : ℝ) ≤ 2 * ρ)
    exact profileIncrementLiminf_add_pos hρ (fun k z hz => hM k z hz) hg
  have h01 := measure_preimage_eq_zero_or_one_of_shift_invariant hX hXm hXc hS hinv
  have hae : {ω | 0 < dyadicIncrementLiminf γ (LatticeProb.Gauss.fieldCircleAverage α (hcirc ω))
      a b w} =ᵐ[P] (fun ω (j : ℕ × ℂ) => hcirc ω (dyadicScale j.1) j.2) ⁻¹'
        {g : ℕ × ℂ → ℝ | 0 < profileIncrementLiminf γ α a b g w} := by
    filter_upwards [ae_continuous_dyadic_circle hh] with ω hω
    have he := profileIncrementLiminf_eq_dyadicIncrementLiminf (γ := γ) (α := α) hab hω w
    show (0 < dyadicIncrementLiminf γ (LatticeProb.Gauss.fieldCircleAverage α (hcirc ω)) a b w) =
      (0 < profileIncrementLiminf γ α a b (fun j : ℕ × ℂ => hcirc ω (dyadicScale j.1) j.2) w)
    rw [he]
  rw [measure_congr hae]
  exact h01

end HarmonicBalls

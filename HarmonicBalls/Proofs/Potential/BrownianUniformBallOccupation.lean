import HarmonicBalls.Proofs.Potential.BrownianPairOccupationBound
import HarmonicBalls.Proofs.Sec6.PlanarIncrementBlocks
import Mathlib.Data.Fin.Tuple.Sort
import LatticeProb.Analysis.RieszKernelHolder

/-! # Uniform-centre Brownian occupation estimates

Planar Brownian occupation moments and finite-grid tails admit bounds uniform in the centre.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Set Metric
open scoped NNReal ENNReal

namespace HarmonicBalls

/-- A centred planar Gaussian assigns every ball at most the product of the
coordinate interval bounds. -/
theorem planarGaussian_ball_le_uniform_center {v : ℝ≥0} (hv : v ≠ 0)
    (z : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    planarGaussian 0 v (ball z r) ≤
      (ENNReal.ofReal (2 * r / Real.sqrt (2 * Real.pi * v))) ^ 2 := by
  let I : Set ℝ := Icc (z.re - r) (z.re + r)
  let J : Set ℝ := Icc (z.im - r) (z.im + r)
  have hsub : Complex.measurableEquivRealProd.symm ⁻¹' (ball z r) ⊆ I ×ˢ J := by
    intro p hp
    have hn : ‖Complex.measurableEquivRealProd.symm p - z‖ < r := by
      simpa [Metric.mem_ball, dist_eq_norm] using hp
    have hre := (Complex.abs_re_le_norm (Complex.measurableEquivRealProd.symm p - z)).trans
      (le_of_lt hn)
    have him := (Complex.abs_im_le_norm (Complex.measurableEquivRealProd.symm p - z)).trans
      (le_of_lt hn)
    change |p.1 - z.re| ≤ r at hre
    change |p.2 - z.im| ≤ r at him
    have hre' := abs_le.mp hre
    have him' := abs_le.mp him
    dsimp [I, J]
    constructor <;> constructor <;> linarith
  have hI : gaussianReal 0 v I ≤ ENNReal.ofReal (2 * r / Real.sqrt (2 * Real.pi * v)) := by
    have h := LatticeProb.gaussianReal_Icc_le hv (c := z.re - r) (d := z.re + r) (by linarith)
    simpa [I, show z.re + r - (z.re - r) = 2 * r by ring] using h
  have hJ : gaussianReal 0 v J ≤ ENNReal.ofReal (2 * r / Real.sqrt (2 * Real.pi * v)) := by
    have h := LatticeProb.gaussianReal_Icc_le hv (c := z.im - r) (d := z.im + r) (by linarith)
    simpa [J, show z.im + r - (z.im - r) = 2 * r by ring] using h
  rw [planarGaussian, Complex.zero_re, Complex.zero_im,
    Measure.map_apply Complex.measurableEquivRealProd.symm.measurable isOpen_ball.measurableSet]
  calc
    _ ≤ ((gaussianReal 0 v).prod (gaussianReal 0 v)) (I ×ˢ J) := measure_mono hsub
    _ = gaussianReal 0 v I * gaussianReal 0 v J := Measure.prod_prod _ _
    _ ≤ (ENNReal.ofReal (2 * r / Real.sqrt (2 * Real.pi * v))) ^ 2 := by
      simpa [pow_two] using mul_le_mul' hI hJ

/-- Every planar Brownian increment satisfies a small-ball bound uniform in the centre. -/
theorem planarBrownianMotion_increment_smallBall_le_uniform_center (x z : ℂ)
    {s t : ℝ≥0} (hts : t ≠ s) {r : ℝ} (hr : 0 ≤ r) :
    planarBrownianMotion x {b | ‖b t - b s - z‖ < r} ≤
      min 1 ((ENNReal.ofReal (2 * r / Real.sqrt (2 * Real.pi *
        (nndist (t : ℝ) (s : ℝ) : ℝ)))) ^ 2) := by
  have hv : nndist (t : ℝ) (s : ℝ) ≠ 0 := by
    intro hzero
    apply hts
    exact_mod_cast (nndist_eq_zero.mp hzero)
  apply le_min
  · exact prob_le_one
  · have hm : Measurable (fun b : ContinuousPath ℂ => b t - b s) :=
      (ContinuousPath.measurable_coordinateProcess _).sub
        (ContinuousPath.measurable_coordinateProcess _)
    have h := congrArg (fun μ : Measure ℂ => μ (ball z r))
      (planarBrownianMotion_map_increment x s t)
    rw [Measure.map_apply hm isOpen_ball.measurableSet] at h
    have hh : planarBrownianMotion x {b | ‖b t - b s - z‖ < r} =
        planarGaussian 0 (nndist (t : ℝ) (s : ℝ)) (ball z r) := by
      simpa only [Metric.ball, Set.preimage_ofPred_eq, dist_eq_norm] using h
    rw [hh]
    exact planarGaussian_ball_le_uniform_center hv z hr

/-- A subcritical power bound for Brownian increment probabilities, uniform in the centre. -/
theorem planarBrownianMotion_increment_smallBall_rpow_le_uniform_center (x z : ℂ)
    {s t : ℝ≥0} (hts : t ≠ s) {r q : ℝ} (hr : 0 < r) (hq0 : 0 < q) (hq1 : q < 1) :
    planarBrownianMotion x {b | ‖b t - b s - z‖ < r} ≤
      ENNReal.ofReal ((2 / Real.pi) ^ q * r ^ (2 * q) *
        |(t : ℝ) - (s : ℝ)| ^ (-q)) := by
  let u : ℝ := |(t : ℝ) - (s : ℝ)|
  have hu : 0 < u := by
    dsimp [u]
    apply abs_pos.mpr
    exact sub_ne_zero.mpr (by exact_mod_cast hts)
  let a : ℝ := 2 * r / Real.sqrt (2 * Real.pi * u)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hs : (Real.sqrt (2 * Real.pi * u)) ^ 2 = 2 * Real.pi * u :=
    Real.sq_sqrt (by positivity)
  have hs0 : Real.sqrt (2 * Real.pi * u) ≠ 0 := by positivity
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hu0 : u ≠ 0 := ne_of_gt hu
  have haeq : a ^ 2 = (2 / Real.pi) * r ^ 2 / u := by
    dsimp [a]
    field_simp
    nlinarith [hs]
  have hpower : (a ^ 2) ^ q =
      (2 / Real.pi) ^ q * r ^ (2 * q) * u ^ (-q) := by
    rw [haeq, Real.div_rpow (by positivity) (le_of_lt hu),
      Real.mul_rpow (by positivity) (sq_nonneg r),
      ← Real.rpow_natCast r 2, ← Real.rpow_mul (le_of_lt hr),
      Real.rpow_neg (le_of_lt hu)]
    ring
  have hmin : min 1 (ENNReal.ofReal (a ^ 2)) ≤ ENNReal.ofReal ((a ^ 2) ^ q) := by
    by_cases h : a ^ 2 ≤ 1
    · exact (min_le_right _ _).trans
        (ENNReal.ofReal_le_ofReal (Real.self_le_rpow_of_le_one (sq_nonneg a) h hq1.le))
    · have hh : 1 ≤ (a ^ 2) ^ q := Real.one_le_rpow (le_of_not_ge h) hq0.le
      exact (min_le_left _ _).trans (by simpa using ENNReal.ofReal_le_ofReal hh)
  have hsmall := planarBrownianMotion_increment_smallBall_le_uniform_center x z hts hr.le
  have hsmall' : planarBrownianMotion x {b | ‖b t - b s - z‖ < r} ≤
      min 1 (ENNReal.ofReal (a ^ 2)) := by
    simpa only [a, u, coe_nndist, Real.dist_eq, ENNReal.ofReal_pow ha] using hsmall
  exact hsmall'.trans (by simpa [hpower, u] using hmin)


/-- Successive increments at ordered times of planar Brownian motion are independent. -/
theorem planarBrownianMotion_hasIndepIncrements (x : ℂ) :
    ProbabilityTheory.HasIndepIncrements (fun t (b : ContinuousPath ℂ) => b t) (planarBrownianMotion x) := by
  intro n t ht
  have h := Section6.iIndepFun_planarBrownian_increment_blocks x
    (fun i (_ : Unit) => t i.castSucc) (fun i (_ : Unit) => t i.succ)
    (fun i _ => ht (Fin.castSucc_le_succ i))
    (fun i j hij _ _ => by
      rcases lt_or_gt_of_ne hij with hij | hji
      · exact Or.inl (ht (Fin.succ_le_castSucc_iff.mpr hij))
      · exact Or.inr (ht (Fin.succ_le_castSucc_iff.mpr hji)))
  have heval := h.comp (fun _ f => f ()) (fun _ => measurable_pi_apply ())
  exact heval


/-- Simultaneous visits at ordered times are controlled by independent increments. -/
theorem planarBrownianMotion_joint_ball_le (x z : ℂ) {n : ℕ}
    (t : Fin (n + 1) → ℝ≥0) (ht : StrictMono t) {r q : ℝ}
    (hr : 0 < r) (hq0 : 0 < q) (hq1 : q < 1) :
    planarBrownianMotion x {b | ∀ i, ‖b (t i) - z‖ < r} ≤
      ∏ i : Fin n, ENNReal.ofReal ((2 / Real.pi) ^ q * (2 * r) ^ (2 * q) *
        |(t i.succ : ℝ) - (t i.castSucc : ℝ)| ^ (-q)) := by
  let f : Fin n → ContinuousPath ℂ → ℂ :=
    fun i b => b (t i.succ) - b (t i.castSucc)
  let A : Set ℂ := ball 0 (2 * r)
  have hi : iIndepFun f (planarBrownianMotion x) :=
    planarBrownianMotion_hasIndepIncrements x n t ht.monotone
  have hsub : {b : ContinuousPath ℂ | ∀ i, ‖b (t i) - z‖ < r} ⊆
      ⋂ i : Fin n, f i ⁻¹' A := by
    intro b hb
    simp only [mem_iInter, mem_preimage]
    intro i
    simp only [f, A, Metric.mem_ball, dist_zero_right]
    have hnorm := norm_sub_le (b (t i.succ) - z) (b (t i.castSucc) - z)
    have heq : (b (t i.succ) - z) - (b (t i.castSucc) - z) =
        b (t i.succ) - b (t i.castSucc) := by abel
    rw [heq] at hnorm
    linarith [hb i.succ, hb i.castSucc]
  calc
    _ ≤ planarBrownianMotion x (⋂ i : Fin n, f i ⁻¹' A) := measure_mono hsub
    _ = ∏ i : Fin n, planarBrownianMotion x (f i ⁻¹' A) := by
      simpa using hi.measure_inter_preimage_eq_mul Finset.univ
        (sets := fun _ => A) (fun _ _ => isOpen_ball.measurableSet)
    _ ≤ _ := by
      apply Finset.prod_le_prod
      intro i _
      have hne : t i.succ ≠ t i.castSucc :=
        ne_of_gt (ht (Fin.castSucc_lt_succ (i := i)))
      have hbound := planarBrownianMotion_increment_smallBall_rpow_le x hne
        (show 0 < 2 * r by positivity) hq0 hq1
      convert hbound using 1
      congr 1
      ext b
      simp [f, A, Metric.mem_ball, dist_zero_right]

/-- Every occupation moment is the integral of the joint visit probability. -/
theorem planarBrownianMotion_occupation_moment_eq (x z : ℂ) (r : ℝ) (n : ℕ)
    (ν : Measure ℝ≥0) [SigmaFinite ν] :
    (∫⁻ b : ContinuousPath ℂ, (ν {t | ‖b t - z‖ < r}) ^ n ∂(planarBrownianMotion x)) =
    ∫⁻ t : Fin n → ℝ≥0, planarBrownianMotion x {b | ∀ i, ‖b (t i) - z‖ < r}
      ∂(Measure.pi (fun _ : Fin n => ν)) := by
  let E : Set (ContinuousPath ℂ × (Fin n → ℝ≥0)) :=
    {p | ∀ i, ‖p.1 (p.2 i) - z‖ < r}
  have hE : MeasurableSet E := by
    simp only [E, ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    apply isOpen_lt _ continuous_const |>.measurableSet
    fun_prop
  let F : ContinuousPath ℂ × (Fin n → ℝ≥0) → ℝ≥0∞ := E.indicator 1
  have hF : Measurable F := measurable_const.indicator hE
  calc
    _ = ∫⁻ b, ∫⁻ t, F (b,t) ∂(Measure.pi (fun _ : Fin n => ν))
        ∂(planarBrownianMotion x) := by
      congr 1; funext b
      let A : Set ℝ≥0 := {t | ‖b t - z‖ < r}
      have hA : MeasurableSet A := by
        apply isOpen_lt _ continuous_const |>.measurableSet
        fun_prop
      have hpi : {t : Fin n → ℝ≥0 | ∀ i, ‖b (t i) - z‖ < r} = Set.univ.pi (fun _ => A) := by
        ext t; simp [A]
      have hm : MeasurableSet {t : Fin n → ℝ≥0 | ∀ i, ‖b (t i) - z‖ < r} := by
        rw [hpi]; exact MeasurableSet.univ_pi (fun _ => hA)
      rw [show (fun t => F (b,t)) = ({t : Fin n → ℝ≥0 | ∀ i, ‖b (t i) - z‖ < r}).indicator 1 by
        funext t; simp [F, E, Set.indicator_apply]]
      rw [lintegral_indicator_one hm, hpi, Measure.pi_pi]
      simp [A]
    _ = ∫⁻ t, ∫⁻ b, F (b,t) ∂(planarBrownianMotion x)
        ∂(Measure.pi (fun _ : Fin n => ν)) := lintegral_lintegral_swap hF.aemeasurable
    _ = _ := by
      congr 1; funext t
      have hm : MeasurableSet {b : ContinuousPath ℂ | ∀ i, ‖b (t i) - z‖ < r} := by
        simp only [ofPred_forall]
        apply MeasurableSet.iInter
        intro i
        apply isOpen_lt _ continuous_const |>.measurableSet
        fun_prop
      convert lintegral_indicator_one hm using 1; simp [F, E, Set.indicator_apply]
/-- Ball occupation is measurable as a function of the continuous path. -/
theorem measurable_ball_occupation (z : ℂ) (r : ℝ)
    (ν : Measure ℝ≥0) [SFinite ν] :
    Measurable (fun b : ContinuousPath ℂ => ν {t | ‖b t - z‖ < r}) := by
  let E : Set (ContinuousPath ℂ × ℝ≥0) := {p | ‖p.1 p.2 - z‖ < r}
  have hE : MeasurableSet E := by
    apply isOpen_lt _ continuous_const |>.measurableSet
    fun_prop
  exact measurable_measure_prodMk_left (ν := ν) hE
/-- Joint visits at distinct times are bounded by the sum over all time orders. -/
theorem planarBrownianMotion_joint_ball_le_sum_permutations (x z : ℂ) {n : ℕ} (t : Fin (n + 1) → ℝ≥0)
    (ht : Function.Injective t) {r q : ℝ} (hr : 0 < r) (hq0 : 0 < q) (hq1 : q < 1) :
    planarBrownianMotion x {b | ∀ i, ‖b (t i) - z‖ < r} ≤
      ∑ σ : Equiv.Perm (Fin (n + 1)), ∏ i : Fin n,
        ENNReal.ofReal ((2 / Real.pi) ^ q * (2 * r) ^ (2 * q) *
          |(t (σ i.succ) : ℝ) - (t (σ i.castSucc) : ℝ)| ^ (-q)) := by
  classical
  let σ := Tuple.sort t
  have hmono : StrictMono (t ∘ σ) :=
    (Tuple.monotone_sort t).strictMono_of_injective (ht.comp σ.injective)
  have h := planarBrownianMotion_joint_ball_le x z (t ∘ σ) hmono hr hq0 hq1
  have hsets : {b : ContinuousPath ℂ | ∀ i, ‖b (t (σ i)) - z‖ < r} =
      {b : ContinuousPath ℂ | ∀ i, ‖b (t i) - z‖ < r} := by
    ext b
    simp only [mem_ofPred_eq]
    exact (σ.surjective.forall (p := fun i => ‖b (t i) - z‖ < r)).symm
  change planarBrownianMotion x {b | ∀ i, ‖b (t (σ i)) - z‖ < r} ≤ _ at h
  rw [hsets] at h
  have hs : (∏ i : Fin n, ENNReal.ofReal ((2 / Real.pi) ^ q * (2 * r) ^ (2 * q) *
      |(t (σ i.succ) : ℝ) - (t (σ i.castSucc) : ℝ)| ^ (-q))) ≤
      ∑ τ : Equiv.Perm (Fin (n + 1)), ∏ i : Fin n,
        ENNReal.ofReal ((2 / Real.pi) ^ q * (2 * r) ^ (2 * q) *
          |(t (τ i.succ) : ℝ) - (t (τ i.castSucc) : ℝ)| ^ (-q)) := by
    apply Finset.single_le_sum (f := fun τ : Equiv.Perm (Fin (n + 1)) =>
      ∏ i : Fin n, ENNReal.ofReal ((2 / Real.pi) ^ q * (2 * r) ^ (2 * q) *
        |(t (τ i.succ) : ℝ) - (t (τ i.castSucc) : ℝ)| ^ (-q)))
    · intro τ hτ
      exact bot_le
    · exact Finset.mem_univ σ
  exact h.trans (by simpa only [Function.comp_apply] using hs)

/-- A finite independent sample from an atomless probability measure has distinct values. -/
theorem ae_injective_pi_of_atomless (n : ℕ) (ν : Measure ℝ≥0) [IsProbabilityMeasure ν] [NullSingletonClass ν] :
    ∀ᵐ t : Fin n → ℝ≥0 ∂(Measure.pi (fun _ : Fin n => ν)), Function.Injective t := by
  classical
  let μ : Measure (Fin n → ℝ≥0) := Measure.pi (fun _ : Fin n => ν)
  have hi : iIndepFun (fun i (t : Fin n → ℝ≥0) => t i) μ :=
    iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
  have hd : (ν.prod ν) (Set.diagonal ℝ≥0) = 0 := by
    apply Measure.measure_prod_null_of_ae_null measurableSet_diagonal
    filter_upwards [] with t
    simp [Set.diagonal]
  have hpair (i j : Fin n) (hij : i ≠ j) : ∀ᵐ t ∂μ, t i ≠ t j := by
    have hmap : μ.map (fun t => (t i, t j)) = ν.prod ν := by
      rw [IndepFun.map_prod_eq_prod_map_map (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable (hi.indepFun hij)]
      rw [(measurePreserving_eval (fun _ : Fin n => ν) i).map_eq,
        (measurePreserving_eval (fun _ : Fin n => ν) j).map_eq]
    have h := measure_eq_zero_iff_ae_notMem.1 hd
    have hm : AEMeasurable (fun t : Fin n → ℝ≥0 => (t i, t j)) μ := by fun_prop
    have hh := ae_of_ae_map hm (hmap.symm ▸ h)
    simpa [Set.diagonal] using hh
  have h : ∀ᵐ t ∂μ, ∀ i j : Fin n, i ≠ j → t i ≠ t j := by
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro j
    by_cases hij : i = j
    · simp [hij]
    · exact (hpair i j hij).mono (fun _ ht _ => ht)
  filter_upwards [h] with t ht i j hij
  by_contra hne
  exact ht i j hne hij

/-- Product unit-time Lebesgue measure gives distinct times almost everywhere. -/
theorem ae_injective_unit_time_pi (n : ℕ) :
    let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
    ∀ᵐ t : Fin n → ℝ≥0 ∂(Measure.pi (fun _ : Fin n => ν)), Function.Injective t := by
  let ν : Measure ℝ≥0 := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  have hp : IsProbabilityMeasure ν := by
    constructor
    simp [ν, Measure.map_apply continuous_real_toNNReal.measurable]
  have ha : NullSingletonClass ν := by
    constructor
    intro t
    dsimp [ν]
    rw [Measure.map_apply continuous_real_toNNReal.measurable (measurableSet_singleton t),
      Measure.restrict_apply (continuous_real_toNNReal.measurable (measurableSet_singleton t))]
    apply measure_mono_null _ (measure_singleton (t : ℝ))
    intro z hz
    have ht := congrArg (fun v : ℝ≥0 => (v : ℝ)) hz.1
    have hz0 : 0 ≤ z := hz.2.1
    simpa [Real.toNNReal_of_nonneg hz0] using ht
  let : IsProbabilityMeasure ν := hp
  let : NullSingletonClass ν := ha
  exact ae_injective_pi_of_atomless n ν

/-- An occupation moment is bounded by the integral of the increment kernels. -/
theorem planarBrownianMotion_occupation_moment_le_kernel (x z : ℂ) {n : ℕ} {r q : ℝ} (hr : 0 < r) (hq0 : 0 < q) (hq1 : q < 1)
    (ν : Measure ℝ≥0) [IsProbabilityMeasure ν] [NullSingletonClass ν] :
    (∫⁻ b : MarkovProcess.ContinuousPath ℂ, (ν {t | ‖b t - z‖ < r}) ^ (n + 1)
      ∂(HarmonicBalls.planarBrownianMotion x)) ≤
    ∫⁻ t : Fin (n + 1) → ℝ≥0,
      ∑ σ : Equiv.Perm (Fin (n + 1)), ∏ i : Fin n,
        ENNReal.ofReal ((2 / Real.pi) ^ q * (2 * r) ^ (2 * q) *
          |(t (σ i.succ) : ℝ) - (t (σ i.castSucc) : ℝ)| ^ (-q))
      ∂(Measure.pi (fun _ : Fin (n + 1) => ν)) := by
  rw [planarBrownianMotion_occupation_moment_eq]
  apply lintegral_mono_ae
  filter_upwards [ae_injective_pi_of_atomless (n + 1) ν] with t ht
  exact planarBrownianMotion_joint_ball_le_sum_permutations x z t ht hr hq0 hq1


/-- The subcritical time kernel has uniformly bounded unit-interval integrals. -/
theorem exists_uniform_unit_interval_rpow_bound {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    ∃ K : ℝ≥0∞, K < ∞ ∧ ∀ y ∈ Icc (0 : ℝ) 1,
      (∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal (|t - y| ^ (-q))) ≤ K := by
  let K : ℝ≥0∞ := ENNReal.ofReal 2 ^ ((1 : ℝ) - q) *
    ∫⁻ v in ball (0 : ℝ) 1, ‖v‖ₑ ^ (-q)
  have hk : K < ∞ := by
    dsimp [K]
    apply ENNReal.mul_lt_top
    · exact ENNReal.rpow_lt_top_of_nonneg (by linarith) ENNReal.ofReal_ne_top
    · apply LatticeProb.PegdenSmart.lintegral_ball_enorm_rpow_lt_top volume
      simp only [Module.finrank_self, Nat.cast_one]
      linarith
  refine ⟨K, hk, ?_⟩
  intro y hy
  have hsub : Icc (0 : ℝ) 1 ⊆ ball y 2 := by
    intro t ht
    rw [Metric.mem_ball, Real.dist_eq]
    rw [abs_lt]
    constructor <;> linarith [ht.1, ht.2, hy.1, hy.2]
  calc
    _ ≤ ∫⁻ t in Icc (0 : ℝ) 1, ‖t - y‖ₑ ^ (-q) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_of_ae (volume.ae_ne y)] with t ht
      have hpos : 0 < ‖t - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr ht)
      change ENNReal.ofReal (‖t - y‖ ^ (-q)) ≤ ‖t - y‖ₑ ^ (-q)
      rw [← ofReal_norm, ENNReal.ofReal_rpow_of_pos hpos]
    _ ≤ ∫⁻ t in ball y 2, ‖t - y‖ₑ ^ (-q) := lintegral_mono_set hsub
    _ = K := by
      rw [LatticeProb.PegdenSmart.lintegral_ball_enorm_sub_rpow volume y (by norm_num)]
      simp [K, Module.finrank_self, sub_eq_add_neg]


/-- The unit-time measure has uniformly bounded subcritical kernel integrals. -/
theorem exists_uniform_unit_time_rpow_bound {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    ∃ K : ℝ≥0∞, K < ∞ ∧ ∀ y : ℝ≥0, (y : ℝ) ≤ 1 →
      (∫⁻ t : ℝ≥0, ENNReal.ofReal (|(t : ℝ) - (y : ℝ)| ^ (-q))
        ∂(Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1)))) ≤ K := by
  obtain ⟨K, hK, hbound⟩ := exists_uniform_unit_interval_rpow_bound hq0 hq1
  refine ⟨K, hK, ?_⟩
  intro y hy
  have hm : Measurable (fun t : ℝ≥0 => ENNReal.ofReal (|(t : ℝ) - (y : ℝ)| ^ (-q))) := by
    fun_prop
  rw [lintegral_map hm continuous_real_toNNReal.measurable]
  have heq : (∫⁻ t : ℝ, ENNReal.ofReal (|((Real.toNNReal t : ℝ≥0) : ℝ) - (y : ℝ)| ^ (-q))
      ∂(volume.restrict (Icc (0 : ℝ) 1))) =
      ∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal (|t - (y : ℝ)| ^ (-q)) := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    simp [Real.toNNReal_of_nonneg ht.1]
  rw [heq]
  exact hbound (y : ℝ) ⟨y.2, hy⟩


/-- Iterated integration of a nonnegative kernel along a chain. -/
noncomputable def kernelChainIntegral {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (k : α → α → ℝ≥0∞) : ℕ → α → ℝ≥0∞
  | 0, _ => 1
  | n + 1, x => ∫⁻ y, k y x * kernelChainIntegral μ k n y ∂μ

/-- A uniform one-step bound controls all iterated chain integrals. -/
theorem kernelChainIntegral_le {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (k : α → α → ℝ≥0∞) (S : Set α) (K : ℝ≥0∞)
    (hk : ∀ x, Measurable (fun y => k y x))
    (hS : ∀ᵐ y ∂μ, y ∈ S)
    (hK : ∀ x ∈ S, (∫⁻ y, k y x ∂μ) ≤ K) :
    ∀ n x, x ∈ S → kernelChainIntegral μ k n x ≤ K ^ n := by
  intro n
  induction n with
  | zero => intro x hx; simp [kernelChainIntegral]
  | succ n ih =>
      intro x hx
      calc
        kernelChainIntegral μ k (n + 1) x =
            ∫⁻ y, k y x * kernelChainIntegral μ k n y ∂μ := rfl
        _ ≤ ∫⁻ y, k y x * K ^ n ∂μ := by
          apply lintegral_mono_ae
          filter_upwards [hS] with y hy
          exact mul_le_mul_right (ih y hy) _
        _ ≤ (∫⁻ y, k y x ∂μ) * K ^ n := (lintegral_mul_const _ (hk x)).le
        _ ≤ K * K ^ n := mul_le_mul_left (hK x hx) _
        _ = K ^ (n + 1) := by rw [pow_succ, mul_comm]

/-- Product of a kernel along a finite chain starting at a fixed point. -/
noncomputable def kernelChainProduct {α : Type*} (k : α → α → ℝ≥0∞) :
    (n : ℕ) → α → (Fin n → α) → ℝ≥0∞
  | 0, _, _ => 1
  | n + 1, x, t => k (t 0) x * kernelChainProduct k n (t 0) (fun i => t i.succ)

/-- The finite chain product of a measurable kernel is measurable. -/
theorem measurable_kernelChainProduct {α : Type*} [MeasurableSpace α]
    (k : α → α → ℝ≥0∞) (hk : Measurable (fun p : α × α => k p.1 p.2)) :
    ∀ n, Measurable (fun p : α × (Fin n → α) => kernelChainProduct k n p.1 p.2) := by
  intro n
  induction n with
  | zero => simp [kernelChainProduct]
  | succ n ih =>
      simp only [kernelChainProduct]
      apply Measurable.mul
      · have hm : Measurable (fun p : α × (Fin (n + 1) → α) => (p.2 0, p.1)) := by fun_prop
        simpa only [Function.comp_def] using hk.comp hm
      · have hm : Measurable (fun p : α × (Fin (n + 1) → α) =>
            (p.2 0, fun i : Fin n => p.2 i.succ)) := by fun_prop
        simpa only [Function.comp_def] using ih.comp hm

/-- The integral over a product space equals the iterated chain integral. -/
theorem lintegral_kernelChainProduct {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (k : α → α → ℝ≥0∞)
    (hk : Measurable (fun p : α × α => k p.1 p.2)) :
    ∀ n x, (∫⁻ t : Fin n → α, kernelChainProduct k n x t ∂(Measure.pi (fun _ => μ))) =
      kernelChainIntegral μ k n x := by
  intro n
  induction n with
  | zero =>
      intro x
      simp [kernelChainProduct, kernelChainIntegral]
  | succ n ih =>
      intro x
      let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => α) 0).symm
      have hp := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0).symm
      rw [MeasurePreserving.lintegral_map_equiv _ e hp]
      have he : (fun p : α × (Fin n → α) => kernelChainProduct k (n + 1) x (e p)) =
          fun p => k p.1 x * kernelChainProduct k n p.1 p.2 := by
        funext p
        simp [kernelChainProduct, e, MeasurableEquiv.piFinSuccAbove_symm_apply,
          Fin.insertNthEquiv]
      rw [he]
      have hm : Measurable (fun p : α × (Fin n → α) => k p.1 x * kernelChainProduct k n p.1 p.2) := by
        exact (hk.comp (measurable_fst.prodMk measurable_const)).mul (measurable_kernelChainProduct k hk n)
      rw [lintegral_prod _ hm.aemeasurable]
      simp only [kernelChainIntegral]
      congr 1
      funext y
      have hm' : Measurable (fun t : Fin n → α => kernelChainProduct k n y t) := by
        simpa only [Function.comp_def, id_eq] using
          (measurable_kernelChainProduct k hk n).comp (measurable_const.prodMk measurable_id)
      rw [lintegral_const_mul _ hm']
      rw [ih]

/-- Subcritical time-kernel chain integrals have uniform geometric bounds. -/
theorem exists_unit_time_chain_kernel_bound {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
    let k : ℝ≥0 → ℝ≥0 → ℝ≥0∞ :=
      fun t y => ENNReal.ofReal (|(t : ℝ) - (y : ℝ)| ^ (-q))
    ∃ K : ℝ≥0∞, K < ∞ ∧ ∀ (n : ℕ) (y : ℝ≥0), (y : ℝ) ≤ 1 →
      (∫⁻ t : Fin n → ℝ≥0, kernelChainProduct k n y t ∂(Measure.pi (fun _ => ν))) ≤ K ^ n := by
  let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  let k : ℝ≥0 → ℝ≥0 → ℝ≥0∞ :=
    fun t y => ENNReal.ofReal (|(t : ℝ) - (y : ℝ)| ^ (-q))
  have hp : IsProbabilityMeasure ν := by
    constructor
    simp [ν, Measure.map_apply continuous_real_toNNReal.measurable]
  let : IsProbabilityMeasure ν := hp
  have hs : ∀ᵐ y ∂ν, y ∈ Iic (1 : ℝ≥0) := by
    dsimp [ν]
    change ∀ᵐ y ∂(Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))), y ≤ 1
    apply (ae_map_iff continuous_real_toNNReal.measurable.aemeasurable
      (measurableSet_le measurable_id measurable_const)).2
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    change Real.toNNReal y ≤ 1
    exact Real.toNNReal_le_iff_le_coe.mpr (by simpa using hy.2)
  have hk : Measurable (fun p : ℝ≥0 × ℝ≥0 => k p.1 p.2) := by
    dsimp [k]
    fun_prop
  obtain ⟨K, hK, hbound⟩ := exists_uniform_unit_time_rpow_bound hq0 hq1
  refine ⟨K, hK, ?_⟩
  intro n y hy
  rw [lintegral_kernelChainProduct ν k hk]
  have hksec : ∀ x, Measurable (fun y => k y x) := by
    intro x
    change Measurable (fun y : ℝ≥0 => ENNReal.ofReal (|(y : ℝ) - (x : ℝ)| ^ (-q)))
    fun_prop
  have hKS : ∀ x ∈ Iic (1 : ℝ≥0), (∫⁻ y, k y x ∂ν) ≤ K := by
    intro x hx
    exact hbound x (by exact_mod_cast hx)
  exact kernelChainIntegral_le ν k (Iic 1) K hksec hs hKS n y (by exact_mod_cast hy)


/-- A chain product is the product over consecutive coordinates. -/
theorem kernelChainProduct_eq_prod {α : Type*} (k : α → α → ℝ≥0∞) :
    ∀ (n : ℕ) (t : Fin (n + 1) → α),
      kernelChainProduct k n (t 0) (fun i => t i.succ) =
        ∏ i : Fin n, k (t i.succ) (t i.castSucc) := by
  intro n
  induction n with
  | zero => intro t; simp [kernelChainProduct]
  | succ n ih =>
      intro t
      rw [Fin.prod_univ_succ]
      simp only [kernelChainProduct, Fin.succ_zero_eq_one, Fin.castSucc_zero]
      have h := ih (fun i => t i.succ)
      simp only [Fin.succ_zero_eq_one] at h
      rw [h]
      congr 1

/-- Uniform one-step bounds control the product over an entire random chain. -/
theorem lintegral_chain_prod_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (k : α → α → ℝ≥0∞) (S : Set α) (K : ℝ≥0∞)
    (hk : Measurable (fun p : α × α => k p.1 p.2))
    (hS : ∀ᵐ y ∂μ, y ∈ S)
    (hK : ∀ x ∈ S, (∫⁻ y, k y x ∂μ) ≤ K) (n : ℕ) :
    (∫⁻ t : Fin (n + 1) → α, ∏ i : Fin n, k (t i.succ) (t i.castSucc)
      ∂(Measure.pi (fun _ => μ))) ≤ K ^ n := by
  have hksec : ∀ x, Measurable (fun y => k y x) := by
    intro x
    have hm : Measurable (fun y : α => (y, x)) := by fun_prop
    simpa only [Function.comp_def] using hk.comp hm
  calc
    _ = ∫⁻ t : Fin (n + 1) → α,
        kernelChainProduct k n (t 0) (fun i => t i.succ) ∂(Measure.pi (fun _ => μ)) := by
      congr 1; funext t; exact (kernelChainProduct_eq_prod k n t).symm
    _ = ∫⁻ p : α × (Fin n → α), kernelChainProduct k n p.1 p.2
        ∂(μ.prod (Measure.pi (fun _ => μ))) := by
      let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => α) 0).symm
      have hp := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0).symm
      rw [MeasurePreserving.lintegral_map_equiv _ e hp]
      congr 1
    _ = ∫⁻ y, ∫⁻ t : Fin n → α, kernelChainProduct k n y t
        ∂(Measure.pi (fun _ => μ)) ∂μ := by
      rw [lintegral_prod _ (measurable_kernelChainProduct k hk n).aemeasurable]
    _ ≤ ∫⁻ _y, K ^ n ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hS] with y hy
      rw [lintegral_kernelChainProduct μ k hk n y]
      exact kernelChainIntegral_le μ k S K hksec hS hK n y hy
    _ = K ^ n := by simp


/-- The chain bound is invariant under permutation of the coordinates. -/
theorem lintegral_chain_perm_prod_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (k : α → α → ℝ≥0∞) (S : Set α) (K : ℝ≥0∞)
    (hk : Measurable (fun p : α × α => k p.1 p.2)) (hS : ∀ᵐ y ∂μ, y ∈ S)
    (hK : ∀ x ∈ S, (∫⁻ y, k y x ∂μ) ≤ K) (n : ℕ) (σ : Equiv.Perm (Fin (n + 1))) :
    (∫⁻ t : Fin (n + 1) → α, ∏ i : Fin n, k (t (σ i.succ)) (t (σ i.castSucc))
      ∂(Measure.pi (fun _ => μ))) ≤ K ^ n := by
  have h := lintegral_chain_prod_le μ k S K hk hS hK n
  let e := MeasurableEquiv.piCongrLeft (fun _ : Fin (n + 1) => α) σ
  have hp := measurePreserving_piCongrLeft (fun _ : Fin (n + 1) => μ) σ
  have he : (∫⁻ t : Fin (n + 1) → α, ∏ i : Fin n, k (t (σ i.succ)) (t (σ i.castSucc))
      ∂(Measure.pi (fun _ => μ))) =
      ∫⁻ t : Fin (n + 1) → α, ∏ i : Fin n, k (t i.succ) (t i.castSucc)
      ∂(Measure.pi (fun _ => μ)) := by
    rw [MeasurePreserving.lintegral_map_equiv _ e hp]
    congr 1
    funext t
    simp [e, MeasurableEquiv.piCongrLeft_apply_apply]
  exact he.le.trans h

/-- The sum of all permuted chain integrals is bounded by their number. -/
theorem lintegral_sum_chain_perm_prod_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (k : α → α → ℝ≥0∞) (S : Set α) (K : ℝ≥0∞)
    (hk : Measurable (fun p : α × α => k p.1 p.2)) (hS : ∀ᵐ y ∂μ, y ∈ S)
    (hK : ∀ x ∈ S, (∫⁻ y, k y x ∂μ) ≤ K) (n : ℕ) :
    (∫⁻ t : Fin (n + 1) → α, ∑ σ : Equiv.Perm (Fin (n + 1)),
      ∏ i : Fin n, k (t (σ i.succ)) (t (σ i.castSucc)) ∂(Measure.pi (fun _ => μ))) ≤
      (Fintype.card (Equiv.Perm (Fin (n + 1))) : ℝ≥0∞) * K ^ n := by
  classical
  have hm (σ : Equiv.Perm (Fin (n + 1))) : Measurable
      (fun t : Fin (n + 1) → α => ∏ i : Fin n, k (t (σ i.succ)) (t (σ i.castSucc))) := by
    apply Finset.measurable_prod
    intro i hi
    have hp : Measurable (fun t : Fin (n + 1) → α => (t (σ i.succ), t (σ i.castSucc))) := by fun_prop
    simpa only [Function.comp_def] using hk.comp hp
  rw [lintegral_finsetSum Finset.univ (fun σ hσ => hm σ)]
  calc
    _ ≤ ∑ _σ : Equiv.Perm (Fin (n + 1)), K ^ n := by
      apply Finset.sum_le_sum
      intro σ hσ
      exact lintegral_chain_perm_prod_le μ k S K hk hS hK n σ
    _ = _ := by simp


/-- All unit-time occupation moments have bounds uniform in the start and centre. -/
theorem planarBrownianMotion_occupation_moment_bound {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
    ∃ K : ℝ≥0∞, K < ∞ ∧ ∀ (x z : ℂ) (n : ℕ) (r : ℝ), 0 < r →
      (∫⁻ b : ContinuousPath ℂ, (ν {t | ‖b t - z‖ < r}) ^ (n + 1)
        ∂(planarBrownianMotion x)) ≤
      (Fintype.card (Equiv.Perm (Fin (n + 1))) : ℝ≥0∞) *
        (ENNReal.ofReal ((2 / Real.pi) ^ q * (2 * r) ^ (2 * q)) * K) ^ n := by
  let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  have hp : IsProbabilityMeasure ν := by
    constructor
    simp [ν, Measure.map_apply continuous_real_toNNReal.measurable]
  let : IsProbabilityMeasure ν := hp
  have ha : NullSingletonClass ν := by
    constructor
    intro t
    dsimp [ν]
    rw [Measure.map_apply continuous_real_toNNReal.measurable (measurableSet_singleton t),
      Measure.restrict_apply (continuous_real_toNNReal.measurable (measurableSet_singleton t))]
    apply measure_mono_null _ (measure_singleton (t : ℝ))
    intro z hz
    have ht := congrArg (fun v : ℝ≥0 => (v : ℝ)) hz.1
    have hz0 : 0 ≤ z := hz.2.1
    simpa [Real.toNNReal_of_nonneg hz0] using ht
  let : NullSingletonClass ν := ha
  have hs : ∀ᵐ y ∂ν, y ∈ Iic (1 : ℝ≥0) := by
    dsimp [ν]
    change ∀ᵐ y ∂(Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))), y ≤ 1
    apply (ae_map_iff continuous_real_toNNReal.measurable.aemeasurable
      (measurableSet_le measurable_id measurable_const)).2
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    change Real.toNNReal y ≤ 1
    exact Real.toNNReal_le_iff_le_coe.mpr (by simpa using hy.2)
  obtain ⟨K, hK, hbound⟩ := exists_uniform_unit_time_rpow_bound hq0 hq1
  refine ⟨K, hK, ?_⟩
  intro x z n r hr
  let A : ℝ := (2 / Real.pi) ^ q * (2 * r) ^ (2 * q)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let k : ℝ≥0 → ℝ≥0 → ℝ≥0∞ :=
    fun t y => ENNReal.ofReal (A * |(t : ℝ) - (y : ℝ)| ^ (-q))
  have hk : Measurable (fun p : ℝ≥0 × ℝ≥0 => k p.1 p.2) := by
    dsimp [k]; fun_prop
  have hK' : ∀ y ∈ Iic (1 : ℝ≥0), (∫⁻ t, k t y ∂ν) ≤ ENNReal.ofReal A * K := by
    intro y hy
    have hm : Measurable (fun t : ℝ≥0 => ENNReal.ofReal (|(t : ℝ) - (y : ℝ)| ^ (-q))) := by fun_prop
    have heq : (∫⁻ t, k t y ∂ν) = ENNReal.ofReal A *
        (∫⁻ t : ℝ≥0, ENNReal.ofReal (|(t : ℝ) - (y : ℝ)| ^ (-q)) ∂ν) := by
      simp only [k, ENNReal.ofReal_mul hA, lintegral_const_mul _ hm]
    rw [heq]
    exact mul_le_mul_right (hbound y (by exact_mod_cast hy)) _
  have h := planarBrownianMotion_occupation_moment_le_kernel x z (n := n) hr hq0 hq1 ν
  have hh := lintegral_sum_chain_perm_prod_le ν k (Iic 1) (ENNReal.ofReal A * K) hk hs hK' n
  exact h.trans hh


/-- Occupation moments bound the probability of a large ball occupation. -/
theorem planarBrownianMotion_occupation_tail_bound {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
    ∃ K : ℝ≥0∞, K < ∞ ∧ ∀ (x z : ℂ) (n : ℕ) (r : ℝ), 0 < r →
      ∀ ε : ℝ≥0∞, ε ≠ 0 → ε ≠ ∞ →
      planarBrownianMotion x {b | ε ≤ ν {t | ‖b t - z‖ < r}} ≤
      ((Fintype.card (Equiv.Perm (Fin (n + 1))) : ℝ≥0∞) *
        (ENNReal.ofReal ((2 / Real.pi) ^ q * (2 * r) ^ (2 * q)) * K) ^ n) / ε ^ (n + 1) := by
  let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  obtain ⟨K, hK, hmoment⟩ := planarBrownianMotion_occupation_moment_bound hq0 hq1
  refine ⟨K, hK, ?_⟩
  intro x z n r hr ε hε0 hεtop
  have hm : Measurable (fun b : ContinuousPath ℂ => (ν {t | ‖b t - z‖ < r}) ^ (n + 1)) :=
    (measurable_ball_occupation z r ν).pow_const _
  calc
    _ ≤ planarBrownianMotion x {b | ε ^ (n + 1) ≤ (ν {t | ‖b t - z‖ < r}) ^ (n + 1)} := by
      apply measure_mono
      intro b hb
      change ε ≤ ν {t | ‖b t - z‖ < r} at hb
      exact pow_le_pow_left₀ (show (0 : ℝ≥0∞) ≤ ε from zero_le) hb _
    _ ≤ (∫⁻ b : ContinuousPath ℂ, (ν {t | ‖b t - z‖ < r}) ^ (n + 1)
        ∂(planarBrownianMotion x)) / ε ^ (n + 1) :=
      meas_ge_le_lintegral_div hm.aemeasurable (pow_ne_zero _ hε0) (ENNReal.pow_ne_top hεtop)
    _ ≤ _ := by gcongr; exact hmoment x z n r hr


/-- A finite family of balls satisfies a uniform occupation tail bound. -/
theorem planarBrownianMotion_occupation_finite_union_bound {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
    ∃ K : ℝ≥0∞, K < ∞ ∧ ∀ (x : ℂ) (G : Finset ℂ) (n : ℕ) (r : ℝ), 0 < r →
      ∀ ε : ℝ≥0∞, ε ≠ 0 → ε ≠ ∞ →
      planarBrownianMotion x {b | ∃ z ∈ G, ε ≤ ν {t | ‖b t - z‖ < r}} ≤
      (G.card : ℝ≥0∞) * (((Fintype.card (Equiv.Perm (Fin (n + 1))) : ℝ≥0∞) *
        (ENNReal.ofReal ((2 / Real.pi) ^ q * (2 * r) ^ (2 * q)) * K) ^ n) / ε ^ (n + 1)) := by
  let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  obtain ⟨K, hK, htail⟩ := planarBrownianMotion_occupation_tail_bound hq0 hq1
  refine ⟨K, hK, ?_⟩
  intro x G n r hr ε hε0 hεtop
  let R := ((Fintype.card (Equiv.Perm (Fin (n + 1))) : ℝ≥0∞) *
        (ENNReal.ofReal ((2 / Real.pi) ^ q * (2 * r) ^ (2 * q)) * K) ^ n) / ε ^ (n + 1)
  calc
    _ = planarBrownianMotion x (⋃ z ∈ G, {b | ε ≤ ν {t | ‖b t - z‖ < r}}) := by
      congr 1; ext b; simp [ν]
    _ ≤ ∑ z ∈ G, planarBrownianMotion x {b | ε ≤ ν {t | ‖b t - z‖ < r}} :=
      measure_biUnion_finset_le G _
    _ ≤ ∑ _z ∈ G, R := by
      apply Finset.sum_le_sum
      intro z hz
      exact htail x z n r hr ε hε0 hεtop
    _ = _ := by simp [R]


/-- Summable occupation tails give eventual bounds simultaneously on each finite set. -/
theorem planarBrownianMotion_occupation_eventually_lt_of_summable {q : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) :
    let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
    ∃ K : ℝ≥0∞, K < ∞ ∧ ∀ (x : ℂ) (G : ℕ → Finset ℂ) (n : ℕ)
      (r : ℕ → ℝ) (ε : ℕ → ℝ≥0∞),
      (∀ j, 0 < r j) → (∀ j, ε j ≠ 0) → (∀ j, ε j ≠ ∞) →
      (∑' j, ((G j).card : ℝ≥0∞) *
        (((Fintype.card (Equiv.Perm (Fin (n + 1))) : ℝ≥0∞) *
          (ENNReal.ofReal ((2 / Real.pi) ^ q * (2 * r j) ^ (2 * q)) * K) ^ n) /
            ε j ^ (n + 1))) ≠ ∞ →
      ∀ᵐ b ∂(planarBrownianMotion x), ∀ᶠ j in Filter.atTop, ∀ z ∈ G j,
        ν {t | ‖b t - z‖ < r j} < ε j := by
  let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  obtain ⟨K, hK, hbound⟩ := planarBrownianMotion_occupation_finite_union_bound hq0 hq1
  refine ⟨K, hK, ?_⟩
  intro x G n r ε hr hε0 hεtop hsum
  let E : ℕ → Set (ContinuousPath ℂ) :=
    fun j => {b | ∃ z ∈ G j, ε j ≤ ν {t | ‖b t - z‖ < r j}}
  have hsum' : (∑' j, planarBrownianMotion x (E j)) ≠ ∞ := by
    apply ne_top_of_le_ne_top hsum
    apply ENNReal.tsum_le_tsum
    intro j
    exact hbound x (G j) n (r j) (hr j) (ε j) (hε0 j) (hεtop j)
  filter_upwards [ae_eventually_notMem hsum'] with b hb
  filter_upwards [hb] with j hj z hz
  exact lt_of_not_ge (fun h => hj ⟨z, hz, h⟩)


/-- A finite square grid of mesh size `1 / m` on a bounded region. -/
noncomputable def squareGrid (N m : ℕ) : Finset ℂ :=
  ((Finset.range (2 * N * m + 1)).product (Finset.range (2 * N * m + 1))).image
    (fun p => Complex.mk ((p.1 : ℝ) / m - N) ((p.2 : ℝ) / m - N))

/-- The number of grid points is bounded by the number of pairs of coordinates. -/
theorem squareGrid_card_le (N m : ℕ) :
    (squareGrid N m).card ≤ (2 * N * m + 1) ^ 2 := by
  classical
  calc
    _ ≤ ((Finset.range (2 * N * m + 1)).product (Finset.range (2 * N * m + 1))).card :=
      Finset.card_image_le
    _ = _ := by simp [pow_two]

/-- Every point of a bounded interval is within one mesh of a grid coordinate. -/
theorem exists_grid_coordinate (N m : ℕ) (hm : 0 < m) (x : ℝ)
    (hx1 : -(N : ℝ) ≤ x) (hx2 : x ≤ N) :
    ∃ i ∈ Finset.range (2 * N * m + 1), |x - ((i : ℝ) / m - N)| < 1 / m := by
  let i := ⌊(x + N) * m⌋₊
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have ha : 0 ≤ (x + N) * m := mul_nonneg (by linarith) hm'.le
  have hf : (i : ℝ) ≤ (x + N) * m := Nat.floor_le ha
  have hf' : (x + N) * m < (i : ℝ) + 1 := Nat.lt_floor_add_one _
  have hi : i ≤ 2 * N * m := by
    have hf'' : (i : ℝ) ≤ (2 * N * m : ℕ) := by
      push_cast
      nlinarith
    exact_mod_cast hf''
  refine ⟨i, Finset.mem_range.mpr (by omega), ?_⟩
  have hnonneg : 0 ≤ x - ((i : ℝ) / m - N) := by
    have hdiv : (i : ℝ) / m ≤ x + N := (div_le_iff₀ hm').2 hf
    linarith
  rw [abs_of_nonneg hnonneg]
  apply (lt_div_iff₀ hm').2
  have hcancel : ((i : ℝ) / m) * m = i := div_mul_cancel₀ _ (ne_of_gt hm')
  nlinarith

/-- The square grid covers every bounded complex ball at twice its mesh size. -/
theorem squareGrid_covers (N m : ℕ) (hm : 0 < m) (z : ℂ) (hz : ‖z‖ ≤ N) :
    ∃ w ∈ squareGrid N m, dist z w < 2 / m := by
  have hre := (Complex.abs_re_le_norm z).trans hz
  have him := (Complex.abs_im_le_norm z).trans hz
  obtain ⟨i, hi, hdi⟩ := exists_grid_coordinate N m hm z.re (abs_le.mp hre).1 (abs_le.mp hre).2
  obtain ⟨j, hj, hdj⟩ := exists_grid_coordinate N m hm z.im (abs_le.mp him).1 (abs_le.mp him).2
  let w := Complex.mk ((i : ℝ) / m - N) ((j : ℝ) / m - N)
  refine ⟨w, ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨(i, j), Finset.mem_product.mpr ⟨hi, hj⟩, rfl⟩
  · rw [dist_eq_norm]
    have h := Complex.norm_le_abs_re_add_abs_im (z - w)
    change ‖z - w‖ ≤ |z.re - ((i : ℝ) / m - N)| + |z.im - ((j : ℝ) / m - N)| at h
    rw [show (2 : ℝ) / m = 1 / m + 1 / m by ring]
    linarith


/-- Dyadic square grids have quadratic growth in the inverse mesh. -/
theorem squareGrid_dyadic_card_le (N k : ℕ) :
    (squareGrid N (2 ^ (k + 1))).card ≤ (4 * N + 1) ^ 2 * (2 ^ k) ^ 2 := by
  have hp : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by norm_num)
  have hh : 2 * N * 2 ^ (k + 1) + 1 ≤ (4 * N + 1) * 2 ^ k := by
    rw [pow_succ]
    nlinarith
  calc
    _ ≤ (2 * N * 2 ^ (k + 1) + 1) ^ 2 := squareGrid_card_le N _
    _ ≤ ((4 * N + 1) * 2 ^ k) ^ 2 := Nat.pow_le_pow_left hh _
    _ = _ := mul_pow _ _ _

/-- Dyadic square grids cover bounded balls at the corresponding dyadic scale. -/
theorem squareGrid_dyadic_covers (N k : ℕ) (z : ℂ) (hz : ‖z‖ ≤ N) :
    ∃ w ∈ squareGrid N (2 ^ (k + 1)), dist z w < (2 : ℝ)⁻¹ ^ k := by
  obtain ⟨w, hw, hd⟩ := squareGrid_covers N (2 ^ (k + 1)) (by positivity) z hz
  refine ⟨w, hw, ?_⟩
  convert hd using 1
  push_cast
  rw [pow_succ]
  have h : (2 : ℝ) ^ k ≠ 0 := by positivity
  field_simp
  rw [show (1 / 2 : ℝ) ^ k = ((2 : ℝ) ^ k)⁻¹ by rw [one_div, inv_pow], inv_mul_cancel₀ h]


/-- Bounds on enlarged grid-centred balls extend to every centre in the region. -/
theorem occupation_le_of_squareGrid (ν : Measure ℝ≥0) (b : ContinuousPath ℂ)
    (N k : ℕ) (M : ℝ≥0∞)
    (h : ∀ w ∈ squareGrid N (2 ^ (k + 1)),
      ν {t | ‖b t - w‖ < 2 * (2 : ℝ)⁻¹ ^ k} ≤ M)
    (z : ℂ) (hz : ‖z‖ ≤ N) :
    ν {t | ‖b t - z‖ < (2 : ℝ)⁻¹ ^ k} ≤ M := by
  obtain ⟨w, hw, hd⟩ := squareGrid_dyadic_covers N k z hz
  calc
    _ ≤ ν {t | ‖b t - w‖ < 2 * (2 : ℝ)⁻¹ ^ k} := by
      apply measure_mono
      intro t ht
      have ht' : dist (b t) z < (2 : ℝ)⁻¹ ^ k := by simpa [dist_eq_norm] using ht
      have hx := dist_triangle (b t) z w
      change ‖b t - w‖ < 2 * (2 : ℝ)⁻¹ ^ k
      rw [← dist_eq_norm]
      linarith
    _ ≤ M := h w hw


/-- Summable dyadic tails imply bounds at all centres in each bounded region. -/
theorem planarBrownianMotion_dyadic_occupation_of_summable {q : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) :
    let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
    ∃ K : ℝ≥0∞, K < ∞ ∧ ∀ (x : ℂ) (N n : ℕ) (d : ℝ),
      (∑' k, ((squareGrid N (2 ^ (k + 1))).card : ℝ≥0∞) *
        (((Fintype.card (Equiv.Perm (Fin (n + 1))) : ℝ≥0∞) *
          (ENNReal.ofReal ((2 / Real.pi) ^ q * (2 * (2 * (2 : ℝ)⁻¹ ^ k)) ^ (2 * q)) * K) ^ n) /
            (ENNReal.ofReal (((2 : ℝ)⁻¹ ^ k) ^ d)) ^ (n + 1))) ≠ ∞ →
      ∀ᵐ b ∂(planarBrownianMotion x), ∀ᶠ k in Filter.atTop, ∀ z : ℂ, ‖z‖ ≤ N →
        ν {t | ‖b t - z‖ < (2 : ℝ)⁻¹ ^ k} ≤ ENNReal.ofReal (((2 : ℝ)⁻¹ ^ k) ^ d) := by
  let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  obtain ⟨K, hK, hbc⟩ := planarBrownianMotion_occupation_eventually_lt_of_summable hq0 hq1
  refine ⟨K, hK, ?_⟩
  intro x N n d hsum
  let G : ℕ → Finset ℂ := fun k => squareGrid N (2 ^ (k + 1))
  let r : ℕ → ℝ := fun k => 2 * (2 : ℝ)⁻¹ ^ k
  let ε : ℕ → ℝ≥0∞ := fun k => ENNReal.ofReal (((2 : ℝ)⁻¹ ^ k) ^ d)
  have hr : ∀ k, 0 < r k := by intro k; dsimp [r]; positivity
  have hε0 : ∀ k, ε k ≠ 0 := by
    intro k
    dsimp [ε]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (by positivity) _))
  have hεtop : ∀ k, ε k ≠ ∞ := by intro k; exact ENNReal.ofReal_ne_top
  have ha := hbc x G n r ε hr hε0 hεtop hsum
  filter_upwards [ha] with b hb
  filter_upwards [hb] with k hk z hz
  apply occupation_le_of_squareGrid ν b N k (ε k) _ z hz
  intro w hw
  exact (hk w hw).le


/-- Positive powers of the dyadic radii form a summable sequence. -/
theorem tsum_dyadic_rpow_lt_top {p : ℝ} (hp : 0 < p) :
    (∑' k : ℕ, ENNReal.ofReal (((2 : ℝ)⁻¹ ^ k) ^ p)) < ∞ := by
  have h : (2 : ℝ)⁻¹ ^ p < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hp
  have h0 : 0 ≤ (2 : ℝ)⁻¹ ^ p := Real.rpow_nonneg (by norm_num) _
  have hb : ENNReal.ofReal ((2 : ℝ)⁻¹ ^ p) < 1 := by
    exact ENNReal.ofReal_lt_one.mpr h
  have heq (k : ℕ) : ENNReal.ofReal (((2 : ℝ)⁻¹ ^ k) ^ p) =
      (ENNReal.ofReal ((2 : ℝ)⁻¹ ^ p)) ^ k := by
    rw [← Real.rpow_natCast_mul (by norm_num) k p,
      show (k : ℝ) * p = p * k by ring, Real.rpow_mul_natCast (by norm_num), ENNReal.ofReal_pow h0]
  simp_rw [heq]
  exact tsum_geometric_lt_top.mpr hb


/-- The radius-dependent part of a dyadic tail bound is a single power. -/
theorem dyadic_tail_real_factor (δ C q d : ℝ) (hδ : 0 < δ) (n : ℕ) :
    (δ⁻¹) ^ 2 * ((C * (4 * δ) ^ (2 * q)) ^ n / (δ ^ d) ^ (n + 1)) =
      (C * (4 : ℝ) ^ (2 * q)) ^ n * δ ^ ((2 * q) * n - d * (n + 1) - 2) := by
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hδ.le]
  rw [← mul_assoc C]
  rw [mul_pow, ← Real.rpow_mul_natCast hδ.le, ← Real.rpow_mul_natCast hδ.le]
  have h2 : (δ⁻¹) ^ 2 = δ ^ (-(2 : ℝ)) := by
    rw [Real.rpow_neg hδ.le]
    norm_num [inv_pow]
  rw [h2]
  calc
    _ = (C * (4 : ℝ) ^ (2 * q)) ^ n *
      ((δ ^ ((2 * q) * n) / δ ^ (d * (n + 1))) * δ ^ (-(2 : ℝ))) := by push_cast; ring
    _ = _ := by
      rw [← Real.rpow_sub hδ, ← Real.rpow_add hδ]
      congr 1

end HarmonicBalls

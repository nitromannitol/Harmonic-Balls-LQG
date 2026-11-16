import HarmonicBalls.Proofs.Potential.BrownianPairOccupationBound
import HarmonicBalls.Proofs.Sec6.PlanarIncrementBlocks
import Mathlib.Data.Fin.Tuple.Sort

/-! # Uniform-centre Brownian increment estimates

Planar Brownian increments satisfy a small-ball bound uniform in the centre.
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
end HarmonicBalls

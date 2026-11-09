import HarmonicBalls.FirstPass.S11i.CovarianceInvariance
import HarmonicBalls.FirstPass.S11i.CovarianceDecay
import HarmonicBalls.FirstPass.S11i.GFFFamily
import HarmonicBalls.FirstPass.S11i.GaussianMix
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Step 8 helper: asymptotic product factorization for the whole-plane GFF (owner n3)

Source: corrected paper, `s11-pinch:lem:mixing` (tex lines 3769-3812), the finite-dimensional factorization: for
test functions `a i` and mean-zero test functions `b j`, the joint laws of `(h, a_i)_i` and `(h, κₙ b_j)_j`
converge to the product of their laws. Proof: Lévy continuity on `EuclideanSpace ℝ (Fin (m+k))`. The
characteristic functions of the joint Gaussian vectors are explicit (`integral_exp_linComb_eq`); the covariance
between the two blocks tends to zero (`tendsto_wholePlaneGFFCov_dilate`); the diagonal blocks are constant in `n`
(covariance invariance `wholePlaneGFFCov_pairing_dilate`); the product law is the law of two independent copies
(`integral_prod_mul`).
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ProbabilityTheory

namespace HarmonicBalls

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- The covariance of two pairings of the whole-plane GFF is the Gaussian covariance `wholePlaneGFFCov`. -/
theorem cov_pairing_eq (hh : IsWholePlaneGFF P hC hcirc) {f g : ℂ → ℝ}
    (hf : IsTestFunction univ f) (hg : IsTestFunction univ g) :
    cov[fun ω => hC ω f, fun ω => hC ω g; P] =
      wholePlaneGFFCov (GFFObservable.pairing f) (GFFObservable.pairing g) :=
  hh.covariance_eq (GFFObservable.pairing f) (GFFObservable.pairing g) hf hg

/-- Pairings with test functions are centred. -/
theorem integral_pairing_eq_zero (hh : IsWholePlaneGFF P hC hcirc) {f : ℂ → ℝ}
    (hf : IsTestFunction univ f) : ∫ ω, hC ω f ∂P = 0 :=
  hh.integral_eq_zero (GFFObservable.pairing f) hf

/-- The family `a` followed by the dilated family `κₙ ∘ b`, indexed by `Fin (m + k)`. -/
noncomputable def dilAppend {m k : ℕ} (a : Fin m → ℂ → ℝ) (b : Fin k → ℂ → ℝ) (n : ℕ) :
    Fin (m + k) → ℂ → ℝ :=
  Fin.append a (fun j => dilateTest n (b j))

theorem dilAppend_isTest {m k : ℕ} {a : Fin m → ℂ → ℝ} {b : Fin k → ℂ → ℝ}
    (ha : ∀ i, IsTestFunction univ (a i)) (hb : ∀ j, IsTestFunction univ (b j)) (n : ℕ)
    (p : Fin (m + k)) : IsTestFunction univ (dilAppend a b n p) := by
  refine Fin.addCases (fun i => ?_) (fun j => ?_) p
  · simpa [dilAppend] using ha i
  · simpa [dilAppend] using isTestFunction_dilateTest (hb j) n

/-- Covariance of the block `a` with the dilated block `κₙ b` tends to zero. -/
theorem tendsto_cov_block_cross (hh : IsWholePlaneGFF P hC hcirc) {a : ℂ → ℝ} {b : ℂ → ℝ}
    (ha : IsTestFunction univ a) (hb : IsTestFunction univ b) (hb0 : ∫ x, b x = 0) :
    Tendsto (fun n : ℕ => cov[fun ω => hC ω a, fun ω => hC ω (dilateTest n b); P]) atTop (𝓝 0) :=
  Tendsto.congr (fun n => (cov_pairing_eq hh ha (isTestFunction_dilateTest hb n)).symm)
    (tendsto_wholePlaneGFFCov_dilate ha hb hb0)

/-- Covariance of two dilated blocks does not depend on the dilation index (covariance invariance). -/
theorem cov_dilated_eq (hh : IsWholePlaneGFF P hC hcirc) {b b' : ℂ → ℝ}
    (hb : IsTestFunction univ b) (hb' : IsTestFunction univ b') (hb0 : ∫ x, b x = 0)
    (hb0' : ∫ x, b' x = 0) (n : ℕ) :
    cov[fun ω => hC ω (dilateTest n b), fun ω => hC ω (dilateTest n b'); P] =
      cov[fun ω => hC ω b, fun ω => hC ω b'; P] := by
  rw [cov_pairing_eq hh (isTestFunction_dilateTest hb n) (isTestFunction_dilateTest hb' n),
    wholePlaneGFFCov_pairing_dilate hb hb' hb0 hb0' n, cov_pairing_eq hh hb hb']

/-- The quadratic form of the joint family converges to the block-diagonal quadratic form. -/
theorem tendsto_quadratic_dilAppend [IsProbabilityMeasure P] (hh : IsWholePlaneGFF P hC hcirc) {m k : ℕ} {a : Fin m → ℂ → ℝ}
    {b : Fin k → ℂ → ℝ} (ha : ∀ i, IsTestFunction univ (a i)) (hb : ∀ j, IsTestFunction univ (b j))
    (hb0 : ∀ j, ∫ x, b j x = 0) (θ : Fin (m + k) → ℝ) :
    Tendsto (fun n : ℕ => ∑ p, ∑ q, θ p * θ q *
        cov[fun ω => hC ω (dilAppend a b n p), fun ω => hC ω (dilAppend a b n q); P]) atTop
      (𝓝 ((∑ i, ∑ i', θ (Fin.castAdd k i) * θ (Fin.castAdd k i') *
          cov[fun ω => hC ω (a i), fun ω => hC ω (a i'); P]) +
        ∑ j, ∑ j', θ (Fin.natAdd m j) * θ (Fin.natAdd m j') *
          cov[fun ω => hC ω (b j), fun ω => hC ω (b j'); P])) := by
  have key : ∀ n : ℕ, (∑ p, ∑ q, θ p * θ q *
      cov[fun ω => hC ω (dilAppend a b n p), fun ω => hC ω (dilAppend a b n q); P]) =
      ((∑ i, ∑ i', θ (Fin.castAdd k i) * θ (Fin.castAdd k i') *
          cov[fun ω => hC ω (a i), fun ω => hC ω (a i'); P]) +
        ∑ j, ∑ j', θ (Fin.natAdd m j) * θ (Fin.natAdd m j') *
          cov[fun ω => hC ω (b j), fun ω => hC ω (b j'); P]) +
      ((∑ i, ∑ j, θ (Fin.castAdd k i) * θ (Fin.natAdd m j) *
          cov[fun ω => hC ω (a i), fun ω => hC ω (dilateTest n (b j)); P]) +
        ∑ j, ∑ i, θ (Fin.natAdd m j) * θ (Fin.castAdd k i) *
          cov[fun ω => hC ω (dilateTest n (b j)), fun ω => hC ω (a i); P]) := by
    intro n
    simp only [Fin.sum_univ_add, Finset.sum_add_distrib, dilAppend, Fin.append_left, Fin.append_right]
    simp only [cov_dilated_eq hh (hb _) (hb _) (hb0 _) (hb0 _) n]
    abel
  have hcross : ∀ i j, Tendsto (fun n : ℕ =>
      cov[fun ω => hC ω (a i), fun ω => hC ω (dilateTest n (b j)); P]) atTop (𝓝 0) :=
    fun i j => tendsto_cov_block_cross hh (ha i) (hb j) (hb0 j)
  have hcross' : ∀ j i, Tendsto (fun n : ℕ =>
      cov[fun ω => hC ω (dilateTest n (b j)), fun ω => hC ω (a i); P]) atTop (𝓝 0) := by
    intro j i
    exact Tendsto.congr (fun n => covariance_comm _ _) (tendsto_cov_block_cross hh (ha i) (hb j) (hb0 j))
  have hC0 : Tendsto (fun n : ℕ => (∑ i, ∑ j, θ (Fin.castAdd k i) * θ (Fin.natAdd m j) *
          cov[fun ω => hC ω (a i), fun ω => hC ω (dilateTest n (b j)); P]) +
        ∑ j, ∑ i, θ (Fin.natAdd m j) * θ (Fin.castAdd k i) *
          cov[fun ω => hC ω (dilateTest n (b j)), fun ω => hC ω (a i); P]) atTop (𝓝 0) := by
    have h1 := tendsto_finsetSum (Finset.univ : Finset (Fin m)) (fun i _ =>
      tendsto_finsetSum (Finset.univ : Finset (Fin k)) (fun j _ =>
        (hcross i j).const_mul (θ (Fin.castAdd k i) * θ (Fin.natAdd m j))))
    have h2 := tendsto_finsetSum (Finset.univ : Finset (Fin k)) (fun j _ =>
      tendsto_finsetSum (Finset.univ : Finset (Fin m)) (fun i _ =>
        (hcross' j i).const_mul (θ (Fin.natAdd m j) * θ (Fin.castAdd k i))))
    simpa using h1.add h2
  have hfin := (tendsto_const_nhds (x := (∑ i, ∑ i', θ (Fin.castAdd k i) * θ (Fin.castAdd k i') *
          cov[fun ω => hC ω (a i), fun ω => hC ω (a i'); P]) +
        ∑ j, ∑ j', θ (Fin.natAdd m j) * θ (Fin.natAdd m j') *
          cov[fun ω => hC ω (b j), fun ω => hC ω (b j'); P])).add hC0
  simp only [add_zero] at hfin
  exact hfin.congr (fun n => (key n).symm)

/-- The joint vector `(h, a_i)_i, (h, κₙ b_j)_j` as a point of `EuclideanSpace ℝ (Fin (m + k))`. -/
noncomputable def jointVec {m k : ℕ} (a : Fin m → ℂ → ℝ) (b : Fin k → ℂ → ℝ) (n : ℕ) (ω : Ω) :
    EuclideanSpace ℝ (Fin (m + k)) :=
  WithLp.toLp 2 (fun p => hC ω (dilAppend a b n p))

/-- The vector `((h₁, a_i)_i, (h₂, b_j)_j)` on two independent copies `Ω × Ω`. -/
noncomputable def jointInf {m k : ℕ} (a : Fin m → ℂ → ℝ) (b : Fin k → ℂ → ℝ) (ω : Ω × Ω) :
    EuclideanSpace ℝ (Fin (m + k)) :=
  WithLp.toLp 2 (Fin.append (fun i => hC ω.1 (a i)) (fun j => hC ω.2 (b j)))

theorem measurable_jointVec (hh : IsWholePlaneGFF P hC hcirc) {m k : ℕ} {a : Fin m → ℂ → ℝ}
    {b : Fin k → ℂ → ℝ} (ha : ∀ i, IsTestFunction univ (a i)) (hb : ∀ j, IsTestFunction univ (b j))
    (n : ℕ) : Measurable (jointVec (hC := hC) a b n) :=
  (WithLp.measurable_toLp 2 _).comp (measurable_pi_iff.2 fun p =>
    hh.measurable_pairing _ (dilAppend_isTest ha hb n p))

theorem measurable_jointInf (hh : IsWholePlaneGFF P hC hcirc) {m k : ℕ} {a : Fin m → ℂ → ℝ}
    {b : Fin k → ℂ → ℝ} (ha : ∀ i, IsTestFunction univ (a i)) (hb : ∀ j, IsTestFunction univ (b j)) :
    Measurable (jointInf (hC := hC) a b) := by
  refine (WithLp.measurable_toLp 2 _).comp (measurable_pi_iff.2 fun p => ?_)
  refine Fin.addCases (fun i => ?_) (fun j => ?_) p
  · simp only [Fin.append_left]
    exact (hh.measurable_pairing _ (ha i)).comp measurable_fst
  · simp only [Fin.append_right]
    exact (hh.measurable_pairing _ (hb j)).comp measurable_snd

theorem inner_toLp_real {N : ℕ} (v : Fin N → ℝ) (t : EuclideanSpace ℝ (Fin N)) :
    inner ℝ (WithLp.toLp 2 v) t = ∑ p, WithLp.ofLp t p * v p := by
  simp [PiLp.inner_apply, mul_comm]

/-- The law of the joint vector at index `n`, a probability measure on `EuclideanSpace ℝ (Fin (m + k))`. -/
noncomputable def lawN [IsProbabilityMeasure P] (hh : IsWholePlaneGFF P hC hcirc) {m k : ℕ}
    {a : Fin m → ℂ → ℝ} {b : Fin k → ℂ → ℝ} (ha : ∀ i, IsTestFunction univ (a i))
    (hb : ∀ j, IsTestFunction univ (b j)) (n : ℕ) :
    ProbabilityMeasure (EuclideanSpace ℝ (Fin (m + k))) :=
  ⟨P.map (jointVec a b n), (Measure.isProbabilityMeasure_map_iff (measurable_jointVec hh ha hb n).aemeasurable).2 inferInstance⟩

/-- The law of the independent-copies vector, a probability measure on `EuclideanSpace ℝ (Fin (m + k))`. -/
noncomputable def lawInf [IsProbabilityMeasure P] (hh : IsWholePlaneGFF P hC hcirc) {m k : ℕ}
    {a : Fin m → ℂ → ℝ} {b : Fin k → ℂ → ℝ} (ha : ∀ i, IsTestFunction univ (a i))
    (hb : ∀ j, IsTestFunction univ (b j)) :
    ProbabilityMeasure (EuclideanSpace ℝ (Fin (m + k))) :=
  ⟨(P.prod P).map (jointInf a b), (Measure.isProbabilityMeasure_map_iff (measurable_jointInf hh ha hb).aemeasurable).2 inferInstance⟩

theorem charFun_lawN [IsProbabilityMeasure P] (hh : IsWholePlaneGFF P hC hcirc) {m k : ℕ}
    {a : Fin m → ℂ → ℝ} {b : Fin k → ℂ → ℝ} (ha : ∀ i, IsTestFunction univ (a i))
    (hb : ∀ j, IsTestFunction univ (b j)) (n : ℕ) (t : EuclideanSpace ℝ (Fin (m + k))) :
    charFun (lawN hh ha hb n : Measure (EuclideanSpace ℝ (Fin (m + k)))) t =
      Complex.exp (-((∑ p, ∑ q, WithLp.ofLp t p * WithLp.ofLp t q *
        cov[fun ω => hC ω (dilAppend a b n p), fun ω => hC ω (dilAppend a b n q); P] : ℝ) : ℂ) / 2) := by
  have hZ := integral_exp_linComb_eq (P := P) (Z := fun p ω => hC ω (dilAppend a b n p))
    (hasGaussianLaw_pairing_family hh _ (dilAppend_isTest ha hb n))
    (fun p => integral_pairing_eq_zero hh (dilAppend_isTest ha hb n p)) (WithLp.ofLp t)
  rw [charFun_apply, show (lawN hh ha hb n : Measure (EuclideanSpace ℝ (Fin (m + k)))) =
    P.map (jointVec a b n) by unfold lawN; rfl,
    integral_map (measurable_jointVec hh ha hb n).aemeasurable
      (Continuous.aestronglyMeasurable (by fun_prop))]
  simp only [jointVec, inner_toLp_real]
  exact hZ

theorem charFun_lawInf [IsProbabilityMeasure P] (hh : IsWholePlaneGFF P hC hcirc) {m k : ℕ}
    {a : Fin m → ℂ → ℝ} {b : Fin k → ℂ → ℝ} (ha : ∀ i, IsTestFunction univ (a i))
    (hb : ∀ j, IsTestFunction univ (b j)) (t : EuclideanSpace ℝ (Fin (m + k))) :
    charFun (lawInf hh ha hb : Measure (EuclideanSpace ℝ (Fin (m + k)))) t =
      Complex.exp (-((∑ i, ∑ i', WithLp.ofLp t (Fin.castAdd k i) * WithLp.ofLp t (Fin.castAdd k i') *
          cov[fun ω => hC ω (a i), fun ω => hC ω (a i'); P] +
        ∑ j, ∑ j', WithLp.ofLp t (Fin.natAdd m j) * WithLp.ofLp t (Fin.natAdd m j') *
          cov[fun ω => hC ω (b j), fun ω => hC ω (b j'); P] : ℝ) : ℂ) / 2) := by
  have hfac : ∀ ω : Ω × Ω, Complex.exp (inner ℝ (jointInf (hC := hC) a b ω) t * Complex.I) =
      Complex.exp (((∑ i, WithLp.ofLp t (Fin.castAdd k i) * hC ω.1 (a i) : ℝ) : ℂ) * Complex.I) *
      Complex.exp (((∑ j, WithLp.ofLp t (Fin.natAdd m j) * hC ω.2 (b j) : ℝ) : ℂ) * Complex.I) := by
    intro ω
    rw [← Complex.exp_add]
    congr 1
    simp only [jointInf, inner_toLp_real, Fin.sum_univ_add, Fin.append_left, Fin.append_right]
    push_cast
    ring
  have hA := integral_exp_linComb_eq (P := P) (Z := fun i ω => hC ω (a i))
    (hasGaussianLaw_pairing_family hh a ha) (fun i => integral_pairing_eq_zero hh (ha i))
    (fun i => WithLp.ofLp t (Fin.castAdd k i))
  have hB := integral_exp_linComb_eq (P := P) (Z := fun j ω => hC ω (b j))
    (hasGaussianLaw_pairing_family hh b hb) (fun j => integral_pairing_eq_zero hh (hb j))
    (fun j => WithLp.ofLp t (Fin.natAdd m j))
  rw [charFun_apply, show (lawInf hh ha hb : Measure (EuclideanSpace ℝ (Fin (m + k)))) =
    (P.prod P).map (jointInf a b) by unfold lawInf; rfl,
    integral_map (measurable_jointInf hh ha hb).aemeasurable
      (Continuous.aestronglyMeasurable (by fun_prop))]
  have hP : ∫ ω : Ω × Ω, Complex.exp (((∑ i, WithLp.ofLp t (Fin.castAdd k i) * hC ω.1 (a i) : ℝ) : ℂ) *
      Complex.I) * Complex.exp (((∑ j, WithLp.ofLp t (Fin.natAdd m j) * hC ω.2 (b j) : ℝ) : ℂ) *
      Complex.I) ∂(P.prod P) = (∫ ω, Complex.exp (((∑ i, WithLp.ofLp t (Fin.castAdd k i) * hC ω (a i) : ℝ) : ℂ) *
      Complex.I) ∂P) * ∫ ω, Complex.exp (((∑ j, WithLp.ofLp t (Fin.natAdd m j) * hC ω (b j) : ℝ) : ℂ) *
      Complex.I) ∂P :=
    integral_prod_mul (fun ω : Ω => Complex.exp (((∑ i, WithLp.ofLp t (Fin.castAdd k i) * hC ω (a i) : ℝ) : ℂ) *
      Complex.I)) (fun ω : Ω => Complex.exp (((∑ j, WithLp.ofLp t (Fin.natAdd m j) * hC ω (b j) : ℝ) : ℂ) *
      Complex.I))
  rw [integral_congr_ae (Filter.Eventually.of_forall hfac), hP, hA, hB, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Lévy continuity for the joint laws: `Law(h, a; κₙ b) → Law(h, a) ⊗ Law(h, b)` weakly. -/
theorem tendsto_lawN_lawInf [IsProbabilityMeasure P] (hh : IsWholePlaneGFF P hC hcirc) {m k : ℕ}
    {a : Fin m → ℂ → ℝ} {b : Fin k → ℂ → ℝ} (ha : ∀ i, IsTestFunction univ (a i))
    (hb : ∀ j, IsTestFunction univ (b j)) (hb0 : ∀ j, ∫ x, b j x = 0) :
    Tendsto (fun n : ℕ => lawN hh ha hb n) atTop (𝓝 (lawInf hh ha hb)) := by
  rw [ProbabilityMeasure.tendsto_iff_tendsto_charFun]
  intro t
  have hQ := tendsto_quadratic_dilAppend hh ha hb hb0 (WithLp.ofLp t)
  have hF : Continuous (fun x : ℝ => Complex.exp (-(x : ℂ) / 2)) := by fun_prop
  simp only [charFun_lawN hh ha hb _ t, charFun_lawInf hh ha hb t]
  exact (hF.tendsto _).comp hQ

/-- Asymptotic product factorization for the whole-plane GFF (paper `lem:mixing`, finite-dimensional step):
for test functions `a i` and mean-zero test functions `b j`, bounded continuous `f, g` on the finite
families, `E[f(h,a) g(h, κₙ b)] → E[f(h,a)] E[g(h,b)]`. -/
theorem tendsto_integral_dilate_factor [IsProbabilityMeasure P] (hh : IsWholePlaneGFF P hC hcirc) {m k : ℕ}
    {a : Fin m → ℂ → ℝ} {b : Fin k → ℂ → ℝ} (ha : ∀ i, IsTestFunction univ (a i))
    (hb : ∀ j, IsTestFunction univ (b j)) (hb0 : ∀ j, ∫ x, b j x = 0)
    (f : BoundedContinuousFunction (Fin m → ℝ) ℝ) (g : BoundedContinuousFunction (Fin k → ℝ) ℝ) :
    Tendsto (fun n : ℕ => ∫ ω, f (fun i => hC ω (a i)) *
        g (fun j => hC ω (dilateTest n (b j))) ∂P) atTop
      (𝓝 ((∫ ω, f (fun i => hC ω (a i)) ∂P) * ∫ ω, g (fun j => hC ω (b j)) ∂P)) := by
  have hcont : Continuous (fun v : EuclideanSpace ℝ (Fin (m + k)) =>
      f (fun i => WithLp.ofLp v (Fin.castAdd k i)) * g (fun j => WithLp.ofLp v (Fin.natAdd m j))) := by
    refine Continuous.mul (f.continuous.comp ?_) (g.continuous.comp ?_)
    · exact continuous_pi fun i => (continuous_apply _).comp (PiLp.continuous_ofLp 2 _)
    · exact continuous_pi fun j => (continuous_apply _).comp (PiLp.continuous_ofLp 2 _)
  let F : BoundedContinuousFunction (EuclideanSpace ℝ (Fin (m + k))) ℝ := BoundedContinuousFunction.ofNormedAddCommGroup _ hcont
    (‖f‖ * ‖g‖) (fun v => by
      rw [norm_mul]
      exact mul_le_mul (f.norm_coe_le_norm _) (g.norm_coe_le_norm _) (norm_nonneg _) (norm_nonneg _))
  have hport := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1
    (tendsto_lawN_lawInf hh ha hb hb0) F
  have h1 : ∀ n : ℕ, ∫ v, F v ∂(lawN hh ha hb n : Measure (EuclideanSpace ℝ (Fin (m + k)))) =
      ∫ ω, f (fun i => hC ω (a i)) * g (fun j => hC ω (dilateTest n (b j))) ∂P := by
    intro n
    rw [show (lawN hh ha hb n : Measure (EuclideanSpace ℝ (Fin (m + k)))) = P.map (jointVec a b n) by
      unfold lawN; rfl, integral_map (measurable_jointVec hh ha hb n).aemeasurable
      (F.continuous.aestronglyMeasurable)]
    congr 1
    funext ω
    simp [F, jointVec, dilAppend, Fin.append_left, Fin.append_right]
  have h2 : ∫ v, F v ∂(lawInf hh ha hb : Measure (EuclideanSpace ℝ (Fin (m + k)))) =
      (∫ ω, f (fun i => hC ω (a i)) ∂P) * ∫ ω, g (fun j => hC ω (b j)) ∂P := by
    rw [show (lawInf hh ha hb : Measure (EuclideanSpace ℝ (Fin (m + k)))) =
      (P.prod P).map (jointInf a b) by unfold lawInf; rfl, integral_map
      (measurable_jointInf hh ha hb).aemeasurable (F.continuous.aestronglyMeasurable)]
    simp only [F, jointInf, BoundedContinuousFunction.coe_ofNormedAddCommGroup,
      Fin.append_left, Fin.append_right]
    exact integral_prod_mul (fun ω => f (fun i => hC ω (a i))) (fun ω => g (fun j => hC ω (b j)))
  simp only [h1] at hport
  rw [h2] at hport
  exact hport

end HarmonicBalls

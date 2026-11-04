import HarmonicBalls.Proofs.Sec6.AnnulusIteration
import LatticeProb.Bonanno.LQGMetric.Field.GFFLaw
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgRate
import LatticeProb.Bonanno.LQGMetric.Field.ExistGFF

/-!
# Law transfer for the whole-plane GFF modulo constants

This bridge uses Leonardo Bonanno's formalization in
`LatticeProb.Bonanno.LQGMetric.Field.GFFLaw` and
`LatticeProb.Bonanno.LQGMetric.Field.CircleAvgRate` and
`LatticeProb.Bonanno.LQGMetric.Field.ExistGFF`, together with his annulus iteration theorem
in `LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Distributions ENNReal

namespace HarmonicBalls.Section6

/-- Away from the diagonal, the normalized covariance splits into the logarithmic kernel and
one additive term in each variable. -/
theorem wholePlaneCov_eq_logCovKernel {x y : ℂ} (hxy : x ≠ y) :
    wholePlaneCov x y = -Real.log ‖x - y‖ + Real.log (max ‖x‖ 1) + Real.log (max ‖y‖ 1) := by
  have hx : max ‖x‖ 1 ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
  have hy : max ‖y‖ 1 ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
  have hxy' : ‖x - y‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy)
  rw [wholePlaneCov, Real.log_div (mul_ne_zero hx hy) hxy', Real.log_mul hx hy]
  ring

/-- The two GFF covariance conventions agree on mean-zero test functions. -/
theorem wholePlaneGFFCov_pairing_eq_logCov (φ ψ : LQGMetric.TestC0) :
    wholePlaneGFFCov (.pairing φ.1) (.pairing ψ.1) = LQGMetric.logCov φ.1 ψ.1 := by
  let ℓ : ℂ → ℝ := fun x => Real.log (max ‖x‖ 1)
  have hℓ : Continuous ℓ := by
    apply Continuous.log ((continuous_norm).max continuous_const)
    intro x
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
  have hψ : Integrable (fun y => ψ.1 y) := LQGMetric.GFFInv.integrable_test ψ.1
  have hφ : Integrable (fun x => φ.1 x) := LQGMetric.GFFInv.integrable_test φ.1
  have hψℓ : Integrable (fun y => ψ.1 y * ℓ y) :=
    (ψ.1.continuous.mul hℓ).integrable_of_hasCompactSupport ψ.1.hasCompactSupport.mul_right
  have hinner (x : ℂ) :
      ∫ y, ψ.1 y * wholePlaneCov x y =
        (∫ y, -Real.log ‖x - y‖ * ψ.1 y) + ∫ y, ψ.1 y * ℓ y := by
    have hae : (fun y => ψ.1 y * wholePlaneCov x y) =ᵐ[volume]
        fun y => (-Real.log ‖x - y‖ * ψ.1 y) + (ℓ x * ψ.1 y + ψ.1 y * ℓ y) := by
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 ((Set.countable_singleton x).measure_zero volume)]
        with y hy
      have hxy : x ≠ y := fun h => hy (by simp [h])
      rw [wholePlaneCov_eq_logCovKernel hxy]
      dsimp [ℓ]
      ring
    have hsum : Integrable (fun y => ℓ x * ψ.1 y + ψ.1 y * ℓ y) := (hψ.const_mul _).add hψℓ
    rw [integral_congr_ae hae,
      integral_add (LQGMetric.CircleAvg.integrable_log_mul_test ψ.1 x) hsum,
      integral_add (hψ.const_mul _) hψℓ, integral_const_mul, ψ.2, mul_zero, zero_add]
  change (∫ x, φ.1 x * ∫ y, ψ.1 y * wholePlaneCov x y) = _
  simp_rw [hinner]
  have heq : (fun x => φ.1 x * ((∫ y, -Real.log ‖x - y‖ * ψ.1 y) + ∫ y, ψ.1 y * ℓ y)) =
      fun x => φ.1 x * (∫ y, ψ.1 y * ℓ y) + φ.1 x * ∫ y, -Real.log ‖x - y‖ * ψ.1 y := by
    funext x
    ring
  rw [heq, LQGMetric.GFFInv.integral_add_of_left (hφ.mul_const _)]
  · unfold LQGMetric.logCov
    congr 1
    funext x
    rw [← integral_const_mul]
    congr 1
    funext y
    ring
  · rw [integral_mul_const, φ.2, zero_mul]


/-- The mean-zero pairings of the frozen GFF, indexed by Bonanno's test-function type. -/
def pairingProc {Ω : Type*} (hC : Ω → (ℂ → ℝ) → ℝ) (ω : Ω) : LQGMetric.TestC0 → ℝ :=
  fun φ => hC ω φ.1

/-- A Bonanno test function is an admissible test function for the frozen field. -/
theorem isTestFunction_of_testC (φ : LQGMetric.TestC) : IsTestFunction Set.univ φ :=
  ⟨φ.contDiff, φ.hasCompactSupport, subset_univ _⟩

/-- The pairing process is measurable in the product σ-algebra. -/
theorem measurable_pairingProc {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) : Measurable (pairingProc hC) :=
  measurable_pi_iff.2 fun φ => hh.measurable_pairing φ.1 (isTestFunction_of_testC φ.1)

/-- Both descriptions give the same law for the process of mean-zero pairings. -/
theorem map_pairingProc_eq {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} {h : Ω' → LQGMetric.DistC}
    (hh : IsWholePlaneGFF P hC hcirc) (hh' : LQGMetric.IsWholePlaneGFF h P') :
    P.map (pairingProc hC) = P'.map (LQGMetric.GFFLaw.pairProc h) := by
  let index : LQGMetric.TestC0 → GFFObservable.Admissible := fun φ =>
    ⟨.pairing φ.1, isTestFunction_of_testC φ.1⟩
  have hgauss := hh.isGaussianProcess.comp_right index
  change IsGaussianProcess (fun (φ : LQGMetric.TestC0) ω => hC ω φ.1) P at hgauss
  have := hh.isProbabilityMeasure
  have := hh'.gaussian.isProbabilityMeasure
  have hfin : ∀ I : Finset LQGMetric.TestC0, (P.map (pairingProc hC)).map I.restrict =
      (P'.map (LQGMetric.GFFLaw.pairProc h)).map I.restrict := by
    intro I
    rw [Measure.map_map (Finset.measurable_restrict I) (measurable_pairingProc hh),
      Measure.map_map (Finset.measurable_restrict I) (LQGMetric.GFFLaw.measurable_pairProc hh'.measurable)]
    exact QuantumZipper.WedgeRes.map_eq_of_gaussian_vec
      (U := fun (i : I) ω => hC ω i.1.1) (V := fun (i : I) ω => h ω i.1.1)
      (hgauss.hasGaussianLaw I) (hh'.gaussian.hasGaussianLaw I)
      (fun i => hh.measurable_pairing i.1.1 (isTestFunction_of_testC i.1.1))
      (fun i => (LQGMetric.GFFInv.measurable_pair _).comp hh'.measurable)
      (fun i => (hgauss.hasGaussianLaw_eval i.1).memLp_two)
      (fun i => (hh'.gaussian.hasGaussianLaw_eval i.1).memLp_two)
      (fun i => hh.integral_eq_zero (.pairing i.1.1) (isTestFunction_of_testC i.1.1))
      (fun i => hh'.centered i.1)
      (fun i j => by
        have hcov := hh.covariance_eq (.pairing i.1.1) (.pairing j.1.1)
          (isTestFunction_of_testC i.1.1) (isTestFunction_of_testC j.1.1)
        change cov[fun ω => hC ω i.1.1, fun ω => hC ω j.1.1; P] = _ at hcov
        exact hcov.trans ((wholePlaneGFFCov_pairing_eq_logCov _ _).trans (hh'.covariance_eq _ _).symm))
  exact IsProjectiveLimit.unique (P := fun I => (P'.map (LQGMetric.GFFLaw.pairProc h)).map I.restrict)
    hfin (fun _ => rfl)


/-- Mean-zero test functions supported in a given open set. -/
def LocalTest (U : Set ℂ) : Type :=
  {φ : LQGMetric.TestC0 // tsupport (φ.1 : ℂ → ℝ) ⊆ U}

/-- The local mean-zero pairing process. -/
def localPairingProc {Ω : Type*} (U : Set ℂ) (hC : Ω → (ℂ → ℝ) → ℝ) (ω : Ω) : LocalTest U → ℝ :=
  fun φ => hC ω φ.1.1

/-- The frozen local σ-algebra is the pullback of the local pairing process. -/
theorem fieldSigmaAlgebraModConst_eq_comap {Ω : Type*} [MeasurableSpace Ω] (hC : Ω → (ℂ → ℝ) → ℝ) (U : Set ℂ) :
    fieldSigmaAlgebraModConst 0 hC U = MeasurableSpace.comap (localPairingProc U hC) inferInstance := by
  apply le_antisymm
  · unfold fieldSigmaAlgebraModConst
    refine iSup_le fun φ => iSup_le fun hφ => ?_
    let ψ : LQGMetric.TestC := ⟨φ, hφ.1.1, hφ.1.2.1, subset_univ _⟩
    let ψ₀ : LocalTest U := ⟨⟨ψ, hφ.2⟩, hφ.1.2.2⟩
    have hm : Measurable[MeasurableSpace.comap (localPairingProc U hC) inferInstance]
        (fun ω => localPairingProc U hC ω ψ₀) := (measurable_pi_apply ψ₀).comp (comap_measurable (localPairingProc U hC))
    change Measurable[MeasurableSpace.comap (localPairingProc U hC) inferInstance]
      (fun ω => hC ω φ) at hm
    have hm' : Measurable[MeasurableSpace.comap (localPairingProc U hC) inferInstance]
        (fun ω => fieldPairing 0 (hC ω) φ) := by
      simpa only [fieldPairing, zero_mul, sub_zero] using hm
    exact measurable_iff_comap_le.1 hm'
  · apply (@measurable_iff_comap_le Ω _ (fieldSigmaAlgebraModConst 0 hC U) _ _).1
    let : MeasurableSpace Ω := fieldSigmaAlgebraModConst 0 hC U
    apply measurable_pi_iff.2
    intro φ
    have hm : Measurable[fieldSigmaAlgebraModConst 0 hC U]
        (fun ω => fieldPairing 0 (hC ω) φ.1.1) := by
      apply measurable_iff_comap_le.2
      unfold fieldSigmaAlgebraModConst
      exact le_iSup_of_le (φ.1.1 : ℂ → ℝ) (le_iSup_of_le
        ⟨⟨φ.1.1.contDiff, φ.1.1.hasCompactSupport, φ.2⟩, φ.1.2⟩ le_rfl)
    simpa only [localPairingProc, fieldPairing, zero_mul, sub_zero] using hm


/-- Restriction of a global mean-zero pairing process to the tests supported in `U`. -/
def localProjection (U : Set ℂ) (v : LQGMetric.TestC0 → ℝ) : LocalTest U → ℝ := fun φ => v φ.1

/-- Restricting the coordinate set is measurable for the product σ-algebra. -/
theorem measurable_localProjection (U : Set ℂ) : Measurable (localProjection U) :=
  measurable_pi_iff.2 fun φ => measurable_pi_apply φ.1

/-- Local mean-zero pairings are measurable from the restriction of any recentered distribution. -/
theorem measurable_localProjection_recentered {Ω : Type} [MeasurableSpace Ω]
    (h : Ω → LQGMetric.DistC) (c : Ω → ℝ) (O : TopologicalSpace.Opens ℂ) :
    Measurable[LQGMetric.Blueprint.fieldSigma (fun ω => LQGMetric.addConst (h ω) (c ω)) O]
      (fun ω => localProjection O (LQGMetric.GFFLaw.pairProc h ω)) := by
  let : MeasurableSpace Ω := LQGMetric.Blueprint.fieldSigma (fun ω => LQGMetric.addConst (h ω) (c ω)) O
  apply measurable_pi_iff.2
  intro φ
  let ψ : LQGMetric.TestOn O := ⟨φ.1.1, φ.1.1.contDiff, φ.1.1.hasCompactSupport, φ.2⟩
  have hres : Measurable[LQGMetric.Blueprint.fieldSigma (fun ω => LQGMetric.addConst (h ω) (c ω)) O]
      (fun ω => LQGMetric.restrictTo O (LQGMetric.addConst (h ω) (c ω))) := comap_measurable _
  have heval : Measurable (fun d : LQGMetric.DistOn O => d ψ) := by
    have hpi : Measurable (fun (d : LQGMetric.DistOn O) (χ : LQGMetric.TestOn O) => d χ) :=
      comap_measurable _
    exact (measurable_pi_apply ψ).comp hpi
  have hm := heval.comp hres
  have heq : (fun ω => LQGMetric.restrictTo O (LQGMetric.addConst (h ω) (c ω)) ψ) =
      (fun ω => localProjection O (LQGMetric.GFFLaw.pairProc h ω) φ) := by
    funext ω
    have hψ : (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := O) (Ω₂ := ⊤)) ψ = φ.1.1 := by
      ext x
      simp only [TestFunction.monoCLM_apply, le_top, and_self, ↓reduceIte, ψ]
      rfl
    change LQGMetric.addConst (h ω) (c ω)
      ((TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := O) (Ω₂ := ⊤)) ψ) = h ω φ.1.1
    rw [hψ, LQGMetric.GFFInv.addConst_apply, φ.1.2, zero_mul, add_zero]
  change Measurable[LQGMetric.Blueprint.fieldSigma (fun ω => LQGMetric.addConst (h ω) (c ω)) O]
    (fun ω => LQGMetric.restrictTo O (LQGMetric.addConst (h ω) (c ω)) ψ) at hm
  rw [heq] at hm
  exact hm


universe u

open Classical in
/-- **Lemma 6.5:** annulus iteration for the frozen pairing-valued GFF, transferred from
Leonardo Bonanno's proof of Gwynne–Miller's Lemma 3.1. -/
theorem annulusIterationStmt_proved : AnnulusIterationStmt.{u} := by
  intro s₁ s₂ hs₁ hs₁₂ hs₂ α hα β hβ
  obtain ⟨p, hp, C, hC, hiter⟩ :=
    annulus_iteration_range_of_distribution s₁ s₂ α β hs₁ hs₁₂ hs₂ hα hβ
  refine ⟨p, hp, C, hC, ?_⟩
  intro α₀ Ω _ P hC' hcirc hh r hr hratio E hlocal hprob K
  obtain ⟨Ω', mΩ', P', hP', h', hh'⟩ := LQGMetric.GFFExist.exists_normalizedWPGFF
  let : MeasurableSpace Ω' := mΩ'
  let : IsProbabilityMeasure P' := hP'
  let U : ℕ → Set ℂ := fun k => annulus 0 (s₁ * r k) (s₂ * r k)
  let O : ℕ → TopologicalSpace.Opens ℂ := fun k => LQGMetric.Blueprint.annulus 0 (s₁ * r k) (s₂ * r k)
  have hOU (k : ℕ) : (O k : Set ℂ) = U k := by
    ext z
    simp [O, U, LQGMetric.Blueprint.annulus, annulus, Metric.mem_ball, Metric.mem_closedBall,
      dist_eq_norm, and_comm]
  choose E₀ hE₀ hEq using hlocal
  have hrepr : ∀ k, ∃ A : Set (LocalTest (U k) → ℝ), MeasurableSet A ∧
      localPairingProc (U k) hC' ⁻¹' A = E₀ k := by
    intro k
    have hmeas := hE₀ k
    rw [fieldSigmaAlgebraModConst_eq, fieldSigmaAlgebraModConst_eq_comap] at hmeas
    exact MeasurableSpace.measurableSet_comap.1 hmeas
  choose A hA hAeq using hrepr
  let B : ℕ → Set (LQGMetric.TestC0 → ℝ) := fun k => localProjection (U k) ⁻¹' A k
  have hB : ∀ k, MeasurableSet (B k) := fun k => measurable_localProjection (U k) (hA k)
  have hmeas : Measurable (pairingProc hC') := measurable_pairingProc hh
  have hmeas' : Measurable (LQGMetric.GFFLaw.pairProc h') :=
    LQGMetric.GFFLaw.measurable_pairProc hh'.1.measurable
  have hlaw := map_pairingProc_eq hh hh'.1
  have hEqB : ∀ k, E k =ᵐ[P] pairingProc hC' ⁻¹' B k := by
    intro k
    have heq : pairingProc hC' ⁻¹' B k = E₀ k := by
      change localPairingProc (U k) hC' ⁻¹' A k = E₀ k
      exact hAeq k
    rw [heq]
    exact hEq k
  let F : ℕ → Set Ω' := fun k => LQGMetric.GFFLaw.pairProc h' ⁻¹' B k
  have hF : ∀ k, MeasurableSet[LQGMetric.Blueprint.fieldSigma
      (fun ω => LQGMetric.addConst (h' ω) (-LQGMetric.circleAvg (h' ω) (r k) 0)) (O k)] (F k) := by
    intro k
    have hm := measurable_localProjection_recentered h' (fun ω => -LQGMetric.circleAvg (h' ω) (r k) 0) (O k)
    rw [hOU k] at hm
    exact hm (hA k)
  have hprob' : ∀ k, ENNReal.ofReal p ≤ P' (F k) := by
    intro k
    have hpEq : P (E k) = P' (F k) := by
      rw [measure_congr (hEqB k)]
      change P (pairingProc hC' ⁻¹' B k) = P' (LQGMetric.GFFLaw.pairProc h' ⁻¹' B k)
      rw [← Measure.map_apply hmeas (hB k), ← Measure.map_apply hmeas' (hB k), hlaw]
    rw [← hpEq]
    exact hprob k
  have hcount : {ω | (((Finset.range K).filter fun k => ω ∈ E k).card : ℝ) < β * K} =ᵐ[P]
      {ω | (((Finset.range K).filter fun k => pairingProc hC' ω ∈ B k).card : ℝ) < β * K} := by
    filter_upwards [ae_all_iff.2 hEqB] with ω hω
    have heq : (Finset.range K).filter (fun k => ω ∈ E k) =
        (Finset.range K).filter (fun k => pairingProc hC' ω ∈ B k) :=
      Finset.filter_congr fun k _ => Iff.of_eq (hω k)
    simp only [heq]
  rw [measure_congr hcount,
    measure_count_range_eq_of_map_eq P P' (pairingProc hC') (LQGMetric.GFFLaw.pairProc h')
      hmeas hmeas' hlaw B hB K (β * K)]
  exact hiter P' h' hh' r hr hratio F hF hprob' K

end HarmonicBalls.Section6

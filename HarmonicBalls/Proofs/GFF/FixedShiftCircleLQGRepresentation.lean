import HarmonicBalls.Proofs.Sec8.LocalCirclePairingApproximation
import HarmonicBalls.Proofs.Sec8.LocalNormalizedMassApproximation
import HarmonicBalls.Proofs.Sec8.CommonApproximationLaw
import HarmonicBalls.Proofs.Sec8.WholePlaneSmoothShift
import HarmonicBalls.Proofs.Sec8.CommonCircleApproximation
import HarmonicBalls.Proofs.Sec6.ContinuousWeylCircleAverage
import HarmonicBalls.Proofs.Sec8.VeryGoodMeasureScaling
import HarmonicBalls.Draft.Section11

/-! # Deterministic shifts of local circle approximations

The imported Section 8 development uses Leonardo Bonanno's LatticeProb
formalization.  The first result identifies the deterministic correction to
the actual signed annular tests used to construct the circle decoder.
-/

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal Topology

namespace HarmonicBalls

/-- A decoder already correct for a limit remains correct after a deterministic
shift of its approximating coordinates when the shifted observation law is
absolutely continuous. The shifted joint observable law is not assumed. -/
theorem decoder_add_shift_of_pairing_law
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (X Y : Ω → E) (hX : Measurable X) (hY : Measurable Y)
    (hAC : P.map Y ≪ P.map X) (D : E → ℝ) (hD : Measurable D)
    (f : ℕ → E → ℝ) (hf : ∀ n, Measurable (f n))
    (u : Ω → ℝ) (c : ℝ) (a : ℕ → ℝ) (b : ℝ)
    (hu : TendstoInMeasure P (fun n ω => f n (X ω)) atTop u)
    (ha : Tendsto a atTop (𝓝 b))
    (hshift : ∀ n ω, f n (Y ω) = f n (X ω) + a n)
    (hDref : ∀ᵐ ω ∂P, D (X ω) = u ω + c) :
    ∀ᵐ ω ∂P, D (Y ω) = u ω + c + b := by
  obtain ⟨s, hs, hsP⟩ := hu.exists_seq_tendsto_ae
  let F : E → ℝ := fun x => limUnder atTop (fun n => f (s n) x)
  have hF : Measurable F :=
    (StronglyMeasurable.limUnder (fun n => (hf (s n)).stronglyMeasurable)).measurable
  let A : Set E := {x | D x = F x + c}
  have hA : MeasurableSet A := measurableSet_eq_fun hD (hF.add_const c)
  have href : ∀ᵐ x ∂(P.map X), x ∈ A := by
    apply (ae_map_iff hX.aemeasurable hA).2
    filter_upwards [hsP, hDref] with ω hω hDω
    rw [hDω]
    change u ω + c = limUnder atTop (fun n => f (s n) (X ω)) + c
    rw [hω.limUnder_eq]
  have hshiftA : ∀ᵐ ω ∂P, Y ω ∈ A :=
    (ae_map_iff hY.aemeasurable hA).1 (hAC.ae_le href)
  filter_upwards [hsP, hshiftA] with ω hω hωA
  have hlim : Tendsto (fun n => f (s n) (Y ω)) atTop (𝓝 (u ω + b)) := by
    have h := hω.add (ha.comp hs.tendsto_atTop)
    simpa only [hshift, Function.comp_def] using h
  change D (Y ω) = F (Y ω) + c at hωA
  rw [hωA]
  change limUnder atTop (fun n => f (s n) (Y ω)) + c = _
  rw [hlim.limUnder_eq]
  ring

/-- Pairing a continuous deterministic shift with the signed annular tests
converges to the difference of its two circle averages. -/
theorem circleDensityDifference_shift_tendsto {r η : ℝ}
    (hr : 0 < r) (hη : 0 < η) (z : ℂ) {g : ℂ → ℝ} (hg : Continuous g) :
    Tendsto (fun n => ∫ x, circleDensityDifference r η hr hη z n x * g x)
      atTop (𝓝 (Real.circleAverage g z r - Real.circleAverage g 0 r)) := by
  have ht := (circleDensity_integral_tendsto_circleAverage hr hη z hg).sub
    (circleDensity_integral_tendsto_circleAverage hr hη 0 hg)
  apply ht.congr'
  filter_upwards with n
  let δ := circleDensityWidth r η n
  let hδ := circleDensityWidth_pos hr hη n
  let m : ℝ := (∫ y, circleDensity r δ hδ 0 y)⁻¹
  have hi (v : ℂ) : Integrable (fun x => m * circleDensity r δ hδ v x * g x) := by
    apply ((continuous_const.mul (circleDensity_contDiff r δ hδ v).continuous).mul hg).integrable_of_hasCompactSupport
    exact (circleDensity_hasCompactSupport hr.le hδ v).mul_left.mul_right
  symm
  change (∫ x, (m * circleDensity r δ hδ z x - m * circleDensity r δ hδ 0 x) * g x) = _
  simp_rw [sub_mul]
  exact integral_sub (hi z) (hi 0)

/-- The same local annular tests approximate the GFF's centered circle in
probability and the deterministic shift's centered circle in the ordinary
sense. The test sequence is fixed before the shift is chosen. -/
theorem IsWholePlaneGFF.exists_localPairing_tests_with_shift_limit
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ε r : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hr : 0 < r) (z : ℂ)
    (hz : closedBall z r ⊆ ball 0 ε) :
    ∃ φ : ℕ → Section6.LocalTest (ball 0 ε),
      TendstoInMeasure P (fun n ω => hC ω (φ n).1.1) atTop
        (fun ω => hcirc ω r z - hcirc ω r 0) ∧
      ∀ g : ℂ → ℝ, Continuous g →
        Tendsto (fun n => ∫ x, (φ n).1.1 x * g x) atTop
          (𝓝 (Real.circleAverage g z r - Real.circleAverage g 0 r)) := by
  let : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  obtain ⟨η, hη, _, htests, _, _⟩ := exists_local_circleDensity_tests hr z hz
  let ψ := circleDensityDifference r η hr hη z
  have htest (n : ℕ) : IsTestFunction (ball 0 ε) (ψ n) ∧ ∫ x, ψ n x = 0 := htests n
  have htestU (n : ℕ) : IsTestFunction univ (ψ n) :=
    ⟨(htest n).1.1, (htest n).1.2.1, subset_univ _⟩
  let φ : ℕ → Section6.LocalTest (ball 0 ε) := fun n =>
    ⟨⟨⟨ψ n, (htest n).1.1, (htest n).1.2.1, subset_univ _⟩, (htest n).2⟩,
      (htest n).1.2.2⟩
  refine ⟨φ, ?_, ?_⟩
  · have hp (n : ℕ) : MemLp (fun ω => hC ω (ψ n)) 2 P :=
      (hGFF.isGaussianProcess.hasGaussianLaw_eval
        (⟨.pairing (ψ n), htestU n⟩ : GFFObservable.Admissible)).memLp (by simp)
    have hzLp : MemLp (fun ω => hcirc ω r z) 2 P :=
      (hGFF.hasGaussianLaw_circle hr z).memLp (by simp)
    have h0Lp : MemLp (fun ω => hcirc ω r 0) 2 P :=
      (hGFF.hasGaussianLaw_circle hr 0).memLp (by simp)
    have hm : ∀ n, ∫ ω, (hC ω (ψ n) - (hcirc ω r z - hcirc ω r 0)) ∂P = 0 := by
      intro n
      have hp0 := hGFF.integral_eq_zero (.pairing (ψ n)) (htestU n)
      have hz0 := hGFF.integral_eq_zero (.circle r z) hr
      have h00 := hGFF.integral_eq_zero (.circle r 0) hr
      simp only [GFFObservable.eval] at hp0 hz0 h00
      have hxy : Integrable (fun ω => hcirc ω r z - hcirc ω r 0) P :=
        (hzLp.sub h0Lp).integrable (by simp)
      rw [integral_sub ((hp n).integrable (by simp)) hxy,
        integral_sub (hzLp.integrable (by simp)) (h0Lp.integrable (by simp)), hp0, hz0, h00]
      ring
    have hkernel := hGFF.circleDensityDifference_error_tendsto_of_self hr hη z
      (hGFF.circleDensityDifference_self_covariance_tendsto hr hη z)
    have hvar : Tendsto (fun n => ProbabilityTheory.variance
        (fun ω => hC ω (ψ n) - (hcirc ω r z - hcirc ω r 0)) P) atTop (𝓝 0) := by
      convert hkernel using 1
      funext n
      exact hGFF.variance_pairing_sub_circle_difference hr z (ψ n) (htestU n)
    exact tendstoInMeasure_of_centered_variance_tendsto_zero P _ _
      (fun n => (hp n).sub (hzLp.sub h0Lp)) hm hvar
  · intro g hg
    exact circleDensityDifference_shift_tendsto hr hη z hg

/-- Every unshifted local centered-circle decoder also decodes the fixed
smooth shift at each deterministic buffered circle center. -/
theorem IsWholePlaneGFF.ae_shifted_centeredCircle_decoder_at
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {α₀ ε R r : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hε : 0 < ε) (hεR : ε < R)
    {g : ℂ → ℝ} (hg : Continuous g)
    (hgs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g (ball 0 R))
    (hr : 0 < r) (z : ℂ) (hz : closedBall z r ⊆ ball 0 ε)
    (D : (Section6.LocalTest (ball 0 ε) → ℝ) → ℂ → ℝ)
    (hD : Measurable (Function.uncurry D))
    (hDref : ∀ᵐ ω ∂P, D (Section6.localPairingProc (ball 0 ε) hC ω) z =
      fieldCircleAverage α₀ (hcirc ω) r z - fieldCircleAverage α₀ (hcirc ω) r 0) :
    ∀ᵐ ω ∂P, D (fun φ => hC ω φ.1.1 + ∫ x, φ.1.1 x * g x) z =
      addCircleAverage (fieldCircleAverage α₀ (hcirc ω)) g r z -
        addCircleAverage (fieldCircleAverage α₀ (hcirc ω)) g r 0 := by
  let X := Section6.localPairingProc (ball 0 ε) hC
  let Y := fun ω (φ : Section6.LocalTest (ball 0 ε)) =>
    hC ω φ.1.1 + ∫ x, φ.1.1 x * g x
  have hX : Measurable X := measurable_pi_iff.mpr fun φ =>
    hGFF.measurable_pairing φ.1.1 (Section6.isTestFunction_of_testC φ.1.1)
  have hY : Measurable Y := measurable_pi_iff.mpr fun φ =>
    (hGFF.measurable_pairing φ.1.1 (Section6.isTestFunction_of_testC φ.1.1)).add_const _
  have hAC : P.map Y ≪ P.map X := by
    have hh := hGFF.local_smooth_shift_pairing_law hε hεR hgs (fun _ => 0)
    change P.map (fun ω (φ : Section6.LocalTest (ball 0 ε)) =>
      hC ω φ.1.1 + ∫ x, φ.1.1 x * g x) ≪
      P.map (fun ω (φ : Section6.LocalTest (ball 0 ε)) => hC ω φ.1.1)
    simpa only [add_zero] using hh
  obtain ⟨φ, hφ, hgφ⟩ := hGFF.exists_localPairing_tests_with_shift_limit hr z hz
  let c := -α₀ * (Real.circleAverage (fun x : ℂ => Real.log ‖x‖) z r -
    Real.circleAverage (fun x : ℂ => Real.log ‖x‖) 0 r)
  have href : ∀ᵐ ω ∂P, D (X ω) z = (hcirc ω r z - hcirc ω r 0) + c := by
    filter_upwards [hDref] with ω hω
    simp only [fieldCircleAverage] at hω
    dsimp [X, c]
    linarith
  have hresult := decoder_add_shift_of_pairing_law P X Y hX hY hAC (fun x => D x z)
    (hD.comp (measurable_id.prodMk measurable_const)) (fun n x => x (φ n))
    (fun n => measurable_pi_apply (φ n)) (fun ω => hcirc ω r z - hcirc ω r 0) c
    (fun n => ∫ x, (φ n).1.1 x * g x)
    (Real.circleAverage g z r - Real.circleAverage g 0 r) hφ (hgφ g hg)
    (by intro n ω; rfl) href
  filter_upwards [hresult] with ω hω
  dsimp [Y, c, addCircleAverage, fieldCircleAverage] at hω ⊢
  linarith

/-- The same decoder is correct for almost every shifted sample and almost
every center in a buffered measurable set. -/
theorem IsWholePlaneGFF.ae_ae_shifted_centeredCircle_decoder
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {α₀ ε R r : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hε : 0 < ε) (hεR : ε < R)
    {g : ℂ → ℝ} (hg : Continuous g)
    (hgs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g (ball 0 R))
    (hr : 0 < r) (E : Set ℂ) (hE : MeasurableSet E)
    (hbuffer : ∀ z ∈ E, closedBall z r ⊆ ball 0 ε)
    (D : (Section6.LocalTest (ball 0 ε) → ℝ) → ℂ → ℝ)
    (hD : Measurable (Function.uncurry D))
    (hDref : ∀ᵐ ω ∂P, ∀ z, closedBall z r ⊆ ball 0 ε →
      D (Section6.localPairingProc (ball 0 ε) hC ω) z =
        fieldCircleAverage α₀ (hcirc ω) r z - fieldCircleAverage α₀ (hcirc ω) r 0) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂(volume.restrict E),
      D (fun φ => hC ω φ.1.1 + ∫ x, φ.1.1 x * g x) z =
        addCircleAverage (fieldCircleAverage α₀ (hcirc ω)) g r z -
          addCircleAverage (fieldCircleAverage α₀ (hcirc ω)) g r 0 := by
  let : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  let X := Section6.localPairingProc (ball 0 ε) hC
  let Y := fun ω (φ : Section6.LocalTest (ball 0 ε)) =>
    hC ω φ.1.1 + ∫ x, φ.1.1 x * g x
  have hX : Measurable X := measurable_pi_iff.mpr fun φ =>
    hGFF.measurable_pairing φ.1.1 (Section6.isTestFunction_of_testC φ.1.1)
  have hY : Measurable Y := measurable_pi_iff.mpr fun φ =>
    (hGFF.measurable_pairing φ.1.1 (Section6.isTestFunction_of_testC φ.1.1)).add_const _
  have hcg : Measurable (fun z => Real.circleAverage g z r) :=
    ((Section6.continuous_circleAverage_radius_center hg).comp
      (continuous_const.prodMk continuous_id)).measurable
  have hm : MeasurableSet {p : Ω × ℂ | D (Y p.1) p.2 =
      D (X p.1) p.2 + (Real.circleAverage g p.2 r - Real.circleAverage g 0 r)} := by
    apply measurableSet_eq_fun
    · exact hD.comp ((hY.comp measurable_fst).prodMk measurable_snd)
    · exact (hD.comp ((hX.comp measurable_fst).prodMk measurable_snd)).add
        ((hcg.comp measurable_snd).sub_const _)
  have hp : ∀ᵐ z ∂(volume.restrict E), ∀ᵐ ω ∂P,
      D (Y ω) z = D (X ω) z +
        (Real.circleAverage g z r - Real.circleAverage g 0 r) := by
    filter_upwards [ae_restrict_mem hE] with z hz
    have hs := hGFF.ae_shifted_centeredCircle_decoder_at hε hεR hg hgs hr z
      (hbuffer z hz) D hD (hDref.mono fun _ h => h z (hbuffer z hz))
    filter_upwards [hs, hDref] with ω hsω hrω
    have h := hrω z (hbuffer z hz)
    dsimp [X, Y, addCircleAverage] at hsω h ⊢
    linarith
  have hpair := (Measure.ae_ae_comm hm).2 hp
  filter_upwards [hpair, hDref] with ω hω hdω
  filter_upwards [hω, ae_restrict_mem hE] with z hz hzin
  have h := hdω z (hbuffer z hzin)
  dsimp [X, Y, addCircleAverage] at hz h ⊢
  linarith

/-- One measurable family realizes the normalized circle approximations for
both a whole-plane field and its fixed deterministic smooth shift. -/
theorem IsWholePlaneGFF.exists_fixedShift_normalizedLQGApprox
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ ε R : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hε : 0 < ε) (hεR : ε < R)
    {g : ℂ → ℝ} (hg : Continuous g)
    (hgs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g (ball 0 R))
    (E : ℕ → Set ℂ) (hEm : ∀ n, MeasurableSet (E n))
    (hbuffer : ∀ n z, z ∈ E n → closedBall z (dyadicScale n) ⊆ ball 0 ε) :
    ∃ F : ℕ → (Section6.LocalTest (ball 0 ε) → ℝ) → Measure ℂ,
      (∀ n, Measurable (F n)) ∧
      (∀ᵐ ω ∂P, ∀ n, F n (Section6.localPairingProc (ball 0 ε) hC ω) =
        normalizedRestriction (lqgApprox γ (fieldCircleAverage α₀ (hcirc ω))
          (dyadicScale n)) (E n)) ∧
      ∀ᵐ ω ∂P, ∀ n,
        F n (fun φ => hC ω φ.1.1 + ∫ x, φ.1.1 x * g x) =
          normalizedRestriction (lqgApprox γ
            (addCircleAverage (fieldCircleAverage α₀ (hcirc ω)) g)
            (dyadicScale n)) (E n) := by
  choose D hDm hDref using fun n =>
    hGFF.exists_localPairing_centeredCircle_decoder (α₀ := α₀) (ε := ε) (dyadicScale_pos n)
  have hshift (n : ℕ) := hGFF.ae_ae_shifted_centeredCircle_decoder
    hε hεR hg hgs (dyadicScale_pos n) (E n) (hEm n) (hbuffer n)
    (D n) (hDm n) (hDref n)
  refine ⟨fun n x => normalizedRestriction
    (volume.withDensity fun z => ENNReal.ofReal (Real.exp (γ * D n x z))) (E n), ?_, ?_, ?_⟩
  · exact fun n => measurable_normalized_centeredLQGApprox γ (D n) (hDm n) (E n) (hEm n)
  · filter_upwards [ae_all_iff.mpr hDref] with ω hω n
    exact (normalizedRestriction_lqgApprox_eq_of_centered_on γ
      (fieldCircleAverage α₀ (hcirc ω)) (dyadicScale_pos n) 0 (hEm n)
      (D n (Section6.localPairingProc (ball 0 ε) hC ω))
      (fun z hz => hω n z (hbuffer n z hz))).symm
  · filter_upwards [ae_all_iff.mpr hshift] with ω hω n
    exact (normalizedRestriction_lqgApprox_eq_of_centered_ae γ
      (addCircleAverage (fieldCircleAverage α₀ (hcirc ω)) g) (dyadicScale_pos n) 0
      (hEm n) (D n (fun φ => hC ω φ.1.1 + ∫ x, φ.1.1 x * g x)) (hω n)).symm

/-- An actual LQG limit and continuity-set exhaustion turn a measurable
finite-scale decoder into convergence in probability of normalized masses.
This applies equally to a smooth-shifted circle process. -/
theorem tendstoInMeasure_normalizedMass_of_fixedShift_approximation
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] {γ : ℝ}
    (h : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (hμ : IsLQGMeasure P γ h μ)
    (hc : ∀ᵐ ω ∂P, ∀ n, Continuous (h ω (dyadicScale n)))
    (U : Set ℂ) (V : ℕ → Set ℂ) (hmono : Monotone V)
    (hbounded : Bornology.IsBounded (⋃ n, V n)) (hunion : (⋃ n, V n) = U)
    (A : Set ℂ) (hA : MeasurableSet A)
    (hfront : ∀ᵐ ω ∂P, (∀ n, μ ω (frontier (V n)) = 0 ∧
      μ ω (frontier (A ∩ V n)) = 0) ∧
      μ ω (frontier (⋃ n, V n)) = 0 ∧ μ ω (frontier (A ∩ ⋃ n, V n)) = 0)
    (hpos : ∀ᵐ ω ∂P, μ ω (⋃ n, V n) ≠ 0 ∧ μ ω (⋃ n, V n) ≠ ∞)
    (X : Ω → E) (hX : Measurable X) (F : ℕ → E → Measure ℂ)
    (hF : ∀ n, Measurable (F n))
    (heq : ∀ᵐ ω ∂P, ∀ n, F n (X ω) =
      normalizedRestriction (lqgApprox γ (h ω) (dyadicScale n)) (V n)) :
    TendstoInMeasure P (fun n ω => (F n (X ω) A).toReal) atTop
      (fun ω => (normalizedRestriction (μ ω) U A).toReal) := by
  apply tendstoInMeasure_of_tendsto_ae
    (fun n => (ENNReal.measurable_toReal.comp
      (((Measure.measurable_coe hA).comp (hF n)).comp hX)).aestronglyMeasurable)
  filter_upwards [hμ, hc, hfront, hpos, heq] with ω hω hcω hfω hpω heqω
  have hlim := hω.tendsto_normalizedRestriction_exhaustion hcω V hmono hbounded A hA
    hfω.1 hfω.2 hpω.1 hpω.2
  have ht : μ ω (A ∩ ⋃ n, V n) / μ ω (⋃ n, V n) =
      normalizedRestriction (μ ω) U A := by
    simp only [normalizedRestriction, Measure.smul_apply, smul_eq_mul,
      Measure.restrict_apply hA, ENNReal.div_eq_inv_mul, hunion]
  rw [ht] at hlim
  have hlim' := (ENNReal.tendsto_toReal (measure_ne_top
    (normalizedRestriction (μ ω) U) A)).comp hlim
  change Tendsto (fun n => (F n (X ω) A).toReal) atTop
    (𝓝 ((normalizedRestriction (μ ω) U A).toReal))
  simp_rw [heqω]
  exact hlim'

/-- Common measurable normalized approximations have one measurable final
decoder on any countable family of mass observables. The two convergence
premises are deliberately explicit: equality of the finite-scale decoders
alone does not establish convergence to a shifted LQG measure. -/
theorem exists_fixedShift_normalizedMass_decoder_of_common_limits
    {Ω Ξ E ι : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    [MeasurableSpace E] [Countable ι] (P : Measure Ω) (Q : Measure Ξ)
    (X : Ω → E) (Y : Ξ → E) (f : ι → ℕ → E → ℝ)
    (hf : ∀ i n, Measurable (f i n))
    (μ : Ω → Measure ℂ) (ν : Ξ → Measure ℂ) (U : Set ℂ) (A : ι → Set ℂ)
    (hμ : ∀ i, TendstoInMeasure P (fun n ω => f i n (X ω)) atTop
      (fun ω => (normalizedRestriction (μ ω) U (A i)).toReal))
    (hν : ∀ i, TendstoInMeasure Q (fun n ω => f i n (Y ω)) atTop
      (fun ω => (normalizedRestriction (ν ω) U (A i)).toReal)) :
    ∃ D : E → ι → ℝ, Measurable D ∧
      (∀ᵐ ω ∂P, ∀ i, D (X ω) i = (normalizedRestriction (μ ω) U (A i)).toReal) ∧
      ∀ᵐ ω ∂Q, ∀ i, D (Y ω) i = (normalizedRestriction (ν ω) U (A i)).toReal := by
  obtain ⟨F, hF, hFP, hFQ⟩ :=
    exists_common_countable_limits_of_tendstoInMeasure P Q X Y f hf
      (fun i ω => (normalizedRestriction (μ ω) U (A i)).toReal)
      (fun i ω => (normalizedRestriction (ν ω) U (A i)).toReal) hμ hν
  exact ⟨fun x i => F i x, Measurable.of_eval hF, hFP, hFQ⟩

/-- The actual LQG limits of a whole-plane field and a fixed smooth shift
have one measurable decoder on countably many normalized mass observables,
provided the stated exhaustion sets are continuity sets for both limits. -/
theorem IsWholePlaneGFF.exists_fixedShift_normalizedMass_decoder
    {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι] {P : Measure Ω}
    {γ α₀ ε R : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hε : 0 < ε) (hεR : ε < R)
    {g : ℂ → ℝ} (hg : Continuous g)
    (hgs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g (ball 0 R))
    (μ ν : Ω → Measure ℂ)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hν : IsLQGMeasure P γ
      (fun ω => addCircleAverage (fieldCircleAverage α₀ (hcirc ω)) g) ν)
    (V : ℕ → Set ℂ) (hVm : ∀ n, MeasurableSet (V n)) (hmono : Monotone V)
    (hbuffer : ∀ n z, z ∈ V n → closedBall z (dyadicScale n) ⊆ ball 0 ε)
    (hunion : (⋃ n, V n) = ball 0 ε) (A : ι → Set ℂ) (hAm : ∀ i, MeasurableSet (A i))
    (hfront : ∀ i, ∀ᵐ ω ∂P, (∀ n,
      μ ω (frontier (V n)) = 0 ∧ μ ω (frontier (A i ∩ V n)) = 0) ∧
      μ ω (frontier (⋃ n, V n)) = 0 ∧ μ ω (frontier (A i ∩ ⋃ n, V n)) = 0)
    (hfront' : ∀ i, ∀ᵐ ω ∂P, (∀ n,
      ν ω (frontier (V n)) = 0 ∧ ν ω (frontier (A i ∩ V n)) = 0) ∧
      ν ω (frontier (⋃ n, V n)) = 0 ∧ ν ω (frontier (A i ∩ ⋃ n, V n)) = 0)
    (hpos : ∀ᵐ ω ∂P, μ ω (⋃ n, V n) ≠ 0 ∧ μ ω (⋃ n, V n) ≠ ∞)
    (hpos' : ∀ᵐ ω ∂P, ν ω (⋃ n, V n) ≠ 0 ∧ ν ω (⋃ n, V n) ≠ ∞) :
    ∃ D : (Section6.LocalTest (ball 0 ε) → ℝ) → ι → ℝ, Measurable D ∧
      (∀ᵐ ω ∂P, ∀ i, D (Section6.localPairingProc (ball 0 ε) hC ω) i =
        (normalizedRestriction (μ ω) (ball 0 ε) (A i)).toReal) ∧
      ∀ᵐ ω ∂P, ∀ i, D (fun φ => hC ω φ.1.1 + ∫ x, φ.1.1 x * g x) i =
        (normalizedRestriction (ν ω) (ball 0 ε) (A i)).toReal := by
  let : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  let X := Section6.localPairingProc (ball 0 ε) hC
  let Y := fun ω (φ : Section6.LocalTest (ball 0 ε)) =>
    hC ω φ.1.1 + ∫ x, φ.1.1 x * g x
  have hX : Measurable X := measurable_pi_iff.mpr fun φ =>
    hGFF.measurable_pairing φ.1.1 (Section6.isTestFunction_of_testC φ.1.1)
  have hY : Measurable Y := measurable_pi_iff.mpr fun φ =>
    (hGFF.measurable_pairing φ.1.1 (Section6.isTestFunction_of_testC φ.1.1)).add_const _
  have hb : Bornology.IsBounded (⋃ n, V n) := by rw [hunion]; exact isBounded_ball
  have hc : ∀ᵐ ω ∂P, ∀ n, Continuous (fieldCircleAverage α₀ (hcirc ω) (dyadicScale n)) :=
    ae_all_iff.mpr fun n => hGFF.ae_continuous_fieldCircleAverage α₀ (dyadicScale_pos n)
  have hc' : ∀ᵐ ω ∂P, ∀ n, Continuous
      (addCircleAverage (fieldCircleAverage α₀ (hcirc ω)) g (dyadicScale n)) := by
    filter_upwards [hc] with ω hω n
    exact (hω n).add ((Section6.continuous_circleAverage_radius_center hg).comp
      (continuous_const.prodMk continuous_id))
  obtain ⟨F, hFm, hF, hF'⟩ := hGFF.exists_fixedShift_normalizedLQGApprox
    (γ := γ) (α₀ := α₀) hε hεR hg hgs V hVm hbuffer
  let f : ι → ℕ → (Section6.LocalTest (ball 0 ε) → ℝ) → ℝ :=
    fun i n x => (F n x (A i)).toReal
  have hf : ∀ i n, Measurable (f i n) := fun i n =>
    ENNReal.measurable_toReal.comp ((Measure.measurable_coe (hAm i)).comp (hFm n))
  apply exists_fixedShift_normalizedMass_decoder_of_common_limits P P X Y f hf μ ν (ball 0 ε) A
  · intro i
    exact tendstoInMeasure_normalizedMass_of_fixedShift_approximation P _ μ hμ hc _ V hmono hb
      hunion (A i) (hAm i) (hfront i) hpos X hX F hFm hF
  · intro i
    exact tendstoInMeasure_normalizedMass_of_fixedShift_approximation P _ ν hν hc' _ V hmono hb
      hunion (A i) (hAm i) (hfront' i) hpos' Y hY F hFm hF'

/-- A measurable event in countably many decoded normalized masses has the
two almost-sure local pairing representations needed for event transfer. -/
theorem fixedShift_event_representation_of_mass_decoder
    {Ω Ξ E ι : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    [MeasurableSpace E] (P : Measure Ω) (Q : Measure Ξ)
    (X : Ω → E) (Y : Ξ → E) (D : E → ι → ℝ) (hD : Measurable D)
    (u : Ω → ι → ℝ) (v : Ξ → ι → ℝ)
    (hu : ∀ᵐ ω ∂P, D (X ω) = u ω) (hv : ∀ᵐ ω ∂Q, D (Y ω) = v ω)
    (C : Set (ι → ℝ)) (hC : MeasurableSet C) :
    ∃ B : Set E, MeasurableSet B ∧
      (∀ᵐ ω ∂P, (u ω ∈ C ↔ X ω ∈ B)) ∧
      ∀ᵐ ω ∂Q, (v ω ∈ C ↔ Y ω ∈ B) := by
  refine ⟨D ⁻¹' C, hD hC, ?_, ?_⟩
  · filter_upwards [hu] with ω hω
    simp only [Set.mem_preimage, hω]
  · filter_upwards [hv] with ω hω
    simp only [Set.mem_preimage, hω]

/-- A deterministic insertion in the local pairing process is absorbed by
translating the decoder's input. This gives exactly the two event
representations used by the smooth-shift positivity transfer. -/
theorem fixedShift_event_representation_with_insertion
    {Ω Ξ ι κ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (P : Measure Ω) (Q : Measure Ξ) (X : Ω → κ → ℝ) (Y : Ξ → κ → ℝ)
    (k : κ → ℝ) (D : (κ → ℝ) → ι → ℝ) (hD : Measurable D)
    (u : Ω → ι → ℝ) (v : Ξ → ι → ℝ)
    (hu : ∀ᵐ ω ∂P, D (X ω) = u ω) (hv : ∀ᵐ ω ∂Q, D (Y ω) = v ω)
    (C : Set (ι → ℝ)) (hC : MeasurableSet C) :
    ∃ B : Set (κ → ℝ), MeasurableSet B ∧
      (∀ᵐ ω ∂P, (u ω ∈ C ↔ (fun φ => X ω φ + k φ) ∈ B)) ∧
      ∀ᵐ ω ∂Q, (v ω ∈ C ↔ (fun φ => Y ω φ + k φ) ∈ B) := by
  let T : (κ → ℝ) → (κ → ℝ) := fun x φ => x φ - k φ
  have hT : Measurable T := measurable_pi_iff.mpr fun φ =>
    (measurable_pi_apply φ).sub_const _
  refine ⟨(D ∘ T) ⁻¹' C, hD.comp hT hC, ?_, ?_⟩
  · filter_upwards [hu] with ω hω
    have heq : T (fun φ => X ω φ + k φ) = X ω := by
      funext φ
      simp [T]
    simp only [Set.mem_preimage, Function.comp_apply, heq, hω]
  · filter_upwards [hv] with ω hω
    have heq : T (fun φ => Y ω φ + k φ) = Y ω := by
      funext φ
      simp [T]
    simp only [Set.mem_preimage, Function.comp_apply, heq, hω]

/-- The cone mass event is unchanged by a finite positive global rescaling
of the measure. -/
theorem coneMassEvent_smul_iff (μ : Measure ℂ) (Q : Set ℂ) (M r : ℝ) (z : ℂ)
    {c : ℝ≥0∞} (hc : c ≠ 0) (hct : c ≠ ∞) :
    coneMassEvent (c • μ) Q M r z ↔ coneMassEvent μ Q M r z := by
  simp only [coneMassEvent, annulusGreenPotentialSup_smul, Measure.smul_apply, smul_eq_mul]
  rw [show ENNReal.ofReal M * (c * annulusGreenPotentialSup μ z (3 * r) (6 * r)) =
    c * (ENNReal.ofReal M * annulusGreenPotentialSup μ z (3 * r) (6 * r)) by ring]
  constructor
  · intro h
    have hi := mul_le_mul_right h c⁻¹
    simpa only [← mul_assoc, ENNReal.inv_mul_cancel hc hct, one_mul] using hi
  · intro h
    exact mul_le_mul_right h c

#print axioms circleDensityDifference_shift_tendsto
#print axioms decoder_add_shift_of_pairing_law
#print axioms IsWholePlaneGFF.exists_localPairing_tests_with_shift_limit
#print axioms IsWholePlaneGFF.ae_shifted_centeredCircle_decoder_at
#print axioms IsWholePlaneGFF.ae_ae_shifted_centeredCircle_decoder
#print axioms IsWholePlaneGFF.exists_fixedShift_normalizedLQGApprox
#print axioms tendstoInMeasure_normalizedMass_of_fixedShift_approximation
#print axioms exists_fixedShift_normalizedMass_decoder_of_common_limits
#print axioms IsWholePlaneGFF.exists_fixedShift_normalizedMass_decoder
#print axioms fixedShift_event_representation_of_mass_decoder
#print axioms fixedShift_event_representation_with_insertion
#print axioms coneMassEvent_smul_iff

end HarmonicBalls

import HarmonicBalls.Proofs.Sec11.SmoothShiftCircleDensity
import HarmonicBalls.Proofs.Sec6.ContinuousWeylCircleAverage
import HarmonicBalls.Proofs.Sec8.CenteredLQGApproximation
import HarmonicBalls.Proofs.Sec6.LQGWeylScaling

/-! # Joint centered circle averages under smooth field shifts

A jointly measurable decoder is reconstructed from countably many pointwise
decoders. The construction is compatible with every continuous deterministic
shift on the same almost-sure event. The imported Section 8 development uses
Leonardo Bonanno's LatticeProb formalization.
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace HarmonicBalls

/-- A centered circle average of a log-singular field admits a jointly
measurable local decoder. On one common event, this decoder is correct at all
buffered centers and after every continuous deterministic shift. -/
theorem IsWholePlaneGFF.exists_joint_local_singular_circle_shift_decoder
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ε r α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hr : 0 < r) :
    ∃ F : (LocalZeroMeanTest (ball 0 ε) → ℝ) → ℂ → ℝ,
      Measurable (Function.uncurry F) ∧
      ∀ᵐ ω ∂P, ∀ g : ℂ → ℝ, Continuous g → ∀ z,
        closedBall z r ⊆ ball 0 ε →
        F (localModConstPairings α (fun ω => addFunPairing (hC ω) g) (ball 0 ε) ω) z =
          (fieldCircleAverage α (hcirc ω) r z - fieldCircleAverage α (hcirc ω) r 0) +
            (Real.circleAverage g z r - Real.circleAverage g 0 r) := by
  classical
  let E := LocalZeroMeanTest (ball 0 ε) → ℝ
  let U : Set ℂ := {z | closedBall z r ⊆ ball 0 ε}
  have hU : IsOpen U := isOpen_centers_closedBall_subset r isOpen_ball
  have hpoint (z : ℂ) (hz : z ∈ U) :=
    hGFF.exists_local_singular_circle_smooth_shift_decoder (α := α) hr z hz
  let G : ℂ → E → ℝ := fun z => if hz : z ∈ U then (hpoint z hz).choose else fun _ => 0
  have hG (z : ℂ) : Measurable (G z) := by
    by_cases hz : z ∈ U
    · simpa [G, hz] using (hpoint z hz).choose_spec.1
    · simp only [G, hz, ↓reduceDIte]
      exact measurable_const
  have hGeq (z : ℂ) (hz : z ∈ U) : ∀ᵐ ω ∂P, ∀ g : ℂ → ℝ, Continuous g →
      G z (localModConstPairings α (fun ω => addFunPairing (hC ω) g) (ball 0 ε) ω) =
        (fieldCircleAverage α (hcirc ω) r z - fieldCircleAverage α (hcirc ω) r 0) +
          (Real.circleAverage g z r - Real.circleAverage g 0 r) := by
    simpa [G, hz] using (hpoint z hz).choose_spec.2
  let a : ℕ → SimpleFunc ℂ ℂ := (stronglyMeasurable_id : StronglyMeasurable (id : ℂ → ℂ)).approx
  have ha (z : ℂ) : Tendsto (fun n => a n z) atTop (𝓝 z) := by
    exact (stronglyMeasurable_id : StronglyMeasurable (id : ℂ → ℂ)).tendsto_approx z
  let H : ℕ → ℂ × E → ℝ := fun n p => G (a n p.1) p.2
  have hH (n : ℕ) : Measurable (H n) := by
    have hfinite : Measurable (fun p : (a n).range × E => G p.1 p.2) := by
      apply measurable_from_prod_countable_right
      intro z
      exact hG z
    change Measurable ((fun p : (a n).range × E => G p.1 p.2) ∘
      (fun p : ℂ × E => (⟨a n p.1, SimpleFunc.mem_range_self _ _⟩, p.2)))
    exact hfinite.comp (((a n).measurable.comp measurable_fst).subtype_mk.prodMk measurable_snd)
  let D : ℂ × E → ℝ := fun p => liminf (fun n => H n p) atTop
  have hD : Measurable D := Measurable.liminf hH
  have hae : ∀ᵐ ω ∂P, ∀ n (z : (a n).range), z.val ∈ U →
      ∀ g : ℂ → ℝ, Continuous g →
        G z (localModConstPairings α (fun ω => addFunPairing (hC ω) g) (ball 0 ε) ω) =
          (fieldCircleAverage α (hcirc ω) r z - fieldCircleAverage α (hcirc ω) r 0) +
            (Real.circleAverage g z r - Real.circleAverage g 0 r) := by
    apply ae_all_iff.mpr
    intro n
    apply ae_all_iff.mpr
    intro z
    by_cases hz : z.val ∈ U
    · filter_upwards [hGeq z hz] with ω hω _
      exact hω
    · exact Filter.Eventually.of_forall (fun _ h => (hz h).elim)
  refine ⟨fun v z => D (z, v), hD.comp measurable_swap, ?_⟩
  filter_upwards [hGFF.ae_continuous_fieldCircleAverage α hr, hae] with ω hω hωeq g hg z hz
  let v : E := localModConstPairings α (fun ω => addFunPairing (hC ω) g) (ball 0 ε) ω
  let f : ℂ → ℝ := fun z =>
    (fieldCircleAverage α (hcirc ω) r z - fieldCircleAverage α (hcirc ω) r 0) +
      (Real.circleAverage g z r - Real.circleAverage g 0 r)
  have hf : Continuous f := by
    exact (hω.sub continuous_const).add
      (((Section6.continuous_circleAverage_radius_center hg).comp
        (continuous_const.prodMk continuous_id)).sub continuous_const)
  have hzmem : ∀ᶠ n in atTop, a n z ∈ U := (ha z).eventually (hU.mem_nhds hz)
  have heq : (fun n => H n (z, v)) =ᶠ[atTop] (fun n => f (a n z)) := by
    filter_upwards [hzmem] with n hn
    exact hωeq n ⟨a n z, SimpleFunc.mem_range_self _ _⟩ hn g hg
  have ht : Tendsto (fun n => H n (z, v)) atTop (𝓝 (f z)) :=
    ((hf.tendsto z).comp (ha z)).congr' heq.symm
  exact ht.liminf_eq

/-- Normalized dyadic LQG approximations on buffered sets have common local
decoders that are correct after every continuous deterministic field shift. -/
theorem IsWholePlaneGFF.exists_local_shifted_normalizedLQGApprox_decoder
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ε α γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (A : ℕ → Set ℂ)
    (hAm : ∀ n, MeasurableSet (A n))
    (hbuffer : ∀ n z, z ∈ A n → closedBall z (dyadicScale n) ⊆ ball 0 ε) :
    ∃ F : ℕ → (LocalZeroMeanTest (ball 0 ε) → ℝ) → Measure ℂ,
      (∀ n, Measurable (F n)) ∧ ∀ᵐ ω ∂P, ∀ n (g : ℂ → ℝ), Continuous g →
        F n (localModConstPairings α (fun ω => addFunPairing (hC ω) g) (ball 0 ε) ω) =
          normalizedRestriction (lqgApprox γ
            (addCircleAverage (fieldCircleAverage α (hcirc ω)) g) (dyadicScale n)) (A n) := by
  choose D hDm hDeq using fun n =>
    hGFF.exists_joint_local_singular_circle_shift_decoder (α := α) (ε := ε) (dyadicScale_pos n)
  refine ⟨fun n v => normalizedRestriction
    (volume.withDensity fun z => ENNReal.ofReal (Real.exp (γ * D n v z))) (A n), ?_, ?_⟩
  · exact fun n => measurable_normalized_centeredLQGApprox γ (D n) (hDm n) (A n) (hAm n)
  · filter_upwards [ae_all_iff.mpr hDeq] with ω hω n g hg
    apply (normalizedRestriction_lqgApprox_eq_of_centered_on γ
      (addCircleAverage (fieldCircleAverage α (hcirc ω)) g) (dyadicScale_pos n) 0
      (hAm n) (D n (localModConstPairings α
        (fun ω => addFunPairing (hC ω) g) (ball 0 ε) ω)) ?_).symm
    intro z hz
    rw [hω n g hg z (hbuffer n z hz)]
    simp only [addCircleAverage]
    ring

/-- A normalized LQG mass on a bounded continuity-set exhaustion has a
single local decoder, compatible with every continuous Weyl shift. -/
theorem IsWholePlaneGFF.exists_local_shifted_normalizedLQGMass_decoder
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ε α γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (A : ℕ → Set ℂ) (hAm : ∀ n, MeasurableSet (A n)) (hmono : Monotone A)
    (hbounded : Bornology.IsBounded (⋃ n, A n))
    (hbuffer : ∀ n z, z ∈ A n → closedBall z (dyadicScale n) ⊆ ball 0 ε)
    (B : Set ℂ) (hB : MeasurableSet B)
    (hfront : ∀ᵐ ω ∂P, (∀ n, μ ω (frontier (A n)) = 0 ∧
      μ ω (frontier (B ∩ A n)) = 0) ∧ μ ω (frontier (⋃ n, A n)) = 0 ∧
      μ ω (frontier (B ∩ ⋃ n, A n)) = 0)
    (hpositive : ∀ᵐ ω ∂P, μ ω (⋃ n, A n) ≠ 0) :
    ∃ F : (LocalZeroMeanTest (ball 0 ε) → ℝ) → ℝ≥0∞, Measurable F ∧
      ∀ᵐ ω ∂P, ∀ g : ℂ → ℝ, Continuous g →
        F (localModConstPairings α (fun ω => addFunPairing (hC ω) g) (ball 0 ε) ω) =
          let ν := (μ ω).withDensity (fun z => ENNReal.ofReal (Real.exp (γ * g z)))
          ν (B ∩ ⋃ n, A n) / ν (⋃ n, A n) := by
  obtain ⟨M, hMm, hMeq⟩ :=
    hGFF.exists_local_shifted_normalizedLQGApprox_decoder (γ := γ) (α := α) A hAm hbuffer
  let F := fun v => liminf (fun n => M n v B) atTop
  have hF : Measurable F := Measurable.liminf (fun n => (Measure.measurable_coe hB).comp (hMm n))
  refine ⟨F, hF, ?_⟩
  have hc := ae_all_iff.mpr fun n => hGFF.ae_continuous_fieldCircleAverage α (dyadicScale_pos n)
  filter_upwards [hμ, hc, hfront, hpositive, hMeq] with ω hω hcω hfrontω hposω heqω g hg
  let w : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (Real.exp (γ * g z))
  let ν := (μ ω).withDensity w
  have hw : Measurable w := ((measurable_const.mul hg.measurable).exp).ennreal_ofReal
  have hw0 : ∀ z, w z ≠ 0 := fun z => ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))
  have hAC : ν ≪ μ ω := withDensity_absolutelyContinuous _ _
  have hAC' : μ ω ≪ ν := withDensity_absolutelyContinuous' hw.aemeasurable
    (Filter.Eventually.of_forall hw0)
  have hνzero : ν (⋃ n, A n) ≠ 0 := fun h => hposω (hAC' h)
  have hshift := Section6.isLQGLimit_addCircleAverage hω hcω g hg
  let : IsLocallyFiniteMeasure ν := hshift.isLocallyFiniteMeasure
  have hνtop : ν (⋃ n, A n) ≠ ∞ := ne_of_lt (hbounded.measure_lt_top (μ := ν))
  have hcshift : ∀ n, Continuous (addCircleAverage (fieldCircleAverage α (hcirc ω)) g (dyadicScale n)) := by
    intro n
    exact (hcω n).add ((Section6.continuous_circleAverage_radius_center hg).comp
      (continuous_const.prodMk continuous_id))
  have hfront' : ∀ n, ν (frontier (A n)) = 0 ∧ ν (frontier (B ∩ A n)) = 0 :=
    fun n => ⟨hAC (hfrontω.1 n).1, hAC (hfrontω.1 n).2⟩
  have hfrontU : ν (frontier (⋃ n, A n)) = 0 ∧ ν (frontier (B ∩ ⋃ n, A n)) = 0 :=
    ⟨hAC hfrontω.2.1, hAC hfrontω.2.2⟩
  have ht := hshift.tendsto_normalizedRestriction_exhaustion hcshift A hmono hbounded B hB
    hfront' hfrontU hνzero hνtop
  have ht' : Tendsto (fun n => M n (localModConstPairings α
      (fun ω => addFunPairing (hC ω) g) (ball 0 ε) ω) B) atTop
      (𝓝 (ν (B ∩ ⋃ n, A n) / ν (⋃ n, A n))) := by
    convert ht using 1
    funext n
    exact congrArg (fun m : Measure ℂ => m B) (heqω n g hg)
  exact ht'.liminf_eq

/-- A deterministic reference ball and a countable generating π-system have
local mass decoders that simultaneously respect all continuous Weyl shifts. -/
theorem IsWholePlaneGFF.exists_referenceBall_shifted_mass_decoders
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ε α γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hfull : ∀ᵐ ω ∂P, ∀ U : Set ℂ, IsOpen U → U.Nonempty → 0 < μ ω U)
    (hε : 0 < ε) :
    ∃ (R : ℝ) (T : Set (Set ℂ)), R ∈ Ioo (0 : ℝ) ε ∧ T.Countable ∧
      IsPiSystem T ∧ (∀ B ∈ T, IsOpen B) ∧
      (inferInstance : MeasurableSpace ℂ) = MeasurableSpace.generateFrom T ∧
      ∃ F : T → (LocalZeroMeanTest (ball 0 ε) → ℝ) → ℝ≥0∞,
        (∀ B, Measurable (F B)) ∧ ∀ᵐ ω ∂P, ∀ (B : T) (g : ℂ → ℝ), Continuous g →
          F B (localModConstPairings α (fun ω => addFunPairing (hC ω) g) (ball 0 ε) ω) =
            let ν := (μ ω).withDensity (fun z => ENNReal.ofReal (Real.exp (γ * g z)))
            ν (B.val ∩ ball 0 R) / ν (ball 0 R) := by
  let : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  obtain ⟨T, R, A, hR, hcount, hpi, hopen, hgen, hAm, hmono, hAunion, hbuffer, hfront⟩ :=
    hGFF.exists_ae_lqg_buffered_continuity_system P hμ hε
  have hbounded : Bornology.IsBounded (⋃ n, A n) := by
    rw [hAunion]
    exact Metric.isBounded_ball
  have hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) := by
    filter_upwards [hμ] with ω hω
    exact hω.isLocallyFiniteMeasure
  have hpositive : ∀ᵐ ω ∂P, μ ω (⋃ n, A n) ≠ 0 := by
    filter_upwards [ae_referenceBall_pos_finite P μ hfull hloc] with ω hω
    rw [hAunion]
    exact (hω R hR.1).1
  have hF (B : T) := hGFF.exists_local_shifted_normalizedLQGMass_decoder
    hμ A hAm hmono hbounded hbuffer B.val (hopen B B.property).measurableSet
    (hfront.mono fun ω hω => hω B B.property) hpositive
  choose F hFm hFeq using hF
  let : Countable T := hcount.to_subtype
  refine ⟨R, T, hR, hcount, hpi, hopen, hgen, F, hFm, ?_⟩
  filter_upwards [ae_all_iff.mpr hFeq] with ω hω B g hg
  simpa only [hAunion] using hω B g hg

#print axioms IsWholePlaneGFF.exists_referenceBall_shifted_mass_decoders
#print axioms IsWholePlaneGFF.exists_local_shifted_normalizedLQGMass_decoder
#print axioms IsWholePlaneGFF.exists_local_shifted_normalizedLQGApprox_decoder
#print axioms IsWholePlaneGFF.exists_joint_local_singular_circle_shift_decoder

end HarmonicBalls

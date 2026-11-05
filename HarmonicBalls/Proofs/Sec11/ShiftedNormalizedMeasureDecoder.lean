import HarmonicBalls.Proofs.Sec11.LocalKernelDecoder
import HarmonicBalls.Proofs.Sec11.JointSmoothShiftCircle
import HarmonicBalls.Proofs.Sec11.SmoothShiftModConstObservable

/-! # Normalized LQG measure after a smooth field shift

The conditional-kernel decoder is shared by the unshifted field and every
fixed smooth shift. The Cameron–Martin argument uses Leonardo Bonanno's
LatticeProb formalization. The exceptional set may depend on the shift.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal

namespace HarmonicBalls

/-- A common local field decoder identifies the normalized LQG measure after
any fixed smooth compactly supported shift with its Weyl-weighted restriction. -/
theorem IsWholePlaneGFF.exists_shifted_normalized_measure_decoder
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ε α γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hfull : ∀ᵐ ω ∂P, ∀ U : Set ℂ, IsOpen U → U.Nonempty → 0 < μ ω U)
    (hε : 0 < ε) :
    ∃ R ∈ Ioo (0 : ℝ) ε,
      ∃ D : (LocalZeroMeanTest (ball 0 ε) → ℝ) → Measure ℂ,
        Measurable D ∧ (∀ v, IsProbabilityMeasure (D v)) ∧
        ∀ g : ℂ → ℝ, IsTestFunction univ g → ∀ᵐ ω ∂P,
          D (localModConstPairings α (fun ω => addFunPairing (hC ω) g) (ball 0 ε) ω) =
            normalizedRestriction ((μ ω).withDensity
              (fun z => ENNReal.ofReal (Real.exp (γ * g z)))) (ball 0 R) := by
  classical
  let : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  obtain ⟨R, T, hR, hcount, hpi, hopen, hgen, F, hFm, hFeq⟩ :=
    hGFF.exists_referenceBall_shifted_mass_decoders hμ hfull hε
  let E := LocalZeroMeanTest (ball 0 ε) → ℝ
  let X : Ω → E := localModConstPairings α hC (ball 0 ε)
  have hX : Measurable X := by
    apply measurable_pi_iff.mpr
    intro φ
    change Measurable (fun ω => hC ω φ.1 - α * ∫ x, φ.1 x * Real.log ‖x‖)
    exact (hGFF.measurable_pairing φ.1 (φ.2.1.mono_set (subset_univ _))).sub_const _
  have hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) :=
    hμ.mono fun _ h => h.isLocallyFiniteMeasure
  have hpos : ∀ᵐ ω ∂P, μ ω (ball 0 R) ≠ 0 ∧ μ ω (ball 0 R) ≠ ∞ :=
    (ae_referenceBall_pos_finite P μ hfull hloc).mono fun _ h => h R hR.1
  let μ' := (hGFF.aemeasurable_lqgMeasure hμ).mk μ
  have hμeq : μ =ᵐ[P] μ' := (hGFF.aemeasurable_lqgMeasure hμ).ae_eq_mk
  let M : Ω → Measure ℂ := fun ω => normalizedRestriction (μ' ω) (ball 0 R)
  have hM : Measurable M := (measurable_normalizedRestriction_measure _ measurableSet_ball).comp
    (hGFF.aemeasurable_lqgMeasure hμ).measurable_mk
  have hprob : ∀ᵐ ω ∂P, IsProbabilityMeasure (M ω) := by
    filter_upwards [hpos, hμeq] with ω hp he
    refine ⟨?_⟩
    simp only [M, normalizedRestriction, Measure.smul_apply, smul_eq_mul,
      Measure.restrict_apply_univ, ← he]
    exact ENNReal.inv_mul_cancel hp.1 hp.2
  let κ : Kernel Ω ℂ := Kernel.mk M hM
  obtain ⟨η, hη, hmarkov⟩ := κ.exists_ae_eq_isMarkovKernel hprob (IsProbabilityMeasure.ne_zero P)
  let : IsMarkovKernel η := hmarkov
  let S : Set (Set ℂ) := insert univ T
  have hSgen : (inferInstance : MeasurableSpace ℂ) = MeasurableSpace.generateFrom S := by
    apply le_antisymm
    · rw [hgen]
      exact MeasurableSpace.generateFrom_mono (subset_insert univ T)
    · apply MeasurableSpace.generateFrom_le
      intro V hV
      rcases Set.mem_insert_iff.mp hV with rfl | hV
      · exact MeasurableSet.univ
      · exact (hopen V hV).measurableSet
  let G : S → E → ℝ≥0∞ := fun V => if hV : V.1 ∈ T then F ⟨V.1, hV⟩ else fun _ => 1
  have hGm (V : S) : Measurable (G V) := by
    dsimp only [G]
    split
    · exact hFm _
    · exact measurable_const
  have hGbase (V : S) : ∀ᵐ ω ∂P, η ω V.1 = G V (X ω) := by
    by_cases hV : V.1 ∈ T
    · filter_upwards [hη, hμeq, hFeq] with ω hηω hμω hFω
      have hzero : (fun ω => addFunPairing (hC ω) (fun _ => 0)) = hC := by
        funext ω φ
        simp [addFunPairing]
      have hh := hFω ⟨V.1, hV⟩ (fun _ => 0) continuous_const
      simp only [hzero, mul_zero, Real.exp_zero, ENNReal.ofReal_one] at hh
      have hwone : (μ ω).withDensity (fun _ => 1) = μ ω := withDensity_one
      rw [hwone] at hh
      simp only [G, hV, ↓reduceDIte]
      rw [← hηω]
      change normalizedRestriction (μ' ω) (ball 0 R) V.1 = _
      rw [← hμω, normalizedRestriction, Measure.smul_apply,
        Measure.restrict_apply (hopen V.1 hV).measurableSet]
      simpa only [smul_eq_mul, ENNReal.div_eq_inv_mul] using hh.symm
    · have hVu : V.1 = univ := by
        rcases Set.mem_insert_iff.mp V.2 with h | h
        · exact h
        · exact (hV h).elim
      have hnot : univ ∉ T := by simpa only [← hVu] using hV
      filter_upwards [] with ω
      simp [G, hVu, hnot]
  obtain ⟨D, hDm, hDprob, hDeq⟩ := exists_measure_decoder_of_piSystem P X hX η S
    (hcount.insert univ) hSgen hpi.insert_univ
    (by intro V hV; rcases Set.mem_insert_iff.mp hV with rfl | hV
        · exact MeasurableSet.univ
        · exact (hopen V hV).measurableSet) (mem_insert univ T) G hGm hGbase
  refine ⟨R, hR, D, hDm, hDprob, ?_⟩
  intro g hg
  have hshift (V : T) : ∀ᵐ ω ∂P,
      D (localModConstPairings α (fun ω => addFunPairing (hC ω) g) (ball 0 ε) ω) V.1 =
        F V (localModConstPairings α (fun ω => addFunPairing (hC ω) g) (ball 0 ε) ω) := by
    apply hGFF.ae_eq_modConst_decoders_after_smooth_shift hg α (ball 0 ε)
      (fun v => D v V.1) (F V) ((Measure.measurable_coe (hopen V.1 V.2).measurableSet).comp hDm) (hFm V)
    filter_upwards [hDeq, hGbase ⟨V.1, mem_insert_of_mem _ V.2⟩] with ω hd hv
    change D (X ω) V.1 = F V (X ω)
    rw [hd]
    simpa only [G, V.2, ↓reduceDIte] using hv
  let : Countable T := hcount.to_subtype
  have hc := ae_all_iff.mpr fun n => hGFF.ae_continuous_fieldCircleAverage α (dyadicScale_pos n)
  filter_upwards [ae_all_iff.mpr hshift, hFeq, hpos, hμ, hc] with ω he hf hp hμω hcω
  let w : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (Real.exp (γ * g z))
  let ν := (μ ω).withDensity w
  have hw : Measurable w := ((measurable_const.mul hg.1.continuous.measurable).exp).ennreal_ofReal
  have hw0 : ∀ z, w z ≠ 0 := fun z => ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))
  have hAC : μ ω ≪ ν := withDensity_absolutelyContinuous' hw.aemeasurable
    (Filter.Eventually.of_forall hw0)
  have hνzero : ν (ball 0 R) ≠ 0 := fun h => hp.1 (hAC h)
  have hμshift := Section6.isLQGLimit_addCircleAverage hμω hcω g hg.1.continuous
  let : IsLocallyFiniteMeasure ν := hμshift.isLocallyFiniteMeasure
  have hνtop : ν (ball 0 R) ≠ ∞ := ne_of_lt (Metric.isBounded_ball.measure_lt_top (μ := ν))
  have hνprob : IsProbabilityMeasure (normalizedRestriction ν (ball 0 R)) := by
    refine ⟨?_⟩
    simp only [normalizedRestriction, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ]
    exact ENNReal.inv_mul_cancel hνzero hνtop
  let : IsProbabilityMeasure (normalizedRestriction ν (ball 0 R)) := hνprob
  let : IsProbabilityMeasure (D (localModConstPairings α
    (fun ω => addFunPairing (hC ω) g) (ball 0 ε) ω)) := hDprob _
  apply ext_of_generate_finite S hSgen hpi.insert_univ
  · intro V hV
    rcases Set.mem_insert_iff.mp hV with rfl | hV
    · simp
    · have hh := hf ⟨V, hV⟩ g hg.1.continuous
      rw [he ⟨V, hV⟩, hh, normalizedRestriction, Measure.smul_apply,
        Measure.restrict_apply (hopen V hV).measurableSet]
      exact ENNReal.div_eq_inv_mul
  · simp

/-- The normalized LQG measure on a small deterministic ball has a law
mutually absolutely continuous with the law of its smooth Weyl weighting. -/
theorem IsWholePlaneGFF.exists_normalized_measure_smooth_shift_laws
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ε α γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hfull : ∀ᵐ ω ∂P, ∀ U : Set ℂ, IsOpen U → U.Nonempty → 0 < μ ω U)
    (hε : 0 < ε) :
    ∃ R ∈ Ioo (0 : ℝ) ε, ∀ g : ℂ → ℝ, IsTestFunction univ g →
      P.map (fun ω => normalizedRestriction ((μ ω).withDensity
        (fun z => ENNReal.ofReal (Real.exp (γ * g z)))) (ball 0 R)) ≪
          P.map (fun ω => normalizedRestriction (μ ω) (ball 0 R)) ∧
      P.map (fun ω => normalizedRestriction (μ ω) (ball 0 R)) ≪
        P.map (fun ω => normalizedRestriction ((μ ω).withDensity
          (fun z => ENNReal.ofReal (Real.exp (γ * g z)))) (ball 0 R)) := by
  obtain ⟨R, hR, D, hDm, _, hD⟩ := hGFF.exists_shifted_normalized_measure_decoder hμ hfull hε
  refine ⟨R, hR, ?_⟩
  intro g hg
  let X := localModConstPairings α hC (ball 0 ε)
  let Y := localModConstPairings α (fun ω => addFunPairing (hC ω) g) (ball 0 ε)
  have hX : Measurable X := by
    apply measurable_pi_iff.mpr
    intro φ
    change Measurable (fun ω => hC ω φ.1 - α * ∫ x, φ.1 x * Real.log ‖x‖)
    exact (hGFF.measurable_pairing φ.1 (φ.2.1.mono_set (subset_univ _))).sub_const _
  have hY : Measurable Y := by
    apply measurable_pi_iff.mpr
    intro φ
    change Measurable (fun ω => (hC ω φ.1 + ∫ x, g x * φ.1 x) -
      α * ∫ x, φ.1 x * Real.log ‖x‖)
    exact ((hGFF.measurable_pairing φ.1 (φ.2.1.mono_set (subset_univ _))).add_const _).sub_const _
  have hzero : (fun ω => addFunPairing (hC ω) (fun _ => 0)) = hC := by
    funext ω φ
    simp [addFunPairing]
  have hzeroTest : IsTestFunction univ (fun _ : ℂ => (0 : ℝ)) := by
    exact ⟨contDiff_const, HasCompactSupport.zero, by simp⟩
  have hbase := hD (fun _ => 0) hzeroTest
  simp only [hzero, mul_zero, Real.exp_zero, ENNReal.ofReal_one] at hbase
  have hwone (ω : Ω) : (μ ω).withDensity (fun _ => 1) = μ ω := withDensity_one
  simp only [hwone] at hbase
  have hshift := hD g hg
  have hforward := (hGFF.singular_smooth_shift_modConst_pairing_laws hg α (ball 0 ε)).1.map hDm
  have hback := (hGFF.singular_smooth_shift_modConst_pairing_laws hg α (ball 0 ε)).2.map hDm
  change (P.map Y).map D ≪ (P.map X).map D at hforward
  change (P.map X).map D ≪ (P.map Y).map D at hback
  rw [Measure.map_map hDm hY, Measure.map_map hDm hX] at hforward
  rw [Measure.map_map hDm hX, Measure.map_map hDm hY] at hback
  have hb : P.map (D ∘ X) = P.map (fun ω => normalizedRestriction (μ ω) (ball 0 R)) :=
    Measure.map_congr hbase
  have hs : P.map (D ∘ Y) = P.map (fun ω => normalizedRestriction ((μ ω).withDensity
      (fun z => ENNReal.ofReal (Real.exp (γ * g z)))) (ball 0 R)) := Measure.map_congr hshift
  rw [hb, hs] at hforward hback
  exact ⟨hforward, hback⟩

#print axioms IsWholePlaneGFF.exists_normalized_measure_smooth_shift_laws

#print axioms IsWholePlaneGFF.exists_shifted_normalized_measure_decoder

end HarmonicBalls

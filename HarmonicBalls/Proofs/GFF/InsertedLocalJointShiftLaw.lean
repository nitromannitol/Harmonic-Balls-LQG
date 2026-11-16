import HarmonicBalls.Proofs.Sec11.ShiftedNormalizedMeasureDecoder
import HarmonicBalls.FirstPass.Phase2.SquarePositiveHolds
import HarmonicBalls.FirstPass.S11j.PositiveWeylInverse

/-! # Local field and normalized measure under smooth shifts

A local centered field and its normalized LQG measure have equivalent joint
laws after a deterministic smooth compactly supported perturbation.
-/

open MeasureTheory Filter Set Metric
open scoped ENNReal

namespace HarmonicBalls

/-- The local centered field and normalized measure are jointly equivalent in
law under each fixed smooth compactly supported shift. -/
theorem IsWholePlaneGFF.exists_local_field_normalizedMeasure_shift_law
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ε α γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hfull : ∀ᵐ ω ∂P, ∀ U : Set ℂ, IsOpen U → U.Nonempty → 0 < μ ω U)
    (hε : 0 < ε) :
    ∃ R ∈ Ioo (0 : ℝ) ε, ∀ g : ℂ → ℝ, IsTestFunction univ g →
      P.map (fun ω =>
        (localModConstPairings α (fun ω => addFunPairing (hC ω) g) (ball 0 ε) ω,
          normalizedRestriction ((μ ω).withDensity
            (fun z => ENNReal.ofReal (Real.exp (γ * g z)))) (ball 0 R))) ≪
        P.map (fun ω =>
          (localModConstPairings α hC (ball 0 ε) ω,
            normalizedRestriction (μ ω) (ball 0 R))) ∧
      P.map (fun ω =>
        (localModConstPairings α hC (ball 0 ε) ω,
          normalizedRestriction (μ ω) (ball 0 R))) ≪
        P.map (fun ω =>
          (localModConstPairings α (fun ω => addFunPairing (hC ω) g) (ball 0 ε) ω,
            normalizedRestriction ((μ ω).withDensity
              (fun z => ENNReal.ofReal (Real.exp (γ * g z)))) (ball 0 R))) := by
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
  have hzeroTest : IsTestFunction univ (fun _ : ℂ => (0 : ℝ)) :=
    ⟨contDiff_const, HasCompactSupport.zero, by simp⟩
  have hbase := hD (fun _ => 0) hzeroTest
  simp only [hzero, mul_zero, Real.exp_zero, ENNReal.ofReal_one] at hbase
  have hwone (ω : Ω) : (μ ω).withDensity (fun _ => 1) = μ ω := withDensity_one
  simp only [hwone] at hbase
  have hshift := hD g hg
  let F := fun v => (v, D v)
  have hF : Measurable F := measurable_id.prodMk hDm
  have hforward := (hGFF.singular_smooth_shift_modConst_pairing_laws hg α (ball 0 ε)).1.map hF
  have hback := (hGFF.singular_smooth_shift_modConst_pairing_laws hg α (ball 0 ε)).2.map hF
  change (P.map Y).map F ≪ (P.map X).map F at hforward
  change (P.map X).map F ≪ (P.map Y).map F at hback
  rw [Measure.map_map hF hY, Measure.map_map hF hX] at hforward
  rw [Measure.map_map hF hX, Measure.map_map hF hY] at hback
  have hb : P.map (F ∘ X) = P.map (fun ω => (X ω, normalizedRestriction (μ ω) (ball 0 R))) := by
    apply Measure.map_congr
    filter_upwards [hbase] with ω hω
    exact Prod.ext rfl hω
  have hs : P.map (F ∘ Y) = P.map (fun ω => (Y ω, normalizedRestriction ((μ ω).withDensity
      (fun z => ENNReal.ofReal (Real.exp (γ * g z)))) (ball 0 R))) := by
    apply Measure.map_congr
    filter_upwards [hshift] with ω hω
    exact Prod.ext rfl hω
  rw [hb, hs] at hforward hback
  exact ⟨hforward, hback⟩

/-- For subcritical LQG, the local centered field and normalized measure have
equivalent joint laws under each fixed smooth compactly supported shift. -/
theorem IsWholePlaneGFF.exists_local_field_normalizedMeasure_shift_law_of_subcritical
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ε α γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ) (hε : 0 < ε) :
    ∃ R ∈ Ioo (0 : ℝ) ε, ∀ g : ℂ → ℝ, IsTestFunction univ g →
      P.map (fun ω =>
        (localModConstPairings α (fun ω => addFunPairing (hC ω) g) (ball 0 ε) ω,
          normalizedRestriction ((μ ω).withDensity
            (fun z => ENNReal.ofReal (Real.exp (γ * g z)))) (ball 0 R))) ≪
        P.map (fun ω =>
          (localModConstPairings α hC (ball 0 ε) ω,
            normalizedRestriction (μ ω) (ball 0 R))) ∧
      P.map (fun ω =>
        (localModConstPairings α hC (ball 0 ε) ω,
          normalizedRestriction (μ ω) (ball 0 R))) ≪
        P.map (fun ω =>
          (localModConstPairings α (fun ω => addFunPairing (hC ω) g) (ball 0 ε) ω,
            normalizedRestriction ((μ ω).withDensity
              (fun z => ENNReal.ofReal (Real.exp (γ * g z)))) (ball 0 R))) := by
  exact hGFF.exists_local_field_normalizedMeasure_shift_law hμ
    (lqgMeasureFullSupportStmt_holds γ α hγ hγ2 hα Ω P hC hcirc μ hGFF hμ) hε


/-- A continuous compactly supported Weyl shift of a Euclidean length metric
is a Euclidean length metric. -/
theorem IsEuclideanLengthMetric.weylScaling_compact_isLengthMetric
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {ξ : ℝ} (hξ : 0 ≤ ξ)
    (f : ℂ → ℝ) (hf : Continuous f) (hc : HasCompactSupport f) :
    IsEuclideanLengthMetric (fun x y => (weylScaling D ξ f x y).toReal) := by
  obtain ⟨m, hm⟩ := exists_lower_bound_of_continuous_compactSupport f hf hc
  obtain ⟨c, hc'⟩ := exists_lower_bound_of_continuous_compactSupport (fun z => -f z) hf.neg hc.neg
  let M := -c
  let g : ℂ → ℝ := fun z => f z - M
  have hglo : ∀ z, m - M ≤ g z := fun z => by dsimp [g]; linarith [hm z]
  have hghi : ∀ z, g z ≤ 0 := fun z => by dsimp [g, M]; linarith [hc' z]
  have hzero := hD.weylScaling_zero ξ
  obtain ⟨hdiag, hsep, htop⟩ := hD.weylScaling_negative_bump_topology hξ g hglo hghi hzero
  have hfin : ∀ x y, weylScaling D ξ g x y ≠ ⊤ :=
    fun x y => (weylScaling_negative_bump_real_bounds hD hξ g hglo hghi hzero x y).1.ne
  have hsymm : ∀ x y, (weylScaling D ξ g x y).toReal = (weylScaling D ξ g y x).toReal :=
    fun x y => congrArg ENNReal.toReal (hD.weylScaling_symm ξ g x y)
  have hE : IsEuclideanLengthMetric (fun x y => (weylScaling D ξ g x y).toReal) :=
    ⟨hdiag, hsep, hsymm, hD.weylScaling_toReal_triangle ξ g hfin, htop,
      hD.weylScaling_internalMetric ξ g (fun x y => ENNReal.ofReal_toReal (hfin x y)) hsymm⟩
  have heq : (fun x y => (weylScaling D ξ f x y).toReal) =
      fun x y => Real.exp (ξ * M) * (weylScaling D ξ g x y).toReal := by
    funext x y
    rw [weylScaling_eq_exp_mul_of_shift D ξ M f g (fun z => by dsimp [g]; ring),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le]
  rw [heq]
  exact hE.const_mul (Real.exp_pos _)

/-- A compact continuous Weyl shift has the inverse shift as its inverse. -/
theorem IsEuclideanLengthMetric.inverse_weylScaling_compact
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {ξ : ℝ} (hξ : 0 ≤ ξ)
    (f : ℂ → ℝ) (hf : Continuous f) (hc : HasCompactSupport f) (x y : ℂ) :
    ENNReal.ofReal (D x y) =
      weylScaling (fun u v => (weylScaling D ξ f u v).toReal) ξ (fun z => -f z) x y := by
  obtain ⟨m, hm⟩ := exists_lower_bound_of_continuous_compactSupport f hf hc
  obtain ⟨c, hc'⟩ := exists_lower_bound_of_continuous_compactSupport (fun z => -f z) hf.neg hc.neg
  let M := -c
  let g : ℂ → ℝ := fun z => f z - M
  have hglo : ∀ z, m - M ≤ g z := fun z => by dsimp [g]; linarith [hm z]
  have hghi : ∀ z, g z ≤ 0 := fun z => by dsimp [g, M]; linarith [hc' z]
  have hg : Continuous g := hf.sub continuous_const
  have hzero := hD.weylScaling_zero ξ
  obtain ⟨hdiag, hsep, htop⟩ := hD.weylScaling_negative_bump_topology hξ g hglo hghi hzero
  have hfin : ∀ u v, weylScaling D ξ g u v ≠ ⊤ :=
    fun u v => (weylScaling_negative_bump_real_bounds hD hξ g hglo hghi hzero u v).1.ne
  have hsymm : ∀ u v, (weylScaling D ξ g u v).toReal = (weylScaling D ξ g v u).toReal :=
    fun u v => congrArg ENNReal.toReal (hD.weylScaling_symm ξ g u v)
  have hE : IsEuclideanLengthMetric (fun u v => (weylScaling D ξ g u v).toReal) :=
    ⟨hdiag, hsep, hsymm, hD.weylScaling_toReal_triangle ξ g hfin, htop,
      hD.weylScaling_internalMetric ξ g (fun u v => ENNReal.ofReal_toReal (hfin u v)) hsymm⟩
  have heq : (fun u v => (weylScaling D ξ f u v).toReal) =
      fun u v => Real.exp (ξ * M) * (weylScaling D ξ g u v).toReal := by
    funext u v
    rw [weylScaling_eq_exp_mul_of_shift D ξ M f g (fun z => by dsimp [g]; ring),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le]
  have hneg : (fun z => -f z) = fun z => -g z + -M := by
    funext z
    dsimp [g]
    ring
  have hinv := hD.inverse_weylScaling hξ g hg hglo hghi hE x y
  have hone : ENNReal.ofReal (Real.exp (ξ * M)) * ENNReal.ofReal (Real.exp (ξ * (-M))) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
      show ξ * M + ξ * (-M) = 0 by ring, Real.exp_zero, ENNReal.ofReal_one]
  rw [heq, hE.weylScaling_const_mul (Real.exp_pos _), hneg,
    weylScaling_add_const, ← mul_assoc, hone, one_mul]
  exact hinv

end HarmonicBalls

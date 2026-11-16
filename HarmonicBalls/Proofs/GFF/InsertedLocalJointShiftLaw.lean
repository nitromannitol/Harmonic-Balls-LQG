import HarmonicBalls.Proofs.Sec11.ShiftedNormalizedMeasureBetween
import HarmonicBalls.FirstPass.Phase2.SquarePositiveHolds
import HarmonicBalls.FirstPass.S11j.PositiveWeylInverse
import HarmonicBalls.Steps.Sec11.WeylLocalComposition
import HarmonicBalls.Proofs.Sec11.SingularCutoffWeylComparison
import HarmonicBalls.Steps.Sec11.InternalMetricExhaustion
import HarmonicBalls.Proofs.Sec11.ExhaustionDecoder
import HarmonicBalls.Proofs.Sec11.SingularWeylExhaustion
import HarmonicBalls.Proofs.Sec11.JointPuncturedSingularShift
import HarmonicBalls.Proofs.Sec11.PuncturedMetricExhaustionLocality
import HarmonicBalls.Steps.Sec11.WeylPointRemoval
import HarmonicBalls.FirstPass.S11m.DecodedDomain

/-! # Local field and normalized measure under smooth shifts

A local centered field and its normalized LQG measure have equivalent joint
laws after a deterministic smooth compactly supported perturbation.
-/

open MeasureTheory Filter Set Metric Topology
open scoped ENNReal NNReal

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

/-- Two Weyl-scaled length metrics that agree locally remain locally equal
    in internal distance after a continuous compactly supported shift. -/
theorem IsEuclideanLengthMetric.internalMetric_weylScaling_twice_eq_of_eqOn_compact
    {D E F : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hE : IsEuclideanLengthMetric E) (hF : IsEuclideanLengthMetric F)
    {ξ : ℝ} (hξ : 0 ≤ ξ) (f g k : ℂ → ℝ)
    (hk : Continuous k) (hc : HasCompactSupport k)
    (hEscale : ∀ x y, ENNReal.ofReal (E x y) = weylScaling D ξ f x y)
    (hFscale : ∀ x y, ENNReal.ofReal (F x y) = weylScaling D ξ g x y)
    {U : Set ℂ} (hU : IsOpen U) (hfg : ∀ z ∈ U, f z = g z) (x y : ℂ) :
    internalMetric (fun a b => (weylScaling E ξ k a b).toReal) U x y =
      internalMetric (fun a b => (weylScaling F ξ k a b).toReal) U x y := by
  obtain ⟨m, hm⟩ := exists_lower_bound_of_continuous_compactSupport k hk hc
  obtain ⟨c, hc'⟩ := exists_lower_bound_of_continuous_compactSupport (fun z => -k z) hk.neg hc.neg
  let M := -c
  let j : ℂ → ℝ := fun z => k z - M
  have hjlo : ∀ z, m - M ≤ j z := fun z => by dsimp [j]; linarith [hm z]
  have hjhi : ∀ z, j z ≤ 0 := fun z => by dsimp [j, M]; linarith [hc' z]
  have hj : Continuous j := hk.sub continuous_const
  have hlength (B : ℂ → ℂ → ℝ) (hB : IsEuclideanLengthMetric B) :
      IsEuclideanLengthMetric (fun a b => (weylScaling B ξ j a b).toReal) := by
    have hzero := hB.weylScaling_zero ξ
    obtain ⟨hdiag, hsep, htop⟩ := hB.weylScaling_negative_bump_topology hξ j hjlo hjhi hzero
    have hfin : ∀ u v, weylScaling B ξ j u v ≠ ⊤ :=
      fun u v => (weylScaling_negative_bump_real_bounds hB hξ j hjlo hjhi hzero u v).1.ne
    have hsymm : ∀ u v, (weylScaling B ξ j u v).toReal =
        (weylScaling B ξ j v u).toReal :=
      fun u v => congrArg ENNReal.toReal (hB.weylScaling_symm ξ j u v)
    exact ⟨hdiag, hsep, hsymm, hB.weylScaling_toReal_triangle ξ j hfin, htop,
      hB.weylScaling_internalMetric ξ j (fun u v => ENNReal.ofReal_toReal (hfin u v)) hsymm⟩
  have heq (B : ℂ → ℂ → ℝ) :
      (fun a b => (weylScaling B ξ k a b).toReal) =
        fun a b => Real.exp (ξ * M) * (weylScaling B ξ j a b).toReal := by
    funext a b
    rw [weylScaling_eq_exp_mul_of_shift B ξ M k j (fun z => by dsimp [j]; ring),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le]
  have hlocal := hD.internalMetric_weylScaling_twice_eq_of_eqOn hE hF hξ f g j hj
    hjlo hjhi hEscale hFscale (hlength E hE) (hlength F hF) hU hfg x y
  rw [heq E, heq F, internalMetric_const_mul _ (Real.exp_pos _) U,
    internalMetric_const_mul _ (Real.exp_pos _) U, hlocal]

/-- Away from the insertion, compact smooth shifts of the singular metric
    agree on internal distances with the corresponding shifted cutoff metric. -/
theorem IsWholePlaneGFF.ae_internal_singularMetric_weylShift_eq_cutoff_compact
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {D : Ω → ℂ → ℂ → ℝ} (h : IsWholePlaneGFF P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hD : ∀ᵐ ω ∂P, ∀ u v, ENNReal.ofReal (D ω u v) =
      weylScaling (𝔇 (hC ω)) ξ (fun z => -α * Real.log ‖z‖) u v)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (g : ℂ → ℝ) (hg : Continuous g) (hc : HasCompactSupport g) (hξ : 0 ≤ ξ)
    {r : ℝ} (hr : 0 < r) (U : ℕ → Set ℂ) (hU : ∀ n, IsOpen (U n))
    (haway : ∀ n z, z ∈ U n → r ≤ ‖z‖) :
    let f : ℂ → ℝ := fun z => -α * Real.log (max ‖z‖ r)
    ∀ᵐ ω ∂P, ∀ n x y,
      internalMetric (fun a b => (weylScaling (D ω) ξ g a b).toReal) (U n) x y =
      internalMetric (fun a b =>
        (weylScaling (𝔇 (hC ω)) ξ (fun z => g z + f z) a b).toReal) (U n) x y := by
  let f : ℂ → ℝ := fun z => -α * Real.log (max ‖z‖ r)
  have hf : Continuous f := by
    apply continuous_const.mul
    apply (continuous_norm.max continuous_const).log
    intro z
    exact ne_of_gt (lt_of_lt_of_le hr (le_max_right _ _))
  have hbase := ae_wholePlane_weylScaling_shift P γ ξ hC hcirc 𝔇 h𝔇 h
    (fun _ => f) (fun _ => hf) (fun _ => measurable_const)
  have hsum := ae_wholePlane_weylScaling_shift P γ ξ hC hcirc 𝔇 h𝔇 h
    (fun _ z => g z + f z) (fun _ => hg.add hf) (fun _ => measurable_const)
  have hshift := (h𝔇.satisfiesLQGMetricAxioms Ω P hC hcirc (fun _ => f) h
    (fun _ => hf) (fun _ => measurable_const)).ae_weylScaling
  filter_upwards [hD, hmetric, hbase, hsum, hshift] with ω hd hm hb hs hw n x y
  have hcomp : (fun a b => (weylScaling (𝔇 (addFunPairing (hC ω) f)) ξ g a b).toReal) =
      𝔇 (addFunPairing (hC ω) (fun z => g z + f z)) := by
    funext a b
    have hn : 0 ≤ 𝔇 (addFunPairing (hC ω) (fun z => g z + f z)) a b := by
      have ht := hs.2.1.triangle a b a
      rw [hs.2.1.self_eq_zero, hs.2.1.symm b a] at ht
      linarith
    have hw' := hw g hg a b
    rw [h𝔇.addFunPairing_addFunPairing (hC ω) hf hg] at hw'
    have hcomm : (fun z => f z + g z) = (fun z => g z + f z) := by
      funext z
      exact add_comm _ _
    rw [hcomm] at hw'
    rw [← hw', ENNReal.toReal_ofReal hn]
  have hsumcomp : (fun a b =>
      (weylScaling (𝔇 (hC ω)) ξ (fun z => g z + f z) a b).toReal) =
      𝔇 (addFunPairing (hC ω) (fun z => g z + f z)) := by
    funext a b
    have hn : 0 ≤ 𝔇 (addFunPairing (hC ω) (fun z => g z + f z)) a b := by
      have ht := hs.2.1.triangle a b a
      rw [hs.2.1.self_eq_zero, hs.2.1.symm b a] at ht
      linarith
    rw [← hs.2.2.2.1 a b, ENNReal.toReal_ofReal hn]
  have heq := hb.1.internalMetric_weylScaling_twice_eq_of_eqOn_compact hm hb.2.1 hξ
    (fun z => -α * Real.log ‖z‖) f g hg hc hd hb.2.2.2.1
    (hU n) (fun z hz => by simp only [f, max_eq_left (haway n z hz)]) x y
  rw [hcomp] at heq
  rwa [hsumcomp]

/-- A countable open exhaustion identifies the shifted singular internal
    metric with the infimum of its shifted cutoff internal metrics. -/
theorem IsWholePlaneGFF.ae_internal_singularMetric_weylShift_eq_iInf_cutoff_compact
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {D : Ω → ℂ → ℂ → ℝ} (h : IsWholePlaneGFF P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hD : ∀ᵐ ω ∂P, ∀ u v, ENNReal.ofReal (D ω u v) =
      weylScaling (𝔇 (hC ω)) ξ (fun z => -α * Real.log ‖z‖) u v)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (g : ℂ → ℝ) (hg : Continuous g) (hc : HasCompactSupport g) (hξ : 0 ≤ ξ)
    (r : ℕ → ℕ → ℝ) (hr : ∀ n m, 0 < r n m) (U : ℕ → ℕ → Set ℂ)
    (hU : ∀ n m, IsOpen (U n m)) (hmono : ∀ n, Monotone (U n))
    (haway : ∀ n m z, z ∈ U n m → r n m ≤ ‖z‖) :
    ∀ᵐ ω ∂P, ∀ n x y,
      internalMetric (fun a b => (weylScaling (D ω) ξ g a b).toReal)
          (⋃ m, U n m) x y =
      ⨅ m, internalMetric (fun a b =>
        (weylScaling (𝔇 (hC ω)) ξ
          (fun z => g z + -α * Real.log (max ‖z‖ (r n m))) a b).toReal) (U n m) x y := by
  have heach : ∀ n m, ∀ᵐ ω ∂P, ∀ x y,
      internalMetric (fun a b => (weylScaling (D ω) ξ g a b).toReal) (U n m) x y =
        internalMetric (fun a b => (weylScaling (𝔇 (hC ω)) ξ
          (fun z => g z + -α * Real.log (max ‖z‖ (r n m))) a b).toReal) (U n m) x y := by
    intro n m
    have ht := h.ae_internal_singularMetric_weylShift_eq_cutoff_compact 𝔇 h𝔇 hD hmetric
      g hg hc hξ (hr n m) (fun _ => U n m) (fun _ => hU n m)
      (fun _ z hz => haway n m z hz)
    filter_upwards [ht] with ω hω x y
    exact hω 0 x y
  have hall : ∀ᵐ ω ∂P, ∀ n m x y,
      internalMetric (fun a b => (weylScaling (D ω) ξ g a b).toReal) (U n m) x y =
        internalMetric (fun a b => (weylScaling (𝔇 (hC ω)) ξ
          (fun z => g z + -α * Real.log (max ‖z‖ (r n m))) a b).toReal) (U n m) x y :=
    ae_all_iff.mpr fun n => ae_all_iff.mpr (heach n)
  filter_upwards [hall] with ω hω n x y
  rw [internalMetric_iUnion_of_monotone_isOpen _ (U n) (hU n) (hmono n)]
  exact iInf_congr fun m => hω n m x y

/-- A single decoder identifies countably many singular internal distances on
    an open exhaustion after each continuous compactly supported shift. -/
theorem IsWholePlaneGFF.exists_exhausted_singularMetric_compactShift_decoder
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {D : Ω → ℂ → ℂ → ℝ} (h : IsWholePlaneGFF P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hD : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
      ENNReal.ofReal (D ω u v) =
        weylScaling (𝔇 (hC ω)) ξ (fun z => -α * Real.log ‖z‖) u v)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (ψ : ℂ → ℝ) (hψ : IsTestFunction univ ψ) (hψint : ∫ x, ψ x = 1)
    (f₀ : ℂ → ℝ) (hf₀ : Continuous f₀)
    (r : ℕ → ℕ → ℝ) (hr : ∀ n m, 0 < r n m)
    (U : ℕ → ℕ → Set ℂ) (hU : ∀ n m, IsOpen (U n m))
    (hmono : ∀ n, Monotone (U n))
    (haway : ∀ n m z, z ∈ U n m → r n m ≤ ‖z‖)
    (p : ℕ → ℂ × ℂ) (hp : ∀ n m, (p n).1 ∈ U n m) (hξ : 0 ≤ ξ) :
    ∃ F : (LocalZeroMeanTest univ → ℝ) → ℕ → ℝ≥0∞, Measurable F ∧
      (∀ᵐ ω ∂P, ∀ n, F (localModConstPairings 0 hC univ ω) n =
        ENNReal.ofReal (Real.exp (ξ * (-(hC ω ψ + ∫ z, f₀ z * ψ z)))) *
          internalMetric (D ω) (⋃ m, U n m) (p n).1 (p n).2) ∧
      ∀ g : ℂ → ℝ, Continuous g → HasCompactSupport g →
        ∀ᵐ ω ∂P, ∀ n, F (localModConstPairings 0
          (fun ω => addFunPairing (hC ω) g) univ ω) n =
          ENNReal.ofReal (Real.exp (ξ * (-(hC ω ψ + ∫ z, (g z + f₀ z) * ψ z)))) *
            internalMetric (fun x y => (weylScaling (D ω) ξ g x y).toReal)
              (⋃ m, U n m) (p n).1 (p n).2 := by
  let f : ℕ → ℕ → ℂ → ℝ := fun n m z => -α * Real.log (max ‖z‖ (r n m))
  have hf (n m : ℕ) : Continuous (f n m) := by
    apply continuous_const.mul
    apply (continuous_norm.max continuous_const).log
    intro z
    exact ne_of_gt (lt_of_lt_of_le (hr n m) (le_max_right _ _))
  have hex (n m : ℕ) := h.exists_internal_singularMetric_cutoff_shift_decoder
    𝔇 h𝔇 hD hmetric ψ hψ hψint (hr n m) (fun _ => U n m)
    (fun _ => hU n m) (fun _ z hz => haway n m z hz) (fun _ => p n) (fun _ => hp n m)
  choose A hA hAbase hAshift using hex
  let a : ℕ → ℕ → ℝ≥0∞ := fun n m => ENNReal.ofReal
    (Real.exp (ξ * ((∫ z, f n m z * ψ z) - ∫ z, f₀ z * ψ z)))
  let F : (LocalZeroMeanTest univ → ℝ) → ℕ → ℝ≥0∞ :=
    fun v n => ⨅ m, a n m * A n m v 0
  have hF : Measurable F := by
    apply measurable_pi_iff.mpr
    intro n
    apply Measurable.iInf
    intro m
    exact measurable_const.mul ((measurable_pi_apply 0).comp (hA n m))
  refine ⟨F, hF, ?_, ?_⟩
  · have hall : ∀ᵐ ω ∂P, ∀ n m,
        A n m (localModConstPairings 0 hC univ ω) 0 =
          ENNReal.ofReal (Real.exp (ξ * (-(hC ω ψ + ∫ z, f n m z * ψ z)))) *
            internalMetric (D ω) (U n m) (p n).1 (p n).2 := by
      apply (ae_all_iff).2
      intro n
      apply (ae_all_iff).2
      intro m
      filter_upwards [hAbase n m] with ω hω
      exact hω 0
    filter_upwards [hall] with ω hω n
    change (⨅ m, a n m * A n m (localModConstPairings 0 hC univ ω) 0) = _
    have hn (m : ℕ) : a n m * ENNReal.ofReal
        (Real.exp (ξ * (-(hC ω ψ + ∫ z, f n m z * ψ z)))) =
        ENNReal.ofReal (Real.exp (ξ * (-(hC ω ψ + ∫ z, f₀ z * ψ z)))) := by
      simpa only [a, zero_add] using cutoff_normalization_factor_pairing ξ (hC ω ψ)
        ψ (fun _ => 0) f₀ (f n m) hψ continuous_const hf₀ (hf n m)
    calc
      (⨅ m, a n m * A n m (localModConstPairings 0 hC univ ω) 0) =
          ⨅ m, ENNReal.ofReal (Real.exp (ξ * (-(hC ω ψ + ∫ z, f₀ z * ψ z)))) *
            internalMetric (D ω) (U n m) (p n).1 (p n).2 := by
        apply iInf_congr
        intro m
        rw [hω n m, ← mul_assoc, hn m]
      _ = ENNReal.ofReal (Real.exp (ξ * (-(hC ω ψ + ∫ z, f₀ z * ψ z)))) *
          internalMetric (D ω) (⋃ m, U n m) (p n).1 (p n).2 := by
        rw [internalMetric_iUnion_of_monotone_isOpen _ (U n) (hU n) (hmono n),
          ENNReal.mul_iInf (fun ht _ => (ENNReal.ofReal_ne_top ht).elim)]
  · intro g hg hgc
    have hall : ∀ᵐ ω ∂P, ∀ n m,
        A n m (localModConstPairings 0 (fun ω => addFunPairing (hC ω) g) univ ω) 0 =
          ENNReal.ofReal (Real.exp (ξ * (-(hC ω ψ + ∫ z, (g z + f n m z) * ψ z)))) *
            internalMetric (fun x y => (weylScaling (𝔇 (hC ω)) ξ
              (fun z => g z + f n m z) x y).toReal) (U n m) (p n).1 (p n).2 := by
      apply (ae_all_iff).2
      intro n
      apply (ae_all_iff).2
      intro m
      filter_upwards [hAshift n m g hg] with ω hω
      exact hω 0
    have hrepr : ∀ᵐ ω ∂P, ∀ x y, ENNReal.ofReal (D ω x y) =
        weylScaling (𝔇 (hC ω)) ξ (fun z => -α * Real.log ‖z‖) x y := by
      filter_upwards [hD] with ω hω x y
      exact (hω x y).2
    have hcomp : ∀ᵐ ω ∂P, ∀ n x y,
        internalMetric (fun x y => (weylScaling (D ω) ξ g x y).toReal)
          (⋃ m, U n m) x y =
        ⨅ m, internalMetric (fun x y => (weylScaling (𝔇 (hC ω)) ξ
          (fun z => g z + f n m z) x y).toReal) (U n m) x y := by
      exact h.ae_internal_singularMetric_weylShift_eq_iInf_cutoff_compact 𝔇 h𝔇 hrepr hmetric
        g hg hgc hξ r hr U hU hmono haway
    filter_upwards [hall, hcomp] with ω hω hωcomp n
    change (⨅ m, a n m * A n m
      (localModConstPairings 0 (fun ω => addFunPairing (hC ω) g) univ ω) 0) = _
    calc
      (⨅ m, a n m * A n m
          (localModConstPairings 0 (fun ω => addFunPairing (hC ω) g) univ ω) 0) =
          ⨅ m, ENNReal.ofReal (Real.exp (ξ * (-(hC ω ψ + ∫ z, (g z + f₀ z) * ψ z)))) *
            internalMetric (fun x y => (weylScaling (𝔇 (hC ω)) ξ
              (fun z => g z + f n m z) x y).toReal) (U n m) (p n).1 (p n).2 := by
        apply iInf_congr
        intro m
        rw [hω n m, ← mul_assoc]
        rw [show a n m * ENNReal.ofReal
          (Real.exp (ξ * (-(hC ω ψ + ∫ z, (g z + f n m z) * ψ z)))) = _ from
            cutoff_normalization_factor_pairing ξ (hC ω ψ) ψ g f₀ (f n m) hψ hg hf₀ (hf n m)]
      _ = ENNReal.ofReal (Real.exp (ξ * (-(hC ω ψ + ∫ z, (g z + f₀ z) * ψ z)))) *
          internalMetric (fun x y => (weylScaling (D ω) ξ g x y).toReal)
            (⋃ m, U n m) (p n).1 (p n).2 := by
        rw [hωcomp n, ENNReal.mul_iInf (fun ht _ => (ENNReal.ofReal_ne_top ht).elim)]

/-- A common decoder represents punctured internal singular metrics after
    every continuous compactly supported shift. -/
theorem IsWholePlaneGFF.exists_punctured_singularMetric_compactShift_decoder
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {D : Ω → ℂ → ℂ → ℝ} (h : IsWholePlaneGFF P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hD : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
      ENNReal.ofReal (D ω u v) =
        weylScaling (𝔇 (hC ω)) ξ (fun z => -α * Real.log ‖z‖) u v)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (ψ : ℂ → ℝ) (hψ : IsTestFunction univ ψ) (hψint : ∫ x, ψ x = 1)
    (f₀ : ℂ → ℝ) (hf₀ : Continuous f₀) (U : ℕ → Set ℂ) (hU : ∀ n, IsOpen (U n))
    (p : ℕ → ℂ × ℂ) (hp : ∀ n, (p n).1 ∈ U n ∧ (p n).1 ≠ 0) (hξ : 0 ≤ ξ) :
    ∃ F : (LocalZeroMeanTest univ → ℝ) → ℕ → ℝ≥0∞, Measurable F ∧
      (∀ᵐ ω ∂P, ∀ n, F (localModConstPairings 0 hC univ ω) n =
        ENNReal.ofReal (Real.exp (ξ * (-(hC ω ψ + ∫ z, f₀ z * ψ z)))) *
          internalMetric (D ω) (U n \ {0}) (p n).1 (p n).2) ∧
      ∀ g : ℂ → ℝ, Continuous g → HasCompactSupport g →
        ∀ᵐ ω ∂P, ∀ n, F (localModConstPairings 0
          (fun ω => addFunPairing (hC ω) g) univ ω) n =
          ENNReal.ofReal (Real.exp (ξ * (-(hC ω ψ + ∫ z, (g z + f₀ z) * ψ z)))) *
            internalMetric (fun x y => (weylScaling (D ω) ξ g x y).toReal)
              (U n \ {0}) (p n).1 (p n).2 := by
  let r : ℕ → ℕ → ℝ := fun n m => min (‖(p n).1‖ / 2) (1 / (m + 1 : ℝ))
  let V : ℕ → ℕ → Set ℂ := fun n m => U n ∩ {z | r n m < ‖z‖}
  have hr (n m : ℕ) : 0 < r n m := by
    exact lt_min (div_pos (norm_pos_iff.mpr (hp n).2) (by norm_num)) (by positivity)
  have hopen (n m : ℕ) : IsOpen (V n m) :=
    (hU n).inter (isOpen_lt continuous_const continuous_norm)
  have hmono (n : ℕ) : Monotone (V n) := by
    intro m k hmk z hz
    refine ⟨hz.1, ?_⟩
    change r n k < ‖z‖
    apply lt_of_le_of_lt ?_ hz.2
    apply min_le_min_left
    gcongr
  have haway (n m : ℕ) (z : ℂ) (hz : z ∈ V n m) : r n m ≤ ‖z‖ := hz.2.le
  have hpV (n m : ℕ) : (p n).1 ∈ V n m := by
    refine ⟨(hp n).1, ?_⟩
    change r n m < ‖(p n).1‖
    have hpos := norm_pos_iff.mpr (hp n).2
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hunion (n : ℕ) : (⋃ m, V n m) = U n \ {0} := by
    apply subset_antisymm
    · intro z hz
      obtain ⟨m, hzm⟩ := mem_iUnion.mp hz
      refine ⟨hzm.1, ?_⟩
      simp only [mem_singleton_iff]
      intro hz0
      have hpos := (hr n m).trans hzm.2
      have hcontradiction : (0 : ℝ) < 0 := by simpa only [hz0, norm_zero] using hpos
      exact (lt_irrefl 0) hcontradiction
    · intro z hz
      have hz' : z ∈ ⋃ m : ℕ, U n ∩ {z : ℂ | 1 / (m + 1 : ℝ) < ‖z‖} := by
        rw [punctured_open_exhaustion]
        exact hz
      obtain ⟨m, hzm⟩ := mem_iUnion.mp hz'
      refine mem_iUnion.mpr ⟨m, hzm.1, ?_⟩
      change r n m < ‖z‖
      exact lt_of_le_of_lt (min_le_right _ _) hzm.2
  obtain ⟨F, hF, hb, hs⟩ := h.exists_exhausted_singularMetric_compactShift_decoder
    𝔇 h𝔇 hD hmetric ψ hψ hψint f₀ hf₀ r hr V hopen hmono haway p hpV hξ
  refine ⟨F, hF, ?_, ?_⟩
  · filter_upwards [hb] with ω hω n
    simpa only [hunion] using hω n
  · intro g hg hc
    filter_upwards [hs g hg hc] with ω hω n
    simpa only [hunion] using hω n



/-- The normalized measure and punctured singular internal distances have
    a common whole-plane field decoder for compact smooth shifts. -/
theorem IsWholePlaneGFF.exists_joint_punctured_singular_compact_weyl_shift_decoder
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α ε : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} {D : Ω → ℂ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hfull : ∀ᵐ ω ∂P, ∀ U : Set ℂ, IsOpen U → U.Nonempty → 0 < μ ω U)
    (hε : 0 < ε) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ)
    (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hD : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
      ENNReal.ofReal (D ω u v) =
        weylScaling (𝔇 (hC ω)) ξ (fun x => -α * Real.log ‖x‖) u v)
    (hDfield : IsLQGMetricOfField P γ ξ α hC D)
    (haxioms : LQGMetricFieldAxioms P γ ξ α hC hcirc)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hα : α < lqgQ γ) (hξ : 0 ≤ ξ)
    (ψ : ℂ → ℝ) (hψ : IsTestFunction univ ψ) (hψint : ∫ x, ψ x = 1)
    (f : ℂ → ℝ) (hf : Continuous f) (U : ℕ → Set ℂ) (hU : ∀ n, IsOpen (U n))
    (p : ℕ → ℂ × ℂ) (hp : ∀ n, (p n).1 ∈ U n ∧ (p n).1 ≠ 0) :
    ∃ R ∈ Ioo (0 : ℝ) ε,
      ∃ F : (LocalZeroMeanTest univ → ℝ) → Measure ℂ × (ℕ → ℝ≥0∞), Measurable F ∧
        (∀ᵐ ω ∂P, F (localModConstPairings 0 hC univ ω) =
          (normalizedRestriction (μ ω) (ball 0 R), fun n =>
            ENNReal.ofReal (Real.exp (ξ * (-(hC ω ψ + ∫ z, f z * ψ z)))) *
              internalMetric (D ω) (U n \ {0}) (p n).1 (p n).2)) ∧
        ∀ g : ℂ → ℝ, IsTestFunction univ g →
          (∀ᵐ ω ∂P, F (localModConstPairings 0
            (fun ω => addFunPairing (hC ω) g) univ ω) =
            (normalizedRestriction ((μ ω).withDensity
              (fun z => ENNReal.ofReal (Real.exp (γ * g z)))) (ball 0 R), fun n =>
                ENNReal.ofReal (Real.exp (ξ * (-(hC ω ψ + ∫ z, (g z + f z) * ψ z)))) *
                  internalMetric (fun x y => (weylScaling (D ω) ξ g x y).toReal)
                    (U n \ {0}) (p n).1 (p n).2)) ∧
          P.map (F ∘ localModConstPairings 0
            (fun ω => addFunPairing (hC ω) g) univ) ≪
            P.map (F ∘ localModConstPairings 0 hC univ) ∧
          P.map (F ∘ localModConstPairings 0 hC univ) ≪
            P.map (F ∘ localModConstPairings 0
              (fun ω => addFunPairing (hC ω) g) univ) := by
  have hmetric := ae_isEuclideanLengthMetric_of_metricFieldAxioms P γ ξ α hC hcirc D
    haxioms h hγ hγ₂ hα hDfield
  obtain ⟨G, hG, hGbase, hGshift⟩ :=
    h.exists_punctured_singularMetric_compactShift_decoder 𝔇 h𝔇 hD hmetric ψ hψ hψint f hf U hU p hp hξ
  obtain ⟨R, hR, M, hM, _, hMeq⟩ := h.exists_shifted_normalized_measure_decoder hμ hfull hε
  let Q : (LocalZeroMeanTest univ → ℝ) → LocalZeroMeanTest (ball 0 ε) → ℝ :=
    fun v φ => v ⟨φ.1, φ.2.1.mono_set (subset_univ _), φ.2.2⟩ -
      α * ∫ x, φ.1 x * Real.log ‖x‖
  have hQ : Measurable Q := by
    apply measurable_pi_iff.mpr
    intro φ
    exact (measurable_pi_apply
      (⟨φ.1, φ.2.1.mono_set (subset_univ _), φ.2.2⟩ : LocalZeroMeanTest univ)).sub_const _
  have hQeq (T : (ℂ → ℝ) → ℝ) :
      Q (localModConstPairings 0 id univ T) = localModConstPairings α id (ball 0 ε) T := by
    funext φ
    simp [Q, localModConstPairings, fieldPairing]
  let F := fun v => (M (Q v), G v)
  have hF : Measurable F := (hM.comp hQ).prodMk hG
  have hzero : (fun ω => addFunPairing (hC ω) (fun _ => 0)) = hC := by
    funext ω φ
    simp [addFunPairing]
  have hzeroTest : IsTestFunction univ (fun _ : ℂ => (0 : ℝ)) :=
    ⟨contDiff_const, HasCompactSupport.zero, by simp⟩
  have hbase := hMeq (fun _ => 0) hzeroTest
  simp only [hzero, mul_zero, Real.exp_zero, ENNReal.ofReal_one] at hbase
  have hwone (ω : Ω) : (μ ω).withDensity (fun _ => 1) = μ ω := withDensity_one
  simp only [hwone] at hbase
  refine ⟨R, hR, F, hF, ?_, ?_⟩
  · filter_upwards [hbase, hGbase] with ω hm hg
    apply Prod.ext
    · change M (Q (localModConstPairings 0 id univ (hC ω))) = _
      rw [hQeq]
      exact hm
    · funext n
      exact hg n
  · intro g hg
    let X := localModConstPairings 0 hC univ
    let Y := localModConstPairings 0 (fun ω => addFunPairing (hC ω) g) univ
    have hX : Measurable X := by
      apply measurable_pi_iff.mpr
      intro φ
      change Measurable (fun ω => hC ω φ.1 - 0 * ∫ x, φ.1 x * Real.log ‖x‖)
      exact (h.measurable_pairing φ.1 φ.2.1).sub_const _
    have hY : Measurable Y := by
      apply measurable_pi_iff.mpr
      intro φ
      change Measurable (fun ω => (hC ω φ.1 + ∫ x, g x * φ.1 x) -
        0 * ∫ x, φ.1 x * Real.log ‖x‖)
      exact ((h.measurable_pairing φ.1 φ.2.1).add_const _).sub_const _
    have hac := h.singular_smooth_shift_modConst_pairing_laws hg 0 univ
    change P.map Y ≪ P.map X ∧ P.map X ≪ P.map Y at hac
    have hf := hac.1.map hF
    have hb := hac.2.map hF
    rw [Measure.map_map hF hY, Measure.map_map hF hX] at hf
    rw [Measure.map_map hF hX, Measure.map_map hF hY] at hb
    refine ⟨?_, hf, hb⟩
    filter_upwards [hMeq g hg, hGshift g hg.1.continuous hg.2.1] with ω hm hg'
    apply Prod.ext
    · change M (Q (localModConstPairings 0 id univ (addFunPairing (hC ω) g))) = _
      rw [hQeq]
      exact hm
    · funext n
      exact hg' n



/-- Countably many punctured internal distances have a local field decoder
with the normalization determined by a fixed unit-integral test function. -/
theorem IsWholePlaneGFF.exists_local_punctured_singularMetric_decoder
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {D : Ω → ℂ → ℂ → ℝ} (h : IsWholePlaneGFF P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hD : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
      ENNReal.ofReal (D ω u v) =
        weylScaling (𝔇 (hC ω)) ξ (fun z => -α * Real.log ‖z‖) u v)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    {U V : Set ℂ} (hV : IsOpen V) (hVU : V ⊆ U)
    (ψ : ℂ → ℝ) (hψ : IsTestFunction U ψ) (hψint : ∫ z, ψ z = 1)
    (p : ℕ → ℂ × ℂ) :
    ∃ F : (LocalZeroMeanTest U → ℝ) → ℕ → ℝ≥0∞, Measurable F ∧
      ∀ᵐ ω ∂P, ∀ n, F (localModConstPairings α hC U ω) n =
        ENNReal.ofReal (Real.exp (ξ * (-hC ω ψ))) *
          internalMetric (D ω) (V \ {0}) (p n).1 (p n).2 := by
  let c : Ω → ℝ := fun ω => -hC ω ψ
  have hc : Measurable c := (h.measurable_pairing ψ (hψ.mono_set (subset_univ _))).neg
  obtain ⟨G, hG, hGeq⟩ := h.exists_shifted_internal_singularMetric_punctured
    𝔇 h𝔇 hD hmetric c hc hV hVU
  have hGmeas : Measurable[fieldSigmaAlgebra α
      (fun ω => addFunPairing (hC ω) (fun _ => -hC ω ψ)) U]
      (fun ω n => G ω (p n).1 (p n).2) := by
    let : MeasurableSpace Ω := fieldSigmaAlgebra α
      (fun ω => addFunPairing (hC ω) (fun _ => -hC ω ψ)) U
    exact measurable_pi_iff.mpr (fun n => hG (p n).1 (p n).2)
  obtain ⟨H, hH, hHeq⟩ := h.exists_modConst_observable_of_reference_shift ψ hψ hψint
    (fun ω n => G ω (p n).1 (p n).2) hGmeas
  let X := localModConstPairings α hC U
  have hHlocal : Measurable[MeasurableSpace.comap X inferInstance] H := by
    rw [← fieldSigmaAlgebraModConst_eq_comap_localModConstPairings]
    exact hH
  obtain ⟨F, hF, hFeq⟩ := hHlocal.exists_eq_measurable_comp
  refine ⟨F, hF, ?_⟩
  have hscale := h.ae_internal_singularMetric_add_random_constant 𝔇 h𝔇 hD c hc
  filter_upwards [hscale, hGeq, hHeq] with ω hs hg hh n
  change F (X ω) n = _
  calc
    F (X ω) n = H ω n := congrFun (congrFun hFeq ω).symm n
    _ = G ω (p n).1 (p n).2 := congrFun hh n
    _ = _ := (hg (p n).1 (p n).2).symm
    _ = _ := hs _ _ _


/-- The local decoder of normalized punctured distances also represents the
Weyl-shifted distances for every fixed smooth compactly supported shift. -/
theorem IsWholePlaneGFF.exists_local_punctured_singularMetric_compactShift_decoder
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {D : Ω → ℂ → ℂ → ℝ} (h : IsWholePlaneGFF P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hD : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
      ENNReal.ofReal (D ω u v) =
        weylScaling (𝔇 (hC ω)) ξ (fun z => -α * Real.log ‖z‖) u v)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    {U V : Set ℂ} (hV : IsOpen V) (hVU : V ⊆ U)
    (ψ : ℂ → ℝ) (hψ : IsTestFunction U ψ) (hψint : ∫ z, ψ z = 1)
    (p : ℕ → ℂ × ℂ) (hp : ∀ n, (p n).1 ∈ V ∧ (p n).1 ≠ 0)
    (hξ : 0 ≤ ξ) :
    ∃ F : (LocalZeroMeanTest U → ℝ) → ℕ → ℝ≥0∞, Measurable F ∧
      (∀ᵐ ω ∂P, ∀ n, F (localModConstPairings α hC U ω) n =
        ENNReal.ofReal (Real.exp (ξ * (-hC ω ψ))) *
          internalMetric (D ω) (V \ {0}) (p n).1 (p n).2) ∧
      ∀ g : ℂ → ℝ, IsTestFunction univ g →
        ∀ᵐ ω ∂P, ∀ n, F (localModConstPairings α
          (fun ω => addFunPairing (hC ω) g) U ω) n =
          ENNReal.ofReal (Real.exp (ξ * (-(hC ω ψ + ∫ z, g z * ψ z)))) *
            internalMetric (fun x y => (weylScaling (D ω) ξ g x y).toReal)
              (V \ {0}) (p n).1 (p n).2 := by
  obtain ⟨F, hF, hFb⟩ := h.exists_local_punctured_singularMetric_decoder
    𝔇 h𝔇 hD hmetric hV hVU ψ hψ hψint p
  obtain ⟨G, hG, hGb, hGs⟩ := h.exists_punctured_singularMetric_compactShift_decoder
    𝔇 h𝔇 hD hmetric ψ (hψ.mono_set (subset_univ _)) hψint
    (fun _ => 0) continuous_const (fun _ => V) (fun _ => hV) p hp hξ
  let X := localModConstPairings 0 hC univ
  let Q : (LocalZeroMeanTest univ → ℝ) → LocalZeroMeanTest U → ℝ :=
    fun v φ => v ⟨φ.1, φ.2.1.mono_set (subset_univ _), φ.2.2⟩ -
      α * ∫ z, φ.1 z * Real.log ‖z‖
  have hQ : Measurable Q := by
    apply measurable_pi_iff.mpr
    intro φ
    exact (measurable_pi_apply
      (⟨φ.1, φ.2.1.mono_set (subset_univ _), φ.2.2⟩ : LocalZeroMeanTest univ)).sub_const _
  have hQeq (T : (ℂ → ℝ) → ℝ) :
      Q (localModConstPairings 0 id univ T) = localModConstPairings α id U T := by
    funext φ
    simp [Q, localModConstPairings, fieldPairing]
  have hX : Measurable X := by
    apply measurable_pi_iff.mpr
    intro φ
    change Measurable (fun ω => hC ω φ.1 - 0 * ∫ z, φ.1 z * Real.log ‖z‖)
    exact (h.measurable_pairing φ.1 φ.2.1).sub_const _
  have hbase : G =ᵐ[P.map X] F ∘ Q := by
    apply (ae_map_iff hX.aemeasurable (measurableSet_eq_fun hG (hF.comp hQ))).2
    filter_upwards [hGb, hFb] with ω hg hf
    funext n
    change G (localModConstPairings 0 id univ (hC ω)) n =
      F (Q (localModConstPairings 0 id univ (hC ω))) n
    rw [hQeq]
    change G (localModConstPairings 0 hC univ ω) n =
      F (localModConstPairings α hC U ω) n
    rw [hf n]
    simpa using hg n
  refine ⟨F, hF, hFb, ?_⟩
  intro g hg
  let Y := localModConstPairings 0 (fun ω => addFunPairing (hC ω) g) univ
  have hY : Measurable Y := by
    apply measurable_pi_iff.mpr
    intro φ
    change Measurable (fun ω => (hC ω φ.1 + ∫ z, g z * φ.1 z) -
      0 * ∫ z, φ.1 z * Real.log ‖z‖)
    exact ((h.measurable_pairing φ.1 φ.2.1).add_const _).sub_const _
  have hac := (h.singular_smooth_shift_modConst_pairing_laws hg 0 univ).1
  change P.map Y ≪ P.map X at hac
  have heq := ae_eq_comp' hY.aemeasurable hbase hac
  filter_upwards [heq, hGs g hg.1.continuous hg.2.1] with ω he hs n
  have he' := congrFun he n
  change G (localModConstPairings 0 id univ (addFunPairing (hC ω) g)) n =
    F (Q (localModConstPairings 0 id univ (addFunPairing (hC ω) g))) n at he'
  rw [hQeq] at he'
  change G (localModConstPairings 0 (fun ω => addFunPairing (hC ω) g) univ ω) n =
    F (localModConstPairings α (fun ω => addFunPairing (hC ω) g) U ω) n at he'
  rw [← he']
  simpa using hs n


/-- The local centered field, normalized measure, and normalized punctured
internal distances have equivalent joint laws under smooth compact shifts. -/
theorem IsWholePlaneGFF.exists_local_joint_punctured_smooth_shift_law
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α ε : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} {D : Ω → ℂ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hfull : ∀ᵐ ω ∂P, ∀ W : Set ℂ, IsOpen W → W.Nonempty → 0 < μ ω W)
    (hε : 0 < ε) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ)
    (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hD : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
      ENNReal.ofReal (D ω u v) =
        weylScaling (𝔇 (hC ω)) ξ (fun z => -α * Real.log ‖z‖) u v)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    {V : Set ℂ} (hV : IsOpen V) (hVU : V ⊆ ball 0 ε)
    (ψ : ℂ → ℝ) (hψ : IsTestFunction (ball 0 ε) ψ) (hψint : ∫ z, ψ z = 1)
    (p : ℕ → ℂ × ℂ) (hp : ∀ n, (p n).1 ∈ V ∧ (p n).1 ≠ 0)
    (hξ : 0 ≤ ξ) :
    ∃ R ∈ Ioo (0 : ℝ) ε,
      ∀ g : ℂ → ℝ, IsTestFunction univ g →
        P.map (fun ω =>
          (localModConstPairings α (fun ω => addFunPairing (hC ω) g) (ball 0 ε) ω,
           normalizedRestriction ((μ ω).withDensity
             (fun z => ENNReal.ofReal (Real.exp (γ * g z)))) (ball 0 R),
           fun n => ENNReal.ofReal (Real.exp (ξ * (-(hC ω ψ + ∫ z, g z * ψ z)))) *
             internalMetric (fun x y => (weylScaling (D ω) ξ g x y).toReal)
               (V \ {0}) (p n).1 (p n).2)) ≪
        P.map (fun ω =>
          (localModConstPairings α hC (ball 0 ε) ω,
           normalizedRestriction (μ ω) (ball 0 R),
           fun n => ENNReal.ofReal (Real.exp (ξ * (-hC ω ψ))) *
             internalMetric (D ω) (V \ {0}) (p n).1 (p n).2)) ∧
        P.map (fun ω =>
          (localModConstPairings α hC (ball 0 ε) ω,
           normalizedRestriction (μ ω) (ball 0 R),
           fun n => ENNReal.ofReal (Real.exp (ξ * (-hC ω ψ))) *
             internalMetric (D ω) (V \ {0}) (p n).1 (p n).2)) ≪
        P.map (fun ω =>
          (localModConstPairings α (fun ω => addFunPairing (hC ω) g) (ball 0 ε) ω,
           normalizedRestriction ((μ ω).withDensity
             (fun z => ENNReal.ofReal (Real.exp (γ * g z)))) (ball 0 R),
           fun n => ENNReal.ofReal (Real.exp (ξ * (-(hC ω ψ + ∫ z, g z * ψ z)))) *
             internalMetric (fun x y => (weylScaling (D ω) ξ g x y).toReal)
               (V \ {0}) (p n).1 (p n).2)) := by
  obtain ⟨N, hN, hNb, hNs⟩ := h.exists_local_punctured_singularMetric_compactShift_decoder
    𝔇 h𝔇 hD hmetric hV hVU ψ hψ hψint p hp hξ
  obtain ⟨R, hR, M, hM, _, hMeq⟩ := h.exists_shifted_normalized_measure_decoder hμ hfull hε
  let F := fun v => (v, M v, N v)
  have hF : Measurable F := measurable_id.prodMk (hM.prodMk hN)
  have hzero : (fun ω => addFunPairing (hC ω) (fun _ => 0)) = hC := by
    funext ω φ
    simp [addFunPairing]
  have hzeroTest : IsTestFunction univ (fun _ : ℂ => (0 : ℝ)) :=
    ⟨contDiff_const, HasCompactSupport.zero, by simp⟩
  have hbase := hMeq (fun _ => 0) hzeroTest
  simp only [hzero, mul_zero, Real.exp_zero, ENNReal.ofReal_one] at hbase
  have hwone (ω : Ω) : (μ ω).withDensity (fun _ => 1) = μ ω := withDensity_one
  simp only [hwone] at hbase
  refine ⟨R, hR, ?_⟩
  intro g hg
  let X := localModConstPairings α hC (ball 0 ε)
  let Y := localModConstPairings α (fun ω => addFunPairing (hC ω) g) (ball 0 ε)
  have hX : Measurable X := by
    apply measurable_pi_iff.mpr
    intro φ
    change Measurable (fun ω => hC ω φ.1 - α * ∫ z, φ.1 z * Real.log ‖z‖)
    exact (h.measurable_pairing φ.1 (φ.2.1.mono_set (subset_univ _))).sub_const _
  have hY : Measurable Y := by
    apply measurable_pi_iff.mpr
    intro φ
    change Measurable (fun ω => (hC ω φ.1 + ∫ z, g z * φ.1 z) -
      α * ∫ z, φ.1 z * Real.log ‖z‖)
    exact ((h.measurable_pairing φ.1 (φ.2.1.mono_set (subset_univ _))).add_const _).sub_const _
  have hac := h.singular_smooth_shift_modConst_pairing_laws hg α (ball 0 ε)
  change P.map Y ≪ P.map X ∧ P.map X ≪ P.map Y at hac
  have hf := hac.1.map hF
  have hb := hac.2.map hF
  rw [Measure.map_map hF hY, Measure.map_map hF hX] at hf
  rw [Measure.map_map hF hX, Measure.map_map hF hY] at hb
  have hbaseMap : P.map (F ∘ X) = P.map (fun ω =>
      (X ω, normalizedRestriction (μ ω) (ball 0 R), fun n =>
        ENNReal.ofReal (Real.exp (ξ * (-hC ω ψ))) *
          internalMetric (D ω) (V \ {0}) (p n).1 (p n).2)) := by
    apply Measure.map_congr
    filter_upwards [hbase, hNb] with ω hm hn
    exact Prod.ext rfl (Prod.ext hm (funext hn))
  have hshiftMap : P.map (F ∘ Y) = P.map (fun ω =>
      (Y ω, normalizedRestriction ((μ ω).withDensity
        (fun z => ENNReal.ofReal (Real.exp (γ * g z)))) (ball 0 R), fun n =>
          ENNReal.ofReal (Real.exp (ξ * (-(hC ω ψ + ∫ z, g z * ψ z)))) *
            internalMetric (fun x y => (weylScaling (D ω) ξ g x y).toReal)
              (V \ {0}) (p n).1 (p n).2)) := by
    apply Measure.map_congr
    filter_upwards [hMeq g hg, hNs g hg] with ω hm hn
    exact Prod.ext rfl (Prod.ext hm (funext hn))
  rw [hbaseMap, hshiftMap] at hf hb
  exact ⟨hf, hb⟩

/-- An upper bound for a Weyl weight transfers point removal between
Euclidean length metrics. -/
theorem IsEuclideanLengthMetric.internalMetric_sdiff_zero_eq_of_weyl_bounded_above
    {D E : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hE : IsEuclideanLengthMetric E) {ξ B : ℝ} {f : ℂ → ℝ}
    {V : Set ℂ} (hV : IsOpen V)
    (hscale : ∀ x y, ENNReal.ofReal (E x y) = weylScaling D ξ f x y)
    (hupper : ∀ z ∈ V \ {0}, ξ * f z ≤ B)
    (hremove : ∀ a ∈ V \ {0}, ∀ b ∈ V \ {0},
      internalMetric D (V \ {0}) a b = internalMetric D V a b)
    {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) :
    internalMetric E (V \ {0}) x y = internalMetric E V x y := by
  by_cases h0 : (0 : ℂ) ∈ V
  · have hcheap := hD.small_detours_of_internalMetric_sdiff_zero_eq hV h0 hremove
    have hnonneg (u v : ℂ) : 0 ≤ E u v := by
      have ht := hE.triangle u v u
      rw [hE.self_eq_zero, hE.symm v u] at ht
      linarith
    apply hE.internalMetric_sdiff_zero_eq_of_small_detours hx hy
    intro ε hε
    let k : ℝ≥0 := ⟨Real.exp B, (Real.exp_pos B).le⟩
    have hk : 0 < k := Real.exp_pos B
    obtain ⟨r, hr, hbound⟩ := hcheap (ε / k) (div_pos hε hk)
    refine ⟨r, hr, ?_⟩
    intro a b ha hb ha0 hb0 har hbr
    have hcomp := hD.internalMetric_weylScaling_le hE hnonneg
      (U := V \ {0}) (hV.sdiff isClosed_singleton) (hD.weylScaling_zero ξ) hscale
      (B := B) hupper a b
    have ht := hbound a b ha hb ha0 hb0 har hbr
    have hk0 : (k : ℝ≥0∞) ≠ 0 := by exact_mod_cast (ne_of_gt hk)
    have hktop : (k : ℝ≥0∞) ≠ ∞ := ENNReal.coe_ne_top
    have hlt : (k : ℝ≥0∞) * internalMetric D (V \ {0}) a b <
        (k : ℝ≥0∞) * ((ε / k : ℝ≥0) : ℝ≥0∞) :=
      by simpa only [mul_comm] using ENNReal.mul_lt_mul_left hk0 hktop ht
    have hcancel : (k : ℝ≥0∞) * ((ε / k : ℝ≥0) : ℝ≥0∞) = ε := by
      rw [← ENNReal.coe_mul, mul_div_cancel₀ _ (ne_of_gt hk)]
    have hkof : ENNReal.ofReal (Real.exp B) = (k : ℝ≥0∞) := by
      change ENNReal.ofReal (k : ℝ) = (k : ℝ≥0∞)
      exact ENNReal.ofReal_coe_nnreal
    rw [hkof] at hcomp
    exact hcomp.trans_lt (hcancel ▸ hlt)
  · have hs : V \ {0} = V := by
      ext z
      simp only [Set.mem_sdiff, mem_singleton_iff]
      constructor
      · exact fun hz => hz.1
      · intro hz
        exact ⟨hz, fun hz0 => h0 (hz0 ▸ hz)⟩
    rw [hs]

/-- Point removal persists under every continuous compactly supported
Weyl shift, including shifts of either sign. -/
theorem IsEuclideanLengthMetric.internalMetric_sdiff_zero_eq_of_compact_weyl
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {ξ : ℝ} (hξ : 0 ≤ ξ)
    (f : ℂ → ℝ) (hf : Continuous f) (hc : HasCompactSupport f)
    {V : Set ℂ} (hV : IsOpen V)
    (hremove : ∀ a ∈ V \ {0}, ∀ b ∈ V \ {0},
      internalMetric D (V \ {0}) a b = internalMetric D V a b)
    {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) :
    internalMetric (fun a b => (weylScaling D ξ f a b).toReal) (V \ {0}) x y =
      internalMetric (fun a b => (weylScaling D ξ f a b).toReal) V x y := by
  obtain ⟨m, hm⟩ := exists_lower_bound_of_continuous_compactSupport f hf hc
  obtain ⟨c, hc'⟩ := exists_lower_bound_of_continuous_compactSupport (fun z => -f z) hf.neg hc.neg
  let M := -c
  let g : ℂ → ℝ := fun z => f z - M
  have hglo : ∀ z, m - M ≤ g z := fun z => by dsimp [g]; linarith [hm z]
  have hghi : ∀ z, g z ≤ 0 := fun z => by dsimp [g, M]; linarith [hc' z]
  have hfg : ∀ z, f z = g z + M := fun z => by dsimp [g]; ring
  have hfinite (u v : ℂ) : weylScaling D ξ f u v ≠ ∞ := by
    rw [weylScaling_eq_exp_mul_of_shift D ξ M f g hfg u v]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (weylScaling_negative_bump_real_bounds hD hξ g hglo hghi (hD.weylScaling_zero ξ) u v).1.ne
  apply hD.internalMetric_sdiff_zero_eq_of_weyl_bounded_above
    (hD.weylScaling_compact_isLengthMetric hξ f hf hc) hV
    (fun u v => ENNReal.ofReal_toReal (hfinite u v)) (B := ξ * M) ?_ hremove hx hy
  intro z hz
  exact mul_le_mul_of_nonneg_left (by have := hc' z; dsimp [M]; linarith) hξ

/-- Point removal extends the local joint shift law to internal distances
on the full observation domain between nonzero endpoints. -/
theorem IsWholePlaneGFF.exists_local_joint_smooth_shift_law_of_point_removal
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α ε : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} {D : Ω → ℂ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hfull : ∀ᵐ ω ∂P, ∀ W : Set ℂ, IsOpen W → W.Nonempty → 0 < μ ω W)
    (hε : 0 < ε) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ)
    (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hD : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
      ENNReal.ofReal (D ω u v) =
        weylScaling (𝔇 (hC ω)) ξ (fun z => -α * Real.log ‖z‖) u v)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    {V : Set ℂ} (hV : IsOpen V) (hVU : V ⊆ ball 0 ε)
    (ψ : ℂ → ℝ) (hψ : IsTestFunction (ball 0 ε) ψ) (hψint : ∫ z, ψ z = 1)
    (p : ℕ → ℂ × ℂ) (hp : ∀ n, (p n).1 ∈ V ∧ (p n).1 ≠ 0)
    (hp₂ : ∀ n, (p n).2 ≠ 0) (hξ : 0 ≤ ξ)
    (hremove : ∀ᵐ ω ∂P, ∀ a ∈ V \ {0}, ∀ b ∈ V \ {0},
      internalMetric (D ω) (V \ {0}) a b = internalMetric (D ω) V a b) :
    ∃ R ∈ Ioo (0 : ℝ) ε,
      ∀ g : ℂ → ℝ, IsTestFunction univ g →
        P.map (fun ω =>
          (localModConstPairings α (fun ω => addFunPairing (hC ω) g) (ball 0 ε) ω,
           normalizedRestriction ((μ ω).withDensity
             (fun z => ENNReal.ofReal (Real.exp (γ * g z)))) (ball 0 R),
           fun n => ENNReal.ofReal (Real.exp (ξ * (-(hC ω ψ + ∫ z, g z * ψ z)))) *
             internalMetric (fun x y => (weylScaling (D ω) ξ g x y).toReal)
               V (p n).1 (p n).2)) ≪
        P.map (fun ω =>
          (localModConstPairings α hC (ball 0 ε) ω,
           normalizedRestriction (μ ω) (ball 0 R),
           fun n => ENNReal.ofReal (Real.exp (ξ * (-hC ω ψ))) *
             internalMetric (D ω) V (p n).1 (p n).2)) ∧
        P.map (fun ω =>
          (localModConstPairings α hC (ball 0 ε) ω,
           normalizedRestriction (μ ω) (ball 0 R),
           fun n => ENNReal.ofReal (Real.exp (ξ * (-hC ω ψ))) *
             internalMetric (D ω) V (p n).1 (p n).2)) ≪
        P.map (fun ω =>
          (localModConstPairings α (fun ω => addFunPairing (hC ω) g) (ball 0 ε) ω,
           normalizedRestriction ((μ ω).withDensity
             (fun z => ENNReal.ofReal (Real.exp (γ * g z)))) (ball 0 R),
           fun n => ENNReal.ofReal (Real.exp (ξ * (-(hC ω ψ + ∫ z, g z * ψ z)))) *
             internalMetric (fun x y => (weylScaling (D ω) ξ g x y).toReal)
               V (p n).1 (p n).2)) := by
  obtain ⟨R, hR, hlaw⟩ := h.exists_local_joint_punctured_smooth_shift_law
    hμ hfull hε 𝔇 h𝔇 hD hmetric hV hVU ψ hψ hψint p hp hξ
  refine ⟨R, hR, ?_⟩
  intro g hg
  have hb : ∀ᵐ ω ∂P, ∀ n,
      internalMetric (D ω) (V \ {0}) (p n).1 (p n).2 =
        internalMetric (D ω) V (p n).1 (p n).2 := by
    filter_upwards [hmetric, hremove] with ω hm hr n
    exact hm.internalMetric_sdiff_zero_eq_of_weyl_bounded_above hm hV
      (fun u v => (hm.weylScaling_zero ξ u v).symm)
      (B := 0) (f := fun _ => 0) (by simp) hr (hp n).2 (hp₂ n)
  have hs : ∀ᵐ ω ∂P, ∀ n,
      internalMetric (fun x y => (weylScaling (D ω) ξ g x y).toReal)
        (V \ {0}) (p n).1 (p n).2 =
      internalMetric (fun x y => (weylScaling (D ω) ξ g x y).toReal)
        V (p n).1 (p n).2 := by
    filter_upwards [hmetric, hremove] with ω hm hr n
    exact hm.internalMetric_sdiff_zero_eq_of_compact_weyl hξ g hg.1.continuous hg.2.1
      hV hr (hp n).2 (hp₂ n)
  have hbase : P.map (fun ω =>
      (localModConstPairings α hC (ball 0 ε) ω,
       normalizedRestriction (μ ω) (ball 0 R), fun n =>
         ENNReal.ofReal (Real.exp (ξ * (-hC ω ψ))) *
           internalMetric (D ω) (V \ {0}) (p n).1 (p n).2)) =
      P.map (fun ω =>
      (localModConstPairings α hC (ball 0 ε) ω,
       normalizedRestriction (μ ω) (ball 0 R), fun n =>
         ENNReal.ofReal (Real.exp (ξ * (-hC ω ψ))) *
           internalMetric (D ω) V (p n).1 (p n).2)) := by
    apply Measure.map_congr
    filter_upwards [hb] with ω he
    simp only [Prod.mk.injEq, true_and]
    funext n
    rw [he n]
  have hshift : P.map (fun ω =>
      (localModConstPairings α (fun ω => addFunPairing (hC ω) g) (ball 0 ε) ω,
       normalizedRestriction ((μ ω).withDensity
         (fun z => ENNReal.ofReal (Real.exp (γ * g z)))) (ball 0 R), fun n =>
         ENNReal.ofReal (Real.exp (ξ * (-(hC ω ψ + ∫ z, g z * ψ z)))) *
           internalMetric (fun x y => (weylScaling (D ω) ξ g x y).toReal)
             (V \ {0}) (p n).1 (p n).2)) =
      P.map (fun ω =>
      (localModConstPairings α (fun ω => addFunPairing (hC ω) g) (ball 0 ε) ω,
       normalizedRestriction ((μ ω).withDensity
         (fun z => ENNReal.ofReal (Real.exp (γ * g z)))) (ball 0 R), fun n =>
         ENNReal.ofReal (Real.exp (ξ * (-(hC ω ψ + ∫ z, g z * ψ z)))) *
           internalMetric (fun x y => (weylScaling (D ω) ξ g x y).toReal)
             V (p n).1 (p n).2)) := by
    apply Measure.map_congr
    filter_upwards [hs] with ω he
    simp only [Prod.mk.injEq, true_and]
    funext n
    rw [he n]
  have hh := hlaw g hg
  rw [hbase, hshift] at hh
  exact hh


/-- A positive finite multiple of the internal root distance is determined by
countably many punctured distances. -/
theorem IsEuclideanLengthMetric.root_eq_limsup_punctured_scaled
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {O : Set ℂ} (hO : IsOpen O) (hconn : IsConnected O) (h0 : (0 : ℂ) ∈ O)
    {ε : ℝ} (hball : ball (0 : ℂ) ε ⊆ O) {x : ℂ} (hx : x ∈ O) (hx0 : x ≠ 0)
    (s : ℕ → ℝ) (hs : Tendsto s atTop (𝓝 0)) (hpos : ∀ n, 0 < s n)
    (hsε : ∀ n, s n < ε) (C : ℕ → Set ℂ)
    (hC : ∀ n, C n ⊆ sphere (0 : ℂ) (s n) ∧ (C n).Countable ∧
      sphere (0 : ℂ) (s n) ⊆ closure (C n))
    {c : ℝ≥0∞} (hc0 : c ≠ 0) (hct : c ≠ ∞) :
    c * internalMetric D O 0 x =
      limsup (fun n => ⨅ z ∈ C n, c * internalMetric D (O \ {0}) z x) atTop := by
  have hfin := S11m.internalMetric_ne_top_of_isConnected hD hO hconn h0 hx
  have hroot := S11m.internalMetric_root_eq_limsup_of_dense hD
    (S11m.isEuclideanLengthMetric_nonneg hD) hO h0 hball hx hx0 hfin s hs hpos hsε C hC
  calc
    c * internalMetric D O 0 x =
        c * limsup (fun n => ⨅ z ∈ C n, internalMetric D (O \ {0}) z x) atTop := by rw [hroot]
    _ = limsup (fun n => c * ⨅ z ∈ C n, internalMetric D (O \ {0}) z x) atTop := by
      rw [ENNReal.limsup_const_mul_of_ne_top hct]
    _ = _ := by
      congr 1
      funext n
      simp only [ENNReal.mul_iInf_of_ne hc0 hct]

/-- Reconstruct a root distance from a fixed family of punctured distances. -/
noncomputable def puncturedRootFrom (C : ℕ → Set ℂ) (F : ℂ → ℂ → ℝ≥0∞) (x : ℂ) : ℝ≥0∞ :=
  limsup (fun n => ⨅ z ∈ C n, F z x) atTop

/-- Root reconstruction is measurable in the punctured distances. -/
theorem measurable_puncturedRootFrom {A : Type*} [MeasurableSpace A]
    (C : ℕ → Set ℂ) (hC : ∀ n, (C n).Countable)
    (F : A → ℂ → ℂ → ℝ≥0∞) (hF : ∀ z x, Measurable fun a => F a z x) (x : ℂ) :
    Measurable fun a => puncturedRootFrom C (F a) x := by
  unfold puncturedRootFrom
  refine S11m.measurable_limsup_nat _ fun n => ?_
  exact S11m.measurable_biInf_of_countable (hC n) (fun z a => F a z x) fun z => hF z x

/-- Internal distances between nonzero points are recovered from punctured
and root distances without a point-removal hypothesis. -/
theorem IsEuclideanLengthMetric.internalMetric_eq_min_punctured_scaled
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) (O : Set ℂ)
    (c : ℝ≥0∞) (x y : ℂ) :
    c * internalMetric D O x y =
      min (c * internalMetric D (O \ {0}) x y)
        (c * internalMetric D O 0 x + c * internalMetric D O 0 y) := by
  rw [S11m.internalMetric_eq_min_punctured hD O, hD.internalMetric_symm O x 0, ← mul_add]
  have hmono : Monotone (fun t : ℝ≥0∞ => c * t) := fun a b hab => by dsimp only; gcongr
  exact Monotone.map_min hmono

/-- A countable punctured-distance decoder determines the normalized root
internal distance. -/
theorem IsEuclideanLengthMetric.puncturedRootFrom_eq
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {O : Set ℂ} (hO : IsOpen O) (hconn : IsConnected O) (h0 : (0 : ℂ) ∈ O)
    {ε : ℝ} (hball : ball (0 : ℂ) ε ⊆ O) {x : ℂ} (hx : x ∈ O) (hx0 : x ≠ 0)
    (s : ℕ → ℝ) (hs : Tendsto s atTop (𝓝 0)) (hpos : ∀ n, 0 < s n)
    (hsε : ∀ n, s n < ε) (C : ℕ → Set ℂ)
    (hC : ∀ n, C n ⊆ sphere (0 : ℂ) (s n) ∧ (C n).Countable ∧
      sphere (0 : ℂ) (s n) ⊆ closure (C n))
    {c : ℝ≥0∞} (hc0 : c ≠ 0) (hct : c ≠ ∞) (F : ℂ → ℂ → ℝ≥0∞)
    (hF : ∀ n z, z ∈ C n → F z x = c * internalMetric D (O \ {0}) z x) :
    puncturedRootFrom C F x = c * internalMetric D O 0 x := by
  rw [hD.root_eq_limsup_punctured_scaled hO hconn h0 hball hx hx0 s hs hpos hsε C hC hc0 hct]
  unfold puncturedRootFrom
  congr 1
  funext n
  refine iInf_congr fun z => ?_
  by_cases hz : z ∈ C n
  · rw [iInf_pos hz, iInf_pos hz, hF n z hz]
  · rw [iInf_neg hz, iInf_neg hz]



/-- Reconstruct full internal distances from punctured distances. -/
noncomputable def puncturedDistanceFrom (C : ℕ → Set ℂ) (F : ℂ → ℂ → ℝ≥0∞) (x y : ℂ) : ℝ≥0∞ :=
  if x = 0 then
    if y = 0 then 0 else puncturedRootFrom C F y
  else if y = 0 then puncturedRootFrom C F x
  else min (F x y) (puncturedRootFrom C F x + puncturedRootFrom C F y)

/-- Reconstructed internal distances are measurable in punctured distances. -/
theorem measurable_puncturedDistanceFrom {A : Type*} [MeasurableSpace A]
    (C : ℕ → Set ℂ) (hC : ∀ n, (C n).Countable)
    (F : A → ℂ → ℂ → ℝ≥0∞) (hF : ∀ z x, Measurable fun a => F a z x) (x y : ℂ) :
    Measurable fun a => puncturedDistanceFrom C (F a) x y := by
  unfold puncturedDistanceFrom
  split_ifs
  · exact measurable_const
  · exact measurable_puncturedRootFrom C hC F hF y
  · exact measurable_puncturedRootFrom C hC F hF x
  · exact (hF x y).min ((measurable_puncturedRootFrom C hC F hF x).add
      (measurable_puncturedRootFrom C hC F hF y))

/-- A countable collection of punctured distances determines full internal
 distances on a connected open set. -/
theorem IsEuclideanLengthMetric.puncturedDistanceFrom_eq
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {O : Set ℂ} (hO : IsOpen O) (hconn : IsConnected O) (h0 : (0 : ℂ) ∈ O)
    {ε : ℝ} (hball : ball (0 : ℂ) ε ⊆ O) {x y : ℂ} (hx : x ∈ O) (hy : y ∈ O)
    (s : ℕ → ℝ) (hs : Tendsto s atTop (𝓝 0)) (hpos : ∀ n, 0 < s n)
    (hsε : ∀ n, s n < ε) (C : ℕ → Set ℂ)
    (hC : ∀ n, C n ⊆ sphere (0 : ℂ) (s n) ∧ (C n).Countable ∧
      sphere (0 : ℂ) (s n) ⊆ closure (C n))
    {c : ℝ≥0∞} (hc0 : c ≠ 0) (hct : c ≠ ∞) (F : ℂ → ℂ → ℝ≥0∞)
    (hFx : x ≠ 0 → ∀ n z, z ∈ C n → F z x = c * internalMetric D (O \ {0}) z x)
    (hFy : y ≠ 0 → ∀ n z, z ∈ C n → F z y = c * internalMetric D (O \ {0}) z y)
    (hFxy : x ≠ 0 → y ≠ 0 → F x y = c * internalMetric D (O \ {0}) x y) :
    puncturedDistanceFrom C F x y = c * internalMetric D O x y := by
  have hroot (z : ℂ) (hz : z ∈ O) (hz0 : z ≠ 0)
      (hFz : ∀ n w, w ∈ C n → F w z = c * internalMetric D (O \ {0}) w z) :
      puncturedRootFrom C F z = c * internalMetric D O 0 z :=
    hD.puncturedRootFrom_eq hO hconn h0 hball hz hz0 s hs hpos hsε C hC hc0 hct F hFz
  unfold puncturedDistanceFrom
  by_cases hx0 : x = 0
  · subst x
    simp only [↓reduceIte]
    by_cases hy0 : y = 0
    · subst y
      simp only [↓reduceIte]
      rw [hD.internalMetric_self_of_mem_open (S11m.isEuclideanLengthMetric_nonneg hD) hO h0, mul_zero]
    · simp only [hy0, ↓reduceIte]
      exact hroot y hy hy0 (hFy hy0)
  · simp only [hx0, ↓reduceIte]
    by_cases hy0 : y = 0
    · subst y
      simp only [↓reduceIte]
      rw [hD.internalMetric_symm O x 0]
      exact hroot x hx hx0 (hFx hx0)
    · simp only [hy0, ↓reduceIte]
      rw [hFxy hx0 hy0, hroot x hx hx0 (hFx hx0), hroot y hy hy0 (hFy hy0)]
      exact (hD.internalMetric_eq_min_punctured_scaled O c x y).symm



/-- A local punctured-distance decoder can be indexed by any nonempty
countable set of endpoint pairs with nonzero first endpoint in the domain. -/
theorem IsWholePlaneGFF.exists_local_punctured_singularMetric_compactShift_decoder_countable
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {D : Ω → ℂ → ℂ → ℝ} (h : IsWholePlaneGFF P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hD : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
      ENNReal.ofReal (D ω u v) =
        weylScaling (𝔇 (hC ω)) ξ (fun z => -α * Real.log ‖z‖) u v)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    {U V : Set ℂ} (hV : IsOpen V) (hVU : V ⊆ U)
    (ψ : ℂ → ℝ) (hψ : IsTestFunction U ψ) (hψint : ∫ z, ψ z = 1)
    (S : Set (ℂ × ℂ)) (hS : S.Countable) (hSne : S.Nonempty)
    (hSV : ∀ q ∈ S, q.1 ∈ V ∧ q.1 ≠ 0) (hξ : 0 ≤ ξ) :
    ∃ F : (LocalZeroMeanTest U → ℝ) → (ℂ × ℂ) → ℝ≥0∞, Measurable F ∧
      (∀ᵐ ω ∂P, ∀ q ∈ S, F (localModConstPairings α hC U ω) q =
        ENNReal.ofReal (Real.exp (ξ * (-hC ω ψ))) *
          internalMetric (D ω) (V \ {0}) q.1 q.2) ∧
      ∀ g : ℂ → ℝ, IsTestFunction univ g →
        ∀ᵐ ω ∂P, ∀ q ∈ S, F (localModConstPairings α
          (fun ω => addFunPairing (hC ω) g) U ω) q =
          ENNReal.ofReal (Real.exp (ξ * (-(hC ω ψ + ∫ z, g z * ψ z)))) *
            internalMetric (fun x y => (weylScaling (D ω) ξ g x y).toReal)
              (V \ {0}) q.1 q.2 := by
  classical
  obtain ⟨p, hp⟩ := hS.exists_eq_range hSne
  have hpV : ∀ n, (p n).1 ∈ V ∧ (p n).1 ≠ 0 := by
    intro n
    apply hSV
    rw [hp]
    exact mem_range_self n
  obtain ⟨F, hF, hFb, hFs⟩ := h.exists_local_punctured_singularMetric_compactShift_decoder
    𝔇 h𝔇 hD hmetric hV hVU ψ hψ hψint p hpV hξ
  let i : ℂ × ℂ → ℕ := fun q => if hq : q ∈ S then Classical.choose (hp ▸ hq) else 0
  have hi : ∀ q ∈ S, p (i q) = q := by
    intro q hq
    simp only [i, dite_eq_left hq]
    exact Classical.choose_spec (hp ▸ hq)
  refine ⟨fun v q => F v (i q), ?_, ?_, ?_⟩
  · exact measurable_pi_iff.mpr (fun q => (measurable_pi_apply (i q)).comp hF)
  · filter_upwards [hFb] with ω hb q hq
    simpa only [hi q hq] using hb (i q)
  · intro g hg
    filter_upwards [hFs g hg] with ω hs q hq
    simpa only [hi q hq] using hs (i q)


/-- Countably many local full internal distances have a common decoder,
provided the punctured coordinate set contains the required circle and
endpoint pairs. -/
theorem IsWholePlaneGFF.exists_local_singularMetric_compactShift_decoder_of_coordinates
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {D : Ω → ℂ → ℂ → ℝ} (h : IsWholePlaneGFF P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hD : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
      ENNReal.ofReal (D ω u v) =
        weylScaling (𝔇 (hC ω)) ξ (fun z => -α * Real.log ‖z‖) u v)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    {U V : Set ℂ} (hV : IsOpen V) (hconn : IsConnected V) (h0 : (0 : ℂ) ∈ V)
    (hVU : V ⊆ U) (ψ : ℂ → ℝ) (hψ : IsTestFunction U ψ)
    (hψint : ∫ z, ψ z = 1) (p : ℕ → ℂ × ℂ)
    (hp : ∀ n, (p n).1 ∈ V ∧ (p n).2 ∈ V)
    {ε : ℝ} (hball : ball (0 : ℂ) ε ⊆ V)
    (s : ℕ → ℝ) (hs : Tendsto s atTop (𝓝 0)) (hpos : ∀ n, 0 < s n)
    (hsε : ∀ n, s n < ε) (C : ℕ → Set ℂ)
    (hcircle : ∀ n, C n ⊆ sphere (0 : ℂ) (s n) ∧ (C n).Countable ∧
      sphere (0 : ℂ) (s n) ⊆ closure (C n))
    (S : Set (ℂ × ℂ)) (hS : S.Countable) (hSne : S.Nonempty)
    (hSV : ∀ q ∈ S, q.1 ∈ V ∧ q.1 ≠ 0)
    (hSx : ∀ n k z, z ∈ C k → (p n).1 ≠ 0 → (z, (p n).1) ∈ S)
    (hSy : ∀ n k z, z ∈ C k → (p n).2 ≠ 0 → (z, (p n).2) ∈ S)
    (hSp : ∀ n, (p n).1 ≠ 0 → (p n).2 ≠ 0 → p n ∈ S)
    (hξ : 0 ≤ ξ) :
    ∃ F : (LocalZeroMeanTest U → ℝ) → ℕ → ℝ≥0∞, Measurable F ∧
      (∀ᵐ ω ∂P, ∀ n, F (localModConstPairings α hC U ω) n =
        ENNReal.ofReal (Real.exp (ξ * (-hC ω ψ))) *
          internalMetric (D ω) V (p n).1 (p n).2) ∧
      ∀ g : ℂ → ℝ, IsTestFunction univ g →
        ∀ᵐ ω ∂P, ∀ n, F (localModConstPairings α
          (fun ω => addFunPairing (hC ω) g) U ω) n =
          ENNReal.ofReal (Real.exp (ξ * (-(hC ω ψ + ∫ z, g z * ψ z)))) *
            internalMetric (fun x y => (weylScaling (D ω) ξ g x y).toReal)
              V (p n).1 (p n).2 := by
  obtain ⟨G, hG, hGb, hGs⟩ := h.exists_local_punctured_singularMetric_compactShift_decoder_countable
    𝔇 h𝔇 hD hmetric hV hVU ψ hψ hψint S hS hSne hSV hξ
  let F := fun v n => puncturedDistanceFrom C (fun x y => G v (x, y)) (p n).1 (p n).2
  have hF : Measurable F := by
    apply measurable_pi_iff.mpr
    intro n
    exact measurable_puncturedDistanceFrom C (fun k => (hcircle k).2.1)
      (fun v x y => G v (x, y))
      (fun x y => (measurable_pi_apply (x, y)).comp hG) _ _
  have hdecode : ∀ (E : ℂ → ℂ → ℝ) (c : ℝ≥0∞) (v : LocalZeroMeanTest U → ℝ),
      IsEuclideanLengthMetric E → c ≠ 0 → c ≠ ∞ →
      (∀ q ∈ S, G v q = c * internalMetric E (V \ {0}) q.1 q.2) →
      ∀ n, F v n = c * internalMetric E V (p n).1 (p n).2 := by
    intro E c v he hc0 hct heq n
    apply he.puncturedDistanceFrom_eq hV hconn h0 hball (hp n).1 (hp n).2
      s hs hpos hsε C hcircle hc0 hct
    · intro hx k z hz
      exact heq (z, (p n).1) (hSx n k z hz hx)
    · intro hy k z hz
      exact heq (z, (p n).2) (hSy n k z hz hy)
    · intro hx hy
      exact heq (p n) (hSp n hx hy)
  refine ⟨F, hF, ?_, ?_⟩
  · filter_upwards [hmetric, hGb] with ω hm hb
    apply hdecode (D ω) _ _ hm
    · exact ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)
    · exact ENNReal.ofReal_ne_top
    · exact hb
  · intro g hg
    filter_upwards [hmetric, hGs g hg] with ω hm hs'
    apply hdecode _ _ _ (hm.weylScaling_compact_isLengthMetric hξ g hg.1.continuous hg.2.1)
    · exact ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)
    · exact ENNReal.ofReal_ne_top
    · exact hs'


/-- Countable circles and endpoints have a countable family of punctured
coordinate pairs containing all pairs used in full-distance reconstruction. -/
theorem exists_punctured_coordinate_set
    {V : Set ℂ} {ε : ℝ} (hball : ball (0 : ℂ) ε ⊆ V)
    (s : ℕ → ℝ) (hpos : ∀ n, 0 < s n) (hsε : ∀ n, s n < ε)
    (C : ℕ → Set ℂ) (hC : ∀ n, C n ⊆ sphere (0 : ℂ) (s n) ∧ (C n).Countable)
    (p : ℕ → ℂ × ℂ) (a : ℂ) (haV : a ∈ V) (ha0 : a ≠ 0) :
    ∃ S : Set (ℂ × ℂ), S.Countable ∧ S.Nonempty ∧
      (∀ q ∈ S, q.1 ∈ V ∧ q.1 ≠ 0) ∧
      (∀ n k z, z ∈ C k → (p n).1 ≠ 0 → (z, (p n).1) ∈ S) ∧
      (∀ n k z, z ∈ C k → (p n).2 ≠ 0 → (z, (p n).2) ∈ S) ∧
      (∀ n, (p n).1 ∈ V → (p n).1 ≠ 0 → (p n).2 ≠ 0 → p n ∈ S) := by
  let T : Set ℂ := {a} ∪ (⋃ n, C n) ∪ range (fun n => (p n).1) ∪ range (fun n => (p n).2)
  have hT : T.Countable := by
    exact (((countable_singleton a).union (countable_iUnion fun n => (hC n).2)).union
      (countable_range _)).union (countable_range _)
  let S := ((V \ {0}) ∩ T) ×ˢ T
  have haT : a ∈ T := Or.inl (Or.inl (Or.inl (mem_singleton a)))
  have hSa : (a, a) ∈ S := ⟨⟨⟨haV, by simpa using ha0⟩, haT⟩, haT⟩
  have hcirc : ∀ k z, z ∈ C k → z ∈ V ∧ z ≠ 0 ∧ z ∈ T := by
    intro k z hz
    have hzs := (hC k).1 hz
    have hzV : z ∈ V := hball (sphere_subset_ball (hsε k) hzs)
    have hzn : ‖z‖ = s k := by simpa only [mem_sphere_zero_iff_norm] using hzs
    have hz0 : z ≠ 0 := by
      intro he
      subst z
      simp only [norm_zero] at hzn
      linarith [hpos k]
    refine ⟨hzV, hz0, ?_⟩
    exact Or.inl (Or.inl (Or.inr (mem_iUnion.mpr ⟨k, hz⟩)))
  have hxT : ∀ n, (p n).1 ∈ T := fun n => Or.inl (Or.inr ⟨n, rfl⟩)
  have hyT : ∀ n, (p n).2 ∈ T := fun n => Or.inr ⟨n, rfl⟩
  refine ⟨S, (hT.mono inter_subset_right).prod hT, ⟨(a, a), hSa⟩, ?_, ?_, ?_, ?_⟩
  · intro q hq
    exact ⟨hq.1.1.1, hq.1.1.2⟩
  · intro n k z hz _
    have hz' := hcirc k z hz
    exact ⟨⟨⟨hz'.1, hz'.2.1⟩, hz'.2.2⟩, hxT n⟩
  · intro n k z hz _
    have hz' := hcirc k z hz
    exact ⟨⟨⟨hz'.1, hz'.2.1⟩, hz'.2.2⟩, hyT n⟩
  · intro n hn hn0 _
    exact ⟨⟨⟨hn, hn0⟩, hxT n⟩, hyT n⟩

/-- The normalized full internal distances at countably many endpoints have
a local decoder under each smooth compact shift. -/
theorem IsWholePlaneGFF.exists_local_singularMetric_compactShift_decoder
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {D : Ω → ℂ → ℂ → ℝ} (h : IsWholePlaneGFF P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hD : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
      ENNReal.ofReal (D ω u v) =
        weylScaling (𝔇 (hC ω)) ξ (fun z => -α * Real.log ‖z‖) u v)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    {U V : Set ℂ} (hV : IsOpen V) (hconn : IsConnected V) (h0 : (0 : ℂ) ∈ V)
    (hVU : V ⊆ U) (ψ : ℂ → ℝ) (hψ : IsTestFunction U ψ)
    (hψint : ∫ z, ψ z = 1) (p : ℕ → ℂ × ℂ)
    (hp : ∀ n, (p n).1 ∈ V ∧ (p n).2 ∈ V)
    {ε : ℝ} (hball : ball (0 : ℂ) ε ⊆ V)
    (s : ℕ → ℝ) (hs : Tendsto s atTop (𝓝 0)) (hpos : ∀ n, 0 < s n)
    (hsε : ∀ n, s n < ε) (C : ℕ → Set ℂ)
    (hcircle : ∀ n, C n ⊆ sphere (0 : ℂ) (s n) ∧ (C n).Countable ∧
      sphere (0 : ℂ) (s n) ⊆ closure (C n))
    (hξ : 0 ≤ ξ) :
    ∃ F : (LocalZeroMeanTest U → ℝ) → ℕ → ℝ≥0∞, Measurable F ∧
      (∀ᵐ ω ∂P, ∀ n, F (localModConstPairings α hC U ω) n =
        ENNReal.ofReal (Real.exp (ξ * (-hC ω ψ))) *
          internalMetric (D ω) V (p n).1 (p n).2) ∧
      ∀ g : ℂ → ℝ, IsTestFunction univ g →
        ∀ᵐ ω ∂P, ∀ n, F (localModConstPairings α
          (fun ω => addFunPairing (hC ω) g) U ω) n =
          ENNReal.ofReal (Real.exp (ξ * (-(hC ω ψ + ∫ z, g z * ψ z)))) *
            internalMetric (fun x y => (weylScaling (D ω) ξ g x y).toReal)
              V (p n).1 (p n).2 := by
  have haV : ((s 0 : ℝ) : ℂ) ∈ V := by
    apply hball
    apply sphere_subset_ball (hsε 0)
    rw [mem_sphere_zero_iff_norm, Complex.norm_real, Real.norm_of_nonneg (hpos 0).le]
  have ha0 : ((s 0 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (hpos 0))
  obtain ⟨S, hS, hSne, hSV, hSx, hSy, hSp⟩ :=
    exists_punctured_coordinate_set hball s hpos hsε C (fun n => ⟨(hcircle n).1, (hcircle n).2.1⟩)
      p ((s 0 : ℝ) : ℂ) haV ha0
  exact h.exists_local_singularMetric_compactShift_decoder_of_coordinates
    𝔇 h𝔇 hD hmetric hV hconn h0 hVU ψ hψ hψint p hp hball s hs hpos hsε C hcircle
    S hS hSne hSV hSx hSy (fun n hx hy => hSp n (hp n).1 hx hy) hξ

/-- The local centered field, normalized measure and full internal distances
on a connected domain containing the origin have equivalent joint laws under
smooth compact shifts. -/
theorem IsWholePlaneGFF.exists_local_joint_smooth_shift_law_of_circles
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α ε : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} {D : Ω → ℂ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hfull : ∀ᵐ ω ∂P, ∀ W : Set ℂ, IsOpen W → W.Nonempty → 0 < μ ω W)
    (hε : 0 < ε) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ)
    (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hD : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
      ENNReal.ofReal (D ω u v) =
        weylScaling (𝔇 (hC ω)) ξ (fun z => -α * Real.log ‖z‖) u v)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    {V : Set ℂ} (hV : IsOpen V) (hVU : V ⊆ ball 0 ε)
    (ψ : ℂ → ℝ) (hψ : IsTestFunction (ball 0 ε) ψ) (hψint : ∫ z, ψ z = 1)
    (p : ℕ → ℂ × ℂ) (hp : ∀ n, (p n).1 ∈ V ∧ (p n).2 ∈ V)
    (hconn : IsConnected V) (h0 : (0 : ℂ) ∈ V)
    {δ : ℝ} (hball : ball (0 : ℂ) δ ⊆ V)
    (s : ℕ → ℝ) (hs : Tendsto s atTop (𝓝 0)) (hpos : ∀ n, 0 < s n)
    (hsδ : ∀ n, s n < δ) (C : ℕ → Set ℂ)
    (hcircle : ∀ n, C n ⊆ sphere (0 : ℂ) (s n) ∧ (C n).Countable ∧
      sphere (0 : ℂ) (s n) ⊆ closure (C n)) (hξ : 0 ≤ ξ) :
    ∃ R ∈ Ioo (0 : ℝ) ε,
      ∀ g : ℂ → ℝ, IsTestFunction univ g →
        P.map (fun ω =>
          (localModConstPairings α (fun ω => addFunPairing (hC ω) g) (ball 0 ε) ω,
           normalizedRestriction ((μ ω).withDensity
             (fun z => ENNReal.ofReal (Real.exp (γ * g z)))) (ball 0 R),
           fun n => ENNReal.ofReal (Real.exp (ξ * (-(hC ω ψ + ∫ z, g z * ψ z)))) *
             internalMetric (fun x y => (weylScaling (D ω) ξ g x y).toReal)
               V (p n).1 (p n).2)) ≪
        P.map (fun ω =>
          (localModConstPairings α hC (ball 0 ε) ω,
           normalizedRestriction (μ ω) (ball 0 R),
           fun n => ENNReal.ofReal (Real.exp (ξ * (-hC ω ψ))) *
             internalMetric (D ω) V (p n).1 (p n).2)) ∧
        P.map (fun ω =>
          (localModConstPairings α hC (ball 0 ε) ω,
           normalizedRestriction (μ ω) (ball 0 R),
           fun n => ENNReal.ofReal (Real.exp (ξ * (-hC ω ψ))) *
             internalMetric (D ω) V (p n).1 (p n).2)) ≪
        P.map (fun ω =>
          (localModConstPairings α (fun ω => addFunPairing (hC ω) g) (ball 0 ε) ω,
           normalizedRestriction ((μ ω).withDensity
             (fun z => ENNReal.ofReal (Real.exp (γ * g z)))) (ball 0 R),
           fun n => ENNReal.ofReal (Real.exp (ξ * (-(hC ω ψ + ∫ z, g z * ψ z)))) *
             internalMetric (fun x y => (weylScaling (D ω) ξ g x y).toReal)
               V (p n).1 (p n).2)) := by
  obtain ⟨N, hN, hNb, hNs⟩ := h.exists_local_singularMetric_compactShift_decoder
    𝔇 h𝔇 hD hmetric hV hconn h0 hVU ψ hψ hψint p hp hball s hs hpos hsδ C hcircle hξ
  obtain ⟨R, hR, M, hM, _, hMeq⟩ := h.exists_shifted_normalized_measure_decoder hμ hfull hε
  let F := fun v => (v, M v, N v)
  have hF : Measurable F := measurable_id.prodMk (hM.prodMk hN)
  have hzero : (fun ω => addFunPairing (hC ω) (fun _ => 0)) = hC := by
    funext ω φ
    simp [addFunPairing]
  have hzeroTest : IsTestFunction univ (fun _ : ℂ => (0 : ℝ)) :=
    ⟨contDiff_const, HasCompactSupport.zero, by simp⟩
  have hbase := hMeq (fun _ => 0) hzeroTest
  simp only [hzero, mul_zero, Real.exp_zero, ENNReal.ofReal_one] at hbase
  have hwone (ω : Ω) : (μ ω).withDensity (fun _ => 1) = μ ω := withDensity_one
  simp only [hwone] at hbase
  refine ⟨R, hR, ?_⟩
  intro g hg
  let X := localModConstPairings α hC (ball 0 ε)
  let Y := localModConstPairings α (fun ω => addFunPairing (hC ω) g) (ball 0 ε)
  have hX : Measurable X := by
    apply measurable_pi_iff.mpr
    intro φ
    change Measurable (fun ω => hC ω φ.1 - α * ∫ z, φ.1 z * Real.log ‖z‖)
    exact (h.measurable_pairing φ.1 (φ.2.1.mono_set (subset_univ _))).sub_const _
  have hY : Measurable Y := by
    apply measurable_pi_iff.mpr
    intro φ
    change Measurable (fun ω => (hC ω φ.1 + ∫ z, g z * φ.1 z) -
      α * ∫ z, φ.1 z * Real.log ‖z‖)
    exact ((h.measurable_pairing φ.1 (φ.2.1.mono_set (subset_univ _))).add_const _).sub_const _
  have hac := h.singular_smooth_shift_modConst_pairing_laws hg α (ball 0 ε)
  change P.map Y ≪ P.map X ∧ P.map X ≪ P.map Y at hac
  have hf := hac.1.map hF
  have hb := hac.2.map hF
  rw [Measure.map_map hF hY, Measure.map_map hF hX] at hf
  rw [Measure.map_map hF hX, Measure.map_map hF hY] at hb
  have hbaseMap : P.map (F ∘ X) = P.map (fun ω =>
      (X ω, normalizedRestriction (μ ω) (ball 0 R), fun n =>
        ENNReal.ofReal (Real.exp (ξ * (-hC ω ψ))) *
          internalMetric (D ω) V (p n).1 (p n).2)) := by
    apply Measure.map_congr
    filter_upwards [hbase, hNb] with ω hm hn
    exact Prod.ext rfl (Prod.ext hm (funext hn))
  have hshiftMap : P.map (F ∘ Y) = P.map (fun ω =>
      (Y ω, normalizedRestriction ((μ ω).withDensity
        (fun z => ENNReal.ofReal (Real.exp (γ * g z)))) (ball 0 R), fun n =>
          ENNReal.ofReal (Real.exp (ξ * (-(hC ω ψ + ∫ z, g z * ψ z)))) *
            internalMetric (fun x y => (weylScaling (D ω) ξ g x y).toReal)
              V (p n).1 (p n).2)) := by
    apply Measure.map_congr
    filter_upwards [hMeq g hg, hNs g hg] with ω hm hn
    exact Prod.ext rfl (Prod.ext hm (funext hn))
  rw [hbaseMap, hshiftMap] at hf hb
  exact ⟨hf, hb⟩

/-- On a connected open domain containing the origin, the local centered
field, normalized measure and countably many normalized full internal distances
have equivalent joint laws under each smooth compact shift. -/
theorem IsWholePlaneGFF.exists_local_joint_smooth_shift_law_on_connected
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α ε : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} {D : Ω → ℂ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hfull : ∀ᵐ ω ∂P, ∀ W : Set ℂ, IsOpen W → W.Nonempty → 0 < μ ω W)
    (hε : 0 < ε) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ)
    (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hD : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
      ENNReal.ofReal (D ω u v) =
        weylScaling (𝔇 (hC ω)) ξ (fun z => -α * Real.log ‖z‖) u v)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    {V : Set ℂ} (hV : IsOpen V) (hVU : V ⊆ ball 0 ε)
    (ψ : ℂ → ℝ) (hψ : IsTestFunction (ball 0 ε) ψ) (hψint : ∫ z, ψ z = 1)
    (p : ℕ → ℂ × ℂ) (hp : ∀ n, (p n).1 ∈ V ∧ (p n).2 ∈ V)
    (hconn : IsConnected V) (h0 : (0 : ℂ) ∈ V)
    (hξ : 0 ≤ ξ) :
    ∃ R ∈ Ioo (0 : ℝ) ε,
      ∀ g : ℂ → ℝ, IsTestFunction univ g →
        P.map (fun ω =>
          (localModConstPairings α (fun ω => addFunPairing (hC ω) g) (ball 0 ε) ω,
           normalizedRestriction ((μ ω).withDensity
             (fun z => ENNReal.ofReal (Real.exp (γ * g z)))) (ball 0 R),
           fun n => ENNReal.ofReal (Real.exp (ξ * (-(hC ω ψ + ∫ z, g z * ψ z)))) *
             internalMetric (fun x y => (weylScaling (D ω) ξ g x y).toReal)
               V (p n).1 (p n).2)) ≪
        P.map (fun ω =>
          (localModConstPairings α hC (ball 0 ε) ω,
           normalizedRestriction (μ ω) (ball 0 R),
           fun n => ENNReal.ofReal (Real.exp (ξ * (-hC ω ψ))) *
             internalMetric (D ω) V (p n).1 (p n).2)) ∧
        P.map (fun ω =>
          (localModConstPairings α hC (ball 0 ε) ω,
           normalizedRestriction (μ ω) (ball 0 R),
           fun n => ENNReal.ofReal (Real.exp (ξ * (-hC ω ψ))) *
             internalMetric (D ω) V (p n).1 (p n).2)) ≪
        P.map (fun ω =>
          (localModConstPairings α (fun ω => addFunPairing (hC ω) g) (ball 0 ε) ω,
           normalizedRestriction ((μ ω).withDensity
             (fun z => ENNReal.ofReal (Real.exp (γ * g z)))) (ball 0 R),
           fun n => ENNReal.ofReal (Real.exp (ξ * (-(hC ω ψ + ∫ z, g z * ψ z)))) *
             internalMetric (fun x y => (weylScaling (D ω) ξ g x y).toReal)
               V (p n).1 (p n).2)) := by
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hV 0 h0
  have hs : Tendsto (fun n : ℕ => δ / ((n : ℝ) + 2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
  exact h.exists_local_joint_smooth_shift_law_of_circles hμ hfull hε 𝔇 h𝔇 hD hmetric
    hV hVU ψ hψ hψint p hp hconn h0 hball (fun n => δ / ((n : ℝ) + 2)) hs
    (fun n => by positivity)
    (fun n => div_lt_self hδ (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]))
    (S11m.decCircle δ) (fun n => S11m.decCircle_spec δ n) hξ

/-- The connected-domain joint law for subcritical inserted LQG. -/
theorem IsWholePlaneGFF.exists_local_joint_smooth_shift_law_on_connected_of_subcritical
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α ε : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} {D : Ω → ℂ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    (hε : 0 < ε) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ)
    (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hD : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
      ENNReal.ofReal (D ω u v) =
        weylScaling (𝔇 (hC ω)) ξ (fun z => -α * Real.log ‖z‖) u v)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    {V : Set ℂ} (hV : IsOpen V) (hVU : V ⊆ ball 0 ε)
    (ψ : ℂ → ℝ) (hψ : IsTestFunction (ball 0 ε) ψ) (hψint : ∫ z, ψ z = 1)
    (p : ℕ → ℂ × ℂ) (hp : ∀ n, (p n).1 ∈ V ∧ (p n).2 ∈ V)
    (hconn : IsConnected V) (h0 : (0 : ℂ) ∈ V)
    (hξ : 0 ≤ ξ) :
    ∃ R ∈ Ioo (0 : ℝ) ε,
      ∀ g : ℂ → ℝ, IsTestFunction univ g →
        P.map (fun ω =>
          (localModConstPairings α (fun ω => addFunPairing (hC ω) g) (ball 0 ε) ω,
           normalizedRestriction ((μ ω).withDensity
             (fun z => ENNReal.ofReal (Real.exp (γ * g z)))) (ball 0 R),
           fun n => ENNReal.ofReal (Real.exp (ξ * (-(hC ω ψ + ∫ z, g z * ψ z)))) *
             internalMetric (fun x y => (weylScaling (D ω) ξ g x y).toReal)
               V (p n).1 (p n).2)) ≪
        P.map (fun ω =>
          (localModConstPairings α hC (ball 0 ε) ω,
           normalizedRestriction (μ ω) (ball 0 R),
           fun n => ENNReal.ofReal (Real.exp (ξ * (-hC ω ψ))) *
             internalMetric (D ω) V (p n).1 (p n).2)) ∧
        P.map (fun ω =>
          (localModConstPairings α hC (ball 0 ε) ω,
           normalizedRestriction (μ ω) (ball 0 R),
           fun n => ENNReal.ofReal (Real.exp (ξ * (-hC ω ψ))) *
             internalMetric (D ω) V (p n).1 (p n).2)) ≪
        P.map (fun ω =>
          (localModConstPairings α (fun ω => addFunPairing (hC ω) g) (ball 0 ε) ω,
           normalizedRestriction ((μ ω).withDensity
             (fun z => ENNReal.ofReal (Real.exp (γ * g z)))) (ball 0 R),
           fun n => ENNReal.ofReal (Real.exp (ξ * (-(hC ω ψ + ∫ z, g z * ψ z)))) *
             internalMetric (fun x y => (weylScaling (D ω) ξ g x y).toReal)
               V (p n).1 (p n).2)) := by
  exact h.exists_local_joint_smooth_shift_law_on_connected hμ
    (lqgMeasureFullSupportStmt_holds γ α hγ hγ2 hα Ω P hC hcirc μ h hμ)
    hε 𝔇 h𝔇 hD hmetric hV hVU ψ hψ hψint p hp hconn h0 hξ

/-- The connected-domain joint shift law for an inserted metric of the
same field and its associated measure. -/
theorem IsWholePlaneGFF.exists_local_joint_smooth_shift_law_on_connected_of_field
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α ε : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} {D : Ω → ℂ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    (hε : 0 < ε) (hDfield : IsLQGMetricOfField P γ ξ α hC D)
    (haxioms : LQGMetricFieldAxioms P γ ξ α hC hcirc)
    {V : Set ℂ} (hV : IsOpen V) (hVU : V ⊆ ball 0 ε)
    (ψ : ℂ → ℝ) (hψ : IsTestFunction (ball 0 ε) ψ) (hψint : ∫ z, ψ z = 1)
    (p : ℕ → ℂ × ℂ) (hp : ∀ n, (p n).1 ∈ V ∧ (p n).2 ∈ V)
    (hconn : IsConnected V) (h0 : (0 : ℂ) ∈ V)
    (hξ : 0 ≤ ξ) :
    ∃ R ∈ Ioo (0 : ℝ) ε,
      ∀ g : ℂ → ℝ, IsTestFunction univ g →
        P.map (fun ω =>
          (localModConstPairings α (fun ω => addFunPairing (hC ω) g) (ball 0 ε) ω,
           normalizedRestriction ((μ ω).withDensity
             (fun z => ENNReal.ofReal (Real.exp (γ * g z)))) (ball 0 R),
           fun n => ENNReal.ofReal (Real.exp (ξ * (-(hC ω ψ + ∫ z, g z * ψ z)))) *
             internalMetric (fun x y => (weylScaling (D ω) ξ g x y).toReal)
               V (p n).1 (p n).2)) ≪
        P.map (fun ω =>
          (localModConstPairings α hC (ball 0 ε) ω,
           normalizedRestriction (μ ω) (ball 0 R),
           fun n => ENNReal.ofReal (Real.exp (ξ * (-hC ω ψ))) *
             internalMetric (D ω) V (p n).1 (p n).2)) ∧
        P.map (fun ω =>
          (localModConstPairings α hC (ball 0 ε) ω,
           normalizedRestriction (μ ω) (ball 0 R),
           fun n => ENNReal.ofReal (Real.exp (ξ * (-hC ω ψ))) *
             internalMetric (D ω) V (p n).1 (p n).2)) ≪
        P.map (fun ω =>
          (localModConstPairings α (fun ω => addFunPairing (hC ω) g) (ball 0 ε) ω,
           normalizedRestriction ((μ ω).withDensity
             (fun z => ENNReal.ofReal (Real.exp (γ * g z)))) (ball 0 R),
           fun n => ENNReal.ofReal (Real.exp (ξ * (-(hC ω ψ + ∫ z, g z * ψ z)))) *
             internalMetric (fun x y => (weylScaling (D ω) ξ g x y).toReal)
               V (p n).1 (p n).2)) := by
  have hmetric := ae_isEuclideanLengthMetric_of_metricFieldAxioms P γ ξ α hC hcirc D
    haxioms h hγ hγ2 hα hDfield
  obtain ⟨𝔇, h𝔇, hD⟩ := hDfield
  exact h.exists_local_joint_smooth_shift_law_on_connected_of_subcritical hμ hγ hγ2 hα
    hε 𝔇 h𝔇 hD hmetric hV hVU ψ hψ hψint p hp hconn h0 hξ

/-- A countable family of open domains, connected whenever they contain the
origin, has a common decoder for normalized internal distances. -/
theorem IsWholePlaneGFF.exists_singularMetric_compactShift_decoder_on_connected_domains
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {D : Ω → ℂ → ℂ → ℝ} (h : IsWholePlaneGFF P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hD : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
      ENNReal.ofReal (D ω u v) =
        weylScaling (𝔇 (hC ω)) ξ (fun z => -α * Real.log ‖z‖) u v)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (V : ℕ → Set ℂ) (hV : ∀ n, IsOpen (V n))
    (hconn : ∀ n, (0 : ℂ) ∈ V n → IsConnected (V n))
    (ψ : ℂ → ℝ) (hψ : IsTestFunction univ ψ) (hψint : ∫ z, ψ z = 1)
    (p : ℕ → ℂ × ℂ) (hp : ∀ n, (p n).1 ∈ V n ∧ (p n).2 ∈ V n)
    (hξ : 0 ≤ ξ) :
    ∃ F : (LocalZeroMeanTest univ → ℝ) → ℕ → ℝ≥0∞, Measurable F ∧
      (∀ᵐ ω ∂P, ∀ n, F (localModConstPairings α hC univ ω) n =
        ENNReal.ofReal (Real.exp (ξ * (-hC ω ψ))) *
          internalMetric (D ω) (V n) (p n).1 (p n).2) ∧
      ∀ g : ℂ → ℝ, IsTestFunction univ g →
        ∀ᵐ ω ∂P, ∀ n, F (localModConstPairings α
          (fun ω => addFunPairing (hC ω) g) univ ω) n =
          ENNReal.ofReal (Real.exp (ξ * (-(hC ω ψ + ∫ z, g z * ψ z)))) *
            internalMetric (fun x y => (weylScaling (D ω) ξ g x y).toReal)
              (V n) (p n).1 (p n).2 := by
  have hex (n : ℕ) :
      ∃ G : (LocalZeroMeanTest univ → ℝ) → ℕ → ℝ≥0∞, Measurable G ∧
        (∀ᵐ ω ∂P, ∀ k, G (localModConstPairings α hC univ ω) k =
          ENNReal.ofReal (Real.exp (ξ * (-hC ω ψ))) *
            internalMetric (D ω) (V n) (p n).1 (p n).2) ∧
        ∀ g : ℂ → ℝ, IsTestFunction univ g →
          ∀ᵐ ω ∂P, ∀ k, G (localModConstPairings α
            (fun ω => addFunPairing (hC ω) g) univ ω) k =
            ENNReal.ofReal (Real.exp (ξ * (-(hC ω ψ + ∫ z, g z * ψ z)))) *
              internalMetric (fun x y => (weylScaling (D ω) ξ g x y).toReal)
                (V n) (p n).1 (p n).2 := by
    by_cases hzero : (0 : ℂ) ∈ V n
    · obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp (hV n) 0 hzero
      have hs : Tendsto (fun k : ℕ => δ / ((k : ℝ) + 2)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
      exact h.exists_local_singularMetric_compactShift_decoder 𝔇 h𝔇 hD hmetric
        (hV n) (hconn n hzero) hzero (subset_univ _) ψ hψ hψint (fun _ => p n)
        (fun _ => hp n) hball (fun k => δ / ((k : ℝ) + 2)) hs
        (fun k => by positivity)
        (fun k => div_lt_self hδ (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]))
        (S11m.decCircle δ) (fun k => S11m.decCircle_spec δ k) hξ
    · have hp0 : (p n).1 ≠ 0 := by
        intro heq
        exact hzero (heq ▸ (hp n).1)
      have hdiff : V n \ {0} = V n := sdiff_singleton_eq_self hzero
      simpa only [hdiff] using
        h.exists_local_punctured_singularMetric_compactShift_decoder 𝔇 h𝔇 hD hmetric
          (hV n) (subset_univ _) ψ hψ hψint (fun _ => p n)
          (fun _ => ⟨(hp n).1, hp0⟩) hξ
  choose G hG hGb hGs using hex
  let F := fun v n => G n v 0
  refine ⟨F, ?_, ?_, ?_⟩
  · exact measurable_pi_iff.mpr fun n => (measurable_pi_apply 0).comp (hG n)
  · filter_upwards [ae_all_iff.mpr hGb] with ω hb n
    exact hb n 0
  · intro g hg
    filter_upwards [ae_all_iff.mpr (fun n => hGs n g hg)] with ω hs n
    exact hs n 0

/-- A common measurable decoder recovers the actual joint observations of the
field and each of its fixed smooth shifts. -/
theorem IsWholePlaneGFF.exists_joint_smooth_shift_decoder_on_domains_between
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α a ε : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} {D : Ω → ℂ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hfull : ∀ᵐ ω ∂P, ∀ W : Set ℂ, IsOpen W → W.Nonempty → 0 < μ ω W)
    (ha : 0 ≤ a) (haε : a < ε) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ)
    (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hD : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
      ENNReal.ofReal (D ω u v) =
        weylScaling (𝔇 (hC ω)) ξ (fun z => -α * Real.log ‖z‖) u v)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (V : ℕ → Set ℂ) (hV : ∀ n, IsOpen (V n))
    (hconn : ∀ n, (0 : ℂ) ∈ V n → IsConnected (V n))
    (ψ : ℂ → ℝ) (hψ : IsTestFunction univ ψ) (hψint : ∫ z, ψ z = 1)
    (p : ℕ → ℂ × ℂ) (hp : ∀ n, (p n).1 ∈ V n ∧ (p n).2 ∈ V n)
    (hξ : 0 ≤ ξ) :
    ∃ R ∈ Ioo a ε, ∃ F : (LocalZeroMeanTest univ → ℝ) →
      (LocalZeroMeanTest (ball 0 ε) → ℝ) × (Measure ℂ × (ℕ → ℝ≥0∞)),
      Measurable F ∧
      (∀ᵐ ω ∂P, F (localModConstPairings α hC univ ω) =
        (localModConstPairings α hC (ball 0 ε) ω,
         normalizedRestriction (μ ω) (ball 0 R), fun n =>
           ENNReal.ofReal (Real.exp (ξ * (-hC ω ψ))) *
             internalMetric (D ω) (V n) (p n).1 (p n).2)) ∧
      ∀ g : ℂ → ℝ, IsTestFunction univ g →
        ∀ᵐ ω ∂P, F (localModConstPairings α
          (fun ω => addFunPairing (hC ω) g) univ ω) =
        (localModConstPairings α (fun ω => addFunPairing (hC ω) g) (ball 0 ε) ω,
         normalizedRestriction ((μ ω).withDensity
           (fun z => ENNReal.ofReal (Real.exp (γ * g z)))) (ball 0 R),
         fun n => ENNReal.ofReal (Real.exp (ξ * (-(hC ω ψ + ∫ z, g z * ψ z)))) *
           internalMetric (fun x y => (weylScaling (D ω) ξ g x y).toReal)
             (V n) (p n).1 (p n).2) := by
  obtain ⟨G, hG, hGb, hGs⟩ := h.exists_singularMetric_compactShift_decoder_on_connected_domains
    𝔇 h𝔇 hD hmetric V hV hconn ψ hψ hψint p hp hξ
  obtain ⟨R, hR, M, hM, _, hMeq⟩ :=
    h.exists_shifted_normalized_measure_decoder_between hμ hfull ha haε
  let Q : (LocalZeroMeanTest univ → ℝ) → LocalZeroMeanTest (ball 0 ε) → ℝ :=
    fun v φ => v ⟨φ.1, φ.2.1.mono_set (subset_univ _), φ.2.2⟩
  have hQ : Measurable Q := by
    apply measurable_pi_iff.mpr
    intro φ
    exact measurable_pi_apply (⟨φ.1, φ.2.1.mono_set (subset_univ _), φ.2.2⟩ :
      LocalZeroMeanTest univ)
  have hQeq (T : (ℂ → ℝ) → ℝ) :
      Q (localModConstPairings α id univ T) = localModConstPairings α id (ball 0 ε) T := by
    funext φ
    rfl
  let F := fun v => (Q v, M (Q v), G v)
  have hF : Measurable F := hQ.prodMk ((hM.comp hQ).prodMk hG)
  have hzero : (fun ω => addFunPairing (hC ω) (fun _ => 0)) = hC := by
    funext ω φ
    simp [addFunPairing]
  have hzeroTest : IsTestFunction univ (fun _ : ℂ => (0 : ℝ)) :=
    ⟨contDiff_const, HasCompactSupport.zero, by simp⟩
  have hbase := hMeq (fun _ => 0) hzeroTest
  simp only [hzero, mul_zero, Real.exp_zero, ENNReal.ofReal_one] at hbase
  have hwone (ω : Ω) : (μ ω).withDensity (fun _ => 1) = μ ω := withDensity_one
  simp only [hwone] at hbase
  refine ⟨R, hR, F, hF, ?_, ?_⟩
  · filter_upwards [hbase, hGb] with ω hm hn
    change (Q (localModConstPairings α id univ (hC ω)),
      M (Q (localModConstPairings α id univ (hC ω))), _) = _
    rw [hQeq]
    exact Prod.ext rfl (Prod.ext hm (funext hn))
  · intro g hg
    filter_upwards [hMeq g hg, hGs g hg] with ω hm hn
    change (Q (localModConstPairings α id univ (addFunPairing (hC ω) g)),
      M (Q (localModConstPairings α id univ (addFunPairing (hC ω) g))), _) = _
    rw [hQeq]
    exact Prod.ext rfl (Prod.ext hm (funext hn))

/-- The local field, normalized measure and normalized internal distances on
countably many open domains have equivalent joint laws under smooth shifts.
The measure reference radius can be chosen above a prescribed lower bound. -/
theorem IsWholePlaneGFF.exists_joint_smooth_shift_law_on_domains_between
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α a ε : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} {D : Ω → ℂ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hfull : ∀ᵐ ω ∂P, ∀ W : Set ℂ, IsOpen W → W.Nonempty → 0 < μ ω W)
    (ha : 0 ≤ a) (haε : a < ε) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ)
    (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hD : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
      ENNReal.ofReal (D ω u v) =
        weylScaling (𝔇 (hC ω)) ξ (fun z => -α * Real.log ‖z‖) u v)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (V : ℕ → Set ℂ) (hV : ∀ n, IsOpen (V n))
    (hconn : ∀ n, (0 : ℂ) ∈ V n → IsConnected (V n))
    (ψ : ℂ → ℝ) (hψ : IsTestFunction univ ψ) (hψint : ∫ z, ψ z = 1)
    (p : ℕ → ℂ × ℂ) (hp : ∀ n, (p n).1 ∈ V n ∧ (p n).2 ∈ V n)
    (hξ : 0 ≤ ξ) :
    ∃ R ∈ Ioo a ε, ∀ g : ℂ → ℝ, IsTestFunction univ g →
      P.map (fun ω =>
        (localModConstPairings α (fun ω => addFunPairing (hC ω) g) (ball 0 ε) ω,
         normalizedRestriction ((μ ω).withDensity
           (fun z => ENNReal.ofReal (Real.exp (γ * g z)))) (ball 0 R),
         fun n => ENNReal.ofReal (Real.exp (ξ * (-(hC ω ψ + ∫ z, g z * ψ z)))) *
           internalMetric (fun x y => (weylScaling (D ω) ξ g x y).toReal)
             (V n) (p n).1 (p n).2)) ≪
      P.map (fun ω =>
        (localModConstPairings α hC (ball 0 ε) ω,
         normalizedRestriction (μ ω) (ball 0 R), fun n =>
           ENNReal.ofReal (Real.exp (ξ * (-hC ω ψ))) *
             internalMetric (D ω) (V n) (p n).1 (p n).2)) ∧
      P.map (fun ω =>
        (localModConstPairings α hC (ball 0 ε) ω,
         normalizedRestriction (μ ω) (ball 0 R), fun n =>
           ENNReal.ofReal (Real.exp (ξ * (-hC ω ψ))) *
             internalMetric (D ω) (V n) (p n).1 (p n).2)) ≪
      P.map (fun ω =>
        (localModConstPairings α (fun ω => addFunPairing (hC ω) g) (ball 0 ε) ω,
         normalizedRestriction ((μ ω).withDensity
           (fun z => ENNReal.ofReal (Real.exp (γ * g z)))) (ball 0 R),
         fun n => ENNReal.ofReal (Real.exp (ξ * (-(hC ω ψ + ∫ z, g z * ψ z)))) *
           internalMetric (fun x y => (weylScaling (D ω) ξ g x y).toReal)
             (V n) (p n).1 (p n).2)) := by
  obtain ⟨G, hG, hGb, hGs⟩ := h.exists_singularMetric_compactShift_decoder_on_connected_domains
    𝔇 h𝔇 hD hmetric V hV hconn ψ hψ hψint p hp hξ
  obtain ⟨R, hR, M, hM, _, hMeq⟩ := h.exists_shifted_normalized_measure_decoder_between hμ hfull ha haε
  let Q : (LocalZeroMeanTest univ → ℝ) → LocalZeroMeanTest (ball 0 ε) → ℝ :=
    fun v φ => v ⟨φ.1, φ.2.1.mono_set (subset_univ _), φ.2.2⟩
  have hQ : Measurable Q := by
    apply measurable_pi_iff.mpr
    intro φ
    exact measurable_pi_apply (⟨φ.1, φ.2.1.mono_set (subset_univ _), φ.2.2⟩ :
      LocalZeroMeanTest univ)
  have hQeq (T : (ℂ → ℝ) → ℝ) :
      Q (localModConstPairings α id univ T) = localModConstPairings α id (ball 0 ε) T := by
    funext φ
    rfl
  let F := fun v => (Q v, M (Q v), G v)
  have hF : Measurable F := hQ.prodMk ((hM.comp hQ).prodMk hG)
  have hzero : (fun ω => addFunPairing (hC ω) (fun _ => 0)) = hC := by
    funext ω φ
    simp [addFunPairing]
  have hzeroTest : IsTestFunction univ (fun _ : ℂ => (0 : ℝ)) :=
    ⟨contDiff_const, HasCompactSupport.zero, by simp⟩
  have hbase := hMeq (fun _ => 0) hzeroTest
  simp only [hzero, mul_zero, Real.exp_zero, ENNReal.ofReal_one] at hbase
  have hwone (ω : Ω) : (μ ω).withDensity (fun _ => 1) = μ ω := withDensity_one
  simp only [hwone] at hbase
  refine ⟨R, hR, ?_⟩
  intro g hg
  let X := localModConstPairings α hC univ
  let Y := localModConstPairings α (fun ω => addFunPairing (hC ω) g) univ
  have hX : Measurable X := by
    apply measurable_pi_iff.mpr
    intro φ
    change Measurable (fun ω => hC ω φ.1 - α * ∫ z, φ.1 z * Real.log ‖z‖)
    exact (h.measurable_pairing φ.1 φ.2.1).sub_const _
  have hY : Measurable Y := by
    apply measurable_pi_iff.mpr
    intro φ
    change Measurable (fun ω => (hC ω φ.1 + ∫ z, g z * φ.1 z) -
      α * ∫ z, φ.1 z * Real.log ‖z‖)
    exact ((h.measurable_pairing φ.1 φ.2.1).add_const _).sub_const _
  have hac := h.singular_smooth_shift_modConst_pairing_laws hg α univ
  change P.map Y ≪ P.map X ∧ P.map X ≪ P.map Y at hac
  have hf := hac.1.map hF
  have hb := hac.2.map hF
  rw [Measure.map_map hF hY, Measure.map_map hF hX] at hf
  rw [Measure.map_map hF hX, Measure.map_map hF hY] at hb
  have hbaseMap : P.map (F ∘ X) = P.map (fun ω =>
      (localModConstPairings α hC (ball 0 ε) ω,
       normalizedRestriction (μ ω) (ball 0 R), fun n =>
         ENNReal.ofReal (Real.exp (ξ * (-hC ω ψ))) *
           internalMetric (D ω) (V n) (p n).1 (p n).2)) := by
    apply Measure.map_congr
    filter_upwards [hbase, hGb] with ω hm hn
    change (Q (localModConstPairings α id univ (hC ω)),
      M (Q (localModConstPairings α id univ (hC ω))), _) = _
    rw [hQeq]
    exact Prod.ext rfl (Prod.ext hm (funext hn))
  have hshiftMap : P.map (F ∘ Y) = P.map (fun ω =>
      (localModConstPairings α (fun ω => addFunPairing (hC ω) g) (ball 0 ε) ω,
       normalizedRestriction ((μ ω).withDensity
         (fun z => ENNReal.ofReal (Real.exp (γ * g z)))) (ball 0 R), fun n =>
           ENNReal.ofReal (Real.exp (ξ * (-(hC ω ψ + ∫ z, g z * ψ z)))) *
             internalMetric (fun x y => (weylScaling (D ω) ξ g x y).toReal)
               (V n) (p n).1 (p n).2)) := by
    apply Measure.map_congr
    filter_upwards [hMeq g hg, hGs g hg] with ω hm hn
    change (Q (localModConstPairings α id univ (addFunPairing (hC ω) g)),
      M (Q (localModConstPairings α id univ (addFunPairing (hC ω) g))), _) = _
    rw [hQeq]
    exact Prod.ext rfl (Prod.ext hm (funext hn))
  rw [hbaseMap, hshiftMap] at hf hb
  exact ⟨hf, hb⟩

/-- The local field, normalized measure and normalized internal distances on
countably many open domains have equivalent joint laws under smooth shifts.
Both observations are almost everywhere measurable, and the reference radius
can be chosen above a prescribed lower bound. -/
theorem IsWholePlaneGFF.exists_joint_smooth_shift_law_and_aemeasurable_on_domains_between
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α a ε : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} {D : Ω → ℂ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hfull : ∀ᵐ ω ∂P, ∀ W : Set ℂ, IsOpen W → W.Nonempty → 0 < μ ω W)
    (ha : 0 ≤ a) (haε : a < ε) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ)
    (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hD : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
      ENNReal.ofReal (D ω u v) =
        weylScaling (𝔇 (hC ω)) ξ (fun z => -α * Real.log ‖z‖) u v)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (V : ℕ → Set ℂ) (hV : ∀ n, IsOpen (V n))
    (hconn : ∀ n, (0 : ℂ) ∈ V n → IsConnected (V n))
    (ψ : ℂ → ℝ) (hψ : IsTestFunction univ ψ) (hψint : ∫ z, ψ z = 1)
    (p : ℕ → ℂ × ℂ) (hp : ∀ n, (p n).1 ∈ V n ∧ (p n).2 ∈ V n)
    (hξ : 0 ≤ ξ) :
    ∃ R ∈ Ioo a ε, ∀ g : ℂ → ℝ, IsTestFunction univ g →
      P.map (fun ω =>
        (localModConstPairings α (fun ω => addFunPairing (hC ω) g) (ball 0 ε) ω,
         normalizedRestriction ((μ ω).withDensity
           (fun z => ENNReal.ofReal (Real.exp (γ * g z)))) (ball 0 R),
         fun n => ENNReal.ofReal (Real.exp (ξ * (-(hC ω ψ + ∫ z, g z * ψ z)))) *
           internalMetric (fun x y => (weylScaling (D ω) ξ g x y).toReal)
             (V n) (p n).1 (p n).2)) ≪
      P.map (fun ω =>
        (localModConstPairings α hC (ball 0 ε) ω,
         normalizedRestriction (μ ω) (ball 0 R), fun n =>
           ENNReal.ofReal (Real.exp (ξ * (-hC ω ψ))) *
             internalMetric (D ω) (V n) (p n).1 (p n).2)) ∧
      P.map (fun ω =>
        (localModConstPairings α hC (ball 0 ε) ω,
         normalizedRestriction (μ ω) (ball 0 R), fun n =>
           ENNReal.ofReal (Real.exp (ξ * (-hC ω ψ))) *
             internalMetric (D ω) (V n) (p n).1 (p n).2)) ≪
      P.map (fun ω =>
        (localModConstPairings α (fun ω => addFunPairing (hC ω) g) (ball 0 ε) ω,
         normalizedRestriction ((μ ω).withDensity
           (fun z => ENNReal.ofReal (Real.exp (γ * g z)))) (ball 0 R),
         fun n => ENNReal.ofReal (Real.exp (ξ * (-(hC ω ψ + ∫ z, g z * ψ z)))) *
           internalMetric (fun x y => (weylScaling (D ω) ξ g x y).toReal)
             (V n) (p n).1 (p n).2)) ∧
      AEMeasurable (fun ω =>
      (localModConstPairings α hC (ball 0 ε) ω,
       normalizedRestriction (μ ω) (ball 0 R), fun n =>
         ENNReal.ofReal (Real.exp (ξ * (-hC ω ψ))) *
           internalMetric (D ω) (V n) (p n).1 (p n).2)) P ∧
      AEMeasurable (fun ω =>
      (localModConstPairings α (fun ω => addFunPairing (hC ω) g) (ball 0 ε) ω,
       normalizedRestriction ((μ ω).withDensity
         (fun z => ENNReal.ofReal (Real.exp (γ * g z)))) (ball 0 R), fun n =>
           ENNReal.ofReal (Real.exp (ξ * (-(hC ω ψ + ∫ z, g z * ψ z)))) *
             internalMetric (fun x y => (weylScaling (D ω) ξ g x y).toReal)
               (V n) (p n).1 (p n).2)) P := by
  obtain ⟨G, hG, hGb, hGs⟩ := h.exists_singularMetric_compactShift_decoder_on_connected_domains
    𝔇 h𝔇 hD hmetric V hV hconn ψ hψ hψint p hp hξ
  obtain ⟨R, hR, M, hM, _, hMeq⟩ := h.exists_shifted_normalized_measure_decoder_between hμ hfull ha haε
  let Q : (LocalZeroMeanTest univ → ℝ) → LocalZeroMeanTest (ball 0 ε) → ℝ :=
    fun v φ => v ⟨φ.1, φ.2.1.mono_set (subset_univ _), φ.2.2⟩
  have hQ : Measurable Q := by
    apply measurable_pi_iff.mpr
    intro φ
    exact measurable_pi_apply (⟨φ.1, φ.2.1.mono_set (subset_univ _), φ.2.2⟩ :
      LocalZeroMeanTest univ)
  have hQeq (T : (ℂ → ℝ) → ℝ) :
      Q (localModConstPairings α id univ T) = localModConstPairings α id (ball 0 ε) T := by
    funext φ
    rfl
  let F := fun v => (Q v, M (Q v), G v)
  have hF : Measurable F := hQ.prodMk ((hM.comp hQ).prodMk hG)
  have hzero : (fun ω => addFunPairing (hC ω) (fun _ => 0)) = hC := by
    funext ω φ
    simp [addFunPairing]
  have hzeroTest : IsTestFunction univ (fun _ : ℂ => (0 : ℝ)) :=
    ⟨contDiff_const, HasCompactSupport.zero, by simp⟩
  have hbase := hMeq (fun _ => 0) hzeroTest
  simp only [hzero, mul_zero, Real.exp_zero, ENNReal.ofReal_one] at hbase
  have hwone (ω : Ω) : (μ ω).withDensity (fun _ => 1) = μ ω := withDensity_one
  simp only [hwone] at hbase
  refine ⟨R, hR, ?_⟩
  intro g hg
  let X := localModConstPairings α hC univ
  let Y := localModConstPairings α (fun ω => addFunPairing (hC ω) g) univ
  have hX : Measurable X := by
    apply measurable_pi_iff.mpr
    intro φ
    change Measurable (fun ω => hC ω φ.1 - α * ∫ z, φ.1 z * Real.log ‖z‖)
    exact (h.measurable_pairing φ.1 φ.2.1).sub_const _
  have hY : Measurable Y := by
    apply measurable_pi_iff.mpr
    intro φ
    change Measurable (fun ω => (hC ω φ.1 + ∫ z, g z * φ.1 z) -
      α * ∫ z, φ.1 z * Real.log ‖z‖)
    exact ((h.measurable_pairing φ.1 φ.2.1).add_const _).sub_const _
  have hac := h.singular_smooth_shift_modConst_pairing_laws hg α univ
  change P.map Y ≪ P.map X ∧ P.map X ≪ P.map Y at hac
  have hf := hac.1.map hF
  have hb := hac.2.map hF
  rw [Measure.map_map hF hY, Measure.map_map hF hX] at hf
  rw [Measure.map_map hF hX, Measure.map_map hF hY] at hb
  have hbaseEq : (F ∘ X) =ᵐ[P] (fun ω =>
      (localModConstPairings α hC (ball 0 ε) ω,
       normalizedRestriction (μ ω) (ball 0 R), fun n =>
         ENNReal.ofReal (Real.exp (ξ * (-hC ω ψ))) *
           internalMetric (D ω) (V n) (p n).1 (p n).2)) := by
    filter_upwards [hbase, hGb] with ω hm hn
    change (Q (localModConstPairings α id univ (hC ω)),
      M (Q (localModConstPairings α id univ (hC ω))), _) = _
    rw [hQeq]
    exact Prod.ext rfl (Prod.ext hm (funext hn))
  have hshiftEq : (F ∘ Y) =ᵐ[P] (fun ω =>
      (localModConstPairings α (fun ω => addFunPairing (hC ω) g) (ball 0 ε) ω,
       normalizedRestriction ((μ ω).withDensity
         (fun z => ENNReal.ofReal (Real.exp (γ * g z)))) (ball 0 R), fun n =>
           ENNReal.ofReal (Real.exp (ξ * (-(hC ω ψ + ∫ z, g z * ψ z)))) *
             internalMetric (fun x y => (weylScaling (D ω) ξ g x y).toReal)
               (V n) (p n).1 (p n).2)) := by
    filter_upwards [hMeq g hg, hGs g hg] with ω hm hn
    change (Q (localModConstPairings α id univ (addFunPairing (hC ω) g)),
      M (Q (localModConstPairings α id univ (addFunPairing (hC ω) g))), _) = _
    rw [hQeq]
    exact Prod.ext rfl (Prod.ext hm (funext hn))
  rw [Measure.map_congr hbaseEq, Measure.map_congr hshiftEq] at hf hb
  exact ⟨hf, hb, (hF.comp hX).aemeasurable.congr hbaseEq,
    (hF.comp hY).aemeasurable.congr hshiftEq⟩

/-- The local field, normalized measure and normalized internal distances on
countably many open domains have equivalent joint laws under smooth shifts. -/
theorem IsWholePlaneGFF.exists_joint_smooth_shift_law_on_domains
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α ε : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} {D : Ω → ℂ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hfull : ∀ᵐ ω ∂P, ∀ W : Set ℂ, IsOpen W → W.Nonempty → 0 < μ ω W)
    (hε : 0 < ε) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ)
    (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hD : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
      ENNReal.ofReal (D ω u v) =
        weylScaling (𝔇 (hC ω)) ξ (fun z => -α * Real.log ‖z‖) u v)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (V : ℕ → Set ℂ) (hV : ∀ n, IsOpen (V n))
    (hconn : ∀ n, (0 : ℂ) ∈ V n → IsConnected (V n))
    (ψ : ℂ → ℝ) (hψ : IsTestFunction univ ψ) (hψint : ∫ z, ψ z = 1)
    (p : ℕ → ℂ × ℂ) (hp : ∀ n, (p n).1 ∈ V n ∧ (p n).2 ∈ V n)
    (hξ : 0 ≤ ξ) :
    ∃ R ∈ Ioo (0 : ℝ) ε, ∀ g : ℂ → ℝ, IsTestFunction univ g →
      P.map (fun ω =>
        (localModConstPairings α (fun ω => addFunPairing (hC ω) g) (ball 0 ε) ω,
         normalizedRestriction ((μ ω).withDensity
           (fun z => ENNReal.ofReal (Real.exp (γ * g z)))) (ball 0 R),
         fun n => ENNReal.ofReal (Real.exp (ξ * (-(hC ω ψ + ∫ z, g z * ψ z)))) *
           internalMetric (fun x y => (weylScaling (D ω) ξ g x y).toReal)
             (V n) (p n).1 (p n).2)) ≪
      P.map (fun ω =>
        (localModConstPairings α hC (ball 0 ε) ω,
         normalizedRestriction (μ ω) (ball 0 R), fun n =>
           ENNReal.ofReal (Real.exp (ξ * (-hC ω ψ))) *
             internalMetric (D ω) (V n) (p n).1 (p n).2)) ∧
      P.map (fun ω =>
        (localModConstPairings α hC (ball 0 ε) ω,
         normalizedRestriction (μ ω) (ball 0 R), fun n =>
           ENNReal.ofReal (Real.exp (ξ * (-hC ω ψ))) *
             internalMetric (D ω) (V n) (p n).1 (p n).2)) ≪
      P.map (fun ω =>
        (localModConstPairings α (fun ω => addFunPairing (hC ω) g) (ball 0 ε) ω,
         normalizedRestriction ((μ ω).withDensity
           (fun z => ENNReal.ofReal (Real.exp (γ * g z)))) (ball 0 R),
         fun n => ENNReal.ofReal (Real.exp (ξ * (-(hC ω ψ + ∫ z, g z * ψ z)))) *
           internalMetric (fun x y => (weylScaling (D ω) ξ g x y).toReal)
             (V n) (p n).1 (p n).2)) := by
  exact h.exists_joint_smooth_shift_law_on_domains_between hμ hfull le_rfl hε
    𝔇 h𝔇 hD hmetric V hV hconn ψ hψ hψint p hp hξ

/-- The joint law on countably many domains for a subcritical measure and
an inserted metric of the same field. -/
theorem IsWholePlaneGFF.exists_joint_smooth_shift_law_on_domains_between_of_field
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α a ε : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} {D : Ω → ℂ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    (ha : 0 ≤ a) (haε : a < ε) (hDfield : IsLQGMetricOfField P γ ξ α hC D)
    (haxioms : LQGMetricFieldAxioms P γ ξ α hC hcirc)
    (V : ℕ → Set ℂ) (hV : ∀ n, IsOpen (V n))
    (hconn : ∀ n, (0 : ℂ) ∈ V n → IsConnected (V n))
    (ψ : ℂ → ℝ) (hψ : IsTestFunction univ ψ) (hψint : ∫ z, ψ z = 1)
    (p : ℕ → ℂ × ℂ) (hp : ∀ n, (p n).1 ∈ V n ∧ (p n).2 ∈ V n)
    (hξ : 0 ≤ ξ) :
    ∃ R ∈ Ioo a ε, ∀ g : ℂ → ℝ, IsTestFunction univ g →
      P.map (fun ω =>
        (localModConstPairings α (fun ω => addFunPairing (hC ω) g) (ball 0 ε) ω,
         normalizedRestriction ((μ ω).withDensity
           (fun z => ENNReal.ofReal (Real.exp (γ * g z)))) (ball 0 R),
         fun n => ENNReal.ofReal (Real.exp (ξ * (-(hC ω ψ + ∫ z, g z * ψ z)))) *
           internalMetric (fun x y => (weylScaling (D ω) ξ g x y).toReal)
             (V n) (p n).1 (p n).2)) ≪
      P.map (fun ω =>
        (localModConstPairings α hC (ball 0 ε) ω,
         normalizedRestriction (μ ω) (ball 0 R), fun n =>
           ENNReal.ofReal (Real.exp (ξ * (-hC ω ψ))) *
             internalMetric (D ω) (V n) (p n).1 (p n).2)) ∧
      P.map (fun ω =>
        (localModConstPairings α hC (ball 0 ε) ω,
         normalizedRestriction (μ ω) (ball 0 R), fun n =>
           ENNReal.ofReal (Real.exp (ξ * (-hC ω ψ))) *
             internalMetric (D ω) (V n) (p n).1 (p n).2)) ≪
      P.map (fun ω =>
        (localModConstPairings α (fun ω => addFunPairing (hC ω) g) (ball 0 ε) ω,
         normalizedRestriction ((μ ω).withDensity
           (fun z => ENNReal.ofReal (Real.exp (γ * g z)))) (ball 0 R),
         fun n => ENNReal.ofReal (Real.exp (ξ * (-(hC ω ψ + ∫ z, g z * ψ z)))) *
           internalMetric (fun x y => (weylScaling (D ω) ξ g x y).toReal)
             (V n) (p n).1 (p n).2)) := by
  have hmetric := ae_isEuclideanLengthMetric_of_metricFieldAxioms P γ ξ α hC hcirc D
    haxioms h hγ hγ2 hα hDfield
  obtain ⟨𝔇, h𝔇, hD⟩ := hDfield
  exact h.exists_joint_smooth_shift_law_on_domains_between hμ
    (lqgMeasureFullSupportStmt_holds γ α hγ hγ2 hα Ω P hC hcirc μ h hμ)
    ha haε 𝔇 h𝔇 hD hmetric V hV hconn ψ hψ hψint p hp hξ

/-- The joint law and almost-everywhere measurability on countably many domains for a subcritical measure and
an inserted metric of the same field. -/
theorem IsWholePlaneGFF.exists_joint_smooth_shift_law_and_aemeasurable_on_domains_between_of_field
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α a ε : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} {D : Ω → ℂ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    (ha : 0 ≤ a) (haε : a < ε) (hDfield : IsLQGMetricOfField P γ ξ α hC D)
    (haxioms : LQGMetricFieldAxioms P γ ξ α hC hcirc)
    (V : ℕ → Set ℂ) (hV : ∀ n, IsOpen (V n))
    (hconn : ∀ n, (0 : ℂ) ∈ V n → IsConnected (V n))
    (ψ : ℂ → ℝ) (hψ : IsTestFunction univ ψ) (hψint : ∫ z, ψ z = 1)
    (p : ℕ → ℂ × ℂ) (hp : ∀ n, (p n).1 ∈ V n ∧ (p n).2 ∈ V n)
    (hξ : 0 ≤ ξ) :
    ∃ R ∈ Ioo a ε, ∀ g : ℂ → ℝ, IsTestFunction univ g →
      P.map (fun ω =>
        (localModConstPairings α (fun ω => addFunPairing (hC ω) g) (ball 0 ε) ω,
         normalizedRestriction ((μ ω).withDensity
           (fun z => ENNReal.ofReal (Real.exp (γ * g z)))) (ball 0 R),
         fun n => ENNReal.ofReal (Real.exp (ξ * (-(hC ω ψ + ∫ z, g z * ψ z)))) *
           internalMetric (fun x y => (weylScaling (D ω) ξ g x y).toReal)
             (V n) (p n).1 (p n).2)) ≪
      P.map (fun ω =>
        (localModConstPairings α hC (ball 0 ε) ω,
         normalizedRestriction (μ ω) (ball 0 R), fun n =>
           ENNReal.ofReal (Real.exp (ξ * (-hC ω ψ))) *
             internalMetric (D ω) (V n) (p n).1 (p n).2)) ∧
      P.map (fun ω =>
        (localModConstPairings α hC (ball 0 ε) ω,
         normalizedRestriction (μ ω) (ball 0 R), fun n =>
           ENNReal.ofReal (Real.exp (ξ * (-hC ω ψ))) *
             internalMetric (D ω) (V n) (p n).1 (p n).2)) ≪
      P.map (fun ω =>
        (localModConstPairings α (fun ω => addFunPairing (hC ω) g) (ball 0 ε) ω,
         normalizedRestriction ((μ ω).withDensity
           (fun z => ENNReal.ofReal (Real.exp (γ * g z)))) (ball 0 R),
         fun n => ENNReal.ofReal (Real.exp (ξ * (-(hC ω ψ + ∫ z, g z * ψ z)))) *
           internalMetric (fun x y => (weylScaling (D ω) ξ g x y).toReal)
             (V n) (p n).1 (p n).2)) ∧
      AEMeasurable (fun ω =>
      (localModConstPairings α hC (ball 0 ε) ω,
       normalizedRestriction (μ ω) (ball 0 R), fun n =>
         ENNReal.ofReal (Real.exp (ξ * (-hC ω ψ))) *
           internalMetric (D ω) (V n) (p n).1 (p n).2)) P ∧
      AEMeasurable (fun ω =>
      (localModConstPairings α (fun ω => addFunPairing (hC ω) g) (ball 0 ε) ω,
       normalizedRestriction ((μ ω).withDensity
         (fun z => ENNReal.ofReal (Real.exp (γ * g z)))) (ball 0 R), fun n =>
           ENNReal.ofReal (Real.exp (ξ * (-(hC ω ψ + ∫ z, g z * ψ z)))) *
             internalMetric (fun x y => (weylScaling (D ω) ξ g x y).toReal)
               (V n) (p n).1 (p n).2)) P := by
  have hmetric := ae_isEuclideanLengthMetric_of_metricFieldAxioms P γ ξ α hC hcirc D
    haxioms h hγ hγ2 hα hDfield
  obtain ⟨𝔇, h𝔇, hD⟩ := hDfield
  exact h.exists_joint_smooth_shift_law_and_aemeasurable_on_domains_between hμ
    (lqgMeasureFullSupportStmt_holds γ α hγ hγ2 hα Ω P hC hcirc μ h hμ)
    ha haε 𝔇 h𝔇 hD hmetric V hV hconn ψ hψ hψint p hp hξ

/-- A countable family of admissible metric coordinates can be indexed by natural numbers, even when the family is empty. -/
theorem exists_countable_admissible_metric_coordinates
    (S : Set (Set ℂ × (ℂ × ℂ))) (hS : S.Countable)
    (hvalid : ∀ t ∈ S, IsOpen t.1 ∧ ((0 : ℂ) ∈ t.1 → IsConnected t.1) ∧
      t.2.1 ∈ t.1 ∧ t.2.2 ∈ t.1) :
    ∃ V : ℕ → Set ℂ, ∃ p : ℕ → ℂ × ℂ,
      (∀ n, IsOpen (V n) ∧ ((0 : ℂ) ∈ V n → IsConnected (V n)) ∧
        (p n).1 ∈ V n ∧ (p n).2 ∈ V n) ∧
      ∀ t ∈ S, ∃ n, V n = t.1 ∧ p n = t.2 := by
  let t₀ : Set ℂ × (ℂ × ℂ) := (univ, (0, 0))
  let T := insert t₀ S
  have hT : T.Countable := hS.insert t₀
  have : Countable T := hT.to_subtype
  have : Nonempty T := ⟨⟨t₀, mem_insert _ _⟩⟩
  obtain ⟨e, he⟩ := exists_surjective_nat T
  refine ⟨fun n => (e n).1.1, fun n => (e n).1.2, ?_, ?_⟩
  · intro n
    dsimp only
    have ht : (e n).1 = t₀ ∨ (e n).1 ∈ S := (mem_insert_iff).mp (e n).2
    rcases ht with ht | ht
    · rw [ht]
      exact ⟨isOpen_univ, fun _ => isConnected_univ, mem_univ _, mem_univ _⟩
    · exact hvalid _ ht
  · intro t ht
    obtain ⟨n, hn⟩ := he ⟨t, mem_insert_of_mem t₀ ht⟩
    have heq : (e n).1 = t := congrArg Subtype.val hn
    exact ⟨n, congrArg Prod.fst heq, congrArg Prod.snd heq⟩


/-- Read a listed metric coordinate from a sequence, using zero outside the list. -/
noncomputable def coordinateReadout (V : ℕ → Set ℂ) (p : ℕ → ℂ × ℂ)
    (t : Set ℂ × (ℂ × ℂ)) (a : ℕ → ℝ≥0∞) : ℝ≥0∞ :=
  by
    classical
    exact if h : ∃ n, (V n, p n) = t then a (Classical.choose h) else 0

/-- Each coordinate readout is measurable. -/
theorem measurable_coordinateReadout (V : ℕ → Set ℂ) (p : ℕ → ℂ × ℂ)
    (t : Set ℂ × (ℂ × ℂ)) : Measurable (coordinateReadout V p t) := by
  classical
  unfold coordinateReadout
  split
  · exact measurable_pi_apply _
  · exact measurable_const

/-- The readout recovers any function evaluated along the coordinate sequence. -/
theorem coordinateReadout_apply (V : ℕ → Set ℂ) (p : ℕ → ℂ × ℂ)
    (t : Set ℂ × (ℂ × ℂ)) (ht : ∃ n, (V n, p n) = t)
    (F : Set ℂ × (ℂ × ℂ) → ℝ≥0∞) :
    coordinateReadout V p t (fun n => F (V n, p n)) = F t := by
  classical
  simp [coordinateReadout, ht, Classical.choose_spec ht]


end HarmonicBalls

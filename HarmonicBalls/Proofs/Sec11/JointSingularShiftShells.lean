import HarmonicBalls.Proofs.Sec11.JointPuncturedSingularShift
import HarmonicBalls.Steps.Sec11.WeylPointRemoval

/-! # Joint singular observables under shell bounds

The Cameron–Martin argument uses Leonardo Bonanno's LatticeProb formalization.
The metric-field axioms are staged and await source check. The summable shell
bounds are explicit geometric hypotheses, not established here.
-/

noncomputable section

namespace HarmonicBalls

open MeasureTheory Filter Set Metric
open scoped ENNReal

set_option maxHeartbeats 400000 in
/-- Summable punctured shell bounds extend the joint decoder to distances on
the full open domains between nonzero endpoints. -/
theorem IsWholePlaneGFF.exists_joint_singular_weyl_shift_decoder_of_shell_bounds
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
    (p : ℕ → ℂ × ℂ) (hp : ∀ n, (p n).1 ∈ U n ∧ (p n).1 ≠ 0)
    (hp₂ : ∀ n, (p n).2 ≠ 0)
    (hshell : ∀ᵐ ω ∂P, ∀ i, ∃ (R q : ℝ) (c : ℕ → ℝ≥0∞),
      0 < R ∧ 0 < q ∧ q < 1 ∧ (∑' n, c n) ≠ ∞ ∧
      ∀ n, ∀ x ∈ geometricShell R q n, ∀ y ∈ geometricShell R q n,
        internalMetric (D ω) (U i \ {0}) x y ≤ c n) :
    ∃ R ∈ Ioo (0 : ℝ) ε,
      ∃ F : (LocalZeroMeanTest univ → ℝ) → Measure ℂ × (ℕ → ℝ≥0∞), Measurable F ∧
        (∀ᵐ ω ∂P, F (localModConstPairings 0 hC univ ω) =
          (normalizedRestriction (μ ω) (ball 0 R), fun n =>
            ENNReal.ofReal (Real.exp (ξ * (-(hC ω ψ + ∫ z, f z * ψ z)))) *
              internalMetric (D ω) (U n) (p n).1 (p n).2)) ∧
        ∀ g : ℂ → ℝ, IsTestFunction univ g → (∀ z, g z ≤ 0) →
          (∀ᵐ ω ∂P, F (localModConstPairings 0
            (fun ω => addFunPairing (hC ω) g) univ ω) =
            (normalizedRestriction ((μ ω).withDensity
              (fun z => ENNReal.ofReal (Real.exp (γ * g z)))) (ball 0 R), fun n =>
                ENNReal.ofReal (Real.exp (ξ * (-(hC ω ψ + ∫ z, (g z + f z) * ψ z)))) *
                  internalMetric (fun x y => (weylScaling (D ω) ξ g x y).toReal)
                    (U n) (p n).1 (p n).2)) ∧
          P.map (F ∘ localModConstPairings 0
            (fun ω => addFunPairing (hC ω) g) univ) ≪
            P.map (F ∘ localModConstPairings 0 hC univ) ∧
          P.map (F ∘ localModConstPairings 0 hC univ) ≪
            P.map (F ∘ localModConstPairings 0
              (fun ω => addFunPairing (hC ω) g) univ) := by
  obtain ⟨R, hR, F, hF, hbase, hshift⟩ :=
    h.exists_joint_punctured_singular_weyl_shift_decoder hμ hfull hε 𝔇 h𝔇 hD
      hDfield haxioms hγ hγ₂ hα hξ ψ hψ hψint f hf U hU p hp
  have hmetric := ae_isEuclideanLengthMetric_of_metricFieldAxioms P γ ξ α hC hcirc D
    haxioms h hγ hγ₂ hα hDfield
  have hremoval := ae_singularField_nonpositive_weyl_point_removal P γ ξ α hC hcirc D
    haxioms h hγ hγ₂ hα hDfield hξ
  refine ⟨R, hR, F, hF, ?_, ?_⟩
  · filter_upwards [hbase, hmetric, hshell] with ω hb hm hs
    rw [hb]
    congr 1
    funext i
    obtain ⟨r, q, c, hr, hq, hq1, hsum, hdiam⟩ := hs i
    rw [hm.internalMetric_sdiff_zero_eq_of_geometric_shells (U i) hr hq hq1
      c hdiam hsum (hp i).2 (hp₂ i)]
  · intro g hg hu
    obtain ⟨hgeq, hac, hca⟩ := hshift g hg hu
    refine ⟨?_, hac, hca⟩
    filter_upwards [hgeq, hremoval, hshell] with ω he hr hs
    rw [he]
    congr 1
    funext i
    obtain ⟨r, q, c, hr', hq, hq1, hsum, hdiam⟩ := hs i
    rw [hr g hg.1.continuous hg.2.1 hu (U i) (hU i) r q hr' hq hq1
      c hdiam hsum (p i).1 (p i).2 (hp i).2 (hp₂ i)]

set_option maxHeartbeats 400000 in
/-- Point removal for the original singular metric extends the joint decoder
to full open domains for all nonpositive smooth shifts. -/
theorem IsWholePlaneGFF.exists_joint_singular_weyl_shift_decoder_of_point_removal
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
    (p : ℕ → ℂ × ℂ) (hp : ∀ n, (p n).1 ∈ U n ∧ (p n).1 ≠ 0)
    (hp₂ : ∀ n, (p n).2 ≠ 0)
    (hremove : ∀ᵐ ω ∂P, ∀ i, ∀ a ∈ U i \ {0}, ∀ b ∈ U i \ {0},
      internalMetric (D ω) (U i \ {0}) a b = internalMetric (D ω) (U i) a b) :
    ∃ R ∈ Ioo (0 : ℝ) ε,
      ∃ F : (LocalZeroMeanTest univ → ℝ) → Measure ℂ × (ℕ → ℝ≥0∞), Measurable F ∧
        (∀ᵐ ω ∂P, F (localModConstPairings 0 hC univ ω) =
          (normalizedRestriction (μ ω) (ball 0 R), fun n =>
            ENNReal.ofReal (Real.exp (ξ * (-(hC ω ψ + ∫ z, f z * ψ z)))) *
              internalMetric (D ω) (U n) (p n).1 (p n).2)) ∧
        ∀ g : ℂ → ℝ, IsTestFunction univ g → (∀ z, g z ≤ 0) →
          (∀ᵐ ω ∂P, F (localModConstPairings 0
            (fun ω => addFunPairing (hC ω) g) univ ω) =
            (normalizedRestriction ((μ ω).withDensity
              (fun z => ENNReal.ofReal (Real.exp (γ * g z)))) (ball 0 R), fun n =>
                ENNReal.ofReal (Real.exp (ξ * (-(hC ω ψ + ∫ z, (g z + f z) * ψ z)))) *
                  internalMetric (fun x y => (weylScaling (D ω) ξ g x y).toReal)
                    (U n) (p n).1 (p n).2)) ∧
          P.map (F ∘ localModConstPairings 0
            (fun ω => addFunPairing (hC ω) g) univ) ≪
            P.map (F ∘ localModConstPairings 0 hC univ) ∧
          P.map (F ∘ localModConstPairings 0 hC univ) ≪
            P.map (F ∘ localModConstPairings 0
              (fun ω => addFunPairing (hC ω) g) univ) := by
  obtain ⟨R, hR, F, hF, hbase, hshift⟩ :=
    h.exists_joint_punctured_singular_weyl_shift_decoder hμ hfull hε 𝔇 h𝔇 hD
      hDfield haxioms hγ hγ₂ hα hξ ψ hψ hψint f hf U hU p hp
  have htransfer := ae_singularField_nonpositive_weyl_point_removal_of_point_removal
    P γ ξ α hC hcirc D haxioms h hγ hγ₂ hα hDfield hξ
  refine ⟨R, hR, F, hF, ?_, ?_⟩
  · filter_upwards [hbase, hremove] with ω hb hr
    rw [hb]
    congr 1
    funext i
    by_cases hy : (p i).2 ∈ U i
    · rw [hr i (p i).1 ⟨(hp i).1, by simpa using (hp i).2⟩
        (p i).2 ⟨hy, by simpa using hp₂ i⟩]
    · have hpunc : (p i).2 ∉ U i \ {0} := fun hm => hy hm.1
      have htop {A : Set ℂ} (ha : (p i).2 ∉ A) :
          internalMetric (D ω) A (p i).1 (p i).2 = ⊤ := by
        unfold internalMetric
        apply iInf_eq_top.mpr
        intro path
        apply iInf_eq_top.mpr
        intro hpath
        exact (ha (path.target ▸ hpath 1)).elim
      rw [htop hpunc, htop hy]
  · intro g hg hu
    obtain ⟨hgeq, hac, hca⟩ := hshift g hg hu
    refine ⟨?_, hac, hca⟩
    filter_upwards [hgeq, htransfer, hremove] with ω he ht hr
    rw [he]
    congr 1
    funext i
    rw [ht g hg.1.continuous hg.2.1 hu (U i) (hU i) (hr i)
      (p i).1 (p i).2 (hp i).2 (hp₂ i)]


end HarmonicBalls

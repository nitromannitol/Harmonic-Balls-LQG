import HarmonicBalls.Proofs.Sec11.JointSingularShiftShells
import HarmonicBalls.Steps.Sec11.DenseInternalMetricVersions

/-! # Joint singular observables at all endpoints

The Cameron–Martin argument uses Leonardo Bonanno's LatticeProb formalization.
The metric-field axioms are staged and await source check.
-/

noncomputable section

namespace HarmonicBalls

open MeasureTheory Filter Set Metric Topology
open scoped ENNReal

/-- The normalized internal distance is continuous at points in an open domain. -/
theorem IsEuclideanLengthMetric.liminf_normalized_internalMetric
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {V : Set ℂ} (hV : IsOpen V) {x y : ℂ} (hx : x ∈ V) (hy : y ∈ V)
    {a b : ℕ → ℂ} (ha : Tendsto a atTop (𝓝 x)) (hb : Tendsto b atTop (𝓝 y))
    (c : ℝ≥0∞) (hc : c ≠ ∞) :
    liminf (fun n => c * internalMetric D V (a n) (b n)) atTop =
      c * internalMetric D V x y := by
  have hnonneg (u v : ℂ) : 0 ≤ D u v := by
    have ht := hD.triangle u v u
    rw [hD.self_eq_zero, hD.symm v u] at ht
    linarith
  have ht := (hD.continuousAt_internalMetric_pair hnonneg hV hx hy).tendsto.comp
    (ha.prodMk_nhds hb)
  exact ((ENNReal.continuous_const_mul hc).continuousAt.tendsto.comp ht).liminf_eq

set_option maxHeartbeats 400000 in
/-- A common joint decoder extends to endpoints at the origin by continuity,
provided the unshifted internal metric permits point removal. -/
theorem IsWholePlaneGFF.exists_joint_singular_weyl_shift_decoder_at_all_endpoints
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
    (p : ℕ → ℂ × ℂ) (hp : ∀ n, (p n).1 ∈ U n ∧ (p n).2 ∈ U n)
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
  classical
  have hdense (n : ℕ) : U n ⊆ closure (U n \ {0}) := by
    simpa only [sdiff_eq] using (dense_compl_singleton (0 : ℂ)).open_subset_closure_inter (hU n)
  have hseqA (n : ℕ) : ∃ q : ℕ → ℂ, (∀ k, q k ∈ U n \ {0}) ∧
      Tendsto q atTop (𝓝 (p n).1) := mem_closure_iff_seq_limit.mp (hdense n (hp n).1)
  have hseqB (n : ℕ) : ∃ q : ℕ → ℂ, (∀ k, q k ∈ U n \ {0}) ∧
      Tendsto q atTop (𝓝 (p n).2) := mem_closure_iff_seq_limit.mp (hdense n (hp n).2)
  choose a ha hat using hseqA
  choose b hb hbt using hseqB
  let V : ℕ → Set ℂ := fun j => U j.unpair.1
  let q : ℕ → ℂ × ℂ := fun j => (a j.unpair.1 j.unpair.2, b j.unpair.1 j.unpair.2)
  have hV (j : ℕ) : IsOpen (V j) := hU _
  have hq (j : ℕ) : (q j).1 ∈ V j ∧ (q j).1 ≠ 0 := by
    exact ⟨(ha _ _).1, by simpa using (ha _ _).2⟩
  have hq₂ (j : ℕ) : (q j).2 ≠ 0 := by simpa using (hb _ _).2
  have hrem : ∀ᵐ ω ∂P, ∀ j, ∀ x ∈ V j \ {0}, ∀ y ∈ V j \ {0},
      internalMetric (D ω) (V j \ {0}) x y = internalMetric (D ω) (V j) x y := by
    filter_upwards [hremove] with ω hr j
    exact hr j.unpair.1
  obtain ⟨R, hR, F, hF, hbase, hshift⟩ :=
    h.exists_joint_singular_weyl_shift_decoder_of_point_removal hμ hfull hε 𝔇 h𝔇
      hD hDfield haxioms hγ hγ₂ hα hξ ψ hψ hψint f hf V hV q hq hq₂ hrem
  let T : Measure ℂ × (ℕ → ℝ≥0∞) → Measure ℂ × (ℕ → ℝ≥0∞) :=
    fun w => (w.1, fun n => liminf (fun k => w.2 (Nat.pair n k)) atTop)
  have hT : Measurable T := by
    apply measurable_fst.prodMk
    apply measurable_pi_iff.mpr
    intro n
    apply Measurable.liminf
    intro k
    exact (measurable_pi_apply (Nat.pair n k)).comp measurable_snd
  let G := T ∘ F
  have hG : Measurable G := hT.comp hF
  have hmetric := ae_isEuclideanLengthMetric_of_metricFieldAxioms P γ ξ α hC hcirc D
    haxioms h hγ hγ₂ hα hDfield
  have hshiftmetric := ae_singularField_weylBump_lengthMetric_of_metricFieldAxioms
    P γ ξ α hC hcirc D haxioms h hγ hγ₂ hα hDfield hξ
  refine ⟨R, hR, G, hG, ?_, ?_⟩
  · filter_upwards [hbase, hmetric] with ω hv hm
    change T (F (localModConstPairings 0 hC univ ω)) = _
    rw [hv]
    dsimp only [T]
    congr 1
    funext n
    change liminf (fun k => _ * internalMetric (D ω) (U (Nat.unpair (Nat.pair n k)).1)
      (a (Nat.unpair (Nat.pair n k)).1 (Nat.unpair (Nat.pair n k)).2)
      (b (Nat.unpair (Nat.pair n k)).1 (Nat.unpair (Nat.pair n k)).2)) atTop = _
    simp only [Nat.unpair_pair]
    exact hm.liminf_normalized_internalMetric (hU n) (hp n).1 (hp n).2
      (hat n) (hbt n) _ ENNReal.ofReal_ne_top
  · intro g hg hu
    obtain ⟨hgeq, hac, hca⟩ := hshift g hg hu
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
    have hfwd := hac.map hT
    have hbwd := hca.map hT
    rw [Measure.map_map hT (hF.comp hY), Measure.map_map hT (hF.comp hX)] at hfwd
    rw [Measure.map_map hT (hF.comp hX), Measure.map_map hT (hF.comp hY)] at hbwd
    refine ⟨?_, hfwd, hbwd⟩
    filter_upwards [hgeq, hshiftmetric] with ω hv hm
    change T (F (localModConstPairings 0 (fun ω => addFunPairing (hC ω) g) univ ω)) = _
    rw [hv]
    dsimp only [T]
    congr 1
    funext n
    change liminf (fun k => _ * internalMetric _ (U (Nat.unpair (Nat.pair n k)).1)
      (a (Nat.unpair (Nat.pair n k)).1 (Nat.unpair (Nat.pair n k)).2)
      (b (Nat.unpair (Nat.pair n k)).1 (Nat.unpair (Nat.pair n k)).2)) atTop = _
    simp only [Nat.unpair_pair]
    exact (hm g hg.1.continuous hg.2.1 hu).liminf_normalized_internalMetric
      (hU n) (hp n).1 (hp n).2 (hat n) (hbt n) _ ENNReal.ofReal_ne_top

#print axioms IsEuclideanLengthMetric.liminf_normalized_internalMetric
#print axioms IsWholePlaneGFF.exists_joint_singular_weyl_shift_decoder_at_all_endpoints

end HarmonicBalls

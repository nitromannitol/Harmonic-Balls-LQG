import HarmonicBalls.FirstPass.Phase2.ClosedSquareDiamAwayFromZero
import HarmonicBalls.FirstPass.Phase2.EnlargedDyadicCellGrid
import LatticeProb.LQG.ClosedDyadicGridRectangleSmall

/-!
# Small internal diameters of the clipped enlarged dyadic cells away from the singularity

Let `D_h = e^{-ξ α₀ log |·|} · D_{h^ℂ}` be the γ-LQG metric of `h = h^ℂ - α₀ log |·|` (`IsLQGMetricOfField`) and let
`S₂` be a closed dyadic square with `0 ∉ S₂`. For `ε, η > 0` there is `N₀` such that for every `N ≥ N₀`, with
probability at least `1 - η` (inner probability: a measurable event of that probability), every enlarged dyadic cell
`Ŝ = enlargedDyadicCell N j k` with `closedDyadicSquare N j k ⊆ S₂` satisfies
`sup_{u, v ∈ Ŝ ∩ S₂} D_h(u, v; Ŝ ∩ S₂) ≤ ε`. This is the case `0 ∉ S₂` of `DyadicCellDiamSmallFrozen` (paper, proof of
Lemma 11.10, lines 3010-3016), under the uniform unit-square crossing tail of `𝔇`
(Dubédat-Falconet-Gwynne-Pfeffer-Sun, arXiv:1905.00380v2, Proposition 3.1, p. 13, at unit scale).

Proof. `Ŝ ∩ S₂` is a closed rectangle made of at most `10 × 10` closed dyadic subsquares of `S₂` of level
`N + 3 - n₀` (`enlargedDyadicCell_inter_closedDyadicSquare_eq_gridRectangle`). On the range space of the model (in
`Type`, `LQGMetricUniv.rangeMeasure`) the weight `-α₀ log |·|` is continuous on `S₂`, and the probability that some
such grid rectangle has internal diameter larger than `ε` tends to `0`
(`LatticeProb.LQG.IsLQGMetric.tendsto_measure_not_forall_internalMetric_weylScaling_gridRectangle_le_of_continuousOn`).
The outer probability of the bad event on `Ω` is at most the probability on the range space
(`LQGMetricUniv.measure_preimage_toRange_le`), and the complement of a measurable hull of the bad event is the
required measurable event (`exists_measurableSet_subset_of_measure_compl_le`).

## Main statements

* `HarmonicBalls.exists_measurableSet_enlargedDyadicCell_internalMetric_le_of_zero_not_mem`
* `HarmonicBalls.dyadicCellDiamSmallFrozen_of_unitTail`: `DyadicCellDiamSmallFrozen` from the uniform unit-square
  crossing tail and the case `0 ∈ S₂`.
-/

universe u

namespace HarmonicBalls

open MeasureTheory Filter Set
open scoped ENNReal Topology

/-- The outer measure of the preimage of any set of the range space is at most its `rangeMeasure`. -/
theorem LQGMetricUniv.measure_preimage_toRange_le {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → LQGMetricUniv.SamplePoint} (T : Set (LQGMetricUniv.RangeSpace P X)) :
    P (LQGMetricUniv.toRange P X ⁻¹' T) ≤ LQGMetricUniv.rangeMeasure P X T := by
  rw [← Measure.completion_apply]
  exact Measure.le_map_apply LQGMetricUniv.measurable_toRange.aemeasurable T

/-- Inner probability from an outer probability bound on the complement: if `P Gᶜ ≤ η` for a probability measure
`P`, then the complement of a measurable hull of `Gᶜ` is a measurable subset of `G` of probability at least
`1 - η`. -/
theorem exists_measurableSet_subset_of_measure_compl_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {G : Set Ω} {η : ℝ} (hη : 0 ≤ η) (h : P Gᶜ ≤ ENNReal.ofReal η) :
    ∃ A ⊆ G, MeasurableSet A ∧ ENNReal.ofReal (1 - η) ≤ P A := by
  refine ⟨(toMeasurable P Gᶜ)ᶜ, fun ω hω => ?_, (measurableSet_toMeasurable P _).compl, ?_⟩
  · by_contra h'
    exact hω (subset_toMeasurable P _ h')
  · rw [prob_compl_eq_one_sub (measurableSet_toMeasurable P _), measure_toMeasurable,
      ENNReal.ofReal_sub _ hη, ENNReal.ofReal_one]
    exact tsub_le_tsub_left h _

/-- **Derived.** Small internal diameters of the clipped enlarged dyadic cells `Ŝ ∩ S₂`, simultaneously over the cells
of level `N` inside a closed dyadic square `S₂` avoiding `0`, with probability at least `1 - η` for all large `N`, for
the γ-LQG metric of a whole-plane GFF plus `-α₀ log |·|`. Inputs: the positivity of the Weyl exponent and the uniform
unit-square crossing tail of `𝔇` (Dubédat-Falconet-Gwynne-Pfeffer-Sun, arXiv:1905.00380v2, Proposition 3.1, p. 13).
The probability space may lie in any universe. -/
theorem exists_measurableSet_enlargedDyadicCell_internalMetric_le_of_zero_not_mem
    (hXi : LQGMetricExponentPositive)
    (hUniv : ∀ (γ ξ : ℝ) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ), 0 < γ → γ < 2 → IsLQGMetric γ ξ 𝔇 →
      ∃ δ : ℝ, δ < ξ * (lqgQ γ - 2) * Real.log 2 ∧ ∃ p : ℕ → ℝ≥0∞, ∑' n, 4 ^ n * p n ≠ ⊤ ∧
        ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
          IsWholePlaneGFF P hC hcirc → ∀ n : ℕ,
            P {ω | ¬ LatticeProb.LQG.HasShortHalfCrossings (𝔇 (hC ω)) 0 1 0 1
              (ENNReal.ofReal (Real.exp (δ * n)))} ≤ p n)
    {γ α₀ ξ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {D : Ω → ℂ → ℂ → ℝ}
    (hW : IsWholePlaneGFF P hC hcirc) (hD : IsLQGMetricOfField P γ ξ α₀ hC D)
    {S2 : Set ℂ} (hS2 : IsClosedDyadicSquare S2) (h0 : (0 : ℂ) ∉ S2) {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      ∃ A ⊆ {ω | ∀ j k : ℤ, closedDyadicSquare (N : ℤ) j k ⊆ S2 →
          ∀ u ∈ enlargedDyadicCell (N : ℤ) j k ∩ S2, ∀ v ∈ enlargedDyadicCell (N : ℤ) j k ∩ S2,
            internalMetric (D ω) (enlargedDyadicCell (N : ℤ) j k ∩ S2) u v ≤ ENNReal.ofReal ε},
        MeasurableSet A ∧ ENNReal.ofReal (1 - η) ≤ P A := by
  have := hW.isProbabilityMeasure
  obtain ⟨𝔇, h𝔇, hDae⟩ := hD
  have hξ : 0 < ξ := hXi γ ξ 𝔇 hγ0 hγ2 h𝔇
  obtain ⟨δ, hδ, p, hp, huniv⟩ := hUniv γ ξ 𝔇 hγ0 hγ2 h𝔇
  obtain ⟨n₀, j₂, k₂, rfl⟩ := hS2
  have hQQ : lqgQ γ = LatticeProb.LQG.lqgQ γ := rfl
  set f : ℂ → ℝ := fun z => -α₀ * Real.log ‖z‖ with hfdef
  set X := LQGMetricUniv.samplePoint hC hcirc (fun _ => 0) with hX
  have hW' : LatticeProb.Gauss.IsWholePlaneGFF (LQGMetricUniv.rangeMeasure P X) (fun y => y.1.pairing)
      (fun y => y.1.circle) :=
    (LPBridge.isWholePlaneGFF_iff _ _ _).1 (LQGMetricUniv.isWholePlaneGFF_rangeMeasure (fun _ => 0) hW)
  have h𝔇' := (LPBridge.isLQGMetric_iff γ ξ 𝔇).1 h𝔇
  let E : LQGMetricUniv.RangeSpace P X → ℂ → ℂ → ℝ := fun y u v => (weylScaling (𝔇 y.1.pairing) ξ f u v).toReal
  have hE : ∀ᵐ y ∂LQGMetricUniv.rangeMeasure P X, ∀ u v,
      ENNReal.ofReal (E y u v) = LatticeProb.LQG.weylScaling (𝔇 y.1.pairing) ξ f u v := by
    refine LQGMetricUniv.ae_rangeMeasure_iff.2 ?_
    filter_upwards [hDae] with ω hω u v
    have hne : weylScaling (𝔇 (hC ω)) ξ f u v ≠ ⊤ := by
      rw [← (hω u v).2]; exact ENNReal.ofReal_ne_top
    exact ENNReal.ofReal_toReal hne
  have hs : (0 : ℝ) < 2 ^ (-n₀) := zpow_pos two_pos _
  have hSq : closedDyadicSquare n₀ j₂ k₂ =
      Icc ((j₂ : ℝ) * 2 ^ (-n₀)) ((j₂ : ℝ) * 2 ^ (-n₀) + 2 ^ (-n₀)) ×ℂ
        Icc ((k₂ : ℝ) * 2 ^ (-n₀)) ((k₂ : ℝ) * 2 ^ (-n₀) + 2 ^ (-n₀)) := by
    simp only [closedDyadicSquare, add_one_mul]
  have hcont : ContinuousOn f (Icc ((j₂ : ℝ) * 2 ^ (-n₀)) ((j₂ : ℝ) * 2 ^ (-n₀) + 2 ^ (-n₀)) ×ℂ
      Icc ((k₂ : ℝ) * 2 ^ (-n₀)) ((k₂ : ℝ) * 2 ^ (-n₀) + 2 ^ (-n₀))) := by
    rw [← hSq]
    refine continuousOn_const.mul (Real.continuousOn_log.comp continuous_norm.continuousOn fun z hz => ?_)
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, norm_eq_zero]
    rintro rfl
    exact h0 hz
  have hmain := h𝔇'.tendsto_measure_not_forall_internalMetric_weylScaling_gridRectangle_le_of_continuousOn hW' hs hξ
    (θ := (δ + ξ * (lqgQ γ - 2) * Real.log 2) / 2) (by rw [← hQQ]; linarith) (by linarith)
    (fun hC'' hcirc'' hG n => huniv _ _ hC'' hcirc'' ((LPBridge.isWholePlaneGFF_iff _ _ _).2 hG) n) hp
    (E := E) hE hcont 9 hε
  obtain ⟨m0, hm0⟩ := eventually_atTop.1 (hmain.eventually (Iic_mem_nhds (ENNReal.ofReal_pos.2 hη)))
  refine ⟨m0 + n₀.toNat, fun N hN => ?_⟩
  have hmm : m0 ≤ ((N : ℤ) + 3 - n₀).toNat := by omega
  refine exists_measurableSet_subset_of_measure_compl_le hη.le ?_
  refine le_trans (measure_mono_ae ?_)
    ((LQGMetricUniv.measure_preimage_toRange_le _).trans (Set.mem_Iic.1 (hm0 _ hmm)))
  filter_upwards [hDae] with ω hω hbad
  intro hgood
  apply hbad
  intro j k hsub u hu v hv
  obtain ⟨i₀, j₀, K, L, hK, hL, hi, hj, hR⟩ := enlargedDyadicCell_inter_closedDyadicSquare_eq_gridRectangle hsub
  have hEq : E (LQGMetricUniv.toRange P X ω) = D ω := by
    funext u v
    show (weylScaling (𝔇 (hC ω)) ξ f u v).toReal = D ω u v
    rw [← (hω u v).2, ENNReal.toReal_ofReal (hω u v).1]
  rw [hR] at hu hv ⊢
  rw [LPBridge.internalMetric_eq, ← hEq]
  exact hgood i₀ j₀ K L hK hL hi hj u hu v hv

/-- **Derived.** `DyadicCellDiamSmallFrozen` (small internal diameters of the clipped enlarged dyadic cells, proof of
Lemma 11.10, paper lines 3010-3016) from the positivity of the Weyl exponent, the uniform unit-square crossing tail of
`𝔇` (Dubédat-Falconet-Gwynne-Pfeffer-Sun, arXiv:1905.00380v2, Proposition 3.1, p. 13) and the case `0 ∈ S₂`
(`hNear0`; same paper, Proposition 3.17, pp. 43-44). Squares avoiding `0` are
`exists_measurableSet_enlargedDyadicCell_internalMetric_le_of_zero_not_mem`. -/
theorem dyadicCellDiamSmallFrozen_of_unitTail (hXi : LQGMetricExponentPositive)
    (hUniv : ∀ (γ ξ : ℝ) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ), 0 < γ → γ < 2 → IsLQGMetric γ ξ 𝔇 →
      ∃ δ : ℝ, δ < ξ * (lqgQ γ - 2) * Real.log 2 ∧ ∃ p : ℕ → ℝ≥0∞, ∑' n, 4 ^ n * p n ≠ ⊤ ∧
        ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
          IsWholePlaneGFF P hC hcirc → ∀ n : ℕ,
            P {ω | ¬ LatticeProb.LQG.HasShortHalfCrossings (𝔇 (hC ω)) 0 1 0 1
              (ENNReal.ofReal (Real.exp (δ * n)))} ≤ p n)
    (hNear0 : ∀ (γ α₀ ξ : ℝ), 0 < γ → γ < 2 → α₀ < lqgQ γ →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
        (D : Ω → ℂ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc → IsLQGMetricOfField P γ ξ α₀ hC D →
      ∀ S2 : Set ℂ, IsClosedDyadicSquare S2 → Disjoint S2 (Metric.sphere 0 1) → (0 : ℂ) ∈ S2 →
      ∀ ε η : ℝ, 0 < ε → 0 < η →
      ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
        ∃ A ⊆ {ω | ∀ j k : ℤ, closedDyadicSquare (N : ℤ) j k ⊆ S2 →
            ∀ u ∈ enlargedDyadicCell (N : ℤ) j k ∩ S2, ∀ v ∈ enlargedDyadicCell (N : ℤ) j k ∩ S2,
              internalMetric (D ω) (enlargedDyadicCell (N : ℤ) j k ∩ S2) u v ≤ ENNReal.ofReal ε},
          MeasurableSet A ∧ ENNReal.ofReal (1 - η) ≤ P A) :
    DyadicCellDiamSmallFrozen.{u} := by
  intro γ α₀ ξ hγ0 hγ2 hα Ω _ P hC hcirc D hW hD S2 hS2 hdisj ε η hε hη
  by_cases h0 : (0 : ℂ) ∈ S2
  · exact hNear0 γ α₀ ξ hγ0 hγ2 hα Ω P hC hcirc D hW hD S2 hS2 hdisj h0 ε η hε hη
  · exact exists_measurableSet_enlargedDyadicCell_internalMetric_le_of_zero_not_mem hXi hUniv hγ0 hγ2 hW hD hS2 h0
      hε hη

end HarmonicBalls

import HarmonicBalls.FirstPass.Phase2.DyadicCellDiamSmallAwayFromZero
import LatticeProb.LQG.GridRectangleSmallOfSubsquare
import LatticeProb.LQG.InternalMetricWeylScalingCornerDyadic

/-!
# Small internal diameters of the clipped enlarged dyadic cells of a square containing the singularity

Let `D_h = e^{-ξ α₀ log |·|} · D_{h^ℂ}` be the γ-LQG metric of `h = h^ℂ - α₀ log |·|` (`IsLQGMetricOfField`), with
`α₀ < Q`, and let `S₂` be a closed dyadic square with `0 ∈ S₂`. Then `0` is a corner of `S₂`:
`S₂ = [a, a + s] × [b, b + s]` with `s = 2^{-n₀}` and `a, b ∈ {0, -s}`. For `ε, η > 0` there is `N₀` such that for
every `N ≥ N₀`, with probability at least `1 - η` (inner probability), every enlarged dyadic cell
`Ŝ = enlargedDyadicCell N j k` with `closedDyadicSquare N j k ⊆ S₂` satisfies
`sup_{u, v ∈ Ŝ ∩ S₂} D_h(u, v; Ŝ ∩ S₂) ≤ ε`. This is the case `0 ∈ S₂` of `DyadicCellDiamSmallFrozen` (paper, proof of
Lemma 11.10, lines 3010-3016; Dubédat-Falconet-Gwynne-Pfeffer-Sun, arXiv:1905.00380v2, Proposition 3.17, pp. 43-44).

Proof. As in the case `0 ∉ S₂` (`DyadicCellDiamSmallAwayFromZero`), `Ŝ ∩ S₂` is a closed rectangle of at most
`10 × 10` closed dyadic subsquares of `S₂`, and one works on the range space of the model. The small internal diameters
of all closed dyadic subsquares of `S₂` of level `m`, with probability tending to one, is the corner tail `hCorner`
(the statement of `LatticeProb.LQG.IsLQGMetric.tendsto_measure_not_forall_internalMetric_weylScaling_closedDyadicSubsquare_le_of_corner`,
at the Weyl scaling by `-α₀ log |·|`); it passes to grid rectangles by
`LatticeProb.LQG.tendsto_measure_not_forall_internalMetric_gridRectangle_le_of_closedDyadicSubsquare`. The crossing
exponent `δ` of the unit-square tail is raised to a positive `δ' < ξ (Q - 2) log 2` (`HasShortHalfCrossings.mono`).

## Main statements

* `HarmonicBalls.exists_measurableSet_enlargedDyadicCell_internalMetric_le_of_zero_mem`
* `HarmonicBalls.dyadicCellDiamSmallFrozen_of_unitTail_of_corner`: `DyadicCellDiamSmallFrozen` from the positivity of
  the Weyl exponent, the uniform unit-square crossing tail of `𝔇` and the corner tail.
* `HarmonicBalls.dyadicCellDiamSmallFrozen_of_unitTail_derived`: the same, with the corner tail supplied by
  `LatticeProb.LQG.IsLQGMetric.tendsto_measure_not_forall_internalMetric_weylScaling_closedDyadicSubsquare_le_of_corner`.
-/

universe u

namespace HarmonicBalls

open MeasureTheory Filter Set
open scoped ENNReal Topology

/-- If `j s ≤ 0 ≤ j s + s` with `j : ℤ` and `s > 0`, then `j s = 0` or `j s = -s`: a closed dyadic interval containing
`0` has `0` as an endpoint. -/
theorem intCast_mul_eq_zero_or_eq_neg_of_mul_le_zero_le {j : ℤ} {s : ℝ} (hs : 0 < s) (h1 : (j : ℝ) * s ≤ 0)
    (h2 : 0 ≤ (j : ℝ) * s + s) : (j : ℝ) * s = 0 ∨ (j : ℝ) * s = -s := by
  have hj1 : (j : ℝ) ≤ 0 := by
    by_contra h
    exact absurd h1 (not_le.2 (mul_pos (not_le.1 h) hs))
  have hj2 : (-1 : ℝ) ≤ j := by
    by_contra h
    have hneg : ((j : ℝ) + 1) * s < 0 := mul_neg_of_neg_of_pos (by linarith [not_le.1 h]) hs
    have he : ((j : ℝ) + 1) * s = (j : ℝ) * s + s := add_one_mul _ _
    linarith
  have hj1' : j ≤ 0 := by exact_mod_cast hj1
  have hj2' : -1 ≤ j := by exact_mod_cast hj2
  rcases (show j = 0 ∨ j = -1 by omega) with rfl | rfl
  · left
    simp
  · right
    simp

/-- **Derived.** Small internal diameters of the clipped enlarged dyadic cells `Ŝ ∩ S₂`, simultaneously over the cells
of level `N` inside a closed dyadic square `S₂` containing `0`, with probability at least `1 - η` for all large `N`, for
the γ-LQG metric of a whole-plane GFF plus `-α₀ log |·|` with `α₀ < Q`. Inputs: the positivity of the Weyl exponent,
the uniform unit-square crossing tail of `𝔇` (Dubédat-Falconet-Gwynne-Pfeffer-Sun, arXiv:1905.00380v2,
Proposition 3.1, p. 13) and the corner tail `hCorner`, which is the statement of the Lattice-Probability theorem
`LatticeProb.LQG.IsLQGMetric.tendsto_measure_not_forall_internalMetric_weylScaling_closedDyadicSubsquare_le_of_corner`.
The probability space may lie in any universe. -/
theorem exists_measurableSet_enlargedDyadicCell_internalMetric_le_of_zero_mem
    (hXi : LQGMetricExponentPositive)
    (hUniv : ∀ (γ ξ : ℝ) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ), 0 < γ → γ < 2 → IsLQGMetric γ ξ 𝔇 →
      ∃ δ : ℝ, δ < ξ * (lqgQ γ - 2) * Real.log 2 ∧ ∃ p : ℕ → ℝ≥0∞, ∑' n, 4 ^ n * p n ≠ ⊤ ∧
        ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
          IsWholePlaneGFF P hC hcirc → ∀ n : ℕ,
            P {ω | ¬ LatticeProb.LQG.HasShortHalfCrossings (𝔇 (hC ω)) 0 1 0 1
              (ENNReal.ofReal (Real.exp (δ * n)))} ≤ p n)
    (hCorner : ∀ (γ ξ : ℝ) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LatticeProb.LQG.IsLQGMetric γ ξ 𝔇 →
      LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc → 0 < ξ → ∀ θ δ : ℝ,
      θ < ξ * (LatticeProb.LQG.lqgQ γ - 2) * Real.log 2 → δ < θ → 0 < δ → ∀ p : ℕ → ℝ≥0∞,
      (∀ (hC' : Ω → (ℂ → ℝ) → ℝ) (hcirc' : Ω → ℝ → ℂ → ℝ), LatticeProb.Gauss.IsWholePlaneGFF P hC' hcirc' →
        ∀ n : ℕ, P {ω | ¬ LatticeProb.LQG.HasShortHalfCrossings (𝔇 (hC' ω)) 0 1 0 1
          (ENNReal.ofReal (Real.exp (δ * n)))} ≤ p n) →
      ∑' n, 4 ^ n * p n ≠ ⊤ → ∀ α : ℝ, α < LatticeProb.LQG.lqgQ γ → ∀ E : Ω → ℂ → ℂ → ℝ,
      (∀ᵐ ω ∂P, ∀ x y, ENNReal.ofReal (E ω x y) =
        LatticeProb.LQG.weylScaling (𝔇 (hC ω)) ξ (fun w => -α * Real.log ‖w‖) x y) →
      ∀ a b s : ℝ, 0 < s → (a = 0 ∨ a = -s) → (b = 0 ∨ b = -s) → ∀ ε : ℝ, 0 < ε →
      Tendsto (fun m : ℕ => P {ω | ¬ ∀ i j : ℕ, i < 2 ^ m → j < 2 ^ m →
        ∀ z ∈ LatticeProb.LQG.closedDyadicSubsquare a b s m i j,
        ∀ w ∈ LatticeProb.LQG.closedDyadicSubsquare a b s m i j,
          LatticeProb.LQG.internalMetric (E ω) (LatticeProb.LQG.closedDyadicSubsquare a b s m i j) z w ≤
            ENNReal.ofReal ε}) atTop (𝓝 0))
    {γ α₀ ξ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ) {Ω : Type u} [MeasurableSpace Ω]
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {D : Ω → ℂ → ℂ → ℝ}
    (hW : IsWholePlaneGFF P hC hcirc) (hD : IsLQGMetricOfField P γ ξ α₀ hC D)
    {S2 : Set ℂ} (hS2 : IsClosedDyadicSquare S2) (h0 : (0 : ℂ) ∈ S2) {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
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
  -- the crossing exponent `δ' = max δ (K / 2)` is positive and below `K = ξ (Q - 2) log 2`
  have hQ2 : 2 < lqgQ γ := by
    have hsq : 0 < (γ - 2) ^ 2 := sq_pos_of_ne_zero (by linarith)
    unfold lqgQ
    have hcalc : 0 < (γ - 2) ^ 2 / (2 * γ) := div_pos hsq (by positivity)
    field_simp at hcalc ⊢
    nlinarith
  have hK : 0 < ξ * (lqgQ γ - 2) * Real.log 2 :=
    mul_pos (mul_pos hξ (by linarith)) (Real.log_pos one_lt_two)
  set K := ξ * (lqgQ γ - 2) * Real.log 2 with hKdef
  set δ' := max δ (K / 2) with hδ'def
  have hδ'K : δ' < K := max_lt hδ (by linarith)
  have hδ'0 : 0 < δ' := lt_of_lt_of_le (by linarith) (le_max_right δ (K / 2))
  have huniv' : ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') (hC' : Ω' → (ℂ → ℝ) → ℝ)
      (hcirc' : Ω' → ℝ → ℂ → ℝ), IsWholePlaneGFF P' hC' hcirc' → ∀ n : ℕ,
        P' {ω | ¬ LatticeProb.LQG.HasShortHalfCrossings (𝔇 (hC' ω)) 0 1 0 1
          (ENNReal.ofReal (Real.exp (δ' * n)))} ≤ p n := by
    intro Ω' _ P' hC' hcirc' hG n
    have hL : ENNReal.ofReal (Real.exp (δ * n)) ≤ ENNReal.ofReal (Real.exp (δ' * n)) :=
      ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2
        (mul_le_mul_of_nonneg_right (le_max_left δ (K / 2)) (Nat.cast_nonneg n)))
    refine le_trans (measure_mono ?_) (huniv Ω' P' hC' hcirc' hG n)
    exact fun ω hω h => hω (h.mono hL)
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
  have htri : ∀ᵐ y ∂LQGMetricUniv.rangeMeasure P X, ∀ x y' z,
      ENNReal.ofReal (E y x z) ≤ ENNReal.ofReal (E y x y') + ENNReal.ofReal (E y y' z) := by
    filter_upwards [(h𝔇'.ae_isEuclideanLengthMetric_self hW').and hE] with y hy x y' z
    obtain ⟨hDy, hEy⟩ := hy
    rw [hEy, hEy, hEy]
    exact hDy.weylScaling_triangle ξ f x y' z
  have hs : (0 : ℝ) < 2 ^ (-n₀) := zpow_pos two_pos _
  have hSq : closedDyadicSquare n₀ j₂ k₂ =
      Icc ((j₂ : ℝ) * 2 ^ (-n₀)) ((j₂ : ℝ) * 2 ^ (-n₀) + 2 ^ (-n₀)) ×ℂ
        Icc ((k₂ : ℝ) * 2 ^ (-n₀)) ((k₂ : ℝ) * 2 ^ (-n₀) + 2 ^ (-n₀)) := by
    simp only [closedDyadicSquare, add_one_mul]
  -- `0` is a corner of `S₂`
  have h0' := h0
  rw [hSq] at h0'
  simp only [Complex.mem_reProdIm, Complex.zero_re, Complex.zero_im, Set.mem_Icc] at h0'
  have ha := intCast_mul_eq_zero_or_eq_neg_of_mul_le_zero_le hs h0'.1.1 h0'.1.2
  have hb := intCast_mul_eq_zero_or_eq_neg_of_mul_le_zero_le hs h0'.2.1 h0'.2.2
  have hmain := LatticeProb.LQG.tendsto_measure_not_forall_internalMetric_gridRectangle_le_of_closedDyadicSubsquare
    htri hs.le (fun ε' hε' => hCorner γ ξ 𝔇 _ _ _ _ h𝔇' hW' hξ ((δ' + K) / 2) δ' (by rw [← hQQ]; linarith)
      (by linarith) hδ'0 p (fun hC'' hcirc'' hG n => huniv' _ _ hC'' hcirc'' ((LPBridge.isWholePlaneGFF_iff _ _ _).2 hG) n)
      hp α₀ (by rw [← hQQ]; exact hα) E hE _ _ _ hs ha hb ε' hε') 9 hε
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
  obtain ⟨i₀, j₀, K', L, hK', hL, hi, hj, hR⟩ := enlargedDyadicCell_inter_closedDyadicSquare_eq_gridRectangle hsub
  have hEq : E (LQGMetricUniv.toRange P X ω) = D ω := by
    funext u v
    show (weylScaling (𝔇 (hC ω)) ξ f u v).toReal = D ω u v
    rw [← (hω u v).2, ENNReal.toReal_ofReal (hω u v).1]
  rw [hR] at hu hv ⊢
  rw [LPBridge.internalMetric_eq, ← hEq]
  exact hgood i₀ j₀ K' L hK' hL hi hj u hu v hv

/-- **Derived.** `DyadicCellDiamSmallFrozen` (small internal diameters of the clipped enlarged dyadic cells, proof of
Lemma 11.10, paper lines 3010-3016) from the positivity of the Weyl exponent, the uniform unit-square crossing tail of
`𝔇` (Dubédat-Falconet-Gwynne-Pfeffer-Sun, arXiv:1905.00380v2, Proposition 3.1, p. 13) and the corner tail
`hCorner` (the statement of
`LatticeProb.LQG.IsLQGMetric.tendsto_measure_not_forall_internalMetric_weylScaling_closedDyadicSubsquare_le_of_corner`).
Squares avoiding `0` are `exists_measurableSet_enlargedDyadicCell_internalMetric_le_of_zero_not_mem`, squares
containing `0` are `exists_measurableSet_enlargedDyadicCell_internalMetric_le_of_zero_mem`. -/
theorem dyadicCellDiamSmallFrozen_of_unitTail_of_corner (hXi : LQGMetricExponentPositive)
    (hUniv : ∀ (γ ξ : ℝ) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ), 0 < γ → γ < 2 → IsLQGMetric γ ξ 𝔇 →
      ∃ δ : ℝ, δ < ξ * (lqgQ γ - 2) * Real.log 2 ∧ ∃ p : ℕ → ℝ≥0∞, ∑' n, 4 ^ n * p n ≠ ⊤ ∧
        ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
          IsWholePlaneGFF P hC hcirc → ∀ n : ℕ,
            P {ω | ¬ LatticeProb.LQG.HasShortHalfCrossings (𝔇 (hC ω)) 0 1 0 1
              (ENNReal.ofReal (Real.exp (δ * n)))} ≤ p n)
    (hCorner : ∀ (γ ξ : ℝ) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LatticeProb.LQG.IsLQGMetric γ ξ 𝔇 →
      LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc → 0 < ξ → ∀ θ δ : ℝ,
      θ < ξ * (LatticeProb.LQG.lqgQ γ - 2) * Real.log 2 → δ < θ → 0 < δ → ∀ p : ℕ → ℝ≥0∞,
      (∀ (hC' : Ω → (ℂ → ℝ) → ℝ) (hcirc' : Ω → ℝ → ℂ → ℝ), LatticeProb.Gauss.IsWholePlaneGFF P hC' hcirc' →
        ∀ n : ℕ, P {ω | ¬ LatticeProb.LQG.HasShortHalfCrossings (𝔇 (hC' ω)) 0 1 0 1
          (ENNReal.ofReal (Real.exp (δ * n)))} ≤ p n) →
      ∑' n, 4 ^ n * p n ≠ ⊤ → ∀ α : ℝ, α < LatticeProb.LQG.lqgQ γ → ∀ E : Ω → ℂ → ℂ → ℝ,
      (∀ᵐ ω ∂P, ∀ x y, ENNReal.ofReal (E ω x y) =
        LatticeProb.LQG.weylScaling (𝔇 (hC ω)) ξ (fun w => -α * Real.log ‖w‖) x y) →
      ∀ a b s : ℝ, 0 < s → (a = 0 ∨ a = -s) → (b = 0 ∨ b = -s) → ∀ ε : ℝ, 0 < ε →
      Tendsto (fun m : ℕ => P {ω | ¬ ∀ i j : ℕ, i < 2 ^ m → j < 2 ^ m →
        ∀ z ∈ LatticeProb.LQG.closedDyadicSubsquare a b s m i j,
        ∀ w ∈ LatticeProb.LQG.closedDyadicSubsquare a b s m i j,
          LatticeProb.LQG.internalMetric (E ω) (LatticeProb.LQG.closedDyadicSubsquare a b s m i j) z w ≤
            ENNReal.ofReal ε}) atTop (𝓝 0)) :
    DyadicCellDiamSmallFrozen.{u} :=
  dyadicCellDiamSmallFrozen_of_unitTail hXi hUniv
    fun _ _ _ hγ0 hγ2 hα _ _ _ _ _ _ hW hD _ hS2 _ h0 _ _ hε hη =>
      exists_measurableSet_enlargedDyadicCell_internalMetric_le_of_zero_mem hXi hUniv hCorner hγ0 hγ2 hα hW hD hS2
        h0 hε hη

/-- **Derived.** `DyadicCellDiamSmallFrozen` (small internal diameters of the clipped enlarged dyadic cells, proof of
Lemma 11.10, paper lines 3010-3016) from the positivity of the Weyl exponent and the uniform unit-square crossing tail
of `𝔇` (Dubédat-Falconet-Gwynne-Pfeffer-Sun, arXiv:1905.00380v2, Proposition 3.1, p. 13) alone. The corner tail
`hCorner` of `dyadicCellDiamSmallFrozen_of_unitTail_of_corner` is the Lattice-Probability theorem
`LatticeProb.LQG.IsLQGMetric.tendsto_measure_not_forall_internalMetric_weylScaling_closedDyadicSubsquare_le_of_corner`
(DFGPS, Proposition 3.17, pp. 43-44, for the closed dyadic subsquares of a square with the singularity at a corner). -/
theorem dyadicCellDiamSmallFrozen_of_unitTail_derived (hXi : LQGMetricExponentPositive)
    (hUniv : ∀ (γ ξ : ℝ) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ), 0 < γ → γ < 2 → IsLQGMetric γ ξ 𝔇 →
      ∃ δ : ℝ, δ < ξ * (lqgQ γ - 2) * Real.log 2 ∧ ∃ p : ℕ → ℝ≥0∞, ∑' n, 4 ^ n * p n ≠ ⊤ ∧
        ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
          IsWholePlaneGFF P hC hcirc → ∀ n : ℕ,
            P {ω | ¬ LatticeProb.LQG.HasShortHalfCrossings (𝔇 (hC ω)) 0 1 0 1
              (ENNReal.ofReal (Real.exp (δ * n)))} ≤ p n) :
    DyadicCellDiamSmallFrozen.{u} :=
  dyadicCellDiamSmallFrozen_of_unitTail_of_corner hXi hUniv
    fun _ _ _ _ _ _ _ _ h𝔇 hG hξ _ _ hθ hδ hδ0 _ huniv hp _ hα _ hE _ _ _ hs ha hb _ hε =>
      h𝔇.tendsto_measure_not_forall_internalMetric_weylScaling_closedDyadicSubsquare_le_of_corner hG hξ hθ hδ hδ0
        huniv hp hα hE hs ha hb hε

end HarmonicBalls

import HarmonicBalls.FirstPass.S11d.MeasurableExterior
import HarmonicBalls.FirstPass.S11d.ShiftPointwise
import HarmonicBalls.FirstPass.S11d.ShiftFunction
import HarmonicBalls.FirstPass.S11d.ShiftSets
import HarmonicBalls.FirstPass.S11d.ShiftGeometry
import HarmonicBalls.FirstPass.S11d.Dyadic
import HarmonicBalls.FirstPass.Frozen.S11d
import HarmonicBalls.Proposed.LQG
import HarmonicBalls.Draft.Section11
import HarmonicBalls.Proofs.GFF.MetricXiSign

universe u

/-!
# Proposition 11.9, the shifted event with positive probability (fp-S11d, owner n3)

FIRST-PASS NEW (assembly R2). For the Draft statement `SmallMetricDiameterLargeMassStmt` (paper `prop:mass-diam-gen`,
corrected draft lines 3110-3137), the shifted field `h~ = h - (φ/ξ) log(2(n+ε)/ε)` has, with positive probability, the
metric bound `E(·,·; W) ≤ ε` on `V` together with `μ_h(S₁) ≥ C`. The unshifted field `h` enters only through the 11.10 event
(`SmallMetricDiameterLargeMassSquareStmt`), the exterior event (Fact 2.2 II, Proposed `LQGMetricFieldAxioms`), and the frozen
Fact 2.2 I for the shift (`LQGMetricContinuousShiftFactI`); the plane topology enters through the frozen
`PlaneDomainMinusConvexCompactPreconnectedFrozen`. The positive-probability transfer back to `h` is the next step (R3).

Caveat (open decision, see notes): the shift `g = -(c/ξ) φ` needs `ξ ≠ 0`; this file assumes `0 < ξ`.
-/

namespace HarmonicBalls

open Set MeasureTheory Filter Topology
open scoped ENNReal

/-- A closed dyadic square is nonempty. -/
theorem closedDyadicSquare_nonempty (n j k : ℤ) : (closedDyadicSquare n j k).Nonempty := by
  have hs : (0 : ℝ) ≤ (2 : ℝ) ^ (-n) := by positivity
  unfold closedDyadicSquare
  refine ⟨⟨(j : ℝ) * (2 : ℝ) ^ (-n), (k : ℝ) * (2 : ℝ) ^ (-n)⟩, ⟨⟨le_refl _, ?_⟩, ⟨le_refl _, ?_⟩⟩⟩
  · nlinarith
  · nlinarith

/-- **The shifted event has positive probability** (paper proof of `prop:mass-diam-gen`, lines 3120-3131, before the
transfer back to `h`). For the smooth shift `g = -(c/ξ) φ` the metric of `h + g - α₀ log|·|` is at most `ε` on `V` on an
event of positive probability on which `μ_h(S₁) ≥ C`. -/
theorem shifted_event_exists
    {γ ξ α₀ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} {D : Ω → ℂ → ℂ → ℝ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hD : IsLQGMetricOfField P γ ξ α₀ hC D)
    (hAx : LQGMetricFieldAxioms P γ ξ α₀ hC hcirc)
    (hShift : LQGMetricContinuousShiftFactI.{u})
    (hFD : PlaneDomainMinusConvexCompactPreconnectedFrozen)
    (h1110 : SmallMetricDiameterLargeMassSquareStmt.{u})
    {U V W : Set ℂ} (hUo : IsOpen U) (hUc : IsConnected U)
    (hVo : IsOpen V) (hVc : IsConnected V) (hVb : Bornology.IsBounded V)
    (hWo : IsOpen W) (hWb : Bornology.IsBounded W)
    (hUV : U ⊆ V) (hVW : V ⊆ W) (hcl : closure V ⊆ W) (hWs : Disjoint W (Metric.sphere (0 : ℂ) 1))
    {C ε : ℝ} (hε : 0 < ε) (hεC : ε < C) :
    ∃ 𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ, IsLQGMetric γ ξ 𝔇 ∧
      (∀ᵐ ω ∂P, D ω = fun u v => (weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v).toReal) ∧
      ∃ g : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g ∧ Real.circleAverage g 0 1 = 0 ∧
        ∃ S₁ : Set ℂ, IsClosed S₁ ∧ (∀ z ∈ S₁, g z = 0) ∧ S₁ ⊆ U ∧ ∃ A : Set Ω, MeasurableSet A ∧ 0 < P A ∧
          ∀ ω ∈ A, (∀ u ∈ V, ∀ v ∈ V,
            internalMetric (fun x y => (weylScaling (𝔇 (hC ω)) ξ (fun z => g z - α₀ * Real.log ‖z‖) x y).toReal)
              W u v ≤ ENNReal.ofReal ε) ∧ ENNReal.ofReal C ≤ μ ω S₁ := by
  have : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  have hD2 := hD
  obtain ⟨𝔇, h𝔇, hDae⟩ := hD
  have hξ : 0 < ξ := IsLQGMetric.weylExponent_pos h𝔇 hγ0
  obtain ⟨hI, hII, hIII, -⟩ := hAx hGFF hγ0 hγ2 hα 𝔇 h𝔇
  obtain ⟨x, hx⟩ := hUc.nonempty
  obtain ⟨S1, S2, hS1, hS2, hS1S2, hS2U⟩ := exists_closedDyadicSquare_pair hUo hx
  have hS1S2' : S1 ⊆ S2 := hS1S2.trans interior_subset
  have hS2V : S2 ⊆ V := hS2U.trans hUV
  have hS2W : S2 ⊆ W := hS2V.trans hVW
  have hdisj : Disjoint S2 (Metric.sphere (0 : ℂ) 1) := hWs.mono_left hS2W
  obtain ⟨A0, hA0sub, hA0m, hA0p⟩ :=
    h1110 γ α₀ ξ hγ0 hγ2 hα Ω P hC hcirc μ D hGFF hμ hD2 S1 S2 hS1 hS2 hS1S2' hdisj C (ε / 2)
      (by positivity) (by linarith)
  obtain ⟨O, φ, hOo, hKO, hclO, hφs, hφc, hφsup, hφ01, hφ1⟩ :=
    shift_geometry hVb hWo hWb hcl hS1 hS2 hS1S2
  have hS2c : IsClosed S2 := isClosed_of_isClosedDyadicSquare hS2
  have hS2comp : IsCompact S2 := by
    obtain ⟨n', j, k, h⟩ := hS2
    rw [h]
    exact isCompact_closedDyadicSquare_of n' j k
  have hS2conv : Convex ℝ S2 := by
    obtain ⟨n', j, k, h⟩ := hS2
    rw [h]
    exact convex_closedDyadicSquare n' j k
  have hS2ne : S2.Nonempty := by
    obtain ⟨n', j, k, h⟩ := hS2
    rw [h]
    exact closedDyadicSquare_nonempty n' j k
  have hA : IsOpen (V \ S2) := hVo.sdiff hS2c
  have hAc : IsPreconnected (V \ S2) := hFD V S2 hVo hVc hS2comp hS2conv hS2V
  have hKc : IsCompact (closure (V \ S2)) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure (hVb.subset sdiff_subset).closure
  have hGO : ∃ G : Ω → ℂ → ℂ → ℝ≥0∞, (∀ z w, Measurable fun ω => G ω z w) ∧
      ∀ᵐ ω ∂P, ∀ z ∈ O, ∀ w ∈ O,
        internalMetric (fun u v => (weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v).toReal) O z w
          = G ω z w := by
    obtain ⟨G, hGm, hGae⟩ := hII O hOo
    exact ⟨G, fun z w => (hGm z w).mono (fieldSigmaAlgebra_le (α₀ := α₀) hGFF O) le_rfl, hGae⟩
  have hIlen : ∀ᵐ ω ∂P, IsEuclideanLengthMetric
      (fun u v => (weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v).toReal) :=
    hI.mono fun ω h => h.2
  obtain ⟨n, Bx, hBxm, hBxsub, hBxp, hBxb⟩ :=
    exists_measurable_exterior_bound
      (Dr := fun ω u v => (weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v).toReal)
      (fun ω x y => ENNReal.toReal_nonneg) hIlen hOo hA hAc hKO hKc hGO hA0m hA0p
  obtain ⟨hc0, hexp⟩ := shift_constants hε (Nat.cast_nonneg (α := ℝ) n)
  set c : ℝ := Real.log (2 * ((n : ℝ) + ε) / ε) with hc
  set g : ℂ → ℝ := fun z => -(c / ξ) * φ z with hg
  have hgs : ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g := shift_smooth_compact hφs hφc
  have hzero : ∀ z ∈ Metric.sphere (0 : ℂ) 1, φ z = 0 := fun z hz =>
    image_eq_zero_of_notMem_tsupport (fun h => Set.disjoint_left.mp hWs (hφsup h).1 hz)
  have hcirc0 : Real.circleAverage g 0 1 = 0 := shift_circleAverage_zero hzero
  have hweightO : ∀ z ∈ O, ξ * g z ≤ -c := fun z hz => le_of_eq (by
    show ξ * (-(c / ξ) * φ z) = -c
    rw [shift_weight_eq hξ.ne' z, hφ1 z hz, mul_one])
  obtain ⟨U', hU'o, hS2U', hclU'⟩ := exists_open_between_of_compact hS2comp hWo hS2W
  have hU'W : U' ⊆ W := subset_closure.trans hclU'
  have hOW : O ⊆ W := subset_closure.trans (hclO.trans sdiff_subset)
  have hweightU : ∀ z ∈ U', ξ * g z ≤ 0 := fun z _ => by
    show ξ * (-(c / ξ) * φ z) ≤ 0
    exact shift_weight_le hξ.ne' hc0 (fun z => (hφ01 z).1) z
  have hEae := hShift γ ξ α₀ Ω P hC hcirc hGFF hγ0 hγ2 hα 𝔇 h𝔇 g hgs.1.continuous
  have hIIIg := hIII.mono fun ω h => h g hgs.1.continuous
  have hDeq : ∀ᵐ ω ∂P, D ω = fun u v => (weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v).toReal := by
    filter_upwards [hDae] with ω hω
    funext u v
    obtain ⟨h0, hof⟩ := hω u v
    rw [← hof, ENNReal.toReal_ofReal h0]
  have hgood : ∀ᵐ ω ∂P,
      IsEuclideanLengthMetric
        (fun u v => (weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v).toReal) ∧
      IsEuclideanLengthMetric
        (fun u v => (weylScaling (𝔇 (hC ω)) ξ (fun x => g x - α₀ * Real.log ‖x‖) u v).toReal) ∧
      (∀ x y, ENNReal.ofReal
          ((fun u v => (weylScaling (𝔇 (hC ω)) ξ (fun x => g x - α₀ * Real.log ‖x‖) u v).toReal) x y)
          = weylScaling
              (fun u v => (weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v).toReal) ξ g x y) ∧
      D ω = fun u v => (weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v).toReal := by
    filter_upwards [hIlen, hEae, hIIIg, hDeq] with ω h1 h2 h3 h4
    refine ⟨h1, h2.2, fun x y => ?_, h4⟩
    exact (ENNReal.ofReal_toReal (ne_top_of_lt (h2.1 x y))).trans (h3 x y)
  obtain ⟨B', hB'm, hB'sub, hB'good, hB'P⟩ := exists_measurable_subset_of_ae hBxm _ hgood
  have hS1c : IsClosed S1 := isClosed_of_isClosedDyadicSquare hS1
  have hS1U : S1 ⊆ U := hS1S2'.trans hS2U
  have hφ0 : ∀ z ∈ S1, φ z = 0 := fun z hz =>
    image_eq_zero_of_notMem_tsupport (fun h => (hφsup h).2 hz)
  have hg0S1 : ∀ z ∈ S1, g z = 0 := fun z hz => by simp [hg, hφ0 z hz]
  refine ⟨𝔇, h𝔇, hDeq, g, hgs.1, hgs.2, hcirc0, S1, hS1c, hg0S1, hS1U, B', hB'm, ?_, ?_⟩
  · rw [hB'P]
    exact hBxp
  · intro ω hω
    obtain ⟨h1, h2, h3, h4⟩ := hB'good ω hω
    have hBx : ω ∈ Bx := hB'sub hω
    obtain ⟨hA0S2, hmass⟩ := hA0sub (hBxsub hBx)
    rw [h4] at hA0S2
    have hDS : ∀ u ∈ S2, ∀ v ∈ S2,
        internalMetric (fun u v => (weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v).toReal) S2 u v
          ≤ ENNReal.ofReal (ε / 2) := hA0S2
    have hDO : ∀ u ∈ V \ S2, ∀ v ∈ V \ S2,
        internalMetric (fun u v => (weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v).toReal) O u v
          ≤ ENNReal.ofReal (n : ℝ) := fun u hu v hv => by
      rw [ENNReal.ofReal_natCast]
      exact hBxb ω hBx u hu v hv
    have hE' := shifted_event_pointwise h1 h2 (fun x y => ENNReal.toReal_nonneg) h3 hε.le hVo hVc hS2c hS2V
      hS2ne hOo hKO hOW hU'o hS2U' hU'W hweightU hweightO hexp hDS hDO
    exact ⟨hE', hmass⟩

end HarmonicBalls

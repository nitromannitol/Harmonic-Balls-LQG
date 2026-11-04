import HarmonicBalls.Proofs.Sec6.BrownianUnitIncrements
import HarmonicBalls.Proofs.Sec6.GreenPotentialHittingLimit

/-!
# Compact hitting and stopped potentials

A bounded nonnegative potential vanishing outside a bounded open domain gives a
compact hitting bound once its stopped harmonic representation is available.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Set Filter MarkovProcess Metric
open scoped ENNReal NNReal Topology

/-- Exit from a bounded planar domain occurs in finite time almost surely. -/
theorem ae_planarBrownian_exitTime_bounded_lt_top (x : ℂ) {U : Set ℂ}
    (hU : Bornology.IsBounded U) :
    ∀ᵐ ω ∂(planarBrownianMotion x), ContinuousPath.exitTime U ω < ∞ := by
  obtain ⟨R, hR⟩ := hU.subset_ball x
  filter_upwards [ae_planarBrownianMotion_exitTime_ball_lt_top x R] with ω hω
  exact lt_of_le_of_lt (ContinuousPath.exitTime_mono hR ω) hω

/-- A finite exit from an open set lands outside it, also when the path starts
outside the set. -/
theorem coordinate_exitTime_notMem {U : Set ℂ} (hU : IsOpen U)
    (ω : ContinuousPath ℂ) (hfin : ContinuousPath.exitTime U ω ≠ ∞) :
    ω ((ContinuousPath.exitTime U ω).toNNReal) ∉ U := by
  by_cases h0 : ω 0 ∈ U
  · exact (hU.frontier_eq ▸ ContinuousPath.coordinate_exitTime_mem_frontier U hU ω h0 hfin).2
  · have ht : ContinuousPath.exitTime U ω = 0 := le_antisymm (by
      simpa using ContinuousPath.exitTime_le_of_notMem U ω 0 h0) bot_le
    simpa [ht] using h0

/-- On finite exit from a punctured domain, a stopped point in the compact
obstacle certifies that the obstacle was reached before leaving the domain. -/
theorem hitting_before_exit_of_stopped_mem {U L : Set ℂ} (ω : ContinuousPath ℂ)
    (hfin : ContinuousPath.exitTime (U \ L) ω ≠ ∞)
    (hmem : ω ((ContinuousPath.exitTime (U \ L) ω).toNNReal) ∈ L) :
    ContinuousPath.exitTime Lᶜ ω ≤ ContinuousPath.exitTime U ω := by
  have hle := ContinuousPath.exitTime_le_of_notMem Lᶜ ω
    ((ContinuousPath.exitTime (U \ L) ω).toNNReal) (by simpa using hmem)
  rw [ENNReal.coe_toNNReal hfin] at hle
  exact hle.trans (ContinuousPath.exitTime_mono sdiff_subset ω)

/-- A stopped-potential representation implies the compact hitting estimate.
The representation is left as a hypothesis for the subsequent harmonicity and
optional-stopping proof. -/
theorem compact_hitting_of_stopped_potential
    {U L : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hL : IsCompact L) (q : ℂ → ℝ) {M : ℝ} (hM : 0 < M)
    (hqzero : ∀ y ∉ U, q y = 0) (hqbound : ∀ y, q y ≤ M) (x : ℂ)
    (hrep : ENNReal.ofReal (q x) ≤ ∫⁻ ω,
      ENNReal.ofReal (q (ω ((ContinuousPath.exitTime (U \ L) ω).toNNReal)))
        ∂(planarBrownianMotion x)) :
    ENNReal.ofReal (q x / M) ≤ planarBrownianMotion x
      {ω | ContinuousPath.exitTime Lᶜ ω ≤ ContinuousPath.exitTime U ω} := by
  let A : Set (ContinuousPath ℂ) :=
    {ω | ContinuousPath.exitTime Lᶜ ω ≤ ContinuousPath.exitTime U ω}
  have hDopen : IsOpen (U \ L) := hU.sdiff hL.isClosed
  have hfin := ae_planarBrownian_exitTime_bounded_lt_top x
    (U := U \ L) (hUb.subset sdiff_subset)
  have hpoint : ∀ᵐ ω ∂(planarBrownianMotion x),
      ENNReal.ofReal (q (ω ((ContinuousPath.exitTime (U \ L) ω).toNNReal))) ≤
        A.indicator (fun _ => ENNReal.ofReal M) ω := by
    filter_upwards [hfin] with ω hω
    by_cases hA : ω ∈ A
    · simp only [indicator_of_mem hA]
      exact ENNReal.ofReal_le_ofReal (hqbound _)
    · have hout : ω ((ContinuousPath.exitTime (U \ L) ω).toNNReal) ∉ U := by
        have hnot := coordinate_exitTime_notMem hDopen ω (ne_top_of_lt hω)
        have hnL : ω ((ContinuousPath.exitTime (U \ L) ω).toNNReal) ∉ L := by
          intro hLmem
          exact hA (hitting_before_exit_of_stopped_mem ω (ne_top_of_lt hω) hLmem)
        intro hmem
        exact hnot ⟨hmem, hnL⟩
      simp [indicator_of_notMem hA, hqzero _ hout]
  rw [ENNReal.ofReal_div_of_pos hM]
  apply (ENNReal.div_le_iff (ENNReal.ofReal_pos.mpr hM).ne' ENNReal.ofReal_ne_top).2
  calc
    ENNReal.ofReal (q x) ≤ ∫⁻ ω,
        ENNReal.ofReal (q (ω ((ContinuousPath.exitTime (U \ L) ω).toNNReal)))
          ∂(planarBrownianMotion x) := hrep
    _ ≤ ∫⁻ ω, A.indicator (fun _ => ENNReal.ofReal M) ω ∂(planarBrownianMotion x) :=
      lintegral_mono_ae hpoint
    _ ≤ ENNReal.ofReal M * planarBrownianMotion x A := lintegral_indicator_const_le A _
    _ = planarBrownianMotion x A * ENNReal.ofReal M := mul_comm _ _


/-- A Green potential restricted to a subset of a bounded domain is bounded
above by the full Green potential when the kernel is integrable. -/
theorem restricted_greenPotential_le {μ : Measure ℂ} {U L : Set ℂ}
    (hUb : Bornology.IsBounded U) (hLU : L ⊆ U)
    (hint : ∀ x ∈ U, IntegrableOn (greenFunction U x) U μ) (x : ℂ) :
    (∫ y in L, greenFunction U x y ∂μ) ≤ greenPotential U μ x := by
  by_cases hx : x ∈ U
  · have hle := setIntegral_mono_set (hint x hx)
      (Filter.Eventually.of_forall (fun y => greenFunction_nonneg hUb x y)) hLU.eventuallySubset
    have heq : (∫ y in U, greenFunction U x y ∂μ) = greenPotential U μ x :=
      setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun y hy => greenFunction_of_notMem_right hy x)
    exact heq ▸ hle
  · simp only [greenFunction_of_notMem_left hx, greenPotential, integral_zero, le_refl]

/-- The compact Green-potential hitting estimate follows from its stopped
representation and an upper bound on the full potential. -/
theorem compact_greenPotential_hitting_of_stopped_representation
    {μ : Measure ℂ} {U L : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hL : IsCompact L) (hLU : L ⊆ U) {M : ℝ} (hM : 0 < M)
    (hint : ∀ x ∈ U, IntegrableOn (greenFunction U x) U μ)
    (hbound : ∀ x, greenPotential U μ x ≤ M) (x : ℂ)
    (hrep : ENNReal.ofReal (∫ y in L, greenFunction U x y ∂μ) ≤ ∫⁻ ω,
      ENNReal.ofReal (∫ y in L,
        greenFunction U (ω ((ContinuousPath.exitTime (U \ L) ω).toNNReal)) y ∂μ)
          ∂(planarBrownianMotion x)) :
    ENNReal.ofReal ((∫ y in L, greenFunction U x y ∂μ) / M) ≤ planarBrownianMotion x
      {ω | ContinuousPath.exitTime Lᶜ ω ≤ ContinuousPath.exitTime U ω} := by
  apply compact_hitting_of_stopped_potential hU hUb hL
    (fun z => ∫ y in L, greenFunction U z y ∂μ) hM ?_ ?_ x hrep
  · intro z hz
    simp only [greenFunction_of_notMem_left hz, integral_zero]
  · intro z
    exact (restricted_greenPotential_le hUb hLU hint z).trans (hbound z)


/-- The real value of a finite positive potential supremum supplies the bound
and denominator in the compact hitting estimate. -/
theorem compact_greenPotential_hitting_of_stopped_representation_sup
    {μ : Measure ℂ} {U L : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hL : IsCompact L) (hLU : L ⊆ U)
    (hint : ∀ x ∈ U, IntegrableOn (greenFunction U x) U μ)
    (hsup0 : (⨆ y : U, ENNReal.ofReal (greenPotential U μ y)) ≠ 0)
    (hsuptop : (⨆ y : U, ENNReal.ofReal (greenPotential U μ y)) ≠ ∞) (x : ℂ)
    (hrep : ENNReal.ofReal (∫ y in L, greenFunction U x y ∂μ) ≤ ∫⁻ ω,
      ENNReal.ofReal (∫ y in L,
        greenFunction U (ω ((ContinuousPath.exitTime (U \ L) ω).toNNReal)) y ∂μ)
          ∂(planarBrownianMotion x)) :
    ENNReal.ofReal ((∫ y in L, greenFunction U x y ∂μ) /
      (⨆ y : U, ENNReal.ofReal (greenPotential U μ y)).toReal) ≤
      planarBrownianMotion x
        {ω | ContinuousPath.exitTime Lᶜ ω ≤ ContinuousPath.exitTime U ω} := by
  have hM : 0 < (⨆ y : U, ENNReal.ofReal (greenPotential U μ y)).toReal :=
    ENNReal.toReal_pos hsup0 hsuptop
  apply compact_greenPotential_hitting_of_stopped_representation hU hUb hL hLU hM hint ?_ x hrep
  intro z
  by_cases hz : z ∈ U
  · have hle := ENNReal.toReal_mono hsuptop
      (le_iSup (fun y : U => ENNReal.ofReal (greenPotential U μ y)) ⟨z, hz⟩)
    simpa only [ENNReal.toReal_ofReal (greenPotential_nonneg hUb μ z)] using hle
  · have hz0 : greenPotential U μ z = 0 := by
      simp only [greenPotential, greenFunction_of_notMem_left hz, integral_zero]
    rw [hz0]
    exact ENNReal.toReal_nonneg


/-- Stopped Green-potential representations imply the extrema-ratio hitting
bound for a full-mass increasing compact union. -/
theorem greenPotentialExtremaRatio_hitting_union_of_stopped_representation
    {μ : Measure ℂ} {U S : Set ℂ} {K : ℕ → Set ℂ}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hS : IsCompact S) (hSU : S ⊆ closure U)
    (hK : ∀ n, IsCompact (K n)) (hKmono : Monotone K)
    (hfull : μ (U \ ⋃ n, K n) = 0)
    (hholder : ∀ f : ℂ → ℝ, MemLp f ⊤ (μ.restrict (closure U)) →
      (∀ x ∈ closure U, IntegrableOn (fun y => greenFunction U x y * f y) U μ) ∧
      ∃ C t : ℝ≥0, 0 < t ∧
        HolderOnWith C t (fun x => ∫ y in U, greenFunction U x y * f y ∂μ) (closure U))
    (hsup0 : (⨆ y : U, ENNReal.ofReal (greenPotential U μ y)) ≠ 0)
    (hsuptop : (⨆ y : U, ENNReal.ofReal (greenPotential U μ y)) ≠ ∞)
    (hrep : ∀ L : Set ℂ, IsCompact L → L ⊆ U → ∀ x ∈ S,
      ENNReal.ofReal (∫ y in L, greenFunction U x y ∂μ) ≤ ∫⁻ ω,
        ENNReal.ofReal (∫ y in L,
          greenFunction U (ω ((ContinuousPath.exitTime (U \ L) ω).toNNReal)) y ∂μ)
            ∂(planarBrownianMotion x)) :
    ∀ x ∈ S, ENNReal.ofReal (greenPotentialExtremaRatio U S μ) ≤
      planarBrownianMotion x {ω | ContinuousPath.exitTime (⋃ n, K n)ᶜ ω ≤
        ContinuousPath.exitTime U ω} := by
  apply greenPotentialExtremaRatio_hitting_union_of_compact_hitting
    hU hUb hS hSU hK hKmono hfull hholder
  intro L hL hLU x hx
  obtain ⟨hint, _⟩ := hholder (fun _ => 1) (memLp_top_const (1 : ℝ))
  apply compact_greenPotential_hitting_of_stopped_representation_sup hU hUb hL hLU ?_
    hsup0 hsuptop x (hrep L hL hLU x hx)
  intro y hy
  simpa only [mul_one] using hint y (subset_closure hy)

end HarmonicBalls.Section6

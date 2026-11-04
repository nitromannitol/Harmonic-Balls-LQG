import HarmonicBalls.Proofs.Sec6.CompactHittingStopping

/-!
# Reduction of the stopped Green-potential representation

A positive extrema ratio gives a finite positive potential supremum. If Brownian
motion starts inside the compact obstacle, the stopped representation is immediate.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Set Filter MarkovProcess Metric
open scoped ENNReal NNReal Topology

/-- A real stopped-potential inequality implies the nonnegative integral
inequality used for the hitting estimate. -/
theorem stopped_lintegral_representation_of_integral_representation
    (U L : Set ℂ) (q : ℂ → ℝ) (x : ℂ) (hq : ∀ y, 0 ≤ q y)
    (hint : Integrable (fun ω : ContinuousPath ℂ =>
      q (ω ((ContinuousPath.exitTime (U \ L) ω).toNNReal))) (planarBrownianMotion x))
    (hrep : q x ≤ ∫ ω, q (ω ((ContinuousPath.exitTime (U \ L) ω).toNNReal))
      ∂(planarBrownianMotion x)) :
    ENNReal.ofReal (q x) ≤ ∫⁻ ω,
      ENNReal.ofReal (q (ω ((ContinuousPath.exitTime (U \ L) ω).toNNReal)))
        ∂(planarBrownianMotion x) := by
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun ω => hq _)]
  exact ENNReal.ofReal_le_ofReal hrep

/-- A positive real extrema ratio forces its extended-real denominator to be
both nonzero and finite. -/
theorem greenPotential_sup_ne_zero_and_top_of_ratio_pos
    {μ : Measure ℂ} {U S : Set ℂ} (hpos : 0 < greenPotentialExtremaRatio U S μ) :
    (⨆ y : U, ENNReal.ofReal (greenPotential U μ y)) ≠ 0 ∧
    (⨆ y : U, ENNReal.ofReal (greenPotential U μ y)) ≠ ∞ := by
  apply ENNReal.toReal_ne_zero.mp
  intro hzero
  unfold greenPotentialExtremaRatio at hpos
  rw [ENNReal.toReal_div, hzero, div_zero] at hpos
  exact lt_irrefl _ hpos

/-- If the start lies in the obstacle, the exit time from the punctured domain
is zero and the stopped representation holds with equality. -/
theorem stopped_representation_of_mem_obstacle
    (U L : Set ℂ) (q : ℂ → ℝ) {x : ℂ} (hx : x ∈ L) :
    ENNReal.ofReal (q x) = ∫⁻ ω,
      ENNReal.ofReal (q (ω ((ContinuousPath.exitTime (U \ L) ω).toNNReal)))
        ∂(planarBrownianMotion x) := by
  have hae : (fun ω : ContinuousPath ℂ =>
      ENNReal.ofReal (q (ω ((ContinuousPath.exitTime (U \ L) ω).toNNReal)))) =ᵐ[
        planarBrownianMotion x] fun _ => ENNReal.ofReal (q x) := by
    filter_upwards [ae_planarBrownianMotion_eval_zero x] with ω h0
    have hnot : ω 0 ∉ U \ L := by simp [h0, hx]
    have ht : ContinuousPath.exitTime (U \ L) ω = 0 := le_antisymm (by
      simpa using ContinuousPath.exitTime_le_of_notMem (U \ L) ω 0 hnot) bot_le
    simp [ht, h0]
  rw [lintegral_congr_ae hae, lintegral_const]
  simp

/-- With a positive extrema ratio, the stopped representation is needed only
for starts in the complement of the compact obstacle. -/
theorem greenPotentialExtremaRatio_hitting_union_of_stopped_representation_off_obstacle
    {μ : Measure ℂ} {U S : Set ℂ} {K : ℕ → Set ℂ}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hS : IsCompact S) (hSU : S ⊆ closure U)
    (hK : ∀ n, IsCompact (K n)) (hKmono : Monotone K)
    (hfull : μ (U \ ⋃ n, K n) = 0)
    (hholder : ∀ f : ℂ → ℝ, MemLp f ⊤ (μ.restrict (closure U)) →
      (∀ x ∈ closure U, IntegrableOn (fun y => greenFunction U x y * f y) U μ) ∧
      ∃ C t : ℝ≥0, 0 < t ∧
        HolderOnWith C t (fun x => ∫ y in U, greenFunction U x y * f y ∂μ) (closure U))
    (hpos : 0 < greenPotentialExtremaRatio U S μ)
    (hrep : ∀ L : Set ℂ, IsCompact L → L ⊆ U → ∀ x ∈ S, x ∉ L →
      ENNReal.ofReal (∫ y in L, greenFunction U x y ∂μ) ≤ ∫⁻ ω,
        ENNReal.ofReal (∫ y in L,
          greenFunction U (ω ((ContinuousPath.exitTime (U \ L) ω).toNNReal)) y ∂μ)
            ∂(planarBrownianMotion x)) :
    ∀ x ∈ S, ENNReal.ofReal (greenPotentialExtremaRatio U S μ) ≤
      planarBrownianMotion x {ω | ContinuousPath.exitTime (⋃ n, K n)ᶜ ω ≤
        ContinuousPath.exitTime U ω} := by
  obtain ⟨hsup0, hsuptop⟩ := greenPotential_sup_ne_zero_and_top_of_ratio_pos hpos
  apply greenPotentialExtremaRatio_hitting_union_of_stopped_representation
    hU hUb hS hSU hK hKmono hfull hholder hsup0 hsuptop
  intro L hL hLU x hx
  by_cases hmem : x ∈ L
  · exact (stopped_representation_of_mem_obstacle U L
      (fun z => ∫ y in L, greenFunction U z y ∂μ) hmem).le
  · exact hrep L hL hLU x hx hmem


/-- The fine-support circle hitting bound follows from the local stopped
representation, the positive ratio and the Green-potential Hölder property. -/
theorem fineSupport_circle_hitting_union_of_stopped_representation
    {μ : Measure ℂ} {c : ℂ} {r ε : ℝ} (hr : 0 < r) (hrε : r ≤ ε)
    {K : ℕ → Set ℂ} (hK : ∀ n, IsCompact (K n)) (hKmono : Monotone K)
    (hfull : μ (ball c ε \ ⋃ n, K n) = 0)
    (hholder : ∀ O : Set ℂ, IsSmoothBoundedOpen O → ∀ f : ℂ → ℝ,
      MemLp f ⊤ (μ.restrict (closure O)) →
      (∀ x ∈ closure O, IntegrableOn (fun y => greenFunction O x y * f y) O μ) ∧
      ∃ C t : ℝ≥0, 0 < t ∧
        HolderOnWith C t (fun x => ∫ y in O, greenFunction O x y * f y ∂μ) (closure O))
    (hpos : 0 < greenPotentialExtremaRatio (fineSupportAnnulus c r) (sphere c (r / 4)) μ)
    (hrep : ∀ L : Set ℂ, IsCompact L → L ⊆ fineSupportAnnulus c r →
      ∀ x ∈ sphere c (r / 4), x ∉ L →
      ENNReal.ofReal (∫ y in L, greenFunction (fineSupportAnnulus c r) x y ∂μ) ≤ ∫⁻ ω,
        ENNReal.ofReal (∫ y in L, greenFunction (fineSupportAnnulus c r)
          (ω ((ContinuousPath.exitTime (fineSupportAnnulus c r \ L) ω).toNNReal)) y ∂μ)
            ∂(planarBrownianMotion x)) :
    ∀ x ∈ sphere c (r / 4),
      ENNReal.ofReal (greenPotentialExtremaRatio (fineSupportAnnulus c r)
        (sphere c (r / 4)) μ) ≤
      planarBrownianMotion x {ω | ContinuousPath.exitTime (⋃ n, K n)ᶜ ω ≤
        ContinuousPath.exitTime (ball c r) ω} := by
  obtain ⟨hO, hS, _, hSO, _⟩ := fineSupportAnnulus_geometry c hr
  have hopen : IsOpen (fineSupportAnnulus c r) := by
    obtain ⟨ρ, hρ, hEq, _⟩ := hO.2
    rw [hEq]
    exact isOpen_lt hρ.continuous continuous_const
  have hsub : fineSupportAnnulus c r ⊆ ball c ε := by
    intro z hz
    rw [mem_ball, dist_eq_norm]
    exact lt_of_lt_of_le hz.2 hrε
  have hratio := greenPotentialExtremaRatio_hitting_union_of_stopped_representation_off_obstacle
    hopen hO.1 hS (hSO.trans subset_closure) hK hKmono
    (measure_mono_null (sdiff_subset_sdiff_left hsub) hfull) (hholder _ hO) hpos hrep
  intro x hx
  exact (hratio x hx).trans (fineSupport_hitting_annulus_le_hitting_ball c x r (⋃ n, K n))


universe u

/-- The LQG regularity and full-support hypotheses supply the positive ratio
and Hölder assumptions simultaneously for all fine-support annuli. -/
theorem ae_fineSupport_circle_hitting_union_of_stopped_representation
    (hholder : GreenPotentialHolderStmt.{u}) (hfull : LQGMeasureFullSupportStmt.{u})
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hnonatom : LQGMeasureNonatomic P γ α₀ hC hcirc)
    (hrep : ∀ᵐ sample ∂P, ∀ c : ℂ, ∀ r : ℝ, 0 < r →
      ∀ L : Set ℂ, IsCompact L → L ⊆ fineSupportAnnulus c r →
      ∀ x ∈ sphere c (r / 4), x ∉ L →
      ENNReal.ofReal (∫ y in L, greenFunction (fineSupportAnnulus c r) x y ∂(μ sample)) ≤ ∫⁻ ω,
        ENNReal.ofReal (∫ y in L, greenFunction (fineSupportAnnulus c r)
          (ω ((ContinuousPath.exitTime (fineSupportAnnulus c r \ L) ω).toNNReal)) y ∂(μ sample))
            ∂(planarBrownianMotion x)) :
    ∀ᵐ sample ∂P, ∀ c : ℂ, ∀ r ε : ℝ, 0 < r → r ≤ ε →
      ∀ K : ℕ → Set ℂ, (∀ n, IsCompact (K n)) → Monotone K →
      (μ sample) (ball c ε \ ⋃ n, K n) = 0 → ∀ x ∈ sphere c (r / 4),
      ENNReal.ofReal (greenPotentialExtremaRatio (fineSupportAnnulus c r)
        (sphere c (r / 4)) (μ sample)) ≤
      planarBrownianMotion x {ω | ContinuousPath.exitTime (⋃ n, K n)ᶜ ω ≤
        ContinuousPath.exitTime (ball c r) ω} := by
  filter_upwards [ae_fineSupport_ratio_pos hholder hfull hgrowth hγ hγ2 hα hGFF hμ hnonatom,
    hholder γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ, hrep] with sample hpos hhold hstop
  intro c r ε hr hrε K hK hKmono hmass
  exact fineSupport_circle_hitting_union_of_stopped_representation hr hrε hK hKmono hmass
    hhold (hpos c r hr) (hstop c r hr)

end HarmonicBalls.Section6

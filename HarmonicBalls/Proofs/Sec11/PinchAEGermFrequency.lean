import HarmonicBalls.Proofs.Sec11.PinchModConstGerm
import HarmonicBalls.Proofs.Sec8.AEIndicatorFrequency

/-! # Pinch frequency from almost-sure local versions

The pointwise ergodic theorem used here is from Leonardo Bonanno's
LatticeProb formalization. -/

namespace HarmonicBalls

open Set Filter MeasureTheory Finset
open scoped Topology

open Classical in
/-- Almost-sure local versions of the indicators suffice for the pinch block
estimate under a trivial germ and stationarity. -/
theorem ae_internal_pinch_block_density_of_ae_local_versions
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ)
    (U T Q V : Set ℂ) (M : ℝ) (z : ℂ) (X : ℕ → Ω → ℝ)
    (germ : ℝ → MeasurableSpace Ω) (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (hcofinal : ∀ ε, 0 < ε → ∃ n, r n ≤ ε)
    (hrmono : Antitone r) (hgmono : Monotone germ)
    (hlocal : ∀ ε, 0 < ε → ∃ K, ∃ Y : ℕ → Ω → ℝ,
      (∀ n, K ≤ n → @Measurable Ω ℝ (germ ε) _ (Y n)) ∧
      (∀ n, K ≤ n → X n =ᵐ[P] Y n))
    (htrivial : ∀ A : Set Ω, (∀ ε, 0 < ε → MeasurableSet[germ ε] A) →
      P A = 0 ∨ P A = 1)
    (hXm : ∀ n, Measurable (X n))
    (hX : ∀ n, ∀ᵐ ω ∂P, X n ω = if pinchPointEventWithInternalBounds (μ ω) (D ω)
      U T Q V M ((2 : ℝ)⁻¹ ^ n) z then 1 else 0)
    (hstat : P.map (fun ω n => X (n + 2) ω) = P.map (fun ω n => X (n + 1) ω))
    (δ : ℝ) (hδ : δ < (P {ω | pinchPointEventWithInternalBounds (μ ω) (D ω)
      U T Q V M ((2 : ℝ)⁻¹ ^ 1) z}).toReal) :
    ∀ᵐ ω ∂P, ∀ᶠ N : ℕ in atTop, δ * N ≤
      ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
        pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q V M ((2 : ℝ)⁻¹ ^ n) z}.ncard : ℝ) := by
  let L : Ω → ℝ := fun ω => limUnder atTop (fun N : ℕ =>
    (∑ n ∈ Icc 1 N, X n ω) / (N : ℝ))
  have hLm : Measurable L := by
    apply (StronglyMeasurable.limUnder ?_).measurable
    intro N
    exact ((Finset.measurable_sum _ fun n _ => hXm n).div_const _).stronglyMeasurable
  obtain ⟨c, hc⟩ := ae_eq_const_of_trivial_germ_of_ae_local P germ r hr hcofinal
    hrmono hgmono L hLm (ae_local_initialScaleFrequency P germ X hlocal) htrivial
  have hInt : Integrable (X 1) P := by
    apply Integrable.mono' (integrable_const (1 : ℝ)) (hXm 1).aestronglyMeasurable
    filter_upwards [hX 1] with ω hω
    rw [hω]
    split_ifs <;> norm_num
  have hconv := ae_tendsto_initialScaleAverage_of_stationary P X
    (pointwiseBirkhoff_of_latticeProb _ _ _) hXm hInt hstat
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun N : ℕ =>
      (∑ n ∈ Icc 1 N, X n ω) / (N : ℝ)) atTop (𝓝 c) := by
    filter_upwards [hconv, hc] with ω ⟨d, hd⟩ hω
    have hdc : d = c := hd.limUnder_eq.symm.trans hω
    simpa only [hdc] using hd
  let E : Set Ω := {ω | pinchPointEventWithInternalBounds (μ ω) (D ω)
    U T Q V M ((2 : ℝ)⁻¹ ^ 1) z}
  let E' : Set Ω := X 1 ⁻¹' ({1} : Set ℝ)
  have hE' : MeasurableSet E' := (hXm 1) (measurableSet_singleton 1)
  have hEq : E =ᵐ[P] E' := by
    filter_upwards [hX 1] with ω hω
    simp only [E, E', mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff, hω]
    split_ifs <;> simp_all
  have hmean : (∫ ω, X 1 ω ∂P) = (P E').toReal := by
    rw [← integral_event_indicator_eq_measureReal P E' hE']
    apply integral_congr_ae
    filter_upwards [hX 1] with ω hω
    simp only [E', Set.mem_preimage, Set.mem_singleton_iff, hω]
    split_ifs <;> simp_all
  have hbound : ∀ n, ∀ᵐ ω ∂P, X n ω ∈ Icc (0 : ℝ) 1 := by
    intro n
    filter_upwards [hX n] with ω hω
    rw [hω]
    split_ifs <;> norm_num
  have hXi : ∀ n, Integrable (X n) P := by
    intro n
    apply Integrable.mono' (integrable_const (1 : ℝ)) (hXm n).aestronglyMeasurable
    filter_upwards [hbound n] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg hω.1]
    exact hω.2
  let F : ℕ → Ω → ℝ := fun N ω => (∑ n ∈ Icc 1 N, X n ω) / (N : ℝ)
  have hF : ∀ N, AEStronglyMeasurable (F N) P :=
    fun N => (integrable_initialScaleAverage P X hXi N).aestronglyMeasurable
  have hFb : ∀ N, ∀ᵐ ω ∂P, ‖F N ω‖ ≤ 1 := by
    intro N
    filter_upwards [ae_all_iff.mpr hbound] with ω hω
    have hh := initialScaleAverage_mem_Icc (fun n => X n ω) hω N
    simpa only [F, Real.norm_eq_abs, abs_of_nonneg hh.1] using hh.2
  have hstatmean : ∀ n, ∫ ω, X (n + 1) ω ∂P = ∫ ω, X 1 ω ∂P := by
    exact integral_eq_first_of_stationary_tail P X hXm hstat
  have hFm : ∀ᶠ N : ℕ in atTop, ∫ ω, F N ω ∂P = ∫ ω, X 1 ω ∂P := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    dsimp only [F]
    rw [integral_div, integral_finsetSum _ (fun n _ => hXi n)]
    have hs : (∑ n ∈ Icc 1 N, ∫ ω, X n ω ∂P) =
        ∑ _n ∈ Icc 1 N, ∫ ω, X 1 ω ∂P := by
      apply Finset.sum_congr rfl
      intro n hn
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
      simpa [Nat.succ_eq_add_one] using hstatmean k
    rw [hs]
    simp only [sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel]
    have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
    field_simp
  have hcmean := constant_limit_eq_of_eventually_integral_eq P F c (∫ ω, X 1 ω ∂P) 1 hF hFb hlim hFm
  have hδq : δ < ∫ ω, X 1 ω ∂P := by
    rw [hmean, ← measure_congr hEq]
    exact hδ
  filter_upwards [hlim, ae_all_iff.mpr hX] with ω hlim hXω
  have hlim' : Tendsto (fun N : ℕ =>
      (∑ n ∈ Icc 1 N, if pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q V M
        ((2 : ℝ)⁻¹ ^ n) z then (1 : ℝ) else 0) / (N : ℝ))
      atTop (𝓝 (∫ ω, X 1 ω ∂P)) := by
    simpa only [hXω, hcmean] using hlim
  have hf := eventually_goodScale_block_ncard
    (fun n => pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q V M
      ((2 : ℝ)⁻¹ ^ n) z) hlim' hδq
  filter_upwards [hf] with N hN
  simpa only [Set.mem_Icc, and_assoc] using hN

#print axioms ae_internal_pinch_block_density_of_ae_local_versions

end HarmonicBalls

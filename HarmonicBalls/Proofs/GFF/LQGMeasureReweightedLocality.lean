import HarmonicBalls.FirstPass.Phase2.CircleAverageLocalityLinkDerived
import HarmonicBalls.Steps.Sec11.ContinuousFieldShift

/-!
# Locality of the reweighted LQG measure

Fact 2.1 II (locality, paper lines 405-418) for the measure `μ_{h+f} = e^{γ f} μ_h` of a deterministic
continuous function `f`, deduced from Fact 2.1 II for `μ_h` (`lqgMeasureLocality_derived`).

* `IsWholePlaneGFF.exists_measurable_setLIntegral_lqgMeasure_eq`: for an open `U` and a lower semicontinuous
  `g : ℂ → ℝ≥0∞`, the integral `∫_U g dμ_h` is a.s. equal to a `σ(h|_U)`-measurable random variable. The dyadic
  layer sums `∑_{k=1}^{n 2^n} 2^{-n} μ_h(U ∩ {g > k 2^{-n}})` converge to the integral, and each set
  `U ∩ {g > k 2^{-n}}` is an open subset of `U`, so its mass is a.s. `σ(h|_U)`-measurable.
* `IsWholePlaneGFF.lqgMeasureLocality_withDensity_exp`: `(e^{γ f} μ_h)(U)` is a.s. equal to a
  `σ((h + f)|_U)`-measurable random variable; the deterministic shift `f` does not change the field σ-algebra
  (`fieldSigmaAlgebra_addFunPairing`).
-/

namespace HarmonicBalls

open MeasureTheory Set Filter Topology Finset
open scoped ENNReal

section DyadicLayer

/-- The dyadic layer sum `∑_{k=1}^{n 2^n} 2^{-n} 1_{k 2^{-n} < v}` of a value `v`. -/
private noncomputable def dyadicLayer (n : ℕ) (v : ℝ≥0∞) : ℝ≥0∞ :=
  ∑ k ∈ range (n * 2 ^ n), if ((k : ℝ≥0∞) + 1) * (2 ^ n)⁻¹ < v then (2 ^ n)⁻¹ else 0

private theorem sum_layer_le (c v : ℝ≥0∞) (N : ℕ) :
    ∑ k ∈ range N, (if ((k : ℝ≥0∞) + 1) * c < v then c else 0) ≤ v := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ]
    split_ifs with h
    · have hle : ∑ k ∈ range N, (if ((k : ℝ≥0∞) + 1) * c < v then c else 0) ≤ N * c := by
        calc _ ≤ ∑ _k ∈ range N, c := sum_le_sum fun k _ => by split_ifs <;> simp
          _ = N * c := by simp [nsmul_eq_mul]
      calc _ ≤ (N : ℝ≥0∞) * c + c := by gcongr
        _ = ((N : ℝ≥0∞) + 1) * c := by ring
        _ ≤ v := h.le
    · simpa using ih

private theorem min_le_sum_layer_add (c v : ℝ≥0∞) (N : ℕ) :
    min v (((N : ℝ≥0∞) + 1) * c) ≤
      ∑ k ∈ range N, (if ((k : ℝ≥0∞) + 1) * c < v then c else 0) + c := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ]
    push_cast
    split_ifs with h
    · rw [min_eq_right h.le] at ih
      calc min v (((N : ℝ≥0∞) + 1 + 1) * c) ≤ ((N : ℝ≥0∞) + 1 + 1) * c := min_le_right _ _
        _ = ((N : ℝ≥0∞) + 1) * c + c := by ring
        _ ≤ _ := by gcongr
    · rw [min_eq_left (not_lt.1 h)] at ih
      exact (min_le_left _ _).trans (by simpa using ih)

private theorem dyadicLayer_le (n : ℕ) (v : ℝ≥0∞) : dyadicLayer n v ≤ v :=
  sum_layer_le _ v _

private theorem tendsto_dyadicLayer (v : ℝ≥0∞) :
    Tendsto (fun n : ℕ => dyadicLayer n v) atTop (𝓝 v) := by
  refine tendsto_order.2 ⟨fun r hr => ?_, fun r hr =>
    Eventually.of_forall fun n => (dyadicLayer_le n v).trans_lt hr⟩
  obtain ⟨m, hrm, hmv⟩ := exists_between hr
  have hc : Tendsto (fun n : ℕ => r + (2 ^ n : ℝ≥0∞)⁻¹) atTop (𝓝 r) := by
    have h0 : Tendsto (fun n : ℕ => ((2 : ℝ≥0∞)⁻¹) ^ n) atTop (𝓝 0) :=
      ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (ENNReal.inv_lt_one.2 ENNReal.one_lt_two)
    simpa [ENNReal.inv_pow] using tendsto_const_nhds.add h0
  obtain ⟨N₀, hN₀⟩ := ENNReal.exists_nat_gt hmv.ne_top
  filter_upwards [hc.eventually (gt_mem_nhds hrm), eventually_ge_atTop N₀] with n hn hnN
  have h2n : (2 ^ n : ℝ≥0∞) ≠ 0 := pow_ne_zero _ two_ne_zero
  have h2n' : (2 ^ n : ℝ≥0∞) ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  have hn' : (n : ℝ≥0∞) ≤ (((n * 2 ^ n : ℕ) : ℝ≥0∞) + 1) * (2 ^ n)⁻¹ := by
    calc (n : ℝ≥0∞) = n * 2 ^ n * (2 ^ n)⁻¹ := by
          rw [mul_assoc, ENNReal.mul_inv_cancel h2n h2n', mul_one]
      _ ≤ _ := by push_cast; gcongr; exact le_self_add
  have hm : m < min v ((((n * 2 ^ n : ℕ) : ℝ≥0∞) + 1) * (2 ^ n)⁻¹) :=
    lt_min hmv (hN₀.trans_le ((Nat.cast_le.2 hnN).trans hn'))
  have key := hn.trans (hm.trans_le (min_le_sum_layer_add _ v _))
  exact (ENNReal.add_lt_add_iff_right (ENNReal.inv_ne_top.2 h2n)).1 key

/-- The lower Lebesgue integral of a measurable function is the supremum of its dyadic layer sums
`∑_{k=1}^{n 2^n} 2^{-n} ν {k 2^{-n} < g}`. -/
private theorem lintegral_eq_iSup_sum_layer {α : Type*} [MeasurableSpace α] (ν : Measure α)
    {g : α → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, g x ∂ν = ⨆ n : ℕ, ∑ k ∈ range (n * 2 ^ n),
      (2 ^ n)⁻¹ * ν {x | ((k : ℝ≥0∞) + 1) * (2 ^ n)⁻¹ < g x} := by
  have hm : ∀ (n k : ℕ), MeasurableSet {x | ((k : ℝ≥0∞) + 1) * (2 ^ n)⁻¹ < g x} :=
    fun _ _ => measurableSet_lt measurable_const hg
  have hGm : ∀ n, Measurable fun x => dyadicLayer n (g x) := fun n =>
    Finset.measurable_sum _ fun k _ => Measurable.ite (hm n k) measurable_const measurable_const
  have hint : ∀ n, ∫⁻ x, dyadicLayer n (g x) ∂ν = ∑ k ∈ range (n * 2 ^ n),
      (2 ^ n)⁻¹ * ν {x | ((k : ℝ≥0∞) + 1) * (2 ^ n)⁻¹ < g x} := by
    intro n
    simp only [dyadicLayer]
    rw [lintegral_finsetSum _ fun k _ => Measurable.ite (hm n k) measurable_const measurable_const]
    refine sum_congr rfl fun k _ => ?_
    have hind : (fun x => if ((k : ℝ≥0∞) + 1) * (2 ^ n)⁻¹ < g x then (2 ^ n : ℝ≥0∞)⁻¹ else 0) =
        {x | ((k : ℝ≥0∞) + 1) * (2 ^ n)⁻¹ < g x}.indicator fun _ => (2 ^ n)⁻¹ := by
      funext x
      simp [Set.indicator_apply]
    rw [hind, lintegral_indicator_const (hm n k)]
  refine le_antisymm ?_ (iSup_le fun n => (hint n) ▸ lintegral_mono fun x => dyadicLayer_le n (g x))
  calc ∫⁻ x, g x ∂ν = ∫⁻ x, liminf (fun n => dyadicLayer n (g x)) atTop ∂ν :=
        lintegral_congr fun x => (tendsto_dyadicLayer (g x)).liminf_eq.symm
    _ ≤ liminf (fun n => ∫⁻ x, dyadicLayer n (g x) ∂ν) atTop := lintegral_liminf_le hGm
    _ ≤ ⨆ n : ℕ, ∫⁻ x, dyadicLayer n (g x) ∂ν := by
        rw [liminf_eq_iSup_iInf_of_nat]
        exact iSup_mono fun n => iInf₂_le n le_rfl
    _ = _ := iSup_congr hint

end DyadicLayer

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
  {hcirc : Ω → ℝ → ℂ → ℝ} {γ α₀ : ℝ}

/-- **Kernel locality of the LQG measure.** For an open `U` and a lower semicontinuous `g : ℂ → ℝ≥0∞`, the
integral `∫_U g dμ_h` is a.s. equal to a `σ(h|_U)`-measurable random variable. It is the supremum of the dyadic
layer sums `∑_{k=1}^{n 2^n} 2^{-n} μ_h(U ∩ {g > k 2^{-n}})`, and Fact 2.1 II applies to each open set
`U ∩ {g > k 2^{-n}} ⊆ U`. -/
theorem IsWholePlaneGFF.exists_measurable_setLIntegral_lqgMeasure_eq
    (hG : IsWholePlaneGFF P hC hcirc) (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) {U : Set ℂ} (hU : IsOpen U)
    {g : ℂ → ℝ≥0∞} (hg : LowerSemicontinuous g) :
    ∃ Y : Ω → ℝ≥0∞, Measurable[fieldSigmaAlgebra α₀ hC U] Y ∧
      ∀ᵐ ω ∂P, ∫⁻ x in U, g x ∂(μ ω) = Y ω := by
  have hloc : ∀ p : ℕ × ℕ, ∃ Z : Ω → ℝ≥0∞, Measurable[fieldSigmaAlgebra α₀ hC U] Z ∧
      ∀ᵐ ω ∂P, μ ω ({x | ((p.2 : ℝ≥0∞) + 1) * (2 ^ p.1)⁻¹ < g x} ∩ U) = Z ω := by
    intro p
    obtain ⟨Z, hZm, hZ⟩ := lqgMeasureLocality_derived γ α₀ Ω P hC hcirc hG hγ0 hγ2 hα μ hμ _
      ((hg.isOpen_preimage (((p.2 : ℝ≥0∞) + 1) * (2 ^ p.1)⁻¹)).inter hU)
    exact ⟨Z, hZm.mono (fieldSigmaAlgebra_mono_of_subset α₀ hC inter_subset_right) le_rfl, hZ⟩
  choose Z hZm hZ using hloc
  refine ⟨fun ω => ⨆ n : ℕ, ∑ k ∈ range (n * 2 ^ n), (2 ^ n)⁻¹ * Z (n, k) ω,
    Measurable.iSup fun n => Finset.measurable_sum _ fun k _ => (hZm (n, k)).const_mul _, ?_⟩
  filter_upwards [ae_all_iff.2 hZ] with ω hω
  rw [lintegral_eq_iSup_sum_layer _ hg.measurable]
  refine iSup_congr fun n => sum_congr rfl fun k _ => ?_
  rw [Measure.restrict_apply (measurableSet_lt measurable_const hg.measurable)]
  exact congrArg _ (hω (n, k))

/-- **Fact 2.1 II for `μ_{h+f} = e^{γ f} μ_h`.** For a deterministic continuous `f : ℂ → ℝ` and an open `U`,
`(e^{γ f} μ_h)(U) = ∫_U e^{γ f} dμ_h` is a.s. equal to a `σ((h + f)|_U)`-measurable random variable. The
deterministic shift does not change the field σ-algebra (`fieldSigmaAlgebra_addFunPairing`). -/
theorem IsWholePlaneGFF.lqgMeasureLocality_withDensity_exp
    (hG : IsWholePlaneGFF P hC hcirc) (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → ℝ} (hf : Continuous f) :
    ∃ Y : Ω → ℝ≥0∞, Measurable[fieldSigmaAlgebra α₀ (fun ω => addFunPairing (hC ω) f) U] Y ∧
      ∀ᵐ ω ∂P, (μ ω).withDensity (fun x => ENNReal.ofReal (Real.exp (γ * f x))) U = Y ω := by
  have hcont : Continuous fun x => ENNReal.ofReal (Real.exp (γ * f x)) :=
    ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul hf))
  obtain ⟨Y, hYm, hY⟩ :=
    hG.exists_measurable_setLIntegral_lqgMeasure_eq hγ0 hγ2 hα hμ hU hcont.lowerSemicontinuous
  refine ⟨Y, by rwa [fieldSigmaAlgebra_addFunPairing], ?_⟩
  filter_upwards [hY] with ω hω
  rw [withDensity_apply _ hU.measurableSet, hω]

end HarmonicBalls

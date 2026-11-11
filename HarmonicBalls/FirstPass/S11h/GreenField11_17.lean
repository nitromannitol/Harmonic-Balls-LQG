import HarmonicBalls.FirstPass.S11h.GreenDyadic11_17
import HarmonicBalls.FirstPass.S11h.MassCoord11_17

/-!
# Lemma 11.17: field-level version of the annulus Green potential

Coordinate 6 of `pinchScalars` is `M * annulusGreenPotentialSup μ 0 3 6` (Defs/Annuli.lean:65). This file gives a
measurable field functional `G` (`exists_annulusGreenField`) with `G (hC ω) = SG(μ_ω)` and
`G (addFunPairing (hC ω) f) = SG(e^{γf} μ_ω)` almost surely, for a shift `f` vanishing on the annulus. Route: a
countable dense set of centres (`exists_countable_annulusGreenPotentialSup`, Fatou in GreenPotential11_17.lean), the
dyadic level-set formula (GreenDyadic11_17.lean), and the mass decoder `exists_mass_open_functional` for the open sets
`𝔸 ∩ {(k+1)/2^n < κ_x}`, which the shift does not change because `f = 0` on the annulus.
-/

namespace HarmonicBalls

open MeasureTheory Filter Set Metric Topology
open scoped ENNReal

universe u

/-- The annulus `𝔸_{a,b}(x₀)` is open. -/
theorem isOpen_annulus (x₀ : ℂ) (a b : ℝ) : IsOpen (annulus x₀ a b) :=
  isOpen_ball.sdiff Metric.isClosed_closedBall

/-- The pairing functional of the zero shift is the functional itself. -/
theorem addFunPairing_zero' (T : (ℂ → ℝ) → ℝ) : addFunPairing T 0 = T := by
  funext φ
  simp [addFunPairing]

/-- Lower semicontinuity of the annulus kernel in its second variable, for a fixed centre `x`. -/
theorem lowerSemicontinuous_annulusKernel_section (x₀ : ℂ) (b : ℝ) (x : ℂ) :
    LowerSemicontinuous (fun y => annulusKernelExt x₀ b (x, y)) := fun y =>
  lowerSemicontinuousAt_comp_of_continuous (x := y) (g := fun y' => (x, y'))
    (annulusKernelExt_lowerSemicontinuous x₀ (b := b) (x, y)) (by fun_prop)

/-- A countable dense set of centres of the annulus, independent of the measure: the supremum defining
`annulusGreenPotentialSup μ x₀ a b` is the supremum over this set for every `μ` (lower semicontinuity in the centre,
Fatou's lemma; GreenPotential11_17.lean, `annulusGreenPotentialSup_eq_countable`, with the set fixed in advance). -/
theorem exists_countable_annulusGreenPotentialSup (x₀ : ℂ) (a b : ℝ) :
    ∃ S : Set ℂ, S ⊆ annulus x₀ a b ∧ S.Countable ∧ ∀ μ : Measure ℂ,
      annulusGreenPotentialSup μ x₀ a b =
        ⨆ x ∈ S, ∫⁻ y in annulus x₀ a b, annulusKernelExt x₀ b (x, y) ∂μ := by
  obtain ⟨S, hSA, hSc, hAS⟩ := exists_countable_subset_dense_of_set (annulus x₀ a b)
  refine ⟨S, hSA, hSc, fun μ => ?_⟩
  have hAball : annulus x₀ a b ⊆ ball x₀ b := fun z hz => hz.1
  have hmeasA : MeasurableSet (annulus x₀ a b) := (isOpen_annulus x₀ a b).measurableSet
  have hG := lowerSemicontinuous_lintegral_section μ (annulus x₀ a b) (annulusKernelExt x₀ b)
    (annulusKernelExt_lowerSemicontinuous x₀)
  have hcongr : ∀ x ∈ annulus x₀ a b, ∫⁻ y in annulus x₀ a b, annulusKernelExt x₀ b (x, y) ∂μ =
      ∫⁻ y in annulus x₀ a b, annulusKernel x₀ b x y ∂μ := by
    intro x hx
    refine setLIntegral_congr_fun hmeasA fun y hy => ?_
    simp [annulusKernelExt, hAball hx, hAball hy]
  show ⨆ x ∈ annulus x₀ a b, ∫⁻ y in annulus x₀ a b, annulusKernel x₀ b x y ∂μ = _
  have hEq : (⨆ x ∈ annulus x₀ a b, ∫⁻ y in annulus x₀ a b, annulusKernel x₀ b x y ∂μ) =
      ⨆ x ∈ annulus x₀ a b, ∫⁻ y in annulus x₀ a b, annulusKernelExt x₀ b (x, y) ∂μ :=
    iSup_congr fun x => iSup_congr fun hx => (hcongr x hx).symm
  rw [hEq]
  exact iSup_mem_eq_iSup_of_dense_of_lowerSemicontinuous hG hSA hAS

/-- The restricted dyadic sum: `∫_A dyadicFun κ n dμ = ∑_{k < n 2^n} 2^{-n} μ(A ∩ {(k+1)/2^n < κ})`. -/
theorem lintegral_restrict_dyadicFun_eq_sum (μ : Measure ℂ) (A : Set ℂ) {κ : ℂ → ℝ≥0∞}
    (hκ : LowerSemicontinuous κ) (n : ℕ) :
    ∫⁻ y in A, dyadicFun κ n y ∂μ =
      ∑ k ∈ Finset.range (n * 2 ^ n), ENNReal.ofReal ((2 ^ n : ℝ)⁻¹) * μ (A ∩ dyadicLevel κ n k) := by
  have hterm : ∀ k : ℕ, ∫⁻ y in A, (if ENNReal.ofReal (((k : ℝ) + 1) / 2 ^ n) < κ y then
      ENNReal.ofReal ((2 ^ n : ℝ)⁻¹) else 0) ∂μ =
      ENNReal.ofReal ((2 ^ n : ℝ)⁻¹) * μ (A ∩ dyadicLevel κ n k) := by
    intro k
    have hS : MeasurableSet (dyadicLevel κ n k) :=
      (hκ.isOpen_preimage (ENNReal.ofReal (((k : ℝ) + 1) / 2 ^ n))).measurableSet
    have hind : (fun y => if ENNReal.ofReal (((k : ℝ) + 1) / 2 ^ n) < κ y then
        ENNReal.ofReal ((2 ^ n : ℝ)⁻¹) else 0) =
        (dyadicLevel κ n k).indicator (fun _ => ENNReal.ofReal ((2 ^ n : ℝ)⁻¹)) := by
      funext y
      simp [Set.indicator_apply, dyadicLevel]
    rw [hind, lintegral_indicator_const hS, Measure.restrict_apply hS, Set.inter_comm]
  unfold dyadicFun
  rw [lintegral_finsetSum]
  · exact Finset.sum_congr rfl fun k _ => hterm k
  · intro k _
    exact Measurable.ite (hκ.isOpen_preimage (ENNReal.ofReal (((k : ℝ) + 1) / 2 ^ n))).measurableSet
      measurable_const measurable_const

/-- The restriction of the Weyl-shifted measure `e^{γf} μ` to a measurable set `A` where `f = 0` is `μ.restrict A`. -/
theorem restrict_withDensity_exp_eq (μ : Measure ℂ) {A : Set ℂ} (hA : MeasurableSet A) (γ : ℝ) {f : ℂ → ℝ}
    (hf : ∀ z ∈ A, f z = 0) :
    (μ.withDensity (fun z => ENNReal.ofReal (Real.exp (γ * f z)))).restrict A = μ.restrict A := by
  rw [restrict_withDensity hA]
  have h1 : (fun z => ENNReal.ofReal (Real.exp (γ * f z))) =ᵐ[μ.restrict A] (1 : ℂ → ℝ≥0∞) := by
    filter_upwards [ae_restrict_mem hA] with z hz
    simp [hf z hz]
  rw [withDensity_congr_ae h1, withDensity_one]

/-- The annulus Green potential is unchanged by a Weyl shift `e^{γf}` vanishing on the annulus. -/
theorem annulusGreenPotentialSup_withDensity_exp_eq (μ : Measure ℂ) (γ : ℝ) (x₀ : ℂ) (a b : ℝ) {f : ℂ → ℝ}
    (hf : ∀ z ∈ annulus x₀ a b, f z = 0) :
    annulusGreenPotentialSup (μ.withDensity (fun z => ENNReal.ofReal (Real.exp (γ * f z)))) x₀ a b =
      annulusGreenPotentialSup μ x₀ a b := by
  have hres := restrict_withDensity_exp_eq μ (isOpen_annulus x₀ a b).measurableSet γ hf
  unfold annulusGreenPotentialSup
  simp only [hres]

/-- Field-level decoder of the annulus Green potential (Lemma 11.17, coordinate 6 of `pinchScalars`). There is a
measurable functional `G` on distributions with `G (hC ω) = SG_{a,b}(x₀)(μ_ω)` and
`G (addFunPairing (hC ω) f) = SG_{a,b}(x₀)(e^{γf} μ_ω)` almost surely, for every continuous shift `f` vanishing on the
annulus. The countable centre set is fixed in advance (`exists_countable_annulusGreenPotentialSup`), each dyadic level
mass is a field mass decoder of an open set (`exists_mass_open_functional`), and the shift leaves those masses unchanged
because the level sets lie in the annulus where `f = 0`. -/
theorem exists_annulusGreenField (hF : LQGMassFunctionalMeasurableFrozen.{u})
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (γ α₀ : ℝ) (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) (x₀ : ℂ) (a b : ℝ) (f : ℂ → ℝ) (hf : Continuous f)
    (hf0 : ∀ z ∈ annulus x₀ a b, f z = 0) :
    ∃ G : ((ℂ → ℝ) → ℝ) → ℝ≥0∞, Measurable[distributionMeasurableSpace] G ∧
      (∀ᵐ ω ∂P, G (hC ω) = annulusGreenPotentialSup (μ ω) x₀ a b) ∧
      (∀ᵐ ω ∂P, G (addFunPairing (hC ω) f) =
        annulusGreenPotentialSup ((μ ω).withDensity (fun z => ENNReal.ofReal (Real.exp (γ * f z)))) x₀ a b) := by
  obtain ⟨S, hSA, hSc, hSup⟩ := exists_countable_annulusGreenPotentialSup x₀ a b
  have : Countable S := hSc.to_subtype
  have hκ : ∀ x : ℂ, LowerSemicontinuous (fun y => annulusKernelExt x₀ b (x, y)) :=
    fun x => lowerSemicontinuous_annulusKernel_section x₀ b x
  have hU : ∀ (x : ℂ) (n k : ℕ),
      IsOpen (annulus x₀ a b ∩ dyadicLevel (fun y => annulusKernelExt x₀ b (x, y)) n k) :=
    fun x n k => (isOpen_annulus x₀ a b).inter
      ((hκ x).isOpen_preimage (ENNReal.ofReal (((k : ℝ) + 1) / 2 ^ n)))
  choose F hFm hFeq using fun (x : ℂ) (n k : ℕ) =>
    exists_mass_open_functional hF P hC hcirc μ hGFF γ α₀ hγ0 hγ2 hα hμ _ (hU x n k)
  have hae : ∀ g : ℂ → ℝ, Continuous g → (∀ z ∈ annulus x₀ a b, g z = 0) →
      ∀ᵐ ω ∂P, ∀ (x : S) (n k : ℕ), F x n k (addFunPairing (hC ω) g) =
        μ ω (annulus x₀ a b ∩ dyadicLevel (fun y => annulusKernelExt x₀ b ((x : ℂ), y)) n k) := by
    intro g hg hg0
    refine ae_all_iff.2 fun x => ae_all_iff.2 fun n => ae_all_iff.2 fun k => ?_
    exact hFeq x n k g hg fun z hz => hg0 z (inter_subset_left hz)
  have h0 : ∀ᵐ ω ∂P, ∀ (x : S) (n k : ℕ), F x n k (hC ω) =
      μ ω (annulus x₀ a b ∩ dyadicLevel (fun y => annulusKernelExt x₀ b ((x : ℂ), y)) n k) := by
    filter_upwards [hae 0 continuous_zero (fun z _ => rfl)] with ω hω
    simpa [addFunPairing_zero'] using hω
  have hf_ae := hae f hf hf0
  -- the countable sum over the centres and the levels, as a function of the measure
  have key : ∀ ν : Measure ℂ,
      (⨆ x : S, ⨆ n : ℕ, ∑ k ∈ Finset.range (n * 2 ^ n), ENNReal.ofReal ((2 ^ n : ℝ)⁻¹) *
        ν (annulus x₀ a b ∩ dyadicLevel (fun y => annulusKernelExt x₀ b ((x : ℂ), y)) n k)) =
        annulusGreenPotentialSup ν x₀ a b := by
    intro ν
    rw [hSup ν]
    refine Eq.trans (iSup_subtype'' S (fun x : ℂ => ⨆ n : ℕ, ∑ k ∈ Finset.range (n * 2 ^ n),
      ENNReal.ofReal ((2 ^ n : ℝ)⁻¹) * ν (annulus x₀ a b ∩ dyadicLevel (fun y => annulusKernelExt x₀ b (x, y)) n k))) ?_
    refine iSup_congr fun x => iSup_congr fun hx => ?_
    rw [lintegral_restrict_eq_iSup_dyadic ν (annulus x₀ a b) (hκ x)]
    exact iSup_congr fun n => (lintegral_restrict_dyadicFun_eq_sum ν _ (hκ x) n).symm
  refine ⟨fun T => ⨆ x : S, ⨆ n : ℕ, ∑ k ∈ Finset.range (n * 2 ^ n),
      ENNReal.ofReal ((2 ^ n : ℝ)⁻¹) * F x n k T, ?_, ?_, ?_⟩
  · refine Measurable.iSup fun x => Measurable.iSup fun n => ?_
    exact Finset.measurable_sum _ fun k _ => (hFm x n k).const_mul _
  · filter_upwards [h0] with ω hω
    simp only [hω]
    exact key (μ ω)
  · filter_upwards [hf_ae] with ω hω
    simp only [hω]
    rw [key (μ ω), annulusGreenPotentialSup_withDensity_exp_eq (μ ω) γ x₀ a b hf0]

end HarmonicBalls

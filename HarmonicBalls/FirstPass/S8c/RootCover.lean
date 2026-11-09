import HarmonicBalls.FirstPass.S8c.RootCount
import HarmonicBalls.Proofs.Sec8.LocalMeasureRatios

/-! # Covering the unit ball off the origin by the local domains (FIRST-PASS fp-S8c-8-2-local, step iv, pure part)

The local domains `D_j = {3 r_j < |z| < 1 - 3 r_j}` (`FirstPass/S8c/LocalObservation.lean`) cover `B_1(0) \ {0}`.
Combined with the root-side eventual count `localRoot_eventually_count_ae`, this gives an almost-sure statement
on the root law `P ⊗ₘ κ` for all nonzero `z` in the unit ball; the disintegration over `ω` and the normalisation
of the kernel are then pure measure theory. The remaining comparison of the root law `λ(ω)|_{B_1}` with the
measure `μ(ω)|_{B_1}` (Weyl relation off the origin, insertion `α₀` against no insertion) is an input `hW`
(NEW, not frozen; see the report) and the non-atomicity of `μ(ω)` at `0` is `hN0`.
-/

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped ENNReal

namespace HarmonicBalls

universe u

theorem measurableSet_localDomain (j : ℕ) : MeasurableSet (localDomain j) := by
  unfold localDomain
  exact (measurableSet_lt measurable_const continuous_norm.measurable).inter
    (measurableSet_lt continuous_norm.measurable measurable_const)

/-- Every nonzero point of the unit ball lies in some local domain `D_j`, `j ≥ 1`. -/
theorem exists_localDomain_of_mem {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) (hz0 : z ≠ 0) :
    ∃ j : ℕ, 1 ≤ j ∧ z ∈ localDomain j := by
  have hs0 : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hs1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hδ : 0 < min ‖z‖ (1 - ‖z‖) := lt_min hs0 (by linarith)
  obtain ⟨j, hj⟩ := exists_nat_gt (3 / (16 * min ‖z‖ (1 - ‖z‖)))
  have hjpos : (0 : ℝ) < j := lt_trans (div_pos (by norm_num) (mul_pos (by norm_num) hδ)) hj
  have hj1 : 1 ≤ j := by
    have : 0 < j := by exact_mod_cast hjpos
    omega
  have key : 3 < (j : ℝ) * (16 * min ‖z‖ (1 - ‖z‖)) :=
    (div_lt_iff₀ (mul_pos (by norm_num) hδ)).mp hj
  have hrad : 3 * localRadius j < min ‖z‖ (1 - ‖z‖) := by
    unfold localRadius
    have h16 : (0 : ℝ) < 16 * (j : ℝ) := mul_pos (by norm_num) hjpos
    rw [show 3 * (1 / (16 * (j : ℝ))) = 3 / (16 * (j : ℝ)) by ring, div_lt_iff₀ h16]
    nlinarith
  have hmin1 := min_le_left ‖z‖ (1 - ‖z‖)
  have hmin2 := min_le_right ‖z‖ (1 - ‖z‖)
  refine ⟨j, hj1, ?_⟩
  unfold localDomain
  exact ⟨by linarith, by linarith⟩

/-- Almost surely on the root law, the property holds for every nonzero `z` in the unit ball, from the
countably many local domains. -/
theorem ae_forall_localDomain {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    (κ : Kernel Ω ℂ) [IsSFiniteKernel κ] (Q : Ω × ℂ → Prop)
    (hQ : ∀ j : ℕ, 1 ≤ j → ∀ᵐ x ∂((P ⊗ₘ κ).restrict (Prod.snd ⁻¹' localDomain j)), Q x) :
    ∀ᵐ x ∂(P ⊗ₘ κ), x.2 ∈ ball (0 : ℂ) 1 → x.2 ≠ 0 → Q x := by
  have h1 : ∀ j : ℕ, ∀ᵐ x ∂(P ⊗ₘ κ), 1 ≤ j → x.2 ∈ localDomain j → Q x := by
    intro j
    by_cases hj : 1 ≤ j
    · filter_upwards [(ae_restrict_iff' ((measurableSet_localDomain j).preimage measurable_snd)).mp
        (hQ j hj)] with x hx
      exact fun _ hxD => hx hxD
    · exact ae_of_all _ fun x h1 _ => absurd h1 hj
  filter_upwards [ae_all_iff.mpr h1] with x hx hxball hx0
  obtain ⟨j, hj1, hjD⟩ := exists_localDomain_of_mem hxball hx0
  exact hx j hj1 hjD

/-- Disintegration over the first coordinate. -/
theorem ae_ae_forall_localDomain {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    (κ : Kernel Ω ℂ) [IsSFiniteKernel κ] (Q : Ω × ℂ → Prop)
    (h : ∀ᵐ x ∂(P ⊗ₘ κ), x.2 ∈ ball (0 : ℂ) 1 → x.2 ≠ 0 → Q x) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂(κ ω), z ∈ ball (0 : ℂ) 1 → z ≠ 0 → Q (ω, z) :=
  Measure.ae_ae_of_ae_compProd h

/-- A.s. normalised kernel: the a.s. property of `κ ω = λ(ω)|_B / λ(ω)(B)` transfers to `λ(ω)|_B`. -/
theorem ae_restrict_of_normalized {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (lam : Ω → Measure ℂ) {B : Set ℂ} (κ : Kernel Ω ℂ)
    (hκ : ∀ᵐ ω ∂P, κ ω = normalizedRestriction ((lam ω).withDensity fun _ => (1 : ℝ≥0∞)) B)
    (hpos : ∀ᵐ ω ∂P, 0 < lam ω B ∧ lam ω B ≠ ∞)
    (p : Ω → ℂ → Prop) (h : ∀ᵐ ω ∂P, ∀ᵐ z ∂(κ ω), p ω z) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂((lam ω).restrict B), p ω z := by
  filter_upwards [hκ, hpos, h] with ω hωκ hωpos hωp
  rw [hωκ, show (lam ω).withDensity (fun _ => (1 : ℝ≥0∞)) = lam ω from withDensity_one] at hωp
  unfold normalizedRestriction at hωp
  have key : (lam ω B) • ((lam ω B)⁻¹ • (lam ω).restrict B) = (lam ω).restrict B := by
    rw [smul_smul, ENNReal.mul_inv_cancel hωpos.1.ne' hωpos.2, one_smul]
  have h2 := Measure.ae_smul_measure hωp (lam ω B)
  rwa [key] at h2

/-- The root-side eventual count holds for `λ(ω)`-almost every point of the unit ball, off the origin, for
almost every `ω`, under the full-support, locality and named L3 inputs. -/
theorem localRoot_ae_ae_eventually_count (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hfull : LQGMeasureFullSupportStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ ν lam : Ω → Measure ℂ) (hGFF : IsWholePlaneGFF P hC hcirc)
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) (hν : IsLQGMeasureOfField P γ γ hcirc ν)
    (hlam : IsLQGMeasureOfField P γ 0 hcirc lam)
    (β : ℝ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m ζ : ℝ)
    (hunit : MeasurableSet {ν' : Measure ℂ | IsGoodAnnulus ν' 1 0 a b})
    (hL3 : ∀ j : ℕ, 1 ≤ j → ∀ᵐ x ∂((volume.restrict (localDomain j)).prod P),
      localReferenceObservation ν j x ∈ recentredGoodSet β N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂(lam ω).restrict (ball 0 1), z ∈ ball (0 : ℂ) 1 → z ≠ 0 →
      ∀ᶠ N : ℕ in atTop, (1 - ζ) * (N : ℝ) ≤
        (veryGoodComparableScaleCount (μ ω) β z N₀ a b C₁m C₁p C₂m C₂p C₃ m N : ℝ) := by
  have : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  have hlamA : AEMeasurable lam P := hGFF.aemeasurable_lqgMeasure hlam
  have hQ0 : (0 : ℝ) < lqgQ γ := by
    unfold lqgQ
    have h1 : 0 < 2 / γ := div_pos two_pos hγ0
    have h2 : 0 < γ / 2 := div_pos hγ0 two_pos
    linarith
  have hposlam : ∀ᵐ ω ∂P, 0 < lam ω (ball 0 1) ∧ lam ω (ball 0 1) ≠ ∞ := by
    filter_upwards [hfull γ 0 hγ0 hγ2 hQ0 Ω P hC hcirc lam hGFF hlam,
      hlam.mono fun _ h => h.isLocallyFiniteMeasure] with ω h1 h2
    have := h2
    exact ⟨h1 _ isOpen_ball (nonempty_ball.mpr one_pos), measure_ball_lt_top.ne⟩
  have hκ : ∀ᵐ ω ∂P, localRootKernel P lam hlamA ω =
      normalizedRestriction ((lam ω).withDensity fun _ => (1 : ℝ≥0∞)) (ball 0 1) :=
    ae_weightedRestrictionKernel_eq P lam hlamA (ball 0 1) measurableSet_ball
      (fun _ => (1 : ℝ≥0∞)) measurable_const
  have hinst : IsSFiniteKernel (localRootKernel P lam hlamA) := by
    unfold localRootKernel
    infer_instance
  let Q : Ω × ℂ → Prop := fun x => ∀ᶠ N : ℕ in atTop, (1 - ζ) * (N : ℝ) ≤
    (veryGoodComparableScaleCount (μ x.1) β x.2 N₀ a b C₁m C₁p C₂m C₂p C₃ m N : ℝ)
  have hall := ae_forall_localDomain P (localRootKernel P lam hlamA) Q
    (fun j hj => localRoot_eventually_count_ae hL1 hfull P γ α₀ hC hcirc μ ν lam hGFF hγ0 hγ2 hα
      hμ hν hlam j hj β N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ hunit (hL3 j hj))
  have hpair := ae_ae_forall_localDomain P (localRootKernel P lam hlamA) Q hall
  exact ae_restrict_of_normalized P lam (localRootKernel P lam hlamA) hκ hposlam
    (fun ω z => z ∈ ball (0 : ℂ) 1 → z ≠ 0 → Q (ω, z)) hpair


/-- The almost-sure statement for the measure `μ(ω)` on the unit ball, from the comparison `hW` of `μ(ω)|_{B_1}` with
`λ(ω)|_{B_1}` (NEW input, pending source; Weyl relation off the origin) and the non-atomicity `hN0` of `μ(ω)` at `0`. -/
theorem localRoot_ae_eventually_count_of_weyl (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hfull : LQGMeasureFullSupportStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ ν lam : Ω → Measure ℂ) (hGFF : IsWholePlaneGFF P hC hcirc)
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) (hν : IsLQGMeasureOfField P γ γ hcirc ν)
    (hlam : IsLQGMeasureOfField P γ 0 hcirc lam)
    (β : ℝ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m ζ : ℝ)
    (hunit : MeasurableSet {ν' : Measure ℂ | IsGoodAnnulus ν' 1 0 a b})
    (hL3 : ∀ j : ℕ, 1 ≤ j → ∀ᵐ x ∂((volume.restrict (localDomain j)).prod P),
      localReferenceObservation ν j x ∈ recentredGoodSet β N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ)
    (hW : ∀ᵐ ω ∂P, (μ ω).restrict (ball 0 1) ≪ (lam ω).restrict (ball 0 1))
    (hN0 : ∀ᵐ ω ∂P, μ ω {0} = 0) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω).restrict (ball 0 1),
      ∀ᶠ N : ℕ in atTop, (1 - ζ) * (N : ℝ) ≤
        (veryGoodComparableScaleCount (μ ω) β z N₀ a b C₁m C₁p C₂m C₂p C₃ m N : ℝ) := by
  filter_upwards [localRoot_ae_ae_eventually_count hL1 hfull P γ α₀ hC hcirc μ ν lam hGFF hγ0 hγ2
    hα hμ hν hlam β N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ hunit hL3, hW, hN0] with ω hω hWω hN0ω
  have h1 := hWω.ae_le hω
  have hae0 : ∀ᵐ z ∂(μ ω), z ≠ 0 := by
    rw [ae_iff]
    simpa using hN0ω
  filter_upwards [h1, ae_restrict_mem measurableSet_ball, ae_restrict_of_ae hae0]
    with z hz1 hz2 hz3
  exact hz1 hz2 hz3

#print axioms localRoot_ae_ae_eventually_count

end HarmonicBalls

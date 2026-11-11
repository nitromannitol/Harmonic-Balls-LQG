import HarmonicBalls.FirstPass.S11i.AlphaCanonical
import HarmonicBalls.FirstPass.S11j.CertificateTransfer

/-!
# Window frequency under a smooth Cameron-Martin shift (write-up Step 11)

For a whole-plane GFF `hC` and a smooth compactly supported `u` with zero unit-circle average, the window frequency along
dilations of an event `E` of the canonical space, for the distribution `addFunPairing (hC ω) u` (that is, `h^γ + u`), has
the same almost sure limit as for `h^γ` (Step 9, `ae_alpha_canonical_window_frequency`).

Proof. The set of distributions along which the window frequency fails to converge to `p` is measurable for the
distribution σ-algebra (`measurableSet_tendsto_windowFreqOf`). Its preimages under `hC ω` and `addFunPairing (hC ω) u`
are the two failure events of one common field event, so the Cameron-Martin transfer through one common field event
(`cameronMartinFieldCertificateTransfer`, S11j, from the frozen `CameronMartinGFFMutualAbsCont`) gives null-set equivalence.

Source: write-up Step 11 ("Cameron-Martin transfers this conclusion after
adding `u_z`"). The shift `u` is a Cameron-Martin shift; the singular shift `-γ log|·|` stays in the event set.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ProbabilityTheory

namespace HarmonicBalls

universe u

/-- The canonical field of a distribution `T` at exponent `γ`: `φ ↦ (T - γ log|·|, φ)` on mean-zero test functions
(`fieldPairing`, `Defs/GFF.lean:113`). For `T = h^ℂ` this is the canonical field of `h^γ`, `alphaCanon γ`. -/
noncomputable def canonFieldOf (γ : ℝ) (T : (ℂ → ℝ) → ℝ) : ModConstTestPairings (Set.univ : Set ℂ) :=
  fun i => fieldPairing γ T i.1

/-- The window frequency of `E` along dilations at the distribution `T` (the sum of Step 9, with the same index set
`[N+1, 2N]` and the same normalisation by `N`). -/
noncomputable def windowFreqOf (γ : ℝ) (E : Set (ModConstTestPairings (Set.univ : Set ℂ)))
    (T : (ℂ → ℝ) → ℝ) (N : ℕ) : ℝ :=
  (∑ n ∈ Finset.Icc (N + 1) (2 * N), E.indicator (fun _ => (1 : ℝ)) (dilOp^[n] (canonFieldOf γ T))) / (N : ℝ)

/-- Evaluation at a test function is measurable for the distribution σ-algebra. -/
theorem measurable_eval_distribution {φ : ℂ → ℝ} (hφ : IsTestFunction univ φ) :
    Measurable[distributionMeasurableSpace] (fun T : (ℂ → ℝ) → ℝ => T φ) := by
  apply Measurable.of_comap_le
  unfold distributionMeasurableSpace
  exact le_iSup₂ (f := fun φ (_ : IsTestFunction univ φ) =>
    MeasurableSpace.comap (fun T : (ℂ → ℝ) → ℝ => T φ) inferInstance) φ hφ

theorem measurable_canonFieldOf (γ : ℝ) :
    Measurable[distributionMeasurableSpace] (canonFieldOf γ) := by
  let _inst : MeasurableSpace ((ℂ → ℝ) → ℝ) := distributionMeasurableSpace
  refine measurable_pi_iff.2 fun i => ?_
  exact (measurable_eval_distribution i.2.1).sub_const (γ * ∫ x, i.1 x * Real.log ‖x‖)

theorem measurable_windowFreqOf {γ : ℝ} {E : Set (ModConstTestPairings (Set.univ : Set ℂ))}
    (hE : MeasurableSet E) (N : ℕ) :
    Measurable[distributionMeasurableSpace] (fun T => windowFreqOf γ E T N) := by
  unfold windowFreqOf
  refine Measurable.div_const ?_ _
  refine Finset.measurable_sum _ fun n _ => ?_
  exact (measurable_const.indicator hE).comp ((measurable_dilOp.iterate n).comp (measurable_canonFieldOf γ))

/-- The set of distributions along which the window frequency of `E` converges to `p` is measurable for the
distribution σ-algebra (a countable intersection-union description of the Cauchy-type limit). -/
theorem measurableSet_tendsto_windowFreqOf {γ : ℝ} {E : Set (ModConstTestPairings (Set.univ : Set ℂ))}
    (hE : MeasurableSet E) (p : ℝ) :
    MeasurableSet[distributionMeasurableSpace]
      {T : (ℂ → ℝ) → ℝ | Tendsto (fun N => windowFreqOf γ E T N) atTop (𝓝 p)} := by
  have hm : ∀ N : ℕ, Measurable[distributionMeasurableSpace] (fun T => windowFreqOf γ E T N) :=
    fun N => measurable_windowFreqOf hE N
  have key : {T : (ℂ → ℝ) → ℝ | Tendsto (fun N => windowFreqOf γ E T N) atTop (𝓝 p)} =
      ⋂ k : ℕ, ⋃ J : ℕ, ⋂ N : ℕ, ⋂ (_ : J ≤ N),
        ({T : (ℂ → ℝ) → ℝ | windowFreqOf γ E T N < p + 1 / ((k : ℝ) + 1)} ∩
          {T : (ℂ → ℝ) → ℝ | p - 1 / ((k : ℝ) + 1) < windowFreqOf γ E T N}) := by
    ext T
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro hT k
      have hk : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      obtain ⟨J, hJ⟩ := Metric.tendsto_atTop.1 hT _ hk
      refine ⟨J, fun N hN => ⟨?_, ?_⟩⟩
      · have h := hJ N hN
        rw [Real.dist_eq, abs_sub_lt_iff] at h
        linarith [h.1]
      · have h := hJ N hN
        rw [Real.dist_eq, abs_sub_lt_iff] at h
        linarith [h.2]
    · intro hT
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
      obtain ⟨J, hJ⟩ := hT k
      refine ⟨J, fun N hN => ?_⟩
      obtain ⟨h1, h2⟩ := hJ N hN
      rw [Real.dist_eq, abs_sub_lt_iff]
      constructor <;> linarith
  rw [key]
  refine MeasurableSet.iInter fun k => MeasurableSet.iUnion fun J =>
    MeasurableSet.iInter fun N => MeasurableSet.iInter fun _ => ?_
  exact (measurableSet_lt (hm N) measurable_const).inter (measurableSet_lt measurable_const (hm N))

/-- Step 11 transfer: for a Cameron-Martin shift `u` (smooth, compactly supported, zero unit-circle average), the
window frequency of `E` for `h^γ + u` converges almost surely to the same limit as for `h^γ`. -/
theorem ae_windowFreqOf_shift (hCM : CameronMartinGFFMutualAbsCont.{u}) (hB : BirkhoffPointwiseErgodic.{0})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc) (γ : ℝ)
    {E : Set (ModConstTestPairings (Set.univ : Set ℂ))} (hE : MeasurableSet E)
    (u : ℂ → ℝ) (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hcomp : HasCompactSupport u)
    (hu0 : Real.circleAverage u 0 1 = 0) :
    ∀ᵐ ω ∂P, Tendsto (fun N => windowFreqOf γ E (addFunPairing (hC ω) u) N) atTop
      (𝓝 (P {ω | alphaCanon γ hC ω ∈ E}).toReal) := by
  have h9 : ∀ᵐ ω ∂P, Tendsto (fun N => windowFreqOf γ E (hC ω) N) atTop
      (𝓝 (P {ω | alphaCanon γ hC ω ∈ E}).toReal) :=
    ae_alpha_canonical_window_frequency hh hB γ hE
  have hcm := cameronMartinFieldCertificateTransfer hCM Ω P hC hcirc u hh hu hcomp hu0
    {ω | ¬ Tendsto (fun N => windowFreqOf γ E (hC ω) N) atTop (𝓝 (P {ω | alphaCanon γ hC ω ∈ E}).toReal)}
    {ω | ¬ Tendsto (fun N => windowFreqOf γ E (addFunPairing (hC ω) u) N) atTop
      (𝓝 (P {ω | alphaCanon γ hC ω ∈ E}).toReal)}
    ⟨{T | Tendsto (fun N => windowFreqOf γ E T N) atTop (𝓝 (P {ω | alphaCanon γ hC ω ∈ E}).toReal)}ᶜ,
      (measurableSet_tendsto_windowFreqOf hE _).compl,
      ae_of_all _ fun ω => Iff.rfl, ae_of_all _ fun ω => Iff.rfl⟩
  have hP0 := ae_iff.1 h9
  exact ae_iff.2 ((hcm.2.2.1).2 hP0)

end HarmonicBalls

import HarmonicBalls.FirstPass.S11c.IdentifyBad11_7
import HarmonicBalls.FirstPass.S11c.CampbellApply11_7

/-!
# First pass, Lemma 11.7: from the Campbell null section to the eventual window bound (task fp-S11c-11-7-redo-11-10,
owner n1; CHATGPT-11-7-B2.md sections 6-7 and the referee notes)

Given the frozen Campbell input (`LocalCampbellMarkedRestrictionFrozen`), the decoder identity on the local
observations, and the fixed-root null sections (B2 (5.3), integrated over the root in `U`), the local bad set
`B_{U,D}` (B2 (4.6)) is `μ`-a.e. avoided by the marked root. By the identification (B2 (4.8)) this means that for
`μ`-a.e. root `z ∈ U` the global window sums of the cone-mass events are eventually at least `a N`.

The fixed-root null section (B2 (5.3)) is a hypothesis `hRef` of `campbell_local_eventual`: it is not yet proved
(it needs the translated origin statement and the Cameron-Martin transfer). The measurability `hF` of the Campbell
integrand is also a hypothesis, to be derived from the decoder identity.
-/

open MeasureTheory ProbabilityTheory Set Metric Filter
open scoped ENNReal

universe u

namespace HarmonicBalls.S11c

/-- A cone is a Borel set: an open cone is open, and the complement of an open cone is closed (`IsCone`). -/
theorem measurableSet_of_isCone {Q : Set ℂ} (hQ : IsCone Q) : MeasurableSet Q := by
  rcases hQ with h | h
  · exact h.2.1.measurableSet
  · exact (isOpen_compl_iff.mp h.2.1).measurableSet

/-- Conditional transfer (B2 sections 6-7): if the fixed-root reference null sections hold on `U = B_{r₁}(c₁)` and
the Campbell integrand is measurable, then almost surely, for `μ`-a.e. root `z ∈ U`, the window sums of the global
cone-mass events of `μ` at `z` are eventually at least `a N`. -/
theorem campbell_local_eventual
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (hCamp : LocalCampbellMarkedRestrictionFrozen.{u})
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    {γ α₀ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hh : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    {c₁ c₂ : ℂ} {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hsub : closedBall c₁ r₁ ⊆ ball c₂ r₂) (h0 : (0 : ℂ) ∉ closedBall c₂ r₂)
    {K : Kernel ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) ℂ} [IsSFiniteKernel K]
    {Q : Set ℂ} (hQ : IsCone Q) {M a : ℝ} {nD : ℕ}
    (hUD : ∀ z ∈ ball c₁ r₁, ∀ n : ℕ, nD ≤ n → closedBall z (6 * (2 : ℝ)⁻¹ ^ n) ⊆ ball c₂ r₂)
    (hdec : ∀ᵐ ω ∂P, ∃ c : ℝ≥0∞, 0 < c ∧ c < ⊤ ∧
      K (localMeanZeroObs α₀ (ball c₂ r₂) (hC ω)) = c • (μ ω).restrict (ball c₂ r₂))
    (hRef : ∀ z ∈ ball c₁ r₁, ∫⁻ ω, (localBadSet K Q M a (ball c₁ r₁) nD).indicator (fun _ => (1 : ℝ≥0∞))
        (campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z) ∂P = 0)
    (hF : AEMeasurable (fun ω => (μ ω (ball c₁ r₁))⁻¹ * ∫⁻ z in ball c₁ r₁,
        (localBadSet K Q M a (ball c₁ r₁) nD).indicator (fun _ => (1 : ℝ≥0∞))
          (campbellMarkedObs α₀ (ball c₂ r₂) (hC ω) z) ∂(μ ω)) P) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω), z ∈ ball c₁ r₁ →
      ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → a * (N : ℝ) ≤ globalWindowSum Q M z (μ ω) N := by
  have hS : MeasurableSet (localBadSet K Q M a (ball c₁ r₁) nD) :=
    measurableSet_localBadSet K (measurableSet_of_isCone hQ) M a measurableSet_ball nD
  have hRef' : (∫⁻ z in ball c₁ r₁, ∫⁻ ω, (localBadSet K Q M a (ball c₁ r₁) nD).indicator (fun _ => (1 : ℝ≥0∞))
        (campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z) ∂P) = 0 := by
    calc _ = ∫⁻ _ in ball c₁ r₁, (0 : ℝ≥0∞) := setLIntegral_congr_fun measurableSet_ball (fun z hz => hRef z hz)
      _ = 0 := by simp
  have hcamp := campbell_marked_ae_notMem hCamp hγ0 hγ2 hα hh hμ hr₁ hr₂ hsub h0 hS hRef' hF
  have hbad := ae_forall_mem_localBadSet_iff (fun ω => localMeanZeroObs α₀ (ball c₂ r₂) (hC ω)) μ K Q M a
    measurableSet_ball nD hUD hdec
  filter_upwards [hcamp, hbad] with ω hω hbadω
  filter_upwards [hω] with z hz hzU
  by_contra hcon
  exact hz hzU ((hbadω z hzU).mpr hcon)

/-- The window count of the cone-mass events at threshold `M` (the Draft count, over `n ∈ [N+1, 2N]`) is at least the
window sum at a larger threshold `M' ≥ M` (B2 (4.8), monotonicity of the cone-mass event in the threshold). -/
theorem globalWindowSum_le_ncard {Q : Set ℂ} {M M' : ℝ} (hMM' : M ≤ M') (z : ℂ) (ν : Measure ℂ) (N : ℕ) :
    globalWindowSum Q M' z ν N ≤
      ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ coneMassEvent ν Q M ((2 : ℝ)⁻¹ ^ n) z}.ncard : ℝ) := by
  classical
  have hset : {n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ coneMassEvent ν Q M ((2 : ℝ)⁻¹ ^ n) z} =
      ↑((Finset.Icc (N + 1) (2 * N)).filter (fun n => coneMassEvent ν Q M ((2 : ℝ)⁻¹ ^ n) z)) := by
    ext n
    simp [Finset.mem_Icc, and_assoc]
  rw [hset, Set.ncard_coe_finset]
  unfold globalWindowSum
  simp only [Set.indicator_apply, Set.mem_ofPred_eq, Finset.sum_boole]
  have hsub : (Finset.Icc (N + 1) (2 * N)).filter (fun n => coneMassEvent ν Q M' ((2 : ℝ)⁻¹ ^ n) z) ⊆
      (Finset.Icc (N + 1) (2 * N)).filter (fun n => coneMassEvent ν Q M ((2 : ℝ)⁻¹ ^ n) z) := by
    intro n hn
    simp only [Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, coneMassEvent_of_threshold_le ν Q hMM' _ z hn.2⟩
  exact_mod_cast Finset.card_le_card hsub

end HarmonicBalls.S11c

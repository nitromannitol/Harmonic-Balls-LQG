import HarmonicBalls.FirstPass.S11c.CampbellIntegrand11_7
import HarmonicBalls.FirstPass.S11c.LocalGlobal11_7
import HarmonicBalls.FirstPass.Frozen.S11c
import HarmonicBalls.Proposed.LQG

/-!
# Lemma 11.7, conditional assembly over the rational discs (B2 sections 7-8)

Conditional on the fixed-root input `hRef` (B2 (5.3): on each rational disc the Campbell-reference bad section is
null; not yet proved, see the report), this file derives from `campbell_local_eventual` the almost-sure statement
that, for `μ_h`-a.e. `z` and all large `N`, `a N ≤ #{n ∈ [N+1, 2N] : coneMassEvent (μ ω) Q M 2^{-n} z}`.

Inputs: `LocalCampbellMarkedRestrictionFrozen` (hCamp, Frozen/S11c.lean; a frozen EXTERNAL input);
`LQGMeasureNonatomic` (hNA, Proposed/LQG.lean:75, HB Fact 2.1 I: `μ_h({x}) = 0` a.s.; pending operator source-check);
`hRef` (per rational disc: a decoder kernel and the null fixed-root bad section; NEW, to be discharged from B2 5.1-5.2).
The local-to-global step is `ae_forall_of_ratDiscs` (LocalGlobal11_7.lean); the window comparison is
`globalWindowSum_le_ncard` (CampbellLocal11_7.lean) at `M' = M`.
-/

open MeasureTheory ProbabilityTheory Set Metric Filter
open scoped ENNReal

universe u

namespace HarmonicBalls.S11c

/-- The outer disc `D = B(c_k, t_k)` of the rational disc `k`; `closedBall c_k s_k ⊆ D` and `0 ∉ closedBall c_k t_k`. -/
abbrev ratDiscOuter (k : RatDiscIdx) : Set ℂ := ball (ratDiscCentre k) (k.1.2.2.2 : ℝ)

lemma ratDisc_pos (k : RatDiscIdx) : (0 : ℝ) < (k.1.2.2.1 : ℝ) := k.2.1

lemma ratDisc_lt (k : RatDiscIdx) : (k.1.2.2.1 : ℝ) < (k.1.2.2.2 : ℝ) := k.2.2.1

lemma ratDisc_lt_norm (k : RatDiscIdx) : (k.1.2.2.2 : ℝ) < ‖ratDiscCentre k‖ := k.2.2.2

lemma closedBall_sub_ratDiscOuter (k : RatDiscIdx) :
    closedBall (ratDiscCentre k) (k.1.2.2.1 : ℝ) ⊆ ratDiscOuter k :=
  Metric.closedBall_subset_ball (ratDisc_lt k)

lemma zero_not_mem_closedBall_ratDiscOuter (k : RatDiscIdx) :
    (0 : ℂ) ∉ closedBall (ratDiscCentre k) (k.1.2.2.2 : ℝ) := by
  intro h
  rw [Metric.mem_closedBall, dist_comm, dist_zero_right] at h
  exact absurd h (not_le.mpr (ratDisc_lt_norm k))

/-- Conditional Lemma 11.7 (fixed-root form, B2 sections 7-8). Assume the frozen Campbell restriction `hCamp`, the
non-atomicity `hNA` of the LQG measure, and the fixed-root input `hRef` on each rational disc. Then almost surely, for
`μ`-a.e. `z`, the cone-mass window count at threshold `M` is at least `a N` for all large `N`. -/
theorem ae_eventually_ncard_of_fixedRoot
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (hCamp : LocalCampbellMarkedRestrictionFrozen.{u})
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    {γ α₀ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hh : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hNA : LQGMeasureNonatomic P γ α₀ hC hcirc)
    {Q : Set ℂ} (hQ : IsCone Q) {M a : ℝ}
    (hRef : ∀ k : RatDiscIdx, ∃ K : Kernel ({φ : ℂ → ℝ // IsTestFunction (ratDiscOuter k) φ ∧ ∫ x, φ x = 0} → ℝ) ℂ,
      IsSFiniteKernel K ∧ ∃ nD : ℕ,
        (∀ z ∈ ratDiscBall k, ∀ n : ℕ, nD ≤ n → closedBall z (6 * (2 : ℝ)⁻¹ ^ n) ⊆ ratDiscOuter k) ∧
        (∀ᵐ ω ∂P, ∃ c : ℝ≥0∞, 0 < c ∧ c < ⊤ ∧
          K (localMeanZeroObs α₀ (ratDiscOuter k) (hC ω)) = c • (μ ω).restrict (ratDiscOuter k)) ∧
        ∀ z ∈ ratDiscBall k, ∫⁻ ω, (localBadSet K Q M a (ratDiscBall k) nD).indicator (fun _ => (1 : ℝ≥0∞))
          (campbellReferenceObs γ α₀ (ratDiscOuter k) (hC ω) z) ∂P = 0) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω), ∀ᶠ N : ℕ in atTop,
      a * (N : ℝ) ≤ ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ coneMassEvent (μ ω) Q M ((2 : ℝ)⁻¹ ^ n) z}.ncard : ℝ) := by
  have hloc : ∀ k : RatDiscIdx, ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω), z ∈ ratDiscBall k →
      ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → a * (N : ℝ) ≤ globalWindowSum Q M z (μ ω) N := by
    intro k
    obtain ⟨K, hK, nD, hUD, hdec, hRefk⟩ := hRef k
    have := hK
    have hF := aemeasurable_campbell_integrand (M := M) (a := a) (nD := nD) hh
      (closedBall_sub_ratDiscOuter k) hQ hdec
    exact campbell_local_eventual hCamp hγ0 hγ2 hα hh hμ (c₁ := ratDiscCentre k) (c₂ := ratDiscCentre k)
      (r₁ := (k.1.2.2.1 : ℝ)) (r₂ := (k.1.2.2.2 : ℝ)) (ratDisc_pos k) (lt_trans (ratDisc_pos k) (ratDisc_lt k))
      (closedBall_sub_ratDiscOuter k) (zero_not_mem_closedBall_ratDiscOuter k) hQ hUD hdec hRefk hF
  have h0 : ∀ᵐ ω ∂P, μ ω {0} = 0 := (hNA hh hγ0 hγ2 hα μ hμ).mono fun ω hω => hω 0
  have hall := ae_forall_of_ratDiscs μ
    (fun ω z => ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → a * (N : ℝ) ≤ globalWindowSum Q M z (μ ω) N) h0 hloc
  filter_upwards [hall] with ω hω
  filter_upwards [hω] with z hz
  obtain ⟨N0, hN0⟩ := hz
  exact Filter.eventually_atTop.mpr ⟨N0, fun N hN =>
    (hN0 N hN).trans (globalWindowSum_le_ncard (M := M) (M' := M) le_rfl z (μ ω) N)⟩

end HarmonicBalls.S11c

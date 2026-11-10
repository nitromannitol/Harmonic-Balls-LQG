import HarmonicBalls.FirstPass.S11n.PatchMeasure
import HarmonicBalls.FirstPass.Frozen.S11c
import HarmonicBalls.Draft.Section2
import HarmonicBalls.Proposed.LQG
import HarmonicBalls.FirstPass.S11i.AlphaCanonical

/-!
# Measure part (B1-μ) of the canonical identification: a universal canonical decoder for the LQG measure

For `0 < γ < 2` and `α₀ < Q`, the LQG measure of a whole-plane GFF model is almost surely a fixed positive multiple of
a measurable-in-field decoder `Dμ` evaluated at the canonical field `alphaCanon α₀ hC ω`. The decoder is the patch
`patchMeasure` (PatchMeasure.lean) of the local decoders `LocalLQGDecoderCommonFrozen` (Frozen/S11c.lean) on a countable
cover of `ℂ \ {0}` by balls `ball (g n) (‖g n‖ / 2)`. The inputs are the frozen full-support statement
`LQGMeasureFullSupportStmt` (Draft/Section2.lean, I1), the local finiteness contained in `IsLQGMeasure`
(Defs/LQG.lean), and non-atomicity `LQGMeasureNonatomic` (Proposed/LQG.lean, pending operator source-check),
used through its universal form `LQGMeasureNonatomicAll` below.

This file proves only the measure half of `LQGCanonicalIdentificationStmt` (S11n.lean). The metric half
(`D ω = b • Dd (alphaCanon ω)`) is not proved here; see the report for the missing a.s. linearity of the pairings.
-/

noncomputable section

universe u

namespace HarmonicBalls.S11n.MeasureDecoder

open MeasureTheory Set Function Filter Metric
open scoped ENNReal Topology
open HarmonicBalls.S11n.PatchMeasure

/-- Universal form of the Proposed input `LQGMeasureNonatomic` (Proposed/LQG.lean:77): for every whole-plane GFF model
`(Ω, P, hC, hcirc)` and every `γ, α₀`, the LQG measure has no atom at any point almost surely. The body is
`HarmonicBalls.LQGMeasureNonatomic`, which asserts this simultaneously for all points, not only at `0`.
Source: Fact 2.1 I (the LQG measure, item I: a.s. `μ_h` is a non-atomic Radon measure), paper
`paper/lqg_harmonic_ball-corrected.tex:408` (Fact `fact:lqg-measure`; Bou-Rabee-Gwynne arXiv:2208.11795, p. 9).
Truth check TRUE as quantified with its GFF guard (notes/fp-gaps/CHATGPT-11-7-11-10-statement-audit.md:74, row
"Universal hNA"). Status: Proposed; the operator's source-check of this locator is not yet recorded. -/
def LQGMeasureNonatomicAll : Prop :=
  ∀ (γ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
    HarmonicBalls.LQGMeasureNonatomic P γ α₀ hC hcirc

/-- A countable family of centres `g n ≠ 0` whose balls `ball (g n) (‖g n‖ / 2)` cover `ℂ \ {0}`. Lindelöf for the
centres (`TopologicalSpace.countable_cover_nhdsWithin`). -/
theorem exists_centres : ∃ g : ℕ → ℂ, (∀ n, g n ≠ 0) ∧ ∀ z : ℂ, z ≠ 0 → ∃ n, z ∈ ball (g n) (‖g n‖ / 2) := by
  have hf : ∀ x ∈ ({0}ᶜ : Set ℂ), ball x (‖x‖ / 2) ∈ 𝓝[({0}ᶜ : Set ℂ)] x := by
    intro x hx
    apply mem_nhdsWithin_of_mem_nhds
    exact Metric.ball_mem_nhds x (div_pos (norm_pos_iff.2 hx) two_pos)
  obtain ⟨t, hts, htc, hcov⟩ := TopologicalSpace.countable_cover_nhdsWithin hf
  have htne : t.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have h1 : (1 : ℂ) ∈ ({0}ᶜ : Set ℂ) := one_ne_zero
    have h2 := hcov h1
    rw [h, Set.biUnion_empty] at h2
    exact h2
  obtain ⟨g, hg⟩ := htc.exists_eq_range htne
  refine ⟨g, fun n => ?_, fun z hz => ?_⟩
  · have hmem : g n ∈ t := by rw [hg]; exact mem_range_self n
    exact fun h => hts hmem (Set.mem_singleton_iff.2 h)
  · obtain ⟨x, hxt, hzx⟩ := Set.mem_iUnion₂.1 (hcov (show z ∈ ({0}ᶜ : Set ℂ) from hz))
    have hxr : x ∈ Set.range g := by rw [← hg]; exact hxt
    obtain ⟨n, rfl⟩ := hxr
    exact ⟨n, hzx⟩

theorem ball_not_zero {g : ℕ → ℂ} (hg : ∀ n, g n ≠ 0) (n : ℕ) : (0 : ℂ) ∉ ball (g n) (‖g n‖ / 2) := by
  intro h
  rw [Metric.mem_ball, dist_zero_left] at h
  linarith [norm_pos_iff.2 (hg n)]

theorem ball_nonempty {g : ℕ → ℂ} (hg : ∀ n, g n ≠ 0) (n : ℕ) : (ball (g n) (‖g n‖ / 2)).Nonempty :=
  ⟨g n, Metric.mem_ball_self (half_pos (norm_pos_iff.2 (hg n)))⟩

/-- Chains from the base ball `0` to every ball of the cover (nerve connectivity of `ℂ \ {0}`). -/
theorem exists_chains {g : ℕ → ℂ} (hg : ∀ n, g n ≠ 0)
    (hcov : ∀ z : ℂ, z ≠ 0 → ∃ n, z ∈ ball (g n) (‖g n‖ / 2)) :
    ∃ L : ℕ → List ℕ, ∀ j, List.IsChain (Ov (fun n => ball (g n) (‖g n‖ / 2))) (0 :: L j) ∧
      lastOf 0 (L j) = j := by
  have h := fun j => exists_chain (B := fun n => ball (g n) (‖g n‖ / 2)) (fun n => isOpen_ball)
    hcov (ball_not_zero hg) (ball_nonempty hg) 0 j
  choose L hL using h
  exact ⟨L, hL⟩

/-- Restriction of a canonical field to the mean-zero observables supported in `D`. -/
def restrictObs (D : Set ℂ) (ℓ : ModConstTestPairings (univ : Set ℂ)) :
    {φ : ℂ → ℝ // IsTestFunction D φ ∧ ∫ x, φ x = 0} → ℝ :=
  fun φ => ℓ ⟨φ.1, by
    obtain ⟨h1, h2, h3⟩ := φ.2.1
    exact ⟨h1, h2, subset_univ _⟩, φ.2.2⟩

theorem restrictObs_alphaCanon (D : Set ℂ) (α₀ : ℝ) {Ω : Type*} (hC : Ω → (ℂ → ℝ) → ℝ) (ω : Ω) :
    restrictObs D (alphaCanon α₀ hC ω) = localMeanZeroObs α₀ D (hC ω) := rfl

/-- Universal canonical measure decoder: there is one measurable-in-field decoder `Dμ` such that, for every whole-plane
GFF model with LQG measure `μ` of the field `h^ℂ - α₀ log|·|`, almost surely `μ ω = a • Dμ (alphaCanon α₀ hC ω)` for a
constant `a > 0`. Inputs: the frozen local decoders, the frozen I1, and the (pending) non-atomicity. -/
theorem exists_measureDecoder (hK : HarmonicBalls.LocalLQGDecoderCommonFrozen.{u})
    (hI1 : HarmonicBalls.LQGMeasureFullSupportStmt.{u}) (hNA : LQGMeasureNonatomicAll.{u})
    (γ α₀ : ℝ) (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < HarmonicBalls.lqgQ γ) :
    ∃ Dμ : ModConstTestPairings (univ : Set ℂ) → Measure ℂ,
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (hC : Ω → (ℂ → ℝ) → ℝ)
        (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), HarmonicBalls.IsWholePlaneGFF P hC hcirc →
        HarmonicBalls.IsLQGMeasureOfField P γ α₀ hcirc μ →
        ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧ μ ω = ENNReal.ofReal a • Dμ (alphaCanon α₀ hC ω) := by
  obtain ⟨g, hg, hcov⟩ := exists_centres
  have hpos : ∀ n, 0 < ‖g n‖ / 2 := fun n => half_pos (norm_pos_iff.2 (hg n))
  have hnotmem : ∀ n, (0 : ℂ) ∉ closedBall (g n) (‖g n‖ / 2) := by
    intro n h
    rw [Metric.mem_closedBall, dist_zero_left] at h
    linarith [norm_pos_iff.2 (hg n)]
  choose K hKs using fun n => hK γ hγ0 hγ2 (g n) (‖g n‖ / 2) (hpos n) (hnotmem n)
  obtain ⟨L, hL⟩ := exists_chains hg hcov
  refine ⟨fun ℓ => patchMeasure (fun n => ball (g n) (‖g n‖ / 2))
    (fun n => K n (restrictObs (ball (g n) (‖g n‖ / 2)) ℓ)) L 0, ?_⟩
  intro Ω _ P _ hC hcirc μ hG hμ
  have hA : ∀ᵐ ω ∂P, ∀ n, ∃ c : ℝ≥0∞, 0 < c ∧ c < ⊤ ∧
      K n (localMeanZeroObs α₀ (ball (g n) (‖g n‖ / 2)) (hC ω)) =
        c • (μ ω).restrict (ball (g n) (‖g n‖ / 2)) := by
    rw [ae_all_iff]
    intro n
    exact (hKs n).2.1 α₀ hα Ω P hC hcirc μ hG hμ
  have hN : ∀ᵐ ω ∂P, ∀ x : ℂ, μ ω {x} = 0 :=
    hNA γ α₀ Ω P hC hcirc hG hγ0 hγ2 hα μ hμ
  have hI : ∀ᵐ ω ∂P, ∀ U : Set ℂ, IsOpen U → U.Nonempty → 0 < μ ω U :=
    hI1 γ α₀ hγ0 hγ2 hα Ω P hC hcirc μ hG hμ
  have hμ' : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage α₀ (hcirc ω)) (μ ω) := hμ
  filter_upwards [hA, hN, hI, hμ'] with ω hcst hnull hpos' hlim
  choose c hc using hcst
  have hloc : IsLocallyFiniteMeasure (μ ω) := hlim.isLocallyFiniteMeasure
  have hν : ∀ n, K n (restrictObs (ball (g n) (‖g n‖ / 2)) (alphaCanon α₀ hC ω)) =
      c n • (μ ω).restrict (ball (g n) (‖g n‖ / 2)) := fun n => (hc n).2.2
  have hfin : ∀ a b, Ov (fun n => ball (g n) (‖g n‖ / 2)) a b →
      μ ω (ball (g a) (‖g a‖ / 2) ∩ ball (g b) (‖g b‖ / 2)) ≠ 0 ∧
        μ ω (ball (g a) (‖g a‖ / 2) ∩ ball (g b) (‖g b‖ / 2)) ≠ ⊤ := by
    intro a b hab
    refine ⟨(hpos' _ (isOpen_ball.inter isOpen_ball) hab).ne', ?_⟩
    have hfinS : μ ω (ball (g a) (‖g a‖ / 2) ∩ ball (g b) (‖g b‖ / 2)) ≤
        μ ω (closedBall (g a) (‖g a‖ / 2)) :=
      measure_mono (inter_subset_left.trans Metric.ball_subset_closedBall)
    exact ne_top_of_le_ne_top (isCompact_closedBall _ _).measure_lt_top.ne hfinS
  have hmain := patchMeasure_identity (B := fun n => ball (g n) (‖g n‖ / 2))
    (fun n => isOpen_ball) hcov (μ ω) (hnull 0)
    (fun n => K n (restrictObs (ball (g n) (‖g n‖ / 2)) (alphaCanon α₀ hC ω)))
    c (fun n => (hc n).1.ne') (fun n => (hc n).2.1.ne) hν hfin 0 L hL
  have hc0ne : c 0 ≠ 0 := (hc 0).1.ne'
  have hc0top : c 0 ≠ ⊤ := (hc 0).2.1.ne
  refine ⟨(c 0).toReal⁻¹, inv_pos.2 (ENNReal.toReal_pos hc0ne hc0top), ?_⟩
  show μ ω = ENNReal.ofReal (c 0).toReal⁻¹ • patchMeasure (fun n => ball (g n) (‖g n‖ / 2))
    (fun n => K n (restrictObs (ball (g n) (‖g n‖ / 2)) (alphaCanon α₀ hC ω))) L 0
  rw [← hmain, ENNReal.ofReal_inv_of_pos (ENNReal.toReal_pos hc0ne hc0top), ENNReal.ofReal_toReal hc0top,
    smul_smul, ENNReal.inv_mul_cancel hc0ne hc0top, one_smul]

end HarmonicBalls.S11n.MeasureDecoder

end

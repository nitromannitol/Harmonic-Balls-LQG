import HarmonicBalls.FirstPass.S11i.Step8PhysReduction
import HarmonicBalls.FirstPass.S11r.LogSingularCutoff

/-!
# Insertion transfer: all-model zero-insertion physical frequency implies the insertion-`α` one
(fp-S11i-insertion-transfer, owner n4)

Source: `notes/fp-gaps/CODEX-hPhys-sol-20261110.md`, section "For insertion transfer" and VERDICT step 3.

`PhysicalAt` and `AllModelsAt` are the proposed interfaces of that note, written with the same bodies as the existing
binder `Step8PhysStmt` (`S11i/Step8PhysReduction.lean:84`). `Step8PhysExists.lean` is not in the repository yet, so the
two definitions are declared here locally (the bodies are unchanged).

Ingredients of the transfer, in the order of the note:
* a finite cover of `B_{2^k} \ {0}` by root balls whose decoder discs avoid `0` (dilates of the valid balls);
* on each decoder disc, a smooth compactly supported shift equal to `-α log|·|` (Cameron–Martin reweighting,
  frozen `CameronMartinGFFReweighting`, `S11aj.lean`);
* the zero-insertion statement applied under the changed law, and transfer of its conull event back;
* the eventual certificate fitting (`ae_fitting_eventually_of_decoders`, `S11i/Step8Fitting.lean:114`), which makes
  the window counts agree for all large `N`.

This file so far contains the definitions and the window-count lemma `tendsto_window_iff_of_eventually_iff`.
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HarmonicBalls.FirstPassS11iInsertionTransfer

open HarmonicBalls FirstPassS11i

universe u

/-- **Physical window frequency of one insertion-`α` model on `B_{2^k}(0)`** (body of `Step8PhysStmt`,
`S11i/Step8PhysReduction.lean:84`). Almost surely, for almost every `z` in `B_{2^k}(0)`, the window count of the
certificate events at radii `2^k 2^{-n}`, `n ∈ [N+1, 2N]`, divided by `N`, tends to `q`. -/
def PhysicalAt {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (q : ℝ) (U V W T Q' Q : Set ℂ) (δ M : ℝ) (k : ℕ)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ) : Prop :=
  ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω), z ∈ ball (0 : ℂ) ((2 : ℝ) ^ k) →
    Tendsto (fun N : ℕ => (({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
        CertificateEvent (μ ω) (D ω) (pinchOmegaGeom W Q δ) U V W T Q' Q δ M
          ((2 : ℝ) ^ k * (2 : ℝ)⁻¹ ^ n) z}.ncard : ℕ) : ℝ) / (N : ℝ))
      atTop (𝓝 q)

/-- **All-model physical frequency at insertion `α`.** For every whole-plane GFF `hC` on every probability space
`(Ω, P)` and every insertion-`α` LQG measure `μ` and metric `D` of the field, `PhysicalAt` holds at scale `2^k`.
The quantification over all `Ω : Type u` and all laws is what the Cameron–Martin change of law uses. -/
def AllModelsAt (γ ξ α q : ℝ) (U V W T Q' Q : Set ℂ) (δ M : ℝ) (k : ℕ) : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
    IsWholePlaneGFF P hC hcirc →
    IsLQGMeasureOfField P γ α hcirc μ →
    IsLQGMetricOfField P γ ξ α hC D →
      PhysicalAt P q U V W T Q' Q δ M k μ D

/-- **Eventually equal window counts have the same frequency limit.** If two predicates on the index `n` agree for all
large `n`, then for all large `N` the window sets `{n ∈ [N+1, 2N] | P n}` and `{n ∈ [N+1, 2N] | Q n}` coincide, so the
window frequencies `#{…}/N` are eventually equal functions of `N` and have the same limit. This is the step where
eventual certificate fitting (`ae_fitting_eventually_of_decoders`) is turned into equal frequency limits. -/
theorem tendsto_window_iff_of_eventually_iff {P Q : ℕ → Prop} (h : ∀ᶠ n in atTop, (P n ↔ Q n)) (q : ℝ) :
    Tendsto (fun N : ℕ => (({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ P n}.ncard : ℕ) : ℝ) / (N : ℝ)) atTop (𝓝 q) ↔
      Tendsto (fun N : ℕ => (({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ Q n}.ncard : ℕ) : ℝ) / (N : ℝ)) atTop (𝓝 q) := by
  obtain ⟨n0, hn0⟩ := eventually_atTop.1 h
  have hEq : (fun N : ℕ => (({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ P n}.ncard : ℕ) : ℝ) / (N : ℝ)) =ᶠ[atTop]
      (fun N : ℕ => (({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ Q n}.ncard : ℕ) : ℝ) / (N : ℝ)) := by
    filter_upwards [eventually_ge_atTop n0] with N hN
    have hs : {n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ P n} = {n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ Q n} := by
      ext n
      simp only [Set.mem_ofPred_eq]
      constructor
      · rintro ⟨h1, h2, h3⟩
        exact ⟨h1, h2, (hn0 n (by omega)).1 h3⟩
      · rintro ⟨h1, h2, h3⟩
        exact ⟨h1, h2, (hn0 n (by omega)).2 h3⟩
    rw [hs]
  exact tendsto_congr' hEq

/-- **Smooth cut-off of `-β log‖·‖` away from the origin.** For a disc `ball c ρ` not containing `0`
(`ρ < ‖c‖`), there is a smooth compactly supported `f` equal to `-β log‖·‖` on `ball c ρ`. Its unit-circle average is zero
because `log 1 = 0` on the unit circle, so no normalisation constant is needed. This is the shift of
`CameronMartinGFFReweighting` (frozen, `FirstPass/Frozen/S11aj.lean:33`) in the zero-insertion coordinates. The proof
follows `exists_log_sing_cutoff` (`S11r/LogSingularCutoff.lean:35`) with the singularity at `0`. -/
theorem exists_log_cutoff_avoid_zero (β : ℝ) {c : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ < ‖c‖) :
    ∃ f : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧ Real.circleAverage f 0 1 = 0 ∧
      ∀ x ∈ ball c ρ, f x = -β * Real.log ‖x‖ := by
  let B : ContDiffBump c :=
    { rIn := ρ, rOut := (ρ + ‖c‖) / 2, rIn_pos := hρ, rIn_lt_rOut := by linarith }
  have hBz : ∀ y : ℂ, (ρ + ‖c‖) / 2 ≤ dist y c → B y = 0 := fun y hy => B.zero_of_le_dist hy
  refine ⟨fun x => B x * (-β * Real.log ‖x‖), ?_, ?_, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x = 0
    · -- near the origin the bump vanishes
      have hx0 : dist x c = ‖c‖ := by rw [hx, dist_zero_left]
      have hd : 0 < dist x c - (ρ + ‖c‖) / 2 := by rw [hx0]; linarith
      refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [Metric.ball_mem_nhds x hd] with y hy
      have hy' : dist y x < dist x c - (ρ + ‖c‖) / 2 := mem_ball.1 hy
      have hyc : (ρ + ‖c‖) / 2 ≤ dist y c := by
        have h3 := dist_triangle x y c
        have h4 := dist_comm x y
        linarith
      simp [hBz y hyc]
    · have hL : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : ℂ => -β * Real.log ‖y‖) x :=
        contDiffAt_const.mul ((Real.contDiffAt_log.2 (norm_ne_zero_iff.2 hx)).comp x (contDiffAt_norm ℝ hx))
      exact B.contDiff.contDiffAt.mul hL
  · exact B.hasCompactSupport.mul_right
  · apply circleAverage_unit_zero_of_vanish
    intro x hx
    simp [hx]
  · intro x hx
    have hB1 : B x = 1 := B.one_of_mem_closedBall (ball_subset_closedBall hx)
    simp [hB1]

end HarmonicBalls.FirstPassS11iInsertionTransfer

#print axioms HarmonicBalls.FirstPassS11iInsertionTransfer.tendsto_window_iff_of_eventually_iff
#print axioms HarmonicBalls.FirstPassS11iInsertionTransfer.exists_log_cutoff_avoid_zero

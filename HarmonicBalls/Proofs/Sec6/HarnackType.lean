import HarmonicBalls.Draft.Section6
import HarmonicBalls.Proofs.Sec2.PolyHighProb

/-!
# Propositions 6.1 and 6.2 from Lemmas 6.6 and 6.11

The proof of Propositions 6.1 and 6.2 (lines 1593-1596 of paper/lqg_harmonic_ball-corrected.tex): "combine Lemma 6.6
and Lemma 6.11", with the constants chosen in the order of fig:constant-dependencies (lines 1579-1588):
`C₃` (Lemma 6.6), then `b = b(γ, β⁻, C₃)` (Lemma 6.11), then `a, C₁^±, C₂^±, N₁` (Lemma 6.6 at this `b`), then
`N₀ := max(N₁ of Lemma 6.6, N₁ a C₁⁻ C₂⁺ of Lemma 6.11)` and `α := α a N₀ C₁⁻` (Lemma 6.11). The exponent of `M_ρ`
is fixed as `β⁻ := (2+γ)²/2 + 1`. The events are `E_ρ(x₀) := Ē_ρ(x₀; N₀, a, b, C₁^±, C₂^±, C₃) ∩ G`, where `G` is
the event of probability one of Lemma 6.11; intersecting with `G` does not change the prevalence (`inter_ae`).
The universal constant of Proposition 6.1 is `c / log 8`, `c` that of Lemma 6.6 (`log₈ = log / log 8`).

* `harnackTypeComponentStmt_of_lemmas`: Proposition 6.2 from Lemmas 6.6 and 6.11.
* `harnackTypeEstimateStmt_of_component`: Proposition 6.1 from Proposition 6.2 (lines 1084-1086: every point of
  `Λ^z_t ∩ B_{ρ/2}(x₀)` lies in a connected component of `Λ^z_t ∩ B_ρ(x₀)`, whose mass in `𝔸_{ρ/2,ρ}(x₀)` is at most
  that of `Λ^z_t`).

Both constants `α` and `c` are chosen before `α₀`, as printed: those of Lemmas 6.6 and 6.11 are.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

open Section6

universe u

/-- Proposition 6.1 from Proposition 6.2 (lines 1084-1086), with the same `c`, `α` and events. -/
theorem harnackTypeEstimateStmt_of_component (h : HarnackTypeComponentStmt.{u}) :
    HarnackTypeEstimateStmt.{u} := by
  obtain ⟨c, hc, h⟩ := h
  refine ⟨c, hc, fun γ hγ hγ2 => ?_⟩
  obtain ⟨α, hα, h⟩ := h γ hγ hγ2
  refine ⟨α, hα, fun α₀ hα₀ Ω _ P hC hcirc μ hGFF hμ => ?_⟩
  obtain ⟨E, hE, hprev⟩ := h α₀ hα₀ Ω P hC hcirc μ hGFF hμ
  refine ⟨E, fun ω ρ hρ x₀ hω z hz t ht hball hmass => ?_, hprev⟩
  refine eq_empty_iff_forall_notMem.2 fun y hy => ?_
  have hyρ : y ∈ cluster (μ ω) 1 z t ∩ ball x₀ ρ :=
    ⟨hy.1, ball_subset_ball (by linarith [hρ.1]) hy.2⟩
  set Λ := connectedComponentIn (cluster (μ ω) 1 z t ∩ ball x₀ ρ) y
  have hΛ : Λ ∈ connectedComponentsIn (cluster (μ ω) 1 z t ∩ ball x₀ ρ) := ⟨y, hyρ, rfl⟩
  have hΛsub : Λ ⊆ cluster (μ ω) 1 z t := fun x hx => (connectedComponentIn_subset _ _ hx).1
  have hΛmass : μ ω (Λ ∩ annulus x₀ (ρ / 2) ρ) ≤ ENNReal.ofReal α * μ ω (annulus x₀ (ρ / 2) ρ) :=
    (measure_mono (inter_subset_inter_left _ hΛsub)).trans hmass
  have h0 := hE ω ρ hρ x₀ hω z hz t ht hball Λ hΛ hΛmass
  exact (eq_empty_iff_forall_notMem.1 h0) y ⟨mem_connectedComponentIn hyρ, ball_subset_closedBall hy.2⟩

/-- `log₈ y = log y / log 8`: the count `c log₈ ε^{-1/2}` of Lemma 6.6 is `(c / log 8) log ε^{-1/2}`. -/
theorem div_log_eight_mul_log (c y : ℝ) : c / Real.log 8 * Real.log y = c * Real.logb 8 y := by
  rw [Real.logb]; ring

/-- Proposition 6.2 from Lemma 6.6 (prevalence of very good annuli, printed `α₀`-uniform order) and Lemma 6.11 (very
good annuli satisfy the Harnack-type estimate), lines 1593-1596. -/
theorem harnackTypeComponentStmt_of_lemmas (h66 : ManyVeryGoodAnnuliStmt.{u})
    (h611 : VeryGoodAnnulusHarnackTypeStmt.{u}) : HarnackTypeComponentStmt.{u} := by
  obtain ⟨c, C₃, hc, hC₃, h66⟩ := h66
  have hlog8 : 0 < Real.log 8 := Real.log_pos (by norm_num)
  refine ⟨c / Real.log 8, div_pos hc hlog8, fun γ hγ hγ2 => ?_⟩
  set β : ℝ := (2 + γ) ^ 2 / 2 + 1
  have hβ : (2 + γ) ^ 2 / 2 < β := show (2 + γ) ^ 2 / 2 < (2 + γ) ^ 2 / 2 + 1 by linarith
  obtain ⟨b, hb, N₁f, αf, hN₁f, h611⟩ := h611 γ hγ hγ2 β hβ C₃ hC₃
  obtain ⟨a, ha, C₁m, C₁p, C₂m, C₂p, h1m, h1p, h2m, h2p, N₁, -, h66⟩ := h66 γ hγ hγ2 β hβ b hb
  set N₀ : ℕ := max N₁ (N₁f a C₁m C₂p)
  have hN₀ : N₁f a C₁m C₂p ≤ N₀ := le_max_right _ _
  have hα := (hN₁f a ha C₁m C₂p h1m h2p).2 N₀ hN₀
  refine ⟨αf a N₀ C₁m, hα.1, fun α₀ hα₀ Ω _ P hC hcirc μ hGFF hμ => ?_⟩
  have hG := h611 α₀ hα₀ Ω P hC hcirc μ hGFF hμ
  set G : Set Ω := {ω | ∀ a ∈ Ioo (0 : ℝ) 1, ∀ C₁m C₁p C₂m C₂p : ℝ, 0 < C₁m → 0 < C₁p → 0 < C₂m → 0 < C₂p →
      ∀ N₀ : ℕ, N₁f a C₁m C₂p ≤ N₀ →
      ∀ z ∈ ball (0 : ℂ) 1, ∀ t : ℝ, 0 < t → ∀ ρ ∈ Ioo (0 : ℝ) 1, ∀ x₀ ∈ ball (0 : ℂ) 1,
      closedBall x₀ ρ ⊆ ball 0 1 \ {z} →
      IsVeryGoodAnnulus (μ ω) β ρ x₀ N₀ a b C₁m C₁p C₂m C₂p C₃ →
      ∀ Λ ∈ connectedComponentsIn (cluster (μ ω) 1 z t ∩ ball x₀ ρ),
        μ ω (Λ ∩ annulus x₀ (ρ / 2) ρ) ≤ ENNReal.ofReal (αf a N₀ C₁m) * μ ω (annulus x₀ (ρ / 2) ρ) →
        Λ ∩ closedBall x₀ (ρ / 2) = ∅}
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := hG
  refine ⟨fun ρ x₀ => {ω | ω ∈ G ∧ IsVeryGoodAnnulus (μ ω) β ρ x₀ N₀ a b C₁m C₁p C₂m C₂p C₃},
    fun ω ρ hρ x₀ hω z hz t ht hball => ?_, ?_⟩
  · have hx₀ : x₀ ∈ ball (0 : ℂ) 1 := (hball (mem_closedBall_self hρ.1.le)).1
    exact hω.1 a ha C₁m C₁p C₂m C₂p h1m h1p h2m h2p N₀ hN₀ z hz t ht ρ hρ x₀ hx₀ hball hω.2
  · refine ((h66 N₀ (le_max_left _ _) α₀ hα₀ Ω P hC hcirc μ hGFF hμ).inter_ae hGae).mono
      fun ε ω hω x₀ hx₀ => ?_
    have hcount := hω.1 x₀ hx₀
    rw [div_log_eight_mul_log]
    refine hcount.trans_eq ?_
    congr 2
    ext ρ
    exact ⟨fun h => ⟨h.1, h.2.1, hω.2, h.2.2⟩, fun h => ⟨h.1, h.2.1, h.2.2.2⟩⟩

end HarmonicBalls

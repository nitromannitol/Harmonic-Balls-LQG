import HarmonicBalls.FirstPass.Phase2.RootedLocalAgreementEvent
import HarmonicBalls.FirstPass.S11at
import HarmonicBalls.FirstPass.S11r.RootedTriangle
import HarmonicBalls.FirstPass.S11r.RootedPhysical
import HarmonicBalls.Steps.Sec11.InternalMetricContinuity

/-!
# Deterministic ingredients of the unrooted membership in the local-agreement event (step 5)

Let `F` be a Euclidean length metric, `D` an open set and `c ∈ [0, ∞]`. This module proves the three deterministic
statements by which the observation of the unrooted field lies in the event `A = A1 ∩ A2 ∩ A3` of
`Phase2/RootedLocalAgreementEvent.lean`, for the distance function `c · internalMetric F D` and the local functions
`c · internalMetric F V`, `V ⊆ D` open:

* `internalMetric_axioms`: vanishing on the diagonal of `D`, symmetry and the triangle inequality (A1);
* `exists_rat_internalMetric_eq_on_compact`: uniformly on a compact `C ⊆ V ⊆ D` the internal metrics of `F` on `D` and
  on `V` agree for points at Euclidean distance `< η` (A3; no shortcut, uniformly by the Lebesgue number lemma);
* `mem_eventLocalAgreement_of_internalMetric` (A3 in the form of the event) and `mem_eventChains_of_natChains`
  (A2: chains through the points of `S` indexed by `ℕ` give the chains of the event, indexed by `Fin (N + 1)`).

Terminology: internal metric `D(·,·;U)` (Armstrong-Kuusi-Mourrat); Euclidean length metric (Gwynne-Miller).
-/

namespace HarmonicBalls

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace UnrootedLocal

/-- A Euclidean length metric is nonnegative. -/
theorem nonneg_of_isEuclideanLengthMetric {F : ℂ → ℂ → ℝ} (hF : IsEuclideanLengthMetric F) (x y : ℂ) :
    0 ≤ F x y := by
  have h1 := hF.triangle x y x
  have h2 := hF.symm y x
  have h3 := hF.self_eq_zero x
  linarith

/-- **A1 for a multiple of the internal metric.** For a Euclidean length metric `F`, an open set `D` and
`c ∈ [0, ∞]`, the function `c · internalMetric F D` vanishes on the diagonal of `D`, is symmetric and satisfies the
triangle inequality. -/
theorem internalMetric_axioms {F : ℂ → ℂ → ℝ} (hF : IsEuclideanLengthMetric F) {D : Set ℂ} (hD : IsOpen D)
    (c : ℝ≥0∞) :
    (∀ x ∈ D, c * internalMetric F D x x = 0) ∧
    (∀ x y, c * internalMetric F D x y = c * internalMetric F D y x) ∧
    (∀ x y w, c * internalMetric F D x w ≤ c * internalMetric F D x y + c * internalMetric F D y w) := by
  have hnn := nonneg_of_isEuclideanLengthMetric hF
  refine ⟨fun x hx => ?_, fun x y => ?_, fun x y w => ?_⟩
  · rw [hF.internalMetric_self_of_mem_open hnn hD hx, mul_zero]
  · rw [internalMetric_symm_of_symm hF.symm D x y]
  · rw [← mul_add]
    have h : internalMetric F D x w ≤ internalMetric F D x y + internalMetric F D y w :=
      internalMetric_triangle_on F (D := D) hF.symm (fun x _ => hF.self_eq_zero x)
        (fun x _ y _ w _ => hF.triangle x y w)
    gcongr

/-- **No shortcut, uniformly on a compact set.** Let `F` be a Euclidean length metric, `V ⊆ D` open and `C ⊆ V`
compact. There is `η > 0` such that the internal metrics of `F` on `D` and on `V` agree at all pairs of points of `C`
at distance `< η`: both equal `F` there. -/
theorem exists_internalMetric_eq_on_compact {F : ℂ → ℂ → ℝ} (hF : IsEuclideanLengthMetric F) {V D : Set ℂ}
    (hV : IsOpen V) (hVD : V ⊆ D) (hD : IsOpen D) {C : Set ℂ} (hC : IsCompact C) (hCV : C ⊆ V) :
    ∃ η : ℝ, 0 < η ∧ ∀ u ∈ C, ∀ v ∈ C, dist u v < η → internalMetric F D u v = internalMetric F V u v := by
  have hr : ∀ q : ℂ, ∃ r : ℝ, 0 < r ∧ (q ∈ C → ∀ x ∈ closedBall q r, ∀ y ∈ closedBall q r,
      internalMetric F D x y = internalMetric F V x y) := by
    intro q
    by_cases hq : q ∈ C
    · obtain ⟨ρ₁, hρ₁, -, h₁⟩ := FirstPassS11at.eq_internalMetric_on_small_ball_at hF hV (hCV hq)
      obtain ⟨ρ₂, hρ₂, -, h₂⟩ := FirstPassS11at.eq_internalMetric_on_small_ball_at hF hD (hVD (hCV hq))
      refine ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, fun _ x hx y hy => ?_⟩
      rw [← h₂ x (closedBall_subset_closedBall (min_le_right _ _) hx) y
          (closedBall_subset_closedBall (min_le_right _ _) hy),
        ← h₁ x (closedBall_subset_closedBall (min_le_left _ _) hx) y
          (closedBall_subset_closedBall (min_le_left _ _) hy)]
    · exact ⟨1, one_pos, fun h => absurd h hq⟩
  choose r hr0 hrc using hr
  obtain ⟨δ, hδ, hδc⟩ := lebesgue_number_lemma_of_metric (c := fun q : C => ball (q : ℂ) (r q)) hC
    (fun q => isOpen_ball) (fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, mem_ball_self (hr0 x)⟩)
  refine ⟨δ, hδ, fun u hu v hv huv => ?_⟩
  obtain ⟨q, hq⟩ := hδc u hu
  have huq : u ∈ ball (q : ℂ) (r q) := hq (mem_ball_self hδ)
  have hvq : v ∈ ball (q : ℂ) (r q) := hq (by rw [mem_ball, dist_comm]; exact huv)
  exact hrc q q.2 u (ball_subset_closedBall huq) v (ball_subset_closedBall hvq)

/-- The same with a positive rational `η` and the norm of the difference. -/
theorem exists_rat_internalMetric_eq_on_compact {F : ℂ → ℂ → ℝ} (hF : IsEuclideanLengthMetric F) {V D : Set ℂ}
    (hV : IsOpen V) (hVD : V ⊆ D) (hD : IsOpen D) {C : Set ℂ} (hC : IsCompact C) (hCV : C ⊆ V) :
    ∃ η : ℚ, 0 < η ∧ ∀ u ∈ C, ∀ v ∈ C, ‖u - v‖ < η →
      internalMetric F D u v = internalMetric F V u v := by
  obtain ⟨δ, hδ, h⟩ := exists_internalMetric_eq_on_compact hF hV hVD hD hC hCV
  obtain ⟨η, hη0, hηδ⟩ := exists_rat_btwn hδ
  refine ⟨η, by exact_mod_cast hη0, fun u hu v hv huv => h u hu v hv ?_⟩
  rw [dist_eq_norm]
  exact huv.trans hηδ

/-- **A3 for multiples of the internal metrics.** Let `F` be a Euclidean length metric, `V i ⊆ D` open sets, `T i k ⊆ V i`
compact for the admissible `(i, k)`, and `c ∈ [0, ∞]`. If `d o = c · internalMetric F D` on `S × S` and
`Fam i o = c · internalMetric F (V i)` on `(S ∩ V i) × (S ∩ V i)`, then `o` lies in the local-agreement event. -/
theorem mem_eventLocalAgreement_of_internalMetric {Ω : Type*} {ι κ : Type*} {S D : Set ℂ} {adm : ι → κ → Prop}
    {T : ι → κ → Set ℂ} {d : Ω → ℂ → ℂ → ℝ≥0∞} {Fam : ι → Ω → ℂ → ℂ → ℝ≥0∞} {o : Ω} {F : ℂ → ℂ → ℝ}
    (hF : IsEuclideanLengthMetric F) (hD : IsOpen D) (V : ι → Set ℂ) (hV : ∀ i, IsOpen (V i))
    (hVD : ∀ i, V i ⊆ D) (hT : ∀ i k, adm i k → IsCompact (T i k) ∧ T i k ⊆ V i) {c : ℝ≥0∞}
    (hd : ∀ u ∈ S, ∀ v ∈ S, d o u v = c * internalMetric F D u v)
    (hFam : ∀ i, ∀ u ∈ S, u ∈ V i → ∀ v ∈ S, v ∈ V i → Fam i o u v = c * internalMetric F (V i) u v) :
    o ∈ eventLocalAgreement S adm T d Fam := by
  intro i k hik
  obtain ⟨hTc, hTV⟩ := hT i k hik
  obtain ⟨η, hη, hη'⟩ := exists_rat_internalMetric_eq_on_compact hF (hV i) (hVD i) hD hTc hTV
  refine ⟨η, hη, fun u hu v hv huT hvT huv => ?_⟩
  rw [hd u hu v hv, hFam i u hu (hTV huT) v hv (hTV hvT), hη' u huT v hvT huv]

/-- **A2 from chains indexed by `ℕ`.** If for all `x, y ∈ S` and real `ε > 0` there is an index `n` such that for every
mesh `δ > 0` there is a chain `m : ℕ → ℂ` of points of `S ∩ K n` from `x` to `y` with steps shorter than `δ` and
`∑ d o (m i) (m (i + 1)) ≤ d o x y + ε`, then `o` lies in the chain event (chains indexed by `Fin (N + 1)` in `S`,
rational tolerances). -/
theorem mem_eventChains_of_natChains {Ω : Type*} {S : Set ℂ} {K : ℕ → Set ℂ} {d : Ω → ℂ → ℂ → ℝ≥0∞} {o : Ω}
    (h : ∀ x ∈ S, ∀ y ∈ S, ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∃ m : ℕ → ℂ,
      m 0 = x ∧ m N = y ∧ (∀ i ≤ N, m i ∈ S ∧ m i ∈ K n) ∧ (∀ i < N, dist (m i) (m (i + 1)) < δ) ∧
      ∑ i ∈ Finset.range N, d o (m i) (m (i + 1)) ≤ d o x y + ENNReal.ofReal ε) :
    o ∈ eventChains S K d := by
  intro x hx y hy ε hε
  obtain ⟨n, hn⟩ := h x hx y hy (ε : ℝ) (by exact_mod_cast hε)
  refine ⟨n, fun δ hδ => ?_⟩
  obtain ⟨N, m, hm0, hmN, hmSK, hmδ, hmsum⟩ := hn (δ : ℝ) (by exact_mod_cast hδ)
  let m' : Fin (N + 1) → S := fun i => ⟨m i, (hmSK i (Nat.lt_succ_iff.1 i.2)).1⟩
  refine ⟨N, m', ?_, ?_, fun i => (hmSK i (Nat.lt_succ_iff.1 i.2)).2, fun i => ?_, ?_⟩
  · simpa [m'] using hm0
  · simpa [m'] using hmN
  · have := hmδ i.1 i.2
    rw [dist_eq_norm] at this
    simpa [m'] using this
  · rw [Finset.sum_range] at hmsum
    simpa [m'] using hmsum

end UnrootedLocal

end HarmonicBalls

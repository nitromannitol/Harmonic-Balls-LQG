import HarmonicBalls.FirstPass.S11m.RootLimit
import HarmonicBalls.FirstPass.S11m.DenseInf

/-!
# The root value as a limit of countable sphere infima (fp-S11m, owner z4)

Route `notes/fp-gaps/CHATGPT-z4-11-12-local-certificate.md` section 3.5 and section 4.3 (step (e)1 of `notes/z4.md`).
The internal distance from the origin `D(0, x; O)` is recovered from the punctured domain `O \ {0}` as the limit of the
infima over the circles `∂B_{s_n}`, `s_n ↘ 0` (`RootLimit.tendsto_sphere_iInf_internalMetric`). The infima over the
circles are replaced by infima over countable dense subsets (`DenseInf.iInf_mem_eq_iInf_mem_of_dense_continuousOn`),
so that the root value is a `limsup` of countable infima, which is measurable in the decoded data.

Deterministic. Input: a nonnegative Euclidean length metric `D` (`HarmonicBalls.IsEuclideanLengthMetric`) and an open
`O ∋ 0` with `D(0, x; O) < ∞`. The continuity of `D(·,·; O)` on `O × O` is
`IsEuclideanLengthMetric.continuousOn_internalMetric_pair`; no further hypothesis is used.
-/

namespace HarmonicBalls.S11m

open Set Metric Filter Topology
open scoped ENNReal

/-- **Root value as a limit of countable sphere infima** (deterministic). Let `D` be a nonnegative Euclidean length metric,
`O` open with `0 ∈ O` and `B_ε(0) ⊆ O`, and `x ∈ O \ {0}` with `D(0, x; O) < ∞`. For a sequence `0 < s_n < ε`, `s_n → 0`,
there are countable subsets `C n` dense in the circle `∂B_{s_n}`, and
`D(0, x; O) = limsup_n ⨅_{y ∈ C n} D(y, x; O \ {0})`. -/
theorem exists_countable_root_limsup {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) {O : Set ℂ} (hO : IsOpen O) (h0 : (0 : ℂ) ∈ O) {ε : ℝ}
    (hball : ball (0 : ℂ) ε ⊆ O) {x : ℂ} (hx : x ∈ O) (hx0 : x ≠ 0) (hfin : internalMetric D O 0 x ≠ ⊤)
    (s : ℕ → ℝ) (hs : Tendsto s atTop (𝓝 0)) (hpos : ∀ n, 0 < s n) (hsε : ∀ n, s n < ε) :
    ∃ C : ℕ → Set ℂ, (∀ n, (C n).Countable ∧ C n ⊆ sphere (0 : ℂ) (s n) ∧ sphere (0 : ℂ) (s n) ⊆ closure (C n)) ∧
      internalMetric D O 0 x = limsup (fun n => ⨅ y ∈ C n, internalMetric D (O \ {0}) y x) atTop := by
  have hcont : ContinuousOn (fun p : ℂ × ℂ => internalMetric D O p.1 p.2) (O ×ˢ O) :=
    hD.continuousOn_internalMetric_pair hnonneg hO
  have hT := tendsto_sphere_iInf_internalMetric hD hO h0 hx0 hfin hcont
  have hs' : Tendsto s atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr ⟨hs, Eventually.of_forall hpos⟩
  have hlim := (hT.comp hs').limsup_eq
  have hO' : IsOpen (O \ {0}) := hO.sdiff isClosed_singleton
  have hx' : x ∈ O \ {0} := ⟨hx, hx0⟩
  have hcontO' : ContinuousOn (fun p : ℂ × ℂ => internalMetric D (O \ {0}) p.1 p.2) ((O \ {0}) ×ˢ (O \ {0})) :=
    hD.continuousOn_internalMetric_pair hnonneg hO'
  have hcontY : ∀ n, ContinuousOn (fun y : ℂ => internalMetric D (O \ {0}) y x) (sphere (0 : ℂ) (s n)) := by
    intro n
    have hsub : sphere (0 : ℂ) (s n) ⊆ O \ {0} := by
      intro y hy
      have hn : ‖y‖ = s n := mem_sphere_zero_iff_norm.mp hy
      have hyb : y ∈ ball (0 : ℂ) ε := mem_ball_zero_iff.mpr (by rw [hn]; exact hsε n)
      refine ⟨hball hyb, fun h => ?_⟩
      have hy0 : y = 0 := h
      rw [hy0, norm_zero] at hn
      linarith [hpos n]
    have hmaps : MapsTo (fun y : ℂ => (y, x)) (sphere (0 : ℂ) (s n)) ((O \ {0}) ×ˢ (O \ {0})) :=
      fun y hy => ⟨hsub hy, hx'⟩
    exact hcontO'.comp (continuousOn_id.prodMk continuousOn_const) hmaps
  choose C hC using fun n => exists_countable_dense_subset_of_secondCountable (sphere (0 : ℂ) (s n))
  refine ⟨C, fun n => ⟨(hC n).2.1, (hC n).1, (hC n).2.2⟩, ?_⟩
  rw [← hlim]
  congr 1
  funext n
  exact iInf_mem_eq_iInf_mem_of_dense_continuousOn (hcontY n) (hC n).1 (hC n).2.2

end HarmonicBalls.S11m

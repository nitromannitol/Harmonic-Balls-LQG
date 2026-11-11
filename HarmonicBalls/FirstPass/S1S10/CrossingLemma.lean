import HarmonicBalls.FirstPass.S1S10.ExceptionalPoints
import HarmonicBalls.FirstPass.S1S10.LocalConnectivity
import HarmonicBalls.FirstPass.S1S10.Punctured
import HarmonicBalls.FirstPass.Frozen.S1S10

/-! # Corrected Lemma 10.5 (deterministic)

Lemma 10.5 of the corrected paper, `lemma:crossing-connected` ([C48]): for a nonempty bounded connected open `G ⊂ ℂ`
with `K = closure G`, if there is a finite set `E` such that every `p ∈ ∂G \ E` has arbitrarily small scales `r` at
which only finitely many components of `G ∩ B_{2r}(p)` have closures meeting both `∂B_{r/3}(p)` and `∂B_{2r}(p)`,
then `K` is locally connected, has no cut points, and every component of `ℂ \ K` has boundary a simple loop.
The last clause is Torhorst's theorem, the frozen external input `TorhorstSimpleLoopFrozen`.
-/

namespace HarmonicBalls

open Set Metric Filter Topology

/-- For `G` open and connected, `closure G \ {a}` is preconnected for each `a ∈ closure G` (no cut points). -/
theorem isPreconnected_closure_diff_singleton {G : Set ℂ} (hGo : IsOpen G) (hGc : IsConnected G) (a : ℂ) :
    IsPreconnected (closure G \ {a}) := by
  by_cases haG : a ∈ G
  · have hG' : IsPreconnected (G \ {a}) := isPreconnected_open_diff_point hGo hGc.isPreconnected haG
    have hdense : G ⊆ closure (G \ {a}) := by
      rw [sdiff_eq]
      exact (dense_compl_singleton a).open_subset_closure_inter hGo
    have hts : closure G \ {a} ⊆ closure (G \ {a}) := fun x hx =>
      closure_minimal hdense isClosed_closure hx.1
    exact hG'.subset_closure (sdiff_subset_sdiff_left subset_closure) hts
  · have hst : G ⊆ closure G \ {a} := fun x hx =>
      ⟨subset_closure hx, fun h => haG (mem_singleton_iff.mp h ▸ hx)⟩
    exact hGc.isPreconnected.subset_closure hst sdiff_subset

/-- Lemma 10.5 (lemma:crossing-connected), corrected as [C48]. Hypotheses: `G` nonempty, bounded,
connected and open; a finite set `E` with the crossing condition on `∂G \ E`. Conclusion: `closure G` is
locally connected, has no cut points, and each component of `ℂ \ closure G` has a simple-loop boundary (Torhorst,
frozen input `TorhorstSimpleLoopFrozen`). -/
theorem firstPass_10_5_corrected {G : Set ℂ} (hGne : G.Nonempty) (hGb : Bornology.IsBounded G)
    (hGo : IsOpen G) (hGc : IsConnected G)
    (hEcross : ∃ E : Set ℂ, E.Finite ∧ ∀ p ∈ frontier G \ E, ∀ δ : ℝ, 0 < δ → ∃ r : ℝ, 0 < r ∧ r < δ ∧
      (crossingComponents (G ∩ ball p (2 * r)) p (r / 3) (2 * r)).Finite)
    (hTor : TorhorstSimpleLoopFrozen) :
    IsLocallyConnectedSet (closure G) ∧ (∀ a : ℂ, ¬ IsCutPoint (closure G) a) ∧
      ∀ C ∈ connectedComponentsIn (closure G)ᶜ, IsSimpleLoop (frontier C) := by
  obtain ⟨E, hE, hcross⟩ := hEcross
  have hKc : IsCompact (closure G) := hGb.isCompact_closure
  have hKconn : IsConnected (closure G) := hGc.closure
  have hKnt : (closure G).Nontrivial := by
    obtain ⟨x, hx⟩ := hGne
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hGo x hx
    have hy : x + (δ / 2 : ℝ) ∈ G := hball (by
      rw [mem_ball, dist_eq_norm]
      simp [abs_of_pos hδ]
      linarith)
    exact ⟨x, subset_closure hx, x + (δ / 2 : ℝ), subset_closure hy, by
      intro h
      have h2 : ((δ / 2 : ℝ) : ℂ) = 0 := by linear_combination -h
      have h3 : (δ / 2 : ℝ) = 0 := Complex.ofReal_eq_zero.mp h2
      linarith⟩
  have hoff : ∀ q ∈ closure G, q ∉ E → ∀ N ∈ 𝓝[closure G] q,
      ∃ V ∈ 𝓝[closure G] q, V ⊆ N ∩ closure G ∧ IsConnected V := by
    intro q hqK hqE N hN
    by_cases hqG : q ∈ G
    · obtain ⟨ε, hε, hεN⟩ := Metric.mem_nhdsWithin_iff.mp hN
      obtain ⟨δ, hδ, hδG⟩ := Metric.isOpen_iff.mp hGo q hqG
      have hs : 0 < min ε δ := lt_min hε hδ
      refine ⟨ball q (min ε δ), mem_nhdsWithin_of_mem_nhds (ball_mem_nhds q hs), ?_,
        (convex_ball q (min ε δ)).isConnected ⟨q, mem_ball_self hs⟩⟩
      intro x hx
      have hxε : x ∈ ball q ε := mem_ball.mpr (lt_of_lt_of_le (mem_ball.mp hx) (min_le_left _ _))
      have hxδ : x ∈ G := hδG (mem_ball.mpr (lt_of_lt_of_le (mem_ball.mp hx) (min_le_right _ _)))
      exact ⟨hεN ⟨hxε, subset_closure hxδ⟩, subset_closure hxδ⟩
    · have hqf : q ∈ frontier G := ⟨hqK, by rwa [hGo.interior_eq]⟩
      exact isLC_at_of_finite_crossings hGo hGc hqK hqG (hcross q ⟨hqf, hqE⟩) hN
  have hLC : IsLocallyConnectedSet (closure G) :=
    isLocallyConnectedSet_of_finite_exceptions hKc hKconn hE hoff
  have hnocut : ∀ a : ℂ, ¬ IsCutPoint (closure G) a := fun a ⟨haK, hnp⟩ =>
    hnp (isPreconnected_closure_diff_singleton hGo hGc a)
  exact ⟨hLC, hnocut, hTor (closure G) hKc hKconn hKnt hLC hnocut⟩

end HarmonicBalls

import HarmonicBalls.Defs.Geometry

/-! # Frozen external inputs for Section 10

Each `def` below is a classical planar-topology fact used by the corrected Lemma 10.5 ([C48]). It is frozen as an
explicit hypothesis, not proved here, and it is not a statement about this paper's clusters or harmonic balls.
-/

namespace HarmonicBalls

/-- FROZEN. Torhorst's theorem in the form printed by the paper for the corrected Lemma 10.5: a
continuum `K ⊂ ℂ` (compact, connected, more than one point) which is locally connected and has no cut points
has, for each connected component `C` of `ℂ \ K`, a boundary `∂C` which is a simple loop.

Source: Torhorst (1931); Jolivet, Loridant, Luo, "A numerical scale for non-locally connected planar continua",
arXiv:1411.6776v1, Theorem 3.1, printed p. 6 (Topology Appl. 202 (2016) 21-39), the locator cited by the paper at
the proof of [C48]. Standard; locator pending source-check.
Used by: firstPass_10_5_corrected, firstPass_10_6. Truth check TRUE: Torhorst's
conclusion for a nondegenerate locally connected plane continuum without cut points. Source: Jolivet-Loridant-Luo, arXiv:1411.6776v1, p. 6, Theorem 3.1. -/
def TorhorstSimpleLoopFrozen : Prop :=
  ∀ K : Set ℂ, IsCompact K → IsConnected K → K.Nontrivial → IsLocallyConnectedSet K →
    (∀ a : ℂ, ¬ IsCutPoint K a) → ∀ C ∈ connectedComponentsIn Kᶜ, IsSimpleLoop (frontier C)

end HarmonicBalls

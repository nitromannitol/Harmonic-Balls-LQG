import HarmonicBalls.FirstPass.S11d.SmoothCutoff
import HarmonicBalls.FirstPass.S11d.ShiftBound
import HarmonicBalls.Defs.Geometry

/-!
# Proposition 11.9, the geometric set-up of the shift

FIRST-PASS NEW. The deterministic set-up of `prop:mass-diam-gen` (corrected paper, lines 3110-3131): closed dyadic squares
`S₁ ⊆ int S₂ ⊆ S₂ ⊆ U`; the open set `O` with `closure(V \ S₂) ⊆ O` and `closure O ⊆ W \ S₁`; and a smooth cutoff `φ`
with `φ = 1` on `O` and support in `W \ S₁`.
-/

namespace HarmonicBalls

open Set

/-- A closed dyadic square is closed. -/
theorem isClosed_of_isClosedDyadicSquare {S : Set ℂ} (h : IsClosedDyadicSquare S) : IsClosed S := by
  obtain ⟨n, j, k, rfl⟩ := h
  unfold closedDyadicSquare
  exact (isClosed_Icc.preimage Complex.continuous_re).inter (isClosed_Icc.preimage Complex.continuous_im)

/-- The geometric set-up of the shift: the open set `O` and the smooth cutoff `φ`. -/
theorem shift_geometry {V W S1 S2 : Set ℂ} (hVb : Bornology.IsBounded V)
    (hWo : IsOpen W) (hWb : Bornology.IsBounded W) (hVW : closure V ⊆ W)
    (hS1 : IsClosedDyadicSquare S1) (hS2 : IsClosedDyadicSquare S2) (hS1S2 : S1 ⊆ interior S2) :
    ∃ O : Set ℂ, ∃ φ : ℂ → ℝ, IsOpen O ∧ closure (V \ S2) ⊆ O ∧ closure O ⊆ W \ S1 ∧
      ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ W \ S1 ∧
      (∀ z, 0 ≤ φ z ∧ φ z ≤ 1) ∧ ∀ z ∈ O, φ z = 1 := by
  have hS2c : IsClosed S2 := isClosed_of_isClosedDyadicSquare hS2
  have hS1c : IsClosed S1 := isClosed_of_isClosedDyadicSquare hS1
  -- the closure of `V \ S₂` avoids `S₁` (since `S₁ ⊆ int S₂` and `V \ S₂` avoids `int S₂`)
  have hdisj : Disjoint (V \ S2) (interior S2) :=
    Set.disjoint_left.mpr fun x hx hy => hx.2 (interior_subset hy)
  have hcl_disj : Disjoint (closure (V \ S2)) (interior S2) := hdisj.closure_left isOpen_interior
  have hKW : closure (V \ S2) ⊆ W := (closure_mono sdiff_subset).trans hVW
  have hKS1 : closure (V \ S2) ⊆ W \ S1 := by
    intro x hx
    refine ⟨hKW hx, fun hxS1 => ?_⟩
    exact Set.disjoint_left.mp hcl_disj hx (hS1S2 hxS1)
  have hKc : IsCompact (closure (V \ S2)) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure (hVb.subset sdiff_subset).closure
  have hWS1o : IsOpen (W \ S1) := hWo.sdiff hS1c
  obtain ⟨O, hOo, hKO, hclO⟩ := exists_open_between_of_compact hKc hWS1o hKS1
  have hclOc : IsCompact (closure O) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure (hWb.subset (hclO.trans sdiff_subset))
  obtain ⟨φ, hφs, hφc, hφsup, hφ01, hφ1⟩ :=
    exists_smooth_cutoff hclOc hWS1o hclO (hWb.subset sdiff_subset)
  exact ⟨O, φ, hOo, hKO, hclO, hφs, hφc, hφsup, hφ01, fun z hz => hφ1 z (subset_closure hz)⟩

end HarmonicBalls

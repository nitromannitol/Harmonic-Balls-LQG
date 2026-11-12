import HarmonicBalls.FirstPass.Frozen.S1S10
import LatticeProb.Topology.BoundaryAccessRay

/-!
# Torhorst's theorem, derived

The frozen input `TorhorstSimpleLoopFrozen` (FirstPass/Frozen/S1S10.lean; Torhorst 1921, Jolivet-Loridant-Luo,
arXiv:1411.6776v1, Theorem 3.1) is a theorem: the frontier of every complementary component of a nondegenerate
locally connected plane continuum without cut points is a simple closed curve.

The proof is `LatticeProb.Topology.torhorstSimpleLoop` (Lattice-Probability,
LatticeProb/Topology/BoundaryAccessRay.lean). The plane-topology definitions of this repository
(`IsSimpleLoop`, `IsLocallyConnectedSet`, `IsCutPoint`, `connectedComponentsIn`; Definitions 10.1-10.4, file
Defs/Geometry.lean) have the same bodies as those of Lattice-Probability, so each bridge below is definitional.
-/

namespace HarmonicBalls

/-- Bridge: simple loops (Definition 10.1) agree with those of Lattice-Probability. -/
theorem isSimpleLoop_iff_latticeProb (Γ : Set ℂ) :
    IsSimpleLoop Γ ↔ LatticeProb.Topology.IsSimpleLoop Γ :=
  Iff.rfl

/-- Bridge: locally connected sets (Definition 10.3) agree with those of Lattice-Probability. -/
theorem isLocallyConnectedSet_iff_latticeProb (X : Set ℂ) :
    IsLocallyConnectedSet X ↔ LatticeProb.Topology.IsLocallyConnectedSet X :=
  Iff.rfl

/-- Bridge: cut points (Definition 10.4) agree with those of Lattice-Probability. -/
theorem isCutPoint_iff_latticeProb (A : Set ℂ) (a : ℂ) :
    IsCutPoint A a ↔ LatticeProb.Topology.IsCutPoint A a :=
  Iff.rfl

/-- Bridge: the set of connected components of a set agrees with that of Lattice-Probability. -/
theorem connectedComponentsIn_eq_latticeProb {α : Type*} [TopologicalSpace α] (F : Set α) :
    connectedComponentsIn F = LatticeProb.Topology.connectedComponentsIn F :=
  rfl

/-- Bridge: the frozen input is the Lattice-Probability statement of Torhorst's theorem. -/
theorem torhorstSimpleLoopFrozen_iff_latticeProb :
    TorhorstSimpleLoopFrozen ↔ LatticeProb.Topology.TorhorstSimpleLoop :=
  Iff.rfl

/-- **Torhorst's theorem** (the frozen input `TorhorstSimpleLoopFrozen` holds). The frontier of every
complementary component of a nondegenerate locally connected continuum `K ⊆ ℂ` without cut points is a simple
closed curve. -/
theorem torhorstSimpleLoopFrozen_holds : TorhorstSimpleLoopFrozen :=
  torhorstSimpleLoopFrozen_iff_latticeProb.mpr LatticeProb.Topology.torhorstSimpleLoop

end HarmonicBalls

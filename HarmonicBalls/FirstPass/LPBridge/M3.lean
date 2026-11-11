import HarmonicBalls.Defs.Geometry
import HarmonicBalls.Defs.Green
import HarmonicBalls.Draft.Section2
import HarmonicBalls.FirstPass.Frozen.S11c
import HarmonicBalls.FirstPass.Frozen.S1S10
import LatticeProb.Topology.PlaneTopology
import LatticeProb.Analysis.PlanarGreen

/-!
# Bridge to the staged plane-topology and planar-Green definitions

Each definition of `LatticeProb.Topology` (file `HarmonicBalls/LPStage/PlaneTopology.lean`) and of
`LatticeProb.Analysis` (file `HarmonicBalls/LPStage/PlanarGreen.lean`) is the same object as the corresponding
`HarmonicBalls` definition: the bodies agree, so each equality holds by `rfl`. The staged names differ from the
`HarmonicBalls` names only for `newtonKernel`, `newtonKernelEReal` (renamed `planarNewtonKernel`,
`planarNewtonKernelEReal`, since `elliptic_regularity` already has a `PDE.newtonKernel` of another type) and
`TorhorstSimpleLoopFrozen` (renamed `TorhorstSimpleLoop`).
-/

namespace HarmonicBalls.LPBridge

open Set

theorem isSimpleLoop_eq : HarmonicBalls.IsSimpleLoop = LatticeProb.Topology.IsSimpleLoop := rfl

theorem isLocallyConnectedSet_eq :
    HarmonicBalls.IsLocallyConnectedSet = LatticeProb.Topology.IsLocallyConnectedSet := rfl

theorem isCutPoint_eq : HarmonicBalls.IsCutPoint = LatticeProb.Topology.IsCutPoint := rfl

theorem connectedComponentsIn_eq {α : Type*} [TopologicalSpace α] (F : Set α) :
    HarmonicBalls.connectedComponentsIn F = LatticeProb.Topology.connectedComponentsIn F := rfl

theorem isClosedRectangle_eq : HarmonicBalls.IsClosedRectangle = LatticeProb.Topology.IsClosedRectangle := rfl

theorem closedDyadicSquare_eq : HarmonicBalls.closedDyadicSquare = LatticeProb.Topology.closedDyadicSquare := rfl

theorem isClosedDyadicSquare_eq :
    HarmonicBalls.IsClosedDyadicSquare = LatticeProb.Topology.IsClosedDyadicSquare := rfl

theorem isSmoothBoundedOpen_eq :
    HarmonicBalls.IsSmoothBoundedOpen = LatticeProb.Topology.IsSmoothBoundedOpen := rfl

theorem torhorstSimpleLoop_eq :
    HarmonicBalls.TorhorstSimpleLoopFrozen = LatticeProb.Topology.TorhorstSimpleLoop := rfl

theorem newtonKernel_eq : HarmonicBalls.newtonKernel = LatticeProb.Analysis.planarNewtonKernel := rfl

theorem newtonKernelEReal_eq :
    HarmonicBalls.newtonKernelEReal = LatticeProb.Analysis.planarNewtonKernelEReal := rfl

theorem isHarmonicMinorant_eq : HarmonicBalls.IsHarmonicMinorant = LatticeProb.Analysis.IsHarmonicMinorant := rfl

theorem greatestHarmonicMinorant_eq :
    HarmonicBalls.greatestHarmonicMinorant = LatticeProb.Analysis.greatestHarmonicMinorant := rfl

theorem greenFunction_eq : HarmonicBalls.greenFunction = LatticeProb.Analysis.greenFunction := rfl

end HarmonicBalls.LPBridge

import HarmonicBalls.Proofs.Sec11.IntermediateSquareCore
import LatticeProb.Topology.ConnectedThickening

/-! # Connected neighborhoods of compact cores -/

namespace HarmonicBalls
open Set Metric

/-- A compact connected planar core has a connected open neighborhood whose
closure is compact and lies inside any prescribed open neighborhood. -/
theorem exists_connected_precompact_neighborhood {C U : Set ℂ}
    (hC : IsCompact C) (hconn : IsConnected C) (hU : IsOpen U)
    (hCU : C ⊆ U) :
    ∃ V : Set ℂ, IsOpen V ∧ IsConnected V ∧ C ⊆ V ∧
      IsCompact (closure V) ∧ closure V ⊆ U := by
  obtain ⟨r, hr, hrU⟩ := hC.exists_cthickening_subset_open hU hCU
  refine ⟨thickening r C, isOpen_thickening,
    LatticeProb.Topology.isConnected_thickening hconn hr,
    self_subset_thickening hr C, ?_, ?_⟩
  · exact hC.cthickening.of_isClosed_subset isClosed_closure
      (closure_thickening_subset_cthickening r C)
  · exact (closure_thickening_subset_cthickening r C).trans hrU

/-- A grid square is closed in the plane. -/
theorem isClosed_complexGridSquare {N : ℕ} (a : ℂ) (r : ℝ)
    (i : Fin N × Fin N) : IsClosed (complexGridSquare a r i) := by
  change IsClosed {z : ℂ | (i.1.val : ℝ) * r ≤ z.re - a.re ∧
    z.re - a.re ≤ ((i.1.val : ℝ) + 1) * r ∧
    (i.2.val : ℝ) * r ≤ z.im - a.im ∧
    z.im - a.im ≤ ((i.2.val : ℝ) + 1) * r}
  have hre : Continuous (fun z : ℂ => z.re - a.re) := by fun_prop
  have him : Continuous (fun z : ℂ => z.im - a.im) := by fun_prop
  exact (isClosed_le continuous_const hre).inter ((isClosed_le hre continuous_const).inter
    ((isClosed_le continuous_const him).inter (isClosed_le him continuous_const)))

/-- A compact connected core disjoint from finitely many closed protected
sets has a connected precompact neighborhood avoiding all of them. -/
theorem exists_connected_precompact_neighborhood_avoiding {ι : Type*} [Finite ι]
    {C U : Set ℂ} (S : ι → Set ℂ) (hC : IsCompact C)
    (hconn : IsConnected C) (hU : IsOpen U) (hCU : C ⊆ U)
    (hS : ∀ i, IsClosed (S i)) (hdisj : Disjoint (⋃ i, S i) C) :
    ∃ V : Set ℂ, IsOpen V ∧ IsConnected V ∧ C ⊆ V ∧
      IsCompact (closure V) ∧ closure V ⊆ U ∧
      Disjoint (⋃ i, S i) (closure V) := by
  have hopen : IsOpen (U \ ⋃ i, S i) :=
    hU.inter (isClosed_iUnion_of_finite hS).isOpen_compl
  have hsub : C ⊆ U \ ⋃ i, S i := by
    intro x hx
    exact ⟨hCU hx, fun hs => Set.disjoint_left.mp hdisj hs hx⟩
  obtain ⟨V, hv, hvc, hCV, hvcompact, hvsub⟩ :=
    exists_connected_precompact_neighborhood hC hconn hopen hsub
  refine ⟨V, hv, hvc, hCV, hvcompact, ?_, ?_⟩
  · exact hvsub.trans sdiff_subset
  · exact disjoint_left.mpr (fun x hxS hxV => (hvsub hxV).2 hxS)

/-- The square-removal core has a suitable neighborhood once its
connectedness is established. -/
theorem dyadic_intermediate_core_neighborhood {N : ℕ} (a : ℂ) (r : ℝ)
    (hr : 0 < r) (j : Fin 4) (K U : Set ℂ) (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U)
    (hHK : ∀ i : {i : Fin N × Fin N // squareParity i = j},
      complexIntermediateGridSquare a r i.1 ⊆ K)
    (hconn : IsConnected (K \ ⋃ i : {i : Fin N × Fin N // squareParity i = j},
      interior (complexIntermediateGridSquare a r i.1))) :
    ∃ V : Set ℂ, IsOpen V ∧ IsConnected V ∧
      (K \ ⋃ i : {i : Fin N × Fin N // squareParity i = j},
        interior (complexIntermediateGridSquare a r i.1)) ⊆ V ∧
      IsCompact (closure V) ∧ closure V ⊆ U ∧
      Disjoint (⋃ i : {i : Fin N × Fin N // squareParity i = j},
        complexGridSquare a r i.1) (closure V) := by
  obtain ⟨hc, _, _, hd⟩ := dyadic_intermediate_compact_core a r hr j K hK hHK
  exact exists_connected_precompact_neighborhood_avoiding
    (fun i : {i : Fin N × Fin N // squareParity i = j} => complexGridSquare a r i.1)
    hc hconn hU (sdiff_subset.trans hKU) (fun i => isClosed_complexGridSquare a r i.1) hd

/-- The core contraction can use an outer open neighborhood avoiding both
the protected squares and an arbitrary closed observation set. -/
theorem dyadic_intermediate_core_shift_neighborhoods {N : ℕ} (a : ℂ) (r : ℝ)
    (hr : 0 < r) (j : Fin 4) (K W F : Set ℂ) (hK : IsCompact K)
    (hW : IsOpen W) (hKW : K ⊆ W) (hF : IsClosed F) (hKF : Disjoint K F)
    (hHK : ∀ i : {i : Fin N × Fin N // squareParity i = j},
      complexIntermediateGridSquare a r i.1 ⊆ K)
    (hconn : IsConnected (K \ ⋃ i : {i : Fin N × Fin N // squareParity i = j},
      interior (complexIntermediateGridSquare a r i.1))) :
    ∃ V T : Set ℂ, IsOpen V ∧ IsConnected V ∧
      (K \ ⋃ i : {i : Fin N × Fin N // squareParity i = j},
        interior (complexIntermediateGridSquare a r i.1)) ⊆ V ∧
      IsCompact (closure V) ∧ IsOpen T ∧ closure V ⊆ T ∧ T ⊆ W ∧
      Disjoint T F ∧ Disjoint T (⋃ i : {i : Fin N × Fin N // squareParity i = j},
        complexGridSquare a r i.1) := by
  let S : Set ℂ := ⋃ i : {i : Fin N × Fin N // squareParity i = j},
    complexGridSquare a r i.1
  have hSc : IsClosed S := isClosed_iUnion_of_finite
    (fun i => isClosed_complexGridSquare a r i.1)
  have hW' : IsOpen (W \ F) := hW.inter hF.isOpen_compl
  have hKW' : K ⊆ W \ F := by
    intro x hx
    exact ⟨hKW hx, fun hxF => disjoint_left.mp hKF hx hxF⟩
  obtain ⟨V, hVo, hVc, hCV, hVcompact, hVW, hVS⟩ :=
    dyadic_intermediate_core_neighborhood a r hr j K (W \ F) hK hW' hKW' hHK hconn
  refine ⟨V, (W \ F) \ S, hVo, hVc, hCV, hVcompact,
    hW'.inter hSc.isOpen_compl, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact ⟨hVW hx, fun hxS => disjoint_left.mp hVS hxS hx⟩
  · exact sdiff_subset.trans sdiff_subset
  · exact disjoint_left.mpr (fun x hx hxF => hx.1.2 hxF)
  · exact disjoint_left.mpr (fun x hx hxS => hx.2 hxS)

#print axioms exists_connected_precompact_neighborhood_avoiding
#print axioms dyadic_intermediate_core_neighborhood
#print axioms dyadic_intermediate_core_shift_neighborhoods
end HarmonicBalls

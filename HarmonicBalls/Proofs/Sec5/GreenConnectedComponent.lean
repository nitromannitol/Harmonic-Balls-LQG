import HarmonicBalls.Proofs.Sec5.GeneralDomainInteriorGreen
import HarmonicBalls.Proofs.Sec5.IrregularLeastSupersolution

/-! # Green functions on connected components

The Green function with pole in one component vanishes on all other components.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set InnerProductSpace Filter

open Classical in
/-- Gluing harmonic functions on disjoint open sets preserves harmonicity. -/
theorem harmonicOnNhd_piecewise_of_disjoint_open {V W : Set ℂ}
    (hV : IsOpen V) (hW : IsOpen W) (hdis : Disjoint V W)
    {f g : ℂ → ℝ} (hf : HarmonicOnNhd f V) (hg : HarmonicOnNhd g W) :
    HarmonicOnNhd (fun x => if x ∈ V then f x else g x) (V ∪ W) := by
  classical
  intro x hx
  rcases hx with hx | hx
  · apply (harmonicAt_congr_nhds ?_).2 (hf x hx)
    filter_upwards [hV.mem_nhds hx] with y hy
    simp [hy]
  · apply (harmonicAt_congr_nhds ?_).2 (hg x hx)
    filter_upwards [hW.mem_nhds hx] with y hy
    have hyV : y ∉ V := fun h => Set.disjoint_left.mp hdis h hy
    simp [hyV]

/-- Green functions vanish on a component disjoint from the pole. -/
theorem greenFunction_eq_zero_of_disjoint_open_components
    {V W : Set ℂ} (hV : IsOpen V) (hW : IsOpen W)
    (hdis : Disjoint V W) (hUb : Bornology.IsBounded (V ∪ W))
    {z x : ℂ} (hz : z ∈ V) (hx : x ∈ W) :
    greenFunction (V ∪ W) z x = 0 := by
  classical
  have hxz : x ≠ z := fun h => Set.disjoint_left.mp hdis (h ▸ hz) hx
  obtain ⟨r, hr⟩ := hUb.subset_closedBall z
  let c : ℝ := -(2 * Real.pi)⁻¹ * Real.log r
  let h : ℂ → ℝ := fun y => if y ∈ V then c else newtonKernel z y
  have hmin : IsHarmonicMinorant (V ∪ W) (newtonKernelEReal z) h := by
    constructor
    · apply harmonicOnNhd_piecewise_of_disjoint_open hV hW hdis
      · exact harmonicOnNhd_const c
      · intro y hy
        apply harmonicAt_newtonKernel
        intro heq
        exact Set.disjoint_left.mp hdis (heq ▸ hz) hy
    · intro y hy
      rcases hy with hy | hy
      · have hc := (isHarmonicMinorant_const_newtonKernelEReal hr).2 y (Or.inl hy)
        simpa [h, hy, c] using hc
      · have hyV : y ∉ V := fun hyV => Set.disjoint_left.mp hdis hyV hy
        have hyz : y ≠ z := fun e => Set.disjoint_left.mp hdis (e ▸ hz) hy
        simp [h, hyV, newtonKernelEReal, hyz]
  have hxV : x ∉ V := fun h => Set.disjoint_left.mp hdis h hx
  have hl : (newtonKernel z x : EReal) ≤
      greatestHarmonicMinorant (V ∪ W) (newtonKernelEReal z) x := by
    simpa [h, hxV] using hmin.le_greatestHarmonicMinorant x
  have hu : greatestHarmonicMinorant (V ∪ W) (newtonKernelEReal z) x ≤
      (newtonKernel z x : EReal) := by
    simpa [newtonKernelEReal, hxz] using
      (greatestHarmonicMinorant_le (O := V ∪ W) (u := newtonKernelEReal z) (Or.inr hx))
  have heq := le_antisymm hu hl
  simp [greenFunction, hz, hx, Ne.symm hxz, heq]

/-- The greatest harmonic minorant on one member of a disjoint open union
is unaffected by the other member, provided it has a minorant there. -/
theorem greatestHarmonicMinorant_eq_of_disjoint_open_union
    {V W : Set ℂ} (hV : IsOpen V) (hW : IsOpen W) (hdis : Disjoint V W)
    {u : ℂ → EReal} {g : ℂ → ℝ} (hg : IsHarmonicMinorant W u g)
    {x : ℂ} (hx : x ∈ V) :
    greatestHarmonicMinorant (V ∪ W) u x = greatestHarmonicMinorant V u x := by
  classical
  apply le_antisymm
  · apply iSup₂_le
    intro f hf
    have hfV : IsHarmonicMinorant V u f :=
      ⟨hf.1.mono subset_union_left, fun y hy => hf.2 y (Or.inl hy)⟩
    exact hfV.le_greatestHarmonicMinorant x
  · apply iSup₂_le
    intro f hf
    let h : ℂ → ℝ := fun y => if y ∈ V then f y else g y
    have hh : IsHarmonicMinorant (V ∪ W) u h := by
      refine ⟨harmonicOnNhd_piecewise_of_disjoint_open hV hW hdis hf.1 hg.1, ?_⟩
      intro y hy
      rcases hy with hy | hy
      · simpa [h, hy] using hf.2 y hy
      · have hyV : y ∉ V := fun hv => Set.disjoint_left.mp hdis hv hy
        simpa [h, hyV] using hg.2 y hy
    simpa [h, hx] using hh.le_greatestHarmonicMinorant x

/-- Inside the pole's component, the Green function is unchanged by adjoining
other disjoint open components. -/
theorem greenFunction_eq_of_disjoint_open_union
    {V W : Set ℂ} (hV : IsOpen V) (hW : IsOpen W)
    (hdis : Disjoint V W) (hUb : Bornology.IsBounded (V ∪ W))
    {z x : ℂ} (hz : z ∈ V) (hx : x ∈ V) :
    greenFunction (V ∪ W) z x = greenFunction V z x := by
  obtain ⟨r, hr⟩ := hUb.subset_closedBall z
  have hg := isHarmonicMinorant_const_newtonKernelEReal
    (show W ⊆ closedBall z r from subset_union_right.trans hr)
  have heq := greatestHarmonicMinorant_eq_of_disjoint_open_union hV hW hdis hg hx
  by_cases hzx : z = x
  · subst x
    simp [greenFunction_self]
  · simp [greenFunction, hz, hx, hzx, heq]

/-- The complement in an open planar set of a connected component is open. -/
theorem IsOpen.sdiff_connectedComponentIn {U : Set ℂ} (hU : IsOpen U) (z : ℂ) :
    IsOpen (U \ connectedComponentIn U z) := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have hxC : x ∈ connectedComponentIn U x := mem_connectedComponentIn hx.1
  filter_upwards [(hU.connectedComponentIn (x := x)).mem_nhds hxC] with y hy
  refine ⟨connectedComponentIn_subset U x hy, ?_⟩
  intro hyz
  have heq : connectedComponentIn U x = connectedComponentIn U z :=
    (connectedComponentIn_eq hy).trans (connectedComponentIn_eq hyz).symm
  exact hx.2 (heq ▸ hxC)

/-- The Green function of a bounded open domain vanishes at points outside
the connected component containing its pole. -/
theorem greenFunction_eq_zero_of_not_mem_connectedComponentIn
    {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {z x : ℂ} (hz : z ∈ U) (hx : x ∉ connectedComponentIn U z) :
    greenFunction U z x = 0 := by
  by_cases hxU : x ∈ U
  · have hsplit : connectedComponentIn U z ∪ (U \ connectedComponentIn U z) = U := by
      exact union_sdiff_cancel (connectedComponentIn_subset U z)
    have hh := greenFunction_eq_zero_of_disjoint_open_components hU.connectedComponentIn
      (IsOpen.sdiff_connectedComponentIn hU z) disjoint_sdiff_right
      (hsplit.symm ▸ hUb) (mem_connectedComponentIn hz) (show x ∈ U \ connectedComponentIn U z from ⟨hxU, hx⟩)
    simpa only [hsplit] using hh
  · exact greenFunction_of_notMem_right hxU z

/-- The Green function restricted to the component of its pole is the Green
function of that component. -/
theorem greenFunction_eq_connectedComponentIn
    {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {z x : ℂ} (hz : z ∈ U) (hx : x ∈ connectedComponentIn U z) :
    greenFunction U z x = greenFunction (connectedComponentIn U z) z x := by
  have hsplit : connectedComponentIn U z ∪ (U \ connectedComponentIn U z) = U :=
    union_sdiff_cancel (connectedComponentIn_subset U z)
  have hh := greenFunction_eq_of_disjoint_open_union hU.connectedComponentIn
    (IsOpen.sdiff_connectedComponentIn hU z) disjoint_sdiff_right
    (hsplit.symm ▸ hUb) (mem_connectedComponentIn hz) hx
  simpa only [hsplit] using hh

/-- The Green functions agree everywhere when the domain is replaced by the
connected component of the pole. -/
theorem greenFunction_eq_connectedComponentIn_all
    {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {z : ℂ} (hz : z ∈ U) :
    greenFunction U z = greenFunction (connectedComponentIn U z) z := by
  funext x
  by_cases hx : x ∈ connectedComponentIn U z
  · exact greenFunction_eq_connectedComponentIn hU hUb hz hx
  · rw [greenFunction_eq_zero_of_not_mem_connectedComponentIn hU hUb hz hx,
      greenFunction_of_notMem_right hx]

/-- Restriction to the pole component preserves admissibility of a
supersolution on the original domain. -/
theorem supersolutionsOn_subset_connectedComponentIn
    {μ : Measure ℂ} {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} :
    supersolutionsOn μ U z t ⊆ supersolutionsOn μ (connectedComponentIn U z) z t := by
  intro w hw
  have hsub := connectedComponentIn_subset U z
  refine ⟨hw.1.mono (closure_mono hsub), hw.2.1.mono_set hsub, ?_⟩
  intro x hx hxz
  rw [← greenFunction_eq_connectedComponentIn_all hU hUb hz]
  exact hw.2.2 x (closure_mono hsub hx) hxz

/-- The cluster of the pole component is contained in the cluster on the
whole bounded open domain. No least-supersolution admissibility is needed. -/
theorem clusterOn_connectedComponentIn_subset
    {μ : Measure ℂ} {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 ≤ t) :
    clusterOn μ (connectedComponentIn U z) z t ⊆ clusterOn μ U z t := by
  intro x hx
  refine ⟨connectedComponentIn_subset U z hx.1, ?_⟩
  by_cases hxz : x = z
  · exact Or.inl hxz
  · have h := hx.2.resolve_left hxz
    have hv : leastSupersolutionOn μ (connectedComponentIn U z) z t x ≤
        leastSupersolutionOn μ U z t x := by
      apply le_csInf
      · exact ⟨_, ⟨0, zero_mem_supersolutionsOn (μ := μ) hUb ht, rfl⟩⟩
      · rintro _ ⟨w, hw, rfl⟩
        exact leastSupersolutionOn_le_of_mem
          (supersolutionsOn_subset_connectedComponentIn hU hUb hz hw) (subset_closure hx.1) hxz
    right
    rw [greenFunction_eq_connectedComponentIn_all hU hUb hz]
    exact h.trans_le hv

/-- A general-domain cluster lies in the connected component containing its
pole, without assuming that the least supersolution is admissible. -/
theorem clusterOn_subset_connectedComponentIn
    {μ : Measure ℂ} {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 ≤ t) :
    clusterOn μ U z t ⊆ connectedComponentIn U z := by
  intro x hx
  by_contra hxC
  have hxz : x ≠ z := by
    intro h
    subst x
    exact hxC (mem_connectedComponentIn hz)
  have hG := greenFunction_eq_zero_of_not_mem_connectedComponentIn hU hUb hz hxC
  have hv := leastSupersolutionOn_le_of_mem (zero_mem_supersolutionsOn (μ := μ) hUb ht)
    (subset_closure hx.1) hxz
  rcases hx.2 with hx | hx
  · exact hxz hx
  · have hxpos : 0 < leastSupersolutionOn μ U z t x := by simpa [hG] using hx
    exact (not_lt_of_ge hv) hxpos

#print axioms greenFunction_eq_connectedComponentIn_all
#print axioms supersolutionsOn_subset_connectedComponentIn
#print axioms clusterOn_connectedComponentIn_subset
#print axioms greatestHarmonicMinorant_eq_of_disjoint_open_union
#print axioms greenFunction_eq_of_disjoint_open_union
#print axioms greenFunction_eq_connectedComponentIn
#print axioms IsOpen.sdiff_connectedComponentIn
#print axioms greenFunction_eq_zero_of_not_mem_connectedComponentIn
#print axioms clusterOn_subset_connectedComponentIn
#print axioms harmonicOnNhd_piecewise_of_disjoint_open
#print axioms greenFunction_eq_zero_of_disjoint_open_components

end HarmonicBalls

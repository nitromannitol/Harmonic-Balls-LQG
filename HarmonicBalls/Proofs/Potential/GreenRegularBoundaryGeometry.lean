import HarmonicBalls.Proofs.Sec5.DiscSupportedBoundary
import HarmonicBalls.Proofs.Sec5.GreenConnectedComponent
import HarmonicBalls.Proofs.Sec5.PuncturedDiscContact
import Mathlib.Geometry.Euclidean.Triangle

/-! # Green boundary comparison

These results use the potential-theoretic infrastructure of Leonardo Bonanno.
-/

namespace HarmonicBalls

open Filter Set Metric Classical
open scoped Topology

/-- A Green boundary limit transfers to a subdomain at a shared boundary
point. The comparison does not require the subdomain to be open. -/
theorem tendsto_greenFunction_zero_of_subset_of_boundary_limit
    {V W : Set ℂ} {z y : ℂ} (hVW : V ⊆ W)
    (hWb : Bornology.IsBounded W)
    (hlim : Tendsto (greenFunction W z) (𝓝[W] y) (𝓝 0)) :
    Tendsto (greenFunction V z) (𝓝[V] y) (𝓝 0) := by
  have hlim' : Tendsto (greenFunction W z) (𝓝[V] y) (𝓝 0) :=
    hlim.mono_left (nhdsWithin_mono y hVW)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim'
    (Filter.Eventually.of_forall (greenFunction_nonneg (hWb.subset hVW) z))
    (Filter.Eventually.of_forall (Section6.greenFunction_le_of_subset hVW hWb z))

/-- Since the Green function vanishes outside its domain, a limit within the
 domain is also an ambient limit. -/
theorem tendsto_greenFunction_nhds_of_nhdsWithin {U : Set ℂ} {z y : ℂ}
    (hlim : Tendsto (greenFunction U z) (𝓝[U] y) (𝓝 0)) :
    Tendsto (greenFunction U z) (𝓝 y) (𝓝 0) := by
  have hout : Tendsto (greenFunction U z) (𝓝[Uᶜ] y) (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (greenFunction_of_notMem_right hx z).symm
  have h : Tendsto (greenFunction U z) (𝓝[U ∪ Uᶜ] y) (𝓝 0) := by
    rw [nhdsWithin_union]
    exact tendsto_sup.2 ⟨hlim, hout⟩
  simpa only [union_compl_self, nhdsWithin_univ] using h

/-- Away from the pole, a Green boundary limit is equivalent to the greatest
harmonic minorant attaining the Newtonian kernel at the boundary in the
limit from within the domain. -/
theorem tendsto_greenFunction_zero_iff_greatestHarmonicMinorant
    {U : Set ℂ} {z y : ℂ} (hz : z ∈ U) (hyz : y ≠ z) :
    Tendsto (greenFunction U z) (𝓝[U] y) (𝓝 0) ↔
      Tendsto (fun x => (greatestHarmonicMinorant U (newtonKernelEReal z) x).toReal)
        (𝓝[U] y) (𝓝 (newtonKernel z y)) := by
  have hN : Tendsto (newtonKernel z) (𝓝[U] y) (𝓝 (newtonKernel z y)) :=
    ((harmonicAt_newtonKernel hyz).1.continuousAt.tendsto).mono_left nhdsWithin_le_nhds
  have heq : ∀ᶠ x in 𝓝[U] y,
      greenFunction U z x = newtonKernel z x -
        (greatestHarmonicMinorant U (newtonKernelEReal z) x).toReal := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds hyz)] with x hx hxz
    simp [greenFunction, hz, hx, Ne.symm hxz]
  constructor
  · intro hG
    have hlim := hN.sub hG
    simp only [sub_zero] at hlim
    apply hlim.congr'
    filter_upwards [heq] with x hx
    linarith
  · intro hminor
    have hlim := hN.sub hminor
    simp only [sub_self] at hlim
    apply hlim.congr'
    filter_upwards [heq] with x hx
    exact hx.symm

/-- A harmonic minorant approaching the Newtonian kernel at a boundary point
is a barrier for the Green function there. -/
theorem tendsto_greenFunction_zero_of_harmonic_minorant
    {U : Set ℂ} (hUb : Bornology.IsBounded U) {z y : ℂ} (hz : z ∈ U) (hyz : y ≠ z)
    {q : ℂ → ℝ} (hq : IsHarmonicMinorant U (newtonKernelEReal z) q)
    (hqlim : Tendsto q (𝓝[U] y) (𝓝 (newtonKernel z y))) :
    Tendsto (greenFunction U z) (𝓝[U] y) (𝓝 0) := by
  have hN : Tendsto (newtonKernel z) (𝓝[U] y) (𝓝 (newtonKernel z y)) :=
    ((harmonicAt_newtonKernel hyz).1.continuousAt.tendsto).mono_left nhdsWithin_le_nhds
  have hupper : Tendsto (fun x => newtonKernel z x - q x) (𝓝[U] y) (𝓝 0) := by
    simpa only [sub_self] using hN.sub hqlim
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · exact Filter.Eventually.of_forall (greenFunction_nonneg hUb z)
  · filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds hyz)] with x hx hxz
    have hxz' : x ≠ z := by simpa using hxz
    have hlow := hq.le_greatestHarmonicMinorant x
    have hupp : greatestHarmonicMinorant U (newtonKernelEReal z) x ≤
        (newtonKernel z x : EReal) := by
      simpa [newtonKernelEReal, hxz'] using
        greatestHarmonicMinorant_le (u := newtonKernelEReal z) hx
    have hqbound : q x ≤ (greatestHarmonicMinorant U (newtonKernelEReal z) x).toReal := by
      have hh := EReal.toReal_le_toReal hlow (EReal.coe_ne_bot _)
        (ne_top_of_le_ne_top (EReal.coe_ne_top _) hupp)
      simpa only [EReal.toReal_coe] using hh
    rw [greenFunction, ite_eq_left ⟨hz, hx, Ne.symm hxz'⟩]
    linarith

/-- A harmonic minorant bounds the Green function away from the pole. -/
theorem greenFunction_le_newtonKernel_sub_minorant
    {U : Set ℂ} {z x : ℂ} (hz : z ∈ U) (hx : x ∈ U) (hxz : x ≠ z)
    {q : ℂ → ℝ} (hq : IsHarmonicMinorant U (newtonKernelEReal z) q) :
    greenFunction U z x ≤ newtonKernel z x - q x := by
  have hlow := hq.le_greatestHarmonicMinorant x
  have hupp : greatestHarmonicMinorant U (newtonKernelEReal z) x ≤
      (newtonKernel z x : EReal) := by
    simpa [newtonKernelEReal, hxz] using
      greatestHarmonicMinorant_le (u := newtonKernelEReal z) hx
  have hqbound : q x ≤ (greatestHarmonicMinorant U (newtonKernelEReal z) x).toReal := by
    have hh := EReal.toReal_le_toReal hlow (EReal.coe_ne_bot _)
      (ne_top_of_le_ne_top (EReal.coe_ne_top _) hupp)
    simpa only [EReal.toReal_coe] using hh
  rw [greenFunction, ite_eq_left ⟨hz, hx, Ne.symm hxz⟩]
  linarith

/-- Approximate harmonic minorants suffice to establish a Green boundary limit. -/
theorem tendsto_greenFunction_zero_of_approximating_harmonic_minorants
    {U : Set ℂ} (hUb : Bornology.IsBounded U) {z y : ℂ} (hz : z ∈ U) (hyz : y ≠ z)
    (hq : ∀ ε : ℝ, 0 < ε → ∃ q : ℂ → ℝ,
      IsHarmonicMinorant U (newtonKernelEReal z) q ∧
      Tendsto q (𝓝[U] y) (𝓝 (newtonKernel z y - ε))) :
    Tendsto (greenFunction U z) (𝓝[U] y) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨q, hminor, hqlim⟩ := hq (ε / 2) (half_pos hε)
  have hN : Tendsto (newtonKernel z) (𝓝[U] y) (𝓝 (newtonKernel z y)) :=
    ((harmonicAt_newtonKernel hyz).1.continuousAt.tendsto).mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (fun x => newtonKernel z x - q x) (𝓝[U] y) (𝓝 (ε / 2)) := by
    convert hN.sub hqlim using 1; ring
  have hlt : ∀ᶠ x in 𝓝[U] y, newtonKernel z x - q x < ε :=
    hlim.eventually (Iio_mem_nhds (by linarith))
  filter_upwards [hlt, self_mem_nhdsWithin,
    nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds hyz)] with x hx hxU hxz
  have hxz' : x ≠ z := by simpa using hxz
  have hG : 0 ≤ greenFunction U z x := greenFunction_nonneg hUb z x
  have hupper := greenFunction_le_newtonKernel_sub_minorant hz hxU hxz' hminor
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hG]
  exact lt_of_le_of_lt hupper hx

/-- The Green function vanishes in a neighbourhood of every point outside
the closure of the pole component. -/
theorem greenFunction_eventually_eq_zero_of_not_mem_closure_pole_component
    {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {z y : ℂ} (hz : z ∈ U) (hy : y ∉ closure (connectedComponentIn U z)) :
    ∀ᶠ x in 𝓝 y, greenFunction U z x = 0 := by
  filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hy] with x hx
  exact greenFunction_eq_zero_of_not_mem_connectedComponentIn hU hUb hz
    (fun hxC => hx (subset_closure hxC))

/-- No boundary regularity assumption is needed at points outside the closure
of the pole component. -/
theorem tendsto_greenFunction_zero_of_not_mem_closure_pole_component
    {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {z y : ℂ} (hz : z ∈ U) (hy : y ∉ closure (connectedComponentIn U z)) :
    Tendsto (greenFunction U z) (𝓝 y) (𝓝 0) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [greenFunction_eventually_eq_zero_of_not_mem_closure_pole_component
    hU hUb hz hy] with x hx
  exact hx.symm

/-- Green boundary regularity of the pole component implies the corresponding
boundary limits for the whole bounded open set. -/
theorem tendsto_greenFunction_zero_of_pole_component_boundary
    {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U) {z : ℂ} (hz : z ∈ U)
    (hcomponent : ∀ y ∈ closure (connectedComponentIn U z),
      y ∉ connectedComponentIn U z →
        Tendsto (greenFunction (connectedComponentIn U z) z)
          (𝓝[connectedComponentIn U z] y) (𝓝 0))
    {y : ℂ} (hyU : y ∉ U) :
    Tendsto (greenFunction U z) (𝓝[U] y) (𝓝 0) := by
  rw [greenFunction_eq_connectedComponentIn_all hU hUb hz]
  by_cases hyC : y ∈ closure (connectedComponentIn U z)
  · have hyout : y ∉ connectedComponentIn U z :=
      fun hy => hyU (connectedComponentIn_subset U z hy)
    exact (tendsto_greenFunction_nhds_of_nhdsWithin (hcomponent y hyC hyout)).mono_left
      nhdsWithin_le_nhds
  · apply tendsto_const_nhds.congr'
    filter_upwards [nhdsWithin_le_nhds (isClosed_closure.isOpen_compl.mem_nhds hyC)] with x hx
    exact (greenFunction_of_notMem_right (fun hxC => hx (subset_closure hxC)) z).symm

/-- Adding a disjoint open set does not change the Green function of a
bounded open set containing the pole. -/
theorem greenFunction_eq_of_disjoint_open_union_all
    {V W : Set ℂ} (hV : IsOpen V) (hW : IsOpen W) (hdis : Disjoint V W)
    (hUb : Bornology.IsBounded (V ∪ W)) {z : ℂ} (hz : z ∈ V) :
    greenFunction (V ∪ W) z = greenFunction V z := by
  funext x
  by_cases hxV : x ∈ V
  · exact greenFunction_eq_of_disjoint_open_union hV hW hdis hUb hz hxV
  · by_cases hxW : x ∈ W
    · rw [greenFunction_eq_zero_of_disjoint_open_components hV hW hdis hUb hz hxW,
        greenFunction_of_notMem_right hxV]
    · rw [greenFunction_of_notMem_right (by simp [hxV, hxW]),
        greenFunction_of_notMem_right hxV]

/-- A disjoint open union inherits Green boundary limits from the member
containing the pole, with no boundary assumption on the other member. -/
theorem tendsto_greenFunction_zero_of_disjoint_open_union
    {V W : Set ℂ} (hV : IsOpen V) (hW : IsOpen W) (hdis : Disjoint V W)
    (hUb : Bornology.IsBounded (V ∪ W)) {z : ℂ} (hz : z ∈ V)
    (hregular : ∀ y ∈ closure V, y ∉ V →
      Tendsto (greenFunction V z) (𝓝[V] y) (𝓝 0))
    {y : ℂ} (hy : y ∉ V ∪ W) :
    Tendsto (greenFunction (V ∪ W) z) (𝓝[V ∪ W] y) (𝓝 0) := by
  rw [greenFunction_eq_of_disjoint_open_union_all hV hW hdis hUb hz]
  by_cases hyV : y ∈ closure V
  · exact (tendsto_greenFunction_nhds_of_nhdsWithin
      (hregular y hyV (fun h => hy (Or.inl h)))).mono_left nhdsWithin_le_nhds
  · apply tendsto_const_nhds.congr'
    filter_upwards [nhdsWithin_le_nhds (isClosed_closure.isOpen_compl.mem_nhds hyV)] with x hx
    exact (greenFunction_of_notMem_right (fun hxV => hx (subset_closure hxV)) z).symm

/-- Adding any bounded open set disjoint from the pole disc preserves Green
boundary regularity. -/
theorem tendsto_greenFunction_zero_of_disjoint_union_ball
    {c z y : ℂ} {r : ℝ} {W : Set ℂ} (hW : IsOpen W)
    (hdis : Disjoint (ball c r) W) (hWb : Bornology.IsBounded W)
    (hz : z ∈ ball c r) (hy : y ∉ ball c r ∪ W) :
    Tendsto (greenFunction (ball c r ∪ W) z) (𝓝[ball c r ∪ W] y) (𝓝 0) := by
  apply tendsto_greenFunction_zero_of_disjoint_open_union isOpen_ball hW hdis
    (isBounded_ball.union hWb) hz ?_ hy
  intro x hx hxout
  have hxle : dist x c ≤ r := mem_closedBall.mp (closure_ball_subset_closedBall hx)
  have hxge : r ≤ dist x c := le_of_not_gt (fun h => hxout (mem_ball.mpr h))
  exact tendsto_greenFunction_zero_of_enclosing_disc hz Subset.rfl
    (mem_sphere.mpr (le_antisymm hxle hxge))

/-- A finite union of discs is Green regular for a pole in a disc disjoint
from all the other discs. The other discs may intersect one another. -/
theorem tendsto_greenFunction_zero_of_finite_disc_union_isolated_pole_disc
    {ι : Type*} (F : Finset ι) (c : ι → ℂ) (r : ι → ℝ) {i : ι} (hi : i ∈ F)
    (hdis : ∀ j ∈ F, j ≠ i → Disjoint (ball (c i) (r i)) (ball (c j) (r j)))
    {z y : ℂ} (hz : z ∈ ball (c i) (r i))
    (hy : y ∉ ⋃ j ∈ F, ball (c j) (r j)) :
    Tendsto (greenFunction (⋃ j ∈ F, ball (c j) (r j)) z)
      (𝓝[⋃ j ∈ F, ball (c j) (r j)] y) (𝓝 0) := by
  classical
  let W : Set ℂ := ⋃ j ∈ F.erase i, ball (c j) (r j)
  have hF : (⋃ j ∈ F, ball (c j) (r j)) = ball (c i) (r i) ∪ W := by
    rw [← Finset.insert_erase hi, Finset.set_biUnion_insert]
  have hW : IsOpen W := isOpen_iUnion fun j => isOpen_iUnion fun _ => isOpen_ball
  have hWb : Bornology.IsBounded W := by
    exact (Bornology.isBounded_biUnion_finset (F.erase i)).2
      (fun _ _ => isBounded_ball)
  have hdisW : Disjoint (ball (c i) (r i)) W := by
    apply disjoint_iUnion_right.mpr
    intro j
    apply disjoint_iUnion_right.mpr
    intro hj
    exact hdis j (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj)
  rw [hF] at hy ⊢
  exact tendsto_greenFunction_zero_of_disjoint_union_ball hW hdisW hWb hz hy

/-- A finite union of pairwise disjoint discs is Green regular at every
boundary point for every pole in the union. -/
theorem tendsto_greenFunction_zero_of_pairwise_disjoint_finite_discs
    {ι : Type*} (F : Finset ι) (c : ι → ℂ) (r : ι → ℝ)
    (hdis : ∀ i ∈ F, ∀ j ∈ F, i ≠ j →
      Disjoint (ball (c i) (r i)) (ball (c j) (r j)))
    {z y : ℂ} (hz : z ∈ ⋃ i ∈ F, ball (c i) (r i))
    (hy : y ∉ ⋃ i ∈ F, ball (c i) (r i)) :
    Tendsto (greenFunction (⋃ i ∈ F, ball (c i) (r i)) z)
      (𝓝[⋃ i ∈ F, ball (c i) (r i)] y) (𝓝 0) := by
  obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp hz
  exact tendsto_greenFunction_zero_of_finite_disc_union_isolated_pole_disc F c r hi
    (fun j hj hji => hdis i hi j hj (Ne.symm hji)) hzi hy

/-- Near a point, a finite union agrees with the union of those members
whose closures contain the point. -/
theorem finite_union_eventually_eq_union_of_active_closures
    {ι : Type*} (F : Finset ι) (A : ι → Set ℂ) (y : ℂ) :
    ∀ᶠ x in 𝓝 y, x ∈ ⋃ i ∈ F, A i ↔
      x ∈ ⋃ i ∈ F.filter (fun i => y ∈ closure (A i)), A i := by
  classical
  have hevent : ∀ᶠ x in 𝓝 y, ∀ i ∈ F, y ∉ closure (A i) → x ∉ A i := by
    rw [eventually_all_finset]
    intro i hi
    by_cases h : y ∈ closure (A i)
    · exact Filter.Eventually.of_forall (fun _ h' => (h' h).elim)
    · filter_upwards [isClosed_closure.isOpen_compl.mem_nhds h] with x hx _ hxA
      exact hx (subset_closure hxA)
  filter_upwards [hevent] with x hx
  constructor
  · intro hxF
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hxF
    have hyi : y ∈ closure (A i) := by
      by_contra hyi
      exact hx i hi hyi hxi
    exact mem_iUnion₂.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hyi⟩, hxi⟩
  · intro hxF
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hxF
    exact mem_iUnion₂.mpr ⟨i, (Finset.mem_filter.mp hi).1, hxi⟩

/-- At a boundary point of a finite union of discs, only discs whose boundary
circles contain that point contribute to the union locally. -/
theorem finite_disc_union_eventually_eq_active_circles
    {ι : Type*} (F : Finset ι) (c : ι → ℂ) (r : ι → ℝ) {y : ℂ}
    (hr : ∀ i ∈ F, 0 < r i)
    (hy : y ∉ ⋃ i ∈ F, ball (c i) (r i)) :
    ∀ᶠ x in 𝓝 y, x ∈ ⋃ i ∈ F, ball (c i) (r i) ↔
      x ∈ ⋃ i ∈ F.filter (fun i => y ∈ sphere (c i) (r i)), ball (c i) (r i) := by
  classical
  have hfilter : F.filter (fun i => y ∈ closure (ball (c i) (r i))) =
      F.filter (fun i => y ∈ sphere (c i) (r i)) := by
    apply Finset.filter_congr
    intro i hi
    constructor
    · intro hyclose
      have hle : dist y (c i) ≤ r i :=
        mem_closedBall.mp (closure_ball_subset_closedBall hyclose)
      have hge : r i ≤ dist y (c i) := by
        apply le_of_not_gt
        intro hyball
        exact hy (mem_iUnion₂.mpr ⟨i, hi, mem_ball.mpr hyball⟩)
      exact mem_sphere.mpr (le_antisymm hle hge)
    · intro hysphere
      rw [closure_ball (c i) (hr i hi).ne']
      exact sphere_subset_closedBall hysphere
  simpa only [hfilter] using
    (finite_union_eventually_eq_union_of_active_closures F (fun i => ball (c i) (r i)) y)

/-- If exactly one disc boundary passes through a point outside a finite
union, that union locally coincides with this disc. -/
theorem finite_disc_union_eventually_eq_unique_active_disc
    {ι : Type*} (F : Finset ι) (c : ι → ℂ) (r : ι → ℝ) {y : ℂ} {i : ι}
    (hr : ∀ j ∈ F, 0 < r j)
    (hy : y ∉ ⋃ j ∈ F, ball (c j) (r j))
    (hi : i ∈ F) (hyi : y ∈ sphere (c i) (r i))
    (hunique : ∀ j ∈ F, y ∈ sphere (c j) (r j) → j = i) :
    ∀ᶠ x in 𝓝 y, x ∈ ⋃ j ∈ F, ball (c j) (r j) ↔ x ∈ ball (c i) (r i) := by
  have hfilter : F.filter (fun j => y ∈ sphere (c j) (r j)) = {i} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hj, hyj⟩
      exact hunique j hj hyj
    · intro hji
      subst j
      exact ⟨hi, hyi⟩
  simpa only [hfilter, Finset.set_biUnion_singleton] using
    (finite_disc_union_eventually_eq_active_circles F c r hr hy)

/-- A unique active boundary circle gives a disc neighbourhood on which the
finite union agrees with the corresponding constituent disc. -/
theorem exists_ball_inter_finite_disc_union_eq_unique_active_disc
    {ι : Type*} (F : Finset ι) (c : ι → ℂ) (r : ι → ℝ) {y : ℂ} {i : ι}
    (hr : ∀ j ∈ F, 0 < r j)
    (hy : y ∉ ⋃ j ∈ F, ball (c j) (r j))
    (hi : i ∈ F) (hyi : y ∈ sphere (c i) (r i))
    (hunique : ∀ j ∈ F, y ∈ sphere (c j) (r j) → j = i) :
    ∃ ε > 0, ball y ε ∩ (⋃ j ∈ F, ball (c j) (r j)) =
      ball y ε ∩ ball (c i) (r i) := by
  have h := finite_disc_union_eventually_eq_unique_active_disc F c r hr hy hi hyi hunique
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp h
  refine ⟨ε, hε, ?_⟩
  ext x
  exact and_congr_right (fun hx => hεsub hx)

/-- A boundary point of a finite union of discs belongs to the boundary
circle of at least one disc in the union. -/
theorem exists_mem_sphere_of_mem_closure_finite_disc_union
    {ι : Type*} (F : Finset ι) (c : ι → ℂ) (r : ι → ℝ) {y : ℂ}
    (hy : y ∈ closure (⋃ i ∈ F, ball (c i) (r i)))
    (hynot : y ∉ ⋃ i ∈ F, ball (c i) (r i)) :
    ∃ i ∈ F, y ∈ sphere (c i) (r i) := by
  rw [F.closure_biUnion] at hy
  obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.mp hy
  have hyclosed : dist y (c i) ≤ r i := mem_closedBall.mp (closure_ball_subset_closedBall hyi)
  have hyoutside : r i ≤ dist y (c i) := by
    apply le_of_not_gt
    intro h
    exact hynot (mem_iUnion₂.mpr ⟨i, hi, mem_ball.mpr h⟩)
  exact ⟨i, hi, mem_sphere.mpr (le_antisymm hyclosed hyoutside)⟩

/-- A disc has a Green-regular exhaustion containing the prescribed pole. -/
theorem exists_greenRegular_exhaustion_ball {c z : ℂ} {R : ℝ}
    (hz : z ∈ ball c R) :
    ∃ V : ℕ → Set ℂ, (∀ n, IsOpen (V n)) ∧ Monotone V ∧
      (⋃ n, V n) = ball c R ∧ (∀ n, closure (V n) ⊆ ball c R) ∧
      (∀ n, z ∈ V n) ∧ ∀ n, ∀ y ∈ closure (V n), y ∉ V n →
        Tendsto (greenFunction (V n) z) (𝓝[V n] y) (𝓝 0) := by
  have hzR : dist z c < R := mem_ball.mp hz
  let δ := R - dist z c
  have hδ : 0 < δ := sub_pos.mpr hzR
  let ρ (n : ℕ) : ℝ := R - δ * ((1 / 2 : ℝ) ^ (n + 1))
  have hp (n : ℕ) : 0 < (1 / 2 : ℝ) ^ (n + 1) := by positivity
  have hp1 (n : ℕ) : (1 / 2 : ℝ) ^ (n + 1) ≤ 1 / 2 := by
    rw [pow_succ]
    have h : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith
  have hrlt (n : ℕ) : ρ n < R := by
    dsimp [ρ]
    exact sub_lt_self _ (mul_pos hδ (hp n))
  have hzp (n : ℕ) : dist z c < ρ n := by
    dsimp [ρ, δ]
    have hh := hp1 n
    nlinarith
  have hmono : Monotone ρ := by
    apply monotone_nat_of_le_succ
    intro n
    dsimp only [ρ]
    have heq : (1 / 2 : ℝ) ^ (n + 1 + 1) =
        (1 / 2 : ℝ) ^ (n + 1) * (1 / 2) := pow_succ _ _
    rw [heq]
    have h : 0 ≤ δ * ((1 / 2 : ℝ) ^ (n + 1)) := mul_nonneg hδ.le (hp n).le
    nlinarith
  have hlim : Tendsto ρ atTop (𝓝 R) := by
    have hpLim : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) atTop (𝓝 0) := by
      have h := (tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).mul_const (1 / 2)
      simpa only [pow_succ, zero_mul] using h
    simpa only [ρ, mul_zero, sub_zero] using tendsto_const_nhds.sub (hpLim.const_mul δ)
  let V (n : ℕ) := ball c (ρ n)
  refine ⟨V, fun _ => isOpen_ball, ?_, ?_, ?_, ?_, ?_⟩
  · intro m n hmn
    exact ball_subset_ball (hmono hmn)
  · apply Subset.antisymm
    · exact iUnion_subset fun n => ball_subset_ball (hrlt n).le
    · intro x hx
      have ht : ∀ᶠ n in atTop, dist x c < ρ n :=
        hlim.eventually (Ioi_mem_nhds (mem_ball.mp hx))
      obtain ⟨n, hn⟩ := ht.exists
      exact mem_iUnion.mpr ⟨n, mem_ball.mpr hn⟩
  · intro n x hx
    exact mem_ball.mpr ((mem_closedBall.mp (closure_ball_subset_closedBall hx)).trans_lt (hrlt n))
  · intro n
    exact mem_ball.mpr (hzp n)
  · intro n y hy hyV
    have hyclosed : dist y c ≤ ρ n := mem_closedBall.mp (closure_ball_subset_closedBall hy)
    have hynot : ρ n ≤ dist y c := le_of_not_gt (fun h => hyV (mem_ball.mpr h))
    exact tendsto_greenFunction_zero_of_enclosing_disc (mem_ball.mpr (hzp n)) Subset.rfl
      (mem_sphere.mpr (le_antisymm hyclosed hynot))

/-- A positive harmonic barrier with a uniform positive lower bound away from
its zero gives a Green boundary limit. -/
theorem tendsto_greenFunction_zero_of_harmonic_barrier
    {U : Set ℂ} (hUb : Bornology.IsBounded U) {z y : ℂ} (hz : z ∈ U)
    (hyz : y ≠ z) {b : ℂ → ℝ}
    (hb : InnerProductSpace.HarmonicOnNhd b U)
    (hbnonneg : ∀ x ∈ U, 0 ≤ b x)
    (hblim : Tendsto b (𝓝[U] y) (𝓝 0))
    (hbaway : ∀ δ > 0, ∃ m > 0, ∀ x ∈ U, δ ≤ dist x y → m ≤ b x) :
    Tendsto (greenFunction U z) (𝓝[U] y) (𝓝 0) := by
  obtain ⟨R, hR⟩ := hUb.subset_closedBall z
  let L : ℝ := -(2 * Real.pi)⁻¹ * Real.log R
  have hL : ∀ x ∈ U, x ≠ z → L ≤ newtonKernel z x := by
    intro x hx hxz
    have h := (isHarmonicMinorant_const_newtonKernelEReal hR).2 x hx
    change (L : EReal) ≤ newtonKernelEReal z x at h
    simpa only [newtonKernelEReal, hxz, ite_false, EReal.coe_le_coe_iff] using h
  apply tendsto_greenFunction_zero_of_approximating_harmonic_minorants hUb hz hyz
  intro ε hε
  have hN : ContinuousAt (newtonKernel z) y :=
    (harmonicAt_newtonKernel hyz).1.continuousAt
  have hnear : ∀ᶠ x in 𝓝 y, newtonKernel z y - ε < newtonKernel z x :=
    hN.eventually (Ioi_mem_nhds (by linarith))
  obtain ⟨δ, hδ, hδnear⟩ := Metric.eventually_nhds_iff.mp hnear
  obtain ⟨m, hm, hbfar⟩ := hbaway δ hδ
  let C : ℝ := max 0 ((newtonKernel z y - ε - L) / m)
  have hC : 0 ≤ C := le_max_left _ _
  have hCm : newtonKernel z y - ε - L ≤ C * m := by
    have h := le_max_right (0 : ℝ) ((newtonKernel z y - ε - L) / m)
    exact (div_le_iff₀ hm).mp h
  let q : ℂ → ℝ := fun x => newtonKernel z y - ε - C * b x
  refine ⟨q, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro x hx
      exact (InnerProductSpace.harmonicAt_const _).sub ((hb x hx).const_smul (c := C))
    · intro x hx
      by_cases hxz : x = z
      · simp [newtonKernelEReal, hxz]
      · have hqle : q x ≤ newtonKernel z x := by
          by_cases hdist : dist x y < δ
          · have hn := hδnear (mem_ball.mpr hdist)
            have hmul := mul_nonneg hC (hbnonneg x hx)
            dsimp [q]
            linarith
          · have hm' := hbfar x hx (le_of_not_gt hdist)
            have hmC := mul_le_mul_of_nonneg_left hm' hC
            have hn := hL x hx hxz
            dsimp [q]
            linarith
        simpa [newtonKernelEReal, hxz] using hqle
  · have hlim : Tendsto (fun x => (newtonKernel z y - ε) - C * b x)
        (𝓝[U] y) (𝓝 ((newtonKernel z y - ε) - C * 0)) :=
      tendsto_const_nhds.sub (tendsto_const_nhds.mul hblim)
    simpa [q] using hlim

/-- A harmonic barrier continuous on the compact closure and vanishing only
at the boundary point yields the uniform separation needed above. -/
theorem tendsto_greenFunction_zero_of_continuous_harmonic_barrier
    {U : Set ℂ} (hUb : Bornology.IsBounded U) {z y : ℂ} (hz : z ∈ U)
    (hy : y ∈ closure U) (hyz : y ≠ z) {b : ℂ → ℝ}
    (hb : InnerProductSpace.HarmonicOnNhd b U)
    (hbc : ContinuousOn b (closure U)) (hby : b y = 0)
    (hbpos : ∀ x ∈ closure U, x ≠ y → 0 < b x) :
    Tendsto (greenFunction U z) (𝓝[U] y) (𝓝 0) := by
  apply tendsto_greenFunction_zero_of_harmonic_barrier hUb hz hyz hb
  · intro x hx
    by_cases hxy : x = y
    · simp [hxy, hby]
    · exact (hbpos x (subset_closure hx) hxy).le
  · rw [← hby]
    exact (hbc y hy).mono subset_closure
  · intro δ hδ
    let K := closure U \ ball y δ
    have hK : IsCompact K := hUb.isCompact_closure.diff isOpen_ball
    by_cases hne : K.Nonempty
    · obtain ⟨w, hw, hmin⟩ := hK.exists_isMinOn hne (hbc.mono sdiff_subset)
      have hwy : w ≠ y := by
        intro heq
        apply hw.2
        simpa [heq] using (mem_ball_self hδ : y ∈ ball y δ)
      refine ⟨b w, hbpos w hw.1 hwy, ?_⟩
      intro x hx hdist
      apply hmin
      exact ⟨subset_closure hx, by simpa [mem_ball, not_lt] using hdist⟩
    · refine ⟨1, zero_lt_one, ?_⟩
      intro x hx hdist
      exfalso
      apply hne
      exact ⟨x, subset_closure hx, by simpa [mem_ball, not_lt] using hdist⟩

/-- A strictly supporting exterior disc gives Green regularity at its point
of contact. -/
theorem tendsto_greenFunction_zero_of_strict_exterior_disc
    {U : Set ℂ} (hUb : Bornology.IsBounded U) {z y a : ℂ} {r : ℝ}
    (hz : z ∈ U) (hy : y ∈ closure U) (hyout : y ∉ U)
    (hr : 0 < r) (hycontact : ‖y - a‖ = r)
    (hsupport : ∀ x ∈ closure U, x ≠ y → r < ‖x - a‖) :
    Tendsto (greenFunction U z) (𝓝[U] y) (𝓝 0) := by
  have hyz : y ≠ z := by intro h; exact hyout (h ▸ hz)
  let b : ℂ → ℝ := fun x => Real.log ‖x - a‖ - Real.log r
  have hnorm : ∀ x ∈ closure U, 0 < ‖x - a‖ := by
    intro x hx
    by_cases hxy : x = y
    · simpa [hxy, hycontact] using hr
    · exact hr.trans (hsupport x hx hxy)
  have hharm : ∀ x ∈ closure U, InnerProductSpace.HarmonicAt b x := by
    intro x hx
    have ha : AnalyticAt ℂ (fun w : ℂ => w - a) x := by fun_prop
    have hn : x - a ≠ 0 := norm_ne_zero_iff.mp (hnorm x hx).ne'
    exact (ha.harmonicAt_log_norm hn).sub (InnerProductSpace.harmonicAt_const _)
  apply tendsto_greenFunction_zero_of_continuous_harmonic_barrier hUb hz hy hyz
  · intro x hx
    exact hharm x (subset_closure hx)
  · intro x hx
    exact (hharm x hx).1.continuousAt.continuousWithinAt
  · simp [b, hycontact]
  · intro x hx hxy
    dsimp [b]
    exact sub_pos.mpr (Real.log_lt_log hr (hsupport x hx hxy))

/-- An exterior disc can be shrunk to make its contact with the closure
strict, and hence gives a Green boundary limit. -/
theorem tendsto_greenFunction_zero_of_exterior_disc
    {U : Set ℂ} (hUb : Bornology.IsBounded U) {z y a : ℂ} {r : ℝ}
    (hz : z ∈ U) (hy : y ∈ closure U) (hyout : y ∉ U)
    (hr : 0 < r) (hycontact : ‖y - a‖ = r)
    (hdisjoint : Disjoint U (ball a r)) :
    Tendsto (greenFunction U z) (𝓝[U] y) (𝓝 0) := by
  have hclosed : closure U ⊆ (ball a r)ᶜ :=
    closure_minimal (disjoint_left.mp hdisjoint) isOpen_ball.isClosed_compl
  have hdist : dist y a = r := by simpa [dist_eq_norm] using hycontact
  have hmid : dist y (midpoint ℝ y a) = r / 2 := by
    rw [dist_left_midpoint, hdist]
    norm_num
    ring
  apply tendsto_greenFunction_zero_of_strict_exterior_disc (a := midpoint ℝ y a) hUb hz hy hyout
    (show 0 < r / 2 by linarith) (by simpa only [dist_eq_norm] using hmid)
  intro x hx hxy
  have hxa : r ≤ dist x a := by
    have h := hclosed hx
    simpa [mem_ball, not_lt] using h
  have hxypos : 0 < dist x y := dist_pos.mpr hxy
  have happ := EuclideanGeometry.dist_sq_add_dist_sq_eq_two_mul_dist_midpoint_sq_add_half_dist_sq x y a
  rw [hdist] at happ
  have hnonneg := dist_nonneg (x := x) (y := midpoint ℝ y a)
  have : r / 2 < dist x (midpoint ℝ y a) := by nlinarith
  simpa [dist_eq_norm] using this

#print axioms tendsto_greenFunction_zero_of_exterior_disc
#print axioms tendsto_greenFunction_zero_of_strict_exterior_disc
#print axioms tendsto_greenFunction_zero_of_continuous_harmonic_barrier
#print axioms tendsto_greenFunction_zero_of_harmonic_barrier

/-- Four unit discs centered at the cardinal directions contain the
punctured unit disc. -/
theorem punctured_unit_ball_subset_four_discs :
    ball (0 : ℂ) 1 \ {0} ⊆
      ball (1 : ℂ) 1 ∪ ball (-1 : ℂ) 1 ∪
        ball Complex.I 1 ∪ ball (-Complex.I) 1 := by
  intro x hx
  have hn : ‖x‖ < 1 := by simpa [mem_ball, dist_eq_norm] using hx.1
  have hp : 0 < ‖x‖ := norm_pos_iff.mpr (by simpa using hx.2)
  by_contra hout
  simp only [mem_union, not_or, mem_ball, not_lt, dist_eq_norm] at hout
  have h1 : 1 ≤ ‖x - (1 : ℂ)‖ ^ 2 := by nlinarith [norm_nonneg (x - (1 : ℂ))]
  have h2 : 1 ≤ ‖x - (-1 : ℂ)‖ ^ 2 := by nlinarith [norm_nonneg (x - (-1 : ℂ))]
  have h3 : 1 ≤ ‖x - Complex.I‖ ^ 2 := by nlinarith [norm_nonneg (x - Complex.I)]
  have h4 : 1 ≤ ‖x - (-Complex.I)‖ ^ 2 := by nlinarith [norm_nonneg (x - (-Complex.I))]
  rw [Complex.sq_norm, Complex.normSq_apply] at h1 h2 h3 h4
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im] at h1 h2 h3 h4
  have hsq : ‖x‖ ^ 2 = x.re * x.re + x.im * x.im := by
    rw [Complex.sq_norm, Complex.normSq_apply]
  have habs := Complex.norm_le_abs_re_add_abs_im x
  have hre := abs_le.mpr (show -(‖x‖ ^ 2 / 2) ≤ x.re ∧ x.re ≤ ‖x‖ ^ 2 / 2 by
    constructor <;> nlinarith)
  have him := abs_le.mpr (show -(‖x‖ ^ 2 / 2) ≤ x.im ∧ x.im ≤ ‖x‖ ^ 2 / 2 by
    constructor <;> nlinarith)
  nlinarith

/-- A bounded domain containing a punctured disc cannot have zero Green
boundary limit at the puncture. -/
theorem not_tendsto_greenFunction_zero_of_punctured_ball_subset
    {V : Set ℂ} {R : ℝ} {z a : ℂ}
    (hV : Bornology.IsBounded V)
    (ha : a ∈ ball (0 : ℂ) R) (hz : z ∈ ball (0 : ℂ) R \ {a})
    (hsub : ball (0 : ℂ) R \ {a} ⊆ V) :
    ¬ Tendsto (greenFunction V z) (𝓝[V] a) (𝓝 0) := by
  have hac : a ∈ closure (ball (0 : ℂ) R \ {a}) := by
    have h := (dense_compl_singleton a).open_subset_closure_inter isOpen_ball ha
    simpa [sdiff_eq, inter_comm] using h
  have : (𝓝[ball (0 : ℂ) R \ {a}] a).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hac
  have hpos := greenFunction_ball_pos hz.1 ha (by simpa using hz.2)
  intro hlim
  have hle := Section6.greenFunction_le_of_subset hsub hV z
  have hlim' := hlim.mono_left (nhdsWithin_mono a hsub)
  have h := le_of_tendsto_of_tendsto
    (tendsto_greenFunction_punctured_ball_at_puncture ha hz) hlim'
    (Filter.Eventually.of_forall hle)
  linarith

/-- The four-disc union has an irregular boundary point at the origin. -/
theorem four_disc_union_irregular_boundary :
    let V : Set ℂ := ball (1 : ℂ) 1 ∪ ball (-1 : ℂ) 1 ∪
      ball Complex.I 1 ∪ ball (-Complex.I) 1
    Bornology.IsBounded V ∧ (0 : ℂ) ∈ closure V ∧ (0 : ℂ) ∉ V ∧
      (1 / 2 : ℂ) ∈ V ∧
      ¬ Tendsto (greenFunction V (1 / 2 : ℂ)) (𝓝[V] 0) (𝓝 0) := by
  dsimp only
  let V : Set ℂ := ball (1 : ℂ) 1 ∪ ball (-1 : ℂ) 1 ∪
      ball Complex.I 1 ∪ ball (-Complex.I) 1
  have hV : Bornology.IsBounded V := by
    dsimp [V]
    exact ((isBounded_ball.union isBounded_ball).union isBounded_ball).union isBounded_ball
  have ha : (0 : ℂ) ∈ ball (0 : ℂ) 1 := by simp
  have hz : (1 / 2 : ℂ) ∈ ball (0 : ℂ) 1 \ {(0 : ℂ)} := by
    norm_num [mem_ball, dist_eq_norm, Complex.norm_real]
  have hsub : ball (0 : ℂ) 1 \ {(0 : ℂ)} ⊆ V :=
    punctured_unit_ball_subset_four_discs
  have hac : (0 : ℂ) ∈ closure (ball (0 : ℂ) 1 \ {(0 : ℂ)}) := by
    have h := (dense_compl_singleton (0 : ℂ)).open_subset_closure_inter isOpen_ball ha
    simpa [sdiff_eq, inter_comm] using h
  refine ⟨hV, closure_mono hsub hac, ?_, hsub hz, ?_⟩
  · simp [mem_ball, dist_eq_norm]
  · exact not_tendsto_greenFunction_zero_of_punctured_ball_subset hV ha hz hsub

#print axioms four_disc_union_irregular_boundary
#print axioms punctured_unit_ball_subset_four_discs
#print axioms not_tendsto_greenFunction_zero_of_punctured_ball_subset
#print axioms tendsto_greenFunction_zero_of_approximating_harmonic_minorants
#print axioms greenFunction_le_newtonKernel_sub_minorant
#print axioms tendsto_greenFunction_zero_of_harmonic_minorant
#print axioms tendsto_greenFunction_zero_iff_greatestHarmonicMinorant
#print axioms greenFunction_eventually_eq_zero_of_not_mem_closure_pole_component
#print axioms tendsto_greenFunction_zero_of_not_mem_closure_pole_component
#print axioms exists_ball_inter_finite_disc_union_eq_unique_active_disc
#print axioms finite_disc_union_eventually_eq_unique_active_disc
#print axioms finite_union_eventually_eq_union_of_active_closures
#print axioms finite_disc_union_eventually_eq_active_circles
#print axioms tendsto_greenFunction_zero_of_pairwise_disjoint_finite_discs
#print axioms tendsto_greenFunction_zero_of_finite_disc_union_isolated_pole_disc
#print axioms tendsto_greenFunction_zero_of_disjoint_union_ball
#print axioms greenFunction_eq_of_disjoint_open_union_all
#print axioms tendsto_greenFunction_zero_of_disjoint_open_union
#print axioms tendsto_greenFunction_nhds_of_nhdsWithin
#print axioms tendsto_greenFunction_zero_of_pole_component_boundary
#print axioms exists_mem_sphere_of_mem_closure_finite_disc_union
#print axioms tendsto_greenFunction_zero_of_subset_of_boundary_limit
#print axioms exists_greenRegular_exhaustion_ball

end HarmonicBalls

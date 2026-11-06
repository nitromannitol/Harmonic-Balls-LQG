import HarmonicBalls.Proofs.Sec5.DiscSupportedBoundary
import HarmonicBalls.Proofs.Sec5.GreenConnectedComponent

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

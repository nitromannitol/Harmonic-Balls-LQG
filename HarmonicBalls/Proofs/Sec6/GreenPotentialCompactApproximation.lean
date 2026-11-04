import HarmonicBalls.Proofs.Sec6.GreenPotentialBound
import Mathlib.Topology.UniformSpace.Dini

/-!
# Uniform approximation of Green potentials

Increasing measurable restrictions of a nonnegative Green kernel converge uniformly on
compact sets whenever their potentials and the limiting potential are continuous there.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Set Filter
open scoped NNReal

/-- A full-measure increasing exhaustion gives uniform convergence of its kernel integrals
on compact sets, provided the restricted and limiting integrals are continuous. -/
theorem tendstoUniformlyOn_setIntegral_of_exhaustion
    {X Y : Type*} [TopologicalSpace X] [MeasurableSpace Y] {μ : Measure Y}
    {S : Set X} (hS : IsCompact S) {O : Set Y} {K : ℕ → Set Y}
    (hKm : ∀ n, MeasurableSet (K n)) (hKmono : Monotone K)
    (hKsub : ∀ n, K n ⊆ O) (hfull : μ (O \ ⋃ n, K n) = 0)
    {F : X → Y → ℝ}
    (hint : ∀ x ∈ S, IntegrableOn (F x) O μ)
    (hnonneg : ∀ x ∈ S, ∀ y ∈ O, 0 ≤ F x y)
    (hcont : ∀ n, ContinuousOn (fun x => ∫ y in K n, F x y ∂μ) S)
    (hcontlim : ContinuousOn (fun x => ∫ y in O, F x y ∂μ) S) :
    TendstoUniformlyOn (fun n x => ∫ y in K n, F x y ∂μ)
      (fun x => ∫ y in O, F x y ∂μ) atTop S := by
  have hUnion : (⋃ n, K n) ⊆ O := iUnion_subset hKsub
  have hEq : (⋃ n, K n) =ᵐ[μ] O := by
    rw [ae_eq_set]
    exact ⟨by simp [sdiff_eq_empty.mpr hUnion], hfull⟩
  refine Monotone.tendstoUniformlyOn_of_forall_tendsto hS hcont ?_ hcontlim ?_
  · intro x hx i j hij
    apply setIntegral_mono_set ((hint x hx).mono_set (hKsub j))
    · filter_upwards [ae_restrict_mem (hKm j)] with y hy
      exact hnonneg x hx y (hKsub j hy)
    · exact (hKmono hij).eventuallySubset
  · intro x hx
    have h := tendsto_setIntegral_of_monotone hKm hKmono ((hint x hx).mono_set hUnion)
    rwa [Measure.restrict_congr_set hEq] at h


/-- The Green-potential Hölder property for bounded measurable densities gives uniform
approximation by a full-measure increasing exhaustion. -/
theorem greenPotential_tendstoUniformlyOn_of_exhaustion
    {μ : Measure ℂ} {O S : Set ℂ} {K : ℕ → Set ℂ}
    (hO : Bornology.IsBounded O) (hS : IsCompact S) (hSO : S ⊆ closure O)
    (hKm : ∀ n, MeasurableSet (K n)) (hKmono : Monotone K)
    (hKsub : ∀ n, K n ⊆ O) (hfull : μ (O \ ⋃ n, K n) = 0)
    (hholder : ∀ f : ℂ → ℝ, MemLp f ⊤ (μ.restrict (closure O)) →
      (∀ x ∈ closure O, IntegrableOn (fun y => greenFunction O x y * f y) O μ) ∧
      ∃ C r : ℝ≥0, 0 < r ∧
        HolderOnWith C r (fun x => ∫ y in O, greenFunction O x y * f y ∂μ) (closure O)) :
    TendstoUniformlyOn (fun n x => ∫ y in K n, greenFunction O x y ∂μ)
      (greenPotential O μ) atTop S := by
  have hpot : (fun x => ∫ y in O, greenFunction O x y ∂μ) = greenPotential O μ := by
    funext x
    exact setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun y hy => greenFunction_of_notMem_right hy x)
  rw [← hpot]
  obtain ⟨hint, C, r, hr, hcont⟩ := hholder (fun _ => 1) (memLp_top_const (1 : ℝ))
  refine tendstoUniformlyOn_setIntegral_of_exhaustion hS hKm hKmono hKsub hfull ?_ ?_ ?_ ?_
  · intro x hx
    simpa only [mul_one] using hint x (hSO hx)
  · intro x hx y hy
    exact greenFunction_nonneg hO x y
  · intro n
    obtain ⟨_, Cn, rn, hrn, hcn⟩ := hholder ((K n).indicator (fun _ => 1))
      ((memLp_top_const (1 : ℝ)).indicator (hKm n))
    have heq : (fun x => ∫ y in O, greenFunction O x y * (K n).indicator (fun _ => 1) y ∂μ) =
        (fun x => ∫ y in K n, greenFunction O x y ∂μ) := by
      funext x
      have hind : (fun y => greenFunction O x y * (K n).indicator (fun _ => 1) y) =
          (K n).indicator (greenFunction O x) := by
        funext y
        by_cases hy : y ∈ K n <;> simp [hy]
      rw [hind, integral_indicator (hKm n), Measure.restrict_restrict_of_subset (hKsub n)]
    rw [heq] at hcn
    exact (hcn.continuousOn hrn).mono hSO
  · simpa only [mul_one] using (hcont.continuousOn hr).mono hSO


/-- A uniform positive lower bound for the limiting potential passes, up to an
arbitrarily small error, to every sufficiently large restricted potential. -/
theorem eventually_lower_bound_of_tendstoUniformlyOn
    {X : Type*} {S : Set X} {f : ℕ → X → ℝ} {g : X → ℝ}
    (h : TendstoUniformlyOn f g atTop S) {m ε : ℝ} (hε : 0 < ε)
    (hmin : ∀ x ∈ S, m ≤ g x) :
    ∀ᶠ n in atTop, ∀ x ∈ S, m - ε < f n x := by
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp h) ε hε] with n hn x hx
  have hd := hn x hx
  rw [Real.dist_eq] at hd
  have := (abs_lt.mp hd).2
  linarith [hmin x hx]


/-- Intersecting with a compact exhaustion of an open set turns an increasing
compact family into an increasing compact family contained in that open set. -/
theorem exists_compact_exhaustion_inter_open
    {O : Set ℂ} (hO : IsOpen O) {K : ℕ → Set ℂ}
    (hK : ∀ n, IsCompact (K n)) (hmono : Monotone K) :
    ∃ L : ℕ → Set ℂ, (∀ n, IsCompact (L n)) ∧ Monotone L ∧
      (∀ n, L n ⊆ K n ∩ O) ∧ (⋃ n, L n) = O ∩ ⋃ n, K n := by
  let : LocallyCompactSpace O := hO.locallyCompactSpace
  let C : CompactExhaustion O := CompactExhaustion.choice O
  let L : ℕ → Set ℂ := fun n => K n ∩ (Subtype.val '' C n)
  refine ⟨L, ?_, ?_, ?_, ?_⟩
  · intro n
    exact (hK n).inter_right ((C.isCompact n).image continuous_subtype_val).isClosed
  · intro i j hij x hx
    exact ⟨hmono hij hx.1, Set.image_mono (C.subset hij) hx.2⟩
  · intro n x hx
    exact ⟨hx.1, by obtain ⟨y, _, rfl⟩ := hx.2; exact y.property⟩
  · apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨n, hn⟩ := mem_iUnion.mp hx
      exact ⟨by obtain ⟨y, _, rfl⟩ := hn.2; exact y.property, mem_iUnion.mpr ⟨n, hn.1⟩⟩
    · intro x hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx.2
      obtain ⟨j, hj⟩ := C.exists_mem ⟨x, hx.1⟩
      refine mem_iUnion.mpr ⟨max i j, hmono (le_max_left i j) hi, ?_⟩
      exact ⟨⟨x, hx.1⟩, C.subset (le_max_right i j) hj, rfl⟩

end HarmonicBalls.Section6

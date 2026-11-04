import HarmonicBalls.Proofs.Sec6.ExitTimeExhaustion
import Mathlib.Topology.Compactness.SigmaCompact

/-! # Relatively compact open exhaustions

Every open subset of the plane admits an increasing exhaustion by open sets
whose closures are compact and contained in the next set.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Set Filter MarkovProcess Metric
open scoped ENNReal NNReal Topology ZeroAtInfty

/-- An open planar domain admits a nested, relatively compact open exhaustion. -/
theorem exists_relativelyCompact_open_exhaustion {U : Set ℂ} (hU : IsOpen U) :
    ∃ D : ℕ → Set ℂ, (∀ n, IsOpen (D n)) ∧ Monotone D ∧
      (∀ n, IsCompact (closure (D n))) ∧
      (∀ n, closure (D n) ⊆ D (n + 1)) ∧ (⋃ n, D n) = U := by
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let K : CompactExhaustion U := CompactExhaustion.choice U
  let D : ℕ → Set ℂ := fun n => Subtype.val '' interior (K (n + 1))
  have hDopen : ∀ n, IsOpen (D n) := fun n =>
    hU.isOpenMap_subtype_val _ isOpen_interior
  have hKcompact : ∀ n, IsCompact (Subtype.val '' K n) := fun n =>
    (K.isCompact n).image continuous_subtype_val
  have hclosure : ∀ n, closure (D n) ⊆ Subtype.val '' K (n + 1) := by
    intro n
    apply closure_minimal _ (hKcompact (n + 1)).isClosed
    exact image_mono interior_subset
  have hnext : ∀ n, closure (D n) ⊆ D (n + 1) := by
    intro n
    exact (hclosure n).trans (image_mono (K.subset_interior_succ (n + 1)))
  refine ⟨D, hDopen, ?_, ?_, hnext, ?_⟩
  · exact monotone_nat_of_le_succ (fun n => subset_closure.trans (hnext n))
  · intro n
    exact (hKcompact (n + 1)).of_isClosed_subset isClosed_closure (hclosure n)
  · apply Subset.antisymm
    · rintro x hx
      obtain ⟨n, y, hy, rfl⟩ := mem_iUnion.mp hx
      exact y.property
    · intro x hx
      let y : U := ⟨x, hx⟩
      obtain ⟨n, hn⟩ := K.exists_mem y
      exact mem_iUnion.mpr ⟨n, y, K.subset_interior_succ n hn, rfl⟩

/-- Compact-local generator extensions yield the stopped representation of a
restricted Green potential. -/
theorem restricted_greenPotential_stopped_representation_of_compact_generator_extensions
    {μ : Measure ℂ} {U L : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hL : IsCompact L) (hLU : L ⊆ U)
    (hholder : ∀ f : ℂ → ℝ, MemLp f ⊤ (μ.restrict (closure U)) →
      (∀ x ∈ closure U, IntegrableOn (fun y => greenFunction U x y * f y) U μ) ∧
      ∃ C t : ℝ≥0, 0 < t ∧
        HolderOnWith C t (fun x => ∫ y in U, greenFunction U x y * f y ∂μ) (closure U))
    {x : ℂ} (hx : x ∈ U \ L)
    (hext : ∀ K : Set ℂ, IsCompact K → K ⊆ U \ L →
      ∃ f : isFellerKernelSemigroup_planarHeatSemigroup.c0Semigroup.generatorDomain,
        (∀ z ∈ K, (∫ y in L, greenFunction U z y ∂μ) = (f : C₀(ℂ, ℝ)) z) ∧
        ∀ z ∈ K, (isFellerKernelSemigroup_planarHeatSemigroup.c0Semigroup.generator f) z = 0) :
    ENNReal.ofReal (∫ y in L, greenFunction U x y ∂μ) ≤ ∫⁻ ω,
      ENNReal.ofReal (∫ y in L,
        greenFunction U (ω ((ContinuousPath.exitTime (U \ L) ω).toNNReal)) y ∂μ)
          ∂(planarBrownianMotion x) := by
  obtain ⟨D, hopen, hmono, hcompact, hnext, hunion⟩ :=
    exists_relativelyCompact_open_exhaustion (hU.sdiff hL.isClosed)
  apply restricted_greenPotential_stopped_representation_of_local_generator_approximation
    hU hUb hL hLU hholder hx hopen hmono hunion
  intro n ε hε
  have hsub : closure (D n) ⊆ U \ L := by
    rw [← hunion]
    exact (hnext n).trans (subset_iUnion D (n + 1))
  obtain ⟨f, hf, hgen⟩ := hext (closure (D n)) (hcompact n) hsub
  refine ⟨f, ?_, ?_⟩
  · intro z hz
    rw [hf z hz, sub_self, abs_zero]
    exact hε.le
  · intro z hz
    exact hgen z (subset_closure hz)

end HarmonicBalls.Section6

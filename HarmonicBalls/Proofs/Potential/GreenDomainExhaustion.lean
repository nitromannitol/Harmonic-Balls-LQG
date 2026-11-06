import HarmonicBalls.Proofs.Sec5.ExhaustionClusterCompatibility
import HarmonicBalls.Proofs.Potential.GreenRegularDomainExhaustion

/-! # Green kernels along open exhaustions

The sweeping and Green-function arguments use the potential-theoretic
infrastructure of Leonardo Bonanno.
-/

namespace HarmonicBalls

open Set Filter
open scoped Topology

/-- Every point of the union eventually belongs to a monotone exhaustion. -/
theorem eventually_mem_open_exhaustion (V : ℕ → Set ℂ) (hmono : Monotone V)
    {U : Set ℂ} (hcover : (⋃ n, V n) = U) {x : ℂ} (hx : x ∈ U) :
    ∀ᶠ n in atTop, x ∈ V n := by
  obtain ⟨N, hN⟩ := mem_iUnion.mp (hcover ▸ hx)
  filter_upwards [eventually_ge_atTop N] with n hn
  exact hmono hn hN

/-- Domain monotonicity makes the kernels nondecreasing at every pair,
including before the pole or evaluation point enters the exhaustion. -/
theorem monotone_greenFunction_of_exhaustion
    (V : ℕ → Set ℂ) (hmono : Monotone V) {U : Set ℂ}
    (hUb : Bornology.IsBounded U) (hcover : (⋃ n, V n) = U) (z x : ℂ) :
    Monotone (fun n => greenFunction (V n) z x) := by
  intro m n hmn
  apply Section6.greenFunction_le_of_subset (hmono hmn)
  apply hUb.subset
  rw [← hcover]
  exact subset_iUnion V n

/-- The Green kernels of an increasing open exhaustion converge to the kernel
of its bounded open union. Neither boundary regularity nor containment of the
pole in the first member is required. -/
theorem tendsto_greenFunction_of_exhaustion
    (V : ℕ → Set ℂ) (hopen : ∀ n, IsOpen (V n)) (hmono : Monotone V)
    {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hcover : (⋃ n, V n) = U) {z x : ℂ} (hz : z ∈ U)
    (hx : x ∈ U) (hzx : z ≠ x) :
    Tendsto (fun n => greenFunction (V n) z x) atTop (𝓝 (greenFunction U z x)) := by
  obtain ⟨N, hN⟩ := mem_iUnion.mp (hcover ▸ hz)
  let W : ℕ → Set ℂ := fun n => V (n + N)
  have hWmono : Monotone W := fun _ _ h => hmono (Nat.add_le_add_right h N)
  have hWcover : (⋃ n, W n) = U := by
    apply Subset.antisymm
    · rw [← hcover]
      exact iUnion_subset fun n => subset_iUnion V _
    · rw [← hcover]
      refine iUnion_subset fun n => ?_
      exact (hmono (show n ≤ n + N by omega)).trans (subset_iUnion W n)
  have h := tendsto_greenFunction_of_open_exhaustion W (fun n => hopen _) hWmono
    hU hUb hWcover (by simpa [W] using hN) hx (Ne.symm hzx)
  exact (tendsto_add_atTop_iff_nat N).mp h

/-- Closure nesting supplies monotonicity, and the two evaluation points
are eventually in every member of the exhaustion. -/
theorem tendsto_greenFunction_of_relativelyCompact_exhaustion
    (V : ℕ → Set ℂ) (hopen : ∀ n, IsOpen (V n))
    (hnext : ∀ n, closure (V n) ⊆ V (n + 1))
    {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hcover : (⋃ n, V n) = U) {z x : ℂ} (hz : z ∈ U)
    (hx : x ∈ U) (hzx : z ≠ x) :
    (∀ᶠ n in atTop, z ∈ V n ∧ x ∈ V n) ∧
      Tendsto (fun n => greenFunction (V n) z x) atTop (𝓝 (greenFunction U z x)) := by
  have hmono : Monotone V := monotone_nat_of_le_succ fun n => subset_closure.trans (hnext n)
  exact ⟨(eventually_mem_open_exhaustion V hmono hcover hz).and
    (eventually_mem_open_exhaustion V hmono hcover hx),
    tendsto_greenFunction_of_exhaustion V hopen hmono hU hUb hcover hz hx hzx⟩

/-- A bounded open planar domain has a Green-regular exhaustion whose kernels
converge pointwise away from the pole. -/
theorem exists_greenRegular_exhaustion_with_kernel_limit
    {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U) {z : ℂ} (hz : z ∈ U) :
    ∃ V : ℕ → Set ℂ, (∀ n, IsOpen (V n)) ∧ Monotone V ∧
      (⋃ n, V n) = U ∧ (∀ n, closure (V n) ⊆ U) ∧
      (∀ n, z ∈ V n) ∧
      (∀ n, ∀ y ∈ closure (V n), y ∉ V n →
        Tendsto (greenFunction (V n) z) (𝓝[V n] y) (𝓝 0)) ∧
      ∀ x ∈ U, z ≠ x →
        Tendsto (fun n => greenFunction (V n) z x) atTop (𝓝 (greenFunction U z x)) := by
  obtain ⟨V, hopen, hmono, hcover, hcompact, hpole, hregular⟩ :=
    exists_greenRegular_exhaustion hU hUb hz
  exact ⟨V, hopen, hmono, hcover, hcompact, hpole, hregular,
    fun x hx hzx => tendsto_greenFunction_of_exhaustion V hopen hmono hU hUb hcover hz hx hzx⟩

#print axioms monotone_greenFunction_of_exhaustion
#print axioms tendsto_greenFunction_of_exhaustion
#print axioms tendsto_greenFunction_of_relativelyCompact_exhaustion
#print axioms exists_greenRegular_exhaustion_with_kernel_limit

end HarmonicBalls

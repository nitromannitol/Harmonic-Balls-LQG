import HarmonicBalls.Proofs.Potential.GreenDomainExhaustion

/-! # Transfer of Green reciprocity by exhaustion

The sweeping and exhaustion infrastructure uses the potential-theoretic
work of Leonardo Bonanno. Finite-disc reciprocity is an explicit assumption;
it is not established here.
-/

namespace HarmonicBalls

open Set Filter Metric
open scoped Topology

/-- Reciprocity on finite unions of open discs transfers to every bounded
open planar set. The premise includes overlapping discs and is not proved by
this theorem. The prescribed diagonal and exterior values are included. -/
theorem greenFunction_reciprocity_of_finite_disc_reciprocity
    (hdisc : ∀ (A : Set ℂ) (r : A → ℝ) (F : Finset A),
      (∀ a ∈ F, 0 < r a) → ∀ x y : ℂ,
        greenFunction (⋃ a ∈ F, ball (a : ℂ) (r a)) x y =
          greenFunction (⋃ a ∈ F, ball (a : ℂ) (r a)) y x)
    {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (x y : ℂ) : greenFunction U x y = greenFunction U y x := by
  by_cases hx : x ∈ U
  · by_cases hy : y ∈ U
    · by_cases hxy : x = y
      · subst y
        rfl
      · obtain ⟨r, F, hr, hF, hopen, hmono, hcover, hclosure, hpole⟩ :=
          exists_finite_disc_open_exhaustion hU hx
        let V : ℕ → Set ℂ := fun n => ⋃ a ∈ F n, ball (a : ℂ) (r a)
        have hforward := tendsto_greenFunction_of_exhaustion V hopen hmono hU hUb hcover hx hy hxy
        have hreverse := tendsto_greenFunction_of_exhaustion V hopen hmono hU hUb hcover hy hx (Ne.symm hxy)
        apply tendsto_nhds_unique hforward
        convert hreverse using 1
        funext n
        exact hdisc U r (F n) (fun a _ => (hr a).1) x y
    · rw [greenFunction_of_notMem_right hy, greenFunction_of_notMem_left hy]
  · rw [greenFunction_of_notMem_left hx, greenFunction_of_notMem_right hx]

#print axioms greenFunction_reciprocity_of_finite_disc_reciprocity

end HarmonicBalls

import HarmonicBalls.FirstPass.S11i.GaussianMix
import HarmonicBalls.Defs.GFF

/-!
# Step 8 helper: finite families of GFF pairings are jointly Gaussian

Source: `IsWholePlaneGFF.isGaussianProcess` (Defs/GFF.lean, Duplantier-Sheffield 2011, Section 3.1 and eq:cov-kernel,
corrected paper lines 356-365): every finite family of admissible observables is a Gaussian vector. Here the family
is the pairings `ω ↦ hC ω (ψ k)` with test functions `ψ k`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace HarmonicBalls

/-- A finite family of pairings of the whole-plane GFF with test functions is jointly Gaussian. -/
theorem hasGaussianLaw_pairing_family {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc)
    {ι : Type*} [Fintype ι] (ψ : ι → (ℂ → ℝ)) (hψ : ∀ k, IsTestFunction Set.univ (ψ k)) :
    HasGaussianLaw (fun ω (k : ι) => hC ω (ψ k)) P := by
  classical
  let obs : ι → GFFObservable.Admissible := fun k => ⟨GFFObservable.pairing (ψ k), hψ k⟩
  let I : Finset GFFObservable.Admissible := Finset.univ.image obs
  have hG := hh.isGaussianProcess.hasGaussianLaw I
  let L : (I → ℝ) →L[ℝ] (ι → ℝ) := LinearMap.toContinuousLinearMap
    { toFun := fun v k => v ⟨obs k, Finset.mem_image_of_mem _ (Finset.mem_univ k)⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have h := hG.map L
  convert h using 1
  funext ω k
  rfl

end HarmonicBalls

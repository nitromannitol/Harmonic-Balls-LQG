import HarmonicBalls.Proofs.Potential.GeneralDomainGreenProductIntegrability
import HarmonicBalls.Proofs.Potential.FiniteDiscGreenReciprocity

/-! # Reciprocity of the Green pairing

The potential-theoretic infrastructure uses work of Leonardo Bonanno.
-/

namespace HarmonicBalls

open MeasureTheory Set Filter
open scoped ENNReal

/-- Bounded signed densities have an absolutely integrable Green pairing on a
bounded open planar domain. Fubini's theorem and Green-kernel reciprocity give
symmetry of the two actual iterated Bochner integrals. -/
theorem green_reciprocal_pairing {V : Set ℂ}
    (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    {f g : ℂ → ℝ} (hf : AEStronglyMeasurable f (volume.restrict V))
    (hg : AEStronglyMeasurable g (volume.restrict V))
    {C D : ℝ} (hf_bound : ∀ᵐ x ∂volume.restrict V, ‖f x‖ ≤ C)
    (hg_bound : ∀ᵐ x ∂volume.restrict V, ‖g x‖ ≤ D) :
    Integrable (fun p : ℂ × ℂ => (f p.1 * greenFunction V p.1 p.2) * g p.2)
        ((volume.restrict V).prod (volume.restrict V)) ∧
    (∀ᵐ x ∂volume.restrict V,
      Integrable (fun y => greenFunction V x y * g y) (volume.restrict V)) ∧
    (∀ᵐ y ∂volume.restrict V,
      Integrable (fun x => greenFunction V y x * f x) (volume.restrict V)) ∧
    Integrable (fun x => f x * ∫ y in V, greenFunction V x y * g y) (volume.restrict V) ∧
    Integrable (fun y => g y * ∫ x in V, greenFunction V y x * f x) (volume.restrict V) ∧
    (∫ x in V, f x * ∫ y in V, greenFunction V x y * g y) =
      ∫ y in V, g y * ∫ x in V, greenFunction V y x * f x := by
  obtain ⟨r, hr⟩ := hVb.subset_ball (0 : ℂ)
  have hfin : volume V < ∞ := (measure_mono hr).trans_lt measure_ball_lt_top
  let : IsFiniteMeasure (volume.restrict V) := isFiniteMeasure_restrict.2 hfin.ne
  have hk := generalDomain_green_integrable_product_volume hV hVb
    (ν := volume.restrict V) (ae_restrict_mem hV.measurableSet)
  have hfp : ∀ᵐ p ∂(volume.restrict V).prod (volume.restrict V), ‖f p.1‖ ≤ C :=
    Measure.quasiMeasurePreserving_fst.ae hf_bound
  have hgp : ∀ᵐ p ∂(volume.restrict V).prod (volume.restrict V), ‖g p.2‖ ≤ D :=
    Measure.quasiMeasurePreserving_snd.ae hg_bound
  have hi : Integrable (fun p : ℂ × ℂ => (f p.1 * greenFunction V p.1 p.2) * g p.2)
      ((volume.restrict V).prod (volume.restrict V)) := by
    have h := (hk.mul_bdd hf.comp_fst hfp).mul_bdd hg.comp_snd hgp
    convert h using 1; ext p; ring
  have hl : (fun x => ∫ y in V, (f x * greenFunction V x y) * g y) =
      (fun x => f x * ∫ y in V, greenFunction V x y * g y) := by
    funext x
    rw [← integral_const_mul]
    congr 1
    funext y
    ring
  have hr' : (fun y => ∫ x in V, (f x * greenFunction V x y) * g y) =
      (fun y => g y * ∫ x in V, greenFunction V y x * f x) := by
    funext y
    rw [← integral_const_mul]
    congr 1
    funext x
    rw [greenFunction_bounded_open_comm hV hVb y x]
    ring
  refine ⟨hi, ?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hk.prod_right_ae] with x hx
    exact hx.mul_bdd hg hg_bound
  · filter_upwards [hk.prod_left_ae] with y hy
    have h := hy.mul_bdd hf hf_bound
    convert h using 1
    ext x
    rw [greenFunction_bounded_open_comm hV hVb]
  · simpa only [hl] using hi.integral_prod_left
  · simpa only [hr'] using hi.integral_prod_right
  · rw [← hl, ← hr']
    exact integral_integral_swap hi

#print axioms green_reciprocal_pairing

end HarmonicBalls

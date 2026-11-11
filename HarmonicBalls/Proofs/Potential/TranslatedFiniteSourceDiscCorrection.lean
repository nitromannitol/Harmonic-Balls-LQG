import HarmonicBalls.Proofs.Potential.FiniteSourceDiscCorrection
import HarmonicBalls.Proofs.Sec6.GreenTranslation

/-! # Finite-source correction for translated discs

This analytic leaf uses the potential-theoretic work of Leonardo Bonanno.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set InnerProductSpace
open HarmonicBalls.Section6

/-- The harmonic disc correction after translating the centre to the origin. -/
noncomputable def translatedDiscSourceCorrection (c : ℂ) (R : ℝ)
    (ν : Measure ℂ) (x : ℂ) : ℝ :=
  discSourceCorrection R (ν.map (fun y => y - c)) (x - c)

private theorem translate_ball (c : ℂ) (R : ℝ) :
    (fun z : ℂ => z + c) '' ball 0 R = ball c R := by simp

private theorem translate_univ (c : ℂ) :
    (fun z : ℂ => z + c) '' univ = univ := by
  exact Set.image_univ_of_surjective (fun z => ⟨z - c, by simp⟩)

private theorem kernel_translate (O : Set ℂ) (c x y : ℂ) :
    greenFunction ((fun z : ℂ => z + c) '' O) x y =
      greenFunction O (x - c) (y - c) := by
  simpa using greenFunction_translate O c (x - c) (y - c)

private theorem potential_translate (O : Set ℂ) (hO : IsOpen O)
    (ν : Measure ℂ) (c x : ℂ) :
    greenPotential ((fun z : ℂ => z + c) '' O) ν x =
      greenPotential O (ν.map (fun y => y - c)) (x - c) := by
  simpa using greenPotential_translate hO ν c (x - c)

/-- The translated correction is harmonic for a compactly concentrated finite source. -/
theorem harmonicOnNhd_translatedDiscSourceCorrection
    {c : ℂ} {R : ℝ} {K : Set ℂ} {ν : Measure ℂ} [IsFiniteMeasure ν]
    (hR : 0 < R) (hK : IsCompact K) (hKB : K ⊆ ball c R) (hν : ν Kᶜ = 0) :
    HarmonicOnNhd (translatedDiscSourceCorrection c R ν) (ball c R) := by
  let e : ℂ ≃ₜ ℂ := Homeomorph.subRight c
  let K₀ := e '' K
  have hK₀ : IsCompact K₀ := hK.image e.continuous
  have hK₀B : K₀ ⊆ ball (0 : ℂ) R := by
    rintro x ⟨y, hy, rfl⟩
    simpa [e, mem_ball, dist_eq_norm] using hKB hy
  have heK : e ⁻¹' K₀ = K := e.injective.preimage_image K
  have hν₀K : (ν.map e) K₀ᶜ = 0 := by
    rw [Measure.map_apply e.measurable hK₀.isClosed.measurableSet.compl]
    simpa only [preimage_compl, heK] using hν
  have hh := harmonicOnNhd_discSourceCorrection hR hK₀ hK₀B hν₀K
  intro x hx
  have hx₀ : e x ∈ ball (0 : ℂ) R := by
    simpa [e, mem_ball, dist_eq_norm] using hx
  have ht := harmonicAt_comp_add_right (x := x) (b := -c) (by
    simpa [e, sub_eq_add_neg] using hh (e x) hx₀)
  change HarmonicAt (fun z => discSourceCorrection R (ν.map (fun y => y - c)) (z - c)) x
  simpa [e, sub_eq_add_neg] using ht

/-- At an uncharged interior observer, the whole-plane potential is the disc
potential plus the translated correction. -/
theorem greenPotential_univ_eq_translatedDisc_add_correction
    {c : ℂ} {R : ℝ} {ν : Measure ℂ} {x : ℂ} (hR : 0 < R)
    (hν : ∀ᵐ y ∂ν, y ∈ ball c R) (hx : x ∈ ball c R) (hatom : ν {x} = 0)
    (huniv : Integrable (fun y => greenFunction univ x y) ν)
    (hball : Integrable (fun y => greenFunction (ball c R) x y) ν) :
    greenPotential univ ν x = greenPotential (ball c R) ν x +
      translatedDiscSourceCorrection c R ν x := by
  let e : ℂ ≃ᵐ ℂ := MeasurableEquiv.subRight c
  have hν₀ : ∀ᵐ y ∂ν.map e, y ∈ ball (0 : ℂ) R := by
    apply (ae_map_iff e.measurable.aemeasurable measurableSet_ball).2
    filter_upwards [hν] with y hy
    change y - c ∈ ball (0 : ℂ) R
    simpa [mem_ball, dist_eq_norm] using hy
  have hx₀ : x - c ∈ ball (0 : ℂ) R := by
    simpa [mem_ball, dist_eq_norm] using hx
  have hatom₀ : (ν.map e) {x - c} = 0 := by
    rw [Measure.map_apply e.measurable (measurableSet_singleton _)]
    have he : e ⁻¹' {x - c} = {x} := by
      ext y
      change y - c = x - c ↔ y = x
      simp
    rw [he, hatom]
  have hu₀ : Integrable (fun y => greenFunction univ (x - c) y) (ν.map e) := by
    apply e.measurableEmbedding.integrable_map_iff.mpr
    have heq : (fun y => greenFunction univ (x - c) (e y)) =
        (fun y => greenFunction univ x y) := by
      funext y
      change greenFunction univ (x - c) (y - c) = _
      simpa only [translate_univ] using (kernel_translate univ c x y).symm
    simpa only [Function.comp_def, heq] using huniv
  have hb₀ : Integrable (fun y => greenFunction (ball 0 R) (x - c) y) (ν.map e) := by
    apply e.measurableEmbedding.integrable_map_iff.mpr
    have heq : (fun y => greenFunction (ball 0 R) (x - c) (e y)) =
        (fun y => greenFunction (ball c R) x y) := by
      funext y
      change greenFunction (ball 0 R) (x - c) (y - c) = _
      simpa [translate_ball] using (kernel_translate (ball 0 R) c x y).symm
    simpa only [Function.comp_def, heq] using hball
  have h := greenPotential_univ_eq_ball_add_discSourceCorrection hR hν₀ hx₀ hatom₀ hu₀ hb₀
  have hu := potential_translate univ isOpen_univ ν c x
  have hb := potential_translate (ball 0 R) isOpen_ball ν c x
  change greenPotential univ (ν.map (fun y => y - c)) (x - c) =
    greenPotential (ball 0 R) (ν.map (fun y => y - c)) (x - c) + _ at h
  simpa only [translatedDiscSourceCorrection, translate_univ, translate_ball] using
    (show greenPotential ((fun z : ℂ => z + c) '' univ) ν x =
      greenPotential ((fun z : ℂ => z + c) '' ball 0 R) ν x +
        discSourceCorrection R (ν.map (fun y => y - c)) (x - c) by rw [hu, hb]; exact h)

/-- Both kernels are integrable, the observer is uncharged, and the correction
identity holds at planar-almost every observer in the translated disc. -/
theorem ae_greenPotential_univ_eq_translatedDisc_add_correction
    {c : ℂ} {R : ℝ} {ν : Measure ℂ} [IsFiniteMeasure ν] (hR : 0 < R)
    (hν : ∀ᵐ y ∂ν, y ∈ ball c R) :
    ∀ᵐ x ∂volume.restrict (ball c R),
      Integrable (fun y => greenFunction univ x y) ν ∧
      Integrable (fun y => greenFunction (ball c R) x y) ν ∧
      ν {x} = 0 ∧
      greenPotential univ ν x = greenPotential (ball c R) ν x +
        translatedDiscSourceCorrection c R ν x := by
  let e : ℂ ≃ᵐ ℂ := MeasurableEquiv.subRight c
  have hν₀ : ∀ᵐ y ∂ν.map e, y ∈ ball (0 : ℂ) R := by
    apply (ae_map_iff e.measurable.aemeasurable measurableSet_ball).2
    filter_upwards [hν] with y hy
    change y - c ∈ ball (0 : ℂ) R
    simpa [mem_ball, dist_eq_norm] using hy
  have hv : (volume.restrict (ball c R)).map e = volume.restrict (ball 0 R) := by
    have hm : volume.map e = volume := by
      change volume.map (fun z : ℂ => z - c) = volume
      simpa [sub_eq_add_neg] using map_add_right_eq_self (volume : Measure ℂ) (-c)
    have he : e ⁻¹' ball (0 : ℂ) R = ball c R := by
      ext x
      change x - c ∈ ball (0 : ℂ) R ↔ x ∈ ball c R
      simp [mem_ball, dist_eq_norm]
    calc
      (volume.restrict (ball c R)).map e =
          (volume.restrict (e ⁻¹' ball (0 : ℂ) R)).map e := by rw [he]
      _ = (volume.map e).restrict (ball (0 : ℂ) R) := (e.restrict_map _ _).symm
      _ = volume.restrict (ball 0 R) := by rw [hm]
  have hbase := ae_greenPotential_univ_eq_ball_add_discSourceCorrection hR hν₀
  have htransport := e.measurableEmbedding.ae_map_iff.mp (hv.symm ▸ hbase)
  filter_upwards [htransport, ae_restrict_mem measurableSet_ball] with x hx hxball
  have hu : Integrable (fun y => greenFunction univ x y) ν := by
    have hi := e.measurableEmbedding.integrable_map_iff.mp hx.1
    have heq : (fun y => greenFunction univ (x - c) (e y)) =
        (fun y => greenFunction univ x y) := by
      funext y
      change greenFunction univ (x - c) (y - c) = _
      simpa only [translate_univ] using (kernel_translate univ c x y).symm
    change Integrable ((fun y => greenFunction univ (x - c) y) ∘ e) ν at hi
    simpa only [Function.comp_def, heq] using hi
  have hb : Integrable (fun y => greenFunction (ball c R) x y) ν := by
    have hi := e.measurableEmbedding.integrable_map_iff.mp hx.2.1
    have heq : (fun y => greenFunction (ball 0 R) (x - c) (e y)) =
        (fun y => greenFunction (ball c R) x y) := by
      funext y
      change greenFunction (ball 0 R) (x - c) (y - c) = _
      simpa only [translate_ball] using (kernel_translate (ball 0 R) c x y).symm
    change Integrable ((fun y => greenFunction (ball 0 R) (x - c) y) ∘ e) ν at hi
    simpa only [Function.comp_def, heq] using hi
  have hatom : ν {x} = 0 := by
    have he : e ⁻¹' {x - c} = {x} := by
      ext y
      change y - c = x - c ↔ y = x
      simp
    have ht := hx.2.2.1
    change (ν.map e) {x - c} = 0 at ht
    rw [Measure.map_apply e.measurable (measurableSet_singleton _), he] at ht
    exact ht
  exact ⟨hu, hb, hatom,
    greenPotential_univ_eq_translatedDisc_add_correction hR hν hxball hatom hu hb⟩


end HarmonicBalls

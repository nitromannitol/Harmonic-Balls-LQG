import HarmonicBalls.Proofs.Potential.DiscSourceFreeHarmonicity
import HarmonicBalls.Proofs.Sec6.GreenTranslation

/-! # Source-free potentials on translated discs

The potential-theoretic infrastructure uses work of Leonardo Bonanno. These
results are analytic leaves, not a closure of a numbered paper result.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set InnerProductSpace
open HarmonicBalls.Section6

/-- A finite compactly concentrated source has a harmonic Green potential
outside its concentration set, for a disc with arbitrary centre. -/
theorem harmonicOnNhd_greenPotential_translatedDisc_of_compact_source
    {c : ℂ} {R : ℝ} {K : Set ℂ} {ν : Measure ℂ} [IsFiniteMeasure ν]
    (hK : IsCompact K) (hKB : K ⊆ ball c R) (hν : ν Kᶜ = 0) :
    HarmonicOnNhd (greenPotential (ball c R) ν) (ball c R \ K) := by
  let e : ℂ ≃ₜ ℂ := Homeomorph.subRight c
  let K₀ := e '' K
  let ν₀ := ν.map e
  have hK₀ : IsCompact K₀ := hK.image e.continuous
  have hK₀B : K₀ ⊆ ball (0 : ℂ) R := by
    rintro x ⟨y, hy, rfl⟩
    simpa [e, mem_ball, dist_eq_norm] using hKB hy
  have heK : e ⁻¹' K₀ = K := e.injective.preimage_image K
  have hν₀K : ν₀ K₀ᶜ = 0 := by
    rw [Measure.map_apply e.measurable hK₀.isClosed.measurableSet.compl]
    simpa only [preimage_compl, heK] using hν
  have hh := harmonicOnNhd_greenPotential_ball_of_compact_source hK₀ hK₀B hν₀K
  have hp : (fun z => greenPotential (ball 0 R) ν₀ (z - c)) =
      greenPotential (ball c R) ν := by
    funext z
    have h := greenPotential_translate (O := ball (0 : ℂ) R) isOpen_ball ν c (z - c)
    simpa [e, ν₀] using h.symm
  intro x hx
  have hx₀ : e x ∈ ball (0 : ℂ) R \ K₀ := by
    constructor
    · simpa [e, mem_ball, dist_eq_norm] using hx.1
    · intro h
      apply hx.2
      rw [← heK]
      exact h
  have ht := harmonicAt_comp_add_right (x := x) (b := -c) (by
    simpa [e, sub_eq_add_neg] using hh (e x) hx₀)
  simpa only [← hp, sub_eq_add_neg] using ht

/-- The potential is continuous off the compact concentration set. -/
theorem continuousOn_greenPotential_translatedDisc_of_compact_source
    {c : ℂ} {R : ℝ} {K : Set ℂ} {ν : Measure ℂ} [IsFiniteMeasure ν]
    (hK : IsCompact K) (hKB : K ⊆ ball c R) (hν : ν Kᶜ = 0) :
    ContinuousOn (greenPotential (ball c R) ν) (ball c R \ K) :=
  (harmonicOnNhd_greenPotential_translatedDisc_of_compact_source hK hKB hν).continuousOn

/-- The potential is harmonic on an open subset carrying no source mass. -/
theorem harmonicOnNhd_greenPotential_translatedDisc_of_source_free_open
    {c : ℂ} {R : ℝ} {K U : Set ℂ} {ν : Measure ℂ} [IsFiniteMeasure ν]
    (hK : IsCompact K) (hKB : K ⊆ ball c R) (hν : ν Kᶜ = 0)
    (hU : IsOpen U) (hUB : U ⊆ ball c R) (hνU : ν U = 0) :
    HarmonicOnNhd (greenPotential (ball c R) ν) U := by
  have hKU : IsCompact (K \ U) := hK.inter_right hU.isClosed_compl
  have hcon : ν (K \ U)ᶜ = 0 := by
    apply measure_mono_null (show (K \ U)ᶜ ⊆ Kᶜ ∪ U from by
      intro y hy
      by_cases hyK : y ∈ K
      · right
        by_contra hyU
        exact hy ⟨hyK, hyU⟩
      · exact Or.inl hyK)
    exact measure_union_null hν hνU
  exact (harmonicOnNhd_greenPotential_translatedDisc_of_compact_source hKU
    (sdiff_subset.trans hKB) hcon).mono (fun x hx => ⟨hUB hx, fun h => h.2 hx⟩)

/-- The potential is continuous on an open subset carrying no source mass. -/
theorem continuousOn_greenPotential_translatedDisc_on_source_free_open
    {c : ℂ} {R : ℝ} {K U : Set ℂ} {ν : Measure ℂ} [IsFiniteMeasure ν]
    (hK : IsCompact K) (hKB : K ⊆ ball c R) (hν : ν Kᶜ = 0)
    (hU : IsOpen U) (hUB : U ⊆ ball c R) (hνU : ν U = 0) :
    ContinuousOn (greenPotential (ball c R) ν) U :=
  (harmonicOnNhd_greenPotential_translatedDisc_of_source_free_open
    hK hKB hν hU hUB hνU).continuousOn


end HarmonicBalls

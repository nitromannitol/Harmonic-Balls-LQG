import HarmonicBalls.FirstPass.S8c.Frequency

/-! # Lifting a periodic almost-sure property from the fundamental box to the plane (FIRST-PASS fp-S8c-8-2-local)

The phase-sensitive very-good event at unit scale is invariant under the period lattice `(1/100) ℤ²` of the phase torus
(every dyadic inner lattice `(2^{-n}/100) ℤ²` contains `(1/100) ℤ²`, G-8-2 section 3). Hence a Lebesgue-almost-sure
statement on the fundamental box `[0, 1/100)²`, which is the image of the phase torus, lifts to Lebesgue-almost every
`w ∈ ℂ`. Pure measure theory: the plane is a countable disjoint union of translates of the box.
-/

open MeasureTheory Set
open scoped ENNReal

namespace HarmonicBalls

/-- The period lattice `(1/100) ℤ²` of the phase torus, as complex numbers. -/
noncomputable def phaseLatticeVec (q : ℤ × ℤ) : ℂ := ⟨(q.1 : ℝ) / 100, (q.2 : ℝ) / 100⟩

/-- The fundamental box `[0, 1/100)²` of the phase torus. -/
def phaseFundamentalBox : Set ℂ :=
  {w | 0 ≤ w.re ∧ w.re < 1 / 100 ∧ 0 ≤ w.im ∧ w.im < 1 / 100}

/-- Every complex number reduces modulo the period lattice to the fundamental box. -/
theorem phaseLattice_reduce (w : ℂ) : ∃ q : ℤ × ℤ, w + -phaseLatticeVec q ∈ phaseFundamentalBox := by
  refine ⟨(⌊100 * w.re⌋, ⌊100 * w.im⌋), ?_⟩
  have h1 := Int.floor_le (100 * w.re)
  have h2 := Int.lt_floor_add_one (100 * w.re)
  have h3 := Int.floor_le (100 * w.im)
  have h4 := Int.lt_floor_add_one (100 * w.im)
  simp only [phaseFundamentalBox, phaseLatticeVec, Set.mem_ofPred_eq, Complex.add_re, Complex.add_im,
    Complex.neg_re, Complex.neg_im]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-- A periodic, measurable-complement property which holds Lebesgue-almost everywhere in the fundamental box holds
Lebesgue-almost everywhere in the plane. -/
theorem ae_of_ae_phaseFundamentalBox (p : ℂ → Prop)
    (hper : ∀ (w : ℂ) (q : ℤ × ℤ), p (w + phaseLatticeVec q) ↔ p w)
    (hS : MeasurableSet {w | ¬ p w})
    (h : ∀ᵐ w ∂(volume.restrict phaseFundamentalBox : Measure ℂ), p w) :
    ∀ᵐ w ∂(volume : Measure ℂ), p w := by
  rw [ae_iff] at h ⊢
  rw [Measure.restrict_apply hS] at h
  have hsub : {w | ¬ p w} ⊆
      ⋃ q : ℤ × ℤ, (fun x => x + -phaseLatticeVec q) ⁻¹' ({w | ¬ p w} ∩ phaseFundamentalBox) := by
    intro w hw
    obtain ⟨q, hq⟩ := phaseLattice_reduce w
    refine Set.mem_iUnion.mpr ⟨q, ?_⟩
    refine ⟨?_, hq⟩
    intro hpx
    apply hw
    have hback := (hper (w + -phaseLatticeVec q) q).mpr hpx
    simpa using hback
  exact measure_mono_null hsub
    (measure_iUnion_null fun q => by
      rw [measure_preimage_add_right]
      exact h)

#print axioms ae_of_ae_phaseFundamentalBox

end HarmonicBalls

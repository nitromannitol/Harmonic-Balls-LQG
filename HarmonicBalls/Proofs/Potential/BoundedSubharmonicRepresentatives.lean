import HarmonicBalls.Audit.GreenSubharmonicTestClass

/-!
# Bounded witnesses for subharmonic tests

A geometric localization and a conditional transport of the two source potentials.
The latter records the separate pointwise and almost-everywhere correction obligations;
it does not establish them. Leonardo Bonanno contributed to this formalization.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set InnerProductSpace

/-- A bounded observation set and a compact source fit in a bounded open subset of
any given open witness. -/
theorem exists_bounded_open_containing_closure_and_compact
    {Λ O K : Set ℂ} (hΛ : Bornology.IsBounded Λ) (hO : IsOpen O)
    (hΛO : closure Λ ⊆ O) (hK : IsCompact K) (hKO : K ⊆ O) :
    ∃ V : Set ℂ, IsOpen V ∧ Bornology.IsBounded V ∧ V ⊆ O ∧
      closure Λ ⊆ V ∧ K ⊆ V := by
  obtain ⟨R, hR⟩ := (hΛ.closure.union hK.isBounded).subset_ball (0 : ℂ)
  refine ⟨O ∩ ball 0 R, hO.inter isOpen_ball,
    isBounded_ball.subset inter_subset_right, inter_subset_left, ?_, ?_⟩
  · exact subset_inter hΛO (subset_union_left.trans hR)
  · exact subset_inter hKO (subset_union_right.trans hR)

/-- Transport a specific witness through two harmonic corrections, provided the old
and new real-valued potentials agree after correction at the pole and almost everywhere.
The two source measures and all their support and sign conditions remain unchanged.
The new negative kernel's pole integrability is a separate hypothesis. -/
theorem bounded_representative_of_source_corrections
    {μ ν₁ ν₂ : Measure ℂ} {Λ O V K : Set ℂ} {z : ℂ}
    {q a b : ℂ → ℝ}
    (hV : IsOpen V) (hVb : Bornology.IsBounded V) (hVO : V ⊆ O)
    (hΛV : closure Λ ⊆ V) (hK : IsCompact K) (hKV : K ⊆ V)
    (hν₁ : IsFiniteMeasure ν₁) (hν₂ : IsFiniteMeasure ν₂)
    (h₁ : ν₁ Kᶜ = 0) (h₂ : ν₂ Kᶜ = 0) (hΛ₁ : ν₁ Λ = 0)
    (hq : HarmonicOnNhd q O) (ha : HarmonicOnNhd a V) (hb : HarmonicOnNhd b V)
    (hz : ν₂ {z} = 0) (hi : Integrable (greenFunction V z) ν₂)
    (h₁z : greenPotential O ν₁ z = a z + greenPotential V ν₁ z)
    (h₂z : greenPotential O ν₂ z = b z + greenPotential V ν₂ z)
    (h₁ae : ∀ᵐ x ∂μ.restrict Λ,
      greenPotential O ν₁ x = a x + greenPotential V ν₁ x)
    (h₂ae : ∀ᵐ x ∂μ.restrict Λ,
      greenPotential O ν₂ x = b x + greenPotential V ν₂ x) :
    ∃ g ∈ boundedSubharmonicBallTestClass Λ z,
      (q + greenPotential O ν₁ - greenPotential O ν₂) z = g z ∧
      (q + greenPotential O ν₁ - greenPotential O ν₂) =ᵐ[μ.restrict Λ] g := by
  let g := (q + a - b) + greenPotential V ν₁ - greenPotential V ν₂
  refine ⟨g, ⟨V, K, ν₁, ν₂, q + a - b, hV, hVb, hΛV, hK, hKV,
    hν₁, hν₂, h₁, h₂, hΛ₁, ((hq.mono hVO).add ha).sub hb, hz, hi, rfl⟩, ?_, ?_⟩
  · dsimp [g, Pi.add_apply, Pi.sub_apply]
    rw [h₁z, h₂z]
    ring
  · filter_upwards [h₁ae, h₂ae] with x hx₁ hx₂
    dsimp [g, Pi.add_apply, Pi.sub_apply]
    rw [hx₁, hx₂]
    ring

/-- The diagonal convention forces a source-by-source correction for a Dirac mass
    to vanish at its atom, for any two domains. -/
theorem dirac_source_correction_at_atom {O V : Set ℂ} {x : ℂ} {a : ℂ → ℝ}
    (h : greenPotential O (Measure.dirac x) x =
      a x + greenPotential V (Measure.dirac x) x) : a x = 0 := by
  simpa only [greenPotential_dirac_self, add_zero] using h.symm

#print axioms dirac_source_correction_at_atom
#print axioms exists_bounded_open_containing_closure_and_compact
#print axioms bounded_representative_of_source_corrections

end HarmonicBalls

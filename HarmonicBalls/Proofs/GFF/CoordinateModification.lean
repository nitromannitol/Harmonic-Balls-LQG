import HarmonicBalls.Defs.GFF

/-! # Coordinatewise modifications of the whole-plane GFF

The related distribution-valued construction is due to Leonardo Bonanno.
Coordinatewise agreement alone does not assert a common samplewise representation. -/

noncomputable section
open MeasureTheory ProbabilityTheory
namespace HarmonicBalls

/-- A measurable coordinatewise modification preserves all six fields of the
whole-plane GFF specification, with circle averages unchanged. -/
theorem IsWholePlaneGFF.coordinateModification
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC hC' : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc)
    (hm : ∀ φ, IsTestFunction Set.univ φ → Measurable fun ω => hC' ω φ)
    (he : ∀ φ, IsTestFunction Set.univ φ → (fun ω => hC ω φ) =ᵐ[P] (fun ω => hC' ω φ)) :
    IsWholePlaneGFF P hC' hcirc := by
  have heval (o : GFFObservable) (ho : o.IsAdmissible) :
      (fun ω => o.eval (hC ω) (hcirc ω)) =ᵐ[P]
        (fun ω => o.eval (hC' ω) (hcirc ω)) := by
    cases o with
    | pairing φ => exact he φ ho
    | circle r z => exact Filter.Eventually.of_forall (fun _ => rfl)
  refine ⟨hm, hh.measurable_circle, hh.isGaussianProcess.congr (fun o => heval o.1 o.2), ?_, ?_, hh.ae_continuousOn_circle⟩
  · intro o ho
    rw [← integral_congr_ae (heval o ho)]
    exact hh.integral_eq_zero o ho
  · intro o o' ho ho'
    have h₁ := heval o ho
    have h₂ := heval o' ho'
    have hi₁ := integral_congr_ae h₁
    have hi₂ := integral_congr_ae h₂
    calc
      cov[fun ω => o.eval (hC' ω) (hcirc ω), fun ω => o'.eval (hC' ω) (hcirc ω); P] =
          cov[fun ω => o.eval (hC ω) (hcirc ω), fun ω => o'.eval (hC ω) (hcirc ω); P] := by
            unfold ProbabilityTheory.covariance
            apply integral_congr_ae
            filter_upwards [h₁, h₂] with ω hω hω'
            rw [← hω, ← hω', ← hi₁, ← hi₂]
      _ = wholePlaneGFFCov o o' := hh.covariance_eq o o' ho ho'

/-- A diagonal spike has measurable sections and vanishes almost surely at
    each fixed index when its parameter has no atoms. -/
theorem diagonalSpike_sections
    {Ω I : Type*} [MeasurableSpace Ω] [DecidableEq I] {P : Measure Ω}
    (t : Ω → ℝ) (ht : Measurable t)
    (hnull : ∀ r, ∀ᵐ ω ∂P, t ω ≠ r)
    (a : ℝ → I) (ha : Function.Injective a) :
    (∀ i, Measurable (fun ω => if i = a (t ω) then (1 : ℝ) else 0)) ∧
    (∀ i, ∀ᵐ ω ∂P, (if i = a (t ω) then (1 : ℝ) else 0) = 0) := by
  classical
  have hsection (i : I) : MeasurableSet {ω | i = a (t ω)} := by
    by_cases hi : ∃ r, i = a r
    · obtain ⟨r, rfl⟩ := hi
      have heq : {ω | a r = a (t ω)} = {ω | t ω = r} := by
        ext ω
        simp only [Set.mem_ofPred_eq]
        constructor
        · intro h
          exact (ha h).symm
        · intro h
          rw [h]
      rw [heq]
      exact measurableSet_eq_fun ht measurable_const
    · have hempty : {ω | i = a (t ω)} = ∅ := by
        ext ω
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        exact fun h => hi ⟨t ω, h⟩
      rw [hempty]
      exact MeasurableSet.empty
  constructor
  · intro i
    exact Measurable.ite (hsection i) measurable_const measurable_const
  · intro i
    by_cases hi : ∃ r, i = a r
    · obtain ⟨r, rfl⟩ := hi
      filter_upwards [hnull r] with ω hω
      have hne : a r ≠ a (t ω) := fun h => hω (ha h).symm
      simp only [hne, ↓reduceIte]
    · filter_upwards with ω
      have hne : i ≠ a (t ω) := fun h => hi ⟨t ω, h⟩
      simp only [hne, ↓reduceIte]

/-- On any GFF probability space carrying a diffuse parameter, the diagonal
modification retains the full GFF specification. If the original pairings
obey the indicated scalar relation, the modified pairings violate it almost
surely. Instantiating this conditional result requires a suitable joint GFF. -/
theorem IsWholePlaneGFF.exists_diagonal_modification
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc)
    (t : Ω → ℝ) (ht : Measurable t)
    (hnull : ∀ r, ∀ᵐ ω ∂P, t ω ≠ r)
    (a : ℝ → (ℂ → ℝ)) (ha : Function.Injective a)
    (hlinear : ∀ᵐ ω ∂P, hC ω (a (2 * t ω)) = 2 * hC ω (a (t ω))) :
    ∃ hC' : Ω → (ℂ → ℝ) → ℝ, IsWholePlaneGFF P hC' hcirc ∧
      (∀ φ, (fun ω => hC ω φ) =ᵐ[P] (fun ω => hC' ω φ)) ∧
      ∀ᵐ ω ∂P, hC' ω (a (2 * t ω)) ≠ 2 * hC' ω (a (t ω)) := by
  classical
  let D : Ω → (ℂ → ℝ) → ℝ := fun ω φ => if φ = a (t ω) then 1 else 0
  have hd := diagonalSpike_sections t ht hnull a ha
  let hC' := fun ω φ => hC ω φ + D ω φ
  have he (φ : ℂ → ℝ) : (fun ω => hC ω φ) =ᵐ[P] (fun ω => hC' ω φ) := by
    filter_upwards [hd.2 φ] with ω hω
    simp only [hC', D, hω, add_zero]
  refine ⟨hC', hh.coordinateModification (fun φ hφ => (hh.measurable_pairing φ hφ).add (hd.1 φ))
    (fun φ _ => he φ), he, ?_⟩
  filter_upwards [hlinear, hnull 0] with ω hl hn
  have hne : a (2 * t ω) ≠ a (t ω) := by
    intro h
    have hhzero : t ω = 0 := by
      have hhcoef := ha h
      linarith
    exact hn hhzero
  change hC ω (a (2 * t ω)) + D ω (a (2 * t ω)) ≠
    2 * (hC ω (a (t ω)) + D ω (a (t ω)))
  simp only [D, hne, ↓reduceIte, add_zero]
  linarith

#print axioms IsWholePlaneGFF.exists_diagonal_modification
#print axioms IsWholePlaneGFF.coordinateModification
#print axioms diagonalSpike_sections
end HarmonicBalls

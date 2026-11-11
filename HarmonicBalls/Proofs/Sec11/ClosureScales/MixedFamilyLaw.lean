import HarmonicBalls.Proofs.Sec11.ClosureScales.UniversalCircleLaw

/-!
# The joint law of pairings and circle averages is universal

The joint
law `(h^ℂ, c)_* P` of the raw field and the coded circle averages is compared with the canonical joint law by testing on
cylinders involving finitely many test-function pairings and finitely many circle evaluations. The paper states that the
finite-dimensional laws agree "by the defining Gaussian covariance and centering". This file proves that statement for
two whole-plane GFFs in arbitrary universes: the joint law of a finite family of pairings `hC ω φ_i` and circle averages
`hcirc ω p_j` (with positive radii) does not depend on the model. It is the cylinder-level input of the joint-law
argument; no identity between the raw field and the coded circle averages is used.
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory

universe u₁ u₂

/-- **Universal finite-dimensional joint law.** For two whole-plane GFFs `(P, hC, hcirc)` and `(P', hC', hcirc')`, and a
finite family of test functions `φ i` and of points `p j` with positive radii, the joint law of the pairings
`hC ω (φ i)` and of the circle averages `hcirc ω (p j).1 (p j).2` agrees (as a family indexed by `ι ⊕ κ`). -/
theorem IsWholePlaneGFF.identDistrib_mixed_family
    {ι κ : Type} [Fintype ι] [Fintype κ]
    {Ω : Type u₁} {Ω' : Type u₂} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {hC' : Ω' → (ℂ → ℝ) → ℝ} {hcirc' : Ω' → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (h' : IsWholePlaneGFF P' hC' hcirc')
    (φ : ι → ℂ → ℝ) (hφ : ∀ i, IsTestFunction Set.univ (φ i))
    (p : κ → ℝ × ℂ) (hp : ∀ j, 0 < (p j).1) :
    IdentDistrib
      (fun ω (s : ι ⊕ κ) => Sum.elim (fun i => hC ω (φ i)) (fun j => hcirc ω (p j).1 (p j).2) s)
      (fun ω (s : ι ⊕ κ) => Sum.elim (fun i => hC' ω (φ i)) (fun j => hcirc' ω (p j).1 (p j).2) s) P P' := by
  let v : ι ⊕ κ → GFFObservable.Admissible := fun s =>
    Sum.elim (fun i => ⟨GFFObservable.pairing (φ i), hφ i⟩)
      (fun j => ⟨GFFObservable.circle (p j).1 (p j).2, hp j⟩) s
  have hid := IsWholePlaneGFF.identDistrib_finite_observables h h' v
  have key : ∀ (H : Ω → (ℂ → ℝ) → ℝ) (G : Ω → ℝ → ℂ → ℝ) (ω : Ω) (s : ι ⊕ κ),
      (v s).1.eval (H ω) (G ω) = Sum.elim (fun i => H ω (φ i)) (fun j => G ω (p j).1 (p j).2) s := by
    intro H G ω s
    cases s <;> rfl
  have key' : ∀ (H : Ω' → (ℂ → ℝ) → ℝ) (G : Ω' → ℝ → ℂ → ℝ) (ω : Ω') (s : ι ⊕ κ),
      (v s).1.eval (H ω) (G ω) = Sum.elim (fun i => H ω (φ i)) (fun j => G ω (p j).1 (p j).2) s := by
    intro H G ω s
    cases s <;> rfl
  have e1 : (fun ω (s : ι ⊕ κ) => Sum.elim (fun i => hC ω (φ i)) (fun j => hcirc ω (p j).1 (p j).2) s) =
      fun ω (s : ι ⊕ κ) => (v s).1.eval (hC ω) (hcirc ω) := by
    funext ω s
    exact (key hC hcirc ω s).symm
  have e2 : (fun ω (s : ι ⊕ κ) => Sum.elim (fun i => hC' ω (φ i)) (fun j => hcirc' ω (p j).1 (p j).2) s) =
      fun ω (s : ι ⊕ κ) => (v s).1.eval (hC' ω) (hcirc' ω) := by
    funext ω s
    exact (key' hC' hcirc' ω s).symm
  rw [e1, e2]
  exact hid

end HarmonicBalls

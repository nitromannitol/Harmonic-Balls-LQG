import HarmonicBalls.Proofs.Sec6.AnnulusCoverScaling
import HarmonicBalls.Proofs.Sec6.HarnackIteration

/-! # Connected finite covers of annuli

The intersection graph of the finite middle-annulus disc cover is connected.
-/

namespace HarmonicBalls.Section6

open Set Metric

/-- The finite disc cover of a middle annulus has a connected intersection graph. -/
theorem exists_connected_middle_annulus_cover {s₁ s₂ s₃ s₄ : ℝ}
    (h1 : 0 < s₁) (h12 : s₁ < s₂) (h23 : s₂ < s₃) (h34 : s₃ < s₄) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ T : Set ℂ, T.Finite ∧ T ⊆ annulus 0 s₂ s₃ ∧
      annulus 0 s₂ s₃ ⊆ ⋃ x ∈ T, ball x δ ∧
      (∀ x ∈ T, closedBall x (2 * δ) ⊆ annulus 0 s₁ s₄) ∧
      (∀ x ∈ T, ∀ y ∈ T, Relation.ReflTransGen
        (fun x y : ℂ => (ball x δ ∩ ball y δ).Nonempty ∧ x ∈ T ∧ y ∈ T) x y) := by
  obtain ⟨δ, hδ, T, hTfin, hTsub, hcover, hdisc⟩ :=
    exists_finite_middle_annulus_cover h12 h34
  have hs2 : 0 < s₂ := lt_trans h1 h12
  let w : ℂ := (((s₂ + s₃) / 2 : ℝ) : ℂ)
  have hw : w ∈ annulus 0 s₂ s₃ := by
    change dist w 0 < s₃ ∧ ¬ dist w 0 ≤ s₂
    have hwpos : 0 < (s₂ + s₃) / 2 := by linarith
    simp only [w, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hwpos]
    constructor <;> linarith
  let F : T → Set ℂ := fun x => ball x.1 δ
  let A : Set ℂ := annulus 0 s₂ s₃
  have hF : A ⊆ ⋃ x : T, F x := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hcover hx)
    exact mem_iUnion.mpr ⟨⟨y, hy⟩, hxy⟩
  have heq : (⋃ x : T, F x) = ⋃ x : T, (A ∪ F x) := by
    ext x
    simp only [mem_iUnion, mem_union]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨y, Or.inr hy⟩
    · rintro ⟨y, hy | hy⟩
      · exact mem_iUnion.mp (hF hy)
      · exact ⟨y, hy⟩
  have hconnected : IsPreconnected (⋃ x : T, F x) := by
    rw [heq]
    apply isPreconnected_iUnion
    · refine ⟨w, mem_iInter.mpr ?_⟩
      intro x
      exact Or.inl hw
    · intro x
      apply (isPreconnected_annulus 0 hs2.le s₃).union'
        ⟨x.1, hTsub x.2, mem_ball_self hδ⟩
      exact isPreconnected_ball
  refine ⟨δ, hδ, T, hTfin, hTsub, hcover, hdisc, ?_⟩
  intro x hx y hy
  have hg := hconnected.transGen_of_iUnion (fun _ => isOpen_ball)
    (⟨x, hx⟩ : T) (⟨y, hy⟩ : T)
    ⟨x, mem_ball_self hδ⟩ ⟨y, mem_ball_self hδ⟩
  have hg' : Relation.TransGen
      (fun x y : ℂ => (ball x δ ∩ ball y δ).Nonempty ∧ x ∈ T ∧ y ∈ T) x y := by
    exact Relation.TransGen.lift (fun a : T => a.1)
      (fun a b hab => ⟨hab, a.2, b.2⟩) _ _ hg
  exact hg'.to_reflTransGen

end HarmonicBalls.Section6

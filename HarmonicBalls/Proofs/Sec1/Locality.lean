import HarmonicBalls.Steps.Sec1.Locality

/-! # Reduction of Proposition 1.3 to cluster locality and Section 5 -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter

universe u

/-- Restricting the domain of the field can only decrease its σ-algebra. -/
theorem fieldSigmaAlgebra_mono {Ω : Type u} (α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
    {V U : Set ℂ} (hVU : V ⊆ U) : fieldSigmaAlgebra α₀ hC V ≤ fieldSigmaAlgebra α₀ hC U := by
  unfold fieldSigmaAlgebra
  refine iSup_le fun φ => iSup_le fun hφ => ?_
  exact le_iSup_of_le φ (le_iSup_of_le ⟨hφ.1, hφ.2.1, hφ.2.2.trans hVU⟩ le_rfl)

/-- At time zero, the containment event is deterministic. -/
theorem harmonicBallLocalSet_zero {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (x : ℂ) (U : Set ℂ) :
    ∃ E : Set Ω, MeasurableSet[fieldSigmaAlgebra α₀ hC U] E ∧
      {_ω : Ω | (if (0 : ℝ) = 0 then {x} else (∅ : Set ℂ)) ⊆ U} =ᵐ[P] E := by
  by_cases hx : x ∈ U
  · refine ⟨univ, @MeasurableSet.univ Ω (fieldSigmaAlgebra α₀ hC U), ?_⟩
    filter_upwards with ω
    simp [hx]
  · refine ⟨∅, @MeasurableSet.empty Ω (fieldSigmaAlgebra α₀ hC U), ?_⟩
    filter_upwards with ω
    simp [hx]

/-- For a bounded domain, strong compatibility identifies the two containment
events. If the centre is outside the domain the first event is null. -/
theorem harmonicBallLocalSet_bounded_of_steps
    (h58 : ClusterStrongCompatibilityStmt.{u}) (h55 : ExistenceHarmonicBallsStmt.{u})
    (h56 : UniquenessHarmonicBallsStmt.{u}) (hlocal : ClusterContainmentLocalityStep.{u})
    (γ α₀ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hmeasure : LQGMeasureLocality P γ α₀ hC hcirc)
    (x : ℂ) (Λ : Ω → ℝ → Set ℂ) (hΛ : ∀ᵐ ω ∂P, IsHarmonicBallFamily (μ ω) (Λ ω) x)
    (t : ℝ) (ht : 0 < t) (U : Set ℂ) (hU : IsOpen U) (hUb : Bornology.IsBounded U) :
    ∃ E : Set Ω, MeasurableSet[fieldSigmaAlgebra α₀ hC U] E ∧
      {ω | closure (Λ ω t) ⊆ U} =ᵐ[P] E := by
  classical
  by_cases hx : x ∈ U
  · let Λhat : Ω → ℂ → ℝ → Set ℂ := fun ω z =>
      if h : ∃ A, IsRegularizedClusterFamily (μ ω) A z then Classical.choose h else fun _ => ∅
    have hhat : ∀ᵐ ω ∂P, ∀ z, IsRegularizedClusterFamily (μ ω) (Λhat ω z) z := by
      filter_upwards [h55 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hω
      intro z
      dsimp only [Λhat]
      simpa only [dite_eq_left (hω z)] using Classical.choose_spec (hω z)
    obtain ⟨E, hE, heq⟩ := hlocal γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ hmeasure U hU hUb x hx t ht
    refine ⟨E, hE, ?_⟩
    filter_upwards [hΛ, h56 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ Λhat hhat,
      h58 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ Λhat hhat U hU hUb, heq] with ω hA hunique hcompat hEω
    have hsame : Λ ω t = Λhat ω x t := hunique x (Λ ω) hA ht
    apply propext
    rw [hsame]
    have hc := hcompat t ht x hx
    have hEω : closure (clusterOn (μ ω) U x t) ⊆ U ↔ ω ∈ E := propext_iff.mp hEω
    constructor
    · intro h
      exact hEω.mp ((hc (Or.inl h)) ▸ h)
    · intro h
      have h' := hEω.mpr h
      exact (hc (Or.inr h')) ▸ h'
  · refine ⟨∅, @MeasurableSet.empty Ω (fieldSigmaAlgebra α₀ hC U), ?_⟩
    filter_upwards [hΛ] with ω hω
    apply propext
    simp only [mem_empty_iff_false, iff_false]
    intro h
    exact hx (h (subset_closure (hω.2.mem t ht)))

/-- Proposition 1.3 from Sections 5 and the remaining local measurability
bridge. Exhaustion uses the boundedness of each harmonic ball. -/
theorem harmonicBallLocalSet_of_steps
    (h58 : ClusterStrongCompatibilityStmt.{u}) (h55 : ExistenceHarmonicBallsStmt.{u})
    (h56 : UniquenessHarmonicBallsStmt.{u}) (hlocal : ClusterContainmentLocalityStep.{u})
    (hmeasure : ∀ (γ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureLocality P γ α₀ hC hcirc) : HarmonicBallLocalSetStmt.{u} := by
  classical
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ x Λ hΛ t ht U hU
  by_cases ht0 : t = 0
  · subst t
    simpa using harmonicBallLocalSet_zero P α₀ hC x U
  · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
    let V : ℕ → Set ℂ := fun n => U ∩ ball 0 ((n : ℝ) + 1)
    have hVopen : ∀ n, IsOpen (V n) := fun _ => hU.inter isOpen_ball
    have hVbounded : ∀ n, Bornology.IsBounded (V n) := fun _ => isBounded_ball.subset inter_subset_right
    have hVsub : ∀ n, V n ⊆ U := fun _ => inter_subset_left
    have hex : ∀ n, ∃ E : Set Ω, MeasurableSet[fieldSigmaAlgebra α₀ hC (V n)] E ∧
        {ω | closure (Λ ω t) ⊆ V n} =ᵐ[P] E := fun n =>
      harmonicBallLocalSet_bounded_of_steps h58 h55 h56 hlocal γ α₀ hγ hγ2 hα Ω P hC hcirc μ
        hGFF hμ (hmeasure γ α₀ Ω P hC hcirc) x Λ hΛ t htpos (V n) (hVopen n) (hVbounded n)
    choose E hE hEq using hex
    refine ⟨⋃ n, E n, ?_, ?_⟩
    · exact MeasurableSet.iUnion (fun n => fieldSigmaAlgebra_mono α₀ hC (hVsub n) _ (hE n))
    · filter_upwards [hΛ, ae_all_iff.mpr hEq] with ω hω heq
      apply propext
      simp only [ite_eq_right ht0, mem_iUnion]
      constructor
      · intro hsub
        obtain ⟨R, hR⟩ := (hω.2.isBounded t htpos).closure.subset_ball (0 : ℂ)
        obtain ⟨n, hn⟩ := exists_nat_gt R
        have hRn : R ≤ (n : ℝ) + 1 := by linarith
        have hbounded : closure (Λ ω t) ⊆ V n :=
          subset_inter hsub (hR.trans (ball_subset_ball hRn))
        exact ⟨n, (propext_iff.mp (heq n)).mp hbounded⟩
      · rintro ⟨n, hn⟩
        exact ((propext_iff.mp (heq n)).mpr hn).trans (hVsub n)

#print axioms harmonicBallLocalSet_of_steps

end HarmonicBalls

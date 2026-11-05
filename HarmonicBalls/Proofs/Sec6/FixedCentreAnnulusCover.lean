import HarmonicBalls.Proofs.Sec6.PhaseApproximationTransfer

/-! # Covering nearby-centre counts by fixed annuli

This geometric reduction does not provide separation from a singularity or
stability of good annuli under centre displacement. The probability estimate
uses Leonardo Bonanno's proof in `LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set
open scoped ENNReal

/-- Every compact set is covered by finitely many annuli of a prescribed
positive radius. -/
theorem exists_finite_annulus_cover (K : Set ℂ) (hK : IsCompact K)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ T : Finset ℂ, K ⊆ ⋃ x ∈ T, annulus x (ρ / 2) ρ := by
  have hopen (x : ℂ) : IsOpen (annulus x (ρ / 2) ρ) :=
    isOpen_ball.sdiff isClosed_closedBall
  have hcover : K ⊆ ⋃ x : ℂ, annulus x (ρ / 2) ρ := by
    intro z hz
    apply mem_iUnion.mpr
    refine ⟨z + ((3 * ρ / 4 : ℝ) : ℂ), ?_⟩
    have hd : dist z (z + ((3 * ρ / 4 : ℝ) : ℂ)) = 3 * ρ / 4 := by
      simp [dist_eq_norm, hρ.le]
    simp only [annulus, mem_sdiff, mem_ball, mem_closedBall, not_le, hd]
    constructor <;> linarith
  exact hK.elim_finite_subcover (fun x : ℂ => annulus x (ρ / 2) ρ) hopen hcover


/-- One finite family of fixed-centre annuli covers all annuli whose centres
lie in the indicated neighbourhood. -/
theorem exists_finite_cover_nearby_annuli (x : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ T : Finset ℂ, ∀ y ∈ ball x (ρ / 2),
      annulus y (ρ / 2) ρ ⊆ ⋃ z ∈ T, annulus z (ρ / 2) ρ := by
  obtain ⟨T, hT⟩ := exists_finite_annulus_cover (closedBall x (2 * ρ))
    (isCompact_closedBall x (2 * ρ)) hρ
  refine ⟨T, ?_⟩
  intro y hy z hz
  apply hT
  have hzy : dist z y < ρ := hz.1
  have hyx : dist y x < ρ / 2 := hy
  have htriangle := dist_triangle z y x
  change dist z x ≤ 2 * ρ
  linarith

/-- The scaled lattice is closed under addition. -/
theorem scaledLattice_add_mem {δ : ℝ} {z w : ℂ}
    (hz : z ∈ scaledLattice δ) (hw : w ∈ scaledLattice δ) :
    z + w ∈ scaledLattice δ := by
  rcases hz with ⟨j, k, rfl⟩
  rcases hw with ⟨l, m, rfl⟩
  refine ⟨j + l, k + m, ?_⟩
  push_cast
  ring

/-- Source counts on a covering family of fixed-centre annuli give source
counts on every annulus contained in their union, including lattice translates
of the finitely many phase representatives. -/
theorem nearby_centre_counts_of_annulus_cover
    (μ : Measure ℂ) (ρ : ℝ) (N : ℕ) (a b c : ℝ)
    (F : ℕ → Finset ℂ) (T : Finset ℂ)
    (hsource : ∀ y ∈ T, ∀ n, N ≤ n → ∀ q ∈ F n,
      ∀ z ∈ annulus y (ρ / 2) ρ,
      z - q ∈ scaledLattice (dyadicScale n * ρ / 100) →
      c * Real.logb 7 (dyadicScale n ^ (-(1 / 2 : ℝ))) ≤
        ({r : ℝ | r ∈ Icc (dyadicScale n * ρ) (Real.sqrt (dyadicScale n) * ρ) ∧
          (∃ k : ℕ, 1 ≤ k ∧ r = ρ * (7 : ℝ)⁻¹ ^ k) ∧
          IsGoodAnnulus μ r z a b}.ncard : ℝ))
    (y : ℂ) (hcover : annulus y (ρ / 2) ρ ⊆ ⋃ x ∈ T, annulus x (ρ / 2) ρ)
    (n : ℕ) (hn : N ≤ n) (q : ℂ) (hq : q ∈ F n)
    (t : ℂ) (ht : t ∈ scaledLattice (dyadicScale n * ρ / 100))
    (z : ℂ) (hz : z ∈ annulus y (ρ / 2) ρ)
    (hlat : z - (q + t) ∈ scaledLattice (dyadicScale n * ρ / 100)) :
    c * Real.logb 7 (dyadicScale n ^ (-(1 / 2 : ℝ))) ≤
      ({r : ℝ | r ∈ Icc (dyadicScale n * ρ) (Real.sqrt (dyadicScale n) * ρ) ∧
        (∃ k : ℕ, 1 ≤ k ∧ r = ρ * (7 : ℝ)⁻¹ ^ k) ∧
        IsGoodAnnulus μ r z a b}.ncard : ℝ) := by
  obtain ⟨x, hx, hzx⟩ := mem_iUnion₂.mp (hcover hz)
  apply hsource x hx n hn q hq z hzx
  have h := scaledLattice_add_mem hlat ht
  convert h using 1
  abel


/-- A bound uniform over all sample-dependent choices also bounds the event
that some index fails. Neither the index set nor the choice needs to be
measurable. -/
theorem measure_exists_event_le_of_selected {Ω ι : Type*}
    [MeasurableSpace Ω] [Nonempty ι] (P : Measure Ω) (E : ι → Set Ω)
    {δ : ℝ≥0∞} (hbound : ∀ choice : Ω → ι, P {ω | ω ∈ E (choice ω)} ≤ δ) :
    P {ω | ∃ i, ω ∈ E i} ≤ δ := by
  classical
  let choice : Ω → ι := fun ω =>
    if h : ∃ i, ω ∈ E i then Classical.choose h else Classical.choice inferInstance
  apply (measure_mono ?_).trans (hbound choice)
  intro ω hω
  change ∃ i, ω ∈ E i at hω
  change ω ∈ E (choice ω)
  simpa only [choice, dite_eq_left hω] using Classical.choose_spec hω


/-- Uniform bounds for sample-dependent representative sequences control the
simultaneous event over all representative sequences. -/
theorem measure_exists_bad_representative_phase_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (μ : Ω → Measure ℂ)
    (ρ : ℝ) (x : ℂ) (N : ℕ) (a b c : ℝ) (F : ℕ → Finset ℂ)
    (hF : ∀ n, (F n).Nonempty) {δ : ℝ≥0∞}
    (hbound : ∀ phase : Ω → ℕ → ℂ, (∀ ω n, phase ω n ∈ F n) →
      P {ω | ¬ PhaseVeryGoodCriterionThree (μ ω) ρ x N a b c (phase ω)} ≤ δ) :
    P {ω | ∃ phase : ℕ → ℂ, (∀ n, phase n ∈ F n) ∧
      ¬ PhaseVeryGoodCriterionThree (μ ω) ρ x N a b c phase} ≤ δ := by
  classical
  let ι := {phase : ℕ → ℂ // ∀ n, phase n ∈ F n}
  have : Nonempty ι := ⟨⟨fun n => (hF n).choose, fun n => (hF n).choose_spec⟩⟩
  let E : ι → Set Ω := fun phase =>
    {ω | ¬ PhaseVeryGoodCriterionThree (μ ω) ρ x N a b c phase.1}
  have h := measure_exists_event_le_of_selected P E (δ := δ) (by
    intro choice
    exact hbound (fun ω => (choice ω).1) (fun ω => (choice ω).2))
  apply (measure_mono ?_).trans h
  rintro ω ⟨phase, hphase, hbad⟩
  exact ⟨⟨phase, hphase⟩, hbad⟩




/-- Simultaneous criterion three for representative sequences gives the
one-scale count for every representative at every scale. -/
theorem representative_counts_of_all_phases
    (μ : Measure ℂ) (ρ : ℝ) (x : ℂ) (N : ℕ) (a b c : ℝ)
    (F : ℕ → Finset ℂ) (hF : ∀ n, (F n).Nonempty)
    (hgood : ∀ phase : ℕ → ℂ, (∀ n, phase n ∈ F n) →
      PhaseVeryGoodCriterionThree μ ρ x N a b c phase) :
    ∀ n, N ≤ n → ∀ q ∈ F n, ∀ z ∈ annulus x (ρ / 2) ρ,
      z - q ∈ scaledLattice (dyadicScale n * ρ / 100) →
      c * Real.logb 7 (dyadicScale n ^ (-(1 / 2 : ℝ))) ≤
        ({r : ℝ | r ∈ Icc (dyadicScale n * ρ) (Real.sqrt (dyadicScale n) * ρ) ∧
          (∃ k : ℕ, 1 ≤ k ∧ r = ρ * (7 : ℝ)⁻¹ ^ k) ∧
          IsGoodAnnulus μ r z a b}.ncard : ℝ) := by
  classical
  choose q₀ hq₀ using hF
  intro n hn q hq z hz hlat
  let phase : ℕ → ℂ := fun k => if k = n then q else q₀ k
  have hphase : ∀ k, phase k ∈ F k := by
    intro k
    by_cases hk : k = n
    · subst k
      simpa [phase] using hq
    · simpa [phase, hk] using hq₀ k
  have h := hgood phase hphase n hn z hz
  apply h
  simpa [phase] using hlat

/-- Simultaneous representative-sequence estimates at a finite set of fixed
centres obey the finite union bound. -/
theorem measure_exists_bad_fixedCentre_phase_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (μ : Ω → Measure ℂ)
    (ρ : ℝ) (N : ℕ) (a b c : ℝ) (F : ℕ → Finset ℂ) (T : Finset ℂ)
    (hF : ∀ n, (F n).Nonempty) {δ : ℝ≥0∞}
    (hbound : ∀ x ∈ T, ∀ phase : Ω → ℕ → ℂ, (∀ ω n, phase ω n ∈ F n) →
      P {ω | ¬ PhaseVeryGoodCriterionThree (μ ω) ρ x N a b c (phase ω)} ≤ δ) :
    P {ω | ∃ x ∈ T, ∃ phase : ℕ → ℂ, (∀ n, phase n ∈ F n) ∧
      ¬ PhaseVeryGoodCriterionThree (μ ω) ρ x N a b c phase} ≤ (T.card : ℝ≥0∞) * δ := by
  let E : ℂ → Set Ω := fun x => {ω | ∃ phase : ℕ → ℂ, (∀ n, phase n ∈ F n) ∧
    ¬ PhaseVeryGoodCriterionThree (μ ω) ρ x N a b c phase}
  calc
    _ = P (⋃ x ∈ T, E x) := by
      congr 1
      ext ω
      simp only [mem_ofPred_eq, mem_iUnion, E, exists_prop]
    _ ≤ ∑ x ∈ T, P (E x) := measure_biUnion_finset_le T E
    _ ≤ ∑ _x ∈ T, δ := by
      apply Finset.sum_le_sum
      intro x hx
      exact measure_exists_bad_representative_phase_le P μ ρ x N a b c F hF (hbound x hx)
    _ = _ := by simp

universe u

/-- The whole-plane criterion-three estimate holds simultaneously over all
sequences of representatives from the given growing finite phase sets. -/
theorem exists_universal_simultaneous_representative_probability
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {γ : ℝ} (hγ : 0 < γ) (hγ₂ : γ < 2)
    {Ω₀ : Type u} [MeasurableSpace Ω₀] {P₀ : Measure Ω₀}
    {hC₀ : Ω₀ → (ℂ → ℝ) → ℝ} {hcirc₀ : Ω₀ → ℝ → ℂ → ℝ} {μ₀ : Ω₀ → Measure ℂ}
    (h₀ : IsWholePlaneGFF P₀ hC₀ hcirc₀) (hμ₀ : IsLQGMeasureOfField P₀ γ 0 hcirc₀ μ₀)
    {b : ℝ} (hb : 0 < b) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∃ N₀ : ℕ, 9 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ 0 hcirc μ →
    ∀ (s : ℝ), 0 < s → ∀ (x : ℂ) (F : ℕ → Finset ℂ),
      (∀ n, (F n).card ≤ 2 ^ (3 * n)) → (∀ n, (F n).Nonempty) →
      P {ω | ∃ phase : ℕ → ℂ, (∀ n, phase n ∈ F n) ∧
        ¬ PhaseVeryGoodCriterionThree (μ ω) s x N a b (1 / 32) phase} ≤ δ := by
  obtain ⟨a, ha, N₀, hN₀, hbound⟩ :=
    exists_universal_growing_phaseCriterion_probability hgrowth hγ hγ₂ h₀ hμ₀ hb hδ
  refine ⟨a, ha, N₀, hN₀, ?_⟩
  intro N hN Ω _ P hC hcirc μ hgff hμ s hs x F hcard hF
  apply measure_exists_bad_representative_phase_le P μ s x N a b (1 / 32) F hF
  exact hbound N hN Ω P hC hcirc μ hgff hμ s hs x F hcard

end HarmonicBalls.Section6

import HarmonicBalls.Proofs.Sec6.PhaseCriterionThreeProbability
import HarmonicBalls.Proofs.Sec6.SizeRatioTranslationLaw
import HarmonicBalls.Proofs.Sec6.CriterionThreeOffCenterScaling

/-! # Translation of the very-good lattice criterion

Translation moves the absolute lattice as well as the centre. -/

namespace HarmonicBalls

open MeasureTheory Metric Set
open scoped ENNReal

/-- Criterion three with a prescribed phase for each lattice scale. -/
def PhaseVeryGoodCriterionThree (μ : Measure ℂ) (ρ : ℝ) (x : ℂ) (N : ℕ)
    (a b c : ℝ) (phase : ℕ → ℂ) : Prop :=
  ∀ n : ℕ, N ≤ n → ∀ z ∈ annulus x (ρ / 2) ρ,
    z - phase n ∈ Section6.scaledLattice (dyadicScale n * ρ / 100) →
    c * Real.logb 7 (dyadicScale n ^ (-(1 / 2 : ℝ))) ≤
      ({r : ℝ | r ∈ Icc (dyadicScale n * ρ) (Real.sqrt (dyadicScale n) * ρ) ∧
        (∃ k : ℕ, 1 ≤ k ∧ r = ρ * (7 : ℝ)⁻¹ ^ k) ∧
        IsGoodAnnulus μ r z a b}.ncard : ℝ)

/-- Zero phase recovers the criterion on the absolute lattice. -/
theorem phaseVeryGoodCriterionThree_zero (μ : Measure ℂ) (ρ : ℝ) (x : ℂ)
    (N : ℕ) (a b c : ℝ) :
    PhaseVeryGoodCriterionThree μ ρ x N a b c (fun _ => 0) ↔
      Section6.VeryGoodCriterionThree μ ρ x N a b c := by
  simp only [PhaseVeryGoodCriterionThree, Section6.VeryGoodCriterionThree,
    sub_zero, mem_inter_iff]
  tauto

/-- Translating the measure, centre, and every lattice phase by the same
vector preserves criterion three. -/
theorem phaseVeryGoodCriterionThree_map_add (μ : Measure ℂ) (ρ : ℝ) (x t : ℂ)
    (N : ℕ) (a b c : ℝ) (phase : ℕ → ℂ) :
    PhaseVeryGoodCriterionThree (μ.map (fun w : ℂ => w + t)) ρ (x + t)
        N a b c (fun n => phase n + t) ↔
      PhaseVeryGoodCriterionThree μ ρ x N a b c phase := by
  have hann (z : ℂ) : z + t ∈ annulus (x + t) (ρ / 2) ρ ↔
      z ∈ annulus x (ρ / 2) ρ := by
    simp only [annulus, mem_sdiff, mem_ball, mem_closedBall, dist_eq_norm,
      add_sub_add_right_eq_sub]
  have hcount (n : ℕ) (z : ℂ) :
      {r : ℝ | r ∈ Icc (dyadicScale n * ρ) (Real.sqrt (dyadicScale n) * ρ) ∧
        (∃ k : ℕ, 1 ≤ k ∧ r = ρ * (7 : ℝ)⁻¹ ^ k) ∧
        IsGoodAnnulus (μ.map (fun w : ℂ => w + t)) r (z + t) a b} =
      {r : ℝ | r ∈ Icc (dyadicScale n * ρ) (Real.sqrt (dyadicScale n) * ρ) ∧
        (∃ k : ℕ, 1 ≤ k ∧ r = ρ * (7 : ℝ)⁻¹ ^ k) ∧
        IsGoodAnnulus μ r z a b} := by
    ext r
    simp only [mem_ofPred_eq, Section6.isGoodAnnulus_map_add_iff]
  constructor
  · intro h n hn z hz hlat
    have hh := h n hn (z + t) ((hann z).mpr hz) (by
      simpa only [add_sub_add_right_eq_sub] using hlat)
    rwa [hcount] at hh
  · intro h n hn z hz hlat
    have hz' : z - t ∈ annulus x (ρ / 2) ρ := by
      apply (hann (z - t)).mp
      simpa only [sub_add_cancel] using hz
    have hlat' : (z - t) - phase n ∈ Section6.scaledLattice (dyadicScale n * ρ / 100) := by
      have heq : (z - t) - phase n = z - (phase n + t) := by abel
      rw [heq]
      exact hlat
    have hh := h n hn (z - t) hz' hlat'
    rw [← hcount n (z - t)] at hh
    simpa only [sub_add_cancel] using hh

/-- At a translated centre, the printed absolute lattice becomes a shifted
lattice in the original coordinates. -/
theorem veryGoodCriterionThree_map_add_iff_phase (μ : Measure ℂ) (ρ : ℝ) (x t : ℂ)
    (N : ℕ) (a b c : ℝ) :
    Section6.VeryGoodCriterionThree (μ.map (fun w : ℂ => w + t)) ρ (x + t) N a b c ↔
      PhaseVeryGoodCriterionThree μ ρ x N a b c (fun _ => -t) := by
  rw [← phaseVeryGoodCriterionThree_zero]
  simpa only [neg_add_cancel] using
    phaseVeryGoodCriterionThree_map_add μ ρ x t N a b c (fun _ => -t)

/-- Dilation transports the centre and every lattice phase by the same
factor. No equality between differently phased lattices is asserted. -/
theorem phaseVeryGoodCriterionThree_map_inv_smul (μ : Measure ℂ) {k : ℝ} (hk : 0 < k)
    (ρ : ℝ) (x : ℂ) (N : ℕ) (a b c : ℝ) (phase : ℕ → ℂ) :
    PhaseVeryGoodCriterionThree (μ.map (fun z : ℂ => k⁻¹ • z)) ρ x N a b c phase ↔
      PhaseVeryGoodCriterionThree μ (k * ρ) (k • x) N a b c (fun n => k • phase n) := by
  have hmem (z : ℂ) : z ∈ annulus x (ρ / 2) ρ ↔
      k • z ∈ annulus (k • x) ((k * ρ) / 2) (k * ρ) := by
    simp only [annulus, Set.mem_sdiff, mem_ball, mem_closedBall, dist_smul₀,
      Real.norm_eq_abs, abs_of_pos hk]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> nlinarith
  have hinj : Function.Injective (fun z : ℂ => k • z) := by
    intro z w h
    have h' := congrArg (fun z : ℂ => k⁻¹ • z) h
    simpa only [smul_smul, inv_mul_cancel₀ hk.ne', one_smul] using h'
  have hscale (n : ℕ) (j l : ℤ) :
      k • (((dyadicScale n * ρ / 100 : ℝ) : ℂ) * ((j : ℂ) + (l : ℂ) * Complex.I)) =
        (((dyadicScale n * (k * ρ) / 100 : ℝ) : ℂ) * ((j : ℂ) + (l : ℂ) * Complex.I)) := by
    rw [Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul]
    congr 1
    congr 1
    ring
  have hlat (n : ℕ) (z : ℂ) :
      z ∈ Section6.scaledLattice (dyadicScale n * ρ / 100) ↔
      k • z ∈ Section6.scaledLattice (dyadicScale n * (k * ρ) / 100) := by
    change (∃ j l : ℤ, z = ((dyadicScale n * ρ / 100 : ℝ) : ℂ) *
        ((j : ℂ) + (l : ℂ) * Complex.I)) ↔
      (∃ j l : ℤ, k • z = ((dyadicScale n * (k * ρ) / 100 : ℝ) : ℂ) *
        ((j : ℂ) + (l : ℂ) * Complex.I))
    constructor
    · rintro ⟨j, l, rfl⟩
      exact ⟨j, l, hscale n j l⟩
    · rintro ⟨j, l, h⟩
      exact ⟨j, l, hinj (h.trans (hscale n j l).symm)⟩
  constructor
  · intro h n hn z hz hzl
    have hz' : k⁻¹ • z ∈ annulus x (ρ / 2) ρ := by
      apply (hmem (k⁻¹ • z)).mpr
      simpa only [smul_smul, mul_inv_cancel₀ hk.ne', one_smul] using hz
    have hl' : (k⁻¹ • z) - phase n ∈ Section6.scaledLattice (dyadicScale n * ρ / 100) := by
      apply (hlat n _).mpr
      simpa only [smul_sub, smul_smul, mul_inv_cancel₀ hk.ne', one_smul] using hzl
    have hh := h n hn (k⁻¹ • z) hz' hl'
    rw [goodAnnulus_radius_count_map_inv_smul μ hk ρ n (k⁻¹ • z) a b
      (fun r => Section6.isGoodAnnulus_map_inv_smul_iff hk μ r (k⁻¹ • z) a b)] at hh
    simpa only [smul_smul, mul_inv_cancel₀ hk.ne', one_smul] using hh
  · intro h n hn z hz hzl
    have hh := h n hn (k • z) ((hmem z).mp hz) (by
      simpa only [← smul_sub] using (hlat n (z - phase n)).mp hzl)
    rw [goodAnnulus_radius_count_map_inv_smul μ hk ρ n z a b
      (fun r => Section6.isGoodAnnulus_map_inv_smul_iff hk μ r z a b)]
    exact hh

/-- After translation to the origin and normalization by `ρ`, the phase
associated with an absolute lattice at `z` is `-ρ⁻¹ • z`. -/
theorem phaseVeryGoodCriterionThree_centered_normalization
    (μ : Measure ℂ) {ρ : ℝ} (hρ : 0 < ρ) (z : ℂ) (N : ℕ) (a b c : ℝ) :
    PhaseVeryGoodCriterionThree (μ.map (fun w : ℂ => w - z)) ρ 0 N a b c (fun _ => -z) ↔
      PhaseVeryGoodCriterionThree
        ((μ.map (fun w : ℂ => w - z)).map (fun w : ℂ => ρ⁻¹ • w))
        1 0 N a b c (fun _ => -(ρ⁻¹ • z)) := by
  have h := phaseVeryGoodCriterionThree_map_inv_smul (μ.map (fun w : ℂ => w - z)) hρ
    1 0 N a b c (fun _ => -(ρ⁻¹ • z))
  simpa only [mul_one, smul_zero, smul_neg, smul_smul, mul_inv_cancel₀ hρ.ne', one_smul] using h.symm

/-- The phase-uniform prevalence estimate controls the phase criterion for
any prescribed centre and phase sequence, with a common starting index. -/
theorem exists_phaseVeryGoodCriterionThree_probability
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {γ : ℝ}
    (hγ : 0 < γ) (hγ₂ : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    {a b c : ℝ} (hc : 0 < c)
    (hgff : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc)
    (hprev : PolyHighProb P fun ε => {ω | ∀ z ∈ Section6.prevalenceGrid ε,
      c * Real.logb 7 (ε ^ (-1 : ℝ)) ≤
        ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
          (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧ IsGoodAnnulus (μ ω) r z a b}.ncard : ℝ)})
    (hunit : MeasurableSet {ν : Measure ℂ | IsGoodAnnulus ν 1 0 a b})
    {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 9 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ (x : ℂ) (phase : ℕ → ℂ),
      P {ω | ¬ PhaseVeryGoodCriterionThree (μ ω) 1 x N a b c phase} ≤ δ := by
  obtain ⟨N₀, hN₀, hbound⟩ := Section6.exists_phase_uniform_unit_criterionThree_probability
    P hγ hγ₂ hc hgff hμ hAff hCC hprev hunit hδ
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN x phase
  simpa only [PhaseVeryGoodCriterionThree, mul_one] using hbound N hN x phase

/-- The entire very-good event at `z` is the centred event for the
translated measure with phase `-z` at every inner lattice scale. -/
theorem isVeryGoodAnnulus_iff_centered_shifted_phase (μ : Measure ℂ)
    (β ρ : ℝ) (z : ℂ) (N : ℕ) (a b C₁m C₁p C₂m C₂p C₃ : ℝ) :
    IsVeryGoodAnnulus μ β ρ z N a b C₁m C₁p C₂m C₂p C₃ ↔
      annulusBallMassSize (μ.map (fun w : ℂ => w - z)) β ρ 0 /
          (μ.map (fun w : ℂ => w - z)) (annulus 0 (ρ / 4) (2 * ρ)) ∈
        Icc (ENNReal.ofReal C₁m) (ENNReal.ofReal C₁p) ∧
      annulusGreenPotentialSup (μ.map (fun w : ℂ => w - z)) 0 (ρ / 4) (2 * ρ) /
          (μ.map (fun w : ℂ => w - z)) (annulus 0 (ρ / 4) (2 * ρ)) ∈
        Icc (ENNReal.ofReal C₂m) (ENNReal.ofReal C₂p) ∧
      PhaseVeryGoodCriterionThree (μ.map (fun w : ℂ => w - z)) ρ 0 N a b C₃
        (fun _ => -z) := by
  rw [Section6.isVeryGoodAnnulus_iff, Section6.annulusBallMassSize_map_sub,
    Section6.annulusGreenPotentialSup_map_sub, Section6.map_sub_annulus]
  have hphase := phaseVeryGoodCriterionThree_map_add μ ρ z (-z) N a b C₃ (fun _ => 0)
  simp only [add_neg_cancel, ← sub_eq_add_neg, zero_sub, phaseVeryGoodCriterionThree_zero] at hphase
  rw [hphase]

end HarmonicBalls

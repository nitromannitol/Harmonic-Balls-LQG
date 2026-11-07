import HarmonicBalls.Proofs.Sec11.MassDiameterTileUnionBound
import HarmonicBalls.Proofs.Sec11.ConditionalMassTileSelection

/-! # Tile failure bounds with a common random factor -/

namespace HarmonicBalls
open MeasureTheory Set Filter Topology
open scoped ENNReal BigOperators

/-- A common exceptional event is paid for once, while tile-specific
exceptional events are summed. No measurability of the events is needed. -/
theorem tendsto_all_tiles_failure_of_common_exception
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ι : ℕ → Type*) [∀ n, Fintype (ι n)]
    (E B : ∀ n, ι n → Set Ω) (F : ℕ → Set Ω)
    (hcontain : ∀ n i, (E n i)ᶜ ⊆ F n ∪ B n i)
    (hF : Tendsto (fun n => P (F n)) atTop (𝓝 0))
    (hB : Tendsto (fun n => ∑ i : ι n, P (B n i)) atTop (𝓝 0)) :
    Tendsto (fun n => P {ω | ∀ i : ι n, ω ∈ E n i}ᶜ) atTop (𝓝 0) := by
  classical
  have hzero : Tendsto (fun n => P (F n) + ∑ i : ι n, P (B n i)) atTop (𝓝 0) := by
    simpa using hF.add hB
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hzero
    (fun _ => zero_le) ?_
  intro n
  calc
    P {ω | ∀ i : ι n, ω ∈ E n i}ᶜ ≤ P (F n ∪ ⋃ i : ι n, B n i) := by
      apply measure_mono
      intro ω hω
      simp only [mem_compl_iff, mem_ofPred_eq, not_forall] at hω
      obtain ⟨i, hi⟩ := hω
      rcases hcontain n i hi with hF | hB
      · exact Or.inl hF
      · exact Or.inr (mem_iUnion.mpr ⟨i, hB⟩)
    _ ≤ P (F n) + P (⋃ i : ι n, B n i) := measure_union_le _ _
    _ ≤ P (F n) + ∑ i : ι n, P (B n i) := by
      gcongr
      exact measure_iUnion_fintype_le P _

/-- A common upper bound with a random factor produces the preceding
exception decomposition. `a n` is the deterministic size of a good tile;
`r n` is a truncation level for the common factor. -/
theorem tendsto_all_tiles_failure_of_common_factor
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ι : ℕ → Type*) [∀ n, Fintype (ι n)]
    (X : ∀ n, ι n → Ω → ℝ≥0∞) (R : Ω → ℝ≥0∞)
    (a r : ℕ → ℝ≥0∞) (d : ℝ≥0∞)
    (hmargin : ∀ n, a n * r n < d)
    (htail : Tendsto (fun n => P {ω | r n < R ω}) atTop (𝓝 0))
    (hsum : Tendsto (fun n => ∑ i : ι n,
      P {ω | a n * R ω < X n i ω}) atTop (𝓝 0)) :
    Tendsto (fun n => P {ω | ∀ i : ι n, X n i ω < d}ᶜ) atTop (𝓝 0) := by
  apply tendsto_all_tiles_failure_of_common_exception P ι
    (fun n i => {ω | X n i ω < d})
    (fun n i => {ω | a n * R ω < X n i ω})
    (fun n => {ω | r n < R ω}) ?_ htail hsum
  intro n i ω hω
  simp only [mem_compl_iff, mem_ofPred_eq, not_lt] at hω
  by_cases hR : r n < R ω
  · exact Or.inl hR
  · right
    have hle : a n * R ω ≤ a n * r n := by gcongr; exact le_of_not_gt hR
    exact (hle.trans_lt (hmargin n)).trans_le hω

#print axioms tendsto_all_tiles_failure_of_common_exception
#print axioms tendsto_all_tiles_failure_of_common_factor

/-- The common-factor estimate and conditional mass positivity select a
fixed scale and mass-carrying class with all tile diameters below `d`. -/
theorem exists_mass_tile_class_of_conditional_mass_and_common_factor
    {Ω Y : Type*} [m₀ : MeasurableSpace Ω] [MeasurableSpace Y]
    (P : Measure Ω) [IsProbabilityMeasure P] (m : MeasurableSpace Ω)
    (μ : Ω → Measure Y) (S : Set Y) (C : ℕ → Fin 4 → Set Y)
    (ι : ℕ → Type*) [∀ n, Fintype (ι n)]
    (X : ∀ n, ι n → Ω → ℝ≥0∞) (R : Ω → ℝ≥0∞)
    (a r : ℕ → ℝ≥0∞) (c d : ℝ≥0∞)
    (hcover : ∀ n, S ⊆ ⋃ j, C n j)
    (hcond : ∀ᵐ ω ∂P, 0 < (P[({ω | (8 : ℝ≥0∞) * c < μ ω S}).indicator
      (fun _ => (1 : ℝ)) | m]) ω)
    (hmargin : ∀ n, a n * r n < d)
    (htail : Tendsto (fun n => P {ω | r n < R ω}) atTop (𝓝 0))
    (hsum : Tendsto (fun n => ∑ i : ι n,
      P {ω | a n * R ω < X n i ω}) atTop (𝓝 0)) :
    ∃ n j, 0 < P {ω | (∀ i : ι n, X n i ω < d) ∧
      (2 : ℝ≥0∞) * c < μ ω (C n j)} := by
  let : MeasurableSpace Ω := m₀
  have hp := measure_pos_of_condExp_indicator_pos P m
    {ω | (8 : ℝ≥0∞) * c < μ ω S} hcond
  have hp' : 0 < P {ω | ω ∈ (univ : Set Ω) ∧ (8 : ℝ≥0∞) * c < μ ω S} := by
    simpa using hp
  have hf := tendsto_all_tiles_failure_of_common_factor P ι X R a r d hmargin htail hsum
  have hsmall : ∃ n, P {ω | ∀ i : ι n, X n i ω < d}ᶜ <
      P {ω | ω ∈ (univ : Set Ω) ∧ (8 : ℝ≥0∞) * c < μ ω S} :=
    ((tendsto_order.1 hf).2 _ hp').exists
  obtain ⟨n, j, hj⟩ := exists_positive_measure_scale_and_four_tile_class_of_failure_bound
    P μ univ S C (fun n => {ω | ∀ i : ι n, X n i ω < d}) c hcover hsmall
  exact ⟨n, j, by simpa using hj⟩

#print axioms exists_mass_tile_class_of_conditional_mass_and_common_factor

/-- For the unit-circle normalized whole-plane GFF, the common factor
`exp (ξ h₁(0))` equals one almost surely, so it has no exceptional tail. -/
theorem IsWholePlaneGFF.tendsto_all_tiles_failure_of_pinned_circle_factor
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (ξ : ℝ)
    (ι : ℕ → Type*) [∀ n, Fintype (ι n)]
    (X : ∀ n, ι n → Ω → ℝ≥0∞) (a : ℕ → ℝ≥0∞) (d : ℝ≥0∞)
    (hmargin : ∀ n, a n < d)
    (hsum : Tendsto (fun n => ∑ i : ι n, P {ω |
      a n * ENNReal.ofReal (Real.exp (ξ * hcirc ω 1 0)) < X n i ω}) atTop (𝓝 0)) :
    Tendsto (fun n => P {ω | ∀ i : ι n, X n i ω < d}ᶜ) atTop (𝓝 0) := by
  let R : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (Real.exp (ξ * hcirc ω 1 0))
  have hR : ∀ᵐ ω ∂P, R ω = 1 := by
    filter_upwards [h.ae_circleAverage_one_zero] with ω hω
    simp [R, hω]
  have hz : P {ω | (1 : ℝ≥0∞) < R ω} = 0 := by
    apply measure_mono_null (t := {ω | R ω ≠ 1})
    · intro ω hω
      exact ne_of_gt hω
    · exact ae_iff.mp hR
  have ht : Tendsto (fun _ : ℕ => P {ω | (1 : ℝ≥0∞) < R ω}) atTop (𝓝 0) := by
    simp [hz]
  apply tendsto_all_tiles_failure_of_common_factor P ι X R a (fun _ => 1) d ?_ ht hsum
  simpa using hmargin

#print axioms IsWholePlaneGFF.tendsto_all_tiles_failure_of_pinned_circle_factor

/-- A uniform geometric tile-failure bound beats a geometric bound on the
number of tiles when the product of their rates is less than one. -/
theorem tendsto_sum_tile_failures_of_geometric_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ι : ℕ → Type*) [∀ n, Fintype (ι n)] (B : ∀ n, ι n → Set Ω)
    (A C r q : ℝ≥0∞) (hA : A ≠ ∞) (hC : C ≠ ∞) (hrq : r * q < 1)
    (hcard : ∀ n, (Fintype.card (ι n) : ℝ≥0∞) ≤ A * r ^ n)
    (hbound : ∀ n i, P (B n i) ≤ C * q ^ n) :
    Tendsto (fun n => ∑ i : ι n, P (B n i)) atTop (𝓝 0) := by
  classical
  have hlim : Tendsto (fun n : ℕ => (r * q) ^ n * (A * C)) atTop (𝓝 0) := by
    have h := ENNReal.Tendsto.mul_const (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hrq)
      (Or.inr (ENNReal.mul_ne_top hA hC))
    simpa using h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => zero_le) ?_
  intro n
  calc
    (∑ i : ι n, P (B n i)) ≤ ∑ _i : ι n, C * q ^ n :=
      Finset.sum_le_sum fun i _ => hbound n i
    _ = (Fintype.card (ι n) : ℝ≥0∞) * (C * q ^ n) := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (A * r ^ n) * (C * q ^ n) := by gcongr; exact hcard n
    _ = (r * q) ^ n * (A * C) := by rw [mul_pow]; ac_rfl

#print axioms tendsto_sum_tile_failures_of_geometric_bound
end HarmonicBalls

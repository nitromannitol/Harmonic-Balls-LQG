import HarmonicBalls.Steps.Sec11.InternalMetricMeasurable

/-! # Boundary clearance for internal distances -/

namespace HarmonicBalls

open MeasureTheory Set
open scoped ENNReal

/-- The distance from a point to the complement of a fixed set is measurable
for a pointwise measurable family of continuous distance functions. -/
theorem measurable_iInf_ofReal_distance_to_complement
    {Ω : Type*} [MeasurableSpace Ω] {D : Ω → ℂ → ℂ → ℝ} (U : Set ℂ) (x : ℂ)
    (hD : ∀ y, Measurable fun ω => D ω x y)
    (hcont : ∀ ω, Continuous fun y => D ω x y) :
    Measurable fun ω => ⨅ y ∈ Uᶜ, ENNReal.ofReal (D ω x y) := by
  let f : (Uᶜ : Set ℂ) → Ω → ℝ≥0∞ := fun y ω => ENNReal.ofReal (D ω x y)
  have hm : Measurable (⨅ y : (Uᶜ : Set ℂ), f y) :=
    measurable_iInf_of_upperSemicontinuous (fun y => (hD y).ennreal_ofReal)
      (fun ω => (ENNReal.continuous_ofReal.comp
        ((hcont ω).comp continuous_subtype_val)).upperSemicontinuous)
  convert hm using 1
  ext ω
  simp only [iInf_apply, f, iInf_subtype]

/-- The event that a fixed edge is shorter than a prescribed positive
clearance from the complement is measurable. -/
theorem measurableSet_edge_with_boundary_clearance
    {Ω : Type*} [MeasurableSpace Ω] {D : Ω → ℂ → ℂ → ℝ} (U : Set ℂ) (x y : ℂ)
    {δ : ℝ} (hδ : 0 < δ)
    (hD : ∀ z, Measurable fun ω => D ω x z)
    (hcont : ∀ ω, Continuous fun z => D ω x z) :
    MeasurableSet {ω | D ω x y < δ ∧ ∀ z ∉ U, δ ≤ D ω x z} := by
  have hm := measurable_iInf_ofReal_distance_to_complement U x hD hcont
  have heq : {ω | ∀ z ∉ U, δ ≤ D ω x z} =
      {ω | ENNReal.ofReal δ ≤ ⨅ z ∈ Uᶜ, ENNReal.ofReal (D ω x z)} := by
    ext ω
    simp only [mem_ofPred_eq, le_iInf_iff, mem_compl_iff, ENNReal.ofReal_le_ofReal_iff',
      not_le_of_gt hδ, or_false]
  have hmeas : MeasurableSet {ω | ∀ z ∉ U, δ ≤ D ω x z} := by
    rw [heq]
    exact measurableSet_le measurable_const hm
  exact (measurableSet_lt (hD y) measurable_const).inter hmeas

/-- The event that a fixed edge has some rational boundary clearance is
measurable. -/
theorem measurableSet_edge_with_rational_boundary_clearance
    {Ω : Type*} [MeasurableSpace Ω] {D : Ω → ℂ → ℂ → ℝ} (U : Set ℂ) (x y : ℂ)
    (hD : ∀ z, Measurable fun ω => D ω x z)
    (hcont : ∀ ω, Continuous fun z => D ω x z) :
    MeasurableSet {ω | ∃ δ : ℚ, 0 < δ ∧ D ω x y < (δ : ℝ) ∧
      ∀ z ∉ U, (δ : ℝ) ≤ D ω x z} := by
  have heq : {ω | ∃ δ : ℚ, 0 < δ ∧ D ω x y < (δ : ℝ) ∧
      ∀ z ∉ U, (δ : ℝ) ≤ D ω x z} =
      ⋃ δ : ℚ, ⋃ (_ : 0 < δ), {ω | D ω x y < (δ : ℝ) ∧
        ∀ z ∉ U, (δ : ℝ) ≤ D ω x z} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, exists_prop]
  rw [heq]
  apply MeasurableSet.iUnion
  intro δ
  apply MeasurableSet.iUnion
  intro hδ
  exact measurableSet_edge_with_boundary_clearance U x y (by exact_mod_cast hδ) hD hcont

/-- A path shorter than a lower bound for the distance to the complement
stays inside the set. -/
theorem IsEuclideanLengthMetric.path_stays_inside_of_boundary_clearance
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) {U : Set ℂ} {x y : ℂ} {δ : ℝ}
    (hclear : ∀ z ∉ U, δ ≤ D x z) (p : Path x y)
    (hp : pathLength D p < ENNReal.ofReal δ) : ∀ t, p t ∈ U := by
  intro t
  by_contra ht
  have ht' : (t : ℝ) ∈ Icc (0 : ℝ) 1 := t.property
  have hseg := hD.ofReal_two_segment_le_pathLength hnonneg p ht'
  have hd : ENNReal.ofReal (D x (p.extend t)) ≤ pathLength D p := by
    apply (ENNReal.ofReal_le_ofReal (show D x (p.extend t) ≤
      D x (p.extend t) + D (p.extend t) y by linarith [hnonneg (p.extend t) y])).trans
    exact hseg
  have hbound : δ ≤ D x (p.extend t) := hclear _ (by simpa only [Path.extend_apply _ ht'] using ht)
  exact (not_le_of_gt hp) ((ENNReal.ofReal_le_ofReal hbound).trans hd)

/-- If the endpoints are closer than a lower bound for distance to the
complement, their internal distance equals their ambient distance. -/
theorem IsEuclideanLengthMetric.internalMetric_eq_of_boundary_clearance
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) {U : Set ℂ} {x y : ℂ} {δ : ℝ}
    (hclear : ∀ z ∉ U, δ ≤ D x z) (hxy : D x y < δ) :
    internalMetric D U x y = ENNReal.ofReal (D x y) := by
  apply le_antisymm
  · apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    let η : ℝ := min ((ε : ℝ) / 2) ((δ - D x y) / 2)
    have hεr : (0 : ℝ) < ε := by exact_mod_cast hε
    have hη : 0 < η := lt_min (by linarith) (by linarith)
    have hηsmall : D x y + η < δ := by
      have := min_le_right ((ε : ℝ) / 2) ((δ - D x y) / 2)
      dsimp [η]
      linarith
    have hηε : ENNReal.ofReal η ≤ (ε : ℝ≥0∞) := by
      have hηle : η ≤ (ε : ℝ) := by
        have := min_le_left ((ε : ℝ) / 2) ((δ - D x y) / 2)
        dsimp [η]
        have hε0 : 0 ≤ (ε : ℝ) := ε.property
        linarith
      exact_mod_cast hηle
    obtain ⟨p, hp⟩ := hD.exists_pathLength_lt hnonneg x y hη
    have hpδ : pathLength D p < ENNReal.ofReal δ :=
      hp.trans_le (ENNReal.ofReal_le_ofReal hηsmall.le)
    have hpU := hD.path_stays_inside_of_boundary_clearance hnonneg hclear p hpδ
    have hle : internalMetric D U x y ≤ pathLength D p :=
      iInf_le_of_le p (iInf_le _ hpU)
    calc
      internalMetric D U x y ≤ pathLength D p := hle
      _ ≤ ENNReal.ofReal (D x y + η) := hp.le
      _ = ENNReal.ofReal (D x y) + ENNReal.ofReal η :=
        ENNReal.ofReal_add (hnonneg x y) hη.le
      _ ≤ ENNReal.ofReal (D x y) + ε := add_le_add (le_refl _) hηε
  · rw [hD.ofReal_eq_internalMetric]
    exact internalMetric_anti D (subset_univ _) x y

end HarmonicBalls

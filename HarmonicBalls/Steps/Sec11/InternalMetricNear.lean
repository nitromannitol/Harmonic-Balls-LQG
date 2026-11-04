import HarmonicBalls.Steps.Sec11.ApproximatePaths
import HarmonicBalls.Steps.Sec11.PinchInequalities

/-!
# Internal distance near a point

A length metric inducing the Euclidean topology agrees locally with the
internal metric of any Euclidean-open neighborhood.
-/

namespace HarmonicBalls

open Set Metric Filter Topology
open scoped ENNReal

/-- A sufficiently short path from `x` remains inside an open neighborhood
of `x`. -/
theorem IsEuclideanLengthMetric.path_stays_in_open_of_short
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) {U : Set ℂ} (hU : IsOpen U)
    {x : ℂ} (hx : x ∈ U) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y (p : Path x y),
      pathLength D p < ENNReal.ofReal δ → ∀ t, p t ∈ U := by
  obtain ⟨δ, hδ, hball⟩ := (hD.isOpen_iff U).mp hU x hx
  refine ⟨δ, hδ, ?_⟩
  intro y p hp t
  apply hball
  have ht : (t : ℝ) ∈ Icc (0 : ℝ) 1 := t.property
  have hseg := hD.ofReal_two_segment_le_pathLength hnonneg p ht
  have hbound : ENNReal.ofReal (D x (p.extend t)) ≤
      ENNReal.ofReal (D x (p.extend t) + D (p.extend t) y) :=
    ENNReal.ofReal_le_ofReal (by linarith [hnonneg (p.extend t) y])
  have hlt := lt_of_le_of_lt (hbound.trans hseg) hp
  have hd : D x (p.extend t) < δ :=
    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (hnonneg x (p.extend t))).mp hlt
  simpa only [Path.extend_apply _ ht] using hd

/-- Around each point of an open set, the internal distance from that point
is exactly the original length metric. -/
theorem IsEuclideanLengthMetric.internalMetric_eq_of_near
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) {U : Set ℂ} (hU : IsOpen U)
    {x : ℂ} (hx : x ∈ U) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y, D x y < δ →
      internalMetric D U x y = ENNReal.ofReal (D x y) := by
  obtain ⟨δ, hδ, hstay⟩ := hD.path_stays_in_open_of_short hnonneg hU hx
  refine ⟨δ, hδ, ?_⟩
  intro y hy
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
        have h := min_le_left ((ε : ℝ) / 2) ((δ - D x y) / 2)
        dsimp [η]
        have hε0 : 0 ≤ (ε : ℝ) := ε.property
        linarith
      exact_mod_cast hηle
    obtain ⟨p, hp⟩ := hD.exists_pathLength_lt hnonneg x y hη
    have hpδ : pathLength D p < ENNReal.ofReal δ :=
      hp.trans_le (ENNReal.ofReal_le_ofReal hηsmall.le)
    have hpU := hstay y p hpδ
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

/-- The internal metric from a point agrees in a Euclidean neighborhood with
the original metric. -/
theorem IsEuclideanLengthMetric.eventually_internalMetric_eq
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) {U : Set ℂ} (hU : IsOpen U)
    {x : ℂ} (hx : x ∈ U) :
    ∀ᶠ y in 𝓝 x, internalMetric D U x y = ENNReal.ofReal (D x y) := by
  obtain ⟨δ, hδ, heq⟩ := hD.internalMetric_eq_of_near hnonneg hU hx
  have hcont : Continuous (fun y => D x y) := by
    simpa only [hD.symm x] using hD.continuous_left x
  have hopen : IsOpen {y | D x y < δ} := isOpen_lt hcont continuous_const
  have hxmem : x ∈ {y | D x y < δ} := by
    change D x x < δ
    simpa only [hD.self_eq_zero] using hδ
  filter_upwards [hopen.mem_nhds hxmem] with y hy
  exact heq y hy

/-- For an open set, the internal distance from an interior point is
continuous at that point. -/
theorem IsEuclideanLengthMetric.continuousAt_internalMetric_self
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) {U : Set ℂ} (hU : IsOpen U)
    {x : ℂ} (hx : x ∈ U) :
    ContinuousAt (fun y => internalMetric D U x y) x := by
  have hbase : Continuous (fun y => D x y) := by
    simpa only [hD.symm x] using hD.continuous_left x
  have hcont : Continuous (fun y => ENNReal.ofReal (D x y)) :=
    ENNReal.continuous_ofReal.comp hbase
  exact hcont.continuousAt.congr_of_eventuallyEq
    (hD.eventually_internalMetric_eq hnonneg hU hx)

end HarmonicBalls

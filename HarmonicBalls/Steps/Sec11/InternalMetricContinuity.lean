import HarmonicBalls.Steps.Sec11.InternalMetricPaths

/-!
# Continuity of internal distances
-/

namespace HarmonicBalls

open Set Filter Topology
open scoped ENNReal

/-- On an open domain, the internal distance from a point to itself is zero. -/
theorem IsEuclideanLengthMetric.internalMetric_self_of_mem_open
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) {U : Set ℂ} (hU : IsOpen U)
    {y : ℂ} (hy : y ∈ U) : internalMetric D U y y = 0 := by
  obtain ⟨δ, hδ, heq⟩ := hD.internalMetric_eq_of_near hnonneg hU hy
  have hyy : D y y < δ := by simpa only [hD.self_eq_zero] using hδ
  simpa only [hD.self_eq_zero, ENNReal.ofReal_zero] using heq y hyy

/-- The internal distance from any fixed point is continuous at each point
of an open domain, including when the distance is infinite. -/
theorem IsEuclideanLengthMetric.continuousAt_internalMetric
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) {U : Set ℂ} (hU : IsOpen U)
    (x : ℂ) {y : ℂ} (hy : y ∈ U) :
    ContinuousAt (fun t => internalMetric D U x t) y := by
  have hself : internalMetric D U y y = 0 := hD.internalMetric_self_of_mem_open hnonneg hU hy
  have hdelta : Tendsto (fun t => internalMetric D U y t) (𝓝 y) (𝓝 0) := by
    have hh := hD.continuousAt_internalMetric_self hnonneg hU hy
    change Tendsto (fun t => internalMetric D U y t) (𝓝 y) (𝓝 (internalMetric D U y y)) at hh
    rw [hself] at hh
    exact hh
  have hadd (a : ℝ≥0∞) : Tendsto (fun t => a + internalMetric D U y t) (𝓝 y) (𝓝 a) := by
    simpa only [add_zero] using (tendsto_const_nhds.add hdelta :
      Tendsto (fun t => a + internalMetric D U y t) (𝓝 y) (𝓝 (a + 0)))
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards [(hadd a).eventually_lt_const ha] with t ht
    have htri := hD.internalMetric_triangle U x t y
    rw [hD.internalMetric_symm U t y] at htri
    by_contra hnot
    have hle : internalMetric D U x t ≤ a := le_of_not_gt hnot
    have := add_le_add hle (le_refl (internalMetric D U y t))
    exact (not_le_of_gt ht) (htri.trans this)
  · intro a ha
    filter_upwards [(hadd (internalMetric D U x y)).eventually_lt_const ha] with t ht
    exact lt_of_le_of_lt (hD.internalMetric_triangle U x y t) ht

/-- The internal distance from a fixed point is continuous on an open domain. -/
theorem IsEuclideanLengthMetric.continuousOn_internalMetric
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) {U : Set ℂ} (hU : IsOpen U) (x : ℂ) :
    ContinuousOn (fun y => internalMetric D U x y) U := by
  intro y hy
  exact (hD.continuousAt_internalMetric hnonneg hU x hy).continuousWithinAt

/-- Joint continuity of internal distance on the product of an open domain
with itself; different path components may have infinite distance. -/
theorem IsEuclideanLengthMetric.continuousAt_internalMetric_pair
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) {U : Set ℂ} (hU : IsOpen U)
    {x y : ℂ} (hx : x ∈ U) (hy : y ∈ U) :
    ContinuousAt (fun p : ℂ × ℂ => internalMetric D U p.1 p.2) (x, y) := by
  have hxself := hD.internalMetric_self_of_mem_open hnonneg hU hx
  have hyself := hD.internalMetric_self_of_mem_open hnonneg hU hy
  have hxdel : Tendsto (fun p : ℂ × ℂ => internalMetric D U x p.1) (𝓝 (x, y)) (𝓝 0) := by
    have hh := (hD.continuousAt_internalMetric_self hnonneg hU hx).comp
      (continuous_fst.continuousAt : ContinuousAt (Prod.fst : ℂ × ℂ → ℂ) (x, y))
    change Tendsto _ _ (𝓝 (internalMetric D U x x)) at hh
    rw [hxself] at hh
    exact hh
  have hydel : Tendsto (fun p : ℂ × ℂ => internalMetric D U y p.2) (𝓝 (x, y)) (𝓝 0) := by
    have hh := (hD.continuousAt_internalMetric_self hnonneg hU hy).comp
      (continuous_snd.continuousAt : ContinuousAt (Prod.snd : ℂ × ℂ → ℂ) (x, y))
    change Tendsto _ _ (𝓝 (internalMetric D U y y)) at hh
    rw [hyself] at hh
    exact hh
  let δ : ℂ × ℂ → ℝ≥0∞ := fun p => internalMetric D U x p.1 + internalMetric D U y p.2
  have hdelta : Tendsto δ (𝓝 (x, y)) (𝓝 0) := by
    simpa only [zero_add] using hxdel.add hydel
  have hadd (a : ℝ≥0∞) : Tendsto (fun p => a + δ p) (𝓝 (x, y)) (𝓝 a) := by
    simpa only [add_zero] using (tendsto_const_nhds.add hdelta :
      Tendsto (fun p => a + δ p) (𝓝 (x, y)) (𝓝 (a + 0)))
  have hupper (u v : ℂ) : internalMetric D U u v ≤ internalMetric D U x y + δ (u, v) := by
    calc
      internalMetric D U u v ≤ internalMetric D U u x + internalMetric D U x v :=
        hD.internalMetric_triangle U u x v
      _ ≤ internalMetric D U u x + (internalMetric D U x y + internalMetric D U y v) :=
        add_le_add le_rfl (hD.internalMetric_triangle U x y v)
      _ = internalMetric D U x y + δ (u, v) := by
        dsimp [δ]
        rw [hD.internalMetric_symm U u x]
        ac_rfl
  have hlower (u v : ℂ) : internalMetric D U x y ≤ internalMetric D U u v + δ (u, v) := by
    calc
      internalMetric D U x y ≤ internalMetric D U x u + internalMetric D U u y :=
        hD.internalMetric_triangle U x u y
      _ ≤ internalMetric D U x u + (internalMetric D U u v + internalMetric D U v y) :=
        add_le_add le_rfl (hD.internalMetric_triangle U u v y)
      _ = internalMetric D U u v + δ (u, v) := by
        dsimp [δ]
        rw [hD.internalMetric_symm U v y]
        ac_rfl
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards [(hadd a).eventually_lt_const ha] with p hp
    by_contra hn
    have hle : internalMetric D U p.1 p.2 ≤ a := le_of_not_gt hn
    have hbound := add_le_add hle (le_refl (δ p))
    exact (not_le_of_gt hp) ((hlower p.1 p.2).trans hbound)
  · intro a ha
    filter_upwards [(hadd (internalMetric D U x y)).eventually_lt_const ha] with p hp
    exact lt_of_le_of_lt (hupper p.1 p.2) hp

/-- Internal distance is jointly continuous on the product of an open domain. -/
theorem IsEuclideanLengthMetric.continuousOn_internalMetric_pair
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) {U : Set ℂ} (hU : IsOpen U) :
    ContinuousOn (fun p : ℂ × ℂ => internalMetric D U p.1 p.2) (U ×ˢ U) := by
  intro p hp
  exact (hD.continuousAt_internalMetric_pair hnonneg hU hp.1 hp.2).continuousWithinAt

end HarmonicBalls

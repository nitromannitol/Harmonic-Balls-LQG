import HarmonicBalls.Steps.Sec11.ProperMetricDyadic

/-!
# Extending dyadic isometries

Compactness supplies an image for each point of the interval, characterized
by its distances to the dyadic images.
-/

namespace HarmonicBalls

open Metric Set Filter
open scoped Topology

/-- An isometric dyadic map into a compact metric ball has a point at every
parameter with the correct distances to all dyadic points. -/
theorem IsEuclideanLengthMetric.exists_dyadic_extension_point
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y)
    (hcompact : ∀ x : ℂ, ∀ R : ℝ, IsCompact {z : ℂ | D x z ≤ R})
    (x y : ℂ) (g : ℕ × ℕ → ℂ) (hg0 : g (0, 0) = x)
    (hg : ∀ m k l j : ℕ, k ≤ 2 ^ m → j ≤ 2 ^ l →
      D (g (m, k)) (g (l, j)) =
        |(k : ℝ) / (2 ^ m : ℕ) - (j : ℝ) / (2 ^ l : ℕ)| * D x y)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ∃ p : ℂ, ∀ m k : ℕ, k ≤ 2 ^ m →
      D p (g (m, k)) = |t - (k : ℝ) / (2 ^ m : ℕ)| * D x y := by
  classical
  choose m k hk hnear using fun n : ℕ =>
    exists_dyadic_approximation ht (show 0 < (1 : ℝ) / ((n : ℝ) + 1) by positivity)
  let a : ℕ → ℝ := fun n => (k n : ℝ) / (2 ^ m n : ℕ)
  have ha : Tendsto a atTop (𝓝 t) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have hzero : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hbound : Tendsto (fun n => |a n - t|) atTop (𝓝 0) :=
      squeeze_zero (fun _ => abs_nonneg _) (fun n => le_of_lt (hnear n)) hzero
    simpa only [Real.dist_eq] using hbound
  let K : Set ℂ := {z | D x z ≤ D x y}
  have hK : IsCompact K := hcompact x (D x y)
  have hmem : ∀ n, g (m n, k n) ∈ K := by
    intro n
    change D x (g (m n, k n)) ≤ D x y
    have h := hg 0 0 (m n) (k n) (by simp) (hk n)
    rw [hg0] at h
    have hden : (0 : ℝ) < ((2 ^ m n : ℕ) : ℝ) := by positivity
    have hbound : (k n : ℝ) / (2 ^ m n : ℕ) ≤ 1 := by
      apply (div_le_one hden).2
      exact_mod_cast hk n
    have hnon : 0 ≤ (k n : ℝ) / (2 ^ m n : ℕ) := by positivity
    simp only [Nat.cast_zero, zero_div, zero_sub, abs_neg, abs_of_nonneg hnon] at h
    rw [h]
    nlinarith [hnonneg x y]
  obtain ⟨p, _, φ, hφ, hp⟩ := hK.tendsto_subseq hmem
  refine ⟨p, ?_⟩
  intro l j hj
  have hp' : Tendsto (fun n => g (m (φ n), k (φ n))) atTop (𝓝 p) := hp
  have hd := (hD.continuous_pair.tendsto (p, g (l, j))).comp
    (hp'.prodMk_nhds tendsto_const_nhds)
  have ha' := ha.comp hφ.tendsto_atTop
  have hv : Tendsto (fun n => |a (φ n) - (j : ℝ) / (2 ^ l : ℕ)| * D x y)
      atTop (𝓝 (|t - (j : ℝ) / (2 ^ l : ℕ)| * D x y)) :=
    (ha'.sub tendsto_const_nhds).abs.mul_const _
  have heq : ∀ n, D (g (m (φ n), k (φ n))) (g (l, j)) =
      |a (φ n) - (j : ℝ) / (2 ^ l : ℕ)| * D x y := by
    intro n
    exact hg (m (φ n)) (k (φ n)) l j (hk (φ n)) hj
  exact tendsto_nhds_unique_of_forall hd hv heq

/-- Convergence in a metric which induces the Euclidean topology implies
convergence in the Euclidean topology. -/
theorem IsEuclideanLengthMetric.tendsto_of_distance_tendsto_zero
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {α : Type*} {l : Filter α} {f : α → ℂ} {p : ℂ}
    (h : Tendsto (fun a => D (f a) p) l (𝓝 0)) : Tendsto f l (𝓝 p) := by
  apply _root_.tendsto_nhds.mpr
  intro U hU hp
  obtain ⟨ε, hε, hball⟩ := (hD.isOpen_iff U).1 hU p hp
  filter_upwards [h.eventually (Iio_mem_nhds hε)] with a ha
  apply hball
  rw [hD.symm]
  exact ha

/-- The dyadic isometry extends to the entire unit interval, preserving all
pairwise distances and the two endpoints. -/
theorem IsEuclideanLengthMetric.exists_isometric_interval_map
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y)
    (hcompact : ∀ x : ℂ, ∀ R : ℝ, IsCompact {z : ℂ | D x z ≤ R})
    (x y : ℂ) :
    ∃ F : Icc (0 : ℝ) 1 → ℂ, F ⟨0, by simp⟩ = x ∧ F ⟨1, by simp⟩ = y ∧
      ∀ s t, D (F s) (F t) = |(s : ℝ) - (t : ℝ)| * D x y := by
  classical
  obtain ⟨g, hg0, hg1, hg⟩ := hD.exists_isometric_dyadic_map hnonneg hcompact x y
  choose F hF using fun t : Icc (0 : ℝ) 1 =>
    hD.exists_dyadic_extension_point hnonneg hcompact x y g hg0 hg t t.property
  have hF0 : F ⟨0, by simp⟩ = x := by
    apply hD.eq_of_eq_zero
    have h := hF ⟨0, by simp⟩ 0 0 (by simp)
    simpa only [hg0, Nat.cast_zero, zero_div, sub_zero, abs_zero, zero_mul] using h
  have hF1 : F ⟨1, by simp⟩ = y := by
    apply hD.eq_of_eq_zero
    have h := hF ⟨1, by simp⟩ 0 1 (by simp)
    simpa only [hg1, pow_zero, Nat.cast_one, div_one, sub_self, abs_zero, zero_mul] using h
  refine ⟨F, hF0, hF1, ?_⟩
  intro s t
  choose m k hk hnear using fun n : ℕ =>
    exists_dyadic_approximation t.property
      (show 0 < (1 : ℝ) / ((n : ℝ) + 1) by positivity)
  let a : ℕ → ℝ := fun n => (k n : ℝ) / (2 ^ m n : ℕ)
  have ha : Tendsto a atTop (𝓝 (t : ℝ)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have hzero : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hb : Tendsto (fun n => |a n - (t : ℝ)|) atTop (𝓝 0) :=
      squeeze_zero (fun _ => abs_nonneg _) (fun n => le_of_lt (hnear n)) hzero
    simpa only [Real.dist_eq] using hb
  have hdist : Tendsto (fun n => D (g (m n, k n)) (F t)) atTop (𝓝 0) := by
    have heq : (fun n => D (g (m n, k n)) (F t)) =
        (fun n => |(t : ℝ) - a n| * D x y) := by
      funext n
      rw [hD.symm]
      exact hF t (m n) (k n) (hk n)
    rw [heq]
    have hbase : Tendsto (fun n => (t : ℝ) - a n) atTop (𝓝 ((t : ℝ) - t)) :=
      tendsto_const_nhds.sub ha
    simpa only [sub_self, abs_zero, zero_mul] using hbase.abs.mul_const (D x y)
  have hgseq : Tendsto (fun n => g (m n, k n)) atTop (𝓝 (F t)) :=
    hD.tendsto_of_distance_tendsto_zero hdist
  have hc : Continuous fun z : ℂ => D (F s) z := by
    simpa only [hD.symm (F s)] using hD.continuous_left (F s)
  have hlhs := (hc.tendsto (F t)).comp hgseq
  have hrhs : Tendsto (fun n => |(s : ℝ) - a n| * D x y) atTop
      (𝓝 (|(s : ℝ) - (t : ℝ)| * D x y)) :=
    (tendsto_const_nhds.sub ha).abs.mul_const _
  have heq : ∀ n, D (F s) (g (m n, k n)) = |(s : ℝ) - a n| * D x y :=
    fun n => hF s (m n) (k n) (hk n)
  exact tendsto_nhds_unique_of_forall hlhs hrhs heq

/-- A Euclidean length metric with compact closed metric balls admits a
constant-speed geodesic between any two points. -/
theorem IsEuclideanLengthMetric.exists_geodesic_of_compact_closedBalls
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y)
    (hcompact : ∀ x : ℂ, ∀ R : ℝ, IsCompact {z : ℂ | D x z ≤ R})
    (x y : ℂ) :
    ∃ p : Path x y, ∀ s t : Icc (0 : ℝ) 1,
      D (p s) (p t) = |(s : ℝ) - (t : ℝ)| * D x y := by
  obtain ⟨F, hF0, hF1, hF⟩ :=
    hD.exists_isometric_interval_map hnonneg hcompact x y
  have hc : Continuous F := by
    apply continuous_iff_continuousAt.2
    intro t
    apply hD.tendsto_of_distance_tendsto_zero
    have heq : (fun s : Icc (0 : ℝ) 1 => D (F s) (F t)) =
        (fun s : Icc (0 : ℝ) 1 => |(s : ℝ) - (t : ℝ)| * D x y) := by
      funext s
      exact hF s t
    rw [heq]
    have hbase : Tendsto (fun s : Icc (0 : ℝ) 1 => (s : ℝ) - (t : ℝ))
        (𝓝 t) (𝓝 ((t : ℝ) - t)) := continuous_subtype_val.continuousAt.sub tendsto_const_nhds
    simpa only [sub_self, abs_zero, zero_mul] using hbase.abs.mul_const (D x y)
  refine ⟨⟨⟨F, hc⟩, hF0, hF1⟩, ?_⟩
  exact hF

end HarmonicBalls

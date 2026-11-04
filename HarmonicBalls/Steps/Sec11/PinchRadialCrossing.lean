import HarmonicBalls.Steps.Sec11.LocalPathLength
import HarmonicBalls.Steps.Sec11.PinchInequalities

/-! # Radial crossings for the pinch-point argument

A near-minimizing path crosses successive Euclidean spheres in order; the
corresponding crossing distances therefore have a bounded sum.
-/

namespace HarmonicBalls

open Set Metric
open scoped ENNReal

private theorem exists_path_sphere_before {y : ℂ} (p : Path 0 y)
    {t r : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hr : 0 ≤ r)
    (hle : r ≤ dist (p.extend t) 0) :
    ∃ s ∈ Icc (0 : ℝ) t, p.extend s ∈ sphere 0 r := by
  let f : ℝ → ℝ := fun s => dist (p.extend s) 0
  have hcont : Continuous f := p.continuous_extend.dist continuous_const
  have hzero : f 0 = 0 := by simp [f]
  have hm : r ∈ Icc (f 0) (f t) := ⟨by simpa [hzero] using hr, hle⟩
  obtain ⟨s, hs, heq⟩ := intermediate_value_Icc ht.1 hcont.continuousOn hm
  exact ⟨s, hs, by simpa only [mem_sphere, f] using heq⟩

/-- The length of a path dominates its distances along three ordered segments. -/
theorem IsEuclideanLengthMetric.ofReal_three_ordered_segments_le_pathLength
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) {w z : ℂ} (p : Path w z)
    {s t u : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (hu : u ∈ Icc (0 : ℝ) 1) (hst : s ≤ t) (htu : t ≤ u) :
    ENNReal.ofReal (D w (p.extend s) + D (p.extend s) (p.extend t) +
      D (p.extend t) (p.extend u)) ≤ pathLength D p := by
  let v : ℕ → ℝ := fun n => if n = 0 then 0 else if n = 1 then s else if n = 2 then t else u
  have hv : Monotone v := by
    apply monotone_nat_of_le_succ
    intro n
    rcases n with _ | _ | _ | n
    · simpa [v] using hs.1
    · simpa [v] using hst
    · simpa [v] using htu
    · simp [v]
  have hvmem : ∀ n, v n ∈ Icc (0 : ℝ) 1 := by
    intro n
    rcases n with _ | _ | _ | n
    · simp [v]
    · simpa [v] using hs
    · simpa [v] using ht
    · simpa [v] using hu
  have hle := le_iSup (fun q : ℕ × {u : ℕ → ℝ // Monotone u ∧ ∀ i, u i ∈ Icc 0 1} =>
    ∑ i ∈ Finset.range q.1, ENNReal.ofReal (D (p.extend (q.2.1 (i + 1)))
      (p.extend (q.2.1 i)))) ⟨3, ⟨v, hv, hvmem⟩⟩
  change _ ≤ pathLength D p at hle
  norm_num [v, Finset.sum_range_succ, p.extend_zero] at hle
  rw [ENNReal.ofReal_add (add_nonneg (hnonneg w (p.extend s)) (hnonneg (p.extend s) (p.extend t)))
    (hnonneg (p.extend t) (p.extend u)), ENNReal.ofReal_add (hnonneg w (p.extend s))
    (hnonneg (p.extend s) (p.extend t))]
  simpa only [hD.symm (p.extend s) w, hD.symm (p.extend t) (p.extend s),
    hD.symm (p.extend u) (p.extend t)] using hle

/-- Radial set distances through three nested spheres sum to at most the
center-to-outer-sphere distance for a Euclidean length metric. -/
theorem IsEuclideanLengthMetric.pinch_radial_crossing
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) {δ : ℝ} (hδ : 0 ≤ δ) (hδ5 : 3 * δ ≤ 5) :
    ENNReal.ofReal (setDist D {0} (sphere 0 δ)) +
      ENNReal.ofReal (setDist D (sphere 0 (2 * δ)) (sphere 0 (3 * δ))) +
      ENNReal.ofReal (setDist D (sphere 0 δ) (sphere 0 (2 * δ))) ≤
    ENNReal.ofReal (setDist D {0} (sphere 0 5)) := by
  conv_rhs => rw [ofReal_setDist_eq_iInf (singleton_nonempty 0)
    (NormedSpace.sphere_nonempty.mpr (by norm_num))]; simp only [iInf_singleton]
  refine le_iInf fun y => le_iInf fun hy => ?_
  rw [hD.ofReal_eq_internalMetric]
  refine le_iInf fun p => le_iInf fun _ => ?_
  have hy' : dist (p.extend 1) 0 = 5 := by simpa [p.extend_one, mem_sphere] using hy
  obtain ⟨u, hu, hu'⟩ := exists_path_sphere_before p (t := 1) (by simp) (by positivity : 0 ≤ 3 * δ)
    (by rw [hy']; exact hδ5)
  have hud : dist (p.extend u) 0 = 3 * δ := by simpa [mem_sphere] using hu'
  have hu1 : u ∈ Icc (0 : ℝ) 1 := hu
  obtain ⟨t, ht, ht'⟩ := exists_path_sphere_before p hu1 (by positivity : 0 ≤ 2 * δ)
    (by rw [hud]; nlinarith)
  have htd : dist (p.extend t) 0 = 2 * δ := by simpa [mem_sphere] using ht'
  have ht1 : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.trans hu.2⟩
  obtain ⟨s, hs, hs'⟩ := exists_path_sphere_before p ht1 hδ (by rw [htd]; nlinarith)
  have hs1 : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1, hs.2.trans ht1.2⟩
  have h1 := ENNReal.ofReal_le_ofReal (setDist_le_of_nonneg D hnonneg (mem_singleton 0) hs')
  have h2 := ENNReal.ofReal_le_ofReal (setDist_le_of_nonneg D hnonneg hs' ht')
  have h3 := ENNReal.ofReal_le_ofReal (setDist_le_of_nonneg D hnonneg ht' hu')
  calc
    _ ≤ ENNReal.ofReal (D 0 (p.extend s)) + ENNReal.ofReal (D (p.extend s) (p.extend t)) +
        ENNReal.ofReal (D (p.extend t) (p.extend u)) := by
          calc
            _ = ENNReal.ofReal (setDist D {0} (sphere 0 δ)) +
                ENNReal.ofReal (setDist D (sphere 0 δ) (sphere 0 (2 * δ))) +
                ENNReal.ofReal (setDist D (sphere 0 (2 * δ)) (sphere 0 (3 * δ))) := by ac_rfl
            _ ≤ _ := add_le_add (add_le_add h1 h2) h3
    _ = ENNReal.ofReal (D 0 (p.extend s) + D (p.extend s) (p.extend t) +
          D (p.extend t) (p.extend u)) := by
        rw [ENNReal.ofReal_add (add_nonneg (hnonneg _ _) (hnonneg _ _)) (hnonneg _ _),
          ENNReal.ofReal_add (hnonneg _ _) (hnonneg _ _)]
    _ ≤ pathLength D p := hD.ofReal_three_ordered_segments_le_pathLength hnonneg p hs1 ht1 hu1 hs.2 ht.2

end HarmonicBalls

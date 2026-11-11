import HarmonicBalls.Proofs.Metric.AnnulusAcrossPositiveFinite
import HarmonicBalls.Steps.Sec11.ProperMetricDyadic

/-!
# Uniform separation for compact families of annuli

A fixed compatible metric uniformly separates Euclidean-separated pairs in a
compact set. Consequently, annuli in a compact parameter family with bounded
nonnegative radii and a uniform positive gap have uniformly positive ambient
across distance. No randomness or measurability in the parameters is used.
-/

namespace HarmonicBalls

open Set Metric
open scoped ENNReal

/-- On a compact set, a continuous separating distance has a uniform positive
lower bound for pairs separated by at least a fixed positive Euclidean distance. -/
theorem compact_euclidean_separation {D : ℂ → ℂ → ℝ}
    (hcont : Continuous fun p : ℂ × ℂ => D p.1 p.2)
    (hnonneg : ∀ x y, 0 ≤ D x y)
    (hsep : ∀ x y, D x y = 0 → x = y)
    {K : Set ℂ} (hK : IsCompact K) {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ K, ∀ y ∈ K, δ ≤ dist x y → c ≤ D x y := by
  let S : Set (ℂ × ℂ) := (K ×ˢ K) ∩ {p | δ ≤ dist p.1 p.2}
  have hS : IsCompact S := (hK.prod hK).inter_right
    (isClosed_le continuous_const (continuous_fst.dist continuous_snd))
  obtain ⟨c, hc, hmin⟩ := hS.exists_forall_le' hcont.continuousOn (a := 0) (by
    intro p hp
    have hne : p.1 ≠ p.2 := by
      intro heq
      have : δ ≤ 0 := by simpa [heq] using hp.2
      linarith
    exact lt_of_le_of_ne (hnonneg p.1 p.2) (Ne.symm (fun hz => hne (hsep p.1 p.2 hz))))
  exact ⟨c, hc, fun x hx y hy hxy => hmin (x, y) ⟨⟨hx, hy⟩, hxy⟩⟩

/-- Let `P` be a compact set of triples `(center, inner radius, outer radius)`.
If the inner radius is nonnegative, the outer radius is at most `R`, and their
gap is at least `δ > 0` uniformly on `P`, one positive constant bounds every
ambient across distance from below. The family may be empty. -/
theorem IsEuclideanLengthMetric.compact_family_pfefferAcross_pos
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {P : Set (ℂ × ℝ × ℝ)} (hP : IsCompact P) {R δ : ℝ} (hδ : 0 < δ)
    (hbound : ∀ p ∈ P, 0 ≤ p.2.1 ∧ p.2.1 + δ ≤ p.2.2 ∧ p.2.2 ≤ R) :
    ∃ c : ℝ≥0∞, 0 < c ∧ ∀ p ∈ P, c ≤ pfefferAcross D p.1 p.2.1 p.2.2 := by
  let K : Set ℂ := (P ×ˢ closedBall (0 : ℂ) R).image (fun q => q.1.1 + q.2)
  have hK : IsCompact K := (hP.prod (isCompact_closedBall 0 R)).image
    ((continuous_fst.fst).add continuous_snd)
  obtain ⟨c, hc, hcK⟩ := compact_euclidean_separation hD.continuous_pair
    hD.distance_nonneg hD.eq_of_eq_zero hK hδ
  refine ⟨ENNReal.ofReal c, ENNReal.ofReal_pos.mpr hc, ?_⟩
  intro p hp
  have hpbound := hbound p hp
  unfold pfefferAcross
  refine le_iInf fun x => le_iInf fun hx => le_iInf fun y => le_iInf fun hy => ?_
  have hxR : dist x p.1 ≤ R := by
    rw [mem_sphere] at hx
    linarith
  have hyR : dist y p.1 ≤ R := by
    rw [mem_sphere] at hy
    linarith
  have hxK : x ∈ K := by
    refine ⟨(p, x - p.1), ⟨hp, ?_⟩, ?_⟩
    · simpa [mem_closedBall, dist_eq_norm, norm_sub_rev] using hxR
    · simp
  have hyK : y ∈ K := by
    refine ⟨(p, y - p.1), ⟨hp, ?_⟩, ?_⟩
    · simpa [mem_closedBall, dist_eq_norm, norm_sub_rev] using hyR
    · simp
  have hxy : δ ≤ dist x y := by
    have ht := dist_triangle y x p.1
    rw [mem_sphere] at hx hy
    rw [dist_comm y x] at ht
    linarith
  exact ENNReal.ofReal_le_ofReal (hcK x hxK y hyK hxy)


end HarmonicBalls

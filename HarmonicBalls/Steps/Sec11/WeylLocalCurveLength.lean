import HarmonicBalls.Steps.Sec11.WeylLocalLower

/-! # Local curve-length comparison under Weyl scaling

Pointwise comparison of distances along a curve transfers to its length.
-/

namespace HarmonicBalls

open Set
open scoped ENNReal

/-- An upper comparison for distances on a curve gives the same comparison
for its length. -/
theorem curveLength_le_mul_of_boundOn {D E : ℂ → ℂ → ℝ}
    (p : ℝ → ℂ) (a b : ℝ) (k : ℝ≥0∞)
    (h : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      ENNReal.ofReal (E (p s) (p t)) ≤ k * ENNReal.ofReal (D (p s) (p t))) :
    curveLength E p a b ≤ k * curveLength D p a b := by
  unfold curveLength
  rw [ENNReal.mul_iSup]
  apply iSup_mono
  intro q
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  exact h _ (q.2.2.2 (i + 1)) _ (q.2.2.2 i)

/-- A lower comparison for distances on a curve gives the same comparison
for its length. -/
theorem mul_curveLength_le_of_boundOn {D E : ℂ → ℂ → ℝ}
    (p : ℝ → ℂ) (a b : ℝ) (k : ℝ≥0∞)
    (h : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      k * ENNReal.ofReal (D (p s) (p t)) ≤ ENNReal.ofReal (E (p s) (p t))) :
    k * curveLength D p a b ≤ curveLength E p a b := by
  unfold curveLength
  rw [ENNReal.mul_iSup]
  apply iSup_mono
  intro q
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  exact h _ (q.2.2.2 (i + 1)) _ (q.2.2.2 i)

/-- On a sufficiently small metric neighborhood, the length of a
length-parametrized curve segment is controlled above and below by the
Weyl weight at the center. -/
theorem IsEuclideanLengthMetric.weylScaling_local_curveLength_comparison
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {ξ c : ℝ} (hξ : 0 ≤ ξ) (f : ℂ → ℝ) (hf : Continuous f)
    (hl : ∀ z, c ≤ f z) (hu : ∀ z, f z ≤ 0)
    (x : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ ∀ (p : ℝ → ℂ) (T a b : ℝ),
      IsLengthParametrized D p T → 0 ≤ a → a ≤ b → b ≤ T →
      (∀ t ∈ Icc a b, D x (p t) < r) →
      let E : ℂ → ℂ → ℝ := fun u v => (weylScaling D ξ f u v).toReal
      ENNReal.ofReal (Real.exp (ξ * f x - ε) * (b - a)) ≤ curveLength E p a b ∧
      curveLength E p a b ≤ ENNReal.ofReal (Real.exp (ξ * f x + ε) * (b - a)) := by
  obtain ⟨r, hr, hcomp⟩ := hD.weylScaling_local_comparison hξ f hf hl hu x hε
  refine ⟨r, hr, ?_⟩
  intro p T a b hp ha hab hb hinside
  dsimp only
  constructor
  · have h := mul_curveLength_le_of_boundOn p a b (ENNReal.ofReal (Real.exp (ξ * f x - ε)))
        (D := D) (E := fun u v => (weylScaling D ξ f u v).toReal) (by
          intro s hs t ht
          rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
          exact ENNReal.ofReal_le_ofReal (hcomp _ _ (hinside s hs) (hinside t ht)).1)
    rw [hp.2.2 a b ha hab hb, ← ENNReal.ofReal_mul (Real.exp_nonneg _)] at h
    exact h
  · have h := curveLength_le_mul_of_boundOn p a b (ENNReal.ofReal (Real.exp (ξ * f x + ε)))
        (D := D) (E := fun u v => (weylScaling D ξ f u v).toReal) (by
          intro s hs t ht
          rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
          exact ENNReal.ofReal_le_ofReal (hcomp _ _ (hinside s hs) (hinside t ht)).2)
    rw [hp.2.2 a b ha hab hb, ← ENNReal.ofReal_mul (Real.exp_nonneg _)] at h
    exact h

/-- A length-parametrized curve is one-Lipschitz in its length metric. -/
theorem IsEuclideanLengthMetric.dist_le_of_lengthParametrized
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {p : ℝ → ℂ} {T s t : ℝ} (hp : IsLengthParametrized D p T)
    (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) :
    D (p s) (p t) ≤ |t - s| := by
  have hordered (a b : ℝ) (ha : a ∈ Icc 0 T) (hb : b ∈ Icc 0 T)
      (hab : a ≤ b) : D (p a) (p b) ≤ b - a := by
    have hsub := hD.isLengthParametrized_subcurve hp ha.1 hab hb.2
    have h := hD.ofReal_dist_start_le_lengthParametrized hsub
      (show b - a ∈ Icc 0 (b - a) from ⟨sub_nonneg.mpr hab, le_rfl⟩)
    have h' : ENNReal.ofReal (D (p a) (p b)) ≤ ENNReal.ofReal (b - a) := by
      simpa only [add_zero, add_sub_cancel] using h
    exact (ENNReal.ofReal_le_ofReal_iff (sub_nonneg.mpr hab)).mp h'
  rcases le_total s t with hst | hts
  · rw [abs_of_nonneg (sub_nonneg.mpr hst)]
    exact hordered s t hs ht hst
  · rw [abs_of_nonpos (sub_nonpos.mpr hts), hD.symm]
    have h := hordered t s ht hs hts
    linarith

/-- The length of a short segment around a parameter value has the local
Weyl weight as its infinitesimal slope. -/
theorem IsEuclideanLengthMetric.weylScaling_local_segment_comparison
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {ξ c : ℝ} (hξ : 0 ≤ ξ) (f : ℂ → ℝ) (hf : Continuous f)
    (hl : ∀ z, c ≤ f z) (hu : ∀ z, f z ≤ 0)
    {p : ℝ → ℂ} {T t₀ : ℝ} (hp : IsLengthParametrized D p T)
    (ht₀ : t₀ ∈ Icc 0 T) {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ T →
      |a - t₀| < r → |b - t₀| < r →
      let E : ℂ → ℂ → ℝ := fun u v => (weylScaling D ξ f u v).toReal
      ENNReal.ofReal (Real.exp (ξ * f (p t₀) - ε) * (b - a)) ≤ curveLength E p a b ∧
      curveLength E p a b ≤ ENNReal.ofReal (Real.exp (ξ * f (p t₀) + ε) * (b - a)) := by
  obtain ⟨r, hr, hcomp⟩ :=
    hD.weylScaling_local_curveLength_comparison hξ f hf hl hu (p t₀) hε
  refine ⟨r, hr, ?_⟩
  intro a b ha hab hb hnearA hnearB
  apply hcomp p T a b hp ha hab hb
  intro t ht
  have htmem : t ∈ Icc 0 T := ⟨ha.trans ht.1, ht.2.trans hb⟩
  have hnear : |t - t₀| < r := by
    have hA := abs_lt.mp hnearA
    have hB := abs_lt.mp hnearB
    apply abs_lt.mpr
    constructor <;> linarith [ht.1, ht.2]
  exact lt_of_le_of_lt (hD.dist_le_of_lengthParametrized hp ht₀ htmem) hnear

/-- If a metric is dominated by the original one, each segment of an
originally length-parametrized curve has finite length in the new metric. -/
theorem curveLength_le_of_lengthParametrized_of_le
    {D E : ℂ → ℂ → ℝ} {p : ℝ → ℂ} {T a b : ℝ}
    (hp : IsLengthParametrized D p T) (hED : ∀ u v, E u v ≤ D u v)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T) :
    curveLength E p a b ≤ ENNReal.ofReal (b - a) := by
  have h := curveLength_le_mul_of_boundOn p a b 1 (D := D) (E := E) (by
    intro s hs t ht
    simpa only [one_mul] using ENNReal.ofReal_le_ofReal (hED (p s) (p t)))
  simpa only [one_mul, hp.2.2 a b ha hab hb] using h

/-- Cumulative length increments equal the length of the intervening segment
when the second metric is dominated by the original metric. -/
theorem IsEuclideanLengthMetric.cumulative_curveLength_sub
    {D E : ℂ → ℂ → ℝ} (hE : IsEuclideanLengthMetric E)
    {p : ℝ → ℂ} {T a b : ℝ} (hp : IsLengthParametrized D p T)
    (hED : ∀ u v, E u v ≤ D u v)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T) :
    (curveLength E p 0 b).toReal - (curveLength E p 0 a).toReal =
      (curveLength E p a b).toReal := by
  have haT : a ≤ T := hab.trans hb
  have hfinite₁ : curveLength E p 0 a ≠ ∞ :=
    (lt_of_le_of_lt (curveLength_le_of_lengthParametrized_of_le hp hED le_rfl ha haT)
      ENNReal.ofReal_lt_top).ne
  have hfinite₂ : curveLength E p a b ≠ ∞ :=
    (lt_of_le_of_lt (curveLength_le_of_lengthParametrized_of_le hp hED ha hab hb)
      ENNReal.ofReal_lt_top).ne
  have hsum := hE.curveLength_add p ha hab
  have hreal := congrArg ENNReal.toReal hsum
  rw [ENNReal.toReal_add hfinite₁ hfinite₂] at hreal
  linarith

/-- Cumulative length in a dominated metric is increasing and
one-Lipschitz along a length-parametrized curve. -/
theorem IsEuclideanLengthMetric.cumulative_curveLength_increment_bounds
    {D E : ℂ → ℂ → ℝ} (hE : IsEuclideanLengthMetric E)
    {p : ℝ → ℂ} {T a b : ℝ} (hp : IsLengthParametrized D p T)
    (hED : ∀ u v, E u v ≤ D u v)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T) :
    0 ≤ (curveLength E p 0 b).toReal - (curveLength E p 0 a).toReal ∧
    (curveLength E p 0 b).toReal - (curveLength E p 0 a).toReal ≤ b - a := by
  rw [hE.cumulative_curveLength_sub hp hED ha hab hb]
  constructor
  · exact ENNReal.toReal_nonneg
  · have hle := curveLength_le_of_lengthParametrized_of_le hp hED ha hab hb
    have hfin : curveLength E p a b ≠ ∞ :=
      (lt_of_le_of_lt hle ENNReal.ofReal_lt_top).ne
    have hreal := (ENNReal.toReal_le_toReal hfin ENNReal.ofReal_ne_top).2 hle
    simpa only [ENNReal.toReal_ofReal (sub_nonneg.mpr hab)] using hreal

/-- Cumulative length in a dominated metric is one-Lipschitz on the
original curve's parameter interval. -/
theorem IsEuclideanLengthMetric.cumulative_curveLength_lipschitzOn
    {D E : ℂ → ℂ → ℝ} (hE : IsEuclideanLengthMetric E)
    {p : ℝ → ℂ} {T : ℝ} (hp : IsLengthParametrized D p T)
    (hED : ∀ u v, E u v ≤ D u v) :
    LipschitzOnWith 1 (fun t => (curveLength E p 0 t).toReal) (Icc 0 T) := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro a ha b hb
  simp only [NNReal.coe_one, one_mul, Real.dist_eq]
  rcases le_total a b with hab | hba
  · obtain ⟨hpos, hbound⟩ := hE.cumulative_curveLength_increment_bounds hp hED ha.1 hab hb.2
    rw [abs_of_nonpos (by linarith : (curveLength E p 0 a).toReal - (curveLength E p 0 b).toReal ≤ 0),
      abs_of_nonpos (sub_nonpos.mpr hab)]
    linarith
  · obtain ⟨hpos, hbound⟩ := hE.cumulative_curveLength_increment_bounds hp hED hb.1 hba ha.2
    rw [abs_of_nonneg (by linarith : 0 ≤ (curveLength E p 0 a).toReal - (curveLength E p 0 b).toReal),
      abs_of_nonneg (sub_nonneg.mpr hba)]
    exact hbound


end HarmonicBalls

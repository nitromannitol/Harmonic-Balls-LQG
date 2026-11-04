import HarmonicBalls.Steps.Sec11.WeylScalingOrder
import HarmonicBalls.Steps.Sec11.ApproximatePaths
import HarmonicBalls.Steps.Sec11.PinchLocalEdgeCover

/-! # Local comparison for Weyl scaling

A constant upper bound on the weight in a metric neighborhood contracts
sufficiently short edges.  The zero-weight identity supplies near-minimizing
length-parametrized curves without an additional geodesic assumption.
-/

namespace HarmonicBalls

open MeasureTheory Set Metric
open scoped ENNReal

/-- Every point of a length-parametrized curve is within its elapsed length
of the starting point. -/
theorem IsEuclideanLengthMetric.ofReal_dist_start_le_lengthParametrized
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {p : ℝ → ℂ} {T t : ℝ} (hp : IsLengthParametrized D p T)
    (ht : t ∈ Icc 0 T) :
    ENNReal.ofReal (D (p 0) (p t)) ≤ ENNReal.ofReal T := by
  let u : ℕ → ℝ := fun n => if n = 0 then 0 else t
  have hu : Monotone u := by
    apply monotone_nat_of_le_succ
    intro n
    rcases n with _ | n
    · simpa [u] using ht.1
    · simp [u]
  have humem : ∀ n, u n ∈ Icc (0 : ℝ) T := by
    intro n
    rcases n with _ | n
    · simpa [u] using (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hp.1⟩)
    · simpa [u] using ht
  have h := le_iSup (fun q : ℕ × {u : ℕ → ℝ // Monotone u ∧ ∀ i, u i ∈ Icc 0 T} =>
    ∑ i ∈ Finset.range q.1, ENNReal.ofReal (D (p (q.2.1 (i + 1))) (p (q.2.1 i))))
      ⟨1, ⟨u, hu, humem⟩⟩
  change _ ≤ curveLength D p 0 T at h
  simpa [u, hD.symm, hp.2.2 0 T le_rfl hp.1 le_rfl] using h

/-- A bound on the Weyl exponent along a length-parametrized path bounds
its weighted endpoint distance. -/
theorem weylScaling_le_of_lengthParametrized
    (D : ℂ → ℂ → ℝ) (ξ : ℝ) (f : ℂ → ℝ) {x y : ℂ}
    {p : ℝ → ℂ} {T B : ℝ} (hp : IsLengthParametrized D p T)
    (h0 : p 0 = x) (hT : p T = y)
    (hweight : ∀ t ∈ Icc 0 T, ξ * f (p t) ≤ B) :
    weylScaling D ξ f x y ≤ ENNReal.ofReal (Real.exp B) * ENNReal.ofReal T := by
  refine (iInf₂_le T p).trans ((iInf₂_le hp h0).trans ((iInf_le _ hT).trans ?_))
  calc
    _ ≤ ∫⁻ _ in Icc (0 : ℝ) T, ENNReal.ofReal (Real.exp B) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (hweight t ht))
    _ = _ := by simp [lintegral_const, Real.volume_Icc]

/-- The zero-weight identity yields arbitrarily close length-parametrized
paths. -/
theorem exists_lengthParametrized_lt_of_weylScaling_zero
    {D : ℂ → ℂ → ℝ} {ξ : ℝ} (hzero : ∀ x y,
      weylScaling D ξ 0 x y = ENNReal.ofReal (D x y))
    (hnonneg : ∀ x y, 0 ≤ D x y) (x y : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ T p, IsLengthParametrized D p T ∧ p 0 = x ∧ p T = y ∧ T < D x y + ε := by
  have hlt : weylScaling D ξ 0 x y < ENNReal.ofReal (D x y + ε) := by
    rw [hzero]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (hnonneg x y)).2 (by linarith)
  unfold weylScaling at hlt
  obtain ⟨T, hlt⟩ := iInf_lt_iff.mp hlt
  obtain ⟨p, hlt⟩ := iInf_lt_iff.mp hlt
  obtain ⟨hp, hlt⟩ := iInf_lt_iff.mp hlt
  obtain ⟨h0, hlt⟩ := iInf_lt_iff.mp hlt
  obtain ⟨hT, hlt⟩ := iInf_lt_iff.mp hlt
  have hlen : ENNReal.ofReal T < ENNReal.ofReal (D x y + ε) := by
    simpa using hlt
  exact ⟨T, p, hp, h0, hT, (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hp.1).mp hlen⟩

/-- If the Weyl exponent is bounded above on a metric neighborhood,
then sufficiently short edges near its center obey the corresponding
multiplicative comparison. -/
theorem IsEuclideanLengthMetric.weylScaling_local_edge_bound
    {D E : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y)
    {ξ B : ℝ} {f : ℂ → ℝ}
    (hzero : ∀ x y, weylScaling D ξ 0 x y = ENNReal.ofReal (D x y))
    (hE : ∀ x y, ENNReal.ofReal (E x y) = weylScaling D ξ f x y)
    {x : ℂ} {R : ℝ} (hR : 0 < R)
    (hweight : ∀ z, D x z < R → ξ * f z ≤ B) :
    ∃ r : ℝ, 0 < r ∧ ∀ y z, D x y < r → D x z < r →
      E y z ≤ Real.exp B * D y z := by
  refine ⟨R / 4, by positivity, ?_⟩
  intro y z hy hz
  apply le_of_forall_pos_le_add
  intro ε hε
  let η := min (R / 4) (ε / (Real.exp B + 1))
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  obtain ⟨T, p, hp, hp0, hpT, hT⟩ :=
    exists_lengthParametrized_lt_of_weylScaling_zero hzero hnonneg y z hη
  have hpinside : ∀ t ∈ Icc 0 T, D x (p t) < R := by
    intro t ht
    have hpt := hD.ofReal_dist_start_le_lengthParametrized hp ht
    rw [hp0] at hpt
    have hpt' : D y (p t) ≤ T :=
      (ENNReal.ofReal_le_ofReal_iff hp.1).mp hpt
    have hyz := hD.triangle y x z
    have hxy := hD.triangle x y (p t)
    have hηR : η ≤ R / 4 := min_le_left _ _
    rw [hD.symm y x] at hyz
    linarith
  have hbound := weylScaling_le_of_lengthParametrized D ξ f hp hp0 hpT
    (fun t ht => hweight (p t) (hpinside t ht))
  rw [← hE y z, ← ENNReal.ofReal_mul (Real.exp_nonneg _)] at hbound
  have hbound' : E y z ≤ Real.exp B * T :=
    (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (Real.exp_nonneg _) hp.1)).mp hbound
  have hηε : η ≤ ε / (Real.exp B + 1) := min_le_right _ _
  have hmul : η * (Real.exp B + 1) ≤ ε := (le_div_iff₀ (by positivity)).mp hηε
  have hexp : 0 < Real.exp B := Real.exp_pos _
  nlinarith

/-- A Weyl exponent bound on the internal neighborhood bounds the
internal diameter by the same exponential factor. -/
theorem IsEuclideanLengthMetric.internalDiam_weylScaling_le
    {D E : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hE : IsEuclideanLengthMetric E) (hEnonneg : ∀ x y, 0 ≤ E x y)
    {ξ B δ : ℝ} {f : ℂ → ℝ} (A : Set ℂ)
    (hzero : ∀ x y, weylScaling D ξ 0 x y = ENNReal.ofReal (D x y))
    (hscale : ∀ x y, ENNReal.ofReal (E x y) = weylScaling D ξ f x y)
    (hweight : ∀ z ∈ thickening δ A, ξ * f z ≤ B) :
    internalDiam E δ A ≤ ENNReal.ofReal (Real.exp B) * internalDiam D δ A := by
  have hnonneg : ∀ x y, 0 ≤ D x y := by
    intro x y
    have h := hD.triangle x y x
    rw [hD.self_eq_zero, hD.symm y x] at h
    linarith
  apply hD.internalDiam_le_const_mul_of_local_comparison hE hEnonneg (Real.exp_pos B) A
  intro x hx
  obtain ⟨R, hR, hball⟩ := (hD.isOpen_iff (thickening δ A)).mp isOpen_thickening x hx
  apply hD.weylScaling_local_edge_bound hnonneg hzero hscale hR
  intro z hz
  exact hweight z (hball z hz)

/-- A Weyl bump yields the strict third pinch inequality when the original
strict margin and the comparison of sphere distances are available. -/
theorem IsEuclideanLengthMetric.pinchThirdEvent_of_weylScaling
    {D E : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hE : IsEuclideanLengthMetric E) (hEnonneg : ∀ x y, 0 ≤ E x y)
    {ξ B δ : ℝ} {f : ℂ → ℝ} (V W : Set ℂ)
    (hzero : ∀ x y, weylScaling D ξ 0 x y = ENNReal.ofReal (D x y))
    (hscale : ∀ x y, ENNReal.ofReal (E x y) = weylScaling D ξ f x y)
    (hweight : ∀ z ∈ thickening δ (thickening (3 * δ) W \ V), ξ * f z ≤ B)
    (hgap : ENNReal.ofReal (setDist D (sphere 0 (2 * δ)) (sphere 0 (3 * δ))) ≤
      ENNReal.ofReal (setDist E (sphere 0 (2 * δ)) (sphere 0 (3 * δ))))
    (hstrict : ENNReal.ofReal (Real.exp B) * internalDiam D δ (thickening (3 * δ) W \ V) <
      ENNReal.ofReal (setDist D (sphere 0 (2 * δ)) (sphere 0 (3 * δ)))) :
    pinchThirdEvent E V W δ := by
  exact (hD.internalDiam_weylScaling_le hE hEnonneg _ hzero hscale hweight).trans_lt
    (hstrict.trans_le hgap)

end HarmonicBalls

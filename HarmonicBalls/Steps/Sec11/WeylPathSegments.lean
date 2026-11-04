import HarmonicBalls.Steps.Sec11.WeylPathConcatenation

/-! # Weyl costs of curve segments

A subcurve of a length-parametrized curve is length-parametrized after
translation. Its weighted integral bounds the Weyl distance of its endpoints.
-/

namespace HarmonicBalls

open MeasureTheory Set
open scoped ENNReal

/-- Translating a subinterval to start at zero preserves length
parametrization. -/
theorem IsEuclideanLengthMetric.isLengthParametrized_subcurve
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {p : ℝ → ℂ} {T a b : ℝ} (hp : IsLengthParametrized D p T)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T) :
    IsLengthParametrized D (fun t => p (a + t)) (b - a) := by
  refine ⟨sub_nonneg.mpr hab, ?_, ?_⟩
  · apply hp.2.1.comp (continuous_const.add continuous_id).continuousOn
    intro t ht
    change 0 ≤ a + t ∧ a + t ≤ T
    constructor <;> linarith [ht.1, ht.2]
  · intro s t hs hst ht
    have heq : (fun t : ℝ => p (a + t)) = fun t => p (t - (-a)) := by
      funext t
      congr 1
      ring
    rw [heq, hD.curveLength_translate]
    have h := hp.2.2 (s - -a) (t - -a) (by linarith) (by linarith) (by linarith)
    rw [h]
    congr 1
    ring

/-- The Weyl distance between two points on a length-parametrized curve is at
most the weighted cost of the intervening segment. -/
theorem IsEuclideanLengthMetric.weylScaling_le_segment_cost
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (ξ : ℝ) (f : ℂ → ℝ) {p : ℝ → ℂ} {T a b : ℝ}
    (hp : IsLengthParametrized D p T) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T) :
    weylScaling D ξ f (p a) (p b) ≤
      ∫⁻ t in Icc a b, ENNReal.ofReal (Real.exp (ξ * f (p t))) := by
  have hsub := hD.isLengthParametrized_subcurve hp ha hab hb
  have hstart : (fun t => p (a + t)) 0 = p a := by simp
  have hend : (fun t => p (a + t)) (b - a) = p b := by
    ring
  calc
    _ ≤ ∫⁻ t in Icc (0 : ℝ) (b - a),
        ENNReal.ofReal (Real.exp (ξ * f (p (a + t)))) :=
      (iInf₂_le (b - a) (fun t => p (a + t))).trans
        ((iInf₂_le hsub hstart).trans (iInf_le _ hend))
    _ = _ := by
      have h := lintegral_Icc_translate
        (fun t => ENNReal.ofReal (Real.exp (ξ * f (p (a + t))))) a (b - a)
      have h₁ : a + (b - a) = b := by ring
      have h₂ (t : ℝ) : a + (t - a) = t := by ring
      simpa only [h₁, h₂] using h.symm

/-- Weighted costs over successive subintervals add, even for a
nonmeasurable integrand. -/
theorem sum_lintegral_Icc_adjacent (F : ℝ → ℝ≥0∞) (u : ℕ → ℝ)
    (hu : Monotone u) (n : ℕ) :
    (∑ i ∈ Finset.range n, ∫⁻ t in Icc (u i) (u (i + 1)), F t) =
      ∫⁻ t in Icc (u 0) (u n), F t := by
  have hinterval (a b : ℝ) :
      (∫⁻ t in Icc a b, F t) = ∫⁻ t in Ioc a b, F t := by
    rw [Measure.restrict_congr_set (Ioc_ae_eq_Icc (μ := volume))]
  simp_rw [hinterval]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have hsplit := lintegral_union (μ := volume) (f := F) measurableSet_Ioc
      (Ioc_disjoint_Ioc_of_le (le_refl (u n)) :
        Disjoint (Ioc (u 0) (u n)) (Ioc (u n) (u (n + 1))))
    rw [Ioc_union_Ioc_eq_Ioc (hu (Nat.zero_le n)) (hu (Nat.le_succ n))] at hsplit
    exact hsplit.symm

/-- A length-parametrized curve has shifted length bounded by its Weyl cost. -/
theorem IsEuclideanLengthMetric.curveLength_weyl_le_cost
    {D E : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (ξ : ℝ) (f : ℂ → ℝ)
    (hE : ∀ x y, ENNReal.ofReal (E x y) = weylScaling D ξ f x y)
    (hEsymm : ∀ x y, E x y = E y x)
    {p : ℝ → ℂ} {T : ℝ} (hp : IsLengthParametrized D p T) :
    curveLength E p 0 T ≤ ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * f (p t))) := by
  unfold curveLength
  refine iSup_le fun q => ?_
  let F : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (Real.exp (ξ * f (p t)))
  have hedge (i : ℕ) :
      ENNReal.ofReal (E (p (q.2.1 (i + 1))) (p (q.2.1 i))) ≤
        ∫⁻ t in Icc (q.2.1 i) (q.2.1 (i + 1)), F t := by
    rw [hEsymm, hE]
    exact hD.weylScaling_le_segment_cost ξ f hp (q.2.2.2 i).1
      (q.2.2.1 (Nat.le_succ i)) (q.2.2.2 (i + 1)).2
  calc
    _ ≤ ∑ i ∈ Finset.range q.1, ∫⁻ t in Icc (q.2.1 i) (q.2.1 (i + 1)), F t :=
      Finset.sum_le_sum fun i _ => hedge i
    _ = ∫⁻ t in Icc (q.2.1 0) (q.2.1 q.1), F t :=
      sum_lintegral_Icc_adjacent F q.2.1 q.2.2.1 q.1
    _ ≤ ∫⁻ t in Icc 0 T, F t :=
      lintegral_mono' (Measure.restrict_mono_set volume (Icc_subset_Icc
        (q.2.2.2 0).1 (q.2.2.2 q.1).2)) le_rfl

/-- A continuous curve on a finite interval gives a unit-interval path whose
length is bounded by the length of the original curve. -/
theorem exists_path_pathLength_le_curveLength
    {E : ℂ → ℂ → ℝ} {p : ℝ → ℂ} {T : ℝ}
    (hT : 0 ≤ T) (hp : ContinuousOn p (Icc 0 T)) :
    ∃ P : Path (p 0) (p T), pathLength E P ≤ curveLength E p 0 T := by
  have hcont : Continuous (fun t : Set.Icc (0 : ℝ) 1 => p (T * (t : ℝ))) := by
    apply hp.comp_continuous (continuous_const.mul continuous_subtype_val)
    intro t
    change 0 ≤ T * (t : ℝ) ∧ T * (t : ℝ) ≤ T
    constructor
    · exact mul_nonneg hT t.2.1
    · nlinarith [t.2.2]
  let P : Path (p 0) (p T) := {
    toFun := fun t => p (T * (t : ℝ))
    continuous_toFun := hcont
    source' := by simp
    target' := by simp }
  refine ⟨P, ?_⟩
  unfold pathLength curveLength
  refine iSup_le fun q => ?_
  let u : ℕ → ℝ := fun i => T * q.2.1 i
  have hu : Monotone u := fun i j hij => mul_le_mul_of_nonneg_left (q.2.2.1 hij) hT
  have humem : ∀ i, u i ∈ Icc (0 : ℝ) T := by
    intro i
    constructor
    · exact mul_nonneg hT (q.2.2.2 i).1
    · have h := (q.2.2.2 i).2
      dsimp [u]
      nlinarith
  have hle := le_iSup (fun r : ℕ × {v : ℕ → ℝ // Monotone v ∧ ∀ i, v i ∈ Icc 0 T} =>
    ∑ i ∈ Finset.range r.1, ENNReal.ofReal (E (p (r.2.1 (i + 1))) (p (r.2.1 i))))
      ⟨q.1, ⟨u, hu, humem⟩⟩
  apply le_trans ?_ hle
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro i hi
  simp only [u, P, Path.extend_apply _ (q.2.2.2 (i + 1)),
    Path.extend_apply _ (q.2.2.2 i)]
  rfl

/-- The internal distance of a shifted metric is at most its Weyl distance. -/
theorem IsEuclideanLengthMetric.internalMetric_le_weylScaling
    {D E : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (ξ : ℝ) (f : ℂ → ℝ)
    (hE : ∀ x y, ENNReal.ofReal (E x y) = weylScaling D ξ f x y)
    (hEsymm : ∀ x y, E x y = E y x) (x y : ℂ) :
    internalMetric E univ x y ≤ weylScaling D ξ f x y := by
  unfold weylScaling
  refine le_iInf fun T => le_iInf fun p => le_iInf fun hp => le_iInf fun hp0 =>
    le_iInf fun hpT => ?_
  obtain ⟨P, hP⟩ := exists_path_pathLength_le_curveLength (E := E) hp.1 hp.2.1
  have hbound := hD.curveLength_weyl_le_cost ξ f hE hEsymm hp
  subst x
  subst y
  exact (iInf_le_of_le P (iInf_le _ (fun _ => mem_univ _))).trans (hP.trans hbound)

/-- The length of a path dominates the symmetric distance of its endpoints. -/
theorem ofReal_le_pathLength_of_symm {E : ℂ → ℂ → ℝ}
    (hEsymm : ∀ x y, E x y = E y x) {x y : ℂ} (P : Path x y) :
    ENNReal.ofReal (E x y) ≤ pathLength E P := by
  let u : ℕ → ℝ := fun n => if n = 0 then 0 else 1
  have hu : Monotone u := by
    apply monotone_nat_of_le_succ
    intro n
    rcases n with _ | n <;> simp [u]
  have humem : ∀ n, u n ∈ Icc (0 : ℝ) 1 := by
    intro n
    rcases n with _ | n <;> simp [u]
  have h := le_iSup (fun q : ℕ × {u : ℕ → ℝ // Monotone u ∧ ∀ i, u i ∈ Icc 0 1} =>
    ∑ i ∈ Finset.range q.1, ENNReal.ofReal (E (P.extend (q.2.1 (i + 1)))
      (P.extend (q.2.1 i)))) ⟨1, ⟨u, hu, humem⟩⟩
  change _ ≤ pathLength E P at h
  simpa [u, hEsymm] using h

/-- If a symmetric real distance represents a Weyl scaling, its internal
distance on the plane equals that distance. -/
theorem IsEuclideanLengthMetric.weylScaling_internalMetric
    {D E : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (ξ : ℝ) (f : ℂ → ℝ)
    (hE : ∀ x y, ENNReal.ofReal (E x y) = weylScaling D ξ f x y)
    (hEsymm : ∀ x y, E x y = E y x) (x y : ℂ) :
    ENNReal.ofReal (E x y) = internalMetric E univ x y := by
  apply le_antisymm
  · refine le_iInf fun P => le_iInf fun _ => ?_
    exact ofReal_le_pathLength_of_symm hEsymm P
  · rw [hE]
    exact hD.internalMetric_le_weylScaling ξ f hE hEsymm x y

end HarmonicBalls

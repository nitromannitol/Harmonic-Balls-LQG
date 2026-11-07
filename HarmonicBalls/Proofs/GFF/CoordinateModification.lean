import HarmonicBalls.Defs.GFF

/-! # Coordinatewise modifications of the whole-plane GFF

The related distribution-valued construction is due to Leonardo Bonanno.
Coordinatewise agreement alone does not assert a common samplewise representation. -/

noncomputable section
open MeasureTheory ProbabilityTheory
namespace HarmonicBalls

/-- A measurable coordinatewise modification preserves all six fields of the
whole-plane GFF specification, with circle averages unchanged. -/
theorem IsWholePlaneGFF.coordinateModification
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC hC' : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc)
    (hm : ∀ φ, IsTestFunction Set.univ φ → Measurable fun ω => hC' ω φ)
    (he : ∀ φ, IsTestFunction Set.univ φ → (fun ω => hC ω φ) =ᵐ[P] (fun ω => hC' ω φ)) :
    IsWholePlaneGFF P hC' hcirc := by
  have heval (o : GFFObservable) (ho : o.IsAdmissible) :
      (fun ω => o.eval (hC ω) (hcirc ω)) =ᵐ[P]
        (fun ω => o.eval (hC' ω) (hcirc ω)) := by
    cases o with
    | pairing φ => exact he φ ho
    | circle r z => exact Filter.Eventually.of_forall (fun _ => rfl)
  refine ⟨hm, hh.measurable_circle, hh.isGaussianProcess.congr (fun o => heval o.1 o.2), ?_, ?_, hh.ae_continuousOn_circle⟩
  · intro o ho
    rw [← integral_congr_ae (heval o ho)]
    exact hh.integral_eq_zero o ho
  · intro o o' ho ho'
    have h₁ := heval o ho
    have h₂ := heval o' ho'
    have hi₁ := integral_congr_ae h₁
    have hi₂ := integral_congr_ae h₂
    calc
      cov[fun ω => o.eval (hC' ω) (hcirc ω), fun ω => o'.eval (hC' ω) (hcirc ω); P] =
          cov[fun ω => o.eval (hC ω) (hcirc ω), fun ω => o'.eval (hC ω) (hcirc ω); P] := by
            unfold ProbabilityTheory.covariance
            apply integral_congr_ae
            filter_upwards [h₁, h₂] with ω hω hω'
            rw [← hω, ← hω', ← hi₁, ← hi₂]
      _ = wholePlaneGFFCov o o' := hh.covariance_eq o o' ho ho'

/-- Pulling back a whole-plane GFF through a measure-preserving map preserves
its complete joint specification. -/
theorem IsWholePlaneGFF.comp_measurePreserving
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {f : Ω' → Ω}
    (hf : MeasurePreserving f P' P) :
    IsWholePlaneGFF P' (fun ω => hC (f ω)) (fun ω => hcirc (f ω)) := by
  have hm (o : GFFObservable) (ho : o.IsAdmissible) :
      Measurable (fun ω => o.eval (hC ω) (hcirc ω)) := by
    cases o with
    | pairing φ => exact hh.measurable_pairing φ ho
    | circle r z => exact hh.measurable_circle r z ho
  refine ⟨fun φ hφ => (hh.measurable_pairing φ hφ).comp hf.measurable,
    fun r z hr => (hh.measurable_circle r z hr).comp hf.measurable, ?_, ?_, ?_, ?_⟩
  · constructor
    intro I
    let X := fun ω (i : I) => i.1.1.eval (hC ω) (hcirc ω)
    have hX : Measurable X := measurable_pi_iff.mpr (fun i => hm i.1.1 i.1.2)
    have hG := hh.isGaussianProcess.hasGaussianLaw I
    have hmap : P'.map (X ∘ f) = P.map X := by
      rw [← Measure.map_map hX hf.measurable, hf.map_eq]
    exact ⟨(hX.comp hf.measurable).aemeasurable, hmap ▸ hG.isGaussian_map⟩
  · intro o ho
    have hi := integral_map hf.measurable.aemeasurable (f := fun ω => o.eval (hC ω) (hcirc ω))
      (by rw [hf.map_eq]; exact (hm o ho).aestronglyMeasurable)
    rw [hf.map_eq] at hi
    exact hi.symm.trans (hh.integral_eq_zero o ho)
  · intro o o' ho ho'
    have hc := covariance_map_fun (μ := P') (Z := f)
      (by rw [hf.map_eq]; exact (hm o ho).aestronglyMeasurable)
      (by rw [hf.map_eq]; exact (hm o' ho').aestronglyMeasurable)
      hf.measurable.aemeasurable
    rw [hf.map_eq] at hc
    exact hc.symm.trans (hh.covariance_eq o o' ho ho')
  · exact hf.quasiMeasurePreserving.ae hh.ae_continuousOn_circle

/-- A diagonal spike has measurable sections and vanishes almost surely at
    each fixed index when its parameter has no atoms. -/
theorem diagonalSpike_sections
    {Ω I : Type*} [MeasurableSpace Ω] [DecidableEq I] {P : Measure Ω}
    (t : Ω → ℝ) (ht : Measurable t)
    (hnull : ∀ r, ∀ᵐ ω ∂P, t ω ≠ r)
    (a : ℝ → I) (ha : Function.Injective a) :
    (∀ i, Measurable (fun ω => if i = a (t ω) then (1 : ℝ) else 0)) ∧
    (∀ i, ∀ᵐ ω ∂P, (if i = a (t ω) then (1 : ℝ) else 0) = 0) := by
  classical
  have hsection (i : I) : MeasurableSet {ω | i = a (t ω)} := by
    by_cases hi : ∃ r, i = a r
    · obtain ⟨r, rfl⟩ := hi
      have heq : {ω | a r = a (t ω)} = {ω | t ω = r} := by
        ext ω
        simp only [Set.mem_ofPred_eq]
        constructor
        · intro h
          exact (ha h).symm
        · intro h
          rw [h]
      rw [heq]
      exact measurableSet_eq_fun ht measurable_const
    · have hempty : {ω | i = a (t ω)} = ∅ := by
        ext ω
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        exact fun h => hi ⟨t ω, h⟩
      rw [hempty]
      exact MeasurableSet.empty
  constructor
  · intro i
    exact Measurable.ite (hsection i) measurable_const measurable_const
  · intro i
    by_cases hi : ∃ r, i = a r
    · obtain ⟨r, rfl⟩ := hi
      filter_upwards [hnull r] with ω hω
      have hne : a r ≠ a (t ω) := fun h => hω (ha h).symm
      simp only [hne, ↓reduceIte]
    · filter_upwards with ω
      have hne : i ≠ a (t ω) := fun h => hi ⟨t ω, h⟩
      simp only [hne, ↓reduceIte]

/-- On any GFF probability space carrying a diffuse parameter, the diagonal
modification retains the full GFF specification. If the original pairings
obey the indicated scalar relation, the modified pairings violate it almost
surely. Instantiating this conditional result requires a suitable joint GFF. -/
theorem IsWholePlaneGFF.exists_diagonal_modification
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc)
    (t : Ω → ℝ) (ht : Measurable t)
    (hnull : ∀ r, ∀ᵐ ω ∂P, t ω ≠ r)
    (a : ℝ → (ℂ → ℝ)) (ha : Function.Injective a)
    (hlinear : ∀ᵐ ω ∂P, hC ω (a (2 * t ω)) = 2 * hC ω (a (t ω))) :
    ∃ hC' : Ω → (ℂ → ℝ) → ℝ, IsWholePlaneGFF P hC' hcirc ∧
      (∀ φ, (fun ω => hC ω φ) =ᵐ[P] (fun ω => hC' ω φ)) ∧
      ∀ᵐ ω ∂P, hC' ω (a (2 * t ω)) ≠ 2 * hC' ω (a (t ω)) := by
  classical
  let D : Ω → (ℂ → ℝ) → ℝ := fun ω φ => if φ = a (t ω) then 1 else 0
  have hd := diagonalSpike_sections t ht hnull a ha
  let hC' := fun ω φ => hC ω φ + D ω φ
  have he (φ : ℂ → ℝ) : (fun ω => hC ω φ) =ᵐ[P] (fun ω => hC' ω φ) := by
    filter_upwards [hd.2 φ] with ω hω
    simp only [hC', D, hω, add_zero]
  refine ⟨hC', hh.coordinateModification (fun φ hφ => (hh.measurable_pairing φ hφ).add (hd.1 φ))
    (fun φ _ => he φ), he, ?_⟩
  filter_upwards [hlinear, hnull 0] with ω hl hn
  have hne : a (2 * t ω) ≠ a (t ω) := by
    intro h
    have hhzero : t ω = 0 := by
      have hhcoef := ha h
      linarith
    exact hn hhzero
  change hC ω (a (2 * t ω)) + D ω (a (2 * t ω)) ≠
    2 * (hC ω (a (t ω)) + D ω (a (t ω)))
  simp only [D, hne, ↓reduceIte, add_zero]
  linarith

/-- A diagonal modification can be chosen to violate scalar linearity at
    almost every sample, without any regularity assumption on the starting
    pairings. The curve must consist of admissible test functions. -/
theorem IsWholePlaneGFF.exists_ae_non_linear_modification
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc)
    (t : Ω → ℝ) (ht : Measurable t)
    (hnull : ∀ r, ∀ᵐ ω ∂P, t ω ≠ r)
    (a : ℝ → (ℂ → ℝ)) (ha : Function.Injective a)
    (hat : ∀ r, IsTestFunction Set.univ (a r)) :
    ∃ hC' : Ω → (ℂ → ℝ) → ℝ, IsWholePlaneGFF P hC' hcirc ∧
      (∀ φ, (fun ω => hC ω φ) =ᵐ[P] (fun ω => hC' ω φ)) ∧
      ∀ᵐ ω ∂P, hC' ω (a (2 * t ω)) ≠ 2 * hC' ω (a (t ω)) := by
  classical
  let D : Ω → (ℂ → ℝ) → ℝ := fun ω φ =>
    if φ = a (t ω) then
      if hC ω (a (2 * t ω)) = 2 * hC ω φ + 2 then 2 else 1
    else 0
  have hd := diagonalSpike_sections t ht hnull a ha
  have hm (φ : ℂ → ℝ) : Measurable (fun ω => D ω φ) := by
    by_cases hφ : ∃ r, φ = a r
    · obtain ⟨r, rfl⟩ := hφ
      have heq : (fun ω => D ω (a r)) = fun ω =>
          if t ω = r then
            if hC ω (a (2 * r)) = 2 * hC ω (a r) + 2 then 2 else 1
          else 0 := by
        funext ω
        by_cases htr : t ω = r
        · subst r
          simp only [D, ↓reduceIte]
        · have hne : a r ≠ a (t ω) := fun h => htr (ha h).symm
          simp only [D, hne, htr, ↓reduceIte]
      rw [heq]
      apply Measurable.ite (measurableSet_eq_fun ht measurable_const)
      · exact Measurable.ite (measurableSet_eq_fun (hh.measurable_pairing _ (hat (2 * r)))
          (((hh.measurable_pairing _ (hat r)).const_mul 2).add_const 2)) measurable_const measurable_const
      · exact measurable_const
    · have heq : (fun ω => D ω φ) = fun _ => 0 := by
        funext ω
        have hne : φ ≠ a (t ω) := fun h => hφ ⟨t ω, h⟩
        simp only [D, hne, ↓reduceIte]
      rw [heq]
      exact measurable_const
  let hC' := fun ω φ => hC ω φ + D ω φ
  have he (φ : ℂ → ℝ) : (fun ω => hC ω φ) =ᵐ[P] (fun ω => hC' ω φ) := by
    filter_upwards [hd.2 φ] with ω hω
    have hne : φ ≠ a (t ω) := by
      intro h
      simp only [h, ↓reduceIte, one_ne_zero] at hω
    simp only [hC', D, hne, ↓reduceIte, add_zero]
  refine ⟨hC', hh.coordinateModification (fun φ hφ => (hh.measurable_pairing φ hφ).add (hm φ))
    (fun φ _ => he φ), he, ?_⟩
  filter_upwards [hnull 0] with ω hn
  have hne : a (2 * t ω) ≠ a (t ω) := by
    intro h
    have hhzero : t ω = 0 := by
      have hhcoef := ha h
      linarith
    exact hn hhzero
  change hC ω (a (2 * t ω)) + D ω (a (2 * t ω)) ≠
    2 * (hC ω (a (t ω)) + D ω (a (t ω)))
  simp only [D, hne, ↓reduceIte, add_zero]
  split_ifs with h
  · linarith
  · intro heq
    apply h
    linarith

/-- Given a diffuse parameter on a GFF probability space, some coordinatewise
modification has no common event of linearity along the specified curve. This
requires no samplewise regularity of the original pairings. -/
theorem IsWholePlaneGFF.exists_modification_not_ae_linear
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc)
    (t : Ω → ℝ) (ht : Measurable t)
    (hnull : ∀ r, ∀ᵐ ω ∂P, t ω ≠ r)
    (a : ℝ → (ℂ → ℝ)) (ha : Function.Injective a) :
    ∃ hC' : Ω → (ℂ → ℝ) → ℝ, IsWholePlaneGFF P hC' hcirc ∧
      (∀ φ, (fun ω => hC ω φ) =ᵐ[P] (fun ω => hC' ω φ)) ∧
      ¬ (∀ᵐ ω ∂P, ∀ r, hC' ω (a (2 * r)) = 2 * hC' ω (a r)) := by
  classical
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  by_cases hl : ∀ᵐ ω ∂P, ∀ r, hC ω (a (2 * r)) = 2 * hC ω (a r)
  · have hl' : ∀ᵐ ω ∂P, hC ω (a (2 * t ω)) = 2 * hC ω (a (t ω)) := by
      filter_upwards [hl] with ω hω
      exact hω (t ω)
    obtain ⟨hC', hG, he, hn⟩ := hh.exists_diagonal_modification t ht hnull a ha hl'
    refine ⟨hC', hG, he, ?_⟩
    intro hc
    have hf : ∀ᵐ ω ∂P, False := by
      filter_upwards [hc, hn] with ω hω hne
      exact hne (hω (t ω))
    obtain ⟨_, hfalse⟩ := Filter.Eventually.exists hf
    exact hfalse
  · exact ⟨hC, hh, fun _ => Filter.Eventually.of_forall (fun _ => rfl), hl⟩

/-- Every whole-plane GFF admits a product extension with an equal-in-law
coordinatewise modification whose test-function pairings lack a common
samplewise scalar-linearity event. -/
theorem IsWholePlaneGFF.product_has_non_linear_modification
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) :
    ∃ hC' : Ω × ℝ → (ℂ → ℝ) → ℝ,
      IsWholePlaneGFF (P.prod (gaussianReal 0 1)) hC' (fun p => hcirc p.1) ∧
      (∀ φ, (fun p : Ω × ℝ => hC p.1 φ) =ᵐ[P.prod (gaussianReal 0 1)] (fun p => hC' p φ)) ∧
      ¬ (∀ᵐ p ∂P.prod (gaussianReal 0 1), ∀ φ, IsTestFunction Set.univ φ → ∀ c : ℝ,
          hC' p (fun z => c * φ z) = c * hC' p φ) := by
  classical
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  let : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  let Q := P.prod (gaussianReal 0 1)
  have hp : IsWholePlaneGFF Q (fun p => hC p.1) (fun p => hcirc p.1) :=
    hh.comp_measurePreserving measurePreserving_fst
  have ht : ∀ r : ℝ, ∀ᵐ p ∂Q, p.2 ≠ r := by
    intro r
    have hr : ∀ᵐ x ∂(gaussianReal 0 1), x ≠ r := by
      apply ae_iff.mpr
      simpa only [not_not, Set.ofPred_eq_eq_singleton] using (measure_singleton r : gaussianReal 0 1 {r} = 0)
    exact measurePreserving_snd.quasiMeasurePreserving.ae hr
  let b : ContDiffBump (0 : ℂ) := ⟨1, 2, by norm_num, by norm_num⟩
  have hb : b (0 : ℂ) = 1 := b.one_of_mem_closedBall (by simp [b])
  let a : ℝ → (ℂ → ℝ) := fun r z => r * b z
  have ha : Function.Injective a := by
    intro r s h
    have hz := congrFun h 0
    simpa only [a, hb, mul_one] using hz
  have htest (r : ℝ) : IsTestFunction Set.univ (a r) :=
    ⟨contDiff_const.mul b.contDiff, b.hasCompactSupport.mul_left, Set.subset_univ _⟩
  obtain ⟨hC', hG, he, hn⟩ := hp.exists_modification_not_ae_linear Prod.snd measurable_snd ht a ha
  refine ⟨hC', hG, he, ?_⟩
  intro hl
  apply hn
  filter_upwards [hl] with p hlin r
  have h := hlin (a r) (htest r) 2
  have heq : (fun z => (2 : ℝ) * a r z) = a (2 * r) := by
    funext z
    simp only [a]
    ring
  rw [heq] at h
  exact h

/-- Every whole-plane GFF admits a product extension and a coordinatewise
modification whose test pairings fail scalar linearity at almost every sample. -/
theorem IsWholePlaneGFF.product_has_ae_non_linear_modification
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) :
    ∃ hC' : Ω × ℝ → (ℂ → ℝ) → ℝ,
      IsWholePlaneGFF (P.prod (gaussianReal 0 1)) hC' (fun p => hcirc p.1) ∧
      (∀ φ, (fun p : Ω × ℝ => hC p.1 φ) =ᵐ[P.prod (gaussianReal 0 1)] (fun p => hC' p φ)) ∧
      ∀ᵐ p ∂P.prod (gaussianReal 0 1), ∃ φ, IsTestFunction Set.univ φ ∧
          hC' p (fun z => 2 * φ z) ≠ 2 * hC' p φ := by
  classical
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  let : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  let Q := P.prod (gaussianReal 0 1)
  have hp : IsWholePlaneGFF Q (fun p => hC p.1) (fun p => hcirc p.1) :=
    hh.comp_measurePreserving measurePreserving_fst
  have ht : ∀ r : ℝ, ∀ᵐ p ∂Q, p.2 ≠ r := by
    intro r
    have hr : ∀ᵐ x ∂(gaussianReal 0 1), x ≠ r := by
      apply ae_iff.mpr
      simpa only [not_not, Set.ofPred_eq_eq_singleton] using (measure_singleton r : gaussianReal 0 1 {r} = 0)
    exact measurePreserving_snd.quasiMeasurePreserving.ae hr
  let b : ContDiffBump (0 : ℂ) := ⟨1, 2, by norm_num, by norm_num⟩
  have hb : b (0 : ℂ) = 1 := b.one_of_mem_closedBall (by simp [b])
  let a : ℝ → (ℂ → ℝ) := fun r z => r * b z
  have ha : Function.Injective a := by
    intro r s h
    have hz := congrFun h 0
    simpa only [a, hb, mul_one] using hz
  have htest (r : ℝ) : IsTestFunction Set.univ (a r) :=
    ⟨contDiff_const.mul b.contDiff, b.hasCompactSupport.mul_left, Set.subset_univ _⟩
  obtain ⟨hC', hG, he, hn⟩ :=
    hp.exists_ae_non_linear_modification Prod.snd measurable_snd ht a ha htest
  refine ⟨hC', hG, he, ?_⟩
  filter_upwards [hn] with p hp
  refine ⟨a p.2, htest p.2, ?_⟩
  have heq : (fun z => (2 : ℝ) * a p.2 z) = a (2 * p.2) := by
    funext z
    simp only [a]
    ring
  rw [heq]
  exact hp

#print axioms IsWholePlaneGFF.product_has_ae_non_linear_modification
#print axioms IsWholePlaneGFF.exists_ae_non_linear_modification
#print axioms IsWholePlaneGFF.product_has_non_linear_modification
#print axioms IsWholePlaneGFF.comp_measurePreserving
#print axioms IsWholePlaneGFF.exists_modification_not_ae_linear
#print axioms IsWholePlaneGFF.exists_diagonal_modification
#print axioms IsWholePlaneGFF.coordinateModification
#print axioms diagonalSpike_sections
end HarmonicBalls

import HarmonicBalls.Proofs.GFF.MeasurableContinuousCircleVersion
import HarmonicBalls.Proofs.Sec9.CircleCovarianceAffine

/-! # Affine law of continuous circle-average profiles

The GFF and continuous circle-average construction used here are due to Leonardo Bonanno.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Topology
namespace HarmonicBalls

private instance : LocallyCompactSpace (Set.Ioi (0 : ℝ)) :=
  isOpen_Ioi.locallyCompactSpace

/-- Pull back positive-radius circles along a nonconstant complex affine map. -/
def affineCircleParameter (a b : ℂ) (ha : a ≠ 0) : C(CircleParameter, CircleParameter) where
  toFun p := (⟨‖a‖ * p.1, mul_pos (norm_pos_iff.mpr ha) p.1.2⟩, a * p.2 + b)
  continuous_toFun := by
    apply Continuous.prodMk
    · exact (continuous_const.mul (continuous_subtype_val.comp continuous_fst)).subtype_mk _
    · exact (continuous_const.mul continuous_snd).add continuous_const

/-- The affine pullback normalized at the unit circle. -/
def continuousCircleAffine (a b : ℂ) (ha : a ≠ 0)
    (f : C(CircleParameter, ℝ)) : C(CircleParameter, ℝ) :=
  f.comp (affineCircleParameter a b ha) -
    ContinuousMap.const CircleParameter (f (⟨‖a‖, norm_pos_iff.mpr ha⟩, b))

/-- The transformed profile vanishes on the unit circle for every sample. -/
theorem continuousCircleAffine_one_zero (a b : ℂ) (ha : a ≠ 0)
    (f : C(CircleParameter, ℝ)) :
    continuousCircleAffine a b ha f (⟨1, by simp⟩, 0) = 0 := by
  simp [continuousCircleAffine, affineCircleParameter]

/-- The normalized affine profile preserves measurability. -/
theorem measurable_continuousCircleAffine {Ω : Type*} [MeasurableSpace Ω]
    {F : Ω → C(CircleParameter, ℝ)} (hF : Measurable F)
    {a b : ℂ} (ha : a ≠ 0) : Measurable (fun ω => continuousCircleAffine a b ha (F ω)) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro p
  change Measurable (fun ω => F ω (affineCircleParameter a b ha p) -
    F ω (⟨‖a‖, norm_pos_iff.mpr ha⟩, b))
  exact ((ContinuousMap.measurable_eval _).comp hF).sub
    ((ContinuousMap.measurable_eval _).comp hF)

/-- Equality in law of all evaluations determines the law of a continuous profile. -/
theorem identDistrib_circle_map_of_evaluations
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {F G : Ω → C(CircleParameter, ℝ)} (hF : Measurable F) (hG : Measurable G)
    (h : IdentDistrib (fun ω p => F ω p) (fun ω p => G ω p) P P) :
    IdentDistrib F G P P := by
  refine ⟨hF.aemeasurable, hG.aemeasurable, ?_⟩
  ext s hs
  have hspace : (inferInstance : MeasurableSpace C(CircleParameter, ℝ)) =
      MeasurableSpace.comap (fun f : C(CircleParameter, ℝ) => (f : CircleParameter → ℝ)) inferInstance := by
    rw [ContinuousMap.measurableSpace_eq_iSup_comap_eval]
    simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
    rfl
  have hs' : @MeasurableSet _ (MeasurableSpace.comap
      (fun f : C(CircleParameter, ℝ) => (f : CircleParameter → ℝ)) inferInstance) s :=
    hspace ▸ hs
  obtain ⟨t, ht, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs'
  rw [Measure.map_apply hF (measurableSet_preimage (Measurable.of_eval fun p => ContinuousMap.measurable_eval p) ht),
    Measure.map_apply hG (measurableSet_preimage (Measurable.of_eval fun p => ContinuousMap.measurable_eval p) ht)]
  exact h.measure_preimage_eq ht

/-- Leonardo Bonanno's normalized measurable circle version has the full affine law. -/
theorem IsWholePlaneGFF.identDistrib_continuousCircleAffine
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) {F : Ω → C(CircleParameter, ℝ)}
    (hF : Measurable F)
    (hversion : ∀ p : CircleParameter, (fun ω => F ω p) =ᵐ[P] fun ω => hcirc ω p.1 p.2)
    {a : ℂ} (ha : a ≠ 0) (b : ℂ) :
    IdentDistrib (fun ω => continuousCircleAffine a b ha (F ω)) F P P := by
  apply identDistrib_circle_map_of_evaluations (measurable_continuousCircleAffine hF ha) hF
  let : IsProbabilityMeasure P := h.isProbabilityMeasure
  apply (identDistrib_iff_forall_finset_identDistrib
    (Measurable.of_eval fun p => (ContinuousMap.measurable_eval p).comp
      (measurable_continuousCircleAffine hF ha)).aemeasurable
    (Measurable.of_eval fun p => (ContinuousMap.measurable_eval p).comp hF).aemeasurable).2
  intro I
  have hd := h.identDistrib_circle_family_complex_affine
    (fun i : I => (i.val.1 : ℝ)) (fun i : I => i.val.2)
    (fun i => i.val.1.2) ha b
  have he₁ : (fun ω (i : I) => continuousCircleAffine a b ha (F ω) i.val) =ᵐ[P]
      (fun ω (i : I) => hcirc ω (‖a‖ * i.val.1) (a * i.val.2 + b) - hcirc ω ‖a‖ b) := by
    have he : ∀ᵐ ω ∂P, ∀ i : I,
        F ω (affineCircleParameter a b ha i.val) =
          hcirc ω (‖a‖ * i.val.1) (a * i.val.2 + b) := by
      apply ae_all_iff.mpr
      intro i
      exact hversion _
    filter_upwards [he, hversion (⟨‖a‖, norm_pos_iff.mpr ha⟩, b)] with ω hω hb
    funext i
    change F ω (affineCircleParameter a b ha i.val) - F ω _ = _
    rw [hω i, hb]
  have he₂ : (fun ω (i : I) => F ω i.val) =ᵐ[P]
      (fun ω (i : I) => hcirc ω i.val.1 i.val.2) := by
    filter_upwards [ae_all_iff.mpr (fun i : I => hversion i.val)] with ω hω
    exact funext hω
  exact (IdentDistrib.of_ae_eq
    (Measurable.of_eval fun i : I => (ContinuousMap.measurable_eval i.val).comp
      (measurable_continuousCircleAffine hF ha)).aemeasurable he₁).trans
      (hd.trans (IdentDistrib.of_ae_eq
        (Measurable.of_eval fun i : I => (ContinuousMap.measurable_eval i.val).comp hF).aemeasurable
        he₂).symm)

/-- Every indexed family of evaluations of the affine profile has the same joint law. -/
theorem IsWholePlaneGFF.identDistrib_continuousCircleAffine_family
    {ι Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) {F : Ω → C(CircleParameter, ℝ)}
    (hF : Measurable F)
    (hversion : ∀ p : CircleParameter, (fun ω => F ω p) =ᵐ[P] fun ω => hcirc ω p.1 p.2)
    {a : ℂ} (ha : a ≠ 0) (b : ℂ) (p : ι → CircleParameter) :
    IdentDistrib (fun ω i => continuousCircleAffine a b ha (F ω) (p i))
      (fun ω i => F ω (p i)) P P := by
  exact (h.identDistrib_continuousCircleAffine hF hversion ha b).comp
    (Measurable.of_eval fun i => ContinuousMap.measurable_eval (p i))

#print axioms affineCircleParameter
#print axioms continuousCircleAffine
#print axioms continuousCircleAffine_one_zero
#print axioms measurable_continuousCircleAffine
#print axioms identDistrib_circle_map_of_evaluations
#print axioms IsWholePlaneGFF.identDistrib_continuousCircleAffine
#print axioms IsWholePlaneGFF.identDistrib_continuousCircleAffine_family

end HarmonicBalls

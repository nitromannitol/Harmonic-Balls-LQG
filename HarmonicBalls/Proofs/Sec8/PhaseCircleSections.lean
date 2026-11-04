import HarmonicBalls.Proofs.Sec8.PhaseTorus

/-! # Circle sections of a joint invariant event

Doubling the circle loses its dyadic digits. An invariant event for a joint
circle/field transformation therefore has circle sections that are almost
surely empty or full, without any hypothesis on the second transformation.
-/

open MeasureTheory Filter Set Function
open scoped Topology Pointwise ENNReal

namespace HarmonicBalls

/-- The dyadic translations that disappear after the corresponding number of
circle doublings. -/
noncomputable def dyadicCircleTranslation (j : ℕ) : PhaseCircle :=
  (((1 : ℝ) / (2 : ℝ) ^ j : ℝ) : PhaseCircle)

/-- A dyadic translation has the expected additive order. -/
theorem addOrderOf_dyadicCircleTranslation (j : ℕ) :
    addOrderOf (dyadicCircleTranslation j) = 2 ^ j := by
  convert! AddCircle.addOrderOf_div_of_gcd_eq_one (p := (1 : ℝ)) (m := 1)
    (pow_pos (by norm_num : 0 < 2) j) (Nat.gcd_one_left _) using 1
  simp [dyadicCircleTranslation]

/-- The corresponding iterate of doubling kills a dyadic translation. -/
theorem nsmul_dyadicCircleTranslation (j : ℕ) :
    (2 ^ j : ℕ) • dyadicCircleTranslation j = 0 := by
  rw [← addOrderOf_dyadicCircleTranslation]
  exact addOrderOf_nsmul_eq_zero _

/-- Iterating joint circle doubling acts by `2 ^ j` on the first coordinate. -/
theorem iterate_circleDouble_prod {Ξ : Type*} (f : Ξ → Ξ) (j : ℕ)
    (x : PhaseCircle) (y : Ξ) :
    (Prod.map (fun t : PhaseCircle => (2 : ℕ) • t) f)^[j] (x, y) =
      ((2 ^ j : ℕ) • x, f^[j] y) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
    simp only [Prod.map_apply, smul_smul, pow_succ]
    rw [Nat.mul_comm]

/-- Circle sections of an invariant measurable event are almost everywhere
empty or full, even for an arbitrary map on the second coordinate. -/
theorem circle_section_ae_empty_or_univ_of_joint_invariant
    {Ξ : Type*} [MeasurableSpace Ξ] (f : Ξ → Ξ)
    (s : Set (PhaseCircle × Ξ)) (hs : MeasurableSet s)
    (hinv : (Prod.map (fun t : PhaseCircle => (2 : ℕ) • t) f) ⁻¹' s = s)
    (y : Ξ) :
    {x : PhaseCircle | (x, y) ∈ s} =ᵐ[volume] ∅ ∨
      {x : PhaseCircle | (x, y) ∈ s} =ᵐ[volume] univ := by
  let A : Set PhaseCircle := {x | (x, y) ∈ s}
  have hA : MeasurableSet A := hs.preimage (measurable_id.prodMk measurable_const)
  have htrans (j : ℕ) : (dyadicCircleTranslation j +ᵥ A : Set PhaseCircle) = A := by
    have hpow := IsFixedPt.preimage_iterate hinv j
    have hpoint (x : PhaseCircle) : x ∈ A ↔ dyadicCircleTranslation j + x ∈ A := by
      have h1 := Set.ext_iff.mp hpow (x, y)
      have h2 := Set.ext_iff.mp hpow (dyadicCircleTranslation j + x, y)
      simp only [mem_preimage, iterate_circleDouble_prod] at h1 h2
      rw [smul_add, nsmul_dyadicCircleTranslation, zero_add] at h2
      exact h1.symm.trans h2
    ext x
    constructor
    · intro hx
      obtain ⟨z, hz, rfl⟩ := hx
      exact (hpoint z).mp hz
    · intro hx
      refine ⟨-dyadicCircleTranslation j + x, ?_, ?_⟩
      · apply (hpoint _).mpr
        simpa using hx
      · simp
  apply AddCircle.ae_empty_or_univ_of_forall_vadd_ae_eq_self (l := atTop) (u := dyadicCircleTranslation) hA.nullMeasurableSet
    (fun j => (htrans j).eventuallyEq)
  change Tendsto (fun j : ℕ => addOrderOf (dyadicCircleTranslation j)) atTop atTop
  simp_rw [addOrderOf_dyadicCircleTranslation]
  exact tendsto_pow_atTop_atTop_of_one_lt (show 1 < (2 : ℕ) by norm_num)

/-- An invariant event is almost everywhere a pullback from the second
coordinate. The representative is measurable under any s-finite second law. -/
theorem exists_ae_second_coordinate_of_joint_circle_invariant
    {Ξ : Type*} [MeasurableSpace Ξ] (P : Measure Ξ) [SFinite P] (f : Ξ → Ξ)
    (s : Set (PhaseCircle × Ξ)) (hs : MeasurableSet s)
    (hinv : (Prod.map (fun t : PhaseCircle => (2 : ℕ) • t) f) ⁻¹' s = s) :
    ∃ B : Set Ξ, MeasurableSet B ∧ s =ᵐ[(volume : Measure PhaseCircle).prod P] (univ ×ˢ B) := by
  let B : Set Ξ := {y | (volume : Measure PhaseCircle) {x | (x, y) ∈ s} = 1}
  have hB : MeasurableSet B :=
    (measurableSet_singleton (1 : ℝ≥0∞)).preimage (measurable_measure_prodMk_right hs)
  refine ⟨B, hB, ?_⟩
  have hEq : MeasurableSet {p : PhaseCircle × Ξ | p ∈ s ↔ p.2 ∈ B} :=
    hs.iff (hB.preimage measurable_snd)
  have hfib : ∀ y, ∀ᵐ x ∂(volume : Measure PhaseCircle), (x, y) ∈ s ↔ y ∈ B := by
    intro y
    let A : Set PhaseCircle := {x | (x, y) ∈ s}
    have hA : MeasurableSet A := hs.preimage (measurable_id.prodMk measurable_const)
    rcases circle_section_ae_empty_or_univ_of_joint_invariant f s hs hinv y with hzero | hfull
    · have hAz : (volume : Measure PhaseCircle) A = 0 := ae_eq_empty.mp hzero
      have hy : y ∉ B := by simp [B, A, hAz]
      filter_upwards [hzero] with x hx
      simpa [A, hy] using hx
    · have hAu : (volume : Measure PhaseCircle) A = 1 := by
        simpa using (ae_eq_univ_iff_measure_eq hA.nullMeasurableSet).mp hfull
      have hy : y ∈ B := hAu
      filter_upwards [hfull] with x hx
      simpa [A, hy] using hx
  have hprod : ∀ᵐ p ∂((volume : Measure PhaseCircle).prod P),
      p ∈ s ↔ p.2 ∈ B := by
    apply (Measure.ae_prod_iff_ae_ae hEq).2
    apply (Measure.ae_ae_comm hEq).2
    exact Filter.Eventually.of_forall hfib
  filter_upwards [hprod] with p hp
  simpa using hp

/-- Circle doubling remains ergodic when paired with any ergodic
measure-preserving transformation. -/
theorem ergodic_circleDouble_prod {Ξ : Type*} [MeasurableSpace Ξ]
    (P : Measure Ξ) [SFinite P] (f : Ξ → Ξ) (hf : Ergodic f P) :
    Ergodic (Prod.map (fun t : PhaseCircle => (2 : ℕ) • t) f)
      ((volume : Measure PhaseCircle).prod P) := by
  let T := Prod.map (fun t : PhaseCircle => (2 : ℕ) • t) f
  have hT : MeasurePreserving T ((volume : Measure PhaseCircle).prod P)
      ((volume : Measure PhaseCircle).prod P) :=
    (AddCircle.ergodic_nsmul (T := (1 : ℝ)) (n := 2) (by norm_num)).toMeasurePreserving.prod
      hf.toMeasurePreserving
  refine ⟨hT, ⟨?_⟩⟩
  intro s hs hinv
  obtain ⟨B, hB, hrep⟩ := exists_ae_second_coordinate_of_joint_circle_invariant P f s hs hinv
  have hpre := hT.quasiMeasurePreserving.preimage_ae_eq hrep
  have heq : ∀ᵐ p ∂((volume : Measure PhaseCircle).prod P), f p.2 ∈ B ↔ p.2 ∈ B := by
    filter_upwards [hrep, hpre] with p hp hp'
    have hs' : T p ∈ s ↔ p ∈ s := Set.ext_iff.mp hinv p
    have hp₁ : p ∈ s ↔ p.2 ∈ B := by
      simpa only [Set.mem_prod, mem_univ, true_and] using (iff_of_eq hp)
    have hp₂ : T p ∈ s ↔ (T p).2 ∈ B := by
      simpa only [Set.mem_preimage, Set.mem_prod, mem_univ, true_and] using (iff_of_eq hp')
    change T p ∈ s ↔ f p.2 ∈ B at hp₂
    exact hp₂.symm.trans (hs'.trans hp₁)
  have hmeas : MeasurableSet {y | f y ∈ B ↔ y ∈ B} :=
    (hB.preimage hf.measurable).iff hB
  have hinvB : f ⁻¹' B =ᵐ[P] B := by
    have hBi : ∀ᵐ y ∂P, f y ∈ B ↔ y ∈ B := by
      rw [← (measurePreserving_snd (μ := (volume : Measure PhaseCircle)) (ν := P)).map_eq,
        ae_map_iff measurable_snd.aemeasurable hmeas]
      exact heq
    filter_upwards [hBi] with y hy
    exact propext hy
  have hset : (univ ×ˢ B : Set (PhaseCircle × Ξ)) = Prod.snd ⁻¹' B := by
    ext p
    simp only [mem_prod, mem_univ, true_and, mem_preimage]
  rw [hset] at hrep
  have hproj : Measure.QuasiMeasurePreserving (Prod.snd : PhaseCircle × Ξ → Ξ)
      ((volume : Measure PhaseCircle).prod P) P := Measure.quasiMeasurePreserving_snd
  rcases hf.quasiErgodic.ae_empty_or_univ₀ hB.nullMeasurableSet hinvB with hzero | hfull
  · have hzero' := hproj.preimage_ae_eq hzero
    rw [eventuallyEmptyOrUniv_iff']
    left
    exact hrep.trans (by simpa only [preimage_empty] using hzero')
  · have hfull' := hproj.preimage_ae_eq hfull
    rw [eventuallyEmptyOrUniv_iff']
    right
    exact hrep.trans (by simpa only [preimage_univ] using hfull')

/-- The phase-torus doubling is jointly ergodic with every ergodic
measure-preserving transformation. -/
theorem ergodic_phaseTorusDouble_prod {Ξ : Type*} [MeasurableSpace Ξ]
    (P : Measure Ξ) [SFinite P] (f : Ξ → Ξ) (hf : Ergodic f P) :
    Ergodic (Prod.map phaseTorusDouble f)
      (((volume : Measure PhaseCircle).prod volume).prod P) := by
  let d : PhaseCircle → PhaseCircle := fun t => (2 : ℕ) • t
  have he : Ergodic (Prod.map d (Prod.map d f))
      ((volume : Measure PhaseCircle).prod ((volume : Measure PhaseCircle).prod P)) :=
    ergodic_circleDouble_prod _ _ (ergodic_circleDouble_prod P f hf)
  let e : (PhaseCircle × PhaseCircle) × Ξ ≃ᵐ PhaseCircle × (PhaseCircle × Ξ) :=
    MeasurableEquiv.prodAssoc
  have hp : MeasurePreserving e.symm
      ((volume : Measure PhaseCircle).prod ((volume : Measure PhaseCircle).prod P))
      (((volume : Measure PhaseCircle).prod volume).prod P) :=
    (measurePreserving_prodAssoc (volume : Measure PhaseCircle) volume P).symm e
  apply hp.ergodic_of_ergodic_semiconj he
    (measurePreserving_phaseTorusDouble.measurable.prodMap hf.measurable)
  intro p
  rfl

end HarmonicBalls

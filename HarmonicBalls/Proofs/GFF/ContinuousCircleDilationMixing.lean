import HarmonicBalls.Proofs.GFF.ContinuousCircleAffineLaw
import HarmonicBalls.Proofs.GFF.FullObservableDilationMixing
import HarmonicBalls.Proofs.MeasureTheory.CylinderMixingExtension
import Mathlib.Dynamics.Ergodic.Ergodic

/-! # Dilation of continuous circle profiles

The GFF and continuous circle-average construction used here are due to Leonardo Bonanno.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
namespace HarmonicBalls

private instance : LocallyCompactSpace (Set.Ioi (0 : ℝ)) :=
  isOpen_Ioi.locallyCompactSpace

/-- Unit-normalized pullback of a circle profile by the map `z ↦ z / 2`. -/
def continuousCircleDilation : C(CircleParameter, ℝ) → C(CircleParameter, ℝ) :=
  continuousCircleAffine ((1 / 2 : ℝ) : ℂ) 0 (by norm_num)

/-- Positive dyadic scales. -/
def circleDilationScale (n : ℕ) : ℝ := (2 : ℝ)⁻¹ ^ n

/-- The zeroth iterate is the identity, even for an unnormalized profile. -/
theorem continuousCircleDilation_iterate_zero (f : C(CircleParameter, ℝ)) :
    (continuousCircleDilation^[0]) f = f := rfl

/-- Evaluation of a positive iterate, including the normalization at its own scale. -/
theorem continuousCircleDilation_iterate_succ (n : ℕ)
    (f : C(CircleParameter, ℝ)) (p : CircleParameter) :
    (continuousCircleDilation^[n + 1]) f p =
      f (⟨circleDilationScale (n + 1) * (p.1 : ℝ),
          mul_pos (pow_pos (show (0 : ℝ) < (2 : ℝ)⁻¹ by norm_num) (n + 1)) p.1.2⟩,
        (circleDilationScale (n + 1) : ℂ) * p.2) -
      f (⟨circleDilationScale (n + 1),
        pow_pos (show (0 : ℝ) < (2 : ℝ)⁻¹ by norm_num) (n + 1)⟩, 0) := by
  induction n generalizing p with
  | zero =>
      simp [continuousCircleDilation, continuousCircleAffine, affineCircleParameter,
        circleDilationScale]
  | succ n ih =>
      rw [show n + 1 + 1 = (n + 1) + 1 by omega, Function.iterate_succ_apply']
      change ((continuousCircleDilation^[n + 1]) f)
          (affineCircleParameter ((1 / 2 : ℝ) : ℂ) 0 (by norm_num) p) -
        ((continuousCircleDilation^[n + 1]) f)
          (⟨‖((1 / 2 : ℝ) : ℂ)‖, by norm_num⟩, 0) = _
      rw [ih, ih]
      simp only [affineCircleParameter, ContinuousMap.coe_mk, circleDilationScale,
        pow_succ, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_ofNat,
        mul_zero, add_zero, sub_sub_sub_cancel_right]
      norm_num
      congr 2 <;> simp <;> ring

/-- Circle evaluations generate the Borel sigma-algebra of continuous profiles. -/
theorem coordinateSigma_circle_evaluation :
    coordinateSigma (fun p : CircleParameter => fun f : C(CircleParameter, ℝ) => f p) =
      (inferInstance : MeasurableSpace C(CircleParameter, ℝ)) := by
  rw [ContinuousMap.measurableSpace_eq_iSup_comap_eval]
  simp only [coordinateSigma, BorelSpace.measurable_eq]

/-- Dyadic dilation preserves the law of any measurable circle-average version. -/
theorem IsWholePlaneGFF.measurePreserving_continuousCircleDilation
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) {F : Ω → C(CircleParameter, ℝ)}
    (hF : Measurable F)
    (hversion : ∀ p : CircleParameter, (fun ω => F ω p) =ᵐ[P] fun ω => hcirc ω p.1 p.2) :
    MeasurePreserving continuousCircleDilation (P.map F) (P.map F) := by
  have hT : Measurable continuousCircleDilation :=
    measurable_continuousCircleAffine measurable_id (by norm_num)
  refine ⟨hT, ?_⟩
  rw [Measure.map_map hT hF]
  exact (h.identDistrib_continuousCircleAffine hF hversion (by norm_num) 0).map_eq

/-- A finite family of iterated profile evaluations agrees with the corresponding
normalized dyadic circle averages, outside a null set depending on the iterate. -/
theorem ae_iterated_circle_evaluations
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hcirc : Ω → ℝ → ℂ → ℝ} {F : Ω → C(CircleParameter, ℝ)}
    (hversion : ∀ p : CircleParameter, (fun ω => F ω p) =ᵐ[P] fun ω => hcirc ω p.1 p.2)
    {k : ℕ} (points : Fin k → CircleParameter) (n : ℕ) :
    (fun ω j => (continuousCircleDilation^[n + 1]) (F ω) (points j)) =ᵐ[P]
      (fun ω j => affineCircle hcirc (((circleDilationScale (n + 1) : ℝ) : ℂ)) 0 ω
        (points j).1 (points j).2) := by
  let scale := circleDilationScale (n + 1)
  have hscale : 0 < scale := pow_pos (by norm_num) _
  let scaled : Fin k → CircleParameter := fun j =>
    (⟨scale * (points j).1, mul_pos hscale (points j).1.2⟩, (scale : ℂ) * (points j).2)
  have he : ∀ᵐ ω ∂P, ∀ j, F ω (scaled j) =
      hcirc ω (scale * (points j).1) ((scale : ℂ) * (points j).2) := by
    exact ae_all_iff.mpr (fun j => hversion (scaled j))
  filter_upwards [he, hversion (⟨scale, hscale⟩, 0)] with ω he hz
  funext j
  rw [continuousCircleDilation_iterate_succ, he j, hz]
  simp [affineCircle, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hscale, scale]

/-- Finite continuous observables of the circle-profile law asymptotically factorize. -/
theorem IsWholePlaneGFF.cylinderFactorization_continuousCircleDilation
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) {F : Ω → C(CircleParameter, ℝ)}
    (hF : Measurable F)
    (hversion : ∀ p : CircleParameter, (fun ω => F ω p) =ᵐ[P] fun ω => hcirc ω p.1 p.2) :
    cylinderFactorization (P.map F) (fun p : CircleParameter => fun u : C(CircleParameter, ℝ) => u p)
      continuousCircleDilation := by
  let : IsProbabilityMeasure P := h.isProbabilityMeasure
  let hT := h.measurePreserving_continuousCircleDilation hF hversion
  intro m k a b f g
  let o : Fin m → GFFObservable.Admissible := fun i => ⟨.circle (a i).1 (a i).2, (a i).1.2⟩
  let q : Fin k → GFFObservable.Admissible := fun i => ⟨.circle (b i).1 (b i).2, (b i).1.2⟩
  have hvec (points : Fin m → CircleParameter) :
      Measurable (fun u : C(CircleParameter, ℝ) => fun i => u (points i)) :=
    Measurable.of_eval fun i => ContinuousMap.measurable_eval _
  have hvec' (points : Fin k → CircleParameter) :
      Measurable (fun u : C(CircleParameter, ℝ) => fun i => u (points i)) :=
    Measurable.of_eval fun i => ContinuousMap.measurable_eval _
  have hf : Measurable (fun u : C(CircleParameter, ℝ) => f (fun i => u (a i))) :=
    f.continuous.measurable.comp (hvec a)
  have hg : Measurable (fun u : C(CircleParameter, ℝ) => g (fun i => u (b i))) :=
    g.continuous.measurable.comp (hvec' b)
  have hfirst : (fun ω i => F ω (a i)) =ᵐ[P] (fun ω i => hcirc ω (a i).1 (a i).2) := by
    filter_upwards [ae_all_iff.mpr (fun i => hversion (a i))] with ω hω
    exact funext hω
  have hsecond : (fun ω i => F ω (b i)) =ᵐ[P] (fun ω i => hcirc ω (b i).1 (b i).2) := by
    filter_upwards [ae_all_iff.mpr (fun i => hversion (b i))] with ω hω
    exact funext hω
  have hleft : (∫ u, f (fun i => u (a i)) ∂P.map F) =
      ∫ ω, f (fun i => hcirc ω (a i).1 (a i).2) ∂P := by
    rw [integral_map hF.aemeasurable hf.aestronglyMeasurable]
    exact integral_congr_ae (hfirst.fun_comp f)
  have hright : (∫ u, g (fun i => u (b i)) ∂P.map F) =
      ∫ ω, g (fun i => hcirc ω (b i).1 (b i).2) ∂P := by
    rw [integral_map hF.aemeasurable hg.aestronglyMeasurable]
    exact integral_congr_ae (hsecond.fun_comp g)
  rw [hleft, hright]
  have hlim := h.tendsto_integral_dyadic_observables_product o q f g
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hm := hf.mul (hg.comp (hT.iterate (n + 1)).measurable)
  change Measurable (fun u => f (fun i => u (a i)) *
    g (fun j => (continuousCircleDilation^[n + 1]) u (b j))) at hm
  simp only [Nat.succ_eq_add_one]
  rw [integral_map hF.aemeasurable hm.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [hfirst, ae_iterated_circle_evaluations hversion b n] with ω hω hn
  dsimp only [circleDilationScale] at hn
  simp only [o, q, GFFObservable.eval]
  rw [← hω, ← hn]

/-- The continuous circle-profile law is mixing for every pair of Borel events. -/
theorem IsWholePlaneGFF.tendsto_continuousCircleDilation_inter
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) {F : Ω → C(CircleParameter, ℝ)}
    (hF : Measurable F)
    (hversion : ∀ p : CircleParameter, (fun ω => F ω p) =ᵐ[P] fun ω => hcirc ω p.1 p.2)
    {A B : Set C(CircleParameter, ℝ)} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    Tendsto (fun n : ℕ => ((P.map F) (A ∩ (continuousCircleDilation^[n]) ⁻¹' B)).toReal)
      atTop (𝓝 (((P.map F) A).toReal * ((P.map F) B).toReal)) := by
  let : IsProbabilityMeasure P := h.isProbabilityMeasure
  apply tendsto_measure_inter_preimage_iterate_of_cylinderFactorization (P.map F)
    (fun p : CircleParameter => fun u : C(CircleParameter, ℝ) => u p)
    (fun p => ContinuousMap.measurable_eval p) continuousCircleDilation
    (h.measurePreserving_continuousCircleDilation hF hversion)
    (h.cylinderFactorization_continuousCircleDilation hF hversion)
  · rwa [coordinateSigma_circle_evaluation]
  · rwa [coordinateSigma_circle_evaluation]

/-- Mixing makes the dyadic dilation ergodic for the continuous-profile law. -/
theorem IsWholePlaneGFF.ergodic_continuousCircleDilation
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) {F : Ω → C(CircleParameter, ℝ)}
    (hF : Measurable F)
    (hversion : ∀ p : CircleParameter, (fun ω => F ω p) =ᵐ[P] fun ω => hcirc ω p.1 p.2) :
    Ergodic continuousCircleDilation (P.map F) := by
  let : IsProbabilityMeasure P := h.isProbabilityMeasure
  refine ⟨h.measurePreserving_continuousCircleDilation hF hversion, ⟨?_⟩⟩
  intro A hA hAinv
  have hi (n : ℕ) : (continuousCircleDilation^[n]) ⁻¹' A = A :=
    Function.IsFixedPt.preimage_iterate hAinv n
  have hmix := h.tendsto_continuousCircleDilation_inter hF hversion hA hA.compl
  have hz : ((P.map F) A).toReal * ((P.map F) Aᶜ).toReal = 0 := by
    apply tendsto_nhds_unique hmix
    simpa only [Set.preimage_compl, hi, Set.inter_compl_self, measure_empty,
      ENNReal.toReal_zero] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  rcases mul_eq_zero.mp hz with ha | ha
  · rw [eventuallyEmptyOrUniv_iff']
    left
    simpa using ((ENNReal.toReal_eq_zero_iff _).mp ha).resolve_right (measure_ne_top _ _)
  · rw [eventuallyEmptyOrUniv_iff']
    right
    simpa using ((ENNReal.toReal_eq_zero_iff _).mp ha).resolve_right (measure_ne_top _ _)

/-- There is a measurable continuous circle version whose law is invariant,
mixing, and ergodic under dyadic dilation. -/
theorem IsWholePlaneGFF.exists_mixing_continuous_circle_version
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) :
    ∃ F : Ω → C(CircleParameter, ℝ),
      Measurable F ∧ (∀ ω, F ω (⟨1, by simp⟩, 0) = 0) ∧
      (∀ p : CircleParameter, (fun ω => F ω p) =ᵐ[P] fun ω => hcirc ω p.1 p.2) ∧
      MeasurePreserving continuousCircleDilation (P.map F) (P.map F) ∧
      (∀ A B : Set C(CircleParameter, ℝ), MeasurableSet A → MeasurableSet B →
        Tendsto (fun n : ℕ => ((P.map F) (A ∩ (continuousCircleDilation^[n]) ⁻¹' B)).toReal)
          atTop (𝓝 (((P.map F) A).toReal * ((P.map F) B).toReal))) ∧
      Ergodic continuousCircleDilation (P.map F) := by
  obtain ⟨F, hF, hnorm, hversion⟩ := h.exists_measurable_continuous_circle_version
  exact ⟨F, hF, hnorm, hversion, h.measurePreserving_continuousCircleDilation hF hversion,
    fun _ _ hA hB => h.tendsto_continuousCircleDilation_inter hF hversion hA hB,
    h.ergodic_continuousCircleDilation hF hversion⟩

#print axioms coordinateSigma_circle_evaluation
#print axioms IsWholePlaneGFF.measurePreserving_continuousCircleDilation
#print axioms continuousCircleDilation_iterate_succ
#print axioms ae_iterated_circle_evaluations
#print axioms IsWholePlaneGFF.cylinderFactorization_continuousCircleDilation
#print axioms IsWholePlaneGFF.tendsto_continuousCircleDilation_inter
#print axioms IsWholePlaneGFF.ergodic_continuousCircleDilation
#print axioms IsWholePlaneGFF.exists_mixing_continuous_circle_version

end HarmonicBalls

import HarmonicBalls.Proofs.GFF.CommonContinuousCircleLQGVersion
import HarmonicBalls.Proofs.GFF.LogInsertionCircleAverages

/-! # Joint logarithmic insertion of continuous circle profiles

The GFF and continuous circle-average construction are due to Leonardo Bonanno.
The literal correction follows `circleAvg_logInsertion`, with coefficient `-α`.
Agreement with the reconstructed distribution is only asserted at fixed circles
by that theorem's accompanying GFF result.
-/

noncomputable section
open MeasureTheory Filter Topology
namespace HarmonicBalls

/-- A positive-radius circle profile with a logarithmic insertion at `v`. -/
def logInsertedCircleProfile (F : C(CircleParameter, ℝ)) (α : ℝ) (v : ℂ) :
    C(CircleParameter, ℝ) where
  toFun p := F p - α * Real.log (max (p.1 : ℝ) ‖p.2 - v‖)
  continuous_toFun := by
    exact F.continuous.sub (continuous_const.mul
      (((continuous_subtype_val.comp continuous_fst).max
        ((continuous_snd.sub continuous_const).norm)).log
        (fun p => (lt_max_of_lt_left p.1.2).ne')))

@[simp] theorem logInsertedCircleProfile_apply (F : C(CircleParameter, ℝ))
    (α : ℝ) (v : ℂ) (p : CircleParameter) :
    logInsertedCircleProfile F α v p = F p - α * Real.log (max (p.1 : ℝ) ‖p.2 - v‖) := rfl

/-- Measurability allows arbitrary dependence among the profile, coefficient and root. -/
theorem measurable_logInsertedCircleProfile_random
    {Ω : Type*} [MeasurableSpace Ω] {F : Ω → C(CircleParameter, ℝ)}
    {A : Ω → ℝ} {V : Ω → ℂ} (hF : Measurable F) (hA : Measurable A)
    (hV : Measurable V) : Measurable (fun ω => logInsertedCircleProfile (F ω) (A ω) (V ω)) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro p
  change Measurable (fun ω => F ω p - A ω * Real.log (max (p.1 : ℝ) ‖p.2 - V ω‖))
  exact ((ContinuousMap.measurable_eval p).comp hF).sub
    (hA.mul ((measurable_const.max ((measurable_const.sub hV).norm)).log))

/-- Joint measurability in the profile, insertion coefficient and insertion root. -/
theorem measurable_logInsertedCircleProfile :
    Measurable (fun x : C(CircleParameter, ℝ) × ℝ × ℂ =>
      logInsertedCircleProfile x.1 x.2.1 x.2.2) :=
  measurable_logInsertedCircleProfile_random measurable_fst measurable_snd.fst measurable_snd.snd

/-- Normalize an inserted profile to have zero average on the unit circle. -/
def normalizedLogInsertedCircleProfile (F : C(CircleParameter, ℝ)) (α : ℝ) (v : ℂ) :
    C(CircleParameter, ℝ) :=
  logInsertedCircleProfile F α v -
    ContinuousMap.const CircleParameter (logInsertedCircleProfile F α v (⟨1, by norm_num⟩, 0))

@[simp] theorem normalizedLogInsertedCircleProfile_apply (F : C(CircleParameter, ℝ))
    (α : ℝ) (v : ℂ) (p : CircleParameter) :
    normalizedLogInsertedCircleProfile F α v p =
      F p - α * Real.log (max (p.1 : ℝ) ‖p.2 - v‖) -
        (F (⟨1, by norm_num⟩, 0) - α * Real.log (max 1 ‖v‖)) := by
  simp [normalizedLogInsertedCircleProfile]

/-- The normalized profile is jointly measurable for dependent random parameters. -/
theorem measurable_normalizedLogInsertedCircleProfile_random
    {Ω : Type*} [MeasurableSpace Ω] {F : Ω → C(CircleParameter, ℝ)}
    {A : Ω → ℝ} {V : Ω → ℂ} (hF : Measurable F) (hA : Measurable A)
    (hV : Measurable V) :
    Measurable (fun ω => normalizedLogInsertedCircleProfile (F ω) (A ω) (V ω)) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro p
  simp only [normalizedLogInsertedCircleProfile_apply]
  exact (((ContinuousMap.measurable_eval p).comp hF).sub
    (hA.mul ((measurable_const.max ((measurable_const.sub hV).norm)).log))).sub
    (((ContinuousMap.measurable_eval ((⟨1, by norm_num⟩, 0) : CircleParameter)).comp hF).sub
      (hA.mul (((measurable_const : Measurable (fun _ : Ω => (1 : ℝ))).max hV.norm).log)))

/-- One event gives the literal raw inserted profile for all roots and coefficients. -/
theorem ae_logInsertedCircleProfile_eq_raw
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hcirc : Ω → ℝ → ℂ → ℝ} {F : Ω → C(CircleParameter, ℝ)}
    (h : ∀ᵐ ω ∂P, ∀ p : CircleParameter, F ω p = hcirc ω p.1 p.2) :
    ∀ᵐ ω ∂P, ∀ (α : ℝ) (v : ℂ) (p : CircleParameter),
      logInsertedCircleProfile (F ω) α v p =
        hcirc ω p.1 p.2 - α * Real.log (max (p.1 : ℝ) ‖p.2 - v‖) := by
  filter_upwards [h] with ω hω α v p
  rw [logInsertedCircleProfile_apply, hω p]

/-- The same event gives the unit-circle normalized raw profile. -/
theorem ae_normalizedLogInsertedCircleProfile_eq_raw
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hcirc : Ω → ℝ → ℂ → ℝ} {F : Ω → C(CircleParameter, ℝ)}
    (h : ∀ᵐ ω ∂P, ∀ p : CircleParameter, F ω p = hcirc ω p.1 p.2) :
    ∀ᵐ ω ∂P, ∀ (α : ℝ) (v : ℂ) (p : CircleParameter),
      normalizedLogInsertedCircleProfile (F ω) α v p =
        hcirc ω p.1 p.2 - α * Real.log (max (p.1 : ℝ) ‖p.2 - v‖) -
          (hcirc ω 1 0 - α * Real.log (max 1 ‖v‖)) := by
  filter_upwards [h] with ω hω α v p
  rw [normalizedLogInsertedCircleProfile_apply, hω p, hω (⟨1, by norm_num⟩, 0)]

/-- Joint measurability of the normalized profile. -/
theorem measurable_normalizedLogInsertedCircleProfile :
    Measurable (fun x : C(CircleParameter, ℝ) × ℝ × ℂ =>
      normalizedLogInsertedCircleProfile x.1 x.2.1 x.2.2) :=
  measurable_normalizedLogInsertedCircleProfile_random measurable_fst measurable_snd.fst
    measurable_snd.snd

/-- A whole-plane GFF has one event for every inserted positive circle. -/
theorem IsWholePlaneGFF.ae_logInsertedCircleProfile_eq_raw
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {F : Ω → C(CircleParameter, ℝ)} (hh : IsWholePlaneGFF P hC hcirc)
    (hF : ∀ p : CircleParameter, (fun ω => F ω p) =ᵐ[P] fun ω => hcirc ω p.1 p.2) :
    ∀ᵐ ω ∂P, ∀ (α : ℝ) (v : ℂ) (p : CircleParameter),
      logInsertedCircleProfile (F ω) α v p =
        hcirc ω p.1 p.2 - α * Real.log (max (p.1 : ℝ) ‖p.2 - v‖) :=
  HarmonicBalls.ae_logInsertedCircleProfile_eq_raw (hh.ae_circle_map_eq_raw hF)

/-- The common event permits arbitrary, possibly dependent, random parameters. -/
theorem ae_logInsertedCircleProfile_random_eq_raw
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hcirc : Ω → ℝ → ℂ → ℝ} {F : Ω → C(CircleParameter, ℝ)}
    (h : ∀ᵐ ω ∂P, ∀ p : CircleParameter, F ω p = hcirc ω p.1 p.2)
    (A : Ω → ℝ) (V : Ω → ℂ) :
    ∀ᵐ ω ∂P, ∀ p : CircleParameter,
      logInsertedCircleProfile (F ω) (A ω) (V ω) p =
        hcirc ω p.1 p.2 - A ω * Real.log (max (p.1 : ℝ) ‖p.2 - V ω‖) := by
  filter_upwards [ae_logInsertedCircleProfile_eq_raw h] with ω hω p
  exact hω (A ω) (V ω) p

/-- The normalized common-event formula also permits dependent parameters. -/
theorem ae_normalizedLogInsertedCircleProfile_random_eq_raw
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hcirc : Ω → ℝ → ℂ → ℝ} {F : Ω → C(CircleParameter, ℝ)}
    (h : ∀ᵐ ω ∂P, ∀ p : CircleParameter, F ω p = hcirc ω p.1 p.2)
    (A : Ω → ℝ) (V : Ω → ℂ) :
    ∀ᵐ ω ∂P, ∀ p : CircleParameter,
      normalizedLogInsertedCircleProfile (F ω) (A ω) (V ω) p =
        hcirc ω p.1 p.2 - A ω * Real.log (max (p.1 : ℝ) ‖p.2 - V ω‖) -
          (hcirc ω 1 0 - A ω * Real.log (max 1 ‖V ω‖)) := by
  filter_upwards [ae_normalizedLogInsertedCircleProfile_eq_raw h] with ω hω p
  exact hω (A ω) (V ω) p

end HarmonicBalls

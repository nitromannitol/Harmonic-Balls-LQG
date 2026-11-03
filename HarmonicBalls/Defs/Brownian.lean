import Mathlib
import MarkovProcess.Examples.HeatSemigroup
import MarkovProcess.Trajectory.ExitLaw

/-! # Planar Brownian motion, exit times and harmonic measure

Standard planar Brownian motion `𝓑^x` started from `x ∈ ℂ` (paper/lqg_harmonic_ball-corrected.tex, line 1122:
"`𝓑^u` denotes standard planar Brownian motion started from `u`"), its exit and hitting times, the harmonic
measure of an open set, and the events "`𝓑^x` exits `U` before exiting `V`" (eq:good-annulus-harmonic,
line 1120), "`𝓑^x` hits `A` before exiting `O`" and "`𝓑^x` exits `A` before hitting `B`"
(Lemma 6.9, lemma:harmonic-odometer-comparison, line 1459;
the event is at line 1463).

## Construction

The path space is MarkovProcess's `ContinuousPath ℂ = C(ℝ≥0, ℂ)` with the Borel σ-algebra of the
compact-open topology. Writing `brownianMotion : Kernel ℝ (ContinuousPath ℝ)` for MarkovProcess's real
Brownian motion (the continuous-path process of the heat semigroup), planar Brownian motion started from `x`
is the law of `𝓑 = 𝓑¹ + i 𝓑²`, where `𝓑¹` and `𝓑²` are independent real Brownian motions started from
`Re x` and `Im x`:
`planarBrownianMotion x = ((brownianMotion (Re x)).prod (brownianMotion (Im x))).map complexPathOfReIm`.
Each coordinate has `E[(𝓑ʲ_t - 𝓑ʲ_0)²] = t` (standard normalization, generator `Δ/2`).

## Exit and hitting times

`ContinuousPath.exitTime U ω = inf {t : ω t ∉ U} ∈ [0, ∞]` is MarkovProcess's exit time; the hitting time
of `A` is the exit time of `Aᶜ`. The exit position `ω(τ_U)` is read as in MarkovProcess's `exitLaw`
(`MarkovProcess/Trajectory/ExitLaw.lean`), so that the harmonic measure below is literally the exit
distribution of the planar process.

## Measurability

For an open `U` the exit time is Borel (`MarkovProcess.ContinuousPath.measurable_exitTime`). For a closed
`A` the hitting time is Borel. The paper also uses exit times of Borel sets (the set `Y` of line 1117); these
are only universally measurable, so every probability below is the value of the measure on the event, i.e.
its outer measure, which is the probability of the event for the completed law whenever it is measurable.
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory MarkovProcess
open scoped ENNReal NNReal

/-! ### Planar Brownian motion -/

/-- The planar path `t ↦ ω₁ t + i ω₂ t` assembled from two real paths. -/
noncomputable def complexPathOfReIm (p : ContinuousPath ℝ × ContinuousPath ℝ) : ContinuousPath ℂ :=
  ⟨fun t => (p.1 t : ℂ) + (p.2 t : ℂ) * Complex.I, by fun_prop⟩

@[simp]
theorem complexPathOfReIm_apply (p : ContinuousPath ℝ × ContinuousPath ℝ) (t : ℝ≥0) :
    complexPathOfReIm p t = (p.1 t : ℂ) + (p.2 t : ℂ) * Complex.I :=
  rfl

/-- The pair of real paths `(Re ω, Im ω)` of a planar path. -/
noncomputable def reImPath (ω : ContinuousPath ℂ) : ContinuousPath ℝ × ContinuousPath ℝ :=
  (⟨fun t => (ω t).re, by fun_prop⟩, ⟨fun t => (ω t).im, by fun_prop⟩)

@[simp]
theorem reImPath_fst_apply (ω : ContinuousPath ℂ) (t : ℝ≥0) : (reImPath ω).1 t = (ω t).re :=
  rfl

@[simp]
theorem reImPath_snd_apply (ω : ContinuousPath ℂ) (t : ℝ≥0) : (reImPath ω).2 t = (ω t).im :=
  rfl

theorem reImPath_complexPathOfReIm (p : ContinuousPath ℝ × ContinuousPath ℝ) :
    reImPath (complexPathOfReIm p) = p := by
  ext t <;> simp

theorem complexPathOfReIm_reImPath (ω : ContinuousPath ℂ) :
    complexPathOfReIm (reImPath ω) = ω := by
  ext t
  simp [Complex.re_add_im]

theorem continuous_complexPathOfReIm : Continuous complexPathOfReIm := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  show Continuous fun q : (ContinuousPath ℝ × ContinuousPath ℝ) × ℝ≥0 =>
    (q.1.1 q.2 : ℂ) + (q.1.2 q.2 : ℂ) * Complex.I
  fun_prop

theorem continuous_reImPath : Continuous reImPath := by
  refine Continuous.prodMk ?_ ?_ <;> apply ContinuousMap.continuous_of_continuous_uncurry
  · show Continuous fun q : ContinuousPath ℂ × ℝ≥0 => (q.1 q.2).re
    fun_prop
  · show Continuous fun q : ContinuousPath ℂ × ℝ≥0 => (q.1 q.2).im
    fun_prop

theorem measurable_complexPathOfReIm : Measurable complexPathOfReIm :=
  continuous_complexPathOfReIm.measurable

theorem measurable_reImPath : Measurable reImPath :=
  continuous_reImPath.measurable

/-- **Standard planar Brownian motion** `𝓑^x`, as a Markov kernel from the starting point `x ∈ ℂ` to
continuous paths (line 1122): `𝓑 = 𝓑¹ + i 𝓑²` with `𝓑¹`, `𝓑²` independent standard real Brownian motions
(MarkovProcess's `brownianMotion`) started from `Re x` and `Im x`. -/
noncomputable def planarBrownianMotion : Kernel ℂ (ContinuousPath ℂ) :=
  ((brownianMotion.comap Complex.re Complex.measurable_re) ×ₖ
      (brownianMotion.comap Complex.im Complex.measurable_im)).map complexPathOfReIm

theorem planarBrownianMotion_apply (x : ℂ) :
    planarBrownianMotion x =
      ((brownianMotion x.re).prod (brownianMotion x.im)).map complexPathOfReIm := by
  rw [planarBrownianMotion, Kernel.map_apply _ measurable_complexPathOfReIm, Kernel.prod_apply,
    Kernel.comap_apply, Kernel.comap_apply]

instance isMarkovKernel_planarBrownianMotion : IsMarkovKernel planarBrownianMotion :=
  Kernel.IsMarkovKernel.map _ measurable_complexPathOfReIm

/-- The real and imaginary parts of planar Brownian motion started from `x` are independent standard real
Brownian motions started from `Re x` and `Im x`: the joint law of `(Re 𝓑, Im 𝓑)` is the product law. -/
theorem planarBrownianMotion_map_reImPath (x : ℂ) :
    (planarBrownianMotion x).map reImPath = (brownianMotion x.re).prod (brownianMotion x.im) := by
  rw [planarBrownianMotion_apply, Measure.map_map measurable_reImPath measurable_complexPathOfReIm]
  have hid : reImPath ∘ complexPathOfReIm = id := funext reImPath_complexPathOfReIm
  rw [hid, Measure.map_id]

/-- The real part of planar Brownian motion started from `x` is a standard real Brownian motion started from
`Re x`. -/
theorem planarBrownianMotion_map_re (x : ℂ) :
    (planarBrownianMotion x).map (fun ω => (reImPath ω).1) = brownianMotion x.re := by
  have hcomp : (fun ω => (reImPath ω).1) = Prod.fst ∘ reImPath := rfl
  rw [hcomp, ← Measure.map_map measurable_fst measurable_reImPath, planarBrownianMotion_map_reImPath,
    Measure.map_fst_prod, measure_univ, one_smul]

/-- The imaginary part of planar Brownian motion started from `x` is a standard real Brownian motion started
from `Im x`. -/
theorem planarBrownianMotion_map_im (x : ℂ) :
    (planarBrownianMotion x).map (fun ω => (reImPath ω).2) = brownianMotion x.im := by
  have hcomp : (fun ω => (reImPath ω).2) = Prod.snd ∘ reImPath := rfl
  rw [hcomp, ← Measure.map_map measurable_snd measurable_reImPath, planarBrownianMotion_map_reImPath,
    Measure.map_snd_prod, measure_univ, one_smul]

/-- Real Brownian motion started from `y` starts at `y` almost surely. -/
theorem ae_brownianMotion_eval_zero (y : ℝ) : ∀ᵐ ω ∂brownianMotion y, ω 0 = y :=
  SubMarkovKernelSemigroup.IsConservative.ae_eval_zero_eq isConservative_heatSemigroup
    kolmogorovRegular_heatSemigroup y

/-- Planar Brownian motion started from `x` starts at `x` almost surely. -/
theorem ae_planarBrownianMotion_eval_zero (x : ℂ) : ∀ᵐ ω ∂planarBrownianMotion x, ω 0 = x := by
  have hset : MeasurableSet {ω : ContinuousPath ℂ | ω 0 = x} :=
    measurableSet_eq_fun (ContinuousPath.measurable_coordinateProcess (alpha := ℂ) 0) measurable_const
  rw [planarBrownianMotion_apply, ae_map_iff measurable_complexPathOfReIm.aemeasurable hset]
  have h1 := (Measure.quasiMeasurePreserving_fst (μ := brownianMotion x.re)
    (ν := brownianMotion x.im)).ae (ae_brownianMotion_eval_zero x.re)
  have h2 := (Measure.quasiMeasurePreserving_snd (μ := brownianMotion x.re)
    (ν := brownianMotion x.im)).ae (ae_brownianMotion_eval_zero x.im)
  filter_upwards [h1, h2] with p hp1 hp2
  simp [hp1, hp2, Complex.re_add_im]

/-! ### Exit and hitting times -/

/-- The *hitting time* `inf {t ≥ 0 : ω t ∈ A} ∈ [0, ∞]` of a set `A` by a path: the exit time of `Aᶜ`. -/
noncomputable def hittingTime {α : Type*} [TopologicalSpace α] (A : Set α) (ω : ContinuousPath α) : ℝ≥0∞ :=
  ContinuousPath.exitTime Aᶜ ω

/-- The *exit position* `ω(τ_U)` of a path from `U`, read at the exit time `τ_U = exitTime U ω`; it is the
exit position only on the event `{τ_U < ∞}` (elsewhere it is the junk value `ω 0`). The formula is the one
of MarkovProcess's `exitLaw`. -/
noncomputable def exitPosition {α : Type*} [PseudoMetricSpace α] (U : Set α) (ω : ContinuousPath α) : α :=
  ω ((ContinuousPath.exitTimeTop U ω).untopD 0)

theorem exitPosition_eq {α : Type*} [PseudoMetricSpace α] (U : Set α) (ω : ContinuousPath α)
    (h : ContinuousPath.exitTime U ω ≠ ⊤) :
    exitPosition U ω = ω (ContinuousPath.exitTime U ω).toNNReal := by
  rw [exitPosition, ContinuousPath.untopD_exitTimeTop_eq_toNNReal U ω h]

theorem measurable_hittingTime {A : Set ℂ} (hA : IsClosed A) :
    Measurable (hittingTime A : ContinuousPath ℂ → ℝ≥0∞) :=
  ContinuousPath.measurable_exitTime Aᶜ hA.isOpen_compl

theorem measurable_exitPosition {U : Set ℂ} (hU : IsOpen U) :
    Measurable (exitPosition U : ContinuousPath ℂ → ℂ) := by
  unfold exitPosition
  exact ContinuousPath.measurable_eval_untopD_exitTimeTop U hU

/-! ### Harmonic measure -/

/-- The *harmonic measure* of `O` seen from `x`: the law of the exit position `𝓑^x_{τ_O}` of planar Brownian
motion started from `x`, on the event `{τ_O < ∞}` that it leaves `O`. Its total mass is the probability of
leaving `O` (`harmonicMeasure_univ`), so it is a sub-probability measure (`harmonicMeasure_univ_le_one`); for
`x ∈ O` with `O` open it is carried by `∂O` (`harmonicMeasure_compl_frontier`). Intended for open `O`: for
other `O` the exit position need not be measurable, and `Measure.map` then returns a junk Dirac mass. -/
noncomputable def harmonicMeasure (O : Set ℂ) (x : ℂ) : Measure ℂ :=
  ((planarBrownianMotion x).restrict {ω | ContinuousPath.exitTime O ω < ⊤}).map (exitPosition O)

instance isFiniteMeasure_harmonicMeasure (O : Set ℂ) (x : ℂ) : IsFiniteMeasure (harmonicMeasure O x) := by
  unfold harmonicMeasure
  infer_instance

theorem harmonicMeasure_apply {O : Set ℂ} (hO : IsOpen O) (x : ℂ) {B : Set ℂ} (hB : MeasurableSet B) :
    harmonicMeasure O x B =
      planarBrownianMotion x {ω | ContinuousPath.exitTime O ω < ⊤ ∧ exitPosition O ω ∈ B} := by
  rw [harmonicMeasure, Measure.map_apply (measurable_exitPosition hO) hB,
    Measure.restrict_apply (measurable_exitPosition hO hB)]
  congr 1
  ext ω
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq]
  exact and_comm

/-- The total mass of the harmonic measure of an open set is the probability that Brownian motion leaves it. -/
theorem harmonicMeasure_univ {O : Set ℂ} (hO : IsOpen O) (x : ℂ) :
    harmonicMeasure O x Set.univ = planarBrownianMotion x {ω | ContinuousPath.exitTime O ω < ⊤} := by
  rw [harmonicMeasure_apply hO x MeasurableSet.univ]
  simp only [Set.mem_univ, and_true]

/-- The harmonic measure has total mass at most one. -/
theorem harmonicMeasure_univ_le_one (O : Set ℂ) (x : ℂ) : harmonicMeasure O x Set.univ ≤ 1 := by
  unfold harmonicMeasure
  by_cases hf : AEMeasurable (exitPosition O)
      ((planarBrownianMotion x).restrict {ω | ContinuousPath.exitTime O ω < ⊤})
  · rw [Measure.map_apply_of_aemeasurable hf MeasurableSet.univ, Set.preimage_univ]
    exact (Measure.restrict_apply_le _ _).trans prob_le_one
  · have hμ : (planarBrownianMotion x).restrict {ω | ContinuousPath.exitTime O ω < ⊤} ≠ 0 := by
      intro h
      rw [h] at hf
      exact hf aemeasurable_zero_measure
    rw [Measure.map_of_not_aemeasurable_of_ne_zero hf hμ]
    simp

theorem harmonicMeasure_le_one (O : Set ℂ) (x : ℂ) (B : Set ℂ) : harmonicMeasure O x B ≤ 1 :=
  (measure_mono (Set.subset_univ B)).trans (harmonicMeasure_univ_le_one O x)

/-- From a point of an open set `O`, the harmonic measure of `O` is carried by the boundary `∂O`. -/
theorem harmonicMeasure_compl_frontier {O : Set ℂ} (hO : IsOpen O) {x : ℂ} (hx : x ∈ O) :
    harmonicMeasure O x (frontier O)ᶜ = 0 := by
  rw [harmonicMeasure_apply hO x isClosed_frontier.measurableSet.compl]
  refine measure_mono_null (fun ω hω => ?_) ((ae_iff).mp (ae_planarBrownianMotion_eval_zero x))
  intro h0
  obtain ⟨hfin, hnot⟩ := hω
  rw [Set.mem_compl_iff, exitPosition_eq O ω hfin.ne] at hnot
  exact hnot (ContinuousPath.coordinate_exitTime_mem_frontier O hO ω (h0 ▸ hx) hfin.ne)

/-! ### Exit and hitting events and their probabilities -/

/-- The event "the path exits `U` before exiting `V`", `τ_U < τ_V` (eq:good-annulus-harmonic, line 1120). -/
def exitsBefore (U V : Set ℂ) : Set (ContinuousPath ℂ) :=
  {ω | ContinuousPath.exitTime U ω < ContinuousPath.exitTime V ω}

/-- The event "the path hits `A` before exiting `O`", `τ^A < τ_O`, where `τ^A` is the hitting time of `A`.
On this event the path does hit `A` (`τ^A < ∞`). -/
def hitsBeforeExiting (A O : Set ℂ) : Set (ContinuousPath ℂ) :=
  {ω | hittingTime A ω < ContinuousPath.exitTime O ω}

/-- The event "the path exits `U` before hitting `A`", `τ_U < τ^A` (Lemma 6.9,
lemma:harmonic-odometer-comparison, line 1459;
the event is at line 1463). -/
def exitsBeforeHitting (U A : Set ℂ) : Set (ContinuousPath ℂ) :=
  {ω | ContinuousPath.exitTime U ω < hittingTime A ω}

theorem exitsBeforeHitting_eq_exitsBefore (U A : Set ℂ) : exitsBeforeHitting U A = exitsBefore U Aᶜ :=
  rfl

theorem hitsBeforeExiting_eq_exitsBefore (A O : Set ℂ) : hitsBeforeExiting A O = exitsBefore Aᶜ O :=
  rfl

theorem measurableSet_exitsBefore {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V) :
    MeasurableSet (exitsBefore U V) :=
  measurableSet_lt (ContinuousPath.measurable_exitTime U hU) (ContinuousPath.measurable_exitTime V hV)

/-- `P[𝓑^x exits U before exiting V]` (eq:good-annulus-harmonic, line 1120), as a real number. -/
noncomputable def exitsBeforeProb (U V : Set ℂ) (x : ℂ) : ℝ :=
  (planarBrownianMotion x (exitsBefore U V)).toReal

/-- `P[𝓑^x hits A before exiting O]`, as a real number. -/
noncomputable def hitsBeforeExitingProb (A O : Set ℂ) (x : ℂ) : ℝ :=
  (planarBrownianMotion x (hitsBeforeExiting A O)).toReal

/-- `P[𝓑^x exits U before hitting A]` (Lemma 6.9, line 1459; the event at line 1463), as a real number. -/
noncomputable def exitsBeforeHittingProb (U A : Set ℂ) (x : ℂ) : ℝ :=
  (planarBrownianMotion x (exitsBeforeHitting U A)).toReal

theorem exitsBeforeProb_nonneg (U V : Set ℂ) (x : ℂ) : 0 ≤ exitsBeforeProb U V x :=
  ENNReal.toReal_nonneg

theorem exitsBeforeProb_le_one (U V : Set ℂ) (x : ℂ) : exitsBeforeProb U V x ≤ 1 :=
  ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)

theorem hitsBeforeExitingProb_eq (A O : Set ℂ) (x : ℂ) :
    hitsBeforeExitingProb A O x = exitsBeforeProb Aᶜ O x :=
  rfl

theorem exitsBeforeHittingProb_eq (U A : Set ℂ) (x : ℂ) :
    exitsBeforeHittingProb U A x = exitsBeforeProb U Aᶜ x :=
  rfl

/-- A path starting in an open set `O` stays in `O` for a positive time. -/
theorem exitTime_pos_of_mem {O : Set ℂ} (hO : IsOpen O) {ω : ContinuousPath ℂ} (h0 : ω 0 ∈ O) :
    0 < ContinuousPath.exitTime O ω := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hO (ω 0) h0
  obtain ⟨δ, hδ, hcont⟩ := Metric.continuous_iff.mp ω.continuous 0 ε hε
  have hδ' : (0 : ℝ≥0∞) < (Real.toNNReal δ : ℝ≥0∞) := by simpa using hδ
  refine lt_of_lt_of_le hδ' (le_sInf ?_)
  rintro s ⟨t, rfl, ht⟩
  rw [ENNReal.coe_le_coe]
  by_contra hlt
  rw [not_le] at hlt
  apply ht
  refine hball (hcont t ?_)
  have ht' : (t : ℝ) < δ := Real.lt_toNNReal_iff_coe_lt.mp hlt
  rw [NNReal.dist_eq, NNReal.coe_zero, sub_zero]
  exact abs_lt.mpr ⟨by linarith [NNReal.coe_nonneg t], ht'⟩

/-- Non-vacuity: started from a point of `A ∩ O` with `O` open, Brownian motion hits `A` before exiting `O`
almost surely. -/
theorem hitsBeforeExitingProb_of_mem {A O : Set ℂ} (hO : IsOpen O) {x : ℂ} (hxA : x ∈ A) (hxO : x ∈ O) :
    hitsBeforeExitingProb A O x = 1 := by
  have hae : ∀ᵐ ω ∂planarBrownianMotion x, ω ∈ hitsBeforeExiting A O := by
    filter_upwards [ae_planarBrownianMotion_eval_zero x] with ω h0
    have hhit : hittingTime A ω = 0 :=
      le_antisymm (sInf_le ⟨0, by simp, by simp [h0, hxA]⟩) bot_le
    show hittingTime A ω < ContinuousPath.exitTime O ω
    rw [hhit]
    exact exitTime_pos_of_mem hO (h0 ▸ hxO)
  have hcompl : planarBrownianMotion x (hitsBeforeExiting A O)ᶜ = 0 := ae_iff.mp hae
  rw [hitsBeforeExitingProb, measure_congr (ae_eq_univ.mpr hcompl), measure_univ, ENNReal.toReal_one]

end HarmonicBalls

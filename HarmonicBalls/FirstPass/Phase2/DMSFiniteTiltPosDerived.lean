import HarmonicBalls.FirstPass.Phase2.RootedDominationJointPosDerived
import HarmonicBalls.FirstPass.Frozen.S11i
import HarmonicBalls.FirstPass.S11at.Producers
import HarmonicBalls.FirstPass.Phase2.ProfileDecoderDerived
import HarmonicBalls.FirstPass.Phase2.B2ShiftedProfileDecoder

/-! # Finite-family marked tilt identity from the Sub input (MQ-lh-22)

`dMSFiniteTiltPos_of_sub` derives `DMSFiniteTiltPosStmt` (RootedDominationJointPosDerived.lean:27) from the
pairing-level marked identity `DMSLemmaA10WholePlaneMarkedSub` (FirstPass/Frozen/S11i.lean:59), which is the
Duplantier-Miller-Sheffield Lemma A.10 input (arXiv:1409.7055v4, p. 184-185). No further input is used.

Route (notes/fp-gaps/MATH-ANSWERS.md, section MQ-lh-22). Circle averages enter as a.s. limits of pairings with
the explicit annular tests `circleApprox`. (A) bounded continuous tests on the finite observation: the Sub identity
for the approximating tests, then limits in both sides by dominated convergence. (B) every measurable test: two
finite measures on the observation space agree on bounded continuous tests, hence are equal.
-/

open MeasureTheory ProbabilityTheory Metric Set Filter Topology
open scoped ENNReal NNReal

namespace HarmonicBalls

universe u

namespace DMSFiniteTiltPosDerived

/-- The measurability of `ω ↦ ∫⁻ z, f (ω, z) ∂(ν ω)` for a measurable family of finite measures. The proof
truncates `ν` by its total mass, which gives uniformly finite kernels, and passes to the limit. -/
theorem measurable_lintegral_finite_family {Ω : Type*} [MeasurableSpace Ω] (ν : Ω → Measure ℂ)
    (hν : Measurable ν) (hfin : ∀ ω, IsFiniteMeasure (ν ω)) {f : Ω × ℂ → ℝ≥0∞} (hf : Measurable f) :
    Measurable fun ω => ∫⁻ z, f (ω, z) ∂(ν ω) := by
  classical
  let νm : ℕ → Ω → Measure ℂ := fun m ω => if ν ω univ ≤ (m : ℝ≥0∞) then ν ω else 0
  have hsetm : ∀ m : ℕ, MeasurableSet {ω | ν ω univ ≤ (m : ℝ≥0∞)} := fun m =>
    measurableSet_le ((Measure.measurable_coe MeasurableSet.univ).comp hν) measurable_const
  have hνm : ∀ m : ℕ, Measurable (νm m) := fun m =>
    Measurable.piecewise (hsetm m) hν measurable_const
  have hbound : ∀ (m : ℕ) (ω : Ω), νm m ω univ ≤ (m : ℝ≥0∞) := by
    intro m ω
    simp only [νm]
    split_ifs with h
    · exact h
    · simp
  have hmeas_m : ∀ m : ℕ, Measurable fun ω => ∫⁻ z, f (ω, z) ∂(νm m ω) := by
    intro m
    let κ : Kernel Ω ℂ := ⟨νm m, hνm m⟩
    have : IsFiniteKernel κ := ⟨⟨(m : ℝ≥0∞), by simp, fun ω => hbound m ω⟩⟩
    exact Measurable.lintegral_kernel_prod_right' (κ := κ) hf
  have hlim : Tendsto (fun m : ℕ => fun ω => ∫⁻ z, f (ω, z) ∂(νm m ω)) atTop
      (𝓝 fun ω => ∫⁻ z, f (ω, z) ∂(ν ω)) := by
    refine tendsto_pi_nhds.2 fun ω => ?_
    obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt (measure_lt_top (ν ω) univ).ne
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_ge_atTop N] with m hm
    have hle : ν ω univ ≤ (m : ℝ≥0∞) := le_trans hN.le (by exact_mod_cast hm)
    simp [νm, hle]
  exact measurable_of_tendsto_metrizable' atTop hmeas_m hlim

/-- The finitized restriction of a measure family to the unit disc: the restriction when its mass is finite,
and `0` otherwise. It is measurable and finite on every fibre. -/
noncomputable def finRestr {Ω : Type*} (μ : Ω → Measure ℂ) : Ω → Measure ℂ :=
  fun ω => if μ ω (ball (0 : ℂ) 1) < ∞ then (μ ω).restrict (ball (0 : ℂ) 1) else 0

theorem measurable_finRestr {Ω : Type*} [MeasurableSpace Ω] {μ : Ω → Measure ℂ} (hμ : Measurable μ) :
    Measurable (finRestr μ) := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  have hB : MeasurableSet (ball (0 : ℂ) 1) := measurableSet_ball
  have hmB : Measurable fun ω => μ ω (ball (0 : ℂ) 1) := Measure.measurable_coe hB |>.comp hμ
  have hmS : Measurable fun ω => μ ω (s ∩ ball (0 : ℂ) 1) :=
    (Measure.measurable_coe (hs.inter hB)).comp hμ
  have hset : MeasurableSet {ω | μ ω (ball (0 : ℂ) 1) < ∞} := measurableSet_lt hmB measurable_const
  have hfun : (fun ω => finRestr μ ω s) =
      fun ω => if μ ω (ball (0 : ℂ) 1) < ∞ then μ ω (s ∩ ball (0 : ℂ) 1) else 0 := by
    funext ω
    unfold finRestr
    split_ifs
    · rw [Measure.restrict_apply hs]
    · simp
  rw [hfun]
  exact Measurable.ite hset hmS measurable_const

theorem isFiniteMeasure_finRestr {Ω : Type*} (μ : Ω → Measure ℂ) (ω : Ω) :
    IsFiniteMeasure (finRestr μ ω) := by
  unfold finRestr
  split_ifs with h
  · exact ⟨by rw [Measure.restrict_apply_univ]; exact h⟩
  · infer_instance

/-- Measurable observation maps: the triple `(X, Y, ζ)` with `ζ` measurable is measurable. -/
theorem measurable_obs {T : Type*} [mT : MeasurableSpace T] {n m : ℕ} (X : T → Fin n → ℝ) (Y : T → Fin m → ℝ)
    (ζ : T → ℂ) (hX : Measurable X) (hY : Measurable Y) (hζ : Measurable ζ) :
    Measurable (fun t => ((X t, Y t, ζ t) : (Fin n → ℝ) × (Fin m → ℝ) × ℂ)) :=
  hX.prodMk (hY.prodMk hζ)

/-- A vector of pairing-measurable coordinates is measurable (explicit σ-algebra on the domain). -/
theorem measurable_vec_of {T : Type*} [mT : MeasurableSpace T] {n : ℕ} (f : T → Fin n → ℝ)
    (h : ∀ i, Measurable fun t => f t i) : Measurable f :=
  measurable_pi_iff.2 h

/-- Evaluation at a test function is measurable for the pairing σ-algebra on functionals. -/
theorem measurable_eval_pairing {φ : ℂ → ℝ} (hφ : IsTestFunction univ φ) :
    Measurable[pairingSigmaAlgebra (fun T : (ℂ → ℝ) → ℝ => T) univ] (fun T : (ℂ → ℝ) → ℝ => T φ) :=
  FirstPassS11atProducers.FirstPassS11atBridge.measurable_pairing_eval (hC := fun T : (ℂ → ℝ) → ℝ => T) hφ

/-- Coordinatewise measurability of a bounded continuous function of a measurable observation. -/
theorem measurable_coe_bcf {T : Type*} [mT : MeasurableSpace T] {n m : ℕ} (g : BoundedContinuousFunction ((Fin n → ℝ) × (Fin m → ℝ) × ℂ) ℝ≥0)
    (X : T → Fin n → ℝ) (Y : T → Fin m → ℝ) (ζ : T → ℂ) (hX : Measurable X) (hY : Measurable Y)
    (hζ : Measurable ζ) : Measurable (fun t => (g (X t, Y t, ζ t) : ℝ≥0∞)) :=
  measurable_coe_nnreal_ennreal.comp (g.continuous.measurable.comp (measurable_obs X Y ζ hX hY hζ))

/-- **Step A (bounded continuous observations).** For a whole-plane pairing family with the marked Sub identity for
the finite-family measure `ρ` (a finite, measurable family of measures on `ℂ`), the identity holds for every bounded
continuous `g` of the finite observation. Proof: apply the Sub identity to the approximating tests
`circleApprox` (Ψ_j), then let `j → ∞` on both sides by dominated convergence. The field limit is a.s. and does not
depend on the centre; the shift limit holds for every `z` (`tendsto_dmsShiftedPairing_approx`). -/
theorem keyBCF {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (hW : IsWholePlaneGFF P hC hcirc)
    (ρ : Ω → Measure ℂ) (hρm : Measurable ρ) (hρfin : ∀ ω, IsFiniteMeasure (ρ ω))
    (hSub : ∀ Ψ : (((ℂ → ℝ) → ℝ) × ℂ) → ℝ≥0∞,
      Measurable[(pairingSigmaAlgebra (fun T : (ℂ → ℝ) → ℝ => T) univ).prod inferInstance] Ψ →
        ∫⁻ ω, ∫⁻ z, Ψ (hC ω, z) ∂(ρ ω) ∂P
          = ∫⁻ z in ball (0 : ℂ) 1, ∫⁻ ω, Ψ (dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0), z) ∂P ∂volume)
    {n m : ℕ} (φ : Fin n → ℂ → ℝ) (hφ : ∀ i, IsTestFunction univ (φ i))
    (c : Fin m → CircleParameter) (g : BoundedContinuousFunction ((Fin n → ℝ) × (Fin m → ℝ) × ℂ) ℝ≥0) :
    ∫⁻ ω, ∫⁻ z, (g ((fun i => hC ω (φ i)), (fun k => hcirc ω (c k).1.1 (c k).2), z) : ℝ≥0∞) ∂(ρ ω) ∂P
      = ∫⁻ z in ball (0 : ℂ) 1, ∫⁻ ω, (g ((fun i => dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0) (φ i)),
          (fun k => dmsShiftedCircle γ z (hcirc ω) (c k).1.1 (c k).2), z) : ℝ≥0∞) ∂P ∂volume := by
  have hr : ∀ k, 0 < (c k).1.1 := fun k => (c k).1.2
  obtain ⟨C, hbd⟩ : ∃ C : ℝ≥0, ∀ x, g x ≤ C := ⟨nndist g 0, fun x => BoundedContinuousFunction.NNReal.upper_bound g x⟩
  -- measurability in ω of the observations
  have hXm : Measurable (fun ω => fun i => hC ω (φ i)) :=
    measurable_pi_iff.2 fun i => hW.measurable_pairing (φ i) (hφ i)
  have hYjm : ∀ j : ℕ, Measurable (fun ω => fun k =>
      hC ω (FirstPassS11atProducers.circleApprox (hr k) (c k).2 j)) := fun j =>
    measurable_pi_iff.2 fun k =>
      hW.measurable_pairing _ (FirstPassS11atProducers.isTestFunction_circleApprox _ _ _)
  -- joint measurability in (z, ω) of the shifted observations
  have hXsJ : Measurable (fun p : ℂ × Ω => fun i =>
      dmsShiftedPairing γ p.1 (hC p.2) (hcirc p.2 1 0) (φ i)) :=
    measurable_pi_iff.2 fun i => (measurable_eval_pairing (hφ i)).comp
      (FirstPassS11atProducers.measurable_dmsShiftedPairing P γ hC hcirc hW)
  have hYsJ : ∀ j : ℕ, Measurable (fun p : ℂ × Ω => fun k =>
      dmsShiftedPairing γ p.1 (hC p.2) (hcirc p.2 1 0)
        (FirstPassS11atProducers.circleApprox (hr k) (c k).2 j)) := fun j =>
    measurable_pi_iff.2 fun k => (measurable_eval_pairing
      (FirstPassS11atProducers.isTestFunction_circleApprox _ _ _)).comp
      (FirstPassS11atProducers.measurable_dmsShiftedPairing P γ hC hcirc hW)
  -- the Sub identity for the approximating tests
  have hLHS : ∀ j : ℕ, ∫⁻ ω, ∫⁻ z, (g ((fun i => hC ω (φ i)),
        (fun k => hC ω (FirstPassS11atProducers.circleApprox (hr k) (c k).2 j)), z) : ℝ≥0∞) ∂(ρ ω) ∂P
      = ∫⁻ z in ball (0 : ℂ) 1, ∫⁻ ω, (g ((fun i => dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0) (φ i)),
          (fun k => dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0)
            (FirstPassS11atProducers.circleApprox (hr k) (c k).2 j)), z) : ℝ≥0∞) ∂P ∂volume := by
    intro j
    have hΨ : Measurable[(pairingSigmaAlgebra (fun T : (ℂ → ℝ) → ℝ => T) univ).prod inferInstance]
        (fun p : ((ℂ → ℝ) → ℝ) × ℂ => (g ((fun i => p.1 (φ i)),
          (fun k => p.1 (FirstPassS11atProducers.circleApprox (hr k) (c k).2 j)), p.2) : ℝ≥0∞)) := by
      set σ := pairingSigmaAlgebra (fun T : (ℂ → ℝ) → ℝ => T) univ with hσ
      have hX' : Measurable[σ] (fun T : (ℂ → ℝ) → ℝ => fun i => T (φ i)) :=
        measurable_vec_of (mT := σ) _ fun i => measurable_eval_pairing (hφ i)
      have hY' : Measurable[σ]
          (fun T : (ℂ → ℝ) → ℝ => fun k => T (FirstPassS11atProducers.circleApprox (hr k) (c k).2 j)) :=
        measurable_vec_of (mT := σ) _ fun k => measurable_eval_pairing
          (FirstPassS11atProducers.isTestFunction_circleApprox _ _ _)
      have hfst : Measurable[σ.prod inferInstance] (fun p : ((ℂ → ℝ) → ℝ) × ℂ => p.1) :=
        @measurable_fst _ _ σ inferInstance
      have hsnd : Measurable[σ.prod inferInstance] (fun p : ((ℂ → ℝ) → ℝ) × ℂ => p.2) :=
        @measurable_snd _ _ σ inferInstance
      exact measurable_coe_bcf (mT := σ.prod inferInstance) g
        (fun p : ((ℂ → ℝ) → ℝ) × ℂ => fun i => p.1 (φ i))
        (fun p : ((ℂ → ℝ) → ℝ) × ℂ => fun k => p.1 (FirstPassS11atProducers.circleApprox (hr k) (c k).2 j))
        (fun p : ((ℂ → ℝ) → ℝ) × ℂ => p.2) (hX'.comp hfst) (hY'.comp hfst) hsnd
    exact hSub _ hΨ
  -- the field limit, almost surely, for all coordinates at once
  have hfield : ∀ᵐ ω ∂P, ∀ k : Fin m, Tendsto (fun j => hC ω (FirstPassS11atProducers.circleApprox (hr k) (c k).2 j))
      atTop (𝓝 (hcirc ω (c k).1.1 (c k).2)) :=
    ae_all_iff.2 fun k => FirstPassS11atProducers.ae_tendsto_circleApprox hW (hr k) (c k).2
  -- the mass identity (Sub with Ψ ≡ 1)
  have hmass : ∫⁻ ω, ρ ω univ ∂P = volume (ball (0 : ℂ) 1) := by
    have h1 := hSub (fun _ => 1) measurable_const
    simpa [lintegral_const, Measure.restrict_apply_univ] using h1
  have hmassfin : ∫⁻ ω, ρ ω univ ∂P ≠ ∞ := by
    rw [hmass]; exact measure_ball_lt_top.ne
  have hρuniv : Measurable fun ω => ρ ω univ := (Measure.measurable_coe MeasurableSet.univ).comp hρm
  -- the limit on the left-hand side (dominated convergence in `z`, then in `ω`)
  -- the shift limit, pointwise in ω and for every centre z
  have hShift : ∀ ω, (∀ k : Fin m, Tendsto (fun j => hC ω (FirstPassS11atProducers.circleApprox (hr k) (c k).2 j))
      atTop (𝓝 (hcirc ω (c k).1.1 (c k).2))) → ∀ z : ℂ,
      Tendsto (fun j : ℕ => fun k => dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0)
        (FirstPassS11atProducers.circleApprox (hr k) (c k).2 j)) atTop
        (𝓝 (fun k => dmsShiftedCircle γ z (hcirc ω) (c k).1.1 (c k).2)) := by
    intro ω hω z
    exact tendsto_pi_nhds.2 fun k =>
      FirstPassS11atProducers.FirstPassS11atBridge.tendsto_dmsShiftedPairing_approx γ z (hC ω) (hcirc ω 1 0)
        (hr k) (c k).2 (hω k)
  have hS2 : Tendsto (fun j : ℕ => ∫⁻ ω, ∫⁻ z, (g ((fun i => hC ω (φ i)),
        (fun k => hC ω (FirstPassS11atProducers.circleApprox (hr k) (c k).2 j)), z) : ℝ≥0∞) ∂(ρ ω) ∂P)
      atTop (𝓝 (∫⁻ ω, ∫⁻ z, (g ((fun i => hC ω (φ i)), (fun k => hcirc ω (c k).1.1 (c k).2), z) : ℝ≥0∞)
        ∂(ρ ω) ∂P)) := by
    have hmeasF : ∀ j : ℕ, Measurable fun ω => ∫⁻ z, (g ((fun i => hC ω (φ i)),
        (fun k => hC ω (FirstPassS11atProducers.circleApprox (hr k) (c k).2 j)), z) : ℝ≥0∞) ∂(ρ ω) := by
      intro j
      refine measurable_lintegral_finite_family ρ hρm hρfin (f := fun p : Ω × ℂ => (g ((fun i => hC p.1 (φ i)),
        (fun k => hC p.1 (FirstPassS11atProducers.circleApprox (hr k) (c k).2 j)), p.2) : ℝ≥0∞)) ?_
      exact measurable_coe_bcf g (fun p : Ω × ℂ => fun i => hC p.1 (φ i))
        (fun p : Ω × ℂ => fun k => hC p.1 (FirstPassS11atProducers.circleApprox (hr k) (c k).2 j))
        (fun p : Ω × ℂ => p.2) (hXm.comp measurable_fst) ((hYjm j).comp measurable_fst) measurable_snd
    refine tendsto_lintegral_of_dominated_convergence (fun ω => (C : ℝ≥0∞) * ρ ω univ) hmeasF
      (fun j => Eventually.of_forall fun ω => ?_) ?_ ?_
    · calc ∫⁻ z, (g _ : ℝ≥0∞) ∂(ρ ω) ≤ ∫⁻ _z, (C : ℝ≥0∞) ∂(ρ ω) :=
            lintegral_mono fun z => ENNReal.coe_le_coe.2 (hbd _)
        _ = (C : ℝ≥0∞) * ρ ω univ := lintegral_const _
    · rw [lintegral_const_mul _ hρuniv]
      exact ENNReal.mul_ne_top ENNReal.coe_ne_top hmassfin
    · filter_upwards [hfield] with ω hω
      refine tendsto_lintegral_of_dominated_convergence (fun _ => (C : ℝ≥0∞))
        (fun j => measurable_coe_bcf g (fun _ : ℂ => fun i => hC ω (φ i))
          (fun _ : ℂ => fun k => hC ω (FirstPassS11atProducers.circleApprox (hr k) (c k).2 j))
          (fun z : ℂ => z) measurable_const measurable_const measurable_id)
        (fun j => Eventually.of_forall fun z => ENNReal.coe_le_coe.2 (hbd _))
        (by rw [lintegral_const]; exact ENNReal.mul_ne_top ENNReal.coe_ne_top (measure_lt_top _ _).ne)
        (Eventually.of_forall fun z => ?_)
      have hpt : Tendsto (fun j : ℕ => ((fun i => hC ω (φ i)),
          (fun k => hC ω (FirstPassS11atProducers.circleApprox (hr k) (c k).2 j)), z))
          atTop (𝓝 ((fun i => hC ω (φ i)), (fun k => hcirc ω (c k).1.1 (c k).2), z)) :=
        tendsto_const_nhds.prodMk_nhds (((tendsto_pi_nhds.2 hω).prodMk_nhds tendsto_const_nhds))
      exact ((ENNReal.continuous_coe.comp g.continuous).tendsto _).comp hpt
  -- the right-hand side, in the inner variable `ω` (for each `z`) and then in `z`
  have hS3 : Tendsto (fun j : ℕ => ∫⁻ z in ball (0 : ℂ) 1, ∫⁻ ω, (g ((fun i => dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0) (φ i)),
          (fun k => dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0)
            (FirstPassS11atProducers.circleApprox (hr k) (c k).2 j)), z) : ℝ≥0∞) ∂P ∂volume)
      atTop (𝓝 (∫⁻ z in ball (0 : ℂ) 1, ∫⁻ ω, (g ((fun i => dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0) (φ i)),
          (fun k => dmsShiftedCircle γ z (hcirc ω) (c k).1.1 (c k).2), z) : ℝ≥0∞) ∂P ∂volume)) := by
    have hmeasG : ∀ j : ℕ, Measurable fun z : ℂ => ∫⁻ ω, (g ((fun i => dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0) (φ i)),
        (fun k => dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0)
          (FirstPassS11atProducers.circleApprox (hr k) (c k).2 j)), z) : ℝ≥0∞) ∂P := by
      intro j
      refine Measurable.lintegral_prod_right'
        (f := fun p : ℂ × Ω => (g ((fun i => dmsShiftedPairing γ p.1 (hC p.2) (hcirc p.2 1 0) (φ i)),
          (fun k => dmsShiftedPairing γ p.1 (hC p.2) (hcirc p.2 1 0)
            (FirstPassS11atProducers.circleApprox (hr k) (c k).2 j)), p.1) : ℝ≥0∞)) ?_
      exact measurable_coe_bcf g (fun p : ℂ × Ω => fun i => dmsShiftedPairing γ p.1 (hC p.2) (hcirc p.2 1 0) (φ i))
        (fun p : ℂ × Ω => fun k => dmsShiftedPairing γ p.1 (hC p.2) (hcirc p.2 1 0)
          (FirstPassS11atProducers.circleApprox (hr k) (c k).2 j))
        (fun p : ℂ × Ω => p.1) hXsJ (hYsJ j) measurable_fst
    have hinner : ∀ z : ℂ, Tendsto (fun j : ℕ => ∫⁻ ω, (g ((fun i => dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0) (φ i)),
        (fun k => dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0)
          (FirstPassS11atProducers.circleApprox (hr k) (c k).2 j)), z) : ℝ≥0∞) ∂P)
        atTop (𝓝 (∫⁻ ω, (g ((fun i => dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0) (φ i)),
          (fun k => dmsShiftedCircle γ z (hcirc ω) (c k).1.1 (c k).2), z) : ℝ≥0∞) ∂P)) := by
      intro z
      refine tendsto_lintegral_of_dominated_convergence (fun _ => (C : ℝ≥0∞))
        (fun j => measurable_coe_bcf g (fun ω => fun i => dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0) (φ i))
          (fun ω => fun k => dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0)
            (FirstPassS11atProducers.circleApprox (hr k) (c k).2 j))
          (fun _ => z) (hXsJ.comp (measurable_const.prodMk measurable_id))
          ((hYsJ j).comp (measurable_const.prodMk measurable_id)) measurable_const)
        (fun j => Eventually.of_forall fun ω => ENNReal.coe_le_coe.2 (hbd _))
        (by rw [lintegral_const, measure_univ, mul_one]; exact ENNReal.coe_ne_top)
        ?_
      filter_upwards [hfield] with ω hω
      have hpt : Tendsto (fun j : ℕ => ((fun i => dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0) (φ i)),
          (fun k => dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0)
            (FirstPassS11atProducers.circleApprox (hr k) (c k).2 j)), z))
          atTop (𝓝 ((fun i => dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0) (φ i)),
            (fun k => dmsShiftedCircle γ z (hcirc ω) (c k).1.1 (c k).2), z)) :=
        tendsto_const_nhds.prodMk_nhds ((hShift ω hω z).prodMk_nhds tendsto_const_nhds)
      exact ((ENNReal.continuous_coe.comp g.continuous).tendsto _).comp hpt
    refine tendsto_lintegral_of_dominated_convergence (fun _ => (C : ℝ≥0∞)) hmeasG
      (fun j => Eventually.of_forall fun z => ?_) ?_ (Eventually.of_forall fun z => hinner z)
    · calc ∫⁻ ω, (g _ : ℝ≥0∞) ∂P ≤ ∫⁻ _ω, (C : ℝ≥0∞) ∂P :=
            lintegral_mono fun ω => ENNReal.coe_le_coe.2 (hbd _)
        _ = (C : ℝ≥0∞) := by simp
    · rw [lintegral_const, Measure.restrict_apply_univ]
      exact ENNReal.mul_ne_top ENNReal.coe_ne_top measure_ball_lt_top.ne
  exact tendsto_nhds_unique hS2 (Tendsto.congr (fun j => (hLHS j).symm) hS3)

/-- **Step B (every measurable observation).** Two finite measures on the observation space, one built from the
measure family `ρ` and one from the DMS-shifted pairings, agree on bounded continuous tests by Step A, hence are
equal; integrating a measurable `Φ` against them gives the claim. -/
theorem keyMeasure {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (hW : IsWholePlaneGFF P hC hcirc)
    (ρ : Ω → Measure ℂ) (hρm : Measurable ρ) (hρfin : ∀ ω, IsFiniteMeasure (ρ ω))
    (hSub : ∀ Ψ : (((ℂ → ℝ) → ℝ) × ℂ) → ℝ≥0∞,
      Measurable[(pairingSigmaAlgebra (fun T : (ℂ → ℝ) → ℝ => T) univ).prod inferInstance] Ψ →
        ∫⁻ ω, ∫⁻ z, Ψ (hC ω, z) ∂(ρ ω) ∂P
          = ∫⁻ z in ball (0 : ℂ) 1, ∫⁻ ω, Ψ (dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0), z) ∂P ∂volume)
    {n m : ℕ} (φ : Fin n → ℂ → ℝ) (hφ : ∀ i, IsTestFunction univ (φ i))
    (c : Fin m → CircleParameter) (Φ : (Fin n → ℝ) × (Fin m → ℝ) × ℂ → ℝ≥0∞) (hΦ : Measurable Φ) :
    ∫⁻ ω, ∫⁻ z, Φ ((fun i => hC ω (φ i)), (fun k => hcirc ω (c k).1.1 (c k).2), z) ∂(ρ ω) ∂P
      = ∫⁻ z in ball (0 : ℂ) 1, ∫⁻ ω, Φ ((fun i => dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0) (φ i)),
          (fun k => dmsShiftedCircle γ z (hcirc ω) (c k).1.1 (c k).2), z) ∂P ∂volume := by
  have hr : ∀ k, 0 < (c k).1.1 := fun k => (c k).1.2
  have hXm : Measurable (fun ω => fun i => hC ω (φ i)) :=
    measurable_pi_iff.2 fun i => hW.measurable_pairing (φ i) (hφ i)
  have hYm : Measurable (fun ω => fun k => hcirc ω (c k).1.1 (c k).2) :=
    measurable_pi_iff.2 fun k => hW.measurable_circle _ _ (hr k)
  have hXsJ : Measurable (fun p : ℂ × Ω => fun i =>
      dmsShiftedPairing γ p.1 (hC p.2) (hcirc p.2 1 0) (φ i)) :=
    measurable_pi_iff.2 fun i => (measurable_eval_pairing (hφ i)).comp
      (FirstPassS11atProducers.measurable_dmsShiftedPairing P γ hC hcirc hW)
  have hYsC : Measurable (fun p : ℂ × Ω => fun k =>
      dmsShiftedCircle γ p.1 (hcirc p.2) (c k).1.1 (c k).2) := by
    refine measurable_pi_iff.2 fun k => ?_
    have h1 : Measurable (fun p : ℂ × Ω => hcirc p.2 (c k).1.1 (c k).2) :=
      (hW.measurable_circle _ _ (hr k)).comp measurable_snd
    have h2 : Measurable (fun p : ℂ × Ω => Real.circleAverage (dmsShift γ p.1) (c k).2 (c k).1.1) :=
      (measurable_circleAverage_dmsShift_centre γ (c k).2 (c k).1.1).comp measurable_fst
    have h3 : Measurable (fun p : ℂ × Ω => dmsConstant γ p.1 (hcirc p.2 1 0)) :=
      FirstPassS11atProducers.measurable_dmsConstant_joint γ (fun ω => hcirc ω 1 0)
        (hW.measurable_circle 1 0 one_pos)
    exact (h1.add h2).add h3
  -- the measures
  let X : Ω → Fin n → ℝ := fun ω i => hC ω (φ i)
  let Y : Ω → Fin m → ℝ := fun ω k => hcirc ω (c k).1.1 (c k).2
  let K : Ω → Measure ((Fin n → ℝ) × (Fin m → ℝ) × ℂ) := fun ω =>
    (ρ ω).map (fun z : ℂ => ((X ω, Y ω, z) : (Fin n → ℝ) × (Fin m → ℝ) × ℂ))
  let ML : Measure ((Fin n → ℝ) × (Fin m → ℝ) × ℂ) := P.bind K
  let Θ : ℂ × Ω → (Fin n → ℝ) × (Fin m → ℝ) × ℂ := fun p =>
    ((fun i => dmsShiftedPairing γ p.1 (hC p.2) (hcirc p.2 1 0) (φ i)),
      (fun k => dmsShiftedCircle γ p.1 (hcirc p.2) (c k).1.1 (c k).2), p.1)
  let MR : Measure ((Fin n → ℝ) × (Fin m → ℝ) × ℂ) :=
    ((volume.restrict (ball (0 : ℂ) 1)).prod P).map Θ
  have hΘm : Measurable Θ :=
    measurable_obs (fun p : ℂ × Ω => fun i => dmsShiftedPairing γ p.1 (hC p.2) (hcirc p.2 1 0) (φ i))
      (fun p : ℂ × Ω => fun k => dmsShiftedCircle γ p.1 (hcirc p.2) (c k).1.1 (c k).2)
      (fun p : ℂ × Ω => p.1) hXsJ hYsC measurable_fst
  have hXobs : ∀ ω, Measurable fun z : ℂ => ((X ω, Y ω, z) : (Fin n → ℝ) × (Fin m → ℝ) × ℂ) :=
    fun ω => measurable_const.prodMk (measurable_const.prodMk measurable_id)
  have hKm : Measurable K := by
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    have hT : MeasurableSet ((fun p : Ω × ℂ => ((X p.1, Y p.1, p.2) : (Fin n → ℝ) × (Fin m → ℝ) × ℂ)) ⁻¹' s) :=
      hs.preimage (measurable_obs (fun p : Ω × ℂ => X p.1) (fun p : Ω × ℂ => Y p.1) (fun p : Ω × ℂ => p.2)
        (hXm.comp measurable_fst) (hYm.comp measurable_fst) measurable_snd)
    have key := Kernel.measurable_kernel_prodMk_left_of_finite (κ := ⟨ρ, hρm⟩) hT (fun ω => hρfin ω)
    have heq : (fun ω => K ω s) = fun ω => ρ ω (Prod.mk ω ⁻¹' ((fun p : Ω × ℂ =>
        ((X p.1, Y p.1, p.2) : (Fin n → ℝ) × (Fin m → ℝ) × ℂ)) ⁻¹' s)) := by
      funext ω
      simp only [K]
      rw [Measure.map_apply (hXobs ω) hs]
      rfl
    rw [heq]
    exact key
  -- the two integral representations
  have hML : ∀ Φ' : (Fin n → ℝ) × (Fin m → ℝ) × ℂ → ℝ≥0∞, Measurable Φ' →
      ∫⁻ x, Φ' x ∂ML = ∫⁻ ω, ∫⁻ z, Φ' ((X ω, Y ω, z)) ∂(ρ ω) ∂P := by
    intro Φ' hΦ'
    show ∫⁻ x, Φ' x ∂(P.bind K) = _
    rw [Measure.lintegral_bind hKm.aemeasurable hΦ'.aemeasurable]
    refine lintegral_congr fun ω => ?_
    show ∫⁻ x, Φ' x ∂((ρ ω).map _) = _
    rw [lintegral_map hΦ' (hXobs ω)]
  have hMR : ∀ Φ' : (Fin n → ℝ) × (Fin m → ℝ) × ℂ → ℝ≥0∞, Measurable Φ' →
      ∫⁻ x, Φ' x ∂MR = ∫⁻ z in ball (0 : ℂ) 1, ∫⁻ ω, Φ' (Θ (z, ω)) ∂P ∂volume := by
    intro Φ' hΦ'
    show ∫⁻ x, Φ' x ∂(((volume.restrict (ball (0 : ℂ) 1)).prod P).map Θ) = _
    rw [lintegral_map hΦ' hΘm]
    exact lintegral_prod (fun p => Φ' (Θ p)) (hΦ'.comp hΘm).aemeasurable
  -- finiteness of ML
  have hmass : ∫⁻ ω, ρ ω univ ∂P = volume (ball (0 : ℂ) 1) := by
    have h1 := hSub (fun _ => 1) measurable_const
    simpa [lintegral_const, Measure.restrict_apply_univ] using h1
  have hMLfin : IsFiniteMeasure ML := by
    refine ⟨?_⟩
    have h1 := hML (fun _ => 1) measurable_const
    simp only [lintegral_const, one_mul, hmass] at h1
    rw [h1]
    exact measure_ball_lt_top
  -- equality of the two measures on bounded continuous tests
  have hext : ML = MR := by
    refine ext_of_forall_lintegral_eq_of_IsFiniteMeasure fun g => ?_
    have hm : Measurable (fun x : (Fin n → ℝ) × (Fin m → ℝ) × ℂ => (g x : ℝ≥0∞)) :=
      measurable_coe_nnreal_ennreal.comp g.continuous.measurable
    exact (hML _ hm).trans ((keyBCF P γ hC hcirc hW ρ hρm hρfin hSub φ hφ c g).trans (hMR _ hm).symm)
  calc ∫⁻ ω, ∫⁻ z, Φ ((fun i => hC ω (φ i)), (fun k => hcirc ω (c k).1.1 (c k).2), z) ∂(ρ ω) ∂P
      = ∫⁻ x, Φ x ∂ML := (hML Φ hΦ).symm
    _ = ∫⁻ x, Φ x ∂MR := by rw [hext]
    _ = _ := hMR Φ hΦ

/-- **MQ-lh-22: the finite-family marked tilt identity from the Sub input.** For every whole-plane GFF `(hC, hcirc)`
and every `α = 0` LQG measure `μ` of `hcirc` at `0 < γ < 2`, the identity of `DMSFiniteTiltPosStmt`
(RootedDominationJointPosDerived.lean:27) follows from the pairing-level marked identity `DMSLemmaA10WholePlaneMarkedSub`
(FirstPass/Frozen/S11i.lean:59; DMS arXiv:1409.7055v4, Lemma A.10). The circle profile is measurable and the LQG measure
has a measurable version (`LQGMeasureOfProfileMeasurableFrozen`, proved in ProfileDecoderDerived.lean:401). -/
theorem dMSFiniteTiltPos_of_sub
    (hSub : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), DMSLemmaA10WholePlaneMarkedSub P γ hC hcirc μ) :
    DMSFiniteTiltPosStmt.{u} := by
  intro Ω _ P γ hC hcirc μ hW hL hγ0 hγ2 n m φ c Φ hφ hΦ
  have : IsProbabilityMeasure P := hW.isProbabilityMeasure
  obtain ⟨F, hFm, -, hF⟩ := hW.exists_measurable_continuous_circle_version
  obtain ⟨Dec, hDecm, hμDec, -⟩ :=
    lqgMeasureOfProfileMeasurable_derived Ω P γ 0 hC hcirc μ F hW hL hFm hF
  have hμ'm : Measurable (fun ω => Dec (F ω)) := hDecm.comp hFm
  have hL' : IsLQGMeasureOfField P γ 0 hcirc (fun ω => Dec (F ω)) := by
    unfold IsLQGMeasureOfField IsLQGMeasure at hL ⊢
    filter_upwards [hL, hμDec] with ω h1 h2
    rw [← h2]
    exact h1
  have hSub' := hSub Ω P γ hC hcirc (fun ω => Dec (F ω))
  have hmass : ∫⁻ ω, Dec (F ω) (ball (0 : ℂ) 1) ∂P = volume (ball (0 : ℂ) 1) := by
    have h1 := hSub' hW hL' hγ0 hγ2 (fun _ => 1) measurable_const
    simpa [lintegral_const, Measure.restrict_apply_univ] using h1
  have hmeasB : Measurable fun ω => Dec (F ω) (ball (0 : ℂ) 1) :=
    (Measure.measurable_coe measurableSet_ball).comp hμ'm
  have hfin : ∀ᵐ ω ∂P, Dec (F ω) (ball (0 : ℂ) 1) < ∞ :=
    ae_lt_top hmeasB (by rw [hmass]; exact measure_ball_lt_top.ne)
  have hres : ∀ ω, Dec (F ω) (ball (0 : ℂ) 1) < ∞ →
      finRestr (fun ω => Dec (F ω)) ω = (Dec (F ω)).restrict (ball (0 : ℂ) 1) := by
    intro ω hω
    simp [finRestr, hω]
  have hρm : Measurable (finRestr (fun ω => Dec (F ω))) := measurable_finRestr hμ'm
  have hρfin : ∀ ω, IsFiniteMeasure (finRestr (fun ω => Dec (F ω)) ω) :=
    isFiniteMeasure_finRestr _
  have hSubρ : ∀ Ψ : (((ℂ → ℝ) → ℝ) × ℂ) → ℝ≥0∞,
      Measurable[(pairingSigmaAlgebra (fun T : (ℂ → ℝ) → ℝ => T) univ).prod inferInstance] Ψ →
        ∫⁻ ω, ∫⁻ z, Ψ (hC ω, z) ∂(finRestr (fun ω => Dec (F ω)) ω) ∂P
          = ∫⁻ z in ball (0 : ℂ) 1, ∫⁻ ω, Ψ (dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0), z) ∂P ∂volume := by
    intro Ψ hΨ
    refine Eq.trans ?_ (hSub' hW hL' hγ0 hγ2 Ψ hΨ)
    refine lintegral_congr_ae ?_
    filter_upwards [hfin] with ω hω
    rw [hres ω hω]
  have hkey := keyMeasure P γ hC hcirc hW (finRestr (fun ω => Dec (F ω))) hρm hρfin hSubρ φ hφ c Φ hΦ
  refine (lintegral_congr_ae ?_).trans hkey
  filter_upwards [hμDec, hfin] with ω h1 h2
  rw [h1, hres ω h2]

end DMSFiniteTiltPosDerived

end HarmonicBalls

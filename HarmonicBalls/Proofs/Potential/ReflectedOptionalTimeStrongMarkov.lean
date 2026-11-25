import HarmonicBalls.Proofs.Brownian.OptionalTimeStrongMarkov
import HarmonicBalls.Proofs.Brownian.PlanarBrownianMotion
import HarmonicBalls.Proofs.Brownian.PlanarHeatFeller
import HarmonicBalls.Proofs.Potential.ReflectedClockIdentification

/-!
# The strong Markov property of reflected Brownian motion at optional times

Let `T` be an optional time of the canonical filtration of the path (`{T < t} ∈ F⁰_t` for every
`t`), possibly infinite. The strong Markov property at optional times
(`continuousProcess_restrict_map_shift_optionalTime_lt_top`, Revuz–Yor (1999), Theorem III.3.7)
applies to planar Brownian motion, the continuous process of the planar heat semigroup. Reflected
Brownian motion in the unit square `K₀ = closedSquare 0 1` is the image of planar Brownian motion
under the fold `ω ↦ squareFold 0 1 ∘ ω`; the fold maps `F⁰_t` into `F⁰_t`, commutes with the time
shifts, and the law of reflected Brownian motion depends on its start only through the fold
(`reflectedPlanarBrownianMotion_zero_one_squareFold`). Hence the strong Markov property passes to
reflected Brownian motion (Fukushima–Oshima–Takeda (2011), Section A.2), in the forms used for
additive functionals:

* the *restart form*: on `A ∩ {T < ∞}`, `A ∈ F_{T+}`, the law of `θ_T b` is the mixture of the
  laws of reflected Brownian motion from `b_T`;
* the *transfer of full events*: an event of probability one from every start in `K₀` holds for
  the path shifted at `T`, almost surely on `{T < ∞}`;
* the *parameter form*: for a variable `V` of `F_{T+}` and a measurable `H ≥ 0`,
  `E_x[H(V, θ_T b); T < ∞] = E_x[∫ H(V, b') dQ_{b_T}(b'); T < ∞]`.

## Main results

* `planarBrownianMotion_restrict_map_shift_optionalTime`: the restart form for planar Brownian
  motion.
* `comap_squareFoldCM_comp_canonicalFiltration_le`: the fold maps `F⁰_t` into `F⁰_t`.
* `reflected_restrict_map_shift_optionalTime`: the restart form for reflected Brownian motion.
* `ae_forall_mem_closedSquare_reflected`: reflected paths stay in `K₀`.
* `reflected_inter_shift_preimage_optionalTime`, `ae_shift_mem_of_forall_reflected_eq_one`,
  `lintegral_reflected_shift_optionalTime_param`, `lintegral_reflected_shift_optionalTime_time`.

Credit: the planar statements and the set, transfer and parameter forms follow
MatedCRT/FirstPass/Derived/PlanarOptionalTimeStrongMarkov.lean of the IDLA-Mated-CRT
formalization. Source commit: IDLA-Mated-CRT ea80b70d7b8c8c59778c86b6bd4b06c1060b6fbe.
Changes: `planarLaw` replaced by `planarBrownianMotion`; the forms after the restart form are
stated for reflected Brownian motion in the unit square (`reflectedPlanarBrownianMotion 0 1`), with
the full events of the transfer form required only from starts in `K₀`; the passage from planar to
reflected Brownian motion through the fold is new here.
-/

open MeasureTheory ProbabilityTheory Set Filter MarkovProcess
open scoped ENNReal NNReal

namespace HarmonicBalls.OptionalTime

/-- **Strong Markov property of planar Brownian motion at an optional time, restart form.** -/
theorem planarBrownianMotion_restrict_map_shift_optionalTime (z : ℂ)
    (T : ContinuousPath ℂ → WithTop ℝ≥0)
    (hT : ∀ t : ℝ≥0, MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) t]
      {ω | T ω < t})
    (A : Set (ContinuousPath ℂ))
    (hA : ∀ t : ℝ≥0, MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) t]
      (A ∩ {ω | T ω < t})) :
    ((planarBrownianMotion z).restrict (A ∩ {ω | T ω < ⊤})).map
        (fun ω ↦ ContinuousPath.shift ((T ω).untopD 0) ω) =
      Kernel.comap planarBrownianMotion (fun ω ↦ ω ((T ω).untopD 0))
          (measurable_eval_untopD hT) ∘ₘ
        ((planarBrownianMotion z).restrict (A ∩ {ω | T ω < ⊤})) := by
  have h := continuousProcess_restrict_map_shift_optionalTime_lt_top planarHeatSemigroup
    isConservative_planarHeatSemigroup isFellerKernelSemigroup_planarHeatSemigroup
    kolmogorovRegular_planarHeatSemigroup z T hT A hA
  rw [← planarBrownianMotion_eq_continuousProcess] at h
  exact h

/-! ### The fold and the canonical filtration -/

/-- The fold `ω ↦ squareFold 0 1 ∘ ω` maps `F⁰_t` into `F⁰_t`. -/
theorem comap_squareFoldCM_comp_canonicalFiltration_le (t : ℝ≥0) :
    MeasurableSpace.comap (fun ω : ContinuousPath ℂ => (squareFoldCM 0 1).comp ω)
        (ContinuousPath.canonicalFiltration (alpha := ℂ) t) ≤
      ContinuousPath.canonicalFiltration (alpha := ℂ) t := by
  show MeasurableSpace.comap _ (⨆ s : Set.Iic t,
    MeasurableSpace.comap (ContinuousPath.coordinateProcess (alpha := ℂ) s) inferInstance) ≤ _
  rw [MeasurableSpace.comap_iSup]
  refine iSup_le fun s => ?_
  rw [MeasurableSpace.comap_comp]
  have hs : Measurable[ContinuousPath.canonicalFiltration (alpha := ℂ) t]
      (ContinuousPath.coordinateProcess (alpha := ℂ) (s : ℝ≥0)) := by
    rw [measurable_iff_comap_le]
    exact le_iSup (fun s : Set.Iic t =>
      MeasurableSpace.comap (ContinuousPath.coordinateProcess (alpha := ℂ) s) inferInstance) s
  have h : Measurable[ContinuousPath.canonicalFiltration (alpha := ℂ) t]
      (squareFold 0 1 ∘ ContinuousPath.coordinateProcess (alpha := ℂ) (s : ℝ≥0)) :=
    (continuous_squareFold 0 1).measurable.comp hs
  exact h.comap_le

/-- An `F⁰_t`-event of the folded path is an `F⁰_t`-event of the path. -/
theorem measurableSet_preimage_squareFoldCM_comp {t : ℝ≥0} {S : Set (ContinuousPath ℂ)}
    (hS : MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) t] S) :
    MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) t]
      ((fun ω : ContinuousPath ℂ => (squareFoldCM 0 1).comp ω) ⁻¹' S) :=
  comap_squareFoldCM_comp_canonicalFiltration_le t _ ⟨S, hS, rfl⟩

/-- The fold commutes with the time shifts. -/
theorem shift_squareFoldCM_comp (s : ℝ≥0) (ω : ContinuousPath ℂ) :
    ContinuousPath.shift s ((squareFoldCM 0 1).comp ω) =
      (squareFoldCM 0 1).comp (ContinuousPath.shift s ω) := by
  ext u
  rfl

/-- Reflected paths stay in the unit square. -/
theorem ae_forall_mem_closedSquare_reflected (x : ℂ) :
    ∀ᵐ b ∂reflectedPlanarBrownianMotion 0 1 x, ∀ t, b t ∈ closedSquare 0 1 := by
  have hclosed : IsClosed {b : ContinuousPath ℂ | ∀ t, b t ∈ closedSquare 0 1} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun t =>
      (isCompact_closedSquare 0 1).isClosed.preimage (continuous_eval_const t)
  rw [reflectedPlanarBrownianMotion, Kernel.map_apply _ (measurable_comp_squareFoldCM 0 1),
    ae_map_iff (measurable_comp_squareFoldCM 0 1).aemeasurable hclosed.measurableSet]
  exact Eventually.of_forall fun ω t => squareFold_zero_one_mem (ω t)

/-! ### The strong Markov property of reflected Brownian motion -/

/-- **Strong Markov property of reflected Brownian motion at an optional time, restart form.**
For an optional time `T` and an event `A` of `F_{T+}`, on `A ∩ {T < ∞}` the law of the path
shifted at `T` is the mixture of the laws of reflected Brownian motion from the state at `T`. -/
theorem reflected_restrict_map_shift_optionalTime (x : ℂ)
    (T : ContinuousPath ℂ → WithTop ℝ≥0)
    (hT : ∀ t : ℝ≥0, MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) t]
      {ω | T ω < t})
    (A : Set (ContinuousPath ℂ))
    (hA : ∀ t : ℝ≥0, MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) t]
      (A ∩ {ω | T ω < t})) :
    ((reflectedPlanarBrownianMotion 0 1 x).restrict (A ∩ {ω | T ω < ⊤})).map
        (fun ω ↦ ContinuousPath.shift ((T ω).untopD 0) ω) =
      Kernel.comap (reflectedPlanarBrownianMotion 0 1) (fun ω ↦ ω ((T ω).untopD 0))
          (measurable_eval_untopD hT) ∘ₘ
        ((reflectedPlanarBrownianMotion 0 1 x).restrict (A ∩ {ω | T ω < ⊤})) := by
  have hfm : Measurable fun ω : ContinuousPath ℂ => (squareFoldCM 0 1).comp ω :=
    measurable_comp_squareFoldCM 0 1
  have hT' : ∀ t : ℝ≥0, MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) t]
      {ω | T ((squareFoldCM 0 1).comp ω) < t} := fun t =>
    measurableSet_preimage_squareFoldCM_comp (hT t)
  have hA' : ∀ t : ℝ≥0, MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) t]
      ((fun ω : ContinuousPath ℂ => (squareFoldCM 0 1).comp ω) ⁻¹' A ∩
        {ω | T ((squareFoldCM 0 1).comp ω) < t}) := fun t =>
    measurableSet_preimage_squareFoldCM_comp (hA t)
  have hSm : MeasurableSet (A ∩ {ω | T ω < ⊤}) :=
    (iSup_le fun t => (ContinuousPath.canonicalFiltration (alpha := ℂ)).le t) _
      (measurableSet_inter_lt_top hA)
  have hshm : Measurable fun ω : ContinuousPath ℂ => ContinuousPath.shift ((T ω).untopD 0) ω :=
    ContinuousPath.measurable_shift_of_measurable _ (measurable_untopD hT)
  have hshm' : Measurable fun ω : ContinuousPath ℂ =>
      ContinuousPath.shift ((T ((squareFoldCM 0 1).comp ω)).untopD 0) ω :=
    ContinuousPath.measurable_shift_of_measurable _ (measurable_untopD hT')
  have hcomm : (fun ω : ContinuousPath ℂ => ContinuousPath.shift ((T ω).untopD 0) ω) ∘
        (fun ω : ContinuousPath ℂ => (squareFoldCM 0 1).comp ω) =
      (fun ω : ContinuousPath ℂ => (squareFoldCM 0 1).comp ω) ∘
        fun ω : ContinuousPath ℂ =>
          ContinuousPath.shift ((T ((squareFoldCM 0 1).comp ω)).untopD 0) ω := by
    funext ω
    exact shift_squareFoldCM_comp _ ω
  have hQ : reflectedPlanarBrownianMotion 0 1 x =
      (planarBrownianMotion x).map fun ω : ContinuousPath ℂ => (squareFoldCM 0 1).comp ω :=
    Kernel.map_apply _ hfm x
  have hP := planarBrownianMotion_restrict_map_shift_optionalTime x _ hT' _ hA'
  rw [hQ, Measure.restrict_map hfm hSm, Measure.map_map hshm hfm, hcomm,
    ← Measure.map_map hfm hshm']
  have hpre : (fun ω : ContinuousPath ℂ => (squareFoldCM 0 1).comp ω) ⁻¹'
      (A ∩ {ω | T ω < ⊤}) =
      (fun ω : ContinuousPath ℂ => (squareFoldCM 0 1).comp ω) ⁻¹' A ∩
        {ω | T ((squareFoldCM 0 1).comp ω) < ⊤} := rfl
  rw [hpre, hP, Measure.map_comp _ _ hfm]
  ext S hS
  rw [Measure.bind_apply hS (Kernel.aemeasurable _), Measure.bind_apply hS (Kernel.aemeasurable _),
    lintegral_map (Kernel.measurable_coe _ hS) hfm]
  refine lintegral_congr fun ω => ?_
  rw [Kernel.map_apply' _ hfm _ hS, Kernel.comap_apply, Kernel.comap_apply]
  set w := ω ((T ((squareFoldCM 0 1).comp ω)).untopD 0) with hw
  calc planarBrownianMotion w ((fun ω : ContinuousPath ℂ => (squareFoldCM 0 1).comp ω) ⁻¹' S)
      = reflectedPlanarBrownianMotion 0 1 w S := by
        rw [reflectedPlanarBrownianMotion, Kernel.map_apply' _ hfm _ hS]
    _ = reflectedPlanarBrownianMotion 0 1 (squareFold 0 1 w) S := by
        rw [reflectedPlanarBrownianMotion_zero_one_squareFold]
    _ = _ := rfl

/-- **Strong Markov property at an optional time, set form.** For an event `A` of `F_{T+}` and a
measurable path event `G`, `Q_x(A, T < ∞, θ_T b ∈ G) = E_x[Q_{b_T}(G); A, T < ∞]`. -/
theorem reflected_inter_shift_preimage_optionalTime (x : ℂ)
    (T : ContinuousPath ℂ → WithTop ℝ≥0)
    (hT : ∀ t : ℝ≥0, MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) t]
      {ω | T ω < t})
    (A : Set (ContinuousPath ℂ))
    (hA : ∀ t : ℝ≥0, MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) t]
      (A ∩ {ω | T ω < t}))
    {G : Set (ContinuousPath ℂ)} (hG : MeasurableSet G) :
    reflectedPlanarBrownianMotion 0 1 x (A ∩ {ω | T ω < ⊤} ∩
        (fun ω ↦ ContinuousPath.shift ((T ω).untopD 0) ω) ⁻¹' G) =
      ∫⁻ ω in A ∩ {ω | T ω < ⊤}, reflectedPlanarBrownianMotion 0 1 (ω ((T ω).untopD 0)) G
        ∂reflectedPlanarBrownianMotion 0 1 x := by
  have hshift : Measurable (fun ω : ContinuousPath ℂ ↦ ContinuousPath.shift ((T ω).untopD 0) ω) :=
    ContinuousPath.measurable_shift_of_measurable _ (measurable_untopD hT)
  have h := congrArg (fun m : Measure (ContinuousPath ℂ) => m G)
    (reflected_restrict_map_shift_optionalTime x T hT A hA)
  rw [Measure.map_apply hshift hG, Measure.restrict_apply (hshift hG),
    Measure.bind_apply hG (Kernel.aemeasurable _)] at h
  simp only [Kernel.comap_apply] at h
  rw [inter_comm]
  exact h

/-- **Transfer of full events through an optional time.** If a measurable path event `G` has
probability one for reflected Brownian motion from every start in `K₀`, then almost surely, on
`{T < ∞}`, the path shifted at `T` lies in `G`. -/
theorem ae_shift_mem_of_forall_reflected_eq_one (x : ℂ)
    (T : ContinuousPath ℂ → WithTop ℝ≥0)
    (hT : ∀ t : ℝ≥0, MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) t]
      {ω | T ω < t})
    {G : Set (ContinuousPath ℂ)} (hG : MeasurableSet G)
    (h1 : ∀ y ∈ closedSquare 0 1, reflectedPlanarBrownianMotion 0 1 y G = 1) :
    ∀ᵐ ω ∂reflectedPlanarBrownianMotion 0 1 x,
      T ω < ⊤ → ContinuousPath.shift ((T ω).untopD 0) ω ∈ G := by
  have hA : ∀ t : ℝ≥0, MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) t]
      (univ ∩ {ω | T ω < t}) := fun t => by rw [univ_inter]; exact hT t
  have h := reflected_inter_shift_preimage_optionalTime x T hT univ hA hG.compl
  have h0 : ∫⁻ ω in univ ∩ {ω | T ω < ⊤},
      reflectedPlanarBrownianMotion 0 1 (ω ((T ω).untopD 0)) Gᶜ
        ∂reflectedPlanarBrownianMotion 0 1 x = 0 := by
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    refine ae_restrict_of_ae ?_
    filter_upwards [ae_forall_mem_closedSquare_reflected x] with ω hω
    exact (prob_compl_eq_zero_iff hG).2 (h1 _ (hω _))
  rw [h0] at h
  rw [ae_iff]
  refine measure_mono_null (fun ω hω => ?_) h
  have hω' : ¬(T ω < ⊤ → ContinuousPath.shift ((T ω).untopD 0) ω ∈ G) := hω
  rw [not_imp] at hω'
  exact ⟨⟨mem_univ _, hω'.1⟩, hω'.2⟩

/-- **The time `T` is `F_{T+}`-measurable**: for every Borel set `B` of times and every `t`,
`{T ∈ B} ∩ {T < t} ∈ F⁰_t` (on `{T < t}`, `T` is finite). -/
theorem measurableSet_untopD_preimage_inter_lt
    {T : ContinuousPath ℂ → WithTop ℝ≥0}
    (hT : ∀ t : ℝ≥0, MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) t]
      {ω | T ω < t})
    {B : Set ℝ≥0} (hB : MeasurableSet B) (t : ℝ≥0) :
    MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) t]
      ((fun ω => (T ω).untopD 0) ⁻¹' B ∩ {ω | T ω < t}) := by
  set g : ContinuousPath ℂ → ℝ≥0 := fun ω => (min (T ω) (t : WithTop ℝ≥0)).untopD 0 with hg
  have hgm : Measurable[ContinuousPath.canonicalFiltration (alpha := ℂ) t] g := by
    refine measurable_of_Iio fun s => ?_
    have hset : g ⁻¹' Iio s = {ω | T ω < (s : WithTop ℝ≥0)} ∪ {_ω | t < s} := by
      ext ω
      simp only [hg, mem_preimage, mem_Iio, mem_union, mem_ofPred_eq]
      rcases eq_or_ne (T ω) ⊤ with h | h
      · rw [h, min_eq_right le_top, WithTop.untopD_coe]
        exact ⟨Or.inr, fun h' => h'.resolve_left not_top_lt⟩
      · obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 h
        rw [← ha, ← WithTop.coe_min, WithTop.untopD_coe, WithTop.coe_lt_coe, min_lt_iff]
    rw [hset]
    by_cases hts : t < s
    · simp [hts]
    · have hst : s ≤ t := le_of_not_gt hts
      simp only [hts, ofPred_false, union_empty]
      exact (ContinuousPath.canonicalFiltration (alpha := ℂ)).mono hst _ (hT s)
  have hset : (fun ω => (T ω).untopD 0) ⁻¹' B ∩ {ω | T ω < t} = g ⁻¹' B ∩ {ω | T ω < t} := by
    ext ω
    simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq, and_congr_left_iff]
    intro hlt
    obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt hlt)
    show (T ω).untopD 0 ∈ B ↔ (min (T ω) (t : WithTop ℝ≥0)).untopD 0 ∈ B
    rw [← ha] at hlt ⊢
    rw [← WithTop.coe_min, min_eq_left (WithTop.coe_lt_coe.1 hlt).le]
  rw [hset]
  exact (hgm hB).inter (hT t)

/-- **Strong Markov property at an optional time, parameter form.** Let `V` be a measurable
variable of `F_{T+}` (`{V ∈ B} ∩ {T < t} ∈ F⁰_t` for every measurable `B` and every `t`) and
`H ≥ 0` measurable on pairs. Then
`E_x[H(V, θ_T b); T < ∞] = E_x[∫ H(V, b') dQ_{b_T}(b'); T < ∞]`. -/
theorem lintegral_reflected_shift_optionalTime_param {β : Type*} [MeasurableSpace β] (x : ℂ)
    (T : ContinuousPath ℂ → WithTop ℝ≥0)
    (hT : ∀ t : ℝ≥0, MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) t]
      {ω | T ω < t})
    (V : ContinuousPath ℂ → β) (hVm : Measurable V)
    (hV : ∀ B : Set β, MeasurableSet B → ∀ t : ℝ≥0,
      MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) t] (V ⁻¹' B ∩ {ω | T ω < t}))
    {H : β × ContinuousPath ℂ → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ (ω : ContinuousPath ℂ) in {ω | T ω < ⊤},
        H (V ω, ContinuousPath.shift ((T ω).untopD 0) ω) ∂reflectedPlanarBrownianMotion 0 1 x =
      ∫⁻ (ω : ContinuousPath ℂ) in {ω | T ω < ⊤},
        ∫⁻ ω', H (V ω, ω') ∂reflectedPlanarBrownianMotion 0 1 (ω ((T ω).untopD 0))
        ∂reflectedPlanarBrownianMotion 0 1 x := by
  set μ := (reflectedPlanarBrownianMotion 0 1 x).restrict {ω | T ω < ⊤} with hμ
  set s : ContinuousPath ℂ → ContinuousPath ℂ :=
    fun ω ↦ ContinuousPath.shift ((T ω).untopD 0) ω with hs
  have hsm : Measurable s := ContinuousPath.measurable_shift_of_measurable _ (measurable_untopD hT)
  have hpm : Measurable fun ω => (V ω, s ω) := hVm.prodMk hsm
  set κ₀ := Kernel.comap (reflectedPlanarBrownianMotion 0 1)
    (fun ω : ContinuousPath ℂ ↦ ω ((T ω).untopD 0)) (measurable_eval_untopD hT) with hκ₀
  set κ := Kernel.deterministic V hVm ×ₖ κ₀ with hκ
  have hκapp : ∀ ω, κ ω =
      (reflectedPlanarBrownianMotion 0 1 (ω ((T ω).untopD 0))).map (Prod.mk (V ω)) := by
    intro ω
    rw [hκ, Kernel.prod_apply, Kernel.deterministic_apply, Measure.dirac_prod, hκ₀,
      Kernel.comap_apply]
  have heq : μ.map (fun ω => (V ω, s ω)) = κ ∘ₘ μ := by
    refine ext_of_generate_finite _ generateFrom_prod.symm isPiSystem_prod ?_ ?_
    · rintro _ ⟨B, hB, G, hG, rfl⟩
      replace hB : MeasurableSet B := hB
      replace hG : MeasurableSet G := hG
      have h1 : ∀ ω, κ ω (B ×ˢ G) = (V ⁻¹' B).indicator
          (fun ω => reflectedPlanarBrownianMotion 0 1 (ω ((T ω).untopD 0)) G) ω := by
        intro ω
        rw [hκ, Kernel.prod_apply, Measure.prod_prod, Kernel.deterministic_apply, hκ₀,
          Kernel.comap_apply, Measure.dirac_apply' _ hB]
        by_cases h : V ω ∈ B <;> simp [h]
      rw [Measure.map_apply hpm (hB.prod hG), Measure.bind_apply (hB.prod hG)
        (Kernel.aemeasurable _)]
      simp_rw [h1]
      rw [lintegral_indicator (hVm hB), hμ, Measure.restrict_restrict (hVm hB),
        Measure.restrict_apply (hpm (hB.prod hG)),
        ← reflected_inter_shift_preimage_optionalTime x T hT _ (hV B hB) hG]
      congr 1
      ext ω
      simp only [mem_inter_iff, mem_preimage, mem_prod, mem_ofPred_eq, hs]
      tauto
    · rw [Measure.map_apply hpm MeasurableSet.univ,
        Measure.bind_apply MeasurableSet.univ (Kernel.aemeasurable _)]
      simp [measure_univ]
  rw [← lintegral_map hH hpm, heq, Measure.lintegral_bind (Kernel.aemeasurable _) hH.aemeasurable]
  refine lintegral_congr fun ω => ?_
  rw [hκapp, lintegral_map hH measurable_prodMk_left]

/-- **Strong Markov property at an optional time, parameter form with `V = T`.** -/
theorem lintegral_reflected_shift_optionalTime_time (x : ℂ)
    (T : ContinuousPath ℂ → WithTop ℝ≥0)
    (hT : ∀ t : ℝ≥0, MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) t]
      {ω | T ω < t})
    {H : ℝ≥0 × ContinuousPath ℂ → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ (ω : ContinuousPath ℂ) in {ω | T ω < ⊤},
        H ((T ω).untopD 0, ContinuousPath.shift ((T ω).untopD 0) ω)
          ∂reflectedPlanarBrownianMotion 0 1 x =
      ∫⁻ (ω : ContinuousPath ℂ) in {ω | T ω < ⊤},
        ∫⁻ ω', H ((T ω).untopD 0, ω') ∂reflectedPlanarBrownianMotion 0 1 (ω ((T ω).untopD 0))
        ∂reflectedPlanarBrownianMotion 0 1 x :=
  lintegral_reflected_shift_optionalTime_param x T hT _ (measurable_untopD hT)
    (fun _ hB t => measurableSet_untopD_preimage_inter_lt hT hB t) hH

end HarmonicBalls.OptionalTime

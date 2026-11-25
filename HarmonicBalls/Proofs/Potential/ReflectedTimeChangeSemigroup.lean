import HarmonicBalls.Proofs.Potential.ReflectedClockOptionalAdditivity

/-!
# The semigroup property of the time change of reflected Brownian motion by a clock

Let `A` be a positive continuous additive functional of reflected Brownian motion in the unit
square `K₀` (`IsUnitSquarePCAF A`) and `τ_r = inf {t | r < A_t}` the right inverse of the clock
(`pcafClockInverse`). Fix a start `z ∈ K₀` from which the clock is almost surely unbounded. Then:

* `τ_r` agrees almost surely with an optional time of the canonical filtration
  (`exists_optionalTime_ae_eq_pcafClockInverse`; Revuz–Yor (1999), Chapter X, Section 1 and
  Proposition V.1.1; Fukushima–Oshima–Takeda (2011), Section A.3): from `F⁰_q`-measurable versions
  `g_q` of `A_q` at the rational times, the rational inverse clock `inf {q | r < g_q}` is optional;
* the time change is additive: `τ_{r+v} = τ_r + τ̄_v ∘ θ_{τ_r}`, where `τ̄` is the right inverse of
  the rational-time regularization `Ā` (`ae_pcafClockInverse_add_eq_shift`);
* the strong Markov property holds at `τ_r` (`lintegral_shift_pcafClockInverse_eq`);
* the transition probabilities of the time-changed process `Y_u = b_{τ_u}` satisfy the semigroup
  property (Revuz–Yor (1999), Chapter X, Section 1; Fukushima–Oshima–Takeda (2011), Section 6.2):
  `Q_z[b_{τ_{v+u}} ∈ S] = E_z[Q_{b_{τ_v}}[b_{τ_u} ∈ S]]`
  (`reflected_eval_pcafClockInverse_add_mem`).

The event `{b_{τ_u} ∈ S}` is written with the raw clock and need not be measurable; it agrees
almost surely, from every start in `K₀`, with the measurable event written with `Ā`
(`unitSquareTimeChangeRegularized`).

Credit: the proofs follow MatedCRT/FirstPass/Derived/RevuzOptionalClockInverse.lean,
RevuzMarkovAgainstClock.lean and RevuzTimeChangeSemigroup.lean of the IDLA-Mated-CRT
formalization, written there for planar Brownian motion. Source commit: IDLA-Mated-CRT
ea80b70d7b8c8c59778c86b6bd4b06c1060b6fbe.
Changes: planar Brownian motion (`planarLaw`, `IsPCAF`, `regularize`, `clockInverse`,
`pathFiltration`) replaced by reflected Brownian motion in the unit square
(`reflectedPlanarBrownianMotion 0 1`, `IsUnitSquarePCAF`, `clockRationalRegularization`,
`pcafClockInverse`, `pathNaturalFiltration`), with starts in `K₀`; the hypothesis `GoodClock` of
the source is replaced by the only part of it the proofs use, that the clock is almost surely
unbounded from the start considered; only the results used for the semigroup property are kept;
proofs otherwise as in the source.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology MarkovProcess
open scoped ENNReal NNReal

namespace HarmonicBalls

/-! ### The right inverse of the clock as an optional time -/

/-- The natural `σ`-field `F⁰_t` of the path is contained in the canonical filtration at
time `t`. -/
theorem pathNaturalFiltration_le_canonicalFiltration (t : ℝ≥0) :
    pathNaturalFiltration t ≤ ContinuousPath.canonicalFiltration (alpha := ℂ) t := by
  show _ ≤ ⨆ s : Set.Iic t,
    MeasurableSpace.comap (ContinuousPath.coordinateProcess (alpha := ℂ) s) inferInstance
  exact iSup₂_le fun s hs => le_iSup_of_le (⟨s, hs⟩ : Set.Iic t) le_rfl

/-- The rational inverse clock: for functionals `g q` read at the rational times `q`,
`inf {q ∈ ℚ≥0 | r < g_q ω}` in `[0, ∞]`. -/
noncomputable def rationalPCAFClockInverse (g : ℚ≥0 → ContinuousPath ℂ → ℝ≥0) (r : ℝ≥0)
    (ω : ContinuousPath ℂ) : WithTop ℝ≥0 :=
  ⨅ (q : ℚ≥0) (_ : r < g q ω), ((q : ℝ≥0) : WithTop ℝ≥0)

theorem rationalPCAFClockInverse_lt_iff {g : ℚ≥0 → ContinuousPath ℂ → ℝ≥0} {r : ℝ≥0}
    {ω : ContinuousPath ℂ} {t : WithTop ℝ≥0} :
    rationalPCAFClockInverse g r ω < t ↔
      ∃ q : ℚ≥0, r < g q ω ∧ ((q : ℝ≥0) : WithTop ℝ≥0) < t := by
  simp only [rationalPCAFClockInverse, iInf_lt_iff, exists_prop]

/-- **The rational inverse clock is an optional time.** If every `g_q` is `F⁰_q`-measurable, then
`{inf {q | r < g_q} < t} = ⋃_{q < t} {r < g_q}` lies in the canonical filtration at time `t`. -/
theorem measurableSet_rationalPCAFClockInverse_lt {g : ℚ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hg : ∀ q : ℚ≥0, Measurable[pathNaturalFiltration q] (g q)) (r t : ℝ≥0) :
    MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) t]
      {ω | rationalPCAFClockInverse g r ω < t} := by
  have hset : {ω | rationalPCAFClockInverse g r ω < t} =
      ⋃ (q : ℚ≥0) (_ : (q : ℝ≥0) < t), {ω | r < g q ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, rationalPCAFClockInverse_lt_iff,
      WithTop.coe_lt_coe, exists_prop]
    exact exists_congr fun q => and_comm
  rw [hset]
  refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun hq => ?_
  have hm : Measurable[ContinuousPath.canonicalFiltration (alpha := ℂ) t] (g q) :=
    (hg q).mono ((pathNaturalFiltration_le_canonicalFiltration q).trans
      ((ContinuousPath.canonicalFiltration (alpha := ℂ)).mono hq.le)) le_rfl
  exact hm measurableSet_Ioi

/-- **Identification of the rational inverse clock.** Along a path where `g_q = A_q` at every
rational time, the clock is nondecreasing and exceeds `r`, the rational inverse clock at level `r`
is the right inverse `τ_r = inf {t | r < A_t}`. -/
theorem rationalPCAFClockInverse_eq {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    {g : ℚ≥0 → ContinuousPath ℂ → ℝ≥0} {r : ℝ≥0} {ω : ContinuousPath ℂ}
    (hg : ∀ q : ℚ≥0, g q ω = A q ω) (hm : Monotone fun t => A t ω) (hne : ∃ t, r < A t ω) :
    rationalPCAFClockInverse g r ω = (pcafClockInverse A r ω : WithTop ℝ≥0) := by
  unfold pcafClockInverse
  have hUne : ({t | r < A t ω} : Set ℝ≥0).Nonempty := hne
  apply le_antisymm
  · refine le_of_forall_gt_imp_ge_of_dense fun c hc => ?_
    induction c with
    | top => exact le_top
    | coe c =>
      rw [WithTop.coe_lt_coe] at hc
      obtain ⟨q, hq1, hq2⟩ := exists_nnrat_btwn_nnreal hc
      obtain ⟨u, hu, huq⟩ := exists_lt_of_csInf_lt hUne hq1
      have hq : r < g q ω := by
        rw [hg q]
        exact lt_of_lt_of_le hu (hm huq.le)
      exact (iInf₂_le q hq).trans (WithTop.coe_le_coe.2 hq2.le)
  · refine le_iInf₂ fun q hq => ?_
    rw [hg q] at hq
    exact WithTop.coe_le_coe.2 (csInf_le (OrderBot.bddBelow _) hq)

/-- Versions of a clock at the rational times, measurable for the natural `σ`-fields. -/
theorem exists_rational_versions_of_isUnitSquarePCAF {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsUnitSquarePCAF A) {z : ℂ} (hz : z ∈ closedSquare 0 1) :
    ∃ g : ℚ≥0 → ContinuousPath ℂ → ℝ≥0, (∀ q : ℚ≥0, Measurable[pathNaturalFiltration q] (g q)) ∧
      ∀ q : ℚ≥0, A q =ᵐ[reflectedPlanarBrownianMotion 0 1 z] g q :=
  ⟨fun q => (hA.adapted z hz q).choose, fun q => (hA.adapted z hz q).choose_spec.1,
    fun q => (hA.adapted z hz q).choose_spec.2⟩

/-- **The rational inverse clock is a version of `τ`.** For a clock almost surely unbounded from
`z` and versions `g_q` of `A_q`, almost surely the rational inverse clock equals `τ_r` for
every `r`. -/
theorem ae_rationalPCAFClockInverse_eq {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsUnitSquarePCAF A) {z : ℂ} (hz : z ∈ closedSquare 0 1)
    (hU : ∀ᵐ b ∂reflectedPlanarBrownianMotion 0 1 z, Tendsto (fun t => A t b) atTop atTop)
    {g : ℚ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hg : ∀ q : ℚ≥0, A q =ᵐ[reflectedPlanarBrownianMotion 0 1 z] g q) :
    ∀ᵐ ω ∂reflectedPlanarBrownianMotion 0 1 z, ∀ r : ℝ≥0,
      rationalPCAFClockInverse g r ω = (pcafClockInverse A r ω : WithTop ℝ≥0) := by
  have hall : ∀ᵐ ω ∂reflectedPlanarBrownianMotion 0 1 z, ∀ q : ℚ≥0, g q ω = A q ω := by
    rw [ae_all_iff]
    intro q
    filter_upwards [hg q] with ω h using h.symm
  filter_upwards [hall, hA.path z hz, hU] with ω hq hp hgood r
  exact rationalPCAFClockInverse_eq hq hp.2.2 (hgood.eventually_gt_atTop r).exists

/-- **An optional version of the inverse clock.** For a clock almost surely unbounded from
`z ∈ K₀`, there is a family `T_r` of optional times of the canonical filtration with
`T_r = τ_r` for every `r`, almost surely. -/
theorem exists_optionalTime_ae_eq_pcafClockInverse {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsUnitSquarePCAF A) {z : ℂ} (hz : z ∈ closedSquare 0 1)
    (hU : ∀ᵐ b ∂reflectedPlanarBrownianMotion 0 1 z, Tendsto (fun t => A t b) atTop atTop) :
    ∃ T : ℝ≥0 → ContinuousPath ℂ → WithTop ℝ≥0,
      (∀ r t : ℝ≥0, MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) t]
        {ω | T r ω < t}) ∧
      ∀ᵐ ω ∂reflectedPlanarBrownianMotion 0 1 z, ∀ r : ℝ≥0,
        T r ω = (pcafClockInverse A r ω : WithTop ℝ≥0) := by
  obtain ⟨g, hgm, hgae⟩ := exists_rational_versions_of_isUnitSquarePCAF hA hz
  exact ⟨rationalPCAFClockInverse g, measurableSet_rationalPCAFClockInverse_lt hgm,
    ae_rationalPCAFClockInverse_eq hA hz hU hgae⟩

/-- **The clock at its right inverse.** For a continuous nondecreasing clock from `0` that exceeds
the level `r`, `A_{τ_r} = r`. -/
theorem apply_pcafClockInverse_eq {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} {r : ℝ≥0}
    {ω : ContinuousPath ℂ} (h0 : A 0 ω = 0) (hc : Continuous fun t => A t ω)
    (hm : Monotone fun t => A t ω) (hne : ∃ t, r < A t ω) :
    A (pcafClockInverse A r ω) ω = r := by
  unfold pcafClockInverse
  have hUne : ({t | r < A t ω} : Set ℝ≥0).Nonempty := hne
  apply le_antisymm
  · refine not_lt.1 fun hlt => ?_
    have hpos : 0 < sInf {t | r < A t ω} := by
      refine pos_iff_ne_zero.2 fun h => ?_
      rw [h, h0] at hlt
      exact absurd hlt (by simp)
    have hopen : {t | r < A t ω} ∈ 𝓝 (sInf {t | r < A t ω}) :=
      (isOpen_lt continuous_const hc).mem_nhds hlt
    obtain ⟨l, hl, hsub⟩ := exists_Ioc_subset_of_mem_nhds hopen ⟨0, hpos⟩
    obtain ⟨t, ht1, ht2⟩ := exists_between hl
    have ht : r < A t ω := hsub ⟨ht1, ht2.le⟩
    exact absurd ht2 (not_lt.2 (csInf_le (OrderBot.bddBelow {t | r < A t ω})
      (show t ∈ {t | r < A t ω} from ht)))
  · have hev : ∀ᶠ t in 𝓝[>] (sInf {t | r < A t ω}), r ≤ A t ω := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      obtain ⟨u, hu, hut⟩ := exists_lt_of_csInf_lt hUne ht
      exact hu.le.trans (hm hut.le)
    exact ge_of_tendsto (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hev

/-- **Additivity of the inverse clock at `τ_r`** (Revuz–Yor (1999), Proposition V.1.1 for the
time change of a PCAF). For a clock almost surely unbounded from `z ∈ K₀` and a level `r`, almost
surely, for every `v`, `τ_{r+v} = τ_r + τ̄_v ∘ θ_{τ_r}`, where `τ̄` is the right inverse of the
rational-time regularization `Ā` of `A`. -/
theorem ae_pcafClockInverse_add_eq_shift {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsUnitSquarePCAF A) {z : ℂ} (hz : z ∈ closedSquare 0 1)
    (hU : ∀ᵐ b ∂reflectedPlanarBrownianMotion 0 1 z, Tendsto (fun t => A t b) atTop atTop)
    (r : ℝ≥0) :
    ∀ᵐ ω ∂reflectedPlanarBrownianMotion 0 1 z, ∀ v : ℝ≥0,
      pcafClockInverse A (r + v) ω = pcafClockInverse A r ω +
        pcafClockInverse (clockRationalRegularization A) v
          (ContinuousPath.shift (pcafClockInverse A r ω) ω) := by
  obtain ⟨g, hgm, hgae⟩ := exists_rational_versions_of_isUnitSquarePCAF hA hz
  filter_upwards [hA.path z hz, hU, ae_rationalPCAFClockInverse_eq hA hz hU hgae,
    ae_add_clockRationalRegularization_shift_optionalTime hA hz (rationalPCAFClockInverse g r)
      (measurableSet_rationalPCAFClockInverse_lt hgm r)] with ω hp hgood hTeq hadd v
  have hTr := hTeq r
  have hfin : rationalPCAFClockInverse g r ω < ⊤ := by
    rw [hTr]
    exact WithTop.coe_lt_top _
  have hshift := hadd hfin
  rw [hTr, WithTop.untopD_coe] at hshift
  have hAτ : A (pcafClockInverse A r ω) ω = r :=
    apply_pcafClockInverse_eq hp.1 hp.2.1 hp.2.2 (hgood.eventually_gt_atTop r).exists
  have key := pcafClockInverse_add_eq_of_shift hp.2.2 hshift
    (hgood.eventually_gt_atTop (A (pcafClockInverse A r ω) ω + v)).exists
  rwa [hAτ] at key

/-- **The time-changed path after `τ_r`.** Almost surely, for every `v`,
`b_{τ_{r+v}} = (θ_{τ_r} b)_{τ̄_v ∘ θ_{τ_r}}`. -/
theorem ae_eval_pcafClockInverse_add_eq_shift {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsUnitSquarePCAF A) {z : ℂ} (hz : z ∈ closedSquare 0 1)
    (hU : ∀ᵐ b ∂reflectedPlanarBrownianMotion 0 1 z, Tendsto (fun t => A t b) atTop atTop)
    (r : ℝ≥0) :
    ∀ᵐ ω ∂reflectedPlanarBrownianMotion 0 1 z, ∀ v : ℝ≥0,
      ω (pcafClockInverse A (r + v) ω) =
        ContinuousPath.shift (pcafClockInverse A r ω) ω
          (pcafClockInverse (clockRationalRegularization A) v
            (ContinuousPath.shift (pcafClockInverse A r ω) ω)) := by
  filter_upwards [ae_pcafClockInverse_add_eq_shift hA hz hU r] with ω h v
  rw [h v, ContinuousPath.shift_apply]

/-! ### The strong Markov property at the right inverse of the clock -/

/-- `τ_u < c` through the rational times, for a clock nondecreasing along the path. -/
theorem pcafClockInverse_lt_iff_of_monotone {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    {ω : ContinuousPath ℂ} (hmono : Monotone fun t => A t ω) (u c : ℝ≥0) :
    pcafClockInverse A u ω < c ↔
      (∃ q : ℚ≥0, (q : ℝ≥0) < c ∧ u < A q ω) ∨ (0 < c ∧ ∀ q : ℚ≥0, A q ω ≤ u) := by
  unfold pcafClockInverse
  constructor
  · intro h
    rcases Set.eq_empty_or_nonempty {t | u < A t ω} with hne | hne
    · refine Or.inr ⟨lt_of_le_of_lt zero_le h, fun q => not_lt.1 fun hq => ?_⟩
      exact (Set.mem_empty_iff_false _).1
        (hne.subset (show (q : ℝ≥0) ∈ {t | u < A t ω} from hq))
    · obtain ⟨s, hs, hsc⟩ := exists_lt_of_csInf_lt hne h
      obtain ⟨q, hsq, hqc⟩ := exists_nnrat_btwn_nnreal hsc
      have hs' : u < A s ω := hs
      exact Or.inl ⟨q, hqc, lt_of_lt_of_le hs' (hmono hsq.le)⟩
  · rintro (⟨q, hqc, hq⟩ | ⟨hc, hall⟩)
    · exact lt_of_le_of_lt
        (csInf_le (OrderBot.bddBelow _) (show (q : ℝ≥0) ∈ {t | u < A t ω} from hq)) hqc
    · have hempty : {t | u < A t ω} = ∅ := by
        by_contra hT
        obtain ⟨s, hs⟩ := Set.nonempty_iff_ne_empty.2 hT
        obtain ⟨q, hsq, -⟩ := exists_nnrat_btwn_nnreal (lt_add_one s)
        have hs' : u < A s ω := hs
        exact absurd (lt_of_lt_of_le hs' (hmono hsq.le)) (not_lt.2 (hall q))
      rw [hempty, NNReal.sInf_empty]
      exact hc

/-- **Joint measurability of the right inverse of a clock.** If every `A t` is measurable and
`A` is nondecreasing in time along every path, then `(u, ω) ↦ τ_u ω` is measurable. -/
theorem measurable_pcafClockInverse_uncurry {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : ∀ t, Measurable (A t)) (hmono : ∀ ω, Monotone fun t => A t ω) :
    Measurable fun p : ℝ≥0 × ContinuousPath ℂ => pcafClockInverse A p.1 p.2 := by
  refine measurable_of_Iio fun c => ?_
  have hset : (fun p : ℝ≥0 × ContinuousPath ℂ => pcafClockInverse A p.1 p.2) ⁻¹' Set.Iio c =
      (⋃ q : ℚ≥0, ({p : ℝ≥0 × ContinuousPath ℂ | (q : ℝ≥0) < c} ∩ {p | p.1 < A q p.2})) ∪
        ({p : ℝ≥0 × ContinuousPath ℂ | 0 < c} ∩ ⋂ q : ℚ≥0, {p | A q p.2 ≤ p.1}) := by
    ext p
    rw [Set.mem_preimage, Set.mem_Iio, pcafClockInverse_lt_iff_of_monotone (hmono p.2)]
    simp only [Set.mem_union, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_iInter,
      Set.mem_ofPred_eq]
  rw [hset]
  exact (MeasurableSet.iUnion fun q : ℚ≥0 => (MeasurableSet.const _).inter
      (measurableSet_lt measurable_fst ((hA q).comp measurable_snd))).union
    ((MeasurableSet.const _).inter (MeasurableSet.iInter fun q : ℚ≥0 =>
      measurableSet_le ((hA q).comp measurable_snd) measurable_fst))

/-- Almost surely, the rational-time regularization of a clock has the same right inverse as the
clock, at every level. -/
theorem ae_pcafClockInverse_regularization_eq {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsUnitSquarePCAF A) {z : ℂ} (hz : z ∈ closedSquare 0 1) :
    ∀ᵐ ω ∂reflectedPlanarBrownianMotion 0 1 z, ∀ u,
      pcafClockInverse (clockRationalRegularization A) u ω = pcafClockInverse A u ω := by
  filter_upwards [hA.path z hz] with ω hp u
  unfold pcafClockInverse
  simp only [clockRationalRegularization_eq_of_continuous_monotone hp.2.1 hp.2.2]

/-- **Strong Markov property at the right inverse of a clock.** For a clock almost surely
unbounded from `z ∈ K₀`, a level `r` and measurable `H ≥ 0` on pairs,
`E_z[H(τ_r, θ_{τ_r} b)] = E_z[∫ H(τ_r, b') dQ_{b_{τ_r}}(b')]`. -/
theorem lintegral_shift_pcafClockInverse_eq {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsUnitSquarePCAF A) {z : ℂ} (hz : z ∈ closedSquare 0 1)
    (hU : ∀ᵐ b ∂reflectedPlanarBrownianMotion 0 1 z, Tendsto (fun t => A t b) atTop atTop)
    (r : ℝ≥0) {H : ℝ≥0 × ContinuousPath ℂ → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ ω, H (pcafClockInverse A r ω, ContinuousPath.shift (pcafClockInverse A r ω) ω)
        ∂reflectedPlanarBrownianMotion 0 1 z =
      ∫⁻ ω, ∫⁻ ω', H (pcafClockInverse A r ω, ω')
        ∂reflectedPlanarBrownianMotion 0 1 (ω (pcafClockInverse A r ω))
        ∂reflectedPlanarBrownianMotion 0 1 z := by
  obtain ⟨T, hT, hae⟩ := exists_optionalTime_ae_eq_pcafClockInverse hA hz hU
  have hfull : (reflectedPlanarBrownianMotion 0 1 z).restrict {ω | T r ω < ⊤} =
      reflectedPlanarBrownianMotion 0 1 z := by
    refine Measure.restrict_eq_self_of_ae_mem ?_
    filter_upwards [hae] with ω h
    show T r ω < ⊤
    rw [h r]
    exact WithTop.coe_lt_top _
  have hu : ∀ᵐ ω ∂reflectedPlanarBrownianMotion 0 1 z,
      (T r ω).untopD 0 = pcafClockInverse A r ω := by
    filter_upwards [hae] with ω h
    rw [h r, WithTop.untopD_coe]
  have hsm := OptionalTime.lintegral_reflected_shift_optionalTime_time z (T r) (hT r) hH
  rw [hfull] at hsm
  calc ∫⁻ ω, H (pcafClockInverse A r ω, ContinuousPath.shift (pcafClockInverse A r ω) ω)
        ∂reflectedPlanarBrownianMotion 0 1 z
      = ∫⁻ ω, H ((T r ω).untopD 0, ContinuousPath.shift ((T r ω).untopD 0) ω)
          ∂reflectedPlanarBrownianMotion 0 1 z := by
        refine lintegral_congr_ae ?_
        filter_upwards [hu] with ω h
        rw [h]
    _ = ∫⁻ ω, ∫⁻ ω', H ((T r ω).untopD 0, ω')
          ∂reflectedPlanarBrownianMotion 0 1 (ω ((T r ω).untopD 0))
          ∂reflectedPlanarBrownianMotion 0 1 z := hsm
    _ = _ := by
        refine lintegral_congr_ae ?_
        filter_upwards [hu] with ω h
        rw [h]

/-! ### The semigroup property -/

/-- The time-changed position `b_{τ_u}`, computed with the rational-time regularization `Ā` of the
clock. -/
noncomputable def unitSquareTimeChangeRegularized (A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0) (u : ℝ≥0)
    (ω : ContinuousPath ℂ) : ℂ :=
  ω (pcafClockInverse (clockRationalRegularization A) u ω)

/-- The regularized time-changed position is measurable. -/
theorem measurable_unitSquareTimeChangeRegularized {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : ∀ t, Measurable (A t)) (u : ℝ≥0) :
    Measurable (unitSquareTimeChangeRegularized A u) := by
  have h1 : Measurable fun ω : ContinuousPath ℂ =>
      pcafClockInverse (clockRationalRegularization A) u ω :=
    (measurable_pcafClockInverse_uncurry (measurable_clockRationalRegularization hA)
      (clockRationalRegularization_monotone A)).comp (measurable_const.prodMk measurable_id)
  exact measurable_path_eval_uncurry.comp (h1.prodMk measurable_id)

/-- Almost surely, the raw and the regularized time-changed positions agree at every level. -/
theorem ae_eval_pcafClockInverse_eq_regularized {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsUnitSquarePCAF A) {y : ℂ} (hy : y ∈ closedSquare 0 1) :
    ∀ᵐ ω ∂reflectedPlanarBrownianMotion 0 1 y, ∀ u,
      ω (pcafClockInverse A u ω) = unitSquareTimeChangeRegularized A u ω := by
  filter_upwards [ae_pcafClockInverse_regularization_eq hA hy] with ω h u
  rw [unitSquareTimeChangeRegularized, h u]

/-- The probability that the time-changed path lies in `S` at level `u` is the probability of the
measurable event written with the regularized clock. -/
theorem reflected_eval_pcafClockInverse_mem {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsUnitSquarePCAF A) {y : ℂ} (hy : y ∈ closedSquare 0 1) (u : ℝ≥0) (S : Set ℂ) :
    reflectedPlanarBrownianMotion 0 1 y {ω | ω (pcafClockInverse A u ω) ∈ S} =
      reflectedPlanarBrownianMotion 0 1 y (unitSquareTimeChangeRegularized A u ⁻¹' S) := by
  refine measure_congr ?_
  filter_upwards [ae_eval_pcafClockInverse_eq_regularized hA hy] with ω h
  show (ω (pcafClockInverse A u ω) ∈ S) = (unitSquareTimeChangeRegularized A u ω ∈ S)
  rw [h u]

/-- **The semigroup property of the time change**, pathwise form. For a clock almost surely
unbounded from `z ∈ K₀`, `Q_z[b_{τ_{v+u}} ∈ S] = E_z[Q_{b_{τ_v}}[b_{τ_u} ∈ S]]`. -/
theorem reflected_eval_pcafClockInverse_add_mem {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsUnitSquarePCAF A) {z : ℂ} (hz : z ∈ closedSquare 0 1)
    (hU : ∀ᵐ b ∂reflectedPlanarBrownianMotion 0 1 z, Tendsto (fun t => A t b) atTop atTop)
    (v u : ℝ≥0) {S : Set ℂ} (hS : MeasurableSet S) :
    reflectedPlanarBrownianMotion 0 1 z {ω | ω (pcafClockInverse A (v + u) ω) ∈ S} =
      ∫⁻ ω, reflectedPlanarBrownianMotion 0 1 (ω (pcafClockInverse A v ω))
          (unitSquareTimeChangeRegularized A u ⁻¹' S)
        ∂reflectedPlanarBrownianMotion 0 1 z := by
  have hEm : MeasurableSet (unitSquareTimeChangeRegularized A u ⁻¹' S) :=
    measurable_unitSquareTimeChangeRegularized hA.measurable u hS
  have hH : Measurable fun p : ℝ≥0 × ContinuousPath ℂ =>
      (unitSquareTimeChangeRegularized A u ⁻¹' S).indicator
        (1 : ContinuousPath ℂ → ℝ≥0∞) p.2 :=
    (measurable_one.indicator hEm).comp measurable_snd
  have key : ∫⁻ ω, (unitSquareTimeChangeRegularized A u ⁻¹' S).indicator
        (1 : ContinuousPath ℂ → ℝ≥0∞) (ContinuousPath.shift (pcafClockInverse A v ω) ω)
          ∂reflectedPlanarBrownianMotion 0 1 z =
      ∫⁻ ω, ∫⁻ ω', (unitSquareTimeChangeRegularized A u ⁻¹' S).indicator
        (1 : ContinuousPath ℂ → ℝ≥0∞) ω'
          ∂reflectedPlanarBrownianMotion 0 1 (ω (pcafClockInverse A v ω))
          ∂reflectedPlanarBrownianMotion 0 1 z :=
    lintegral_shift_pcafClockInverse_eq hA hz hU v hH
  calc reflectedPlanarBrownianMotion 0 1 z {ω | ω (pcafClockInverse A (v + u) ω) ∈ S}
      = reflectedPlanarBrownianMotion 0 1 z (unitSquareTimeChangeRegularized A (v + u) ⁻¹' S) :=
        reflected_eval_pcafClockInverse_mem hA hz _ S
    _ = ∫⁻ ω, (unitSquareTimeChangeRegularized A (v + u) ⁻¹' S).indicator
          (1 : ContinuousPath ℂ → ℝ≥0∞) ω ∂reflectedPlanarBrownianMotion 0 1 z :=
        (lintegral_indicator_one
          (measurable_unitSquareTimeChangeRegularized hA.measurable _ hS)).symm
    _ = ∫⁻ ω, (unitSquareTimeChangeRegularized A u ⁻¹' S).indicator
          (1 : ContinuousPath ℂ → ℝ≥0∞) (ContinuousPath.shift (pcafClockInverse A v ω) ω)
          ∂reflectedPlanarBrownianMotion 0 1 z := by
        refine lintegral_congr_ae ?_
        filter_upwards [ae_eval_pcafClockInverse_eq_regularized hA hz,
          ae_eval_pcafClockInverse_add_eq_shift hA hz hU v] with ω h1 h2
        have h3 : unitSquareTimeChangeRegularized A (v + u) ω =
            unitSquareTimeChangeRegularized A u (ContinuousPath.shift (pcafClockInverse A v ω) ω) :=
          (h1 (v + u)).symm.trans (h2 u)
        by_cases hm : unitSquareTimeChangeRegularized A (v + u) ω ∈ S
        · have hm' : unitSquareTimeChangeRegularized A u
              (ContinuousPath.shift (pcafClockInverse A v ω) ω) ∈ S := h3 ▸ hm
          exact (Set.indicator_of_mem (s := unitSquareTimeChangeRegularized A (v + u) ⁻¹' S)
            (a := ω) hm 1).trans (Set.indicator_of_mem
              (s := unitSquareTimeChangeRegularized A u ⁻¹' S)
              (a := ContinuousPath.shift (pcafClockInverse A v ω) ω) hm' 1).symm
        · have hm' : unitSquareTimeChangeRegularized A u
              (ContinuousPath.shift (pcafClockInverse A v ω) ω) ∉ S := h3 ▸ hm
          exact (Set.indicator_of_notMem (s := unitSquareTimeChangeRegularized A (v + u) ⁻¹' S)
            (a := ω) hm 1).trans (Set.indicator_of_notMem
              (s := unitSquareTimeChangeRegularized A u ⁻¹' S)
              (a := ContinuousPath.shift (pcafClockInverse A v ω) ω) hm' 1).symm
    _ = _ := key
    _ = _ := by
        refine lintegral_congr fun ω => ?_
        rw [lintegral_indicator_one hEm]

end HarmonicBalls

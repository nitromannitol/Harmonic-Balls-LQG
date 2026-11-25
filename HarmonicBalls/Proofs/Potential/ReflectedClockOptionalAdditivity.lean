import HarmonicBalls.Proofs.Potential.ReflectedOptionalTimeStrongMarkov
import HarmonicBalls.Proofs.Potential.ReflectedRevuzFormula

/-!
# Additivity of a clock of reflected Brownian motion at optional times

Let `A` be a positive continuous additive functional of reflected Brownian motion in the unit
square (`IsUnitSquarePCAF A`) and `Ā` its rational-time regularization
(`clockRationalRegularization A`). The additivity `A (t + s) = A t + A s ∘ θ_t` holds almost surely
for each fixed pair of times. This module proves it

* at a fixed time `t`, for all later times `s` at once, with `Ā` on the shifted path
  (`ae_add_clockRationalRegularization_shift`, Revuz–Yor (1999), X.1.1, raw form);
* at an optional time `T` of the natural filtration, almost surely on `{T < ∞}`, for all `s`
  (`ae_clockRationalRegularization_add_shift_optionalTime`, Revuz–Yor (1999), X.1;
  Fukushima–Oshima–Takeda (2011), Section A.3), through the strong Markov property at optional
  times in the transfer form.

No perfection theorem is used. The proof at an optional time:
1. `Ā` is jointly measurable in the time and the path, and right-continuous in the time.
2. The set of pairs `(v, b)` with `Ā (v + q) b = Ā v b + Ā q (θ_v b)` for all rationals `q ≥ 0`
   is measurable, and each fixed-`v` section has full probability; by Tonelli, almost surely
   `(v, b)` lies in it for Lebesgue-almost every `v`.
3. The event "`Ā 0 = 0` and `(v, ·)` lies in that set for almost every `v`" is measurable and has
   probability one from every start in `K₀`, so it holds for `θ_T b`.
4. Pathwise: `D(t) := Ā (T + t) b - Ā t (θ_T b)` satisfies `D(q + p) = D(q)` for rationals `p`
   and almost every `q`, hence `D(t) = D(0) = Ā T b` by right-continuity.

Credit: the proofs follow MatedCRT/FirstPass/Derived/RevuzShiftAdditivity.lean and
RevuzOptionalAdditivity.lean of the IDLA-Mated-CRT formalization, written there for planar
Brownian motion. Source commit: IDLA-Mated-CRT ea80b70d7b8c8c59778c86b6bd4b06c1060b6fbe.
Changes: planar Brownian motion (`planarLaw`, `IsPCAF`, `regularize`, `LatticeProb.pathShift`)
replaced by reflected Brownian motion in the unit square (`reflectedPlanarBrownianMotion 0 1`,
`IsUnitSquarePCAF`, `clockRationalRegularization`, `ContinuousPath.shift`), with starts in `K₀`;
the right inverse of the clock is `pcafClockInverse`; proofs otherwise as in the source.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology MarkovProcess
open scoped ENNReal NNReal

namespace HarmonicBalls

/-- The right inverse `τ_r = inf {t | r < A_t}` of a clock along a path. -/
noncomputable def pcafClockInverse (A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0) (r : ℝ≥0)
    (b : ContinuousPath ℂ) : ℝ≥0 :=
  sInf {t | r < A t b}

/-- The right inverse of the real-valued clock `t ↦ A t b` (`clockInverse`, the time change of
`liouvilleBrownianPath`) is `pcafClockInverse`. -/
theorem clockInverse_coe_eq_pcafClockInverse (A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0) (r : ℝ≥0)
    (b : ContinuousPath ℂ) :
    clockInverse (fun t => (A t b : ℝ)) r = pcafClockInverse A r b := by
  unfold clockInverse pcafClockInverse
  simp only [NNReal.coe_lt_coe]

/-! ### Additivity at a fixed time -/

/-- **Additivity at all times from additivity at rational times.** If `A` is continuous and
nondecreasing along `ω` and `A (t + q) ω = A t ω + A q ω'` for every rational `q ≥ 0`, then
`A (t + s) ω = A t ω + Ā s ω'` for every `s`. -/
theorem add_clockRationalRegularization_of_forall_nnrat {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    {ω ω' : ContinuousPath ℂ} {t : ℝ≥0} (hc : Continuous fun u => A u ω)
    (hm : Monotone fun u => A u ω)
    (hq : ∀ q : ℚ≥0, A (t + (q : ℝ≥0)) ω = A t ω + A (q : ℝ≥0) ω') (s : ℝ≥0) :
    A (t + s) ω = A t ω + clockRationalRegularization A s ω' := by
  have hne := nonempty_clockRationalRegularization_index s
  have hcond : ∀ p q : ℚ≥0, p ≤ q → A p ω' ≤ A q ω' := fun p q hpq => by
    have h := hm (show t + (p : ℝ≥0) ≤ t + (q : ℝ≥0) by gcongr)
    simp only [hq] at h
    exact le_of_add_le_add_left h
  unfold clockRationalRegularization
  split_ifs
  refine le_antisymm ?_ ?_
  · rw [← tsub_le_iff_left]
    refine le_ciInf fun q => ?_
    rw [tsub_le_iff_left, ← hq]
    exact hm (show t + s ≤ t + (q.1 : ℝ≥0) by gcongr; exact q.2.le)
  · refine le_of_forall_gt_imp_ge_of_dense fun c hc' => ?_
    have hU : {u | A u ω < c} ∈ 𝓝 (t + s) := hc.continuousAt.eventually (gt_mem_nhds hc')
    obtain ⟨u, hu, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1 (nhdsWithin_le_nhds hU)
    have hsu : s < u - t := lt_tsub_iff_left.2 hu
    obtain ⟨q, hq1, hq2⟩ := exists_nnrat_btwn_nnreal hsu
    have hmem : t + (q : ℝ≥0) ∈ Ioo (t + s) u :=
      ⟨by gcongr, lt_tsub_iff_left.1 hq2⟩
    calc A t ω + ⨅ q' : {q : ℚ≥0 // s < (q : ℝ≥0)}, A (q'.1 : ℝ≥0) ω'
        ≤ A t ω + A (q : ℝ≥0) ω' := by
          gcongr
          exact ciInf_le (OrderBot.bddBelow _) (⟨q, hq1⟩ : {q : ℚ≥0 // s < (q : ℝ≥0)})
      _ = A (t + (q : ℝ≥0)) ω := (hq q).symm
      _ ≤ c := (hsub hmem).le

/-- **Additivity of a clock at a fixed time, for all later times at once.** For every start
`x ∈ K₀` and time `t`, almost surely, `A (t + s) b = A t b + Ā s (θ_t b)` for every `s`. -/
theorem ae_add_clockRationalRegularization_shift {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsUnitSquarePCAF A) {x : ℂ} (hx : x ∈ closedSquare 0 1) (t : ℝ≥0) :
    ∀ᵐ b ∂reflectedPlanarBrownianMotion 0 1 x, ∀ s,
      A (t + s) b = A t b + clockRationalRegularization A s (ContinuousPath.shift t b) := by
  have hrat : ∀ᵐ b ∂reflectedPlanarBrownianMotion 0 1 x, ∀ q : ℚ≥0,
      A (t + (q : ℝ≥0)) b = A t b + A (q : ℝ≥0) (ContinuousPath.shift t b) := by
    refine ae_all_iff.2 fun q => ?_
    filter_upwards [hA.additive x hx q t] with b hb
    rw [hb, pathTimeShift_eq_shift]
  filter_upwards [hA.path x hx, hrat] with b hp hq s
  exact add_clockRationalRegularization_of_forall_nnrat hp.2.1 hp.2.2 hq s

/-- **Additivity of the regularized clock at a fixed time.** For every start `x ∈ K₀` and time
`t`, almost surely, `Ā (t + s) b = Ā t b + Ā s (θ_t b)` for every `s`. -/
theorem ae_clockRationalRegularization_add_shift {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsUnitSquarePCAF A) {x : ℂ} (hx : x ∈ closedSquare 0 1) (t : ℝ≥0) :
    ∀ᵐ b ∂reflectedPlanarBrownianMotion 0 1 x, ∀ s,
      clockRationalRegularization A (t + s) b = clockRationalRegularization A t b +
        clockRationalRegularization A s (ContinuousPath.shift t b) := by
  filter_upwards [hA.path x hx, ae_add_clockRationalRegularization_shift hA hx t]
    with b hp hadd s
  rw [clockRationalRegularization_eq_of_continuous_monotone hp.2.1 hp.2.2,
    clockRationalRegularization_eq_of_continuous_monotone hp.2.1 hp.2.2, hadd s]

/-- **Shift of the right inverse of a clock.** If `A` is nondecreasing along `ω`,
`A (t + s) ω = A t ω + B s ω'` for every `s`, and `A` exceeds `A t ω + r` along `ω`, then the
right inverse of `A` at level `A t ω + r` is `t` plus the right inverse of `B` at level `r`
along `ω'`. -/
theorem pcafClockInverse_add_eq_of_shift {A B : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    {ω ω' : ContinuousPath ℂ} {t r : ℝ≥0} (hm : Monotone fun u => A u ω)
    (hshift : ∀ s, A (t + s) ω = A t ω + B s ω') (hne : ∃ u, A t ω + r < A u ω) :
    pcafClockInverse A (A t ω + r) ω = t + pcafClockInverse B r ω' := by
  unfold pcafClockInverse
  have hS : {s | r < B s ω'} = {s | A t ω + r < A (t + s) ω} := by
    ext s
    simp only [Set.mem_ofPred_eq, hshift s, add_lt_add_iff_left]
  have himg : (fun s => t + s) '' {s | A t ω + r < A (t + s) ω} = {u | A t ω + r < A u ω} := by
    ext u
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact hs
    · intro hu
      have htu : t ≤ u := by
        by_contra h
        exact absurd hu (not_lt.2 ((hm (not_le.1 h).le).trans le_self_add))
      refine ⟨u - t, ?_, add_tsub_cancel_of_le htu⟩
      simpa only [Set.mem_ofPred_eq, add_tsub_cancel_of_le htu] using hu
  have hSne : {s | A t ω + r < A (t + s) ω}.Nonempty := by
    obtain ⟨u, hu⟩ := hne
    have hmem : u ∈ (fun s => t + s) '' {s | A t ω + r < A (t + s) ω} := by
      rw [himg]
      exact hu
    obtain ⟨s, hs, -⟩ := hmem
    exact ⟨s, hs⟩
  rw [hS, ← himg]
  exact (Monotone.map_csInf_of_continuousAt (f := fun s : ℝ≥0 => t + s)
    (by fun_prop : Continuous fun s : ℝ≥0 => t + s).continuousAt
    (fun a b (h : a ≤ b) => (add_le_add_iff_left t).2 h) hSne (OrderBot.bddBelow _)).symm

/-! ### Additivity at an optional time -/

/-- The regularized clock is jointly measurable in the time and the path. -/
theorem measurable_clockRationalRegularization_uncurry {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : ∀ t, Measurable (A t)) :
    Measurable (fun p : ℝ≥0 × ContinuousPath ℂ => clockRationalRegularization A p.1 p.2) := by
  classical
  have hCm : MeasurableSet {p : ℝ≥0 × ContinuousPath ℂ |
      ∀ a b : ℚ≥0, a ≤ b → A a p.2 ≤ A b p.2} := by
    have hC : MeasurableSet {ω : ContinuousPath ℂ | ∀ a b : ℚ≥0, a ≤ b → A a ω ≤ A b ω} := by
      have : {ω : ContinuousPath ℂ | ∀ a b : ℚ≥0, a ≤ b → A a ω ≤ A b ω} =
          ⋂ a : ℚ≥0, ⋂ b : ℚ≥0, {ω | a ≤ b → A a ω ≤ A b ω} := by
        ext ω
        simp
      rw [this]
      refine MeasurableSet.iInter fun a => MeasurableSet.iInter fun b => ?_
      by_cases hab : a ≤ b
      · simpa [hab] using measurableSet_le (hA _) (hA _)
      · simp [hab]
    exact measurable_snd hC
  have hFm : Measurable fun p : ℝ≥0 × ContinuousPath ℂ =>
      ⨅ q : ℚ≥0, if p.1 < (q : ℝ≥0) then ((A q p.2 : ℝ≥0) : ℝ≥0∞) else ⊤ := by
    refine Measurable.iInf fun q => Measurable.ite ?_ ?_ measurable_const
    · exact measurableSet_lt measurable_fst measurable_const
    · exact ((hA _).comp measurable_snd).coe_nnreal_ennreal
  have heq : (fun p : ℝ≥0 × ContinuousPath ℂ =>
        ⨅ q : {q : ℚ≥0 // p.1 < (q : ℝ≥0)}, A (q.1 : ℝ≥0) p.2) =
      fun p => (⨅ q : ℚ≥0, if p.1 < (q : ℝ≥0) then ((A q p.2 : ℝ≥0) : ℝ≥0∞) else ⊤).toNNReal := by
    funext p
    have hne := nonempty_clockRationalRegularization_index p.1
    have hF : (⨅ q : ℚ≥0, if p.1 < (q : ℝ≥0) then ((A q p.2 : ℝ≥0) : ℝ≥0∞) else ⊤) =
        ((⨅ q : {q : ℚ≥0 // p.1 < (q : ℝ≥0)}, A (q.1 : ℝ≥0) p.2 : ℝ≥0) : ℝ≥0∞) := by
      rw [ENNReal.coe_iInf, iInf_subtype]
      refine iInf_congr fun q => ?_
      exact (iInf_eq_if _).symm
    rw [hF, ENNReal.toNNReal_coe]
  unfold clockRationalRegularization
  refine Measurable.ite hCm ?_ measurable_const
  rw [heq]
  exact hFm.ennreal_toNNReal

/-- The regularized clock is right-continuous in the time, along every path. -/
theorem continuousWithinAt_clockRationalRegularization_Ici (A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0)
    (ω : ContinuousPath ℂ) (t : ℝ≥0) :
    ContinuousWithinAt (fun u => clockRationalRegularization A u ω) (Ici t) t := by
  by_cases h : ∀ a b : ℚ≥0, a ≤ b → A a ω ≤ A b ω
  · have hval : ∀ u, clockRationalRegularization A u ω =
        ⨅ q : {q : ℚ≥0 // u < (q : ℝ≥0)}, A (q.1 : ℝ≥0) ω := by
      intro u
      unfold clockRationalRegularization
      split_ifs
      rfl
    have hmono := clockRationalRegularization_monotone A ω
    unfold ContinuousWithinAt
    refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
    · have ha' : a < clockRationalRegularization A t ω := ha
      filter_upwards [self_mem_nhdsWithin] with u hu
      exact ha'.trans_le (hmono hu)
    · have hne := nonempty_clockRationalRegularization_index t
      have ha' : clockRationalRegularization A t ω < a := ha
      rw [hval t] at ha'
      replace ha := ha'
      obtain ⟨q, hq⟩ := exists_lt_of_ciInf_lt ha
      filter_upwards [inter_mem_nhdsWithin (Ici t) (Iio_mem_nhds q.2)] with u hu
      have hne' := nonempty_clockRationalRegularization_index u
      rw [hval u]
      exact (ciInf_le (OrderBot.bddBelow _)
        (⟨q.1, hu.2⟩ : {q : ℚ≥0 // u < (q : ℝ≥0)})).trans_lt hq
  · have hzero : ∀ u, clockRationalRegularization A u ω = 0 := by
      intro u
      unfold clockRationalRegularization
      split_ifs
      rfl
    simp only [hzero]
    exact continuousWithinAt_const

/-- The pairs `(v, ω)` at which the regularized clock is additive at time `v` against every
rational time: `Ā (v + q) ω = Ā v ω + Ā q (θ_v ω)` for all `q ∈ ℚ≥0`. -/
def clockRegularizationAddSet (A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0) :
    Set (ℝ≥0 × ContinuousPath ℂ) :=
  {p | ∀ q : ℚ≥0, clockRationalRegularization A (p.1 + q) p.2 =
    clockRationalRegularization A p.1 p.2 +
      clockRationalRegularization A q (ContinuousPath.shift p.1 p.2)}

theorem measurableSet_clockRegularizationAddSet {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : ∀ t, Measurable (A t)) : MeasurableSet (clockRegularizationAddSet A) := by
  have hR := measurable_clockRationalRegularization_uncurry hA
  have hS : Measurable fun p : ℝ≥0 × ContinuousPath ℂ => ContinuousPath.shift p.1 p.2 :=
    (ContinuousPath.continuous_shift (alpha := ℂ)).measurable
  have hset : clockRegularizationAddSet A = ⋂ q : ℚ≥0, {p : ℝ≥0 × ContinuousPath ℂ |
      clockRationalRegularization A (p.1 + q) p.2 =
        clockRationalRegularization A p.1 p.2 +
          clockRationalRegularization A q (ContinuousPath.shift p.1 p.2)} := by
    ext p
    simp [clockRegularizationAddSet]
  rw [hset]
  refine MeasurableSet.iInter fun q => ?_
  have hf : Measurable fun p : ℝ≥0 × ContinuousPath ℂ =>
      clockRationalRegularization A (p.1 + q) p.2 :=
    hR.comp ((measurable_fst.add_const _).prodMk measurable_snd)
  have hg : Measurable fun p : ℝ≥0 × ContinuousPath ℂ =>
      clockRationalRegularization A p.1 p.2 +
        clockRationalRegularization A q (ContinuousPath.shift p.1 p.2) :=
    hR.add ((measurable_clockRationalRegularization hA _).comp hS)
  exact (hf.prodMk hg) measurableSet_diagonal

/-- **Tonelli step.** Almost surely, `(v, ω)` lies in `clockRegularizationAddSet A` for
Lebesgue-almost every time `v ≥ 0` (times are indexed by `x ∈ ℝ` through `x.toNNReal`). -/
theorem ae_ae_mem_clockRegularizationAddSet {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsUnitSquarePCAF A) {z : ℂ} (hz : z ∈ closedSquare 0 1) :
    ∀ᵐ ω ∂reflectedPlanarBrownianMotion 0 1 z,
      ∀ᵐ x : ℝ ∂(volume : Measure ℝ), (x.toNNReal, ω) ∈ clockRegularizationAddSet A := by
  have hS : MeasurableSet {p : ℝ × ContinuousPath ℂ |
      (p.1.toNNReal, p.2) ∈ clockRegularizationAddSet A} :=
    (measurable_real_toNNReal.prodMap measurable_id)
      (measurableSet_clockRegularizationAddSet hA.measurable)
  have hfix : ∀ x : ℝ, ∀ᵐ ω ∂reflectedPlanarBrownianMotion 0 1 z,
      (x.toNNReal, ω) ∈ clockRegularizationAddSet A := by
    intro x
    filter_upwards [ae_clockRationalRegularization_add_shift hA hz x.toNNReal] with ω hω q
    exact hω q
  exact (Measure.ae_ae_comm hS).1 (Eventually.of_forall hfix)

/-- The event "`Ā 0 = 0` and `(v, ·) ∈ clockRegularizationAddSet A` for almost every `v`" is
measurable. -/
theorem measurableSet_clockRegularizationAddGood {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : ∀ t, Measurable (A t)) :
    MeasurableSet {ω : ContinuousPath ℂ | clockRationalRegularization A 0 ω = 0 ∧
      volume {x : ℝ | (x.toNNReal, ω) ∉ clockRegularizationAddSet A} = 0} := by
  have hS : MeasurableSet {p : ℝ × ContinuousPath ℂ |
      (p.1.toNNReal, p.2) ∈ clockRegularizationAddSet A} :=
    (measurable_real_toNNReal.prodMap measurable_id) (measurableSet_clockRegularizationAddSet hA)
  have hm : Measurable fun ω : ContinuousPath ℂ =>
      (volume : Measure ℝ) ((fun x => (x, ω)) ⁻¹'
        {p : ℝ × ContinuousPath ℂ | (p.1.toNNReal, p.2) ∈ clockRegularizationAddSet A}ᶜ) :=
    measurable_measure_prodMk_right hS.compl
  exact ((measurable_clockRationalRegularization hA 0) (measurableSet_singleton 0)).inter
    (hm (measurableSet_singleton 0))

/-- The event of `measurableSet_clockRegularizationAddGood` has probability one from every start
in `K₀`. -/
theorem reflected_clockRegularizationAddGood_eq_one {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsUnitSquarePCAF A) {y : ℂ} (hy : y ∈ closedSquare 0 1) :
    reflectedPlanarBrownianMotion 0 1 y
      {ω : ContinuousPath ℂ | clockRationalRegularization A 0 ω = 0 ∧
        volume {x : ℝ | (x.toNNReal, ω) ∉ clockRegularizationAddSet A} = 0} = 1 := by
  rw [← prob_compl_eq_zero_iff (measurableSet_clockRegularizationAddGood hA.measurable)]
  have h : ∀ᵐ ω ∂reflectedPlanarBrownianMotion 0 1 y, clockRationalRegularization A 0 ω = 0 ∧
      volume {x : ℝ | (x.toNNReal, ω) ∉ clockRegularizationAddSet A} = 0 := by
    filter_upwards [hA.path y hy, ae_ae_mem_clockRegularizationAddSet hA hy] with ω hp hgood
    refine ⟨?_, ae_iff.1 hgood⟩
    rw [clockRationalRegularization_eq_of_continuous_monotone hp.2.1 hp.2.2]
    exact hp.1
  exact ae_iff.1 h

/-- **Pathwise step.** If `(v, ω)` and `(v, θ_τ ω)` lie in `clockRegularizationAddSet A` for
almost every `v`, and `Ā 0 (θ_τ ω) = 0`, then `Ā (τ + s) ω = Ā τ ω + Ā s (θ_τ ω)` for every
`s`. -/
theorem clockRationalRegularization_add_shift_of_ae {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    {ω : ContinuousPath ℂ} (τ : ℝ≥0)
    (h1 : ∀ᵐ x : ℝ ∂(volume : Measure ℝ), (x.toNNReal, ω) ∈ clockRegularizationAddSet A)
    (h2 : ∀ᵐ x : ℝ ∂(volume : Measure ℝ),
      (x.toNNReal, ContinuousPath.shift τ ω) ∈ clockRegularizationAddSet A)
    (h0 : clockRationalRegularization A 0 (ContinuousPath.shift τ ω) = 0) (s : ℝ≥0) :
    clockRationalRegularization A (τ + s) ω = clockRationalRegularization A τ ω +
      clockRationalRegularization A s (ContinuousPath.shift τ ω) := by
  obtain ⟨d, hd⟩ : ∃ d : ℝ≥0 → ℝ, ∀ u, d u =
      (clockRationalRegularization A (τ + u) ω : ℝ) -
        clockRationalRegularization A u (ContinuousPath.shift τ ω) :=
    ⟨_, fun _ => rfl⟩
  have hdc : ∀ u, ContinuousWithinAt d (Ici u) u := by
    intro u
    have ha : ContinuousWithinAt (fun v => clockRationalRegularization A (τ + v) ω) (Ici u) u :=
      (continuousWithinAt_clockRationalRegularization_Ici A ω (τ + u)).comp
        (continuous_const.add continuous_id).continuousWithinAt
        (fun v hv => by simp only [mem_Ici] at hv ⊢; exact add_le_add_right hv τ)
    have hb := continuousWithinAt_clockRationalRegularization_Ici A (ContinuousPath.shift τ ω) u
    have hsub := (NNReal.continuous_coe.continuousAt.comp_continuousWithinAt ha).sub
      (NNReal.continuous_coe.continuousAt.comp_continuousWithinAt hb)
    have hfun : d = fun v => ((clockRationalRegularization A (τ + v) ω : ℝ≥0) : ℝ) -
        ((clockRationalRegularization A v (ContinuousPath.shift τ ω) : ℝ≥0) : ℝ) := funext hd
    rw [hfun]
    exact hsub
  have h1' : ∀ᵐ x : ℝ ∂(volume : Measure ℝ),
      ((x + (τ : ℝ)).toNNReal, ω) ∈ clockRegularizationAddSet A :=
    (measurePreserving_add_right volume (τ : ℝ)).quasiMeasurePreserving.ae h1
  have hgood : ∀ᵐ x : ℝ ∂(volume : Measure ℝ), 0 ≤ x →
      ∀ p : ℚ≥0, d (x.toNNReal + p) = d x.toNNReal := by
    filter_upwards [h1', h2] with x hx1 hx2 hx0 p
    have hτx : (x + τ).toNNReal = τ + x.toNNReal := by
      rw [Real.toNNReal_add hx0 τ.coe_nonneg, Real.toNNReal_coe, add_comm]
    rw [hτx] at hx1
    have e1 := hx1 p
    have e2 := hx2 p
    simp only at e1 e2
    rw [ContinuousPath.shift_add] at e2
    rw [hd, hd, ← add_assoc, e1, e2]
    push_cast
    ring
  have hstep : ∀ q : ℝ≥0, (∀ p : ℚ≥0, d (q + p) = d q) → ∀ u, q ≤ u → d u = d q := by
    intro q hq u hqu
    refine eq_of_forall_dist_le fun ε hε => ?_
    obtain ⟨δ, hδ, hδu⟩ := Metric.continuousWithinAt_iff.1 (hdc u) ε hε
    obtain ⟨p, hp1, hp2⟩ := exists_nnrat_btwn_nnreal
      (show u - q < u - q + δ.toNNReal from lt_add_of_pos_right _ (Real.toNNReal_pos.2 hδ))
    have hv : u ≤ q + (p : ℝ≥0) := ((tsub_lt_iff_left hqu).1 hp1).le
    have hp2' : ((p : ℝ≥0) : ℝ) < (u : ℝ) - q + δ := by
      have := NNReal.coe_lt_coe.2 hp2
      rwa [NNReal.coe_add, NNReal.coe_sub hqu, Real.coe_toNNReal _ hδ.le] at this
    have hvd : dist (q + (p : ℝ≥0)) u < δ := by
      rw [NNReal.dist_eq, abs_sub_lt_iff]
      have hv' : (u : ℝ) ≤ q + (p : ℝ≥0) := by exact_mod_cast hv
      push_cast
      constructor <;> linarith
    have hlt := hδu (mem_Ici.2 hv) hvd
    rw [hq p] at hlt
    rw [dist_comm]
    exact hlt.le
  have hfinal : d s = d 0 := by
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ s) with hs | hs
    · rw [← hs]
    refine eq_of_forall_dist_le fun ε hε => ?_
    obtain ⟨δ, hδ, hδ0⟩ := Metric.continuousWithinAt_iff.1 (hdc 0) ε hε
    have hcpos : 0 < min δ (s : ℝ) := lt_min hδ (by exact_mod_cast hs)
    obtain ⟨x, hx, hxg⟩ : ∃ x ∈ Ioo (0 : ℝ) (min δ (s : ℝ)),
        0 ≤ x → ∀ p : ℚ≥0, d (x.toNNReal + p) = d x.toNNReal := by
      by_contra hcon
      have hsub : Ioo (0 : ℝ) (min δ (s : ℝ)) ⊆
          {x | ¬(0 ≤ x → ∀ p : ℚ≥0, d (x.toNNReal + p) = d x.toNNReal)} :=
        fun x hx hg => hcon ⟨x, hx, hg⟩
      have hpos : 0 < volume (Ioo (0 : ℝ) (min δ (s : ℝ))) := by
        rw [Real.volume_Ioo]
        exact ENNReal.ofReal_pos.2 (by linarith)
      exact hpos.ne' (measure_mono_null hsub (ae_iff.1 hgood))
    have hx0 : 0 ≤ x := hx.1.le
    have hxs : x.toNNReal ≤ s := by
      rw [Real.toNNReal_le_iff_le_coe]
      exact hx.2.le.trans (min_le_right _ _)
    have heq := hstep x.toNNReal (hxg hx0) s hxs
    have hclose := hδ0 (mem_Ici.2 zero_le) (show dist x.toNNReal 0 < δ by
      rw [NNReal.dist_eq, NNReal.coe_zero, sub_zero, Real.coe_toNNReal _ hx0, abs_of_nonneg hx0]
      exact hx.2.trans_le (min_le_left _ _))
    rw [heq]
    exact hclose.le
  have hd0 : d 0 = clockRationalRegularization A τ ω := by
    rw [hd, add_zero, h0, NNReal.coe_zero, sub_zero]
  rw [hd0, hd] at hfinal
  have hreal : (clockRationalRegularization A (τ + s) ω : ℝ) =
      clockRationalRegularization A τ ω +
        clockRationalRegularization A s (ContinuousPath.shift τ ω) := by
    linarith
  exact_mod_cast hreal

/-- **Additivity of the regularized clock at an optional time.** For a PCAF of reflected Brownian
motion in the unit square, a start `z ∈ K₀` and an optional time `T` of the natural filtration,
almost surely on `{T < ∞}`, `Ā (T + s) b = Ā T b + Ā s (θ_T b)` for every `s`. -/
theorem ae_clockRationalRegularization_add_shift_optionalTime
    {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} (hA : IsUnitSquarePCAF A) {z : ℂ}
    (hz : z ∈ closedSquare 0 1) (T : ContinuousPath ℂ → WithTop ℝ≥0)
    (hT : ∀ t : ℝ≥0, MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) t]
      {ω | T ω < t}) :
    ∀ᵐ ω ∂reflectedPlanarBrownianMotion 0 1 z, T ω < ⊤ → ∀ s : ℝ≥0,
      clockRationalRegularization A ((T ω).untopD 0 + s) ω =
        clockRationalRegularization A ((T ω).untopD 0) ω +
          clockRationalRegularization A s (ContinuousPath.shift ((T ω).untopD 0) ω) := by
  filter_upwards [ae_ae_mem_clockRegularizationAddSet hA hz,
    OptionalTime.ae_shift_mem_of_forall_reflected_eq_one z T hT
      (measurableSet_clockRegularizationAddGood hA.measurable)
      (fun y hy => reflected_clockRegularizationAddGood_eq_one hA hy)]
    with ω h1 h2 hfin s
  obtain ⟨h0, hnull⟩ := h2 hfin
  exact clockRationalRegularization_add_shift_of_ae _ h1 (ae_iff.2 hnull) h0 s

/-- **Additivity at an optional time, raw clock on the unshifted path.** Almost surely on
`{T < ∞}`, `A (T + s) b = A T b + Ā s (θ_T b)` for every `s`. -/
theorem ae_add_clockRationalRegularization_shift_optionalTime
    {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} (hA : IsUnitSquarePCAF A) {z : ℂ}
    (hz : z ∈ closedSquare 0 1) (T : ContinuousPath ℂ → WithTop ℝ≥0)
    (hT : ∀ t : ℝ≥0, MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) t]
      {ω | T ω < t}) :
    ∀ᵐ ω ∂reflectedPlanarBrownianMotion 0 1 z, T ω < ⊤ → ∀ s : ℝ≥0,
      A ((T ω).untopD 0 + s) ω = A ((T ω).untopD 0) ω +
        clockRationalRegularization A s (ContinuousPath.shift ((T ω).untopD 0) ω) := by
  filter_upwards [hA.path z hz, ae_clockRationalRegularization_add_shift_optionalTime hA hz T hT]
    with ω hp hadd hfin s
  have h := hadd hfin s
  rwa [clockRationalRegularization_eq_of_continuous_monotone hp.2.1 hp.2.2,
    clockRationalRegularization_eq_of_continuous_monotone hp.2.1 hp.2.2] at h

end HarmonicBalls

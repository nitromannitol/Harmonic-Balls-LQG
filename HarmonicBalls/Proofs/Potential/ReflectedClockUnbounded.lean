import HarmonicBalls.Proofs.Potential.ReflectedNeumannMixing
import HarmonicBalls.Proofs.Potential.ReflectedOptionalTimeStrongMarkov
import HarmonicBalls.Proofs.Potential.ReflectedRevuzFormula
import HarmonicBalls.Proofs.Potential.ReflectedTimeChangeSemigroup
import HarmonicBalls.Proofs.Potential.ReflectedClockIdentification

/-!
# A clock with nonzero Revuz measure is unbounded from every start

Let `A` be a positive continuous additive functional of reflected Brownian motion in the unit
square `K₀` (`IsUnitSquarePCAF A`) whose Revuz measure is not zero. Then from every start
`x ∈ K₀` the clock tends to `∞` almost surely (`ae_tendsto_atTop_of_isUnitSquarePCAF`).

Let `D` be the event that `A` is bounded at the integer times (`boundedClockSet`) and
`h(x) = Q_x(D)`. By additivity `D` is invariant under the shifts at integer times
(`ae_shift_mem_boundedClockSet_iff`), so the Markov property at time `1` gives
`h(x) = ∫_{K₀} h(z) k_1(x, z) dz`, and the bounds `δ ≤ k_1 ≤ C` on `K₀ × K₀` give
`δ c ≤ h ≤ C c` with `c = ∫_{K₀} h` (`boundedClockSet_bounds`). Under reflected Brownian motion
started from Lebesgue measure on `K₀`, which is stationary, the probability of
`{A_1 ∘ θ_n > δ} ∩ D` does not depend on `n`, and it tends to `0` since the increments of a
bounded nondecreasing clock tend to `0`; so `{A_1 > 0} ∩ D` is null
(`setLIntegral_reflected_lt_inter_boundedClockSet_eq_zero`). The Markov property at time `1`
with the past event `{A_1 > 0}` bounds the probability of `{A_1 > 0} ∩ D` below by
`δ c` times that of `{A_1 > 0}` (`reflected_pos_inter_boundedClockSet_ge`), which is positive since
the Revuz measure is not zero (`setLIntegral_reflected_pos_ne_zero`). Hence `c = 0` and `h = 0`.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology MarkovProcess
open scoped ENNReal NNReal

namespace HarmonicBalls

variable {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}

/-- The paths along which the clock is bounded at the integer times. -/
def boundedClockSet (A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0) : Set (ContinuousPath ℂ) :=
  {b | ∃ M : ℕ, ∀ m : ℕ, A m b ≤ M}

theorem measurableSet_boundedClockSet (hA : ∀ t, Measurable (A t)) :
    MeasurableSet (boundedClockSet A) := by
  have e : boundedClockSet A = ⋃ M : ℕ, ⋂ m : ℕ, {b | A m b ≤ (M : ℝ≥0)} := by
    ext b
    simp [boundedClockSet]
  rw [e]
  exact MeasurableSet.iUnion fun M => MeasurableSet.iInter fun m =>
    measurableSet_le (hA _) measurable_const

/-- **The bounded event is invariant under the shifts at integer times.** -/
theorem ae_shift_mem_boundedClockSet_iff (hA : IsUnitSquarePCAF A) {z : ℂ}
    (hz : z ∈ closedSquare 0 1) (n : ℕ) :
    ∀ᵐ b ∂reflectedPlanarBrownianMotion 0 1 z,
      (ContinuousPath.shift n b ∈ boundedClockSet A ↔ b ∈ boundedClockSet A) := by
  have hadd : ∀ᵐ b ∂reflectedPlanarBrownianMotion 0 1 z, ∀ m : ℕ,
      A ((n : ℝ≥0) + m) b = A n b + A m (ContinuousPath.shift n b) := by
    refine ae_all_iff.2 fun m => ?_
    filter_upwards [hA.additive z hz m n] with b hb
    rw [hb, pathTimeShift_eq_shift]
  filter_upwards [hadd, hA.path z hz] with b hb hp
  constructor
  · rintro ⟨M, hM⟩
    refine ⟨⌈(A n b : ℝ≥0)⌉₊ + M, fun m => ?_⟩
    calc A m b ≤ A ((n : ℝ≥0) + m) b := hp.2.2 (le_add_of_nonneg_left zero_le)
      _ = A n b + A m (ContinuousPath.shift n b) := hb m
      _ ≤ (⌈(A n b : ℝ≥0)⌉₊ : ℝ≥0) + M := add_le_add (Nat.le_ceil _) (hM m)
      _ = ((⌈(A n b : ℝ≥0)⌉₊ + M : ℕ) : ℝ≥0) := by norm_cast
  · rintro ⟨M, hM⟩
    refine ⟨M, fun m => ?_⟩
    calc A m (ContinuousPath.shift n b) ≤ A n b + A m (ContinuousPath.shift n b) := le_add_self
      _ = A ((n : ℝ≥0) + m) b := (hb m).symm
      _ = A ((n + m : ℕ) : ℝ≥0) b := by rw [Nat.cast_add]
      _ ≤ M := hM (n + m)

/-- **The probability of the bounded event is harmonic** for the Neumann kernel at time `1`. -/
theorem reflected_boundedClockSet_eq (hA : IsUnitSquarePCAF A) {x : ℂ}
    (hx : x ∈ closedSquare 0 1) :
    reflectedPlanarBrownianMotion 0 1 x (boundedClockSet A) =
      ∫⁻ z in closedSquare 0 1, reflectedPlanarBrownianMotion 0 1 z (boundedClockSet A) *
        squareNeumannKernel 1 x z := by
  have hD := measurableSet_boundedClockSet hA.measurable
  have h := lintegral_shift_eq_neumannKernel (Ψ := (boundedClockSet A).indicator 1)
    (measurable_one.indicator hD) x one_ne_zero
  simp only [lintegral_indicator_one hD] at h
  rw [← h, ← lintegral_indicator_one hD]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_shift_mem_boundedClockSet_iff hA hx 1] with b hb
  simp only [Nat.cast_one] at hb
  by_cases h1 : b ∈ boundedClockSet A
  · simp [indicator, h1, hb.2 h1]
  · simp [indicator, h1, mt hb.1 h1]

/-- **Two-sided bounds for the probability of the bounded event**:
`δ c ≤ Q_x(D) ≤ C c` on `K₀`, with `c = ∫_{K₀} Q_z(D) dz`. -/
theorem boundedClockSet_bounds (hA : IsUnitSquarePCAF A) :
    ∃ δ C : ℝ, 0 < δ ∧ ∀ x ∈ closedSquare 0 1,
      ENNReal.ofReal δ * ∫⁻ z in closedSquare 0 1,
          reflectedPlanarBrownianMotion 0 1 z (boundedClockSet A) ≤
        reflectedPlanarBrownianMotion 0 1 x (boundedClockSet A) ∧
      reflectedPlanarBrownianMotion 0 1 x (boundedClockSet A) ≤
        ENNReal.ofReal C * ∫⁻ z in closedSquare 0 1,
          reflectedPlanarBrownianMotion 0 1 z (boundedClockSet A) := by
  have hKm : MeasurableSet (closedSquare (0 : ℂ) 1) := measurableSet_closedSquare_zero_one
  have hD := measurableSet_boundedClockSet hA.measurable
  have hhm : Measurable fun z => reflectedPlanarBrownianMotion 0 1 z (boundedClockSet A) :=
    (reflectedPlanarBrownianMotion 0 1).measurable_coe hD
  obtain ⟨δ, hδ, hδle⟩ := exists_le_neumannKernel_one
  obtain ⟨C, -, hC⟩ := exists_neumannKernel_le one_pos le_rfl
  have hk : ∀ x ∈ closedSquare (0 : ℂ) 1, ∀ z ∈ closedSquare (0 : ℂ) 1,
      squareNeumannKernel 1 x z = ENNReal.ofReal (neumannKernel 1 x z) := fun x hx z hz => by
    rw [ofReal_neumannKernel one_pos hx hz, Real.toNNReal_one]
  refine ⟨δ, C, hδ, fun x hx => ⟨?_, ?_⟩⟩
  · rw [reflected_boundedClockSet_eq hA hx, ← lintegral_const_mul _ hhm]
    refine lintegral_mono_ae ((ae_restrict_iff' hKm).2 (Eventually.of_forall fun z hz => ?_))
    rw [hk x hx z hz, mul_comm]
    exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (hδle x hx z hz))
  · rw [reflected_boundedClockSet_eq hA hx, ← lintegral_const_mul _ hhm]
    refine lintegral_mono_ae ((ae_restrict_iff' hKm).2 (Eventually.of_forall fun z hz => ?_))
    rw [hk x hx z hz, mul_comm]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal (hC 1 ⟨le_rfl, le_rfl⟩ x hx z hz)) le_rfl

/-- **Under the stationary motion the bounded event carries no increment**: for `δ > 0`,
`∫_{K₀} Q_z(A_1 > δ, D) dz = 0`. -/
theorem setLIntegral_reflected_lt_inter_boundedClockSet_eq_zero (hA : IsUnitSquarePCAF A)
    {δ : ℝ≥0} (hδ : 0 < δ) :
    ∫⁻ z in closedSquare 0 1,
      reflectedPlanarBrownianMotion 0 1 z ({b | δ < A 1 b} ∩ boundedClockSet A) = 0 := by
  have hKm : MeasurableSet (closedSquare (0 : ℂ) 1) := measurableSet_closedSquare_zero_one
  have hD := measurableSet_boundedClockSet hA.measurable
  set S : Set (ContinuousPath ℂ) := {b | δ < A 1 b} ∩ boundedClockSet A with hS_def
  have hS : MeasurableSet S := (measurableSet_lt measurable_const (hA.measurable 1)).inter hD
  have hΨ : Measurable (S.indicator (1 : ContinuousPath ℂ → ℝ≥0∞)) := measurable_one.indicator hS
  have hshift : ∀ n : ℕ, Measurable (ContinuousPath.shift (alpha := ℂ) n) := fun n =>
    (ContinuousPath.continuous_shift_fixed (n : ℝ≥0)).measurable
  -- stationarity: the integrals do not depend on `n`
  have hstat : ∀ n : ℕ, ∫⁻ z in closedSquare 0 1, ∫⁻ b, S.indicator 1 (ContinuousPath.shift n b)
      ∂reflectedPlanarBrownianMotion 0 1 z = ∫⁻ z in closedSquare 0 1,
        reflectedPlanarBrownianMotion 0 1 z S := by
    intro n
    rw [setLIntegral_lintegral_shift_eq hΨ n]
    simp_rw [lintegral_indicator_one hS]
  -- the integrals tend to `0`
  have hpt : ∀ z ∈ closedSquare (0 : ℂ) 1, ∀ᵐ b ∂reflectedPlanarBrownianMotion 0 1 z,
      Tendsto (fun n : ℕ => S.indicator (1 : ContinuousPath ℂ → ℝ≥0∞) (ContinuousPath.shift n b))
        atTop (𝓝 0) := by
    intro z hz
    have hadd : ∀ᵐ b ∂reflectedPlanarBrownianMotion 0 1 z, ∀ n : ℕ,
        A ((n : ℝ≥0) + 1) b = A n b + A 1 (ContinuousPath.shift n b) := by
      refine ae_all_iff.2 fun n => ?_
      filter_upwards [hA.additive z hz 1 n] with b hb
      rw [hb, pathTimeShift_eq_shift]
    filter_upwards [ae_all_iff.2 (ae_shift_mem_boundedClockSet_iff hA hz), hadd, hA.path z hz]
      with b hiff hb hp
    by_cases hbD : b ∈ boundedClockSet A
    · obtain ⟨M, hM⟩ := hbD
      set a : ℕ → ℝ := fun n => (A n b : ℝ) with ha
      have hmono : Monotone a := fun m n hmn => by
        simp only [ha]
        exact_mod_cast hp.2.2 (Nat.cast_le.2 hmn)
      have hbdd : BddAbove (range a) := ⟨M, by
        rintro _ ⟨m, rfl⟩
        simp only [ha]
        exact_mod_cast hM m⟩
      have hL := tendsto_atTop_ciSup hmono hbdd
      have hdiff : Tendsto (fun n => a (n + 1) - a n) atTop (𝓝 0) := by
        have := (hL.comp (tendsto_add_atTop_nat 1)).sub hL
        rw [sub_self] at this
        exact this
      have hev : ∀ᶠ n in atTop, a (n + 1) - a n < δ :=
        hdiff.eventually (gt_mem_nhds (by exact_mod_cast hδ))
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev] with n hn
      have he : (A 1 (ContinuousPath.shift n b) : ℝ) = a (n + 1) - a n := by
        simp only [ha, Nat.cast_add, Nat.cast_one, hb n, NNReal.coe_add]
        ring
      have hnot : ¬ δ < A 1 (ContinuousPath.shift n b) := by
        intro hlt
        have : (δ : ℝ) < A 1 (ContinuousPath.shift n b) := by exact_mod_cast hlt
        linarith
      simp [hS_def, indicator, hnot]
    · refine tendsto_const_nhds.congr fun n => ?_
      have : ContinuousPath.shift n b ∉ boundedClockSet A := fun h => hbD ((hiff n).1 h)
      simp [hS_def, indicator, this]
  have hlim : Tendsto (fun n : ℕ => ∫⁻ z in closedSquare 0 1, ∫⁻ b,
      S.indicator 1 (ContinuousPath.shift n b) ∂reflectedPlanarBrownianMotion 0 1 z)
      atTop (𝓝 0) := by
    have hbound : ∀ (n : ℕ) (z : ℂ), ∫⁻ b, S.indicator (1 : ContinuousPath ℂ → ℝ≥0∞)
        (ContinuousPath.shift n b) ∂reflectedPlanarBrownianMotion 0 1 z ≤ 1 := by
      intro n z
      calc ∫⁻ b, S.indicator (1 : ContinuousPath ℂ → ℝ≥0∞) (ContinuousPath.shift n b)
            ∂reflectedPlanarBrownianMotion 0 1 z ≤ ∫⁻ _, 1 ∂reflectedPlanarBrownianMotion 0 1 z :=
            lintegral_mono fun b => indicator_le_self' (fun _ _ => zero_le) _
        _ = 1 := by simp
    have h := tendsto_lintegral_of_dominated_convergence (μ := volume.restrict (closedSquare 0 1))
      (F := fun (n : ℕ) z => ∫⁻ b, S.indicator (1 : ContinuousPath ℂ → ℝ≥0∞)
        (ContinuousPath.shift n b) ∂reflectedPlanarBrownianMotion 0 1 z)
      (f := fun _ => 0) (fun _ => 1)
      (fun n => (hΨ.comp (hshift n)).lintegral_kernel)
      (fun n => Eventually.of_forall (hbound n))
      (by simp)
      ((ae_restrict_iff' hKm).2 (Eventually.of_forall fun z hz => by
        have h := tendsto_lintegral_of_dominated_convergence
          (μ := reflectedPlanarBrownianMotion 0 1 z)
          (F := fun (n : ℕ) b => S.indicator (1 : ContinuousPath ℂ → ℝ≥0∞)
            (ContinuousPath.shift n b)) (f := fun _ => 0) (fun _ => 1)
          (fun n => hΨ.comp (hshift n))
          (fun n => Eventually.of_forall fun b => indicator_le_self' (fun _ _ => zero_le) _)
          (by simp) (hpt z hz)
        simpa using h))
    simpa using h
  have hconst := hlim.congr hstat
  exact tendsto_const_nhds_iff.1 hconst

/-- **The Markov property at time `1` with the past event `{A_1 > 0}`**: if `c ≤ Q_y(D)` on
`K₀`, then `c Q_z(A_1 > 0) ≤ Q_z(A_1 > 0, D)`. -/
theorem reflected_pos_inter_boundedClockSet_ge (hA : IsUnitSquarePCAF A) {z : ℂ}
    (hz : z ∈ closedSquare 0 1) {c : ℝ≥0∞}
    (hc : ∀ y ∈ closedSquare 0 1, c ≤ reflectedPlanarBrownianMotion 0 1 y (boundedClockSet A)) :
    c * reflectedPlanarBrownianMotion 0 1 z {b | 0 < A 1 b} ≤
      reflectedPlanarBrownianMotion 0 1 z ({b | 0 < A 1 b} ∩ boundedClockSet A) := by
  have hD := measurableSet_boundedClockSet hA.measurable
  obtain ⟨g, hgm, hg⟩ := hA.adapted z hz 1
  have hgm' : Measurable g := hgm.mono ((pathNaturalFiltration_le_canonicalFiltration 1).trans
    (ContinuousPath.canonicalFiltration.le 1)) le_rfl
  have hpos : MeasurableSet {v : ℝ≥0 | 0 < v} := measurableSet_lt measurable_const measurable_id
  have hT : ∀ t : ℝ≥0, MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) t]
      {ω : ContinuousPath ℂ | ((1 : ℝ≥0) : WithTop ℝ≥0) < t} := fun t => MeasurableSet.const _
  have hV : ∀ B : Set ℝ≥0, MeasurableSet B → ∀ t : ℝ≥0,
      MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) t]
        (g ⁻¹' B ∩ {ω : ContinuousPath ℂ | ((1 : ℝ≥0) : WithTop ℝ≥0) < t}) := by
    intro B hB t
    by_cases h1t : (1 : ℝ≥0) < t
    · have e : {ω : ContinuousPath ℂ | ((1 : ℝ≥0) : WithTop ℝ≥0) < t} = univ := by
        ext ω
        simp only [mem_ofPred_eq, mem_univ, iff_true]
        exact WithTop.coe_lt_coe.2 h1t
      rw [e, inter_univ]
      have h1 : MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) 1] (g ⁻¹' B) :=
        (pathNaturalFiltration_le_canonicalFiltration 1) _ (hgm hB)
      exact (ContinuousPath.canonicalFiltration (alpha := ℂ)).mono h1t.le _ h1
    · have e : {ω : ContinuousPath ℂ | ((1 : ℝ≥0) : WithTop ℝ≥0) < t} = ∅ := by
        ext ω
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
        exact fun h => h1t (WithTop.coe_lt_coe.1 h)
      rw [e, inter_empty]
      exact @MeasurableSet.empty _ (ContinuousPath.canonicalFiltration (alpha := ℂ) t)
  have hH : Measurable fun p : ℝ≥0 × ContinuousPath ℂ =>
      {v : ℝ≥0 | 0 < v}.indicator (1 : ℝ≥0 → ℝ≥0∞) p.1 *
        (boundedClockSet A).indicator (1 : ContinuousPath ℂ → ℝ≥0∞) p.2 :=
    ((measurable_one.indicator hpos).comp measurable_fst).mul
      ((measurable_one.indicator hD).comp measurable_snd)
  have hsm := OptionalTime.lintegral_reflected_shift_optionalTime_param z
    (fun _ => ((1 : ℝ≥0) : WithTop ℝ≥0)) hT g hgm' hV hH
  simp only [WithTop.coe_lt_top, ofPred_true, Measure.restrict_univ, WithTop.untopD_coe] at hsm
  have hinner : ∀ ω : ContinuousPath ℂ, ∫⁻ ω', {v : ℝ≥0 | 0 < v}.indicator (1 : ℝ≥0 → ℝ≥0∞) (g ω) *
      (boundedClockSet A).indicator 1 ω' ∂reflectedPlanarBrownianMotion 0 1 (ω 1) =
      {v : ℝ≥0 | 0 < v}.indicator 1 (g ω) *
        reflectedPlanarBrownianMotion 0 1 (ω 1) (boundedClockSet A) := by
    intro ω
    rw [lintegral_const_mul _ (measurable_one.indicator hD), lintegral_indicator_one hD]
  simp only [hinner] at hsm
  have hgpos : ∀ ω : ContinuousPath ℂ, {v : ℝ≥0 | 0 < v}.indicator (1 : ℝ≥0 → ℝ≥0∞) (g ω) =
      {ω' : ContinuousPath ℂ | 0 < g ω'}.indicator 1 ω := fun ω => by
    by_cases h : 0 < g ω <;> simp [indicator, h]
  have hset : {b : ContinuousPath ℂ | 0 < A 1 b} =ᵐ[reflectedPlanarBrownianMotion 0 1 z]
      {b | 0 < g b} := hg.mono fun ω h => by
    change (0 < A 1 ω) = (0 < g ω)
    rw [h]
  have hgset : MeasurableSet {b : ContinuousPath ℂ | 0 < g b} :=
    measurableSet_lt measurable_const hgm'
  calc c * reflectedPlanarBrownianMotion 0 1 z {b | 0 < A 1 b}
      = ∫⁻ ω, {ω' : ContinuousPath ℂ | 0 < g ω'}.indicator 1 ω * c
          ∂reflectedPlanarBrownianMotion 0 1 z := by
        rw [lintegral_mul_const _ (measurable_one.indicator hgset), lintegral_indicator_one hgset,
          measure_congr hset, mul_comm]
    _ ≤ ∫⁻ ω, {v : ℝ≥0 | 0 < v}.indicator (1 : ℝ≥0 → ℝ≥0∞) (g ω) *
          reflectedPlanarBrownianMotion 0 1 (ω 1) (boundedClockSet A)
          ∂reflectedPlanarBrownianMotion 0 1 z := by
        refine lintegral_mono_ae ?_
        filter_upwards [OptionalTime.ae_forall_mem_closedSquare_reflected z] with ω hω
        rw [hgpos ω]
        exact mul_le_mul' le_rfl (hc _ (hω 1))
    _ = ∫⁻ ω, {v : ℝ≥0 | 0 < v}.indicator (1 : ℝ≥0 → ℝ≥0∞) (g ω) *
          (boundedClockSet A).indicator 1 (ContinuousPath.shift 1 ω)
          ∂reflectedPlanarBrownianMotion 0 1 z := hsm.symm
    _ = reflectedPlanarBrownianMotion 0 1 z ({b | 0 < A 1 b} ∩ boundedClockSet A) := by
        rw [← lintegral_indicator_one ((measurableSet_lt measurable_const (hA.measurable 1)).inter hD)]
        refine lintegral_congr_ae ?_
        filter_upwards [hg, ae_shift_mem_boundedClockSet_iff hA hz 1] with ω hω hiff
        simp only [Nat.cast_one] at hiff
        by_cases h1 : 0 < g ω <;> by_cases h2 : ω ∈ boundedClockSet A <;>
          simp [indicator, hω, h1, h2, hiff]

/-- **The clock charges the stationary motion**: if the Revuz measure is not zero, then
`∫_{K₀} Q_z(A_1 > 0) dz ≠ 0`. -/
theorem setLIntegral_reflected_pos_ne_zero (hA : IsUnitSquarePCAF A)
    (hν : unitSquareRevuzMeasure A univ ≠ 0) :
    ∫⁻ z in closedSquare 0 1, reflectedPlanarBrownianMotion 0 1 z {b | 0 < A 1 b} ≠ 0 := by
  have hKm : MeasurableSet (closedSquare (0 : ℂ) 1) := measurableSet_closedSquare_zero_one
  have hS : MeasurableSet {b : ContinuousPath ℂ | 0 < A 1 b} :=
    measurableSet_lt measurable_const (hA.measurable 1)
  intro h0
  apply hν
  have hz : ∀ᵐ z ∂volume.restrict (closedSquare 0 1),
      reflectedPlanarBrownianMotion 0 1 z {b | 0 < A 1 b} = 0 :=
    (lintegral_eq_zero_iff ((reflectedPlanarBrownianMotion 0 1).measurable_coe hS)).1 h0
  rw [← lintegral_one, lintegral_unitSquareRevuzMeasure_of_isUnitSquarePCAF hA
    (g := fun _ => (1 : ℝ≥0∞)) measurable_const]
  have hzero : ∀ᵐ z ∂volume.restrict (closedSquare 0 1), ∫⁻ b, ∫⁻ _, (1 : ℝ≥0∞)
      ∂clockOccupationMeasure (fun t => A t b) b ∂reflectedPlanarBrownianMotion 0 1 z = 0 := by
    filter_upwards [hz, ae_restrict_mem hKm] with z hz0 hzK
    have hb0 : ∀ᵐ b ∂reflectedPlanarBrownianMotion 0 1 z, A 1 b = 0 := by
      have h := (measure_eq_zero_iff_ae_notMem.1 hz0)
      filter_upwards [h] with b hb
      exact le_antisymm (not_lt.1 hb) zero_le
    rw [lintegral_congr_ae (g := fun _ => 0) ?_, lintegral_zero]
    filter_upwards [hb0, hA.path z hzK] with b hb hp
    rw [lintegral_one]
    have hbm : Measurable fun s : ℝ => b s.toNNReal :=
      (b.continuous.comp continuous_real_toNNReal).measurable
    unfold clockOccupationMeasure
    rw [Measure.map_apply hbm MeasurableSet.univ,
      preimage_univ, Measure.restrict_apply_univ, clockStieltjesFunction_measure_Ioc hp.2.2 hp.2.1,
      Real.toNNReal_one, Real.toNNReal_zero, hb, hp.1]
    simp
  rw [lintegral_congr_ae hzero, lintegral_zero]

/-- **A clock with nonzero Revuz measure tends to `∞` from every start** of `K₀`. -/
theorem ae_tendsto_atTop_of_isUnitSquarePCAF (hA : IsUnitSquarePCAF A)
    (hν : unitSquareRevuzMeasure A univ ≠ 0) {x : ℂ} (hx : x ∈ closedSquare 0 1) :
    ∀ᵐ b ∂reflectedPlanarBrownianMotion 0 1 x, Tendsto (fun t => A t b) atTop atTop := by
  have hKm : MeasurableSet (closedSquare (0 : ℂ) 1) := measurableSet_closedSquare_zero_one
  have hD := measurableSet_boundedClockSet hA.measurable
  have hS : MeasurableSet {b : ContinuousPath ℂ | 0 < A 1 b} :=
    measurableSet_lt measurable_const (hA.measurable 1)
  obtain ⟨δ, C, hδ, hbd⟩ := boundedClockSet_bounds hA
  set c := ∫⁻ z in closedSquare 0 1, reflectedPlanarBrownianMotion 0 1 z (boundedClockSet A)
    with hc_def
  -- the event `{A_1 > 0} ∩ D` is null under the stationary motion
  have h0 : ∫⁻ z in closedSquare 0 1,
      reflectedPlanarBrownianMotion 0 1 z ({b | 0 < A 1 b} ∩ boundedClockSet A) = 0 := by
    refine le_antisymm ?_ zero_le
    have hmk : ∀ k : ℕ, Measurable fun z => reflectedPlanarBrownianMotion 0 1 z
        ({b | ((k : ℝ≥0) + 1)⁻¹ < A 1 b} ∩ boundedClockSet A) := fun k =>
      (reflectedPlanarBrownianMotion 0 1).measurable_coe
        ((measurableSet_lt measurable_const (hA.measurable 1)).inter hD)
    calc ∫⁻ z in closedSquare 0 1,
          reflectedPlanarBrownianMotion 0 1 z ({b | 0 < A 1 b} ∩ boundedClockSet A)
        ≤ ∫⁻ z in closedSquare 0 1, ∑' k : ℕ, reflectedPlanarBrownianMotion 0 1 z
            ({b | ((k : ℝ≥0) + 1)⁻¹ < A 1 b} ∩ boundedClockSet A) := by
          refine lintegral_mono fun z => ?_
          refine (measure_mono ?_).trans (measure_iUnion_le _)
          rintro b ⟨hb, hbD⟩
          obtain ⟨k, hk⟩ := exists_nat_one_div_lt (show (0 : ℝ≥0) < A 1 b from hb)
          exact mem_iUnion.2 ⟨k, ⟨by simpa [one_div] using hk, hbD⟩⟩
      _ = ∑' k : ℕ, ∫⁻ z in closedSquare 0 1, reflectedPlanarBrownianMotion 0 1 z
            ({b | ((k : ℝ≥0) + 1)⁻¹ < A 1 b} ∩ boundedClockSet A) :=
          lintegral_tsum fun k => (hmk k).aemeasurable
      _ = 0 := ENNReal.tsum_eq_zero.2 fun k =>
          setLIntegral_reflected_lt_inter_boundedClockSet_eq_zero hA (by positivity)
  -- the Markov property bounds it below
  have hge : ENNReal.ofReal δ * c * ∫⁻ z in closedSquare 0 1,
      reflectedPlanarBrownianMotion 0 1 z {b | 0 < A 1 b} ≤ ∫⁻ z in closedSquare 0 1,
        reflectedPlanarBrownianMotion 0 1 z ({b | 0 < A 1 b} ∩ boundedClockSet A) := by
    rw [← lintegral_const_mul _ ((reflectedPlanarBrownianMotion 0 1).measurable_coe hS)]
    refine lintegral_mono_ae ((ae_restrict_iff' hKm).2 (Eventually.of_forall fun z hz => ?_))
    exact reflected_pos_inter_boundedClockSet_ge hA hz fun y hy => (hbd y hy).1
  have hpos := setLIntegral_reflected_pos_ne_zero hA hν
  have hc : c = 0 := by
    rw [h0, nonpos_iff_eq_zero] at hge
    rcases mul_eq_zero.1 hge with h | h
    · rcases mul_eq_zero.1 h with h' | h'
      · exact absurd h' (ENNReal.ofReal_pos.2 hδ).ne'
      · exact h'
    · exact absurd h hpos
  have hx0 : reflectedPlanarBrownianMotion 0 1 x (boundedClockSet A) = 0 :=
    le_antisymm ((hbd x hx).2.trans (by rw [hc, mul_zero])) zero_le
  have hae : ∀ᵐ b ∂reflectedPlanarBrownianMotion 0 1 x, b ∉ boundedClockSet A :=
    measure_eq_zero_iff_ae_notMem.1 hx0
  filter_upwards [hae, hA.path x hx] with b hb hp
  refine tendsto_atTop_atTop_of_monotone hp.2.2 fun M => ?_
  by_contra hcon
  exact hb ⟨⌈M⌉₊, fun m => (not_le.1 fun h => hcon ⟨m, h⟩).le.trans (Nat.le_ceil M)⟩

end HarmonicBalls

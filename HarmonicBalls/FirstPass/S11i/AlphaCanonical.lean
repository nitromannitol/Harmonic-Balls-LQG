import HarmonicBalls.FirstPass.S11i.WindowFrequency

/-!
# Window frequencies of the canonical field `h^α` modulo constants (write-up Steps 7.1 and 9)

The pairings of the field `h^α = h^ℂ - α log|·|` (`fieldPairing`, `HarmonicBalls/Defs/GFF.lean:113`) on mean-zero test
functions are the pairings of `h^ℂ` shifted by the logarithmic drift `φ ↦ -α ∫ φ(x) log|x| dx`. This drift is invariant
under the canonical dilation on mean-zero tests, `∫ κ₁φ · log|·| = ∫ φ · log|·|` (with `κ₁ = dilateTest 1`), because the
constant `log 2` multiplies `∫ φ = 0`. Hence the window frequency of an event along `h^α` equals the window frequency of the
preimage event along `h^ℂ`, and `ae_canonical_window_frequency` (Birkhoff, `WindowFrequency.lean`) transfers to every `α`
without a new ergodicity argument. This is the "law of `h^α` is also ergodic" of write-up Step 8, and it gives the
frequency `p = P_can[e_M(q_{0,1}(h^γ))]` of eq. (16) on the canonical field of `h^γ`.
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Filter Topology Set

/-- The logarithmic drift of `h^α` on a test function: `φ ↦ -α ∫ φ(x) log|x| dx` (the drift in `fieldPairing`). -/
noncomputable def logDriftFun (α : ℝ) (φ : ℂ → ℝ) : ℝ :=
  -(α * ∫ x, φ x * Real.log ‖x‖)

/-- The drift as a vector of canonical pairings (mean-zero test functions on `ℂ`). -/
noncomputable def logDrift (α : ℝ) : ModConstTestPairings (Set.univ : Set ℂ) :=
  fun i => logDriftFun α i.1

/-- Translation of canonical pairings by a fixed vector `v`. -/
noncomputable def transl (v : ModConstTestPairings (Set.univ : Set ℂ)) :
    ModConstTestPairings (Set.univ : Set ℂ) → ModConstTestPairings (Set.univ : Set ℂ) :=
  fun L i => L i + v i

theorem measurable_transl (v : ModConstTestPairings (Set.univ : Set ℂ)) : Measurable (transl v) :=
  Measurable.of_eval fun i => by
    show Measurable fun x : ModConstTestPairings (Set.univ : Set ℂ) => x i + v i
    exact (measurable_pi_apply i : Measurable fun x : ModConstTestPairings (Set.univ : Set ℂ) => x i).add_const (v i)

/-- A compactly supported function is bounded on its support. -/
theorem exists_radius_of_hasCompactSupport {k : ℂ → ℝ} (hk : HasCompactSupport k) :
    ∃ R : ℝ, ∀ z, k z ≠ 0 → ‖z‖ ≤ R := by
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).1 hk.isCompact.isBounded
  refine ⟨R, fun z hz => ?_⟩
  have := hR (subset_tsupport k (Function.mem_support.2 hz))
  simpa using this

/-- The drift is invariant under the dilation on mean-zero tests: `∫ κ₁φ · log|·| = ∫ φ · log|·|`. -/
theorem integral_dilateTest_one_mul_log {k : ℂ → ℝ} (hk : IsTestFunction univ k) (hmean : ∫ z, k z = 0) :
    ∫ y, dilateTest 1 k y * Real.log ‖y‖ = ∫ z, k z * Real.log ‖z‖ := by
  rw [integral_dilateTest_mul 1 k (fun y => Real.log ‖y‖)]
  obtain ⟨R, hR⟩ := exists_radius_of_hasCompactSupport hk.2.1
  have hint : Integrable (fun z => k z * Real.log ‖z - (0 : ℂ)‖) :=
    integrable_mul_log_norm_sub hk hR 0
  simp only [sub_zero] at hint
  have hcongr : ∀ᵐ z ∂(volume : Measure ℂ),
      k z * Real.log ‖((2 : ℝ) ^ 1)⁻¹ • z‖ = k z * Real.log ‖z‖ - Real.log 2 * k z := by
    have h0 : ∀ᵐ z ∂(volume : Measure ℂ), z ≠ 0 := compl_mem_ae_iff.2 (measure_singleton 0)
    filter_upwards [h0] with z hz
    have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.2 hz
    have h2 : ((2 : ℝ) ^ 1)⁻¹ ≠ 0 := by positivity
    rw [norm_smul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ ((2 : ℝ) ^ 1)⁻¹),
      Real.log_mul h2 hn, pow_one, Real.log_inv]
    ring
  have hk_int : Integrable k := hk.1.continuous.integrable_of_hasCompactSupport hk.2.1
  rw [integral_congr_ae hcongr, integral_sub hint (hk_int.const_mul (Real.log 2)), integral_const_mul, hmean,
    mul_zero, sub_zero]

/-- The drift is dilation invariant on each mean-zero test function of the canonical index set. -/
theorem logDrift_dilOp (α : ℝ) (i : {φ : ℂ → ℝ // IsTestFunction univ φ ∧ ∫ x, φ x = 0}) :
    logDrift α ⟨dilateTest 1 i.1, isTestFunction_dilateTest i.2.1 1, (integral_dilateTest 1 i.1).trans i.2.2⟩ =
      logDrift α i := by
  show logDriftFun α (dilateTest 1 i.1) = logDriftFun α i.1
  unfold logDriftFun
  rw [integral_dilateTest_one_mul_log i.2.1 i.2.2]

/-- The canonical dilation commutes with the translation by the drift `logDrift α`. -/
theorem dilOp_transl (α : ℝ) (L : ModConstTestPairings (Set.univ : Set ℂ)) :
    dilOp (transl (logDrift α) L) = transl (logDrift α) (dilOp L) := by
  funext i
  dsimp only [dilOp, transl]
  rw [logDrift_dilOp α i]

theorem dilOp_iterate_transl (α : ℝ) (n : ℕ) (L : ModConstTestPairings (Set.univ : Set ℂ)) :
    dilOp^[n] (transl (logDrift α) L) = transl (logDrift α) (dilOp^[n] L) := by
  induction n generalizing L with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, dilOp_transl, ih]

/-- The canonical field of `h^α = h^ℂ - α log|·|` modulo constants: the pairings `φ ↦ (h^α, φ)` on mean-zero tests. -/
noncomputable def alphaCanon {Ω : Type*} (α : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (ω : Ω) :
    ModConstTestPairings (Set.univ : Set ℂ) :=
  fun i => fieldPairing α (hC ω) i.1

theorem alphaCanon_eq {Ω : Type*} (α : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (ω : Ω) :
    alphaCanon α hC ω = transl (logDrift α) (fun i => hC ω i.1) := by
  funext i
  simp [alphaCanon, transl, logDrift, logDriftFun, fieldPairing, sub_eq_add_neg]

/-- Window frequency along the canonical field of `h^α` (write-up Step 9 uses it at `α = γ`): for almost every `ω`, the
frequency of the visits `dilOp^[n] (alphaCanon α hC ω) ∈ E` in `[N+1, 2N]`, divided by `N`, tends to the probability of
`{alphaCanon α hC · ∈ E}`. Input: Birkhoff's theorem `hB` (frozen) and the canonical ergodicity of `dilOp`. -/
theorem ae_alpha_canonical_window_frequency {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc)
    (hB : BirkhoffPointwiseErgodic.{0}) (α : ℝ)
    {E : Set (ModConstTestPairings (Set.univ : Set ℂ))} (hE : MeasurableSet E) :
    ∀ᵐ ω ∂P, Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.Icc (N + 1) (2 * N), E.indicator (fun _ => (1 : ℝ)) (dilOp^[n] (alphaCanon α hC ω))) / (N : ℝ))
      atTop (𝓝 (P {ω | alphaCanon α hC ω ∈ E}).toReal) := by
  set E' : Set (ModConstTestPairings (Set.univ : Set ℂ)) := transl (logDrift α) ⁻¹' E with hE'_def
  have hE' : MeasurableSet E' := measurable_transl (logDrift α) hE
  have hX : Measurable (fun ω (i : CanonIdx) => hC ω i.1) := measurable_canonical hh
  have hA := ae_canonical_window_frequency hh hB hE'
  have hB' := ae_of_ae_map hX.aemeasurable hA
  have hset : (fun ω (i : CanonIdx) => hC ω i.1) ⁻¹' E' = {ω | alphaCanon α hC ω ∈ E} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, alphaCanon_eq, hE'_def]
  have hval : (canonicalLaw hC P E').toReal = (P {ω | alphaCanon α hC ω ∈ E}).toReal := by
    unfold canonicalLaw
    rw [Measure.map_apply hX hE', hset]
  rw [← hval]
  filter_upwards [hB'] with ω hω
  refine Tendsto.congr (fun N => ?_) hω
  refine congrArg (fun s : ℝ => s / (N : ℝ)) (Finset.sum_congr rfl fun n _ => ?_)
  rw [alphaCanon_eq, dilOp_iterate_transl]
  simp only [hE'_def]
  rfl

end HarmonicBalls

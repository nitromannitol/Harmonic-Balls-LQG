import Mathlib
import HarmonicBalls.Proofs.Sec11.ClosureScales.BorelCircleLimitDecoder
import HarmonicBalls.Proofs.Sec11.ClosureScales.MollifiedCircleGaussianL2
import HarmonicBalls.Proofs.Sec11.ClosureScales.MollifiedContinuousCircleLimit
import HarmonicBalls.Proofs.Sec11.ClosureScales.MollifiedLogCircleLimit
import HarmonicBalls.Proofs.Sec11.ClosureScales.RootedShiftProfile
import HarmonicBalls.Proposed.DuplantierMillerSheffield

/-!
# Compatibility of the circle-limit decoder with deterministic additions

Source: r10 written proof `notes/sec11-proof/sec11-proof-r10.tex`, lines 1313-1350 (the Borel decoder, then the two
continuous additions). Audited in `AUDIT-r9.md` 959-998 and reaffirmed in `AUDIT-r10.md` 110.

Setting. `I` is countable, `q : I → CircleDomain` has dense range, `rho` is a literal mollifier (`IsLiteralMollifier`),
and `eps : I → ℕ → ℝ` has positive terms with `eps i → 0⁺` for each `i`. For `q i = (r, c)` put
`psi i n = circleMollifier rho c r (eps i n)`, the mollified circle average over `∂B_r(c)` at scale `eps i n`.
Raw functionals are arbitrary maps `T : (ℂ → ℝ) → ℝ`; nothing here assumes linearity of `T` or a distributional
representation of `T`.

Results.
* `circleCompatDecoder` is the named pairing decoder `T ↦ circleLimitDecoder q (fun i n S => S (psi i n)) T`.
  `circleCompatDecoder_spec` states that it is measurable for the pairing σ-algebra, has the valid and invalid
  characterizations, and is the unique map with them (from `exists_measurable_circle_limit_decoder_pairing`,
  `circleLimitDecoder_of_tendsto`, `circleLimitDecoder_of_not_exists`, `circleLimitDecoder_unique`).
* `circleAverageFun u hu` is `Ucirc u`, the continuous function `p ↦ Real.circleAverage u p.val.2 p.val.1` on
  `CircleDomain`. `circleDMSShiftFun γ z F` is the continuous function
  `p ↦ F p - γ log max(r, |c - z|) + γ ⨍_{∂B_r(c)} log max(1, |·|)` (Duplantier-Miller-Sheffield logarithmic shift).
* `circleCompat_addition`: under the single baseline premise `n ↦ T (psi i n) → F (q i)` for every `i`, the decoder of
  `T` is `F`. For every continuous `u` and every `γ`, `z`, the added integrals are integrable against each `psi i n`,
  and the decoder of the shifted functional is `F + Ucirc u`, resp. `circleDMSShiftFun γ z F`.

Inputs. `mollified_continuous_circle_limit` (approximate identity on a circle, continuous `u`) and
`mollified_log_circle_limit` (logarithmic insertion). The function `dmsShift` is used as a definition only, from
`HarmonicBalls.Proposed.DuplantierMillerSheffield` (Lemma A.10 of Duplantier-Miller-Sheffield, operator source-check
pending); no proposition of that file is used. The joint continuity of the circle average is re-proved locally by the
parametric-integral argument of `Section6.continuous_circleAverage_radius_center`: importing that module would pull in
the Lattice-Probability port, which this file does not consume.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace HarmonicBalls

/-- The literal mollified circle average of the `i`-th point at scale `eps i n`:
`psi i n = circleMollifier rho (q i).val.2 (q i).val.1 (eps i n)`. -/
def circleCompatPsi (rho : ℂ → ℝ) {I : Type*} (q : I → CircleDomain) (eps : I → ℕ → ℝ) (i : I) (n : ℕ) :
    ℂ → ℝ :=
  circleMollifier rho (q i).val.2 (q i).val.1 (eps i n)

/-- The named pairing decoder `D(T) = circleLimitDecoder q (fun i n S => S (psi i n)) T` (r10 lines 1313-1323). -/
def circleCompatDecoder (rho : ℂ → ℝ) {I : Type*} (q : I → CircleDomain) (eps : I → ℕ → ℝ)
    (T : (ℂ → ℝ) → ℝ) : C(CircleDomain, ℝ) :=
  circleLimitDecoder q (fun (i : I) (n : ℕ) (S : (ℂ → ℝ) → ℝ) => S (circleCompatPsi rho q eps i n)) T

/-- Joint continuity of the circle average in the radius and the centre, for a continuous `u`. This is the
parametric-integral argument of `Section6.continuous_circleAverage_radius_center`, repeated locally. -/
theorem continuous_circleAverage_pair {u : ℂ → ℝ} (hu : Continuous u) :
    Continuous fun p : ℝ × ℂ => Real.circleAverage u p.2 p.1 := by
  unfold Real.circleAverage
  refine continuous_const.mul ?_
  have hf : Continuous fun x : (ℝ × ℂ) × ℝ => u (circleMap x.1.2 x.1.1 x.2) :=
    hu.comp (by unfold circleMap; fun_prop)
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun (p : ℝ × ℂ) (θ : ℝ) => u (circleMap p.2 p.1 θ)) hf 0 (2 * Real.pi)

/-- The circle average of a continuous `u` as a function of the point `p = (r, c)` of `CircleDomain`. -/
theorem continuous_circleAverage_domain {u : ℂ → ℝ} (hu : Continuous u) :
    Continuous fun p : CircleDomain => Real.circleAverage u p.val.2 p.val.1 :=
  (continuous_circleAverage_pair hu).comp continuous_subtype_val

/-- The continuous function `Ucirc u` on `CircleDomain`: `Ucirc u (p) = Real.circleAverage u p.val.2 p.val.1`. -/
def circleAverageFun (u : ℂ → ℝ) (hu : Continuous u) : C(CircleDomain, ℝ) :=
  ⟨fun p => Real.circleAverage u p.val.2 p.val.1, continuous_circleAverage_domain hu⟩

@[simp] theorem circleAverageFun_apply (u : ℂ → ℝ) (hu : Continuous u) (p : CircleDomain) :
    circleAverageFun u hu p = Real.circleAverage u p.val.2 p.val.1 :=
  rfl

/-- Continuity of the literal shift formula `p ↦ F p - γ log max(r, |c - z|) + γ ⨍_{∂B_r(c)} log max(1, |·|)`. -/
theorem continuous_circleDMSShift (γ : ℝ) (z : ℂ) (F : C(CircleDomain, ℝ)) :
    Continuous fun p : CircleDomain =>
      F p - γ * Real.log (max p.val.1 ‖p.val.2 - z‖) + γ * Real.circleAverage logMaxOne p.val.2 p.val.1 := by
  have hmax : Continuous fun p : CircleDomain => max p.val.1 ‖p.val.2 - z‖ := by fun_prop
  have hlog : Continuous fun p : CircleDomain => Real.log (max p.val.1 ‖p.val.2 - z‖) :=
    hmax.log fun p => (lt_max_of_lt_left p.property).ne'
  have hcirc : Continuous fun p : CircleDomain => Real.circleAverage logMaxOne p.val.2 p.val.1 :=
    continuous_circleAverage_logMaxOne.comp
      ((continuous_snd.comp continuous_subtype_val).prodMk (continuous_fst.comp continuous_subtype_val))
  exact (F.continuous.sub (continuous_const.mul hlog)).add (continuous_const.mul hcirc)

/-- The continuous function `G(γ, z, F)` on `CircleDomain` with the literal formula
`p ↦ F p - γ log max(r, |c - z|) + γ ⨍_{∂B_r(c)} log max(1, |·|)`, for `p = (r, c)`. -/
def circleDMSShiftFun (γ : ℝ) (z : ℂ) (F : C(CircleDomain, ℝ)) : C(CircleDomain, ℝ) :=
  ⟨fun p => F p - γ * Real.log (max p.val.1 ‖p.val.2 - z‖) + γ * Real.circleAverage logMaxOne p.val.2 p.val.1,
    continuous_circleDMSShift γ z F⟩

@[simp] theorem circleDMSShiftFun_apply (γ : ℝ) (z : ℂ) (F : C(CircleDomain, ℝ)) (p : CircleDomain) :
    circleDMSShiftFun γ z F p =
      F p - γ * Real.log (max p.val.1 ‖p.val.2 - z‖) + γ * Real.circleAverage logMaxOne p.val.2 p.val.1 :=
  rfl

/-- In kernel form, `psi i n v` is the circle average over `∂B_r(c)` of `x ↦ (eps^2)⁻¹ rho (eps⁻¹ • (x - v))`. -/
theorem circleCompatPsi_apply (rho : ℂ → ℝ) {I : Type*} (q : I → CircleDomain) (eps : I → ℕ → ℝ) (i : I)
    (n : ℕ) (v : ℂ) :
    circleCompatPsi rho q eps i n v =
      Real.circleAverage (fun x : ℂ => ((eps i n : ℝ) ^ 2)⁻¹ * rho ((eps i n : ℝ)⁻¹ • (x - v)))
        (q i).val.2 (q i).val.1 := by
  unfold circleCompatPsi
  exact circleMollifier_eq rho _ _ _ v

/-- Each `psi i n` is a test function on `Set.univ` (`isTestFunction_circleMollifier`). -/
theorem isTestFunction_circleCompatPsi (rho : ℂ → ℝ) (hρ : IsLiteralMollifier rho) {I : Type*}
    (q : I → CircleDomain) (eps : I → ℕ → ℝ) (heps_pos : ∀ i n, 0 < eps i n) (i : I) (n : ℕ) :
    IsTestFunction Set.univ (circleCompatPsi rho q eps i n) :=
  isTestFunction_circleMollifier hρ (w := (q i).val.2) (q i).property (heps_pos i n)

/-- Integrability of a continuous addition against each `psi i n` (`mollified_continuous_circle_limit`). -/
theorem integrable_circleCompat_mul (rho : ℂ → ℝ) (hρ : IsLiteralMollifier rho) {I : Type*}
    (q : I → CircleDomain) (eps : I → ℕ → ℝ) (heps_pos : ∀ i n, 0 < eps i n) {u : ℂ → ℝ} (hu : Continuous u)
    (i : I) (n : ℕ) :
    Integrable (fun v : ℂ => u v * circleCompatPsi rho q eps i n v) :=
  (mollified_continuous_circle_limit hρ.even hρ.nonneg hρ.smooth hρ.supp hρ.mass hu (q i).property
    (q i).val.2).1 (eps i n) (heps_pos i n)

/-- Convergence of a continuous addition against the mollified circle averages along `eps i n`: the approximate
identity limit `mollified_continuous_circle_limit`, composed with `eps i → 0⁺`. -/
theorem tendsto_circleCompat_mul (rho : ℂ → ℝ) (hρ : IsLiteralMollifier rho) {I : Type*}
    (q : I → CircleDomain) (eps : I → ℕ → ℝ) (heps : ∀ i, Tendsto (eps i) atTop (𝓝[>] 0)) {u : ℂ → ℝ}
    (hu : Continuous u) (i : I) :
    Tendsto (fun n : ℕ => ∫ v : ℂ, u v * circleCompatPsi rho q eps i n v) atTop
      (𝓝 (Real.circleAverage u (q i).val.2 (q i).val.1)) :=
  ((mollified_continuous_circle_limit hρ.even hρ.nonneg hρ.smooth hρ.supp hρ.mass hu (q i).property
    (q i).val.2).2).comp (heps i)

/-- Integrability of the logarithmic shift against each `psi i n` (`mollified_log_circle_limit`). -/
theorem integrable_circleCompat_dms (rho : ℂ → ℝ) (hρ : IsLiteralMollifier rho) {I : Type*}
    (q : I → CircleDomain) (eps : I → ℕ → ℝ) (heps_pos : ∀ i n, 0 < eps i n) (γ : ℝ) (z : ℂ) (i : I) (n : ℕ) :
    Integrable (fun v : ℂ => dmsShift γ z v * circleCompatPsi rho q eps i n v) := by
  simp only [circleCompatPsi_apply]
  exact (mollified_log_circle_limit rho hρ.even hρ.nonneg hρ.smooth hρ.supp hρ.mass γ z (q i).val.2
    (q i).property).1 (eps i n) (heps_pos i n)

/-- Convergence of the logarithmic shift against the mollified circle averages along `eps i n`, with the literal limit
`-γ log max(r, |c - z|) + γ ⨍_{∂B_r(c)} log max(1, |·|)` (`mollified_log_circle_limit`). -/
theorem tendsto_circleCompat_dms (rho : ℂ → ℝ) (hρ : IsLiteralMollifier rho) {I : Type*}
    (q : I → CircleDomain) (eps : I → ℕ → ℝ) (heps : ∀ i, Tendsto (eps i) atTop (𝓝[>] 0)) (γ : ℝ) (z : ℂ)
    (i : I) :
    Tendsto (fun n : ℕ => ∫ v : ℂ, dmsShift γ z v * circleCompatPsi rho q eps i n v) atTop
      (𝓝 (-γ * Real.log (max (q i).val.1 ‖(q i).val.2 - z‖) +
        γ * Real.circleAverage logMaxOne (q i).val.2 (q i).val.1)) := by
  refine Filter.Tendsto.congr (fun n => ?_) ((mollified_log_circle_limit rho hρ.even hρ.nonneg hρ.smooth
    hρ.supp hρ.mass γ z (q i).val.2 (q i).property).2.comp (heps i))
  simp only [Function.comp_apply, circleCompatPsi_apply]

/-- Valid characterization of the named decoder: if every `n ↦ T (psi i n)` tends to `F (q i)`, the decoder is `F`
(`circleLimitDecoder_of_tendsto`). -/
theorem circleCompatDecoder_valid (rho : ℂ → ℝ) {I : Type*} {q : I → CircleDomain} (hq : DenseRange q)
    (eps : I → ℕ → ℝ) {T : (ℂ → ℝ) → ℝ} {F : C(CircleDomain, ℝ)}
    (hT : ∀ i, Tendsto (fun n => T (circleCompatPsi rho q eps i n)) atTop (𝓝 (F (q i)))) :
    circleCompatDecoder rho q eps T = F :=
  circleLimitDecoder_of_tendsto (a := fun (i : I) (n : ℕ) (S : (ℂ → ℝ) → ℝ) => S (circleCompatPsi rho q eps i n)) (s := T) hq hT

/-- Invalid characterization of the named decoder: if no continuous `F` is a limit, the decoder is `0`
(`circleLimitDecoder_of_not_exists`). -/
theorem circleCompatDecoder_invalid (rho : ℂ → ℝ) {I : Type*} (q : I → CircleDomain) (eps : I → ℕ → ℝ)
    {T : (ℂ → ℝ) → ℝ}
    (hns : ¬ ∃ F : C(CircleDomain, ℝ),
      ∀ i, Tendsto (fun n => T (circleCompatPsi rho q eps i n)) atTop (𝓝 (F (q i)))) :
    circleCompatDecoder rho q eps T = 0 :=
  circleLimitDecoder_of_not_exists (a := fun (i : I) (n : ℕ) (S : (ℂ → ℝ) → ℝ) => S (circleCompatPsi rho q eps i n)) (s := T) hns

/-- **The named decoder.** `circleCompatDecoder` is measurable for the pairing σ-algebra, has the valid and invalid
characterizations, and is the unique map with these characterizations (`exists_measurable_circle_limit_decoder_pairing`
and `circleLimitDecoder_unique`). -/
theorem circleCompatDecoder_spec (rho : ℂ → ℝ) (hρ : IsLiteralMollifier rho) {I : Type*} [Countable I]
    (q : I → CircleDomain) (hq : DenseRange q) (eps : I → ℕ → ℝ) (heps_pos : ∀ i n, 0 < eps i n) :
    @Measurable ((ℂ → ℝ) → ℝ) (C(CircleDomain, ℝ)) pairingMeasSpace _ (circleCompatDecoder rho q eps) ∧
    (∀ (T : (ℂ → ℝ) → ℝ) (F : C(CircleDomain, ℝ)),
      (∀ i, Tendsto (fun n => T (circleCompatPsi rho q eps i n)) atTop (𝓝 (F (q i)))) →
        circleCompatDecoder rho q eps T = F) ∧
    (∀ T : (ℂ → ℝ) → ℝ,
      (¬ ∃ F : C(CircleDomain, ℝ),
        ∀ i, Tendsto (fun n => T (circleCompatPsi rho q eps i n)) atTop (𝓝 (F (q i)))) →
          circleCompatDecoder rho q eps T = 0) ∧
    (∀ Dec : ((ℂ → ℝ) → ℝ) → C(CircleDomain, ℝ),
      (∀ (T : (ℂ → ℝ) → ℝ) (F : C(CircleDomain, ℝ)),
        (∀ i, Tendsto (fun n => T (circleCompatPsi rho q eps i n)) atTop (𝓝 (F (q i)))) → Dec T = F) →
      (∀ T : (ℂ → ℝ) → ℝ,
        (¬ ∃ F : C(CircleDomain, ℝ),
          ∀ i, Tendsto (fun n => T (circleCompatPsi rho q eps i n)) atTop (𝓝 (F (q i)))) →
            Dec T = 0) →
      Dec = circleCompatDecoder rho q eps) := by
  obtain ⟨Dec, hDm, h1, h2⟩ := exists_measurable_circle_limit_decoder_pairing q hq
    (circleCompatPsi rho q eps) (fun i n => isTestFunction_circleCompatPsi rho hρ q eps heps_pos i n)
  have hDec : Dec = circleCompatDecoder rho q eps :=
    circleLimitDecoder_unique hq (a := fun (i : I) (n : ℕ) (S : (ℂ → ℝ) → ℝ) => S (circleCompatPsi rho q eps i n)) h1 h2
  refine ⟨?_, fun T F hT => circleCompatDecoder_valid rho hq eps hT,
    fun T hns => circleCompatDecoder_invalid rho q eps hns, fun Dec' h1' h2' => ?_⟩
  · rw [← hDec]
    exact hDm
  · exact circleLimitDecoder_unique hq (a := fun (i : I) (n : ℕ) (S : (ℂ → ℝ) → ℝ) => S (circleCompatPsi rho q eps i n)) h1' h2'

/-- **Compatibility of the named decoder with deterministic additions** (r10 lines 1313-1350). Under the single baseline
premise `n ↦ T (psi i n) → F (q i)` for every `i`: the decoder of `T` is `F`; for every continuous `u` the additions
`v ↦ u v * psi i n v` are integrable and the decoder of `T + ∫ u φ` is `F + Ucirc u`; for every `γ`, `z` the additions
`v ↦ dmsShift γ z v * psi i n v` are integrable and the decoder of `T + ∫ dmsShift γ z φ` is `G(γ, z, F)`. No linearity
of `T` is assumed. -/
theorem circleCompat_addition (rho : ℂ → ℝ) (hρ : IsLiteralMollifier rho) {I : Type*} (q : I → CircleDomain)
    (hq : DenseRange q) (eps : I → ℕ → ℝ) (heps_pos : ∀ i n, 0 < eps i n)
    (heps : ∀ i, Tendsto (eps i) atTop (𝓝[>] 0)) (T : (ℂ → ℝ) → ℝ) (F : C(CircleDomain, ℝ))
    (hT : ∀ i, Tendsto (fun n => T (circleCompatPsi rho q eps i n)) atTop (𝓝 (F (q i)))) :
    circleCompatDecoder rho q eps T = F ∧
    (∀ (u : ℂ → ℝ) (hu : Continuous u),
      (∀ i n, Integrable (fun v : ℂ => u v * circleCompatPsi rho q eps i n v)) ∧
        circleCompatDecoder rho q eps (fun φ => T φ + ∫ v : ℂ, u v * φ v) = F + circleAverageFun u hu) ∧
    (∀ (γ : ℝ) (z : ℂ),
      (∀ i n, Integrable (fun v : ℂ => dmsShift γ z v * circleCompatPsi rho q eps i n v)) ∧
        circleCompatDecoder rho q eps (fun φ => T φ + ∫ v : ℂ, dmsShift γ z v * φ v) =
          circleDMSShiftFun γ z F) := by
  refine ⟨circleCompatDecoder_valid rho hq eps hT, fun u hu => ⟨fun i n =>
    integrable_circleCompat_mul rho hρ q eps heps_pos hu i n, ?_⟩, fun γ z => ⟨fun i n =>
    integrable_circleCompat_dms rho hρ q eps heps_pos γ z i n, ?_⟩⟩
  · refine circleCompatDecoder_valid rho hq eps (fun i => ?_)
    exact (hT i).add (tendsto_circleCompat_mul rho hρ q eps heps hu i)
  · refine circleCompatDecoder_valid rho hq eps (fun i => ?_)
    have hval : circleDMSShiftFun γ z F (q i) =
        F (q i) + (-γ * Real.log (max (q i).val.1 ‖(q i).val.2 - z‖) +
          γ * Real.circleAverage logMaxOne (q i).val.2 (q i).val.1) := by
      rw [circleDMSShiftFun_apply]
      ring
    rw [hval]
    exact (hT i).add (tendsto_circleCompat_dms rho hρ q eps heps γ z i)

end HarmonicBalls

end

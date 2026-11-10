import HarmonicBalls.Defs.LQGMetric
import HarmonicBalls.FirstPass.S11asLocal

/-!
# Eventual rooted covariance: internal proportionality and the eventual ambient metric (fp-S11at, round 10)

Chat 195 (`notes/fp-gaps/CHATGPT-hb-hCov-locality.md`) replaces the false fixed-scale ambient locality by three steps:
* step 6a (`ae_internalMetric_decoded_scalar`): the two decoded internal metrics on a locality domain are proportional, a.s.,
  because the two local decoder outputs coincide (equal observations) and each equals a positive multiple of its internal
  metric (the replacement clauses of `LocalMetricReplacementStmt`, normalised by `LQGCanonicalIdentificationStmt`);
* step 6b (`NoShortcutSmallBallStmt`, now the task of n2, `S11r/NoShortcut.lean`): ambient equals internal near `0`;
* step 6c (`ae_eventual_ambient_proportional`, `ae_eventual_certificateEvent_iff`): a.s., for all large `n`, the ambient
  metrics are proportional on the window and the certificate events agree.

Only `NoShortcutSmallBallStmt` is an explicit hypothesis of the eventual lemmas; step 6a is proved here in its
deterministic core (the normalising constants are explicit), and the link from `LocalMetricReplacementStmt` to the
observation-level hypotheses `hrepR`, `hrepU` is NOT yet written (see the report).
-/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal
open HarmonicBalls

namespace FirstPassS11at

/-- A Euclidean length metric is nonnegative (triangle inequality with `D z z = 0` and symmetry). -/
theorem nonneg_of_isEuclideanLengthMetric {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) (x y : ℂ) :
    0 ≤ D x y := by
  have h := hD.triangle x y x
  rw [hD.self_eq_zero, hD.symm y x] at h
  linarith

/-- **Input from n2 (task `fp-S11r-11-13-no-shortcut`, `HarmonicBalls/FirstPass/S11r/NoShortcut.lean`; not yet in the
repository).** No shortcut near a point of an open set: for a Euclidean length metric `D` and an open `U ∋ 0`, the ambient
length metric equals the internal metric of `U` on a small closed Euclidean ball about `0`
(Armstrong-Kuusi-Mourrat length structure; ChatGPT chat 195, step 6b). Taken as an explicit hypothesis until its name
appears in `notes/n3-inbox.md`. -/
def NoShortcutSmallBallStmt : Prop :=
  ∀ (D : ℂ → ℂ → ℝ), IsEuclideanLengthMetric D → ∀ (U : Set ℂ), IsOpen U → (0 : ℂ) ∈ U →
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ x ∈ closedBall (0 : ℂ) ρ, ∀ y ∈ closedBall (0 : ℂ) ρ,
      ENNReal.ofReal (D x y) = internalMetric D U x y

/-- **Step 6a, deterministic core: proportionality of two internal metrics from equal observations.** Let `Dr ω`, `Du ω` be
the decoded metrics and `obsR ω`, `obsU ω` their local observations on `Uloc`. Suppose, almost surely, that the local decoder
`m` of the replacement clause returns, on every endpoint pair `p ∈ Uloc × Uloc`, a positive multiple of the internal metric:
`ofReal (m (obs ω) p) = ofReal (c ω) * internalMetric (D ω) Uloc p.1 p.2` (`c ω > 0`; the clause of
`LocalMetricReplacementStmt` after normalisation by `LQGCanonicalIdentificationStmt`). If the two observations agree a.s.
(local observation equality of the two rooted pairs), then the two internal metrics are proportional on `Uloc`, with the
constant `cU / cR` independent of the endpoints. -/
theorem ae_internalMetric_decoded_scalar {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Obs : Type*}
    (Dr Du : Ω → ℂ → ℂ → ℝ) (Uloc : Set ℂ) (obsR obsU : Ω → Obs) (m : Obs → ℂ × ℂ → ℝ)
    (cR cU : Ω → ℝ) (hcR : ∀ᵐ ω ∂P, 0 < cR ω) (hcU : ∀ᵐ ω ∂P, 0 < cU ω)
    (hobs : ∀ᵐ ω ∂P, obsR ω = obsU ω)
    (hrepR : ∀ᵐ ω ∂P, ∀ p ∈ Uloc ×ˢ Uloc,
      ENNReal.ofReal (m (obsR ω) p) = ENNReal.ofReal (cR ω) * internalMetric (Dr ω) Uloc p.1 p.2)
    (hrepU : ∀ᵐ ω ∂P, ∀ p ∈ Uloc ×ˢ Uloc,
      ENNReal.ofReal (m (obsU ω) p) = ENNReal.ofReal (cU ω) * internalMetric (Du ω) Uloc p.1 p.2) :
    ∀ᵐ ω ∂P, ∃ β : ℝ, 0 < β ∧ ∀ x ∈ Uloc, ∀ y ∈ Uloc,
      internalMetric (Dr ω) Uloc x y = ENNReal.ofReal β * internalMetric (Du ω) Uloc x y := by
  filter_upwards [hcR, hcU, hobs, hrepR, hrepU] with ω hR hU hO hRR hUU
  refine ⟨cU ω / cR ω, div_pos hU hR, fun x hx y hy => ?_⟩
  have hp : (x, y) ∈ Uloc ×ˢ Uloc := ⟨hx, hy⟩
  have eR := hRR (x, y) hp
  have eU := hUU (x, y) hp
  dsimp only at eR eU
  rw [hO] at eR
  have h1 : ENNReal.ofReal (cR ω) * internalMetric (Dr ω) Uloc x y =
      ENNReal.ofReal (cU ω) * internalMetric (Du ω) Uloc x y := eR.symm.trans eU
  have hR0 : ENNReal.ofReal (cR ω) ≠ 0 := (ENNReal.ofReal_pos.2 hR).ne'
  have hRt : ENNReal.ofReal (cR ω) ≠ ⊤ := ENNReal.ofReal_ne_top
  have key : internalMetric (Dr ω) Uloc x y =
      (ENNReal.ofReal (cR ω))⁻¹ * (ENNReal.ofReal (cU ω) * internalMetric (Du ω) Uloc x y) := by
    rw [← h1, ← mul_assoc, ENNReal.inv_mul_cancel hR0 hRt, one_mul]
  rw [key, ENNReal.ofReal_div_of_pos hR, div_eq_mul_inv]
  ac_rfl

/-- **Step 6c, eventual ambient proportionality.** Let `D ω`, `E ω` be Euclidean length metrics for almost every `ω`, and
suppose their internal metrics on the open set `Uloc ∋ 0` are proportional on a fixed window `closedBall 0 r₀` (`hInt`, the
output of `ae_internalMetric_decoded_scalar`). With the no-shortcut input `hNS` (n2), almost surely there are `β > 0` and
`n₀` such that the ambient metrics are proportional on `closedBall 0 (rad n)` for all `n ≥ n₀`, whenever `rad n → 0`. The
statement is only eventual: the no-shortcut radius is random (chat 195, step 6c). -/
theorem ae_eventual_ambient_proportional {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (hNS : NoShortcutSmallBallStmt)
    (D E : Ω → ℂ → ℂ → ℝ) {Uloc : Set ℂ} (hUloc : IsOpen Uloc) (h0 : (0 : ℂ) ∈ Uloc)
    {r₀ : ℝ} (hr₀ : 0 < r₀) (rad : ℕ → ℝ) (hrad : Tendsto rad atTop (𝓝 0))
    (hD : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (hE : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (E ω))
    (hInt : ∀ᵐ ω ∂P, ∃ β : ℝ, 0 < β ∧ ∀ x ∈ closedBall (0 : ℂ) r₀, ∀ y ∈ closedBall (0 : ℂ) r₀,
      internalMetric (D ω) Uloc x y = ENNReal.ofReal β * internalMetric (E ω) Uloc x y) :
    ∀ᵐ ω ∂P, ∃ β : ℝ, 0 < β ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ x ∈ closedBall (0 : ℂ) (rad n),
      ∀ y ∈ closedBall (0 : ℂ) (rad n), D ω x y = β * E ω x y := by
  filter_upwards [hD, hE, hInt] with ω hDω hEω hIω
  obtain ⟨β, hβ, hβint⟩ := hIω
  obtain ⟨ρD, hρD, hD2⟩ := hNS (D ω) hDω Uloc hUloc h0
  obtain ⟨ρE, hρE, hE2⟩ := hNS (E ω) hEω Uloc hUloc h0
  have hm : (0 : ℝ) < min (min ρD ρE) r₀ := lt_min (lt_min hρD hρE) hr₀
  have hev : ∀ᶠ n in atTop, rad n < min (min ρD ρE) r₀ := hrad.eventually (gt_mem_nhds hm)
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hev
  refine ⟨β, hβ, n₀, fun n hn x hx y hy => ?_⟩
  have hlt : rad n ≤ min (min ρD ρE) r₀ := (hn₀ n hn).le
  have hρD' : rad n ≤ ρD := hlt.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hρE' : rad n ≤ ρE := hlt.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hr' : rad n ≤ r₀ := hlt.trans (min_le_right _ _)
  have eD := hD2 x (closedBall_subset_closedBall hρD' hx) y (closedBall_subset_closedBall hρD' hy)
  have eE := hE2 x (closedBall_subset_closedBall hρE' hx) y (closedBall_subset_closedBall hρE' hy)
  have eI := hβint x (closedBall_subset_closedBall hr' hx) y (closedBall_subset_closedBall hr' hy)
  have key : ENNReal.ofReal (D ω x y) = ENNReal.ofReal (β * E ω x y) := by
    rw [eD, eI, ← eE, ENNReal.ofReal_mul hβ.le]
  exact (ENNReal.ofReal_eq_ofReal_iff (nonneg_of_isEuclideanLengthMetric hDω x y)
    (mul_nonneg hβ.le (nonneg_of_isEuclideanLengthMetric hEω x y))).1 key

/-- **Eventual certificate equivalence from local locality (deterministic assembly).** For each scale `r n → 0`, the mass
locality on the window `closedBall 0 (7 r n)` (`hMass`, the output of `FirstPassS11asLocal.ae_decoded_restrict_scalar` at that
scale) and the eventual metric proportionality above give, almost surely, the certificate equivalence at `(r n, 0)` for all
`n ≥ n₀`. The constants `a` and `β` are absorbed by `FirstPassS11asLocal.certificateEvent_of_restrict_scalar`. -/
theorem ae_eventual_certificateEvent_iff {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (hNS : NoShortcutSmallBallStmt)
    (μ μ' : Ω → Measure ℂ) (D E : Ω → ℂ → ℂ → ℝ) {Uloc : Set ℂ} (hUloc : IsOpen Uloc) (h0 : (0 : ℂ) ∈ Uloc)
    {r₀ : ℝ} (hr₀ : 0 < r₀) (Ostar U V W T Q' Q : Set ℂ) (η M : ℝ)
    (hC : FirstPassS11i.CertificateContainments η Ostar V W T Q' Q) (hU : U ⊆ closedBall 0 7)
    (r : ℕ → ℝ) (hr : Tendsto r atTop (𝓝 0)) (hpos : ∀ n, 0 < r n)
    (hD : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (hE : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (E ω))
    (hInt : ∀ᵐ ω ∂P, ∃ β : ℝ, 0 < β ∧ ∀ x ∈ closedBall (0 : ℂ) r₀, ∀ y ∈ closedBall (0 : ℂ) r₀,
      internalMetric (D ω) Uloc x y = ENNReal.ofReal β * internalMetric (E ω) Uloc x y)
    (hMass : ∀ n, ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧
      (μ ω).restrict (closedBall 0 (7 * r n)) = (ENNReal.ofReal a • μ' ω).restrict (closedBall 0 (7 * r n))) :
    ∀ᵐ ω ∂P, ∃ n₀ : ℕ, ∀ n ≥ n₀,
      (FirstPassS11i.CertificateEvent (μ ω) (D ω) Ostar U V W T Q' Q η M (r n) 0 ↔
        FirstPassS11i.CertificateEvent (μ' ω) (E ω) Ostar U V W T Q' Q η M (r n) 0) := by
  have h7 : Tendsto (fun n => 7 * r n) atTop (𝓝 0) := by
    have h := hr.const_mul 7
    rw [mul_zero] at h
    exact h
  have hmet := ae_eventual_ambient_proportional hNS D E hUloc h0 hr₀ (fun n => 7 * r n) h7 hD hE hInt
  have hall := ae_all_iff.2 hMass
  filter_upwards [hall, hmet] with ω hmass hω
  obtain ⟨β, hβ, n₀, hn₀⟩ := hω
  refine ⟨n₀, fun n hn => ?_⟩
  obtain ⟨a, ha, hμ⟩ := hmass n
  refine FirstPassS11asLocal.certificateEvent_of_restrict_scalar (μ ω) (μ' ω) (D ω) (E ω) Ostar U V W T Q' Q η M
    (r n) ha hβ hC hU (hpos n) hμ ?_
  intro p hp
  show D ω p.1 p.2 = β * E ω p.1 p.2
  exact hn₀ n hn p.1 hp.1 p.2 hp.2

end FirstPassS11at

import HarmonicBalls.FirstPass.S11r.NoShortcut
import HarmonicBalls.FirstPass.S11i.CertDilate
import HarmonicBalls.FirstPass.S11i.RootedFrequencyShift
import HarmonicBalls.FirstPass.S11aq
import HarmonicBalls.FirstPass.S11ah.Cutoff
import HarmonicBalls.FirstPass.S11c.TranslateField11_7
import HarmonicBalls.Defs.LQGMetric
import HarmonicBalls.FirstPass.S11asLocal
import HarmonicBalls.FirstPass.S11r.CMTransfer
import HarmonicBalls.FirstPass.S11i.TranslationCanonical
import HarmonicBalls.FirstPass.Frozen.S11c
import HarmonicBalls.FirstPass.S11at.Producers

/-!
# Eventual rooted covariance: internal proportionality and the eventual ambient metric (fp-S11at, round 10)

Chat 195 (`notes/fp-gaps/CHATGPT-hb-hCov-locality.md`) replaces the false fixed-scale ambient locality by three steps:
* step 6a (`ae_internalMetric_decoded_scalar`): the two decoded internal metrics on a locality domain are proportional, a.s.,
  because the two local decoder outputs coincide (equal observations) and each equals a positive multiple of its internal
  metric (the replacement clauses of `LocalMetricReplacementStmt`, normalised by `LQGCanonicalIdentificationStmt`);
* step 6b (`HarmonicBalls.eq_internalMetric_on_small_ball`, committed by n2 in `S11r/NoShortcut.lean`): ambient equals internal near `0`;
* step 6c (`ae_eventual_ambient_proportional`, `ae_eventual_certificateEvent_iff`): a.s., for all large `n`, the ambient
  metrics are proportional on the window and the certificate events agree.

The no-shortcut step is `HarmonicBalls.eq_internalMetric_on_small_ball` (n2, committed); no explicit hypothesis remains for it. step 6a is proved here in its
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
output of `ae_internalMetric_decoded_scalar`). With the no-shortcut lemma `HarmonicBalls.eq_internalMetric_on_small_ball` (n2), almost surely there are `β > 0` and
`n₀` such that the ambient metrics are proportional on `closedBall 0 (rad n)` for all `n ≥ n₀`, whenever `rad n → 0`. The
statement is only eventual: the no-shortcut radius is random (chat 195, step 6c). -/
theorem ae_eventual_ambient_proportional {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
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
  obtain ⟨ρD, hρD, hD2⟩ := HarmonicBalls.eq_internalMetric_on_small_ball hDω hUloc h0
  obtain ⟨ρE, hρE, hE2⟩ := HarmonicBalls.eq_internalMetric_on_small_ball hEω hUloc h0
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
  have hmet := ae_eventual_ambient_proportional D E hUloc h0 hr₀ (fun n => 7 * r n) h7 hD hE hInt
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

namespace FirstPassS11at

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal
open HarmonicBalls HarmonicBalls.S11c

/-- The root-shifted canonical element `canonFieldOf γ (addFunPairing (translatedPairing hC hcirc z ω) u)` of the rooted
pair at `z` with shift `u` (the right-hand side of `hCov` in `S11ai/RootedInstance.lean`). -/
noncomputable def shiftedCanon {Ω : Type*} (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (z : ℂ)
    (u : ℂ → ℝ) (ω : Ω) : ModConstTestPairings (Set.univ : Set ℂ) :=
  canonFieldOf γ (addFunPairing (translatedPairing hC hcirc z ω) u)

/-- **Eventual pair locality at the certificate scales (step 6c, fixed root and shift).** For a fixed root, the physical
pair `(μ0 ω, D0 ω)` and the shifted pair `(μu ω, Du ω)` have, almost surely and eventually in `n`, equal certificate
events at `(certScale n, 0)`. Inputs: the no-shortcut lemma `HarmonicBalls.eq_internalMetric_on_small_ball` (n2), the Euclidean length property of both metrics,
the proportionality of the internal metrics on the window `closedBall 0 r₀` inside `Uloc`, and the mass locality
`hMass` (eventual in `n`). -/
theorem ae_eventual_certificateEvent_pair {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (μ0 μu : Ω → Measure ℂ) (D0 Du : Ω → ℂ → ℂ → ℝ) {Uloc : Set ℂ} (hUloc : IsOpen Uloc) (h0 : (0 : ℂ) ∈ Uloc)
    {r₀ : ℝ} (hr₀ : 0 < r₀) (Ostar U V W T Q' Q : Set ℂ) (η M : ℝ)
    (hC : FirstPassS11i.CertificateContainments η Ostar V W T Q' Q) (hU : U ⊆ closedBall 0 7)
    (hD0 : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D0 ω)) (hDu : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (Du ω))
    (hInt : ∀ᵐ ω ∂P, ∃ β : ℝ, 0 < β ∧ ∀ x ∈ closedBall (0 : ℂ) r₀, ∀ y ∈ closedBall (0 : ℂ) r₀,
      internalMetric (D0 ω) Uloc x y = ENNReal.ofReal β * internalMetric (Du ω) Uloc x y)
    (hMass : ∀ᵐ ω ∂P, ∃ n₁ : ℕ, ∀ n ≥ n₁, ∃ a : ℝ, 0 < a ∧
      (μ0 ω).restrict (closedBall 0 (7 * FirstPassS11ah.certScale n)) =
        (ENNReal.ofReal a • μu ω).restrict (closedBall 0 (7 * FirstPassS11ah.certScale n))) :
    ∀ᵐ ω ∂P, ∃ n₀ : ℕ, ∀ n ≥ n₀,
      (FirstPassS11i.CertificateEvent (μ0 ω) (D0 ω) Ostar U V W T Q' Q η M (FirstPassS11ah.certScale n) 0 ↔
        FirstPassS11i.CertificateEvent (μu ω) (Du ω) Ostar U V W T Q' Q η M (FirstPassS11ah.certScale n) 0) := by
  have h1 : Tendsto (fun n : ℕ => FirstPassS11ah.certScale n) atTop (𝓝 0) := by
    simpa [FirstPassS11ah.certScale] using
      tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2 : ℝ)⁻¹) (by norm_num) (by norm_num)
  have h7 : Tendsto (fun n : ℕ => 7 * FirstPassS11ah.certScale n) atTop (𝓝 0) := by
    have h := h1.const_mul 7
    rwa [mul_zero] at h
  have hpos : ∀ n : ℕ, 0 < FirstPassS11ah.certScale n := fun n => by
    unfold FirstPassS11ah.certScale
    positivity
  have hmet := ae_eventual_ambient_proportional D0 Du hUloc h0 hr₀
    (fun n : ℕ => 7 * FirstPassS11ah.certScale n) h7 hD0 hDu hInt
  filter_upwards [hmet, hMass] with ω hω hmω
  obtain ⟨β, hβ, n₂, hn₂⟩ := hω
  obtain ⟨n₁, hn₁⟩ := hmω
  refine ⟨max n₁ n₂, fun n hn => ?_⟩
  obtain ⟨a, ha, hμ⟩ := hn₁ n (le_trans (le_max_left _ _) hn)
  refine FirstPassS11asLocal.certificateEvent_of_restrict_scalar (μ0 ω) (μu ω) (D0 ω) (Du ω) Ostar U V W T Q' Q η M
    (FirstPassS11ah.certScale n) ha hβ hC hU (hpos n) hμ ?_
  intro p hp
  show D0 ω p.1 p.2 = β * Du ω p.1 p.2
  exact hn₂ n (le_trans (le_max_right _ _) hn) p.1 hp.1 p.2 hp.2

/-- **The eventual rooted covariance statement (the `hCov` clause of `S11ai/RootedInstance.lean`, n1 form).** The
admissible-shift predicate `Adm` and the root radius `rR` are parameters, so that this file does not import the rooted
instance (import cycle). For almost every root `z ∈ A` in `ball c₁ r₁`, every admissible shift `(b, u)` at `z`, almost
surely, eventually in `n` (with the cutoff inclusions as premises): the physical rooted certificate at scale
`certScale n` about `z` equals the unit-scale certificate of the dilated, translated, shifted canonical pair. -/
def RootedCertificateEventualCovarianceStmt {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (c₁ c₂ : ℂ) (r₁ r₂ : ℝ) (A : Set ℂ)
    (Ostar U V W T Q' Q : Set ℂ) (η M : ℝ) (Adm : ℂ → ℝ → (ℂ → ℝ) → Prop) (rR : ℂ → ℝ)
    (μR : ℂ → Ω → Measure ℂ) (dR : ℂ → Ω → ℂ → ℂ → ℝ)
    (Dμ : ModConstTestPairings (Set.univ : Set ℂ) → Measure ℂ)
    (Dd : ModConstTestPairings (Set.univ : Set ℂ) → ℂ → ℂ → ℝ) : Prop :=
  ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), z ∈ A → ∀ (b : ℝ) (u : ℂ → ℝ), Adm z b u → ∀ᵐ ω ∂P, ∃ n₀ : ℕ, ∀ n ≥ n₀,
    closedBall z (FirstPassS11ah.cutRadius n) ⊆ ball z b →
    closedBall z (FirstPassS11ah.cutRadius n) ⊆ ball z (rR z) →
    closedBall z (FirstPassS11ah.cutRadius n) ⊆ ball c₂ r₂ →
    (FirstPassS11i.CertificateEvent (μR z ω) (dR z ω) Ostar U V W T Q' Q η M
        (FirstPassS11ah.certScale n) z ↔
      FirstPassS11i.CertificateEvent (Dμ (dilOp^[n] (shiftedCanon γ hC hcirc z u ω)))
        (Dd (dilOp^[n] (shiftedCanon γ hC hcirc z u ω))) Ostar U V W T Q' Q η M 1 0)

/-- Small closed ball inside an open neighbourhood of the root: if `O` is open and `0 ∈ O`, then
`closedBall 0 (2 * ρ) ⊆ O` for some `ρ > 0`. This gives the root-dependent locality radius of the rooted wrapper. -/
theorem exists_closedBall_two_mul_subset {O : Set ℂ} (hO : IsOpen O) (h0 : (0 : ℂ) ∈ O) :
    ∃ ρ : ℝ, 0 < ρ ∧ closedBall (0 : ℂ) (2 * ρ) ⊆ O := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hO 0 h0
  refine ⟨ε / 4, by linarith, fun x hx => hball (Metric.mem_ball.2 ?_)⟩
  have h := Metric.mem_closedBall.1 hx
  linarith

/-- **Eventual certificate equivalence, one-sided (decoded-to-internal form).** The decoder `Ddec ω` is not required to be
a global Euclidean length metric. It is compared with the internal metric of the length metric `Du ω` on an open window
`W₀ ∋ 0`, through a positive constant `β` on `closedBall 0 r₀` (`hDecInt`). The no-shortcut lemma
`HarmonicBalls.eq_internalMetric_on_small_ball` (n2) is applied to `Du ω` only. Conclusion: almost surely, eventually in
`n`, the certificate events at `(certScale n, 0)` of `(μdec, Ddec)` and of `(μu, Du)` agree. -/
theorem ae_eventual_certificateEvent_decoded {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (μdec μu : Ω → Measure ℂ) (Ddec Du : Ω → ℂ → ℂ → ℝ)
    (Ostar U V W T Q' Q : Set ℂ) (η M : ℝ)
    (hC : FirstPassS11i.CertificateContainments η Ostar V W T Q' Q) (hU : U ⊆ closedBall 0 7)
    (hDu : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (Du ω))
    (hDecInt : ∀ᵐ ω ∂P, ∃ (W₀ : Set ℂ) (r₀ β : ℝ), IsOpen W₀ ∧ (0 : ℂ) ∈ W₀ ∧ 0 < r₀ ∧ 0 < β ∧
      ∀ x ∈ closedBall (0 : ℂ) r₀, ∀ y ∈ closedBall (0 : ℂ) r₀,
        Ddec ω x y = β * (internalMetric (Du ω) W₀ x y).toReal)
    (hMass : ∀ᵐ ω ∂P, ∃ n₁ : ℕ, ∀ n ≥ n₁, ∃ a : ℝ, 0 < a ∧
      (μdec ω).restrict (closedBall 0 (7 * FirstPassS11ah.certScale n)) =
        (ENNReal.ofReal a • μu ω).restrict (closedBall 0 (7 * FirstPassS11ah.certScale n))) :
    ∀ᵐ ω ∂P, ∃ n₀ : ℕ, ∀ n ≥ n₀,
      (FirstPassS11i.CertificateEvent (μdec ω) (Ddec ω) Ostar U V W T Q' Q η M
          (FirstPassS11ah.certScale n) 0 ↔
        FirstPassS11i.CertificateEvent (μu ω) (Du ω) Ostar U V W T Q' Q η M
          (FirstPassS11ah.certScale n) 0) := by
  have h1 : Tendsto (fun n : ℕ => FirstPassS11ah.certScale n) atTop (𝓝 0) := by
    simpa [FirstPassS11ah.certScale] using
      tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2 : ℝ)⁻¹) (by norm_num) (by norm_num)
  have h7 : Tendsto (fun n : ℕ => 7 * FirstPassS11ah.certScale n) atTop (𝓝 0) := by
    have h := h1.const_mul 7
    rwa [mul_zero] at h
  have hpos : ∀ n : ℕ, 0 < FirstPassS11ah.certScale n := fun n => by
    unfold FirstPassS11ah.certScale
    positivity
  filter_upwards [hDu, hDecInt, hMass] with ω hDuω hIω hMω
  obtain ⟨W₀, r₀, β, hW₀, h0, hr₀, hβ, hI⟩ := hIω
  obtain ⟨ρ, hρ, hNS⟩ := HarmonicBalls.eq_internalMetric_on_small_ball hDuω hW₀ h0
  have hsmall : ∀ᶠ n : ℕ in atTop, 7 * FirstPassS11ah.certScale n < min ρ r₀ :=
    h7.eventually (gt_mem_nhds (lt_min hρ hr₀))
  obtain ⟨n₂, hn₂⟩ := eventually_atTop.1 hsmall
  obtain ⟨n₁, hn₁⟩ := hMω
  refine ⟨max n₁ n₂, fun n hn => ?_⟩
  obtain ⟨a, ha, hμ⟩ := hn₁ n (le_trans (le_max_left _ _) hn)
  have hw : 7 * FirstPassS11ah.certScale n ≤ min ρ r₀ :=
    (hn₂ n (le_trans (le_max_right _ _) hn)).le
  refine FirstPassS11asLocal.certificateEvent_of_restrict_scalar (μdec ω) (μu ω) (Ddec ω) (Du ω) Ostar U V W T Q' Q η M
    (FirstPassS11ah.certScale n) ha hβ hC hU (hpos n) hμ ?_
  intro p hp
  have hx : p.1 ∈ closedBall (0 : ℂ) ρ :=
    closedBall_subset_closedBall (hw.trans (min_le_left _ _)) hp.1
  have hy : p.2 ∈ closedBall (0 : ℂ) ρ :=
    closedBall_subset_closedBall (hw.trans (min_le_left _ _)) hp.2
  have hx' : p.1 ∈ closedBall (0 : ℂ) r₀ :=
    closedBall_subset_closedBall (hw.trans (min_le_right _ _)) hp.1
  have hy' : p.2 ∈ closedBall (0 : ℂ) r₀ :=
    closedBall_subset_closedBall (hw.trans (min_le_right _ _)) hp.2
  show Ddec ω p.1 p.2 = β * Du ω p.1 p.2
  rw [hI p.1 hx' p.2 hy', ← hNS p.1 hx p.2 hy,
    ENNReal.toReal_ofReal (FirstPassS11at.nonneg_of_isEuclideanLengthMetric hDuω _ _)]

/-- **Eventual rooted covariance from the decoded inputs (fixed-root assembly, one-sided).** The physical pair is the
centred pair `(μ0, D0)` at `z` (`hμR`, `hdR` identify it with the rooted pair `(μR, dR)`). The decoder `D0 z ω` is only
compared with the internal metric of the shifted canonical metric `Dd (shiftedCanon …)` on a window `ball 0 (2ρ)`:
`hDecInt` gives a root-dependent locality radius `ρ` with `closedBall 0 (2ρ)` inside the admissible ball `ball 0 b`, the
rooted ball `ball 0 (rR z)` and the translated observation domain `(· + z) ⁻¹' ball c₂ r₂`. The length property `hDu` and the
dilation identity `hdil` are needed only for the shifted canonical element. -/
theorem rootedCertificateEventualCovarianceStmt_of_local {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {γ : ℝ} (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (c₁ c₂ : ℂ) (r₁ r₂ : ℝ) (A : Set ℂ) (Ostar U V W T Q' Q : Set ℂ) (η M : ℝ)
    (hCont : FirstPassS11i.CertificateContainments η Ostar V W T Q' Q) (hU : U ⊆ closedBall 0 7)
    (Adm : ℂ → ℝ → (ℂ → ℝ) → Prop) (rR : ℂ → ℝ)
    (μ0 μR : ℂ → Ω → Measure ℂ) (D0 dR : ℂ → Ω → ℂ → ℂ → ℝ)
    (Dμ : ModConstTestPairings (Set.univ : Set ℂ) → Measure ℂ)
    (Dd : ModConstTestPairings (Set.univ : Set ℂ) → ℂ → ℂ → ℝ)
    (hμR : ∀ z ω, μR z ω = (μ0 z ω).map (fun w : ℂ => w - -z))
    (hdR : ∀ z ω, dR z ω = fun x y => D0 z ω (x + -z) (y + -z))
    (hDu : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), z ∈ A → ∀ (b : ℝ) (u : ℂ → ℝ), Adm z b u →
      ∀ᵐ ω ∂P, IsEuclideanLengthMetric (Dd (shiftedCanon γ hC hcirc z u ω)))
    (hDecInt : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), z ∈ A → ∀ (b : ℝ) (u : ℂ → ℝ), Adm z b u →
      ∀ᵐ ω ∂P, ∃ ρ r β : ℝ, 0 < ρ ∧ 0 < r ∧ 0 < β ∧
        closedBall (0 : ℂ) (2 * ρ) ⊆ ball 0 b ∩ ball 0 (rR z) ∩ ((fun x : ℂ => x + z) ⁻¹' ball c₂ r₂) ∧
        ∀ x ∈ closedBall (0 : ℂ) r, ∀ y ∈ closedBall (0 : ℂ) r,
          D0 z ω x y = β * (internalMetric (Dd (shiftedCanon γ hC hcirc z u ω)) (ball 0 (2 * ρ)) x y).toReal)
    (hMass : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), z ∈ A → ∀ (b : ℝ) (u : ℂ → ℝ), Adm z b u →
      ∀ᵐ ω ∂P, ∃ n₁ : ℕ, ∀ n ≥ n₁, ∃ a : ℝ, 0 < a ∧
        (μ0 z ω).restrict (closedBall 0 (7 * FirstPassS11ah.certScale n)) =
          (ENNReal.ofReal a • Dμ (shiftedCanon γ hC hcirc z u ω)).restrict
            (closedBall 0 (7 * FirstPassS11ah.certScale n)))
    (hdil : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), z ∈ A → ∀ (b : ℝ) (u : ℂ → ℝ), Adm z b u →
      ∀ n : ℕ, ∀ᵐ ω ∂P, ∃ a c : ℝ, 0 < a ∧ 0 < c ∧
        Dμ (dilOp^[n] (shiftedCanon γ hC hcirc z u ω)) =
            ENNReal.ofReal a • (Dμ (shiftedCanon γ hC hcirc z u ω)).map
              (fun w : ℂ => w / (((1 / 2 : ℝ) ^ n : ℝ) : ℂ)) ∧
          ∀ x y : ℂ, Dd (dilOp^[n] (shiftedCanon γ hC hcirc z u ω)) x y =
            c * Dd (shiftedCanon γ hC hcirc z u ω) (((((1 / 2 : ℝ) ^ n : ℝ) : ℂ)) * x)
              ((((1 / 2 : ℝ) ^ n : ℝ) : ℂ) * y)) :
    RootedCertificateEventualCovarianceStmt P γ hC hcirc c₁ c₂ r₁ r₂ A Ostar U V W T Q' Q η M Adm rR
      μR dR Dμ Dd := by
  filter_upwards [hDu, hDecInt, hMass, hdil] with z hDuz hDecz hMassz hdilz hzA b u hadm
  have hDecU : ∀ᵐ ω ∂P, ∃ (W₀ : Set ℂ) (r₀ β : ℝ), IsOpen W₀ ∧ (0 : ℂ) ∈ W₀ ∧ 0 < r₀ ∧ 0 < β ∧
      ∀ x ∈ closedBall (0 : ℂ) r₀, ∀ y ∈ closedBall (0 : ℂ) r₀,
        D0 z ω x y = β * (internalMetric (Dd (shiftedCanon γ hC hcirc z u ω)) W₀ x y).toReal :=
    (hDecz hzA b u hadm).mono fun ω ⟨ρ, r, β, hρ, hr, hβ, _, hI⟩ =>
      ⟨ball 0 (2 * ρ), r, β, isOpen_ball, mem_ball_self (by linarith), hr, hβ, hI⟩
  have hpair := ae_eventual_certificateEvent_decoded (μ0 z) (fun ω => Dμ (shiftedCanon γ hC hcirc z u ω))
    (D0 z) (fun ω => Dd (shiftedCanon γ hC hcirc z u ω)) Ostar U V W T Q' Q η M hCont hU
    (hDuz hzA b u hadm) hDecU (hMassz hzA b u hadm)
  filter_upwards [hpair, ae_all_iff.2 (hdilz hzA b u hadm)] with ω hωp hωd
  obtain ⟨n₀, hn₀⟩ := hωp
  refine ⟨n₀, fun n hn _ _ _ => ?_⟩
  obtain ⟨a, c, ha, hc, hM, hE⟩ := hωd n
  have hcs : FirstPassS11ah.certScale n = (1 / 2 : ℝ) ^ n := by
    simp [FirstPassS11ah.certScale, one_div]
  have hEfun : Dd (dilOp^[n] (shiftedCanon γ hC hcirc z u ω)) = fun x y : ℂ =>
      c * Dd (shiftedCanon γ hC hcirc z u ω) ((((1 / 2 : ℝ) ^ n : ℝ) : ℂ) * x)
        ((((1 / 2 : ℝ) ^ n : ℝ) : ℂ) * y) :=
    funext fun x => funext fun y => hE x y
  have key := HarmonicBalls.FirstPassS11iCertDilate.certificateEvent_dilate_iff
    (Dμ (shiftedCanon γ hC hcirc z u ω)) (Dd (shiftedCanon γ hC hcirc z u ω)) Ostar U V W T Q' Q η M 1 0
    (R := (1 / 2 : ℝ) ^ n) (by positivity) ha hc
  rw [mul_one, mul_zero] at key
  rw [hμR z ω, hdR z ω]
  refine (FirstPassS11aq.certificateEvent_translate_iff (μ0 z ω) (D0 z ω) Ostar U V W T Q' Q η M
    (FirstPassS11ah.certScale n) z (-z)).trans ?_
  rw [add_neg_cancel, hn₀ n hn, hcs, hM, hEfun]
  exact key.symm

/-- **Centred pair identities (translation to the root).** For a pair `(μR, dR)` with root `z` in absolute coordinates, the
centred pair `μ0 z ω = (μR z ω).map (· - z)` and `D0 z ω x y = dR z ω (x + z) (y + z)` satisfies the identities `hμR` and
`hdR` of `rootedCertificateEventualCovarianceStmt_of_local`. This instantiates that wrapper at the decoded pair
`(μR, dR) = (κ obsR, m obsR)`, where `hFit` is definitional. -/
theorem centred_pair_identities {Ω : Type*} (μR : ℂ → Ω → Measure ℂ) (dR : ℂ → Ω → ℂ → ℂ → ℝ) :
    (∀ z ω, μR z ω = ((μR z ω).map (fun w : ℂ => w - z)).map (fun w : ℂ => w - -z)) ∧
    (∀ z ω, dR z ω = fun x y => (fun x' y' : ℂ => dR z ω (x' + z) (y' + z)) (x + -z) (y + -z)) := by
  refine ⟨fun z ω => ?_, fun z ω => ?_⟩
  · have hg : Measurable (fun w : ℂ => w - z) := by fun_prop
    have hf : Measurable (fun w : ℂ => w - -z) := by fun_prop
    rw [Measure.map_map hf hg]
    have hfun : ((fun w : ℂ => w - -z) ∘ fun w : ℂ => w - z) = id := by
      funext w
      simp
    rw [hfun, Measure.map_id]
  · funext x y
    simp

universe u

/-- **Iterated dilation covariance on an invariant set (deterministic).** Let `G0` be a `dilOp`-invariant set on which the
decoders satisfy the one-step dilation identities (the conclusion of `B1_covariance`, S11s/B1Covariance.lean:120, on `G0`).
Then on `G0` the `n`-fold identities hold with positive constants: induction on `n`, composing the scalings `(1/2)^k`. -/
theorem dilOp_iterate_of_one_step {Dμ : S11n.CanonSpace → Measure ℂ} {Dd : S11n.CanonSpace → ℂ → ℂ → ℝ}
    {G0 : Set S11n.CanonSpace} (hinv : ∀ L ∈ G0, dilOp L ∈ G0)
    (hstep : ∀ L ∈ G0, ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      Dμ (dilOp L) = ENNReal.ofReal a • (Dμ L).map (fun w : ℂ => w / (((1 / 2 : ℝ)) : ℂ)) ∧
      ∀ x y : ℂ, Dd (dilOp L) x y = b * Dd L (((1 / 2 : ℝ) : ℂ) * x) (((1 / 2 : ℝ) : ℂ) * y))
    (n : ℕ) : ∀ L ∈ G0, ∃ a c : ℝ, 0 < a ∧ 0 < c ∧
      Dμ (dilOp^[n] L) = ENNReal.ofReal a • (Dμ L).map (fun w : ℂ => w / (((1 / 2 : ℝ) ^ n : ℝ) : ℂ)) ∧
      ∀ x y : ℂ, Dd (dilOp^[n] L) x y
        = c * Dd L (((((1 / 2 : ℝ) ^ n : ℝ) : ℂ)) * x) ((((1 / 2 : ℝ) ^ n : ℝ) : ℂ) * y) := by
  induction n with
  | zero =>
    intro L _
    refine ⟨1, 1, one_pos, one_pos, ?_, fun x y => ?_⟩
    · simp
    · simp
  | succ n ih =>
    intro L hL
    obtain ⟨a1, b1, ha1, hb1, hμ1, hd1⟩ := hstep L hL
    obtain ⟨a2, c2, ha2, hc2, hμ2, hd2⟩ := ih (dilOp L) (hinv L hL)
    have hs1 : Measurable (fun w : ℂ => w / (((1 / 2 : ℝ)) : ℂ)) := by fun_prop
    have hsn : Measurable (fun w : ℂ => w / (((1 / 2 : ℝ) ^ n : ℝ) : ℂ)) := by fun_prop
    have hfun : ((fun w : ℂ => w / (((1 / 2 : ℝ) ^ n : ℝ) : ℂ)) ∘ (fun w : ℂ => w / (((1 / 2 : ℝ)) : ℂ)))
        = (fun w : ℂ => w / (((1 / 2 : ℝ) ^ (n + 1) : ℝ) : ℂ)) := by
      funext w
      simp only [Function.comp_apply]
      rw [div_div, ← Complex.ofReal_mul, ← pow_succ']
    have e1 : ∀ x : ℂ, (((1 / 2 : ℝ)) : ℂ) * ((((1 / 2 : ℝ) ^ n : ℝ) : ℂ) * x)
        = ((((1 / 2 : ℝ) ^ (n + 1) : ℝ)) : ℂ) * x := by
      intro x
      push_cast
      ring
    refine ⟨a2 * a1, c2 * b1, mul_pos ha2 ha1, mul_pos hc2 hb1, ?_, fun x y => ?_⟩
    · rw [Function.iterate_succ_apply, hμ2, hμ1, Measure.map_smul _ hsn.aemeasurable, Measure.map_map hsn hs1, hfun,
        smul_smul,
        ← ENNReal.ofReal_mul ha2.le]
    · rw [Function.iterate_succ_apply, hd2, hd1, e1 x, e1 y]
      ring

/-- **Length property and dilation covariance transferred to the root-shifted canonical field, from the base set
for `alphaCanon γ hC`.** Translation of the base event: `ae_alphaCanon_translatedPairing_mem` (below) moves the a.s.
membership in the measurable set `G` from the field `hC` to the translated field, by `prob_alphaCanon_translatedPairing`
(S11i/TranslationCanonical.lean:98) applied to `Gᶜ`. -/
theorem ae_alphaCanon_translatedPairing_mem {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc) (γ : ℝ) (z : ℂ)
    {G : Set S11n.CanonSpace} (hG : MeasurableSet G) (hGa : ∀ᵐ ω ∂P, alphaCanon γ hC ω ∈ G) :
    ∀ᵐ ω ∂P, alphaCanon γ (S11c.translatedPairing hC hcirc z) ω ∈ G := by
  rw [ae_iff] at hGa ⊢
  exact (prob_alphaCanon_translatedPairing hh γ z hG.compl).trans hGa

/-- **Length property of the root-shifted canonical metric (Cameron–Martin transfer of the decoder regularity set).**
`G` is measurable, conull for `alphaCanon γ hC` (the field of the wrapper), and `Dd` is a Euclidean length metric on `G`.
Such `G` and `Dd` are the output of `LQGCanonicalDecodersMeasurableExistStmt` (Frozen/S11n.lean:71). The Cameron–Martin
transfer `HarmonicBalls.ae_shiftedCanon_mem_regularity` (n2, S11r/CMTransfer.lean:67) moves the event to
`shiftedCanon γ hC hcirc z u`, for a root shift `u` that is smooth, compactly supported, with zero unit-circle average. -/
theorem ae_isEuclideanLengthMetric_shiftedCanon {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (hCM : HarmonicBalls.CameronMartinGFFMutualAbsCont.{u}) (γ : ℝ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc)
    (hTr : ∀ z : ℂ, IsWholePlaneGFF P (S11c.translatedPairing hC hcirc z) (S11c.translatedCircle hcirc z))
    (z : ℂ) (u : ℂ → ℝ) (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hcomp : HasCompactSupport u)
    (hu0 : Real.circleAverage u 0 1 = 0) (G : Set S11n.CanonSpace) (hG : MeasurableSet G)
    (hGa : ∀ᵐ ω ∂P, alphaCanon γ hC ω ∈ G)
    (Dd : S11n.CanonSpace → ℂ → ℂ → ℝ) (hGreg : ∀ L ∈ G, IsEuclideanLengthMetric (Dd L)) :
    ∀ᵐ ω ∂P, IsEuclideanLengthMetric (Dd (shiftedCanon γ hC hcirc z u ω)) := by
  have hbase : ∀ᵐ ω ∂P, canonFieldOf γ (S11c.translatedPairing hC hcirc z ω) ∈ G :=
    ae_alphaCanon_translatedPairing_mem hh γ z hG hGa
  filter_upwards [HarmonicBalls.ae_shiftedCanon_mem_regularity P hCM γ z (hTr z) hu hcomp hu0 hG hbase] with ω hω
  exact hGreg _ hω

/-- **Dilation covariance of the root-shifted canonical decoders (Cameron–Martin transfer of the covariance set `G0`).**
`G0` is a measurable `dilOp`-invariant set, conull for `alphaCanon γ hC` (the output of `B1_covariance`,
S11s/B1Covariance.lean:120, for the field `hC`), on which the one-step dilation identities hold. The transfer
`HarmonicBalls.ae_shiftedCanon_mem_covariance`-style membership is `ae_canonFieldOf_addFunPairing_mem`
(n2, S11r/CMTransfer.lean:54), and the `n`-fold identities come from `dilOp_iterate_of_one_step`. -/
theorem ae_shiftedCanon_dilation {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (hCM : HarmonicBalls.CameronMartinGFFMutualAbsCont.{u}) (γ : ℝ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc)
    (hTr : ∀ z : ℂ, IsWholePlaneGFF P (S11c.translatedPairing hC hcirc z) (S11c.translatedCircle hcirc z))
    (z : ℂ) (u : ℂ → ℝ) (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hcomp : HasCompactSupport u)
    (hu0 : Real.circleAverage u 0 1 = 0)
    {Dμ : S11n.CanonSpace → Measure ℂ} {Dd : S11n.CanonSpace → ℂ → ℂ → ℝ}
    {G0 : Set S11n.CanonSpace} (hG0 : MeasurableSet G0) (hG0a : ∀ᵐ ω ∂P, alphaCanon γ hC ω ∈ G0)
    (hinv : dilOp ⁻¹' G0 = G0)
    (hstep : ∀ L ∈ G0, ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      Dμ (dilOp L) = ENNReal.ofReal a • (Dμ L).map (fun w : ℂ => w / (((1 / 2 : ℝ)) : ℂ)) ∧
      ∀ x y : ℂ, Dd (dilOp L) x y = b * Dd L (((1 / 2 : ℝ) : ℂ) * x) (((1 / 2 : ℝ) : ℂ) * y))
    (n : ℕ) : ∀ᵐ ω ∂P, ∃ a c : ℝ, 0 < a ∧ 0 < c ∧
      Dμ (dilOp^[n] (shiftedCanon γ hC hcirc z u ω)) =
          ENNReal.ofReal a • (Dμ (shiftedCanon γ hC hcirc z u ω)).map
            (fun w : ℂ => w / (((1 / 2 : ℝ) ^ n : ℝ) : ℂ)) ∧
        ∀ x y : ℂ, Dd (dilOp^[n] (shiftedCanon γ hC hcirc z u ω)) x y =
          c * Dd (shiftedCanon γ hC hcirc z u ω) (((((1 / 2 : ℝ) ^ n : ℝ) : ℂ)) * x)
            ((((1 / 2 : ℝ) ^ n : ℝ) : ℂ) * y) := by
  have hinv' : ∀ L ∈ G0, dilOp L ∈ G0 := fun L hL => by
    have h : L ∈ dilOp ⁻¹' G0 := by
      rw [hinv]
      exact hL
    exact h
  have hbase : ∀ᵐ ω ∂P, canonFieldOf γ (S11c.translatedPairing hC hcirc z ω) ∈ G0 :=
    ae_alphaCanon_translatedPairing_mem hh γ z hG0 hG0a
  filter_upwards [ae_canonFieldOf_addFunPairing_mem P hCM γ (hTr z) hu hcomp hu0 hG0 hbase] with ω hω
  exact dilOp_iterate_of_one_step hinv' hstep n _ hω

/-- **Eventual rooted covariance with the length property and the dilation covariance transferred.** The inputs `hDu`
and `hdil` of `rootedCertificateEventualCovarianceStmt_of_local` are discharged by the Cameron–Martin transfers above, for
every root `z` and every admissible shift `(b, u)` (`hAdmReg`: smoothness, compact support, zero circle average of `u`).
The remaining inputs are `hDecInt` and `hMass` (the decoded pair). -/
theorem rootedCertificateEventualCovarianceStmt_of_transfer {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (hCM : HarmonicBalls.CameronMartinGFFMutualAbsCont.{u}) {γ : ℝ}
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (hh : IsWholePlaneGFF P hC hcirc)
    (hTr : ∀ z : ℂ, IsWholePlaneGFF P (S11c.translatedPairing hC hcirc z) (S11c.translatedCircle hcirc z))
    (c₁ c₂ : ℂ) (r₁ r₂ : ℝ) (A : Set ℂ) (Ostar U V W T Q' Q : Set ℂ) (η M : ℝ)
    (hCont : FirstPassS11i.CertificateContainments η Ostar V W T Q' Q) (hU : U ⊆ closedBall 0 7)
    (Adm : ℂ → ℝ → (ℂ → ℝ) → Prop)
    (hAdmReg : ∀ z b u, Adm z b u → ContDiff ℝ (⊤ : ℕ∞) u ∧ HasCompactSupport u ∧ Real.circleAverage u 0 1 = 0)
    (rR : ℂ → ℝ) (μ0 μR : ℂ → Ω → Measure ℂ) (D0 dR : ℂ → Ω → ℂ → ℂ → ℝ)
    (Dμ : ModConstTestPairings (Set.univ : Set ℂ) → Measure ℂ)
    (Dd : ModConstTestPairings (Set.univ : Set ℂ) → ℂ → ℂ → ℝ)
    (G : Set S11n.CanonSpace) (hG : MeasurableSet G) (hGa : ∀ᵐ ω ∂P, alphaCanon γ hC ω ∈ G)
    (hGreg : ∀ L ∈ G, IsEuclideanLengthMetric (Dd L))
    (G0 : Set S11n.CanonSpace) (hG0 : MeasurableSet G0) (hG0a : ∀ᵐ ω ∂P, alphaCanon γ hC ω ∈ G0)
    (hinv : dilOp ⁻¹' G0 = G0)
    (hstep : ∀ L ∈ G0, ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      Dμ (dilOp L) = ENNReal.ofReal a • (Dμ L).map (fun w : ℂ => w / (((1 / 2 : ℝ)) : ℂ)) ∧
      ∀ x y : ℂ, Dd (dilOp L) x y = b * Dd L (((1 / 2 : ℝ) : ℂ) * x) (((1 / 2 : ℝ) : ℂ) * y))
    (hμR : ∀ z ω, μR z ω = (μ0 z ω).map (fun w : ℂ => w - -z))
    (hdR : ∀ z ω, dR z ω = fun x y => D0 z ω (x + -z) (y + -z))
    (hDecInt : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), z ∈ A → ∀ (b : ℝ) (u : ℂ → ℝ), Adm z b u →
      ∀ᵐ ω ∂P, ∃ ρ r β : ℝ, 0 < ρ ∧ 0 < r ∧ 0 < β ∧
        closedBall (0 : ℂ) (2 * ρ) ⊆ ball 0 b ∩ ball 0 (rR z) ∩ ((fun x : ℂ => x + z) ⁻¹' ball c₂ r₂) ∧
        ∀ x ∈ closedBall (0 : ℂ) r, ∀ y ∈ closedBall (0 : ℂ) r,
          D0 z ω x y = β * (internalMetric (Dd (shiftedCanon γ hC hcirc z u ω)) (ball 0 (2 * ρ)) x y).toReal)
    (hMass : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), z ∈ A → ∀ (b : ℝ) (u : ℂ → ℝ), Adm z b u →
      ∀ᵐ ω ∂P, ∃ n₁ : ℕ, ∀ n ≥ n₁, ∃ a : ℝ, 0 < a ∧
        (μ0 z ω).restrict (closedBall 0 (7 * FirstPassS11ah.certScale n)) =
          (ENNReal.ofReal a • Dμ (shiftedCanon γ hC hcirc z u ω)).restrict
            (closedBall 0 (7 * FirstPassS11ah.certScale n))) :
    RootedCertificateEventualCovarianceStmt P γ hC hcirc c₁ c₂ r₁ r₂ A Ostar U V W T Q' Q η M Adm rR
      μR dR Dμ Dd :=
  rootedCertificateEventualCovarianceStmt_of_local hC hcirc c₁ c₂ r₁ r₂ A Ostar U V W T Q' Q η M hCont hU Adm
    rR μ0 μR D0 dR Dμ Dd hμR hdR
    (ae_of_all _ fun z _ b u hadm => by
      obtain ⟨hu, hcomp, hu0⟩ := hAdmReg z b u hadm
      exact ae_isEuclideanLengthMetric_shiftedCanon hCM γ hh hTr z u hu hcomp hu0 G hG hGa Dd hGreg)
    hDecInt hMass
    (ae_of_all _ fun z _ b u hadm n => by
      obtain ⟨hu, hcomp, hu0⟩ := hAdmReg z b u hadm
      exact ae_shiftedCanon_dilation hCM γ hh hTr z u hu hcomp hu0 hG0 hG0a hinv hstep n)

/-! ### The decoded pair: Campbell-Palm rooted decoders in absolute coordinates

The decoded rooted measure and metric at the root `z` are the observation decoders `κ` (measure) and `dd` (metric) evaluated
on the Campbell-Palm reference observation `campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z` (Frozen/S11c.lean:251). The
centred pair (root at `0`) is the translate by `-z`; `centred_pair_identities` gives the identities `hμR`, `hdR`.
The named hypotheses `hDecInt` and `hMass` of the wrapper are kept as hypotheses (operator note 2026-11-10 08:35 UTC). -/

/-- Decoded rooted measure `μR z ω = κ(obs_D h^{α₀}_z)` in absolute coordinates (rooted LQG measure of Duplantier-Sheffield). -/
noncomputable def decodedRootMeasure {Ω : Type*} {c₂ : ℂ} {r₂ : ℝ}
    (κ : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) → Measure ℂ)
    (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (z : ℂ) (ω : Ω) : Measure ℂ :=
  κ (campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z).2

/-- Decoded rooted metric `dR z ω = dd(obs_D h^{α₀}_z)` in absolute coordinates (Armitage-Gardiner: the decoder is evaluated on
the observation code of the root `z`). -/
noncomputable def decodedRootMetric {Ω : Type*} {c₂ : ℂ} {r₂ : ℝ}
    (dd : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) → ℂ → ℂ → ℝ)
    (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (z : ℂ) (ω : Ω) : ℂ → ℂ → ℝ :=
  dd (campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z).2

/-- Centred decoded measure: the translate of `decodedRootMeasure` by `-z`, so that the root is at `0`. -/
noncomputable def decodedCentredMeasure {Ω : Type*} {c₂ : ℂ} {r₂ : ℝ}
    (κ : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) → Measure ℂ)
    (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (z : ℂ) (ω : Ω) : Measure ℂ :=
  (decodedRootMeasure κ γ α₀ hC z ω).map (fun w : ℂ => w - z)

/-- Centred decoded metric: `D0 z ω x y = dR z ω (x + z) (y + z)`. -/
noncomputable def decodedCentredMetric {Ω : Type*} {c₂ : ℂ} {r₂ : ℝ}
    (dd : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) → ℂ → ℂ → ℝ)
    (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (z : ℂ) (ω : Ω) : ℂ → ℂ → ℝ :=
  fun x y => decodedRootMetric dd γ α₀ hC z ω (x + z) (y + z)

/-- **Eventual covariance for the decoded pair (Campbell-Palm rooted decoders).** The rooted certificate covariance statement
`RootedCertificateEventualCovarianceStmt` for the pair `(μR, dR) = (κ ∘ obs, dd ∘ obs)` in absolute coordinates. Proved from
the Cameron-Martin transfer wrapper `rootedCertificateEventualCovarianceStmt_of_transfer` (n2, CMTransfer.lean) and the
centred pair identities; the decoded-to-internal identity `hDecInt` and the local mass identity `hMass` remain hypotheses. -/
theorem rootedCertificateEventualCovarianceStmt_decoded {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (hCM : HarmonicBalls.CameronMartinGFFMutualAbsCont.{u}) {γ α₀ : ℝ}
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (hh : IsWholePlaneGFF P hC hcirc)
    (hTr : ∀ z : ℂ, IsWholePlaneGFF P (S11c.translatedPairing hC hcirc z) (S11c.translatedCircle hcirc z))
    (c₁ c₂ : ℂ) (r₁ r₂ : ℝ) (A : Set ℂ) (Ostar U V W T Q' Q : Set ℂ) (η M : ℝ)
    (hCont : FirstPassS11i.CertificateContainments η Ostar V W T Q' Q) (hU : U ⊆ closedBall 0 7)
    (Adm : ℂ → ℝ → (ℂ → ℝ) → Prop)
    (hAdmReg : ∀ z b u, Adm z b u → ContDiff ℝ (⊤ : ℕ∞) u ∧ HasCompactSupport u ∧ Real.circleAverage u 0 1 = 0)
    (rR : ℂ → ℝ)
    (κ : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) → Measure ℂ)
    (dd : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) → ℂ → ℂ → ℝ)
    (Dμ : ModConstTestPairings (Set.univ : Set ℂ) → Measure ℂ)
    (Dd : ModConstTestPairings (Set.univ : Set ℂ) → ℂ → ℂ → ℝ)
    (G : Set S11n.CanonSpace) (hG : MeasurableSet G) (hGa : ∀ᵐ ω ∂P, alphaCanon γ hC ω ∈ G)
    (hGreg : ∀ L ∈ G, IsEuclideanLengthMetric (Dd L))
    (G0 : Set S11n.CanonSpace) (hG0 : MeasurableSet G0) (hG0a : ∀ᵐ ω ∂P, alphaCanon γ hC ω ∈ G0)
    (hinv : dilOp ⁻¹' G0 = G0)
    (hstep : ∀ L ∈ G0, ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      Dμ (dilOp L) = ENNReal.ofReal a • (Dμ L).map (fun w : ℂ => w / (((1 / 2 : ℝ)) : ℂ)) ∧
      ∀ x y : ℂ, Dd (dilOp L) x y = b * Dd L (((1 / 2 : ℝ) : ℂ) * x) (((1 / 2 : ℝ) : ℂ) * y))
    (hDecInt : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), z ∈ A → ∀ (b : ℝ) (u : ℂ → ℝ), Adm z b u →
      ∀ᵐ ω ∂P, ∃ ρ r β : ℝ, 0 < ρ ∧ 0 < r ∧ 0 < β ∧
        closedBall (0 : ℂ) (2 * ρ) ⊆ ball 0 b ∩ ball 0 (rR z) ∩ ((fun x : ℂ => x + z) ⁻¹' ball c₂ r₂) ∧
        ∀ x ∈ closedBall (0 : ℂ) r, ∀ y ∈ closedBall (0 : ℂ) r,
          decodedCentredMetric dd γ α₀ hC z ω x y =
            β * (internalMetric (Dd (shiftedCanon γ hC hcirc z u ω)) (ball 0 (2 * ρ)) x y).toReal)
    (hMass : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), z ∈ A → ∀ (b : ℝ) (u : ℂ → ℝ), Adm z b u →
      ∀ᵐ ω ∂P, ∃ n₁ : ℕ, ∀ n ≥ n₁, ∃ a : ℝ, 0 < a ∧
        (decodedCentredMeasure κ γ α₀ hC z ω).restrict (closedBall 0 (7 * FirstPassS11ah.certScale n)) =
          (ENNReal.ofReal a • Dμ (shiftedCanon γ hC hcirc z u ω)).restrict
            (closedBall 0 (7 * FirstPassS11ah.certScale n))) :
    RootedCertificateEventualCovarianceStmt P γ hC hcirc c₁ c₂ r₁ r₂ A Ostar U V W T Q' Q η M Adm rR
      (decodedRootMeasure κ γ α₀ hC) (decodedRootMetric dd γ α₀ hC) Dμ Dd :=
  rootedCertificateEventualCovarianceStmt_of_transfer hCM hC hcirc hh hTr c₁ c₂ r₁ r₂ A Ostar U V W T Q' Q η M
    hCont hU Adm hAdmReg rR (decodedCentredMeasure κ γ α₀ hC) (decodedRootMeasure κ γ α₀ hC)
    (decodedCentredMetric dd γ α₀ hC) (decodedRootMetric dd γ α₀ hC) Dμ Dd G hG hGa hGreg G0 hG0 hG0a hinv hstep
    (centred_pair_identities (decodedRootMeasure κ γ α₀ hC) (decodedRootMetric dd γ α₀ hC)).1
    (centred_pair_identities (decodedRootMeasure κ γ α₀ hC) (decodedRootMetric dd γ α₀ hC)).2
    hDecInt hMass

end FirstPassS11at

namespace FirstPassS11at

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal
open HarmonicBalls HarmonicBalls.S11c

/-! ### Rooted local identification: the decoded mass identity `hMass` (ChatGPT chat 201, sections 4.2-4.5 and 5)

Inputs. `κ` is the decoder on the large domain `D = ball c₂ r₂`; `κj j` and `Dj j` are the decoders and buffered windows of
n2's countable family (`RootedLocalIdent.lean`, pending; `Uj j` the root windows). The inputs `hμ` (rooted LQG measure
existence, LQGMeasureExistence threaded), `hκ`, `hκj` (the rooted clauses of `LocalMeasureKernelStmt`, second conjunct at
`α₀`) and `hRLI` (the buffered identification, outputs of `ae_rootedLocalIdent_base` and `ae_rootedLocalIdent_shifted`)
are hypotheses until their names appear in hb notes/n3-inbox.md. -/

/-- The rooted circle field at root `z` of the decoded clause: the GFF at background insertion `α₀`, plus `-γ log|· - z|`
and the normalisation `γ log max(1, |·|)` (Campbell-Palm rooted field; the field of `LocalMeasureKernelStmt`). -/
noncomputable def rootedCircleField {Ω : Type*} (α₀ γ : ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (z : ℂ) : Ω → ℝ → ℂ → ℝ :=
  fun ω => addCircleAverage (fieldCircleAverage α₀ (hcirc ω))
    (fun w => -γ * Real.log ‖w - z‖ + γ * Real.log (max 1 ‖w‖))

/-- Centred transfer of proportionality (Armitage-Gardiner: restriction and push-forward). If `ν` and `νj` are both
proportional to `μ` on `D` and on `Dj ⊆ D`, and `z + S ⊆ Dj`, then the centred restrictions of `ν` and `νj` to `S` are
proportional with constant `a / aj`. -/
theorem centred_restrict_eq_of_restrict_eq {ν νj μ : Measure ℂ} {z : ℂ} {D Dj S : Set ℂ} {a aj : ℝ}
    (ha : 0 < a) (haj : 0 < aj) (hS : MeasurableSet S) (hDj : Dj ⊆ D)
    (hνD : ν.restrict D = ENNReal.ofReal a • μ.restrict D)
    (hνj : νj.restrict Dj = ENNReal.ofReal aj • μ.restrict Dj)
    (hT : (fun w : ℂ => w - z) ⁻¹' S ⊆ Dj) :
    (ν.map (fun w : ℂ => w - z)).restrict S =
      ENNReal.ofReal (a / aj) • (νj.map (fun w : ℂ => w - z)).restrict S := by
  have hmeas : Measurable (fun w : ℂ => w - z) := measurable_id.sub_const z
  have hTD : (fun w : ℂ => w - z) ⁻¹' S ⊆ D := hT.trans hDj
  have hν : ν.restrict ((fun w : ℂ => w - z) ⁻¹' S) =
      ENNReal.ofReal a • μ.restrict ((fun w : ℂ => w - z) ⁻¹' S) := by
    rw [← Measure.restrict_restrict_of_subset hTD, hνD, Measure.restrict_smul,
      Measure.restrict_restrict_of_subset hTD]
  have hνj' : νj.restrict ((fun w : ℂ => w - z) ⁻¹' S) =
      ENNReal.ofReal aj • μ.restrict ((fun w : ℂ => w - z) ⁻¹' S) := by
    rw [← Measure.restrict_restrict_of_subset hT, hνj, Measure.restrict_smul,
      Measure.restrict_restrict_of_subset hT]
  have hfac : ν.restrict ((fun w : ℂ => w - z) ⁻¹' S) =
      ENNReal.ofReal (a / aj) • νj.restrict ((fun w : ℂ => w - z) ⁻¹' S) := by
    rw [hν, hνj', smul_smul, ← ENNReal.ofReal_mul (div_nonneg ha.le haj.le), div_mul_cancel₀ a haj.ne']
  rw [Measure.restrict_map hmeas hS, Measure.restrict_map hmeas hS, hfac, Measure.map_smul _ hmeas.aemeasurable]

/-- Pointwise assembly of the mass identity at one root `z`, one shift `u` and one buffered window `Dj` (ChatGPT §5): the
two rooted kernel clauses for the same rooted LQG measure `μz` and the buffered identification give the centred mass identity
on `closedBall 0 ρ`; the certificate windows `closedBall 0 (7 certScale n)` eventually lie in it (restriction bookkeeping). -/
theorem ae_mass_of_buffered_identification {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {γ α₀ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {c₂ : ℂ} {r₂ : ℝ} {z : ℂ} {u : ℂ → ℝ}
    {Dj : Set ℂ} (hDj : Dj ⊆ ball c₂ r₂)
    (κ : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) → Measure ℂ)
    (κj : ({φ : ℂ → ℝ // IsTestFunction Dj φ ∧ ∫ x, φ x = 0} → ℝ) → Measure ℂ)
    (Dμ : ModConstTestPairings (Set.univ : Set ℂ) → Measure ℂ) (μz : Ω → Measure ℂ)
    (hκz : ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧
      (κ (campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z).2).restrict (ball c₂ r₂) =
        ENNReal.ofReal a • (μz ω).restrict (ball c₂ r₂))
    (hκjz : ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧
      (κj (campbellReferenceObs γ α₀ Dj (hC ω) z).2).restrict Dj = ENNReal.ofReal a • (μz ω).restrict Dj)
    (hid : ∀ᵐ ω ∂P, ∃ ρ c : ℝ, 0 < ρ ∧ 0 < c ∧ closedBall z ρ ⊆ Dj ∧
      ((κj (campbellReferenceObs γ α₀ Dj (hC ω) z).2).map (fun w : ℂ => w - z)).restrict (closedBall 0 ρ) =
        ENNReal.ofReal c • (Dμ (shiftedCanon γ hC hcirc z u ω)).restrict (closedBall 0 ρ)) :
    ∀ᵐ ω ∂P, ∃ n₁ : ℕ, ∀ n ≥ n₁, ∃ a : ℝ, 0 < a ∧
      (decodedCentredMeasure κ γ α₀ hC z ω).restrict (closedBall 0 (7 * FirstPassS11ah.certScale n)) =
        (ENNReal.ofReal a • Dμ (shiftedCanon γ hC hcirc z u ω)).restrict
          (closedBall 0 (7 * FirstPassS11ah.certScale n)) := by
  filter_upwards [hκz, hκjz, hid] with ω hκzω hκjω hidω
  obtain ⟨a, ha, hνD⟩ := hκzω
  obtain ⟨aj, haj, hνj⟩ := hκjω
  obtain ⟨ρ, c, hρ, hc, hsub, hνc⟩ := hidω
  have hT : (fun w : ℂ => w - z) ⁻¹' closedBall (0 : ℂ) ρ ⊆ Dj := fun w hw =>
    hsub (by simpa [Metric.mem_closedBall, dist_eq_norm] using hw)
  have hEq := centred_restrict_eq_of_restrict_eq ha haj measurableSet_closedBall hDj hνD hνj hT
  rw [hνc] at hEq
  have hS : ((κ (campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z).2).map (fun w : ℂ => w - z)).restrict
      (closedBall 0 ρ) = ENNReal.ofReal ((a / aj) * c) •
        (Dμ (shiftedCanon γ hC hcirc z u ω)).restrict (closedBall 0 ρ) := by
    rw [hEq, smul_smul, ENNReal.ofReal_mul (div_nonneg ha.le haj.le)]
  have hlim : Filter.Tendsto (fun n : ℕ => 7 * FirstPassS11ah.certScale n) Filter.atTop (nhds 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
      (by norm_num : (2 : ℝ)⁻¹ < 1)).const_mul 7
    simpa [FirstPassS11ah.certScale] using h
  obtain ⟨n₁, hn₁⟩ := eventually_atTop.1 ((tendsto_order.1 hlim).2 ρ hρ)
  refine ⟨n₁, fun n hn => ⟨(a / aj) * c, mul_pos (div_pos ha haj) hc, ?_⟩⟩
  have hK : closedBall (0 : ℂ) (7 * FirstPassS11ah.certScale n) ⊆ closedBall 0 ρ :=
    Metric.closedBall_subset_closedBall (hn₁ n hn).le
  unfold decodedCentredMeasure decodedRootMeasure
  calc ((κ (campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z).2).map (fun w : ℂ => w - z)).restrict
        (closedBall 0 (7 * FirstPassS11ah.certScale n))
      = (((κ (campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z).2).map (fun w : ℂ => w - z)).restrict
          (closedBall 0 ρ)).restrict (closedBall 0 (7 * FirstPassS11ah.certScale n)) :=
        (Measure.restrict_restrict_of_subset hK).symm
    _ = (ENNReal.ofReal ((a / aj) * c) • (Dμ (shiftedCanon γ hC hcirc z u ω)).restrict (closedBall 0 ρ)).restrict
          (closedBall 0 (7 * FirstPassS11ah.certScale n)) := by rw [hS]
    _ = (ENNReal.ofReal ((a / aj) * c) • Dμ (shiftedCanon γ hC hcirc z u ω)).restrict
          (closedBall 0 (7 * FirstPassS11ah.certScale n)) := by
        rw [Measure.restrict_smul, Measure.restrict_restrict_of_subset hK, Measure.restrict_smul]

/-- **Decoded mass identity from the rooted local identification (hMass).** The output of the decoded-to-canonical local
identification of n2 (`ae_rootedLocalIdent_base`, `ae_rootedLocalIdent_shifted`, here the hypothesis `hRLI`), with the rooted
kernel clauses `hκ` (large domain) and `hκj` (buffered windows) and the rooted LQG measure existence `hμ`, gives the
`hMass` hypothesis of `rootedCertificateEventualCovarianceStmt_decoded`. The buffered index `j` is chosen after `(z, b, u)`
and before the inner `P`-a.s. statement (ChatGPT §4.2), so `hRLI` quantifies `∃ j` outside `∀ᵐ ω`. -/
theorem hMass_of_rootedLocalIdent {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {γ α₀ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {c₁ c₂ : ℂ} {r₁ r₂ : ℝ} (A : Set ℂ)
    (Adm : ℂ → ℝ → (ℂ → ℝ) → Prop)
    (κ : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) → Measure ℂ)
    (Dμ : ModConstTestPairings (Set.univ : Set ℂ) → Measure ℂ)
    (Uj Dj : ℕ → Set ℂ)
    (κj : (j : ℕ) → ({φ : ℂ → ℝ // IsTestFunction (Dj j) φ ∧ ∫ x, φ x = 0} → ℝ) → Measure ℂ)
    (hDj : ∀ j, Dj j ⊆ ball c₂ r₂)
    (hμ : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), z ∈ A →
      ∃ μz : Ω → Measure ℂ, IsLQGMeasure P γ (rootedCircleField α₀ γ hcirc z) μz)
    (hκ : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), ∀ μz : Ω → Measure ℂ,
      IsLQGMeasure P γ (rootedCircleField α₀ γ hcirc z) μz → ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧
        (κ (campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z).2).restrict (ball c₂ r₂) =
          ENNReal.ofReal a • (μz ω).restrict (ball c₂ r₂))
    (hκj : ∀ j, ∀ᵐ z ∂(volume : Measure ℂ), z ∈ Uj j → ∀ μz : Ω → Measure ℂ,
      IsLQGMeasure P γ (rootedCircleField α₀ γ hcirc z) μz → ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧
        (κj j (campbellReferenceObs γ α₀ (Dj j) (hC ω) z).2).restrict (Dj j) =
          ENNReal.ofReal a • (μz ω).restrict (Dj j))
    (hRLI : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), z ∈ A → ∀ (b : ℝ) (u : ℂ → ℝ), Adm z b u →
      ∃ j : ℕ, z ∈ Uj j ∧ ∀ᵐ ω ∂P, ∃ ρ c : ℝ, 0 < ρ ∧ 0 < c ∧ closedBall z ρ ⊆ Dj j ∧
        ((κj j (campbellReferenceObs γ α₀ (Dj j) (hC ω) z).2).map (fun w : ℂ => w - z)).restrict
            (closedBall 0 ρ) =
          ENNReal.ofReal c • (Dμ (shiftedCanon γ hC hcirc z u ω)).restrict (closedBall 0 ρ)) :
    ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), z ∈ A → ∀ (b : ℝ) (u : ℂ → ℝ), Adm z b u →
      ∀ᵐ ω ∂P, ∃ n₁ : ℕ, ∀ n ≥ n₁, ∃ a : ℝ, 0 < a ∧
        (decodedCentredMeasure κ γ α₀ hC z ω).restrict (closedBall 0 (7 * FirstPassS11ah.certScale n)) =
          (ENNReal.ofReal a • Dμ (shiftedCanon γ hC hcirc z u ω)).restrict
            (closedBall 0 (7 * FirstPassS11ah.certScale n)) := by
  have hκj' : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), ∀ j, z ∈ Uj j → ∀ μz : Ω → Measure ℂ,
      IsLQGMeasure P γ (rootedCircleField α₀ γ hcirc z) μz → ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧
        (κj j (campbellReferenceObs γ α₀ (Dj j) (hC ω) z).2).restrict (Dj j) =
          ENNReal.ofReal a • (μz ω).restrict (Dj j) :=
    ae_restrict_of_ae (ae_all_iff.2 hκj)
  filter_upwards [hμ, hκ, hκj', hRLI] with z hμz hκz hκjz hRz hzA b u hadm
  obtain ⟨μz, hμzE⟩ := hμz hzA
  obtain ⟨j, hzj, hRω⟩ := hRz hzA b u hadm
  exact ae_mass_of_buffered_identification (hDj j) κ (κj j) Dμ μz (hκz μz hμzE) (hκjz j hzj μz hμzE) hRω

end FirstPassS11at

namespace FirstPassS11at

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal
open HarmonicBalls HarmonicBalls.S11c

/-! ### Rooted local identification: the decoded metric identity `hDecInt` (ChatGPT chat 201, sections 4.3(4), 6)

A continuous metric decoder `m φ` on the window `D` (Frozen/S11r `LocalMetricReplacementStmt`, clause (20)) is read as the
window metric `windowMetric D m φ`, extended by `0` off `D × D` (as n2's `rootedMetricAt`). The physical rooted metric is
`rootedWeylMetric` (the real part of the Weyl scaling of the rooted field, Armitage-Gardiner / Duplantier-Sheffield).
The sign and diagonal of the decoded metric are fixed by continuity (`eq_const_mul_of_ofReal_eq`), using that the physical
metric is a Euclidean length metric (an input, see the report). -/

/-- Mean-zero test functions supported in the window `D` (the domain of the decoders). -/
abbrev WinTest (D : Set ℂ) : Type := {φ : ℂ → ℝ // IsTestFunction D φ ∧ ∫ x, φ x = 0}

open Classical in
/-- The window metric of a continuous decoder `m`, extended by `0` off `D × D`. -/
noncomputable def windowMetric (D : Set ℂ) (m : (WinTest D → ℝ) → C(↥(D ×ˢ D), ℝ)) (φ : WinTest D → ℝ) : ℂ → ℂ → ℝ :=
  fun x y => if h : (x, y) ∈ D ×ˢ D then m φ ⟨(x, y), h⟩ else 0

/-- The physical rooted metric at the root `z` (clause (20) of `LocalMetricReplacementStmt`): the real part of the Weyl
scaling of the rooted field `h^ℂ - α₀ log|·| - γ log|· - z| + γ log max(1, |·|)`. -/
noncomputable def rootedWeylMetric {Ω : Type*} (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (ξ α₀ γ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (z : ℂ) (ω : Ω) : ℂ → ℂ → ℝ :=
  fun u v => (weylScaling (𝔇 (hC ω)) ξ
    (fun w => -α₀ * Real.log ‖w‖ - γ * Real.log ‖w - z‖ + γ * Real.log (max 1 ‖w‖)) u v).toReal

/-- Continuity of the window metric in the second variable at a point of the open window (Armitage-Gardiner: a continuous
decoder is continuous on its window). -/
theorem continuousAt_windowMetric {D : Set ℂ} (hD : IsOpen D) (m : (WinTest D → ℝ) → C(↥(D ×ˢ D), ℝ)) (φ : WinTest D → ℝ)
    {x : ℂ} (hx : x ∈ D) : ContinuousAt (fun y => windowMetric D m φ x y) x := by
  have hF : Continuous (fun y : D => (⟨(x, (y : ℂ)), ⟨hx, y.2⟩⟩ : ↥(D ×ˢ D))) :=
    Continuous.subtype_mk (continuous_const.prodMk continuous_subtype_val) (fun y => ⟨hx, y.2⟩)
  have hOn : ContinuousOn (fun y => windowMetric D m φ x y) D := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : (D.domRestrict fun y => windowMetric D m φ x y) =
        fun y : D => m φ ⟨(x, (y : ℂ)), ⟨hx, y.2⟩⟩ := by
      funext y
      simp [Set.domRestrict_apply, windowMetric, hx, y.2]
    rw [heq]
    exact (m φ).continuous.comp hF
  exact hOn.continuousAt (hD.mem_nhds hx)

/-- Sign and diagonal fixing for a decoded length metric (ChatGPT §6; Armitage-Gardiner). If `D` is a Euclidean length
metric, `m` is continuous in its second variable on the open set `O`, and `m` equals `b · D` in `ENNReal` on `O × O`
(`ofReal (m x y) = ofReal b * ofReal (D x y)`), then `m = b · D` on `O × O` as real numbers. Off the diagonal `D > 0`
forces `m > 0` and the equality of reals; on the diagonal `m ≤ 0` from the `ENNReal` identity and `m ≥ 0` from the
limit of the positive values `m x y`, `y → x`. -/
theorem eq_const_mul_of_ofReal_eq {D m : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {O : Set ℂ} (hO : IsOpen O)
    {b : ℝ} (hb : 0 < b) (hcont : ∀ x ∈ O, ContinuousAt (fun y => m x y) x)
    (hid : ∀ x ∈ O, ∀ y ∈ O, ENNReal.ofReal (m x y) = ENNReal.ofReal b * ENNReal.ofReal (D x y)) :
    ∀ x ∈ O, ∀ y ∈ O, m x y = b * D x y := by
  have hnonneg : ∀ x y, 0 ≤ D x y := fun x y => by
    have h1 := hD.triangle x y x
    have h2 := hD.symm y x
    have h3 := hD.self_eq_zero x
    linarith
  have hoff : ∀ x ∈ O, ∀ y ∈ O, x ≠ y → m x y = b * D x y := by
    intro x hx y hy hxy
    have hpos : 0 < D x y :=
      lt_of_le_of_ne (hnonneg x y) (fun h => hxy (hD.eq_of_eq_zero x y h.symm))
    have h1 : ENNReal.ofReal (m x y) = ENNReal.ofReal (b * D x y) := by
      rw [hid x hx y hy, ENNReal.ofReal_mul hb.le]
    have hmpos : 0 < m x y :=
      ENNReal.ofReal_pos.1 (by rw [h1]; exact ENNReal.ofReal_pos.2 (mul_pos hb hpos))
    exact (ENNReal.ofReal_eq_ofReal_iff hmpos.le (mul_nonneg hb.le (hnonneg x y))).1 h1
  intro x hx y hy
  by_cases hxy : x = y
  · subst hxy
    have h0 : ENNReal.ofReal (m x x) = 0 := by
      rw [hid x hx x hx, hD.self_eq_zero x, ENNReal.ofReal_zero, mul_zero]
    have hle : m x x ≤ 0 := ENNReal.ofReal_eq_zero.1 h0
    have hge : 0 ≤ m x x := by
      have ht : Tendsto (fun y => m x y) (𝓝[≠] x) (𝓝 (m x x)) :=
        (hcont x hx).mono_left nhdsWithin_le_nhds
      refine ge_of_tendsto ht ?_
      filter_upwards [eventually_nhdsWithin_of_eventually_nhds (hO.mem_nhds hx),
        (eventually_mem_nhdsWithin : ∀ᶠ y in 𝓝[≠] x, y ∈ ({x}ᶜ : Set ℂ))] with y hyO hyne
      show 0 ≤ m x y
      have hne : x ≠ y := fun h => hyne (Set.mem_singleton_iff.2 h.symm)
      rw [hoff x hx y hyO hne]
      exact mul_nonneg hb.le (hnonneg x y)
    rw [le_antisymm hle hge, hD.self_eq_zero x, mul_zero]
  · exact hoff x hx y hy hxy

/-- No shortcut at a point of an open set, centred at `w0` (the centred version of `HarmonicBalls.eq_internalMetric_on_small_ball`,
S11r/NoShortcut.lean:28; same proof with the centre `w0`). For a Euclidean length metric `D` and an open set `U ∋ w0`, the
ambient length metric equals the internal metric of `U` on a small closed ball about `w0`, and that ball lies in `U`. -/
theorem eq_internalMetric_on_small_ball_at {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {U : Set ℂ} (hU : IsOpen U) {w0 : ℂ} (h0 : w0 ∈ U) :
    ∃ ρ : ℝ, 0 < ρ ∧ closedBall w0 ρ ⊆ U ∧ ∀ x ∈ closedBall w0 ρ, ∀ y ∈ closedBall w0 ρ,
      ENNReal.ofReal (D x y) = internalMetric D U x y := by
  have hnonneg : ∀ x y, 0 ≤ D x y := fun x y => by
    have h1 := hD.triangle x y x
    have h2 := hD.symm y x
    have h3 := hD.self_eq_zero x
    linarith
  obtain ⟨δ, hδ, hball⟩ := (hD.isOpen_iff U).1 hU w0 h0
  have hS : IsOpen {w : ℂ | D w0 w < δ / 4} := by
    refine (hD.isOpen_iff _).2 fun z hz => ⟨δ / 4 - D w0 z, ?_, fun w hw => ?_⟩
    · have hz' : D w0 z < δ / 4 := hz
      linarith
    · have hz' : D w0 z < δ / 4 := hz
      have htri := hD.triangle w0 z w
      have hw' : D z w < δ / 4 - D w0 z := hw
      show D w0 w < δ / 4
      linarith
  have h00 : w0 ∈ {w : ℂ | D w0 w < δ / 4} := by
    show D w0 w0 < δ / 4
    rw [hD.self_eq_zero]
    linarith
  obtain ⟨η, hη, hηS⟩ := Metric.isOpen_iff.1 hS w0 h00
  have key : ∀ x ∈ closedBall w0 (η / 2), D w0 x < δ / 4 := by
    intro x hx
    have hdist : dist x w0 < η := by
      have := mem_closedBall.1 hx
      linarith
    exact hηS (mem_ball.2 hdist)
  refine ⟨η / 2, by linarith, ?_, fun x hx y hy => ?_⟩
  · intro x hx
    exact hball x (by linarith [key x hx])
  have hx' := key x hx
  have hy' := key y hy
  have hxy : D x y < δ / 2 := by
    have htri := hD.triangle x w0 y
    have hsymm := hD.symm x w0
    linarith
  have hclear : ∀ z ∉ U, δ / 2 ≤ D x z := by
    intro z hz
    have hz0 : δ ≤ D w0 z := by
      by_contra hlt
      exact hz (hball z (not_le.1 hlt))
    have htri := hD.triangle w0 x z
    linarith
  exact (hD.internalMetric_eq_of_boundary_clearance hnonneg hclear hxy).symm

/-- **Decoded metric identity on a small ball (ChatGPT §6, the assembly of `hDecInt`).** Fix a root `z`, a buffered window
`Dj ⊆ D` (open), and the two decoders `mD`, `mj` of the large and buffered windows. Inputs: the physical rooted metric `Dw`
is a Euclidean length metric (the input `hDw`, to be sourced; see the report); the canonical metric `Dl` is one (`hDl`); the
two clauses (20) for `Dw` with the internal metrics on `D` and on `Dj`; and the buffered identification (n2's metric
output, on a whole ball about `z`). Conclusion: a positive radius `ρ` with `closedBall 0 (2ρ) ⊆ W`, a radius `r`, and a constant
`β > 0` with the centred decoded metric equal to `β` times the internal metric of `Dl` on `ball 0 (2ρ)`. -/
theorem hDecInt_at_of_local {D Dj W : Set ℂ} {z : ℂ} {Dw Dl : ℂ → ℂ → ℝ}
    (hDw : IsEuclideanLengthMetric Dw) (hDl : IsEuclideanLengthMetric Dl)
    (hDO : IsOpen D) (hzD : z ∈ D) (hDjO : IsOpen Dj) (hWO : IsOpen W) (hW0 : (0 : ℂ) ∈ W)
    (mD : (WinTest D → ℝ) → C(↥(D ×ˢ D), ℝ)) (φD : WinTest D → ℝ)
    (mj : (WinTest Dj → ℝ) → C(↥(Dj ×ˢ Dj), ℝ)) (φj : WinTest Dj → ℝ)
    (hclD : ∃ bD : ℝ, 0 < bD ∧ ∀ x ∈ D, ∀ y ∈ D,
      ENNReal.ofReal (windowMetric D mD φD x y) = ENNReal.ofReal bD * internalMetric Dw D x y)
    (hclj : ∃ bj : ℝ, 0 < bj ∧ ∀ x ∈ Dj, ∀ y ∈ Dj,
      ENNReal.ofReal (windowMetric Dj mj φj x y) = ENNReal.ofReal bj * internalMetric Dw Dj x y)
    (hid : ∃ c ρ : ℝ, 0 < c ∧ 0 < ρ ∧ closedBall z ρ ⊆ Dj ∧
      ∀ x ∈ closedBall (0 : ℂ) ρ, ∀ y ∈ closedBall (0 : ℂ) ρ,
        windowMetric Dj mj φj (x + z) (y + z) = c * Dl x y) :
    ∃ ρ r β : ℝ, 0 < ρ ∧ 0 < r ∧ 0 < β ∧ closedBall (0 : ℂ) (2 * ρ) ⊆ W ∧
      ∀ x ∈ closedBall (0 : ℂ) r, ∀ y ∈ closedBall (0 : ℂ) r,
        windowMetric D mD φD (x + z) (y + z) = β * (internalMetric Dl (ball 0 (2 * ρ)) x y).toReal := by
  obtain ⟨bD, hbD, hclD⟩ := hclD
  obtain ⟨bj, hbj, hclj⟩ := hclj
  obtain ⟨c, ρ, hc, hρ, hsubj, hidn⟩ := hid
  have hzDj : z ∈ Dj := hsubj (mem_closedBall_self hρ.le)
  obtain ⟨ρD, hρD, hsubD, hidD⟩ := eq_internalMetric_on_small_ball_at hDw hDO hzD
  obtain ⟨ρJ, hρJ, hsubJ, hidJ⟩ := eq_internalMetric_on_small_ball_at hDw hDjO hzDj
  have hm : 0 < min ρD ρJ := lt_min hρD hρJ
  have hOD : ball z (min ρD ρJ) ⊆ closedBall z ρD := fun x hx =>
    Metric.closedBall_subset_closedBall (min_le_left _ _) (Metric.ball_subset_closedBall hx)
  have hOJ : ball z (min ρD ρJ) ⊆ closedBall z ρJ := fun x hx =>
    Metric.closedBall_subset_closedBall (min_le_right _ _) (Metric.ball_subset_closedBall hx)
  have hOD' : ∀ x ∈ ball z (min ρD ρJ), x ∈ D := fun x hx => hsubD (hOD hx)
  have hOJ' : ∀ x ∈ ball z (min ρD ρJ), x ∈ Dj := fun x hx => hsubJ (hOJ hx)
  -- sign and diagonal fixing on the two windows
  have hD1 : ∀ x ∈ ball z (min ρD ρJ), ∀ y ∈ ball z (min ρD ρJ),
      windowMetric D mD φD x y = bD * Dw x y :=
    eq_const_mul_of_ofReal_eq hDw isOpen_ball hbD
      (fun x hx => continuousAt_windowMetric hDO mD φD (hOD' x hx))
      (fun x hx y hy => by
        rw [hclD x (hOD' x hx) y (hOD' y hy), hidD x (hOD hx) y (hOD hy)])
  have hJ1 : ∀ x ∈ ball z (min ρD ρJ), ∀ y ∈ ball z (min ρD ρJ),
      windowMetric Dj mj φj x y = bj * Dw x y :=
    eq_const_mul_of_ofReal_eq hDw isOpen_ball hbj
      (fun x hx => continuousAt_windowMetric hDjO mj φj (hOJ' x hx))
      (fun x hx y hy => by
        rw [hclj x (hOJ' x hx) y (hOJ' y hy), hidJ x (hOJ hx) y (hOJ hy)])
  -- the identity on a small ball about `0` (centred coordinates), physical side equal to the canonical side
  have hkey : ∀ x ∈ closedBall (0 : ℂ) (min ρ (min ρD ρJ / 2)), ∀ y ∈ closedBall (0 : ℂ) (min ρ (min ρD ρJ / 2)),
      windowMetric D mD φD (x + z) (y + z) = bD * c / bj * Dl x y := by
    intro x hx y hy
    have hxn : ‖x‖ ≤ min ρD ρJ / 2 := (mem_closedBall_zero_iff.1 hx).trans (min_le_right _ _)
    have hyn : ‖y‖ ≤ min ρD ρJ / 2 := (mem_closedBall_zero_iff.1 hy).trans (min_le_right _ _)
    have hx1 : x + z ∈ ball z (min ρD ρJ) := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_right]
      linarith
    have hy1 : y + z ∈ ball z (min ρD ρJ) := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_right]
      linarith
    have hxρ : x ∈ closedBall (0 : ℂ) ρ :=
      mem_closedBall_zero_iff.2 ((mem_closedBall_zero_iff.1 hx).trans (min_le_left _ _))
    have hyρ : y ∈ closedBall (0 : ℂ) ρ :=
      mem_closedBall_zero_iff.2 ((mem_closedBall_zero_iff.1 hy).trans (min_le_left _ _))
    have h := (hJ1 _ hx1 _ hy1).symm.trans (hidn x hxρ y hyρ)
    rw [hD1 _ hx1 _ hy1, div_mul_eq_mul_div, eq_div_iff hbj.ne']
    linear_combination bD * h
  -- the canonical side: the internal metric on a ball `ball 0 (2 ρo)` inside `W`
  obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.1 hWO 0 hW0
  have hball2 : closedBall (0 : ℂ) (2 * (ε / 4)) ⊆ ball (0 : ℂ) ε :=
    Metric.closedBall_subset_ball (by linarith)
  have hUo : closedBall (0 : ℂ) (2 * (ε / 4)) ⊆ W := hball2.trans hεW
  have hU0 : (0 : ℂ) ∈ ball (0 : ℂ) (2 * (ε / 4)) := mem_ball_self (by linarith)
  obtain ⟨ρL, hρL, _, hidL⟩ := eq_internalMetric_on_small_ball_at hDl isOpen_ball hU0
  have hnonnegL : ∀ x y, 0 ≤ Dl x y := fun x y => by
    have h1 := hDl.triangle x y x
    have h2 := hDl.symm y x
    have h3 := hDl.self_eq_zero x
    linarith
  refine ⟨ε / 4, min (min ρ (min ρD ρJ / 2)) ρL, bD * c / bj, by linarith,
    lt_min (lt_min hρ (half_pos hm)) hρL, div_pos (mul_pos hbD hc) hbj, hUo, ?_⟩
  intro x hx y hy
  have hx' : x ∈ closedBall (0 : ℂ) (min ρ (min ρD ρJ / 2)) :=
    mem_closedBall_zero_iff.2 ((mem_closedBall_zero_iff.1 hx).trans (min_le_left _ _))
  have hy' : y ∈ closedBall (0 : ℂ) (min ρ (min ρD ρJ / 2)) :=
    mem_closedBall_zero_iff.2 ((mem_closedBall_zero_iff.1 hy).trans (min_le_left _ _))
  have hxL : x ∈ closedBall (0 : ℂ) ρL :=
    mem_closedBall_zero_iff.2 ((mem_closedBall_zero_iff.1 hx).trans (min_le_right _ _))
  have hyL : y ∈ closedBall (0 : ℂ) ρL :=
    mem_closedBall_zero_iff.2 ((mem_closedBall_zero_iff.1 hy).trans (min_le_right _ _))
  rw [hkey x hx' y hy']
  rw [← hidL x hxL y hyL, ENNReal.toReal_ofReal (hnonnegL x y)]

end FirstPassS11at

namespace FirstPassS11at

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal
open HarmonicBalls HarmonicBalls.S11c

/-- The window `ball 0 b ∩ ball 0 (rR z) ∩ (· + z)⁻¹' ball c₂ r₂` of the decoded identity `hDecInt` is open. -/
theorem isOpen_decodedWindow {c₂ z : ℂ} {r₂ b r : ℝ} :
    IsOpen (ball (0 : ℂ) b ∩ ball (0 : ℂ) r ∩ ((fun x : ℂ => x + z) ⁻¹' ball c₂ r₂)) :=
  (isOpen_ball.inter isOpen_ball).inter (isOpen_ball.preimage (by fun_prop))

/-- **Decoded metric identity from the rooted local identification (hDecInt, ae level).** The assembly of
`hDecInt_at_of_local` over the root `z`, the shift `(b, u)` and the buffered index `j`: as in §4.2 of ChatGPT chat 201, `j` is
chosen after `(z, b, u)` and before the inner `P`-a.s. statement. Inputs: the frozen metric clauses (20) of
`LocalMetricReplacementStmt` on the large window (`hDwD`) and on the buffered windows (`hDwj`), in the `ENNReal` form of
the clause; the rooted physical metric is a Euclidean length metric (`hLen`: NOT in the repository, see the report); n2's
buffered metric identification (`hRLIm`, whole-ball form); the canonical length-metric property (`hLenC`); and the
positivity of admissible shifts (`hAdmPos`: `0 < b`) and of the root radius (`hrR`: `0 < rR z` on `A`), which give
`0 ∈ ball 0 b ∩ ball 0 (rR z) ∩ V_z` (`z ∈ ball c₂ r₂` from `hc1`). The conclusion is `hDecInt` of
`rootedCertificateEventualCovarianceStmt_decoded` for the decoder `windowMetric (ball c₂ r₂) mD`. -/
theorem hDecInt_of_rootedLocalIdent {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {γ α₀ ξ : ℝ} {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {c₁ c₂ : ℂ} {r₁ r₂ : ℝ} (A : Set ℂ) (Adm : ℂ → ℝ → (ℂ → ℝ) → Prop) (rR : ℂ → ℝ)
    (Dd : ModConstTestPairings (Set.univ : Set ℂ) → ℂ → ℂ → ℝ)
    (Uj Dj : ℕ → Set ℂ)
    (mD : (WinTest (ball c₂ r₂) → ℝ) → C(↥(ball c₂ r₂ ×ˢ ball c₂ r₂), ℝ))
    (mj : (j : ℕ) → (WinTest (Dj j) → ℝ) → C(↥(Dj j ×ˢ Dj j), ℝ))
    (hDjO : ∀ j, IsOpen (Dj j)) (hc1 : ball c₁ r₁ ⊆ ball c₂ r₂)
    (hAdmPos : ∀ (z : ℂ) (b : ℝ) (u : ℂ → ℝ), Adm z b u → 0 < b)
    (hrR : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), z ∈ A → 0 < rR z)
    (hDwD : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), ∀ᵐ ω ∂P, ∃ b : ℝ, 0 < b ∧
      ∀ p : ↥(ball c₂ r₂ ×ˢ ball c₂ r₂),
        ENNReal.ofReal (mD (campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z).2 p) =
          ENNReal.ofReal b * internalMetric (rootedWeylMetric 𝔇 ξ α₀ γ hC z ω) (ball c₂ r₂) p.1.1 p.1.2)
    (hDwj : ∀ j, ∀ᵐ z ∂(volume : Measure ℂ), z ∈ Uj j → ∀ᵐ ω ∂P, ∃ b : ℝ, 0 < b ∧
      ∀ p : ↥(Dj j ×ˢ Dj j),
        ENNReal.ofReal (mj j (campbellReferenceObs γ α₀ (Dj j) (hC ω) z).2 p) =
          ENNReal.ofReal b * internalMetric (rootedWeylMetric 𝔇 ξ α₀ γ hC z ω) (Dj j) p.1.1 p.1.2)
    (hLen : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), ∀ᵐ ω ∂P,
      IsEuclideanLengthMetric (rootedWeylMetric 𝔇 ξ α₀ γ hC z ω))
    (hRLIm : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), z ∈ A → ∀ (b : ℝ) (u : ℂ → ℝ), Adm z b u →
      ∃ j : ℕ, z ∈ Uj j ∧ ∀ᵐ ω ∂P, ∃ c ρ : ℝ, 0 < c ∧ 0 < ρ ∧ closedBall z ρ ⊆ Dj j ∧
        ∀ x ∈ closedBall (0 : ℂ) ρ, ∀ y ∈ closedBall (0 : ℂ) ρ,
          windowMetric (Dj j) (mj j) (campbellReferenceObs γ α₀ (Dj j) (hC ω) z).2 (x + z) (y + z) =
            c * Dd (shiftedCanon γ hC hcirc z u ω) x y)
    (hLenC : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), z ∈ A → ∀ (b : ℝ) (u : ℂ → ℝ), Adm z b u →
      ∀ᵐ ω ∂P, IsEuclideanLengthMetric (Dd (shiftedCanon γ hC hcirc z u ω))) :
    ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), z ∈ A → ∀ (b : ℝ) (u : ℂ → ℝ), Adm z b u →
      ∀ᵐ ω ∂P, ∃ ρ r β : ℝ, 0 < ρ ∧ 0 < r ∧ 0 < β ∧
        closedBall (0 : ℂ) (2 * ρ) ⊆ ball (0 : ℂ) b ∩ ball (0 : ℂ) (rR z) ∩ ((fun x : ℂ => x + z) ⁻¹' ball c₂ r₂) ∧
        ∀ x ∈ closedBall (0 : ℂ) r, ∀ y ∈ closedBall (0 : ℂ) r,
          decodedCentredMetric (windowMetric (ball c₂ r₂) mD) γ α₀ hC z ω x y =
            β * (internalMetric (Dd (shiftedCanon γ hC hcirc z u ω)) (ball 0 (2 * ρ)) x y).toReal := by
  have hDwj' : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), ∀ j, z ∈ Uj j → ∀ᵐ ω ∂P, ∃ b : ℝ, 0 < b ∧
      ∀ p : ↥(Dj j ×ˢ Dj j),
        ENNReal.ofReal (mj j (campbellReferenceObs γ α₀ (Dj j) (hC ω) z).2 p) =
          ENNReal.ofReal b * internalMetric (rootedWeylMetric 𝔇 ξ α₀ γ hC z ω) (Dj j) p.1.1 p.1.2 :=
    ae_restrict_of_ae (ae_all_iff.2 hDwj)
  filter_upwards [hDwD, hDwj', hLen, hRLIm, hLenC, hrR, ae_restrict_mem measurableSet_ball]
    with z hDwDz hDwjz hLenz hRLIz hLenCz hrRz hzB hzA b u hadm
  have hzD : z ∈ ball c₂ r₂ := hc1 hzB
  obtain ⟨j, hzj, hRω⟩ := hRLIz hzA b u hadm
  have hWO : IsOpen (ball (0 : ℂ) b ∩ ball (0 : ℂ) (rR z) ∩ ((fun x : ℂ => x + z) ⁻¹' ball c₂ r₂)) :=
    isOpen_decodedWindow
  have hW0' : (0 : ℂ) ∈ ball (0 : ℂ) b ∩ ball (0 : ℂ) (rR z) ∩ ((fun x : ℂ => x + z) ⁻¹' ball c₂ r₂) :=
    ⟨⟨Metric.mem_ball_self (hAdmPos z b u hadm), Metric.mem_ball_self (hrRz hzA)⟩, by simpa using hzD⟩
  filter_upwards [hDwDz, hDwjz j hzj, hLenz, hRω, hLenCz hzA b u hadm] with ω hDω hDjω hLenω hidω hLenCω
  obtain ⟨bD, hbD, hDform⟩ := hDω
  obtain ⟨bj, hbj, hDjform⟩ := hDjω
  have hclD : ∃ bD' : ℝ, 0 < bD' ∧ ∀ x ∈ ball c₂ r₂, ∀ y ∈ ball c₂ r₂,
      ENNReal.ofReal (windowMetric (ball c₂ r₂) mD (campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z).2 x y) =
        ENNReal.ofReal bD' * internalMetric (rootedWeylMetric 𝔇 ξ α₀ γ hC z ω) (ball c₂ r₂) x y := by
    refine ⟨bD, hbD, fun x hx y hy => ?_⟩
    have hxy : (x, y) ∈ ball c₂ r₂ ×ˢ ball c₂ r₂ := ⟨hx, hy⟩
    have h := hDform ⟨(x, y), hxy⟩
    simpa [windowMetric, hxy] using h
  have hclj : ∃ bj' : ℝ, 0 < bj' ∧ ∀ x ∈ Dj j, ∀ y ∈ Dj j,
      ENNReal.ofReal (windowMetric (Dj j) (mj j) (campbellReferenceObs γ α₀ (Dj j) (hC ω) z).2 x y) =
        ENNReal.ofReal bj' * internalMetric (rootedWeylMetric 𝔇 ξ α₀ γ hC z ω) (Dj j) x y := by
    refine ⟨bj, hbj, fun x hx y hy => ?_⟩
    have hxy : (x, y) ∈ Dj j ×ˢ Dj j := ⟨hx, hy⟩
    have h := hDjform ⟨(x, y), hxy⟩
    simpa [windowMetric, hxy] using h
  obtain ⟨ρ', r, β, h1, h2, h3, h4, h5⟩ :=
    hDecInt_at_of_local hLenω hLenCω (isOpen_ball) hzD (hDjO j) hWO hW0'
      (mD) (campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z).2 (mj j)
      (campbellReferenceObs γ α₀ (Dj j) (hC ω) z).2 hclD hclj hidω
  exact ⟨ρ', r, β, h1, h2, h3, h4, fun x hx y hy => h5 x hx y hy⟩

universe u

/-- **Rooted certificate eventual covariance, decoded form, from the rooted local identification** (q1,
fp-S11at). The two decoded clauses `hMass` (measure, `hMass_of_rootedLocalIdent`) and `hDecInt` (metric,
`hDecInt_of_rootedLocalIdent`) are derived from their stated inputs; the rest is passed through to
`rootedCertificateEventualCovarianceStmt_decoded`, with the decoder `windowMetric (ball c₂ r₂) mD`. -/
theorem rootedCertificateEventualCovarianceStmt_decoded_of_rootedLocalIdent {Ω : Type u} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (hCM : HarmonicBalls.CameronMartinGFFMutualAbsCont.{u})
    {γ α₀ ξ : ℝ} {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ}
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (hh : IsWholePlaneGFF P hC hcirc)
    (hTr : ∀ z : ℂ, IsWholePlaneGFF P (S11c.translatedPairing hC hcirc z) (S11c.translatedCircle hcirc z))
    (c₁ c₂ : ℂ) (r₁ r₂ : ℝ) (A : Set ℂ) (Ostar U V W T Q' Q : Set ℂ) (η M : ℝ)
    (hCont : FirstPassS11i.CertificateContainments η Ostar V W T Q' Q) (hU : U ⊆ closedBall 0 7)
    (Adm : ℂ → ℝ → (ℂ → ℝ) → Prop)
    (hAdmReg : ∀ z b u, Adm z b u → ContDiff ℝ (⊤ : ℕ∞) u ∧ HasCompactSupport u ∧ Real.circleAverage u 0 1 = 0)
    (rR : ℂ → ℝ)
    (κ : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) → Measure ℂ)
    (mD : (WinTest (ball c₂ r₂) → ℝ) → C(↥(ball c₂ r₂ ×ˢ ball c₂ r₂), ℝ))
    (Dμ : ModConstTestPairings (Set.univ : Set ℂ) → Measure ℂ)
    (Dd : ModConstTestPairings (Set.univ : Set ℂ) → ℂ → ℂ → ℝ)
    (G : Set S11n.CanonSpace) (hG : MeasurableSet G) (hGa : ∀ᵐ ω ∂P, alphaCanon γ hC ω ∈ G)
    (hGreg : ∀ L ∈ G, IsEuclideanLengthMetric (Dd L))
    (G0 : Set S11n.CanonSpace) (hG0 : MeasurableSet G0) (hG0a : ∀ᵐ ω ∂P, alphaCanon γ hC ω ∈ G0)
    (hinv : dilOp ⁻¹' G0 = G0)
    (hstep : ∀ L ∈ G0, ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      Dμ (dilOp L) = ENNReal.ofReal a • (Dμ L).map (fun w : ℂ => w / (((1 / 2 : ℝ)) : ℂ)) ∧
      ∀ x y : ℂ, Dd (dilOp L) x y = b * Dd L (((1 / 2 : ℝ) : ℂ) * x) (((1 / 2 : ℝ) : ℂ) * y))
    (Uj Dj : ℕ → Set ℂ)
    (κj : (j : ℕ) → ({φ : ℂ → ℝ // IsTestFunction (Dj j) φ ∧ ∫ x, φ x = 0} → ℝ) → Measure ℂ)
    (mj : (j : ℕ) → (WinTest (Dj j) → ℝ) → C(↥(Dj j ×ˢ Dj j), ℝ))
    (hDj : ∀ j, Dj j ⊆ ball c₂ r₂) (hDjO : ∀ j, IsOpen (Dj j)) (hc1 : ball c₁ r₁ ⊆ ball c₂ r₂)
    (hAdmPos : ∀ (z : ℂ) (b : ℝ) (u : ℂ → ℝ), Adm z b u → 0 < b)
    (hrR : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), z ∈ A → 0 < rR z)
    (hExist0 : LQGMeasureExistence P γ 0 hC hcirc) (hExistα : LQGMeasureExistence P γ α₀ hC hcirc)
    (hA10 : ∀ μ : Ω → Measure ℂ, DMSLemmaA10WholePlaneMarked P γ hC hcirc μ)
    (hBridge : FirstPassS11atProducers.HMuPairingBridge P γ α₀ hC hcirc) (hWin : ball c₁ r₁ ⊆ ball (0 : ℂ) 1)
    (hκ : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), ∀ μz : Ω → Measure ℂ,
      IsLQGMeasure P γ (rootedCircleField α₀ γ hcirc z) μz → ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧
        (κ (campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z).2).restrict (ball c₂ r₂) =
          ENNReal.ofReal a • (μz ω).restrict (ball c₂ r₂))
    (hκj : ∀ j, ∀ᵐ z ∂(volume : Measure ℂ), z ∈ Uj j → ∀ μz : Ω → Measure ℂ,
      IsLQGMeasure P γ (rootedCircleField α₀ γ hcirc z) μz → ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧
        (κj j (campbellReferenceObs γ α₀ (Dj j) (hC ω) z).2).restrict (Dj j) =
          ENNReal.ofReal a • (μz ω).restrict (Dj j))
    (hRLI : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), z ∈ A → ∀ (b : ℝ) (u : ℂ → ℝ), Adm z b u →
      ∃ j : ℕ, z ∈ Uj j ∧ ∀ᵐ ω ∂P, ∃ ρ c : ℝ, 0 < ρ ∧ 0 < c ∧ closedBall z ρ ⊆ Dj j ∧
        ((κj j (campbellReferenceObs γ α₀ (Dj j) (hC ω) z).2).map (fun w : ℂ => w - z)).restrict
            (closedBall 0 ρ) =
          ENNReal.ofReal c • (Dμ (shiftedCanon γ hC hcirc z u ω)).restrict (closedBall 0 ρ))
    (hDwD : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), ∀ᵐ ω ∂P, ∃ b : ℝ, 0 < b ∧
      ∀ p : ↥(ball c₂ r₂ ×ˢ ball c₂ r₂),
        ENNReal.ofReal (mD (campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z).2 p) =
          ENNReal.ofReal b * internalMetric (rootedWeylMetric 𝔇 ξ α₀ γ hC z ω) (ball c₂ r₂) p.1.1 p.1.2)
    (hDwj : ∀ j, ∀ᵐ z ∂(volume : Measure ℂ), z ∈ Uj j → ∀ᵐ ω ∂P, ∃ b : ℝ, 0 < b ∧
      ∀ p : ↥(Dj j ×ˢ Dj j),
        ENNReal.ofReal (mj j (campbellReferenceObs γ α₀ (Dj j) (hC ω) z).2 p) =
          ENNReal.ofReal b * internalMetric (rootedWeylMetric 𝔇 ξ α₀ γ hC z ω) (Dj j) p.1.1 p.1.2)
    (hLenFr : LQGMetricLengthUnivFrozen.{u}) (hFieldFr : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hRootFr : RootedPhysicalMetricContinuousAtInsertionFrozen.{u})
    (h𝔇 : IsLQGMetric γ ξ 𝔇) (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hRLIm : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), z ∈ A → ∀ (b : ℝ) (u : ℂ → ℝ), Adm z b u →
      ∃ j : ℕ, z ∈ Uj j ∧ ∀ᵐ ω ∂P, ∃ c ρ : ℝ, 0 < c ∧ 0 < ρ ∧ closedBall z ρ ⊆ Dj j ∧
        ∀ x ∈ closedBall (0 : ℂ) ρ, ∀ y ∈ closedBall (0 : ℂ) ρ,
          windowMetric (Dj j) (mj j) (campbellReferenceObs γ α₀ (Dj j) (hC ω) z).2 (x + z) (y + z) =
            c * Dd (shiftedCanon γ hC hcirc z u ω) x y)
    (hLenC : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), z ∈ A → ∀ (b : ℝ) (u : ℂ → ℝ), Adm z b u →
      ∀ᵐ ω ∂P, IsEuclideanLengthMetric (Dd (shiftedCanon γ hC hcirc z u ω))) :
    RootedCertificateEventualCovarianceStmt P γ hC hcirc c₁ c₂ r₁ r₂ A Ostar U V W T Q' Q η M Adm rR
      (decodedRootMeasure κ γ α₀ hC) (decodedRootMetric (windowMetric (ball c₂ r₂) mD) γ α₀ hC) Dμ Dd :=
  rootedCertificateEventualCovarianceStmt_decoded hCM hC hcirc hh hTr c₁ c₂ r₁ r₂ A Ostar U V W T Q' Q η M
    hCont hU Adm hAdmReg rR κ (windowMetric (ball c₂ r₂) mD) Dμ Dd G hG hGa hGreg G0 hG0 hG0a hinv hstep
    (hDecInt_of_rootedLocalIdent A Adm rR Dd Uj Dj mD mj hDjO hc1 hAdmPos hrR hDwD hDwj
      (FirstPassS11atProducers.rootedWeylMetric_ae_z hLenFr hFieldFr hRootFr P γ ξ α₀ hC hcirc hh 𝔇 h𝔇 hγ0 hγ2 hα
        (ball c₁ r₁))
      hRLIm hLenC)
    (hMass_of_rootedLocalIdent A Adm κ Dμ Uj Dj κj hDj
      (by
        filter_upwards [FirstPassS11atProducers.ae_exists_rootedLQGMeasure P γ α₀ hC hcirc c₁ r₁ hh hγ0 hγ2 hα
          hExist0 hExistα hA10 hBridge hWin] with z hz
        exact fun _ => hz)
      hκ hκj hRLI)

end FirstPassS11at

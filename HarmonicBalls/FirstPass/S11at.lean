import HarmonicBalls.FirstPass.S11r.NoShortcut
import HarmonicBalls.FirstPass.S11i.CertDilate
import HarmonicBalls.FirstPass.S11i.RootedFrequencyShift
import HarmonicBalls.FirstPass.S11aq
import HarmonicBalls.FirstPass.S11ah.Cutoff
import HarmonicBalls.FirstPass.S11c.TranslateField11_7
import HarmonicBalls.Defs.LQGMetric
import HarmonicBalls.FirstPass.S11asLocal

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

/-- **Eventual rooted covariance from the local inputs (fixed-root assembly).** Given the physical pair `(μ0, D0)` at
`z` (the root-shifted field, translated so that it is centred at `0`; `hμR`, `hdR` identify the rooted physical pair
with it), the local inputs of `ae_eventual_certificateEvent_pair` for every admissible `(b, u)`, and the dilation identity
of the shifted canonical decoders `hdil` (the scaling covariance of `ae_decoders_dilOp_iterate`, here required for the
shifted element), the statement `RootedCertificateEventualCovarianceStmt` follows. -/
theorem rootedCertificateEventualCovarianceStmt_of_local {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {γ : ℝ} (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (c₁ c₂ : ℂ) (r₁ r₂ : ℝ) (A : Set ℂ) (Ostar U V W T Q' Q : Set ℂ) (η M : ℝ)
    (hCont : FirstPassS11i.CertificateContainments η Ostar V W T Q' Q) (hU : U ⊆ closedBall 0 7)
    (Adm : ℂ → ℝ → (ℂ → ℝ) → Prop) (hAdm : ∀ z b u, Adm z b u → 0 < b) (rR : ℂ → ℝ)
    (μ0 μR : ℂ → Ω → Measure ℂ) (D0 dR : ℂ → Ω → ℂ → ℂ → ℝ)
    (Dμ : ModConstTestPairings (Set.univ : Set ℂ) → Measure ℂ)
    (Dd : ModConstTestPairings (Set.univ : Set ℂ) → ℂ → ℂ → ℝ)
    (hμR : ∀ z ω, μR z ω = (μ0 z ω).map (fun w : ℂ => w - -z))
    (hdR : ∀ z ω, dR z ω = fun x y => D0 z ω (x + -z) (y + -z))
    (hD0 : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), z ∈ A → ∀ (b : ℝ) (u : ℂ → ℝ), Adm z b u →
      ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D0 z ω))
    (hDu : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), z ∈ A → ∀ (b : ℝ) (u : ℂ → ℝ), Adm z b u →
      ∀ᵐ ω ∂P, IsEuclideanLengthMetric (Dd (shiftedCanon γ hC hcirc z u ω)))
    (hInt : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), z ∈ A → ∀ (b : ℝ) (u : ℂ → ℝ), Adm z b u →
      ∀ᵐ ω ∂P, ∃ β : ℝ, 0 < β ∧ ∀ x ∈ closedBall (0 : ℂ) (b / 2), ∀ y ∈ closedBall (0 : ℂ) (b / 2),
        internalMetric (D0 z ω) (ball 0 b) x y =
          ENNReal.ofReal β * internalMetric (Dd (shiftedCanon γ hC hcirc z u ω)) (ball 0 b) x y)
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
  filter_upwards [hD0, hDu, hInt, hMass, hdil] with z hD0z hDuz hIntz hMassz hdilz hzA b u hadm
  have hb : 0 < b := hAdm z b u hadm
  have hball : (0 : ℂ) ∈ ball (0 : ℂ) b := mem_ball_self hb
  have hpair := ae_eventual_certificateEvent_pair (μ0 z) (fun ω => Dμ (shiftedCanon γ hC hcirc z u ω))
    (D0 z) (fun ω => Dd (shiftedCanon γ hC hcirc z u ω)) isOpen_ball hball (half_pos hb) Ostar U V W T Q' Q η M hCont hU
    (hD0z hzA b u hadm) (hDuz hzA b u hadm) (hIntz hzA b u hadm) (hMassz hzA b u hadm)
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
end FirstPassS11at

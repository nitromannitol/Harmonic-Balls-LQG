import HarmonicBalls.Defs.LQGMetric
import HarmonicBalls.FirstPass.S11asLocal

/-!
# Internal and ambient length metric agree on a small ball (fp-S11at, round 9)

Deterministic half of the eventual rooted certificate covariance (ChatGPT chat 195,
`notes/fp-gaps/CHATGPT-hb-hCov-locality.md`, steps 6a-6b). A Euclidean length metric `D` (`IsEuclideanLengthMetric`,
Fact 2.2 I of Bou-Rabee-Gwynne) is not local: its ambient value `D(x, y)` is an infimum over paths in all of `ℂ`, which
may leave a fixed open set `U`. Near a point `0 ∈ U` the two distances nevertheless agree (Armstrong-Kuusi-Mourrat length
structure): an almost-geodesic between two points of a much smaller `D`-ball about `0` cannot leave the `D`-ball of radius
`ε` about `0`, and that ball lies in `U`. This is the no-shortcut localization of `eq_internalMetric_on_small_ball`.
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

/-- The `D`-length of a path bounds the `D`-distance from its initial point to each of its points:
`D(z, P(t)) ≤ len(P; D)` for `t ∈ [0, 1]` (Armitage-Gardiner: a one-step partition of the length sum). -/
theorem ofReal_dist_le_pathLength {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {z w : ℂ} (P : Path z w) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    ENNReal.ofReal (D z (P.extend t)) ≤ pathLength D P := by
  have ht0 : 0 ≤ t := ht.1
  have ht1 : t ≤ 1 := ht.2
  unfold pathLength curveLength
  refine le_iSup_of_le ⟨1, ⟨fun i : ℕ => min t (i : ℝ), ?_, ?_⟩⟩ ?_
  · intro i j hij
    exact min_le_min le_rfl (Nat.cast_le.mpr hij)
  · intro i
    exact ⟨le_min ht0 (Nat.cast_nonneg i), (min_le_left _ _).trans ht1⟩
  · simp only [Finset.sum_range_one, zero_add, Nat.cast_one, Nat.cast_zero]
    rw [min_eq_left ht1, min_eq_right ht0, Path.extend_zero, hD.symm]

/-- **No shortcut near a point of an open set (deterministic).** Let `D` be a Euclidean length metric and `U` an open set
containing `0`. There is a Euclidean radius `ρ > 0` such that for all `x, y` in the closed Euclidean ball of radius `ρ`
about `0`, the ambient length metric equals the internal metric of `U`:
`ENNReal.ofReal (D x y) = internalMetric D U x y`. This is the locality needed to replace the ambient metric by the
internal metric on a small window (ChatGPT chat 195, step 6b). -/
theorem eq_internalMetric_on_small_ball {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {U : Set ℂ} (hU : IsOpen U) (h0 : (0 : ℂ) ∈ U) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ x ∈ closedBall (0 : ℂ) ρ, ∀ y ∈ closedBall (0 : ℂ) ρ,
      ENNReal.ofReal (D x y) = internalMetric D U x y := by
  -- the `D`-ball of radius `ε` about `0` lies in `U`
  obtain ⟨ε, hε, hεU⟩ := (hD.isOpen_iff U).1 hU 0 h0
  -- the `D`-ball of radius `ε / 4` about `0` is a Euclidean neighbourhood of `0`
  have hVopen : IsOpen {w : ℂ | D 0 w < ε / 4} := by
    rw [hD.isOpen_iff]
    intro z hz
    have hz' : D 0 z < ε / 4 := hz
    refine ⟨ε / 4 - D 0 z, by linarith, fun w hw => ?_⟩
    have hw' : D z w < ε / 4 - D 0 z := hw
    have htri := hD.triangle 0 z w
    show D 0 w < ε / 4
    linarith
  have h0V : (0 : ℂ) ∈ {w : ℂ | D 0 w < ε / 4} := by
    show D 0 0 < ε / 4
    rw [hD.self_eq_zero]
    linarith
  obtain ⟨ρ0, hρ0, hball⟩ := Metric.isOpen_iff.1 hVopen 0 h0V
  refine ⟨ρ0 / 2, by linarith, fun x hx y hy => ?_⟩
  have hsmall : ∀ w ∈ closedBall (0 : ℂ) (ρ0 / 2), D 0 w < ε / 4 := by
    intro w hw
    have hwb : w ∈ ball (0 : ℂ) ρ0 := by
      rw [mem_closedBall] at hw
      rw [mem_ball]
      linarith
    exact hball hwb
  have hx4 : D 0 x < ε / 4 := hsmall x hx
  have hy4 : D 0 y < ε / 4 := hsmall y hy
  have hx0 : D x 0 = D 0 x := hD.symm x 0
  have hxy_le : D x y < ε / 2 := by
    have htri := hD.triangle x 0 y
    linarith
  have hDxy_nonneg : 0 ≤ D x y := nonneg_of_isEuclideanLengthMetric hD x y
  -- lower bound: the internal metric on `U` is at least the ambient one (fewer paths in `U`)
  have hlow : ENNReal.ofReal (D x y) ≤ internalMetric D U x y := by
    rw [hD.ofReal_eq_internalMetric x y]
    unfold internalMetric
    refine le_iInf fun P => le_iInf fun _ => ?_
    exact iInf₂_le P (fun t => mem_univ (P t))
  -- upper bound: almost-geodesics for the ambient metric stay in `U`
  have hup : internalMetric D U x y ≤ ENNReal.ofReal (D x y) := by
    refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_
    obtain ⟨r, hr_pos, hr8, hrδ⟩ : ∃ r : ℝ, 0 < r ∧ r ≤ ε / 8 ∧ r ≤ (δ : ℝ) :=
      ⟨min (ε / 8) (δ : ℝ), lt_min (by linarith) (by exact_mod_cast hδ), min_le_left _ _, min_le_right _ _⟩
    have hlt : ENNReal.ofReal (D x y) < ENNReal.ofReal (D x y) + ENNReal.ofReal r :=
      ENNReal.lt_add_right ENNReal.ofReal_ne_top (ENNReal.ofReal_pos.2 hr_pos).ne'
    have hcomp : internalMetric D univ x y < ENNReal.ofReal (D x y) + ENNReal.ofReal r := by
      rw [← hD.ofReal_eq_internalMetric x y]
      exact hlt
    unfold internalMetric at hcomp
    obtain ⟨P, hP⟩ := iInf_lt_iff.1 hcomp
    obtain ⟨_, hPlen⟩ := iInf_lt_iff.1 hP
    have hPU : ∀ t, P t ∈ U := by
      intro t
      apply hεU
      have h1 := ofReal_dist_le_pathLength hD P (show (t : ℝ) ∈ Icc (0 : ℝ) 1 from t.2)
      have hext : P.extend (t : ℝ) = P t := P.extend_extends' t
      rw [hext] at h1
      have h2 : ENNReal.ofReal (D x (P t)) < ENNReal.ofReal (D x y + r) := by
        rw [ENNReal.ofReal_add hDxy_nonneg hr_pos.le]
        exact lt_of_le_of_lt h1 hPlen
      have h3 : D x (P t) < D x y + r :=
        (ENNReal.ofReal_lt_ofReal_iff (by linarith)).1 h2
      have htri := hD.triangle 0 x (P t)
      linarith
    have hint : internalMetric D U x y ≤ pathLength D P := by
      unfold internalMetric
      exact iInf₂_le P hPU
    have hrδ' : ENNReal.ofReal r ≤ (δ : ℝ≥0∞) := by
      rw [← ENNReal.ofReal_coe_nnreal]
      exact ENNReal.ofReal_le_ofReal hrδ
    calc internalMetric D U x y ≤ pathLength D P := hint
      _ ≤ ENNReal.ofReal (D x y) + ENNReal.ofReal r := hPlen.le
      _ ≤ ENNReal.ofReal (D x y) + (δ : ℝ≥0∞) := add_le_add le_rfl hrδ'
  exact le_antisymm hlow hup

/-- **Eventual ambient proportionality of two decoded length metrics.** Let `D ω`, `E ω` be Euclidean length metrics for
almost every `ω`. Suppose (`hInt`, the output of `ae_internalMetric_decoded_scalar`, NOT yet proved in the repository) that
their internal metrics on the open set `Uloc ∋ 0` are proportional on a fixed window `closedBall 0 r₀`. Then almost surely
there are `β > 0` and `n₀` with the ambient metrics proportional on `closedBall 0 (rad n)` for all `n ≥ n₀`, whenever
`rad n → 0`. The statement is only eventual: the no-shortcut radius of `eq_internalMetric_on_small_ball` is random
(ChatGPT chat 195, step 6c). -/
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
  obtain ⟨ρD, hρD, hD2⟩ := eq_internalMetric_on_small_ball hDω hUloc h0
  obtain ⟨ρE, hρE, hE2⟩ := eq_internalMetric_on_small_ball hEω hUloc h0
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
locality on the window `closedBall 0 (7 r n)` (`hMass`, the output of `FirstPassS11asLocal.ae_decoded_restrict_scalar` at
that scale) and the eventual metric proportionality above give, almost surely, the certificate equivalence at `(r n, 0)`
for all `n ≥ n₀`. The constants `a` and `β` are absorbed by `certificateEvent_of_restrict_scalar`. -/
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

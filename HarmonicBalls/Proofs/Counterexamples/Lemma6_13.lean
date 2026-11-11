import HarmonicBalls.Draft.Section2
import HarmonicBalls.Draft.Section3
import HarmonicBalls.Draft.Section5
import HarmonicBalls.Draft.Section6
import HarmonicBalls.Proofs.Potential.GreenBall

/-!
# Lemma 6.13 as printed is false (correction [C15])

Lemma 6.13 (lemma:low-mass-implies-small-odometer, lines 1710-1726) assumes only that the annulus
`𝔸_{ρ/2,ρ}(x₀)` does not contain the pole `z`. This allows `z = x₀`. The correction [C15] (used by
`LowMassSmallOdometerStmt`) assumes `closure B_ρ(x₀) ⊆ B_1 \ {z}`. This file certifies the counterexample to the
printed form.

## Structure

* `LowMassSmallOdometerPrintedStmt`: the printed statement, in the reading of `LowMassSmallOdometerStmt`
  (Draft/Section6.lean) with the printed hypothesis `z ∉ 𝔸_{ρ/2,ρ}(x₀)` in place of [C15]. It also assumes
  `closure B_ρ(x₀) ⊆ B_1`, which is implicit in the paper; this extra hypothesis only weakens the statement.
* `odometer_le_of_le_dist` (deterministic): `u^z_t(x) ≤ t (4π)⁻¹ δ⁻²` when `|x - z| ≥ δ`, from `v ≤ 0` and the explicit
  Green function of `B_1`.
* `exists_component_printed_fails` (deterministic, every measure `μ`): a *collar configuration*
  `Λ^z_t ⊆ B_R(z)` with `R ≤ min(ρ, d⁺_j, d⁺_{j+1})`, a point of `Λ^z_t` outside `closure B_{ρ/2}(z)`, and
  `μ(Λ^z_t ∩ 𝔸_{ρ/2,ρ}(z)) ≤ K` yields a component `Λ̃` of `Λ^z_t ∩ B_ρ(z)` for which the printed hypothesis holds
  and the printed conclusion fails for every factor `c < 1`. The two suprema are taken over the same set, on which
  the odometer is positive and bounded.
* `exists_collar_time` (deterministic, every locally finite `μ`): the collar configuration occurs at some `t > 0`,
  given the deterministic content of Lemmas 3.2-3.4, Propositions 5.2-5.3 and full support (input I1).
* `not_lowMassSmallOdometerPrintedStmt`: the Draft statements of Lemmas 3.2, 3.3, 3.4, 6.7, Propositions 5.2, 5.3,
  input I1, and the existence of a whole-plane GFF with its LQG measure refute the printed statement. The probabilistic
  input is only Lemma 6.7 (criterion (VG-iii) occurs with positive probability); the counterexample uses `z = x₀ = 0`,
  `ρ = 1/2`, `b = 1/2`, `j = 0` and the universal `C₃` of Lemma 6.7.
-/

universe u

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal Pointwise

namespace Lemma6_13Counterexample

open Section6

/-! ## The printed statement -/

/-- The hypothesis of eq:low-mass-small-odometer (line 1719): `μ(Λ̃ ∩ 𝔸_{3r,5r}(w)) ≤ K` for all `r > 0`,
`w ∈ B_1` with `𝔸_{r,7r}(w) ⊆ 𝔸_{ρ/2,d⁺_j}(x₀)`. -/
def PrintedMassHypothesis (μ : Measure ℂ) (ρ : ℝ) (x₀ : ℂ) (Λ : Set ℂ) (j : ℕ) (K : ℝ≥0∞) : Prop :=
  ∀ r : ℝ, 0 < r → ∀ w ∈ ball (0 : ℂ) 1,
    annulus w r (7 * r) ⊆ annulus x₀ (ρ / 2) (shellOuterRadius ρ j) →
    μ (Λ ∩ annulus w (3 * r) (5 * r)) ≤ K

/-- The conclusion of eq:low-mass-small-odometer (lines 1721-1722) with factor `c` (printed:
`c = b^{C' C₃ (N₀+j)}`). -/
def PrintedConclusion (μ : Measure ℂ) (z : ℂ) (t ρ : ℝ) (x₀ : ℂ) (Λ : Set ℂ) (j : ℕ) (c : ℝ) : Prop :=
  ⨆ x ∈ Λ ∩ annulus x₀ (ρ / 2) (shellOuterRadius ρ (j + 1)), odometerExt μ z t x ≤
    ENNReal.ofReal c * ⨆ x ∈ Λ ∩ annulus x₀ (ρ / 2) (shellOuterRadius ρ j), odometerExt μ z t x

/-- Lemma 6.13 as printed (lines 1710-1726), in the reading of `LowMassSmallOdometerStmt`: the hypothesis [C15]
`closure B_ρ(x₀) ⊆ B_1 \ {z}` is replaced by the printed "`𝔸_{ρ/2,ρ}(x₀)` not containing `z`", together with
`closure B_ρ(x₀) ⊆ B_1` (implicit in the paper; it only weakens the statement). -/
def LowMassSmallOdometerPrintedStmt : Prop :=
  ∃ C' : ℝ, 0 < C' ∧
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ βminus : ℝ, (2 + γ) ^ 2 / 2 < βminus →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1, ∀ t : ℝ, 0 < t →
  ∀ a ∈ Ioo (0 : ℝ) 1, ∀ b ∈ Ioo (0 : ℝ) 1, ∀ N₀ : ℕ, 200 ≤ N₀ → ∀ C₃ : ℝ, 0 < C₃ →
  ∀ ρ : ℝ, 0 < ρ → ∀ x₀ : ℂ, closedBall x₀ ρ ⊆ ball 0 1 → z ∉ annulus x₀ (ρ / 2) ρ →
  VeryGoodCriterionThree (μ ω) ρ x₀ N₀ a b C₃ →
  ∀ Λ ∈ connectedComponentsIn (cluster (μ ω) 1 z t ∩ ball x₀ ρ), ∀ j : ℕ,
    PrintedMassHypothesis (μ ω) ρ x₀ Λ j
      (ENNReal.ofReal a * annulusBallMassSize (μ ω) βminus ρ x₀ *
        ENNReal.ofReal (shellScale N₀ j ^ βminus)) →
    PrintedConclusion (μ ω) z t ρ x₀ Λ j (b ^ (C' * C₃ * ((N₀ : ℝ) + j)))

/-! ## The odometer is bounded away from the pole -/

/-- `u^z_t(x) ≤ t (4π)⁻¹ δ⁻²` for `x ∈ B_1`, `|x - z| ≥ δ > 0`: the least supersolution is `≤ 0` (the zero function
is a supersolution, line 599) and `G_{B_1}(z,x) ≤ (4π)⁻¹ |x - z|⁻²` (explicit Green function of the ball). -/
theorem odometer_le_of_le_dist (μ : Measure ℂ) {z x : ℂ} (hz : z ∈ ball (0 : ℂ) 1) (hx : x ∈ ball (0 : ℂ) 1)
    {t δ : ℝ} (ht : 0 ≤ t) (hδ : 0 < δ) (hd : δ ≤ dist x z) :
    odometer μ 1 z t x ≤ t * ((4 * Real.pi)⁻¹ / δ ^ 2) := by
  have hxz : x ≠ z := by
    rintro rfl
    simp at hd
    linarith
  have hv := leastSupersolution_nonpos (μ := μ) ht (ball_subset_closedBall hx) hxz
  have hG : greenFunction (ball 0 1) z x = greenBall 1 z x := greenFunction_ball hz hx (Ne.symm hxz)
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.1 hz
  have hx1 : ‖x‖ < 1 := mem_ball_zero_iff.1 hx
  have hle := greenBall_le (R := 1) one_pos (Ne.symm hxz) (norm_sub_conj_mul_pos one_pos hz1 hx1.le)
  have hzx : δ ≤ ‖z - x‖ := by rw [← dist_eq_norm, dist_comm]; exact hd
  have hnum : (1 - ‖z‖ ^ 2) * (1 - ‖x‖ ^ 2) ≤ 1 := by
    have h1 : 0 ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
    have h2 : 0 ≤ 1 - ‖x‖ ^ 2 := by nlinarith [norm_nonneg x]
    nlinarith [sq_nonneg ‖z‖, sq_nonneg ‖x‖]
  have hfrac : (1 ^ 2 - ‖z‖ ^ 2) * (1 ^ 2 - ‖x‖ ^ 2) / (1 ^ 2 * ‖z - x‖ ^ 2) ≤ 1 / δ ^ 2 := by
    rw [one_pow, one_mul]
    have hδ2 : 0 < δ ^ 2 := by positivity
    calc (1 - ‖z‖ ^ 2) * (1 - ‖x‖ ^ 2) / ‖z - x‖ ^ 2 ≤ 1 / ‖z - x‖ ^ 2 := by
          gcongr
      _ ≤ 1 / δ ^ 2 := by gcongr
  have hG' : greenFunction (ball 0 1) z x ≤ (4 * Real.pi)⁻¹ / δ ^ 2 := by
    rw [hG]
    calc greenBall 1 z x ≤ _ := hle
      _ ≤ (4 * Real.pi)⁻¹ * (1 / δ ^ 2) := by gcongr
      _ = (4 * Real.pi)⁻¹ / δ ^ 2 := by ring
  unfold odometer
  nlinarith [mul_le_mul_of_nonneg_left hG' ht]

/-! ## The deterministic core -/

/-- **The printed conclusion fails on a collar configuration.** Let `μ` be any measure, `z ∈ B_1`, `t ≥ 0`, and
suppose the cluster `Λ^z_t` lies in `B_R(z)` with `R ≤ min(ρ, d⁺_j, d⁺_{j+1})`, contains a point `y` with
`|y - z| > ρ/2`, and `μ(Λ^z_t ∩ 𝔸_{ρ/2,ρ}(z)) ≤ K`. Then the connected component `Λ̃` of `y` in `Λ^z_t ∩ B_ρ(z)`
satisfies the printed mass hypothesis with `K` and, with `x₀ = z`, violates the printed conclusion for every
factor `c < 1`: both suprema are taken over `Λ̃ \ closure B_{ρ/2}(z)`, on which the odometer is positive and
bounded. -/
theorem exists_component_printed_fails (μ : Measure ℂ) {z y : ℂ} (hz : z ∈ ball (0 : ℂ) 1) {t ρ R : ℝ}
    (ht : 0 ≤ t) (hρ : 0 < ρ) {j : ℕ} {K : ℝ≥0∞}
    (hRρ : R ≤ ρ) (hRj : R ≤ shellOuterRadius ρ j) (hRj1 : R ≤ shellOuterRadius ρ (j + 1))
    (hsub : cluster μ 1 z t ⊆ ball z R) (hy : y ∈ cluster μ 1 z t) (hyz : ρ / 2 < dist y z)
    (hmass : μ (cluster μ 1 z t ∩ annulus z (ρ / 2) ρ) ≤ K) :
    ∃ Λ ∈ connectedComponentsIn (cluster μ 1 z t ∩ ball z ρ),
      PrintedMassHypothesis μ ρ z Λ j K ∧ ∀ c : ℝ, c < 1 → ¬ PrintedConclusion μ z t ρ z Λ j c := by
  set F := cluster μ 1 z t ∩ ball z ρ with hF
  have hyF : y ∈ F := ⟨hy, mem_ball.2 ((mem_ball.1 (hsub hy)).trans_le hRρ)⟩
  set Λ := connectedComponentIn F y with hΛdef
  have hΛF : Λ ⊆ F := connectedComponentIn_subset F y
  have hyΛ : y ∈ Λ := mem_connectedComponentIn hyF
  -- every point of `Λ` lies in the cluster and in `B_R(z)`
  have hΛcl : ∀ x ∈ Λ, x ∈ cluster μ 1 z t ∧ dist x z < R := fun x hx =>
    ⟨(hΛF hx).1, mem_ball.1 (hsub (hΛF hx).1)⟩
  refine ⟨Λ, ⟨y, hyF, rfl⟩, ?_, ?_⟩
  · -- the printed mass hypothesis
    intro r hr w _ hann
    refine le_trans (measure_mono ?_) hmass
    rintro x ⟨hxΛ, hxA⟩
    obtain ⟨hxc, hxR⟩ := hΛcl x hxΛ
    have hxA' : x ∈ annulus w r (7 * r) := by
      simp only [annulus, Set.mem_sdiff, mem_ball, mem_closedBall, not_le] at hxA ⊢
      constructor <;> linarith [hxA.1, hxA.2]
    have hx2 := hann hxA'
    simp only [annulus, Set.mem_sdiff, mem_ball, mem_closedBall, not_le] at hx2
    exact ⟨hxc, by simp only [annulus, Set.mem_sdiff, mem_ball, mem_closedBall, not_le]; exact ⟨by linarith, hx2.2⟩⟩
  · -- the printed conclusion fails
    intro c hc hconcl
    -- the two index sets coincide
    have hS : ∀ s : ℝ, R ≤ s →
        Λ ∩ annulus z (ρ / 2) s = {x | x ∈ Λ ∧ ρ / 2 < dist x z} := by
      intro s hs
      ext x
      simp only [annulus, mem_inter_iff, Set.mem_sdiff, mem_ball, mem_closedBall, not_le, mem_ofPred_eq]
      constructor
      · rintro ⟨hxΛ, -, hx⟩
        exact ⟨hxΛ, hx⟩
      · rintro ⟨hxΛ, hx⟩
        exact ⟨hxΛ, (hΛcl x hxΛ).2.trans_le hs, hx⟩
    unfold PrintedConclusion at hconcl
    rw [hS _ hRj1, hS _ hRj] at hconcl
    set X := ⨆ x ∈ {x | x ∈ Λ ∧ ρ / 2 < dist x z}, odometerExt μ z t x with hX
    -- `X > 0`: the odometer is positive at `y`
    have hyz' : y ≠ z := by
      rintro rfl
      simp at hyz
      linarith
    have hpos : 0 < odometer μ 1 z t y := by
      rcases (mem_cluster_iff.1 hy).2 with h | h
      · exact absurd h hyz'
      · exact h
    have hX0 : X ≠ 0 := by
      have : odometerExt μ z t y ≤ X :=
        le_iSup₂ (f := fun x (_ : x ∈ {x | x ∈ Λ ∧ ρ / 2 < dist x z}) => odometerExt μ z t x) y ⟨hyΛ, hyz⟩
      refine (lt_of_lt_of_le ?_ this).ne'
      simp only [odometerExt, hyz', ↓reduceIte]
      exact ENNReal.ofReal_pos.2 hpos
    -- `X < ∞`: the odometer is bounded off `B_{ρ/2}(z)`
    have hXtop : X ≠ ⊤ := by
      refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := t * ((4 * Real.pi)⁻¹ / (ρ / 2) ^ 2))) (iSup₂_le fun x hx => ?_)
      obtain ⟨hxΛ, hxd⟩ := hx
      have hxz : x ≠ z := by
        rintro rfl
        simp at hxd
        linarith
      simp only [odometerExt, hxz, ↓reduceIte]
      exact ENNReal.ofReal_le_ofReal
        (odometer_le_of_le_dist μ hz (cluster_subset_ball (hΛcl x hxΛ).1) ht (half_pos hρ) hxd.le)
    have hc1 : ENNReal.ofReal c < 1 := ENNReal.ofReal_lt_one.2 hc
    have : ENNReal.ofReal c * X < X := by
      calc ENNReal.ofReal c * X < 1 * X := ENNReal.mul_lt_mul_left hX0 hXtop hc1
        _ = X := one_mul X
    exact absurd hconcl (not_le.2 this)

/-! ## Existence of a collar time -/

/-- **A collar configuration occurs.** Let `μ` be locally finite and `closure B_{ρ/2}(z) ⊆ B_1`. Suppose the
clusters `Λ_t = Λ^z_t` (`t > 0`) are open (Lemma 3.2), increasing (Lemma 3.3), satisfy `μ(Λ_t) ≤ t` with equality
when `closure Λ_t ⊆ B_1` (Lemma 3.4 with Proposition 5.3), shrink to `{z}` and are right-continuous
(Proposition 5.2), and that `μ` charges nonempty open sets (input I1). Then for all `K > 0` and `R > ρ/2` there is
`t > 0` with `Λ_t ⊆ B_R(z)`, a point of `Λ_t` outside `closure B_{ρ/2}(z)`, and `μ(Λ_t ∩ 𝔸_{ρ/2,ρ}(z)) ≤ K`.

Proof: `τ = sup {t > 0 : Λ_t ⊆ closure B_{ρ/2}(z)}` is positive (eq:contains-origin and compactness) and finite
(conservation of mass). `Λ_τ ⊆ closure B_{ρ/2}(z)`: otherwise `Λ_τ \ closure B_{ρ/2}(z)` is open, nonempty, and has
mass `≤ μ(Λ_τ) - μ(Λ_s) ≤ τ - s` for all `s < τ`. Right-continuity at `τ` gives `t > τ` with `Λ_t ⊆ B_R(z)`;
`Λ_t ⊄ closure B_{ρ/2}(z)` since `t > τ`; and `μ(Λ_t ∩ 𝔸_{ρ/2,ρ}(z)) ≤ μ(Λ_t \ Λ_s) ≤ t - s` for `s < τ`. -/
theorem exists_collar_time (μ : Measure ℂ) [IsLocallyFiniteMeasure μ] {z : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hzρ : closedBall z (ρ / 2) ⊆ ball 0 1)
    (hopen : ∀ t : ℝ, 0 < t → IsOpen (cluster μ 1 z t))
    (hmono : ∀ t₁ t₂ : ℝ, 0 < t₁ → t₁ ≤ t₂ → cluster μ 1 z t₁ ⊆ cluster μ 1 z t₂)
    (hmass_le : ∀ t : ℝ, 0 < t → μ (cluster μ 1 z t) ≤ ENNReal.ofReal t)
    (hmass_eq : ∀ t : ℝ, 0 < t → closure (cluster μ 1 z t) ⊆ ball 0 1 →
      μ (cluster μ 1 z t) = ENNReal.ofReal t)
    (hsupp : ∀ U : Set ℂ, IsOpen U → U.Nonempty → 0 < μ U)
    (horigin : ⋂ t ∈ Ioi (0 : ℝ), closure (cluster μ 1 z t) = {z})
    (hcont : ∀ t : ℝ, 0 < t → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε ∈ Ioo 0 ε₀, ∃ δ : ℝ, 0 < δ ∧ ∀ t' ∈ Icc t (t + δ),
      closure (cluster μ 1 z t') ⊆ cluster μ 1 z t + ball (0 : ℂ) ε)
    {K : ℝ≥0∞} (hK : 0 < K) {R : ℝ} (hR : ρ / 2 < R) :
    ∃ t : ℝ, 0 < t ∧ cluster μ 1 z t ⊆ ball z R ∧ (∃ y ∈ cluster μ 1 z t, ρ / 2 < dist y z) ∧
      μ (cluster μ 1 z t ∩ annulus z (ρ / 2) ρ) ≤ K := by
  set C : ℝ → Set ℂ := fun t => cluster μ 1 z t with hCdef
  set B := closedBall z (ρ / 2) with hBdef
  set T : Set ℝ := {t | 0 < t ∧ C t ⊆ B} with hTdef
  -- mass of the difference of two clusters
  have hdiff : ∀ s t : ℝ, 0 < s → s ≤ t → C s ⊆ B → μ (C t \ C s) ≤ ENNReal.ofReal (t - s) := by
    intro s t hs hst hsB
    have hsB' : closure (C s) ⊆ ball 0 1 := (isClosed_closedBall.closure_subset_iff.2 hsB).trans hzρ
    rw [measure_sdiff (hmono s t hs hst) (hopen s hs).measurableSet.nullMeasurableSet
      (by rw [hmass_eq s hs hsB']; exact ENNReal.ofReal_ne_top), hmass_eq s hs hsB',
      ENNReal.ofReal_sub _ hs.le]
    exact tsub_le_tsub_right (hmass_le t (hs.trans_le hst)) _
  -- `T` is nonempty: small clusters lie in `B_{ρ/2}(z)` (eq:contains-origin and compactness)
  have hTne : ∃ t₀, t₀ ∈ T := by
    have hcpt : IsCompact (closedBall (0 : ℂ) 1 \ ball z (ρ / 2)) :=
      (isCompact_closedBall 0 1).diff isOpen_ball
    have : Nonempty (Ioi (0 : ℝ)) := ⟨⟨1, mem_Ioi.2 one_pos⟩⟩
    obtain ⟨i, hi⟩ := hcpt.elim_directed_family_closed (fun i : Ioi (0 : ℝ) => closure (C i))
      (fun _ => isClosed_closure)
      (by
        rw [Set.disjoint_left]
        intro x hxs hx
        have hx' : x ∈ ⋂ t ∈ Ioi (0 : ℝ), closure (C t) :=
          mem_iInter₂.2 fun t ht => mem_iInter.1 hx ⟨t, ht⟩
        rw [horigin, mem_singleton_iff] at hx'
        exact hxs.2 (by rw [hx']; exact mem_ball_self (half_pos hρ)))
      (fun i j => ⟨⟨min (i : ℝ) j, mem_Ioi.2 (lt_min i.2 j.2)⟩,
        closure_mono (hmono _ _ (lt_min i.2 j.2) (min_le_left _ _)),
        closure_mono (hmono _ _ (lt_min i.2 j.2) (min_le_right _ _))⟩)
    refine ⟨i, i.2, fun x hx => ?_⟩
    have hx1 : x ∈ closedBall (0 : ℂ) 1 := ball_subset_closedBall (cluster_subset_ball hx)
    by_contra hxB
    exact Set.disjoint_left.1 hi ⟨hx1, fun h => hxB (ball_subset_closedBall h)⟩ (subset_closure hx)
  -- `T` is bounded above (conservation of mass)
  have hTbdd : BddAbove T := by
    refine ⟨(μ B).toReal, fun t ht => ?_⟩
    have hcl : closure (C t) ⊆ ball 0 1 := (isClosed_closedBall.closure_subset_iff.2 ht.2).trans hzρ
    have h1 : ENNReal.ofReal t ≤ μ B := (hmass_eq t ht.1 hcl).symm.le.trans (measure_mono ht.2)
    exact (ENNReal.ofReal_le_iff_le_toReal (isCompact_closedBall z (ρ / 2)).measure_lt_top.ne).1 h1
  obtain ⟨t₀, ht₀⟩ := hTne
  set τ := sSup T with hτdef
  have hτ0 : 0 < τ := ht₀.1.trans_le (le_csSup hTbdd ht₀)
  -- clusters before `τ` lie in `B`
  have hbefore : ∀ s, 0 < s → s < τ → C s ⊆ B := by
    intro s hs hsτ
    obtain ⟨a, ha, hsa⟩ := exists_lt_of_lt_csSup ⟨t₀, ht₀⟩ hsτ
    exact (hmono s a hs hsa.le).trans ha.2
  -- the cluster at `τ` lies in `B`
  have hτB : C τ ⊆ B := by
    intro y hy
    by_contra hyB
    have hU : 0 < μ (C τ \ B) := hsupp _ ((hopen τ hτ0).sdiff isClosed_closedBall) ⟨y, hy, hyB⟩
    have htend : Tendsto (fun s : ℝ => ENNReal.ofReal (τ - s)) (𝓝[<] τ) (𝓝 (ENNReal.ofReal (τ - τ))) :=
      ((ENNReal.continuous_ofReal.comp (continuous_const.sub continuous_id)).tendsto τ).mono_left
        nhdsWithin_le_nhds
    have hle : μ (C τ \ B) ≤ ENNReal.ofReal (τ - τ) :=
      ge_of_tendsto htend (Filter.eventually_of_mem (Ioo_mem_nhdsLT hτ0) fun s hs =>
        (measure_mono (sdiff_subset_sdiff_right (hbefore s hs.1 hs.2))).trans
          (hdiff s τ hs.1 hs.2.le (hbefore s hs.1 hs.2)))
    rw [sub_self, ENNReal.ofReal_zero] at hle
    exact hU.ne' (le_antisymm hle bot_le)
  -- right-continuity at `τ`
  obtain ⟨ε₀, hε₀, hcontτ⟩ := hcont τ hτ0
  set ε := min (ε₀ / 2) (R - ρ / 2) with hεdef
  have hε : 0 < ε := lt_min (half_pos hε₀) (sub_pos.2 hR)
  obtain ⟨δ, hδ, hδcont⟩ := hcontτ ε ⟨hε, (min_le_left _ _).trans_lt (half_lt_self hε₀)⟩
  obtain ⟨κ, -, hκpos, hκK⟩ := ENNReal.lt_iff_exists_real_btwn.1 hK
  have hκ : 0 < κ := ENNReal.ofReal_pos.1 hκpos
  set t := τ + min δ (κ / 2) with htdef
  set s := τ - min τ κ / 2 with hsdef
  have hmin1 : 0 < min δ (κ / 2) := lt_min hδ (half_pos hκ)
  have hmin2 : 0 < min τ κ := lt_min hτ0 hκ
  have hs0 : 0 < s := by have := min_le_left τ κ; linarith
  have hsτ : s < τ := by linarith
  have hτt : τ < t := by linarith
  have ht0 : 0 < t := hτ0.trans hτt
  have htsub : C t ⊆ ball z R := by
    refine subset_closure.trans ((hδcont t ⟨hτt.le, by linarith [min_le_left δ (κ / 2)]⟩).trans ?_)
    rintro x ⟨a, ha, b, hb, rfl⟩
    have ha' := mem_closedBall.1 (hτB ha)
    have hb' := mem_ball_zero_iff.1 hb
    rw [mem_ball]
    calc dist (a + b) z ≤ dist a z + ‖b‖ := by
          rw [dist_eq_norm, dist_eq_norm, add_sub_right_comm]; exact norm_add_le _ _
      _ < ρ / 2 + ε := by linarith
      _ ≤ R := by linarith [min_le_right (ε₀ / 2) (R - ρ / 2)]
  refine ⟨t, ht0, htsub, ?_, ?_⟩
  · -- `t > τ`, so the cluster leaves `B`
    by_contra hno
    push Not at hno
    have htT : t ∈ T := ⟨ht0, fun y hy => mem_closedBall.2 (hno y hy)⟩
    exact absurd (le_csSup hTbdd htT) (not_le.2 hτt)
  · calc μ (C t ∩ annulus z (ρ / 2) ρ) ≤ μ (C t \ C s) := by
          refine measure_mono fun x hx => ⟨hx.1, fun hxs => ?_⟩
          have h1 := mem_closedBall.1 (hbefore s hs0 hsτ hxs)
          have h2 := hx.2
          simp only [annulus, Set.mem_sdiff, mem_ball, mem_closedBall, not_le] at h2
          linarith [h2.2]
      _ ≤ ENNReal.ofReal (t - s) := hdiff s t hs0 (hsτ.trans hτt).le (hbefore s hs0 hsτ)
      _ ≤ ENNReal.ofReal κ :=
          ENNReal.ofReal_le_ofReal (by linarith [min_le_right δ (κ / 2), min_le_right τ κ])
      _ ≤ K := hκK.le

/-! ## The paper's own results refute the printed statement -/

/-- The printed hypothesis allows `z = x₀`: the annulus `𝔸_{ρ/2,ρ}(x₀)` never contains its centre. -/
theorem center_not_mem_annulus (x₀ : ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) : x₀ ∉ annulus x₀ (ρ / 2) ρ := fun h =>
  h.2 (mem_closedBall_self (by linarith))

/-- The corrected hypothesis [C15] excludes `z = x₀`. -/
theorem not_closedBall_subset_diff_center (x₀ : ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ¬ closedBall x₀ ρ ⊆ ball 0 1 \ {x₀} := fun h => (h (mem_closedBall_self hρ)).2 rfl

/-- `d⁺_0, d⁺_1 ≥ 3ρ/5` for `ρ ≥ 0` (shell decomposition, lines 1643-1665). -/
theorem three_fifths_le_shellOuterRadius {ρ : ℝ} (hρ : 0 ≤ ρ) :
    3 / 5 * ρ ≤ shellOuterRadius ρ 0 ∧ 3 / 5 * ρ ≤ shellOuterRadius ρ 1 := by
  have hw0 : shellWidth ρ 0 = ρ * (2 : ℝ)⁻¹ ^ 50 := by simp [shellWidth]
  have hw1 : 0 ≤ shellWidth ρ 1 := by unfold shellWidth; positivity
  have hq : ρ * (2 : ℝ)⁻¹ ^ 50 ≤ ρ * (1 / 1000) := mul_le_mul_of_nonneg_left (by norm_num) hρ
  have hq0 : 0 ≤ ρ * (2 : ℝ)⁻¹ ^ 50 := by positivity
  simp only [shellOuterRadius, shellRadius, hw0]
  constructor <;> linarith

/-- **Lemma 6.13 as printed is false**, granted the paper's own statements of Lemmas 3.2, 3.3, 3.4, 6.7,
Propositions 5.2, 5.3, input I1 (full support of `μ_h`), and one whole-plane GFF `h^ℂ` with the LQG measure `μ_h` of
`h = h^ℂ - α₀ log |·|` for some admissible `γ, α₀, β⁻`.

Take `z = x₀ = 0`, `ρ = 1/2`, `b = 1/2`, `j = 0`, the universal `C₃` of Lemma 6.7, and `a`, `N₀ ≥ max(N₁, 200)`
from Lemma 6.7 with `p = 1/2`. On the event `Ē_ρ(0)` (probability `≥ 1/2`), `M_ρ(0) > 0` by (VG-i), so
`K_0 = a M_ρ(0) ε_0^{β⁻} > 0`; `exists_collar_time` gives `t > 0` with `Λ^0_t ⊆ B_{3ρ/5}`, poking out of
`closure B_{ρ/2}` with `μ_h(Λ^0_t ∩ 𝔸_{ρ/2,ρ}) ≤ K_0`; `exists_component_printed_fails` gives a component `Λ̃`
violating the printed implication. Hence the printed statement would force `P[Ē_ρ(0)] = 0`. -/
theorem not_lowMassSmallOdometerPrintedStmt
    (h32 : ClusterOpenLaplacianStmt.{u}) (h33 : ClusterMonotoneStmt.{u})
    (h34 : ClusterConservationOfMassStmt.{u}) (h52 : ClusterContinuityStmt.{u})
    (h53 : ClusterBoundaryMeasureZeroStmt.{u}) (hI1 : LQGMeasureFullSupportStmt.{u})
    (h67 : VeryGoodAnnulusProbabilityStmt.{u})
    {γ α₀ βminus : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα₀ : α₀ < lqgQ γ) (hβ : (2 + γ) ^ 2 / 2 < βminus)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (hh : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ¬ LowMassSmallOdometerPrintedStmt.{u} := by
  rintro ⟨C', hC', hpr⟩
  obtain ⟨C₃, hC₃, h67'⟩ := h67
  obtain ⟨a, ha, C₁m, C₁p, C₂m, C₂p, hC₁m, -, -, -, N₁, -, hN⟩ :=
    h67' γ α₀ hγ0 hγ2 hα₀ βminus hβ (1 / 2) ⟨by norm_num, by norm_num⟩ (1 / 2) ⟨by norm_num, by norm_num⟩
  set N₀ := max N₁ 200 with hN₀def
  have hN₀ : 200 ≤ N₀ := le_max_right _ _
  set ρ : ℝ := 1 / 2 with hρdef
  have hρ : 0 < ρ := by norm_num [hρdef]
  have hdist : ρ / 100 ≤ infDist (0 : ℂ) (annulus 0 (ρ / 4) (2 * ρ)) := by
    have hne : (annulus (0 : ℂ) (ρ / 4) (2 * ρ)).Nonempty := ⟨(ρ : ℂ), by
      simp only [annulus, Set.mem_sdiff, mem_ball, mem_closedBall, dist_zero_right, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hρ, not_le]
      constructor <;> linarith⟩
    refine (le_infDist hne).2 fun y hy => ?_
    simp only [annulus, Set.mem_sdiff, mem_ball, mem_closedBall, not_le] at hy
    rw [dist_comm]
    linarith [hy.2]
  have hVG := hN N₀ (le_max_left _ _) Ω P hC hcirc μ hh hμ ρ hρ 0 hdist
  have hlimit : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage α₀ (hcirc ω)) (μ ω) := hμ
  have hae : ∀ᵐ ω ∂P, ¬ IsVeryGoodAnnulus (μ ω) βminus ρ 0 N₀ a (1 / 2) C₁m C₁p C₂m C₂p C₃ := by
    filter_upwards [hpr γ α₀ hγ0 hγ2 hα₀ βminus hβ Ω P hC hcirc μ hh hμ,
      h32 γ α₀ hγ0 hγ2 hα₀ Ω P hC hcirc μ hh hμ, h33 γ α₀ hγ0 hγ2 hα₀ Ω P hC hcirc μ hh hμ,
      h34 γ α₀ hγ0 hγ2 hα₀ Ω P hC hcirc μ hh hμ, h52 γ α₀ hγ0 hγ2 hα₀ Ω P hC hcirc μ hh hμ,
      h53 γ α₀ hγ0 hγ2 hα₀ Ω P hC hcirc μ hh hμ, hI1 γ α₀ hγ0 hγ2 hα₀ Ω P hC hcirc μ hh hμ, hlimit]
      with ω hp h2 h3 h4 h5 h6 h7 hl
    intro hVGω
    -- `filter_upwards` normalizes the binder `∀ w ∈ (ερ/100) ℤ² ∩ 𝔸`; restore criterion (VG-iii)
    have hVG3 : VeryGoodCriterionThree (μ ω) ρ 0 N₀ a (1 / 2) C₃ := fun n hn w hw =>
      hVGω.2.2 n hn w hw.2 hw.1
    have := hl.isLocallyFiniteMeasure
    have hz : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
    obtain ⟨horigin, hcont⟩ := h5 0 (mem_ball_self (by norm_num))
    -- `K_0 > 0`, since `M_ρ(0) > 0` by (VG-i)
    have hM : annulusBallMassSize (μ ω) βminus ρ 0 ≠ 0 := by
      intro hM0
      have h1 := hVGω.1.1
      rw [hM0, ENNReal.zero_div] at h1
      exact (ENNReal.ofReal_pos.2 hC₁m).ne' (le_antisymm h1 bot_le)
    have hK : 0 < ENNReal.ofReal a * annulusBallMassSize (μ ω) βminus ρ 0 *
        ENNReal.ofReal (shellScale N₀ 0 ^ βminus) :=
      ENNReal.mul_pos (ENNReal.mul_pos (ENNReal.ofReal_pos.2 ha.1).ne' hM).ne'
        (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos (dyadicScale_pos _) _)).ne'
    have hR := three_fifths_le_shellOuterRadius hρ.le
    obtain ⟨t, ht, hsub, ⟨y, hy, hyz⟩, hmassK⟩ := exists_collar_time (μ ω) (z := 0) hρ
      (closedBall_subset_ball (by norm_num [hρdef]))
      (fun t ht => (h2 t 1 ht one_pos 0 hz).1)
      (fun t₁ t₂ ht₁ hle => h3 t₁ t₂ 1 ht₁ hle one_pos 0 hz)
      (fun t ht => (h4 1 t one_pos ht 0 hz).1)
      (fun t ht hcl => (h4 1 t one_pos ht 0 hz).2.2 hcl (h6 0 hz t ht hcl))
      h7 horigin hcont hK (R := 3 / 5 * ρ) (by linarith)
    obtain ⟨Λ, hΛ, hmassΛ, hfail⟩ := exists_component_printed_fails (μ ω) hz ht.le hρ (j := 0)
      (by linarith) hR.1 hR.2 hsub hy hyz hmassK
    have hN₀pos : (0 : ℝ) < (N₀ : ℝ) + ((0 : ℕ) : ℝ) := by
      have : (0 : ℝ) < N₀ := by exact_mod_cast (show 0 < N₀ by omega)
      simpa using this
    refine hfail _ (Real.rpow_lt_one (by norm_num) (by norm_num) (mul_pos (mul_pos hC' hC₃) hN₀pos))
      (hp 0 hz t ht a ha (1 / 2) ⟨by norm_num, by norm_num⟩ N₀ hN₀ C₃ hC₃ ρ hρ 0
        (closedBall_subset_ball (by norm_num [hρdef])) (center_not_mem_annulus 0 hρ.le) hVG3 Λ hΛ 0
        hmassΛ)
  -- conclusion: `P[Ē_ρ(0)] = 0`, against `P[Ē_ρ(0)ᶜ] ≤ 1/2`
  have := hh.isProbabilityMeasure
  have h0 := ae_iff.1 hae
  have huniv : P univ ≤ P {ω | ¬ ¬ IsVeryGoodAnnulus (μ ω) βminus ρ 0 N₀ a (1 / 2) C₁m C₁p C₂m C₂p C₃} +
      P {ω | ¬ IsVeryGoodAnnulus (μ ω) βminus ρ 0 N₀ a (1 / 2) C₁m C₁p C₂m C₂p C₃} := by
    refine (measure_mono fun ω _ => ?_).trans (measure_union_le _ _)
    by_cases hω : IsVeryGoodAnnulus (μ ω) βminus ρ 0 N₀ a (1 / 2) C₁m C₁p C₂m C₂p C₃
    · exact Or.inl (not_not.2 hω)
    · exact Or.inr hω
  rw [measure_univ, h0, zero_add] at huniv
  have hlt : ENNReal.ofReal (1 - 1 / 2) < 1 := ENNReal.ofReal_lt_one.2 (by norm_num)
  exact absurd (huniv.trans hVG) (not_le.2 hlt)

end Lemma6_13Counterexample

end HarmonicBalls

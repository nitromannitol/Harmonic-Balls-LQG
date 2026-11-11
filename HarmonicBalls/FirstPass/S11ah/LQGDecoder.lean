import Mathlib
import HarmonicBalls.Defs.LQGMetric
import HarmonicBalls.Defs.Laplacian
import HarmonicBalls.FirstPass.S11ah.LengthScale
import HarmonicBalls.FirstPass.S11ah.Modified

/-!
# The local metric decoders are a.s. Euclidean length metrics

Lemma 11.13, Step 5. The unrooted local metric replacement (identity (18) of `LocalMetricReplacementStmt`,
`S11r/LocalMetricReplacement.lean`) says that, almost surely, the decoder `m(obs)` on the disc `B = ball c₂ r₂` is
`b · internalMetric(W_g, B)` on `B × B`, with a random constant `b > 0` and `W_g = weylScaling (𝔇 (hC ω)) ξ (-α log‖·‖)`.
This file proves that the decoder family is a.s. an `IsLengthMetricOn B` metric, from

* the almost-sure Euclidean length property of `𝔇 (hC ω)` (`IsLQGMetric`, axiom I of `SatisfiesLQGMetricAxioms`,
  applied to the field `hC ω + 0`);
* the cutoff transfer `CutoffInternalLengthStmt ξ α`, proved as `cutoffInternalLengthStmt` (CutoffLength.lean:163). The theorems below keep it as a parameter
  `hR1`, which FirstPassS11ar instantiates with that proof. It is a deterministic statement about every finite length
  metric `d` inducing the Euclidean topology.

The deterministic core is `isLengthMetricOn_decoderOn`: the decoder equals `b · internalReal G B` on `B × B` because the
two functions are continuous on `B × B`, agree off the diagonal (where the identity (18) and the length metric axioms
of `internalReal G B` give it), and the off-diagonal part is dense in `B × B`.
-/

open MeasureTheory ProbabilityTheory Metric Set Filter Topology HarmonicBalls
open scoped ENNReal

noncomputable section

namespace FirstPassS11ah

/-- The real-valued Weyl scaling of the metric `d` by the logarithmic weight `-α log‖·‖` (identity (18)). -/
def weylLogReal (d : ℂ → ℂ → ℝ) (ξ α : ℝ) : ℂ → ℂ → ℝ :=
  fun u v => (weylScaling d ξ (fun z => -α * Real.log ‖z‖) u v).toReal

/-- The internal distance of `D` on `U`, as a real number: `(x, y) ↦ (internalMetric D U x y).toReal`. -/
def internalReal (D : ℂ → ℂ → ℝ) (U : Set ℂ) : ℂ → ℂ → ℝ :=
  fun x y => (internalMetric D U x y).toReal

/-- **Cutoff transfer of the internal metric of the logarithmic Weyl scaling (proved as
`cutoffInternalLengthStmt`, CutoffLength.lean:163).**
The statement is quantified over every finite
length metric `d` on `ℂ` inducing the Euclidean topology (`IsEuclideanLengthMetric d`) and every open connected `V`
with compact closure and `0 ∉ closure V` (here `V = ball c₂ r₂`, `0 ∉ closedBall c₂ r₂`). The cutoff `f` of setup (17)
is a test function equal to `-α log‖·‖` near `closure V`. The conclusions are items 1-4: (1) `W_f` is finite and
`W_f.toReal` is a global Euclidean length metric; (2) `W_g` is finite on `V × V`; (3) `internalMetric` of `W_g` and of
`W_f` agree on `V × V`; (4) the common internal distances are finite, induce the Euclidean topology and form a length
metric on `V`. -/
def CutoffInternalLengthStmt (ξ α : ℝ) : Prop :=
  ∀ d : ℂ → ℂ → ℝ, IsEuclideanLengthMetric d → ∀ V : Set ℂ, IsOpen V → IsConnected V →
    IsCompact (closure V) → (0 : ℂ) ∉ closure V →
    (∃ f : ℂ → ℝ, IsTestFunction univ f ∧ (∀ᶠ x in 𝓝ˢ (closure V), f x = -α * Real.log ‖x‖) ∧
        (∀ u v, weylScaling d ξ f u v ≠ ⊤) ∧
        IsEuclideanLengthMetric (fun u v => (weylScaling d ξ f u v).toReal) ∧
        ∀ x ∈ V, ∀ y ∈ V, internalMetric (weylLogReal d ξ α) V x y =
          internalMetric (fun u v => (weylScaling d ξ f u v).toReal) V x y) ∧
    (∀ x ∈ V, ∀ y ∈ V, weylScaling d ξ (fun z => -α * Real.log ‖z‖) x y ≠ ⊤) ∧
    (∀ x ∈ V, ∀ y ∈ V, internalMetric (weylLogReal d ξ α) V x y ≠ ⊤) ∧
    IsLengthMetricOn V (internalReal (weylLogReal d ξ α) V)

/-! ### Congruence of internal metrics and length metrics -/

lemma curveLength_congr_of_eqOn {U : Set ℂ} {D E : ℂ → ℂ → ℝ} (hDE : ∀ x ∈ U, ∀ y ∈ U, D x y = E x y)
    {p : ℝ → ℂ} {a b : ℝ} (hp : ∀ t ∈ Icc a b, p t ∈ U) :
    curveLength D p a b = curveLength E p a b := by
  unfold curveLength
  refine iSup_congr fun q => Finset.sum_congr rfl fun i _ => ?_
  rw [hDE _ (hp _ (q.2.2.2 (i + 1))) _ (hp _ (q.2.2.2 i))]

lemma pathLength_congr_of_eqOn {U : Set ℂ} {D E : ℂ → ℂ → ℝ} (hDE : ∀ x ∈ U, ∀ y ∈ U, D x y = E x y)
    {x y : ℂ} (P : Path x y) (hP : ∀ t, P t ∈ U) : pathLength D P = pathLength E P := by
  unfold pathLength
  exact curveLength_congr_of_eqOn hDE (fun t ht => by
    have h := Path.extend_extends' P ⟨t, ht⟩
    dsimp only at h
    rw [h]
    exact hP _)

lemma internalMetric_congr_of_eqOn {U : Set ℂ} {D E : ℂ → ℂ → ℝ} (hDE : ∀ x ∈ U, ∀ y ∈ U, D x y = E x y)
    (z w : ℂ) : internalMetric D U z w = internalMetric E U z w := by
  unfold internalMetric
  congr 1
  funext P
  congr 1
  funext hP
  exact pathLength_congr_of_eqOn hDE P hP

/-- Two metrics that agree on `B × B` are both `IsLengthMetricOn B` or neither: the axioms only see `B × B`. -/
lemma IsLengthMetricOn.congr_of_eqOn {B : Set ℂ} {D E : ℂ → ℂ → ℝ} (hD : IsLengthMetricOn B D)
    (hDE : ∀ x ∈ B, ∀ y ∈ B, D x y = E x y) : IsLengthMetricOn B E where
  self_eq_zero z hz := by rw [← hDE z hz z hz]; exact hD.self_eq_zero z hz
  eq_of_eq_zero z hz w hw h := hD.eq_of_eq_zero z hz w hw (by rw [hDE z hz w hw]; exact h)
  symm z hz w hw := by rw [← hDE z hz w hw, ← hDE w hw z hz]; exact hD.symm z hz w hw
  triangle x hx y hy z hz := by
    rw [← hDE x hx y hy, ← hDE y hy z hz, ← hDE x hx z hz]
    exact hD.triangle x hx y hy z hz
  continuousOn := hD.continuousOn.congr fun q hq => (hDE q.1 hq.1 q.2 hq.2).symm
  isOpen_iff U hU := by
    rw [hD.isOpen_iff U hU]
    constructor
    · intro h z hz
      obtain ⟨ε, hε, h'⟩ := h z hz
      exact ⟨ε, hε, fun w hw hlt => h' w hw (by rw [hDE z (hU hz) w hw]; exact hlt)⟩
    · intro h z hz
      obtain ⟨ε, hε, h'⟩ := h z hz
      exact ⟨ε, hε, fun w hw hlt => h' w hw (by rw [← hDE z (hU hz) w hw]; exact hlt)⟩
  ofReal_eq_internalMetric z hz w hw := by
    rw [← hDE z hz w hw, hD.ofReal_eq_internalMetric z hz w hw, internalMetric_congr_of_eqOn hDE]

/-! ### The density of the off-diagonal part of `B × B` -/

lemma prod_subset_closure_offDiag {B : Set ℂ} (hBo : IsOpen B) :
    B ×ˢ B ⊆ closure ((B ×ˢ B) ∩ {p : ℂ × ℂ | p.1 ≠ p.2}) := by
  rintro ⟨z, w⟩ ⟨hz, hw⟩
  by_cases hzw : z = w
  · subst hzw
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hBo z hz
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨δ, hδ0, hδε, hδr⟩ : ∃ δ : ℝ, 0 < δ ∧ δ < ε ∧ δ < r :=
      ⟨min ε r / 2, half_pos (lt_min hε hr), by linarith [min_le_left ε r], by linarith [min_le_right ε r]⟩
    refine ⟨(z + (δ : ℂ), z), ⟨⟨hball ?_, hz⟩, fun h => ?_⟩, ?_⟩
    · rw [Metric.mem_ball, Complex.dist_eq, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hδ0]
      exact hδr
    · have h2 := congrArg Complex.re h
      simp at h2
      linarith
    · rw [Prod.dist_eq, dist_self, dist_comm, Complex.dist_eq, add_sub_cancel_left, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hδ0]
      exact max_lt hδε hε
  · exact subset_closure ⟨⟨hz, hw⟩, hzw⟩

/-! ### The deterministic core -/

open scoped Classical in
/-- The decoder of a family `m` of continuous functions on `B × B`: `m (x, y)` on `B × B`, `0` off `B × B`. -/
def decoderOn (B : Set ℂ) (m : ContinuousMap ↥(B ×ˢ B : Set (ℂ × ℂ)) ℝ) : ℂ → ℂ → ℝ :=
  fun x y => if h : (x, y) ∈ B ×ˢ B then m ⟨(x, y), h⟩ else 0

/-- **Deterministic core of Step 5.** Let `B` be open and let `G` have finite internal distances on `B` with
`internalReal G B` a length metric on `B` (R1 item 4). If the continuous decoder `m` satisfies identity (18),
`ofReal (m (x, y)) = ofReal b · internalMetric G B x y` on `B × B` with `b > 0`, then `decoderOn B m` is an
`IsLengthMetricOn B` metric. -/
theorem isLengthMetricOn_decoderOn {B : Set ℂ} (hBo : IsOpen B) {G : ℂ → ℂ → ℝ}
    (hfin : ∀ x ∈ B, ∀ y ∈ B, internalMetric G B x y ≠ ⊤)
    (hR : IsLengthMetricOn B (internalReal G B))
    (m : ContinuousMap ↥(B ×ˢ B : Set (ℂ × ℂ)) ℝ) {b : ℝ} (hb : 0 < b)
    (hid : ∀ p : ↥(B ×ˢ B : Set (ℂ × ℂ)),
      ENNReal.ofReal (m p) = ENNReal.ofReal b * internalMetric G B p.1.1 p.1.2) :
    IsLengthMetricOn B (decoderOn B m) := by
  have hFI : ∀ x ∈ B, ∀ y ∈ B, internalMetric G B x y = ENNReal.ofReal (internalReal G B x y) :=
    fun x hx y hy => (ENNReal.ofReal_toReal (hfin x hx y hy)).symm
  have hnonneg : ∀ x ∈ B, ∀ y ∈ B, 0 ≤ internalReal G B x y := fun x hx y hy => hR.nonneg hx hy
  have hpos : ∀ x ∈ B, ∀ y ∈ B, x ≠ y → 0 < b * internalReal G B x y := fun x hx y hy hxy =>
    mul_pos hb (lt_of_le_of_ne (hnonneg x hx y hy) fun h => hxy (hR.eq_of_eq_zero x hx y hy h.symm))
  -- identity (18) off the diagonal: the decoder is positive there, so the sign of `m` is determined
  have hEqOff : ∀ x ∈ B, ∀ y ∈ B, x ≠ y → decoderOn B m x y = b * internalReal G B x y := by
    intro x hx y hy hxy
    have hmem : (x, y) ∈ B ×ˢ B := ⟨hx, hy⟩
    have h1 : ENNReal.ofReal (m ⟨(x, y), hmem⟩) = ENNReal.ofReal b * internalMetric G B x y :=
      hid ⟨(x, y), hmem⟩
    have h2 : ENNReal.ofReal (m ⟨(x, y), hmem⟩) = ENNReal.ofReal (b * internalReal G B x y) := by
      rw [ENNReal.ofReal_mul hb.le, h1, hFI x hx y hy]
    have hD0 : 0 < m ⟨(x, y), hmem⟩ :=
      ENNReal.ofReal_pos.mp (by rw [h2]; exact ENNReal.ofReal_pos.mpr (hpos x hx y hy hxy))
    unfold decoderOn
    rw [dite_eq_left hmem]
    exact (ENNReal.ofReal_eq_ofReal_iff hD0.le (hpos x hx y hy hxy).le).mp h2
  have hcont : ContinuousOn (fun q : ℂ × ℂ => decoderOn B m q.1 q.2) (B ×ˢ B) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hfun : (B ×ˢ B).domRestrict (fun q : ℂ × ℂ => decoderOn B m q.1 q.2) = fun q => m q := by
      funext q
      exact dite_eq_left q.2
    rw [hfun]
    exact m.continuous
  have hbF : ContinuousOn (fun q : ℂ × ℂ => b * internalReal G B q.1 q.2) (B ×ˢ B) :=
    continuousOn_const.mul hR.continuousOn
  -- the two continuous functions agree on the off-diagonal part, which is dense in `B × B`
  have hEqOn : Set.EqOn (fun q : ℂ × ℂ => decoderOn B m q.1 q.2)
      (fun q : ℂ × ℂ => b * internalReal G B q.1 q.2) (B ×ˢ B) :=
    Set.EqOn.of_subset_closure (s := (B ×ˢ B) ∩ {p : ℂ × ℂ | p.1 ≠ p.2})
      (fun q hq => hEqOff q.1 hq.1.1 q.2 hq.1.2 hq.2) hcont hbF Set.inter_subset_left
      (prod_subset_closure_offDiag hBo)
  have hlen : IsLengthMetricOn B (fun x y => b * internalReal G B x y) := hR.const_mul hb
  refine hlen.congr_of_eqOn fun x hx y hy => ?_
  exact (hEqOn (show (x, y) ∈ B ×ˢ B from ⟨hx, hy⟩)).symm

/-! ### Almost-sure form -/

/-- The almost-sure Euclidean length property of the LQG metric of the field `hC ω` (axiom I of Fact 2.2, applied
to the whole-plane GFF with the zero continuous perturbation). -/
theorem ae_isEuclideanLengthMetric_of_lqg {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ : ℝ}
    {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hL : IsLQGMetric γ ξ 𝔇) (hG : IsWholePlaneGFF P hC hcirc) :
    ∀ᵐ ω ∂P, IsEuclideanLengthMetric (𝔇 (hC ω)) := by
  have h := (hL.satisfiesLQGMetricAxioms Ω P hC hcirc (fun _ => 0) hG (fun _ => continuous_zero)
    (fun _ => measurable_const)).ae_isEuclideanLengthMetric
  have hadd : ∀ ω, addFunPairing (hC ω) (fun _ => (0 : ℝ)) = hC ω := fun ω => by
    funext φ
    simp [addFunPairing]
  filter_upwards [h] with ω hω
  have hω' : IsEuclideanLengthMetric (𝔇 (addFunPairing (hC ω) (fun _ => (0 : ℝ)))) := hω
  rw [hadd ω] at hω'
  exact hω'

/-- **Step 5 decoders are a.s. length metrics on the disc.** Given the LQG metric `𝔇` (with `IsLQGMetric`), the whole-plane
GFF `hC`, the named input R1 `CutoffInternalLengthStmt`, and identity (18) for the continuous decoders `mω ω` on
`B × B` (with random constant `b(ω) > 0`), the decoder family is a.s. an `IsLengthMetricOn B` metric. -/
theorem ae_isLengthMetricOn_decoderOn {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α : ℝ}
    {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hL : IsLQGMetric γ ξ 𝔇) (hG : IsWholePlaneGFF P hC hcirc) (hR1 : CutoffInternalLengthStmt ξ α)
    {B : Set ℂ} (hBo : IsOpen B) (hBc : IsConnected B) (hBcpt : IsCompact (closure B))
    (h0 : (0 : ℂ) ∉ closure B)
    (mω : Ω → ContinuousMap ↥(B ×ˢ B : Set (ℂ × ℂ)) ℝ)
    (hid : ∀ᵐ ω ∂P, ∃ b : ℝ, 0 < b ∧ ∀ p : ↥(B ×ˢ B : Set (ℂ × ℂ)),
      ENNReal.ofReal (mω ω p) =
        ENNReal.ofReal b * internalMetric (weylLogReal (𝔇 (hC ω)) ξ α) B p.1.1 p.1.2) :
    ∀ᵐ ω ∂P, IsLengthMetricOn B (decoderOn B (mω ω)) := by
  filter_upwards [ae_isEuclideanLengthMetric_of_lqg hL hG, hid] with ω hω hidω
  obtain ⟨b, hb, hbid⟩ := hidω
  obtain ⟨_, _, hfin, hlen⟩ := hR1 (𝔇 (hC ω)) hω B hBo hBc hBcpt h0
  exact isLengthMetricOn_decoderOn hBo hfin hlen (mω ω) hb hbid

/-- Measurability in `ω` of the decoder at a pair of points of `B`, from measurability of `ω ↦ mω ω`. -/
theorem measurable_decoderOn {Ω : Type*} [MeasurableSpace Ω] {B : Set ℂ}
    {mω : Ω → ContinuousMap ↥(B ×ˢ B : Set (ℂ × ℂ)) ℝ} (hm : Measurable mω) :
    ∀ x ∈ B, ∀ y ∈ B, Measurable fun ω => decoderOn B (mω ω) x y := by
  intro x hx y hy
  have hmem : (x, y) ∈ B ×ˢ B := ⟨hx, hy⟩
  have hfun : (fun ω => decoderOn B (mω ω) x y) = fun ω => mω ω ⟨(x, y), hmem⟩ :=
    funext fun ω => dite_eq_left hmem
  rw [hfun]
  exact (ContinuousMap.measurable_eval (⟨(x, y), hmem⟩ : ↥(B ×ˢ B : Set (ℂ × ℂ)))).comp hm

/-! ### Step 5 for the local decoders -/

/-- **Step 5 for the unrooted local decoders (a.s. form).** The decoders `decoderOn (ball c R) (mω ·)` of the local
metric replacement (identity (18)) are almost surely `IsLengthMetricOn (ball c R)` metrics (`ae_isLengthMetricOn_decoderOn`).
Hence the modification of `localLengthModification_of_ae` exists, and its failure sets (K) agree
`P`-a.s. with those of the decoders (`exists_modified_failureSet_ae`). -/
theorem exists_modified_failureSet_lqg {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α : ℝ}
    {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hL : IsLQGMetric γ ξ 𝔇) (hG : IsWholePlaneGFF P hC hcirc) (hR1 : CutoffInternalLengthStmt ξ α)
    {c : ℂ} {R : ℝ} (hR : 0 < R) (h0ball : (0 : ℂ) ∉ closedBall c R)
    (κ : Kernel Ω ℂ) [IsSFiniteKernel κ]
    (mω : Ω → ContinuousMap ↥(ball c R ×ˢ ball c R : Set (ℂ × ℂ)) ℝ) (hm : Measurable mω)
    (hid : ∀ᵐ ω ∂P, ∃ b : ℝ, 0 < b ∧ ∀ p : ↥(ball c R ×ˢ ball c R : Set (ℂ × ℂ)),
      ENNReal.ofReal (mω ω p) =
        ENNReal.ofReal b * internalMetric (weylLogReal (𝔇 (hC ω)) ξ α) (ball c R) p.1.1 p.1.2)
    {Ostar U V W T Q' Q : Set ℂ} (hOstar : IsOpen Ostar) (h0 : (0 : ℂ) ∈ Ostar)
    (hsph : sphere (0 : ℂ) 5 ⊆ Ostar) (hU : MeasurableSet U) {η M : ℝ} (hη : 0 < η)
    {A : Set ℂ} (hA : MeasurableSet A) (q : ℝ) :
    ∃ D' : Ω → ℂ → ℂ → ℝ,
      (∀ x ∈ ball c R, ∀ y ∈ ball c R, Measurable fun ω => D' ω x y) ∧
      (∀ ω, IsLengthMetricOn (ball c R) (D' ω)) ∧
      MeasurableSet (failureSetLoc c R κ D' Ostar U V W T Q' Q η M A q) ∧
      ∀ᵐ ω ∂P, ∀ z : ℂ,
        ((z, ω) ∈ failureSetLoc c R κ (fun ω => decoderOn (ball c R) (mω ω)) Ostar U V W T Q' Q η M A q ↔
          (z, ω) ∈ failureSetLoc c R κ D' Ostar U V W T Q' Q η M A q) := by
  have hBc : IsConnected (ball c R) := (convex_ball c R).isConnected (Metric.nonempty_ball.mpr hR)
  have hBcpt : IsCompact (closure (ball c R)) :=
    (isCompact_closedBall c R).of_isClosed_subset isClosed_closure closure_ball_subset_closedBall
  have h0c : (0 : ℂ) ∉ closure (ball c R) := fun h => h0ball (closure_ball_subset_closedBall h)
  have hLen : ∀ᵐ ω ∂P, IsLengthMetricOn (ball c R) (decoderOn (ball c R) (mω ω)) :=
    ae_isLengthMetricOn_decoderOn hL hG hR1 isOpen_ball hBc hBcpt h0c mω hid
  exact exists_modified_failureSet_ae hR κ P (fun ω => decoderOn (ball c R) (mω ω))
    (measurable_decoderOn hm) hLen hOstar h0 hsph hU hη hA q

end FirstPassS11ah

end

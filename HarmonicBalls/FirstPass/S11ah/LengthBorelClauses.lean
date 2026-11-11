import Mathlib
import HarmonicBalls.FirstPass.S11ah.LengthBorel
import HarmonicBalls.FirstPass.S11ah.LengthTransport
import HarmonicBalls.FirstPass.S11ah.LQGDecoder

/-!
# Borel code of the clauses of `IsLengthMetricOn B (decoderOn B d)`

Let `B = ball c r` and let `d` be a continuous function on the window
`B ×ˢ B`. The clauses of `IsLengthMetricOn B (decoderOn B d)` are treated as follows.

* `self_eq_zero`, `symm`, `triangle`: countable dense reduction (`LengthBorel.lean`, generic
  `measurableSet_forall_nonpos_of_dense`), applied to the window points involved.
* `continuousOn`: automatic for a continuous `d` (`continuousOn_decoderOn`).
* `isOpen_iff` and `eq_of_eq_zero`: equivalent to the pointwise condition `V2`
  (`D z w ≥ ε` for `w ∈ B`, `δ ≤ dist w z`, with `ε` depending on `z` and `δ`), see `isOpen_iff_of_V2`.
  `V2` is equivalent to a countable Borel code `codeSet` through the compact exhaustion
  `expK` of `B`: the pointwise `ε` is made uniform on each compact `expK i` (`uniform_on_compact`,
  a finite-subcover argument using the triangle inequality and continuity of `D` on `B × B`).
* `ofReal_eq_internalMetric`: NOT reduced here. It enters as the explicit hypothesis `hL7` of
  `measurableSet_isLengthMetricOn_decoderOn_of_internal`, with `internalSet B` the set where it holds.
  The chain code does not by itself give this clause.
-/

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

noncomputable section

namespace HarmonicBalls.FirstPassS11ahLengthBorelClauses

open FirstPassS11ah HarmonicBalls HarmonicBalls.FirstPassS11ahLengthBorel

/-- The window `B ×ˢ B` as a type: the domain of a decoder. -/
abbrev Win (B : Set ℂ) : Type := ↥(B ×ˢ B : Set (ℂ × ℂ))

/-- The triple window `B ×ˢ (B ×ˢ B)`: the triangle inequality is tested on `(x, u, z)`. -/
abbrev Tri (B : Set ℂ) : Type := ↥(B ×ˢ (B ×ˢ B) : Set (ℂ × ℂ × ℂ))

section Basic

variable {B : Set ℂ}

lemma decoderOn_eq_eval (d : C(Win B, ℝ)) (p : Win B) :
    decoderOn B d p.1.1 p.1.2 = d p := by
  unfold decoderOn
  split_ifs with h
  · rfl
  · exact absurd p.2 h

lemma decoderOn_of_eq (d : C(Win B, ℝ)) (p : Win B) {x y : ℂ} (hx : p.1.1 = x) (hy : p.1.2 = y) :
    decoderOn B d x y = d p := by
  subst hx hy
  exact decoderOn_eq_eval d p

lemma decoderOn_apply_of_mem (d : C(Win B, ℝ)) {x y : ℂ} (hx : x ∈ B) (hy : y ∈ B) :
    decoderOn B d x y = d ⟨(x, y), mk_mem_prod hx hy⟩ :=
  decoderOn_of_eq d _ rfl rfl

lemma continuousOn_decoderOn (d : C(Win B, ℝ)) :
    ContinuousOn (fun q : ℂ × ℂ => decoderOn B d q.1 q.2) (B ×ˢ B) := by
  rw [continuousOn_iff_continuous_domRestrict]
  convert d.continuous using 1
  funext p
  exact decoderOn_eq_eval d p

/-- The diagonal point `(z, z)` of the window. -/
def diagW (B : Set ℂ) (z : ↥B) : Win B := ⟨(z.1, z.1), mk_mem_prod z.2 z.2⟩

/-- The swap `(x, y) ↦ (y, x)` of the window. -/
def swapW (B : Set ℂ) (p : Win B) : Win B :=
  ⟨(p.1.2, p.1.1), mk_mem_prod (mem_prod.1 p.2).2 (mem_prod.1 p.2).1⟩

lemma swapW_swapW (p : Win B) : swapW B (swapW B p) = p :=
  Subtype.ext (Prod.ext rfl rfl)

lemma continuous_diagW : Continuous (diagW B) :=
  Continuous.subtype_mk (continuous_subtype_val.prodMk continuous_subtype_val)
    (fun z => (diagW B z).2)

lemma continuous_swapW : Continuous (swapW B) :=
  Continuous.subtype_mk ((continuous_snd.comp continuous_subtype_val).prodMk
    (continuous_fst.comp continuous_subtype_val)) (fun p => (swapW B p).2)

/-- The window points `(x, z)`, `(x, u)`, `(u, z)` of a triple `y = (x, u, z)`. -/
def triXZ (B : Set ℂ) (y : Tri B) : Win B :=
  ⟨(y.1.1, y.1.2.2), mk_mem_prod (mem_prod.1 y.2).1 (mem_prod.1 (mem_prod.1 y.2).2).2⟩

def triXU (B : Set ℂ) (y : Tri B) : Win B :=
  ⟨(y.1.1, y.1.2.1), mk_mem_prod (mem_prod.1 y.2).1 (mem_prod.1 (mem_prod.1 y.2).2).1⟩

def triUZ (B : Set ℂ) (y : Tri B) : Win B :=
  ⟨(y.1.2.1, y.1.2.2), mk_mem_prod (mem_prod.1 (mem_prod.1 y.2).2).1 (mem_prod.1 (mem_prod.1 y.2).2).2⟩

lemma continuous_triXZ : Continuous (triXZ B) :=
  Continuous.subtype_mk ((continuous_fst.comp continuous_subtype_val).prodMk
    ((continuous_snd.comp continuous_snd).comp continuous_subtype_val)) (fun y => (triXZ B y).2)

lemma continuous_triXU : Continuous (triXU B) :=
  Continuous.subtype_mk ((continuous_fst.comp continuous_subtype_val).prodMk
    ((continuous_fst.comp continuous_snd).comp continuous_subtype_val)) (fun y => (triXU B y).2)

lemma continuous_triUZ : Continuous (triUZ B) :=
  Continuous.subtype_mk (((continuous_fst.comp continuous_snd).comp continuous_subtype_val).prodMk
    ((continuous_snd.comp continuous_snd).comp continuous_subtype_val)) (fun y => (triUZ B y).2)

lemma decoderOn_diag (d : C(Win B, ℝ)) (z : ↥B) : decoderOn B d z.1 z.1 = d (diagW B z) :=
  decoderOn_of_eq d _ rfl rfl

lemma decoderOn_swap (d : C(Win B, ℝ)) (p : Win B) : decoderOn B d p.1.2 p.1.1 = d (swapW B p) :=
  decoderOn_of_eq d _ rfl rfl

lemma decoderOn_triXZ (d : C(Win B, ℝ)) (y : Tri B) :
    decoderOn B d y.1.1 y.1.2.2 = d (triXZ B y) :=
  decoderOn_of_eq d _ rfl rfl

lemma decoderOn_triXU (d : C(Win B, ℝ)) (y : Tri B) :
    decoderOn B d y.1.1 y.1.2.1 = d (triXU B y) :=
  decoderOn_of_eq d _ rfl rfl

lemma decoderOn_triUZ (d : C(Win B, ℝ)) (y : Tri B) :
    decoderOn B d y.1.2.1 y.1.2.2 = d (triUZ B y) :=
  decoderOn_of_eq d _ rfl rfl

/-- Countable reduction of a continuous pointwise inequality, for an arbitrary measurable parameter space
`α`. Same proof as `LengthBorel.measurableSet_forall_nonpos_of_dense` (kept local so that this module does not
depend on a rebuilt `LengthBorel` olean). -/
lemma measurableSet_forall_nonpos_gen {α Y : Type*} [MeasurableSpace α] [TopologicalSpace Y] {Q : Set Y}
    (hQc : Q.Countable) (hQd : Dense Q) {Φ : α → Y → ℝ} (hΦc : ∀ d, Continuous (Φ d))
    (hΦm : ∀ q ∈ Q, Measurable fun d : α => Φ d q) :
    MeasurableSet {d : α | ∀ p, Φ d p ≤ 0} := by
  have hEq : {d : α | ∀ p, Φ d p ≤ 0} = ⋂ q ∈ Q, {d : α | Φ d q ≤ 0} := by
    ext d
    simp only [mem_ofPred_eq, mem_iInter]
    constructor
    · intro h q _
      exact h q
    · intro h p
      have hsub : Q ⊆ {p | Φ d p ≤ 0} := fun q hq => h q hq
      have hcl : closure Q ⊆ {p | Φ d p ≤ 0} :=
        closure_minimal hsub (isClosed_le (hΦc d) continuous_const)
      have hp : p ∈ closure Q := by
        rw [hQd.closure_eq]
        exact mem_univ p
      exact hcl hp
  rw [hEq]
  exact MeasurableSet.biInter hQc fun q hq => measurableSet_le (hΦm q hq) measurable_const

/-- Countable reduction on a separable parameter space, for the window functions. -/
lemma measurableSet_forall_le_zero_of {Y : Type*} [TopologicalSpace Y] [TopologicalSpace.SeparableSpace Y]
    {Φ : C(Win B, ℝ) → Y → ℝ} (hΦc : ∀ d, Continuous (Φ d))
    (hΦm : ∀ y, Measurable fun d : C(Win B, ℝ) => Φ d y) :
    MeasurableSet {d : C(Win B, ℝ) | ∀ y, Φ d y ≤ 0} := by
  obtain ⟨Q, hQc, hQd⟩ := TopologicalSpace.exists_countable_dense Y
  exact measurableSet_forall_nonpos_gen hQc hQd hΦc (fun q _ => hΦm q)

/-- Clause `self_eq_zero`: `D z z = 0` for `z ∈ B`. -/
lemma measurableSet_diag_zero (B : Set ℂ) :
    MeasurableSet {d : C(Win B, ℝ) | ∀ z ∈ B, decoderOn B d z z = 0} := by
  have h1 : MeasurableSet {d : C(Win B, ℝ) | ∀ z : ↥B, d (diagW B z) ≤ 0} :=
    measurableSet_forall_le_zero_of (Φ := fun d z => d (diagW B z))
      (fun d => d.continuous.comp continuous_diagW) (fun z => measurable_eval_real (diagW B z))
  have h2 : MeasurableSet {d : C(Win B, ℝ) | ∀ z : ↥B, -d (diagW B z) ≤ 0} :=
    measurableSet_forall_le_zero_of (Φ := fun d z => -d (diagW B z))
      (fun d => (d.continuous.comp continuous_diagW).neg)
      (fun z => (measurable_eval_real (diagW B z)).neg)
  have hEq : {d : C(Win B, ℝ) | ∀ z ∈ B, decoderOn B d z z = 0} =
      {d : C(Win B, ℝ) | ∀ z : ↥B, d (diagW B z) ≤ 0} ∩
        {d : C(Win B, ℝ) | ∀ z : ↥B, -d (diagW B z) ≤ 0} := by
    ext d
    simp only [mem_ofPred_eq, mem_inter_iff]
    constructor
    · intro h
      refine ⟨fun z => ?_, fun z => ?_⟩
      · rw [← decoderOn_diag d z, h z.1 z.2]
      · rw [← decoderOn_diag d z, h z.1 z.2, neg_zero]
    · rintro ⟨h1, h2⟩ z hz
      have key : decoderOn B d z z = d (diagW B ⟨z, hz⟩) := decoderOn_diag d ⟨z, hz⟩
      rw [key]
      exact le_antisymm (h1 ⟨z, hz⟩) (by linarith [h2 ⟨z, hz⟩])
  rw [hEq]
  exact h1.inter h2

/-- Clause `symm`: `D z w = D w z` for `z, w ∈ B`. -/
lemma measurableSet_symm (B : Set ℂ) :
    MeasurableSet {d : C(Win B, ℝ) | ∀ z ∈ B, ∀ w ∈ B, decoderOn B d z w = decoderOn B d w z} := by
  have h1 : MeasurableSet {d : C(Win B, ℝ) | ∀ p : Win B, d p - d (swapW B p) ≤ 0} :=
    measurableSet_forall_le_zero_of (Φ := fun d p => d p - d (swapW B p))
      (fun d => d.continuous.sub (d.continuous.comp continuous_swapW))
      (fun p => (measurable_eval_real p).sub (measurable_eval_real (swapW B p)))
  have hEq : {d : C(Win B, ℝ) | ∀ z ∈ B, ∀ w ∈ B, decoderOn B d z w = decoderOn B d w z} =
      {d : C(Win B, ℝ) | ∀ p : Win B, d p - d (swapW B p) ≤ 0} := by
    ext d
    simp only [mem_ofPred_eq]
    constructor
    · intro h p
      have hp := h p.1.1 (mem_prod.1 p.2).1 p.1.2 (mem_prod.1 p.2).2
      rw [decoderOn_eq_eval d p, decoderOn_swap d p] at hp
      linarith
    · intro h z hz w hw
      set p : Win B := ⟨(z, w), mk_mem_prod hz hw⟩ with hpdef
      have h1 := h p
      have h2 := h (swapW B p)
      rw [swapW_swapW] at h2
      have e1 : decoderOn B d z w = d p := decoderOn_of_eq d p rfl rfl
      have e2 : decoderOn B d w z = d (swapW B p) := decoderOn_of_eq d (swapW B p) rfl rfl
      rw [e1, e2]
      linarith
  rw [hEq]
  exact h1

/-- Clause `triangle`: `D x z ≤ D x y + D y z` for `x, y, z ∈ B`. -/
lemma measurableSet_triangle (B : Set ℂ) :
    MeasurableSet {d : C(Win B, ℝ) |
      ∀ x ∈ B, ∀ y ∈ B, ∀ z ∈ B, decoderOn B d x z ≤ decoderOn B d x y + decoderOn B d y z} := by
  have h1 : MeasurableSet {d : C(Win B, ℝ) |
      ∀ y : Tri B, d (triXZ B y) - d (triXU B y) - d (triUZ B y) ≤ 0} :=
    measurableSet_forall_le_zero_of
      (Φ := fun d y => d (triXZ B y) - d (triXU B y) - d (triUZ B y))
      (fun d => ((d.continuous.comp continuous_triXZ).sub (d.continuous.comp continuous_triXU)).sub
        (d.continuous.comp continuous_triUZ))
      (fun y => ((measurable_eval_real (triXZ B y)).sub (measurable_eval_real (triXU B y))).sub
        (measurable_eval_real (triUZ B y)))
  have hEq : {d : C(Win B, ℝ) |
      ∀ x ∈ B, ∀ y ∈ B, ∀ z ∈ B, decoderOn B d x z ≤ decoderOn B d x y + decoderOn B d y z} =
      {d : C(Win B, ℝ) | ∀ y : Tri B, d (triXZ B y) - d (triXU B y) - d (triUZ B y) ≤ 0} := by
    ext d
    simp only [mem_ofPred_eq]
    constructor
    · intro h y
      have hy := h y.1.1 (mem_prod.1 y.2).1 y.1.2.1 (mem_prod.1 (mem_prod.1 y.2).2).1
        y.1.2.2 (mem_prod.1 (mem_prod.1 y.2).2).2
      rw [decoderOn_triXZ d y, decoderOn_triXU d y, decoderOn_triUZ d y] at hy
      linarith
    · intro h x hx u hu z hz
      have hxuz : (x, (u, z)) ∈ B ×ˢ (B ×ˢ B) := mk_mem_prod hx (mk_mem_prod hu hz)
      have hy := h ⟨(x, (u, z)), hxuz⟩
      have e1 : decoderOn B d x z = d (triXZ B ⟨(x, (u, z)), hxuz⟩) :=
        decoderOn_of_eq d _ rfl rfl
      have e2 : decoderOn B d x u = d (triXU B ⟨(x, (u, z)), hxuz⟩) :=
        decoderOn_of_eq d _ rfl rfl
      have e3 : decoderOn B d u z = d (triUZ B ⟨(x, (u, z)), hxuz⟩) :=
        decoderOn_of_eq d _ rfl rfl
      rw [e1, e2, e3]
      linarith
  rw [hEq]
  exact h1

/-- The clauses `self_eq_zero`, `symm`, `triangle` of `IsLengthMetricOn B (decoderOn B d)`. -/
def clausesSet (B : Set ℂ) : Set C(Win B, ℝ) :=
  {d | (∀ z ∈ B, decoderOn B d z z = 0) ∧
    (∀ z ∈ B, ∀ w ∈ B, decoderOn B d z w = decoderOn B d w z) ∧
    (∀ x ∈ B, ∀ y ∈ B, ∀ z ∈ B, decoderOn B d x z ≤ decoderOn B d x y + decoderOn B d y z)}

lemma measurableSet_clausesSet (B : Set ℂ) : MeasurableSet (clausesSet B) := by
  unfold clausesSet
  rw [ofPred_and, ofPred_and]
  exact (measurableSet_diag_zero B).inter ((measurableSet_symm B).inter (measurableSet_triangle B))

end Basic

/-! ### The compact exhaustion and the countable code of the pointwise `V2` condition -/

/-- The pointwise condition behind `isOpen_iff`: for `z ∈ B`, `δ > 0` there is `ε > 0` with
`D z w ≥ ε` whenever `w ∈ B` and `δ ≤ dist w z`. -/
def V2 (B : Set ℂ) (D : ℂ → ℂ → ℝ) : Prop :=
  ∀ z ∈ B, ∀ δ > 0, ∃ ε > 0, ∀ w ∈ B, δ ≤ dist w z → ε ≤ D z w

/-- Clause `isOpen_iff` is equivalent to `V2` (for continuous `D` on `B × B` with `D z z = 0`). -/
lemma isOpen_iff_of_V2 {B : Set ℂ} (hB : IsOpen B) {D : ℂ → ℂ → ℝ}
    (hcont : ContinuousOn (fun q : ℂ × ℂ => D q.1 q.2) (B ×ˢ B)) (hself : ∀ z ∈ B, D z z = 0) :
    (∀ U ⊆ B, (IsOpen U ↔ ∀ z ∈ U, ∃ ε > 0, ∀ w ∈ B, D z w < ε → w ∈ U)) ↔ V2 B D := by
  constructor
  · intro H z hz δ hδ
    obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hB z hz
    have hUB : ball z (min δ ρ) ⊆ B := (ball_subset_ball (min_le_right _ _)).trans hball
    obtain ⟨ε, hε, hw⟩ := (H (ball z (min δ ρ)) hUB).1 isOpen_ball z (mem_ball_self (lt_min hδ hρ))
    refine ⟨ε, hε, fun w hwB hδw => ?_⟩
    by_contra hlt

    have hwU : w ∈ ball z (min δ ρ) := hw w hwB (not_le.1 hlt)
    rw [mem_ball] at hwU
    have := min_le_left δ ρ
    linarith
  · intro hV U hU
    constructor
    · intro hUo z hz
      obtain ⟨δ, hδ, hsub⟩ := Metric.isOpen_iff.1 hUo z hz
      obtain ⟨ε, hε, hV'⟩ := hV z (hU hz) δ hδ
      refine ⟨ε, hε, fun w hwB hlt => hsub ?_⟩
      rw [mem_ball]
      by_contra hge

      have := hV' w hwB (not_lt.1 hge)
      linarith
    · intro hex
      refine Metric.isOpen_iff.2 fun z hz => ?_
      obtain ⟨ε, hε, hEx⟩ := hex z hz
      have hzB : z ∈ B := hU hz
      obtain ⟨ρ, hρ, hballB⟩ := Metric.isOpen_iff.1 hB z hzB
      have hc : ContinuousWithinAt (fun w => D z w) B z :=
        (hcont.comp (continuousOn_const.prodMk continuousOn_id)
          (fun w hw => mk_mem_prod hzB hw)) z hzB
      have hcA : ContinuousAt (fun w => D z w) z := hc.continuousAt (hB.mem_nhds hzB)
      obtain ⟨δ, hδ, hδc⟩ := Metric.continuousAt_iff.1 hcA ε hε
      refine ⟨min δ ρ, lt_min hδ hρ, fun w hwin => ?_⟩
      rw [mem_ball] at hwin
      have hwρ : dist w z < ρ := lt_of_lt_of_le hwin (min_le_right _ _)
      have hwδ : dist w z < δ := lt_of_lt_of_le hwin (min_le_left _ _)
      have hwB : w ∈ B := hballB (mem_ball.2 hwρ)
      have hD : dist (D z w) (D z z) < ε := hδc hwδ
      rw [hself z hzB, Real.dist_eq, sub_zero] at hD
      exact hEx w hwB (lt_of_le_of_lt (le_abs_self _) hD)

/-- The compact exhaustion `K_i = closedBall c (r - 1/(i+2))` of `ball c r`. -/
def expK (c : ℂ) (r : ℝ) (i : ℕ) : Set ℂ := closedBall c (r - 1 / ((i : ℝ) + 2))

lemma expK_subset (c : ℂ) (r : ℝ) (i : ℕ) : expK c r i ⊆ ball c r := by
  intro z hz
  rw [expK, mem_closedBall] at hz
  rw [mem_ball]
  have : 0 < 1 / ((i : ℝ) + 2) := by positivity
  linarith

lemma isCompact_expK (c : ℂ) (r : ℝ) (i : ℕ) : IsCompact (expK c r i) :=
  isCompact_closedBall _ _

lemma exists_mem_expK {c : ℂ} {r : ℝ} {z : ℂ} (hz : z ∈ ball c r) : ∃ i : ℕ, z ∈ expK c r i := by
  rw [mem_ball] at hz
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hz)
  refine ⟨n, ?_⟩
  rw [expK, mem_closedBall]
  have h1 : 1 / ((n : ℝ) + 2) ≤ 1 / ((n : ℝ) + 1) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  linarith

/-- **Uniformity on compacts.** If `V2` holds for `D` on the open set `B`, then for a compact `K ⊆ B` and
`δ > 0` one `ε > 0` works for all `z ∈ K`. Proof: finite subcover of `K` by neighbourhoods `U x` of `x`
where `D x ·` is small and `dist · x < δ/2`; for `z ∈ U x`, `w ∈ B`, `δ ≤ dist w z` one has
`δ/2 ≤ dist w x`, hence `e x ≤ D x w` and `D z w ≥ D x w - D x z > e x / 2 ≥ ε`. -/
lemma uniform_on_compact {B : Set ℂ} (hB : IsOpen B) {D : ℂ → ℂ → ℝ}
    (hcont : ContinuousOn (fun q : ℂ × ℂ => D q.1 q.2) (B ×ˢ B))
    (hself : ∀ z ∈ B, D z z = 0)
    (htri : ∀ x ∈ B, ∀ y ∈ B, ∀ z ∈ B, D x z ≤ D x y + D y z)
    (hV : V2 B D) {K : Set ℂ} (hK : IsCompact K) (hKB : K ⊆ B) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε > 0, ∀ z ∈ K, ∀ w ∈ B, δ ≤ dist w z → ε ≤ D z w := by
  have hloc : ∀ x : ℂ, ∃ e : ℝ, x ∈ K → (0 < e ∧ ∀ w ∈ B, δ / 2 ≤ dist w x → e ≤ D x w) := by
    intro x
    by_cases hx : x ∈ K
    · obtain ⟨e, he, hw⟩ := hV x (hKB hx) (δ / 2) (half_pos hδ)
      exact ⟨e, fun _ => ⟨he, hw⟩⟩
    · exact ⟨1, fun h => absurd h hx⟩
  choose e he using hloc
  have hnhds : ∀ x ∈ K, {z : ℂ | D x z < e x / 2 ∧ dist z x < δ / 2} ∈ 𝓝 x := by
    intro x hx
    have hxB : x ∈ B := hKB hx
    have hepos : 0 < e x / 2 := by linarith [(he x hx).1]
    have hc : ContinuousWithinAt (fun z => D x z) B x :=
      (hcont.comp (continuousOn_const.prodMk continuousOn_id)
        (fun z hz => mk_mem_prod hxB hz)) x hxB
    have hcA : ContinuousAt (fun z => D x z) x := hc.continuousAt (hB.mem_nhds hxB)
    have h1 : ∀ᶠ z in 𝓝 x, D x z < e x / 2 := by
      have h0 : D x x < e x / 2 := by rw [hself x hxB]; exact hepos
      exact hcA.eventually (Iio_mem_nhds h0)
    have h2 : ∀ᶠ z in 𝓝 x, dist z x < δ / 2 := Metric.ball_mem_nhds x (half_pos hδ)
    exact h1.and h2
  obtain ⟨t, htK, hcov⟩ :=
    hK.elim_nhds_subcover (fun x => {z : ℂ | D x z < e x / 2 ∧ dist z x < δ / 2}) hnhds
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ x ∈ t, ε ≤ e x / 2 := by
    refine (Filter.eventually_all_finset t).2 fun x hx => ?_
    have hepos : 0 < e x / 2 := by linarith [(he x (htK x hx)).1]
    exact mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds hepos)
  have hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  obtain ⟨ε, hε, hεpos⟩ := (hev.and hpos).exists
  refine ⟨ε, hεpos, fun z hz w hwB hδw => ?_⟩
  obtain ⟨x, hx, hzx⟩ := mem_iUnion₂.1 (hcov hz)
  obtain ⟨hDxz, hdzx⟩ := hzx
  have hxB : x ∈ B := hKB (htK x hx)
  have hzB : z ∈ B := hKB hz
  obtain ⟨-, hewx⟩ := he x (htK x hx)
  have hdwx : δ / 2 ≤ dist w x := by
    have h1 := dist_triangle w x z
    have h2 := dist_comm x z
    linarith
  have h3 := hewx w hwB hdwx
  have h4 := htri x hxB z hzB w hwB
  have h5 := hε x hx
  linarith

/-- The Borel-code window: points `(x, y)` with `x ∈ K_i` and `1/(n+1) ≤ dist y x`. -/
def codeWin (c : ℂ) (r : ℝ) (i n : ℕ) : Set (Win (ball c r)) :=
  {p | p.1.1 ∈ expK c r i ∧ 1 / ((n : ℝ) + 1) ≤ dist p.1.2 p.1.1}

/-- The countable Borel code of `V2`: for all `n, i` some `m` gives `d ≥ 1/(m+1)` on `codeWin i n`. -/
def codeSet (c : ℂ) (r : ℝ) : Set C(Win (ball c r), ℝ) :=
  {d | ∀ n i : ℕ, ∃ m : ℕ, ∀ p ∈ codeWin c r i n, 1 / ((m : ℝ) + 1) ≤ d p}

lemma measurableSet_codeSet (c : ℂ) (r : ℝ) : MeasurableSet (codeSet c r) := by
  have hEq : codeSet c r = ⋂ n : ℕ, ⋂ i : ℕ, ⋃ m : ℕ,
      {d : C(Win (ball c r), ℝ) | ∀ p ∈ codeWin c r i n, 1 / ((m : ℝ) + 1) ≤ d p} := by
    ext d
    simp only [codeSet, mem_ofPred_eq, mem_iInter, mem_iUnion]
  rw [hEq]
  refine MeasurableSet.iInter fun n => MeasurableSet.iInter fun i => MeasurableSet.iUnion fun m => ?_
  have hc : IsClosed {d : C(Win (ball c r), ℝ) | ∀ p ∈ codeWin c r i n, 1 / ((m : ℝ) + 1) ≤ d p} := by
    have : {d : C(Win (ball c r), ℝ) | ∀ p ∈ codeWin c r i n, 1 / ((m : ℝ) + 1) ≤ d p} =
        ⋂ p ∈ codeWin c r i n, {d : C(Win (ball c r), ℝ) | 1 / ((m : ℝ) + 1) ≤ d p} := by
      ext d
      simp only [mem_ofPred_eq, mem_iInter]
    rw [this]
    exact isClosed_biInter fun p _ =>
      isClosed_le continuous_const (continuous_eval_const p)
  exact hc.measurableSet

lemma mem_codeSet_iff (c : ℂ) (r : ℝ) (d : C(Win (ball c r), ℝ)) :
    d ∈ codeSet c r ↔ ∀ n i : ℕ, ∃ m : ℕ, ∀ z ∈ expK c r i, ∀ w ∈ ball c r,
      1 / ((n : ℝ) + 1) ≤ dist w z → 1 / ((m : ℝ) + 1) ≤ decoderOn (ball c r) d z w := by
  constructor
  · intro h n i
    obtain ⟨m, hm⟩ := h n i
    refine ⟨m, fun z hz w hw hd => ?_⟩
    rw [decoderOn_apply_of_mem d (expK_subset c r i hz) hw]
    exact hm ⟨(z, w), mk_mem_prod (expK_subset c r i hz) hw⟩ ⟨hz, hd⟩
  · intro h n i
    obtain ⟨m, hm⟩ := h n i
    refine ⟨m, fun p hp => ?_⟩
    rw [← decoderOn_eq_eval d p]
    exact hm p.1.1 hp.1 p.1.2 p.2.2 hp.2

/-- `V2` from the countable code. -/
lemma V2_of_codeSet {c : ℂ} {r : ℝ} {D : ℂ → ℂ → ℝ}
    (h : ∀ n i : ℕ, ∃ m : ℕ, ∀ z ∈ expK c r i, ∀ w ∈ ball c r,
      1 / ((n : ℝ) + 1) ≤ dist w z → 1 / ((m : ℝ) + 1) ≤ D z w) :
    V2 (ball c r) D := by
  intro z hz δ hδ
  obtain ⟨i, hi⟩ := exists_mem_expK hz
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  obtain ⟨m, hm⟩ := h n i
  exact ⟨1 / ((m : ℝ) + 1), by positivity, fun w hw hδw => hm z hi w hw (le_trans hn.le hδw)⟩

/-- The countable code holds for `V2` (uniformity on the compacts `expK i`). -/
lemma codeSet_of_V2 {c : ℂ} {r : ℝ} {D : ℂ → ℂ → ℝ}
    (hcont : ContinuousOn (fun q : ℂ × ℂ => D q.1 q.2) (ball c r ×ˢ ball c r))
    (hself : ∀ z ∈ ball c r, D z z = 0)
    (htri : ∀ x ∈ ball c r, ∀ y ∈ ball c r, ∀ z ∈ ball c r, D x z ≤ D x y + D y z)
    (hV : V2 (ball c r) D) :
    ∀ n i : ℕ, ∃ m : ℕ, ∀ z ∈ expK c r i, ∀ w ∈ ball c r,
      1 / ((n : ℝ) + 1) ≤ dist w z → 1 / ((m : ℝ) + 1) ≤ D z w := by
  intro n i
  have hδ : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  obtain ⟨ε, hε, hunif⟩ := uniform_on_compact isOpen_ball hcont hself htri hV
    (isCompact_expK c r i) (expK_subset c r i) hδ
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
  exact ⟨m, fun z hz w hw hd => le_trans hm.le (hunif z hz w hw hd)⟩

/-- The length identity `ofReal D = internalMetric D B` on `B × B` (clause `ofReal_eq_internalMetric`).
NOT reduced to a countable code here: it is the named input `hL7` below (open gap, see the report). -/
def internalSet (B : Set ℂ) : Set C(Win B, ℝ) :=
  {d | ∀ z ∈ B, ∀ w ∈ B, ENNReal.ofReal (decoderOn B d z w) = internalMetric (decoderOn B d) B z w}

/-- Characterisation: `IsLengthMetricOn` of the decoder is the conjunction of the three pieces. -/
theorem isLengthMetricOn_decoderOn_iff {c : ℂ} {r : ℝ} (d : C(Win (ball c r), ℝ)) :
    IsLengthMetricOn (ball c r) (decoderOn (ball c r) d) ↔
      d ∈ clausesSet (ball c r) ∧ d ∈ codeSet c r ∧ d ∈ internalSet (ball c r) := by
  have hB : IsOpen (ball c r) := isOpen_ball
  have hcont : ContinuousOn (fun q : ℂ × ℂ => decoderOn (ball c r) d q.1 q.2) (ball c r ×ˢ ball c r) :=
    continuousOn_decoderOn d
  constructor
  · intro h
    have hV : V2 (ball c r) (decoderOn (ball c r) d) :=
      (isOpen_iff_of_V2 hB hcont h.self_eq_zero).1 h.isOpen_iff
    exact ⟨⟨h.self_eq_zero, h.symm, h.triangle⟩,
      (mem_codeSet_iff c r d).2 (codeSet_of_V2 hcont h.self_eq_zero h.triangle hV),
      h.ofReal_eq_internalMetric⟩
  · rintro ⟨⟨hs, hsym, htri⟩, hcode, hL⟩
    have hV : V2 (ball c r) (decoderOn (ball c r) d) :=
      V2_of_codeSet ((mem_codeSet_iff c r d).1 hcode)
    have eq0 : ∀ z ∈ ball c r, ∀ w ∈ ball c r, decoderOn (ball c r) d z w = 0 → z = w := by
      intro z hz w hw hzw
      by_contra hne
      have hδ : 0 < dist w z := dist_pos.2 (Ne.symm hne)
      obtain ⟨ε, hε, hv⟩ := hV z hz (dist w z) hδ
      have := hv w hw le_rfl
      linarith
    exact ⟨hs, eq0, hsym, htri, hcont, (isOpen_iff_of_V2 hB hcont hs).2 hV, hL⟩

/-- **Reduction of B1.** `IsLengthMetricOn B (decoderOn B d)` is Borel as a set of decoders, provided the
internal-metric clause is Borel (named hypothesis `hL7`; NOT derived). The clauses `self_eq_zero`,
`symm`, `triangle`, `isOpen_iff`, `eq_of_eq_zero`, `continuousOn` are proved Borel above. -/
theorem measurableSet_isLengthMetricOn_decoderOn_of_internal {c : ℂ} {r : ℝ}
    (hL7 : MeasurableSet (internalSet (ball c r))) :
    MeasurableSet {d : C(Win (ball c r), ℝ) | IsLengthMetricOn (ball c r) (decoderOn (ball c r) d)} := by
  have hEq : {d : C(Win (ball c r), ℝ) | IsLengthMetricOn (ball c r) (decoderOn (ball c r) d)} =
      (clausesSet (ball c r) ∩ codeSet c r) ∩ internalSet (ball c r) := by
    ext d
    rw [mem_ofPred_eq, isLengthMetricOn_decoderOn_iff d]
    simp only [mem_inter_iff, and_assoc]
  rw [hEq]
  exact ((measurableSet_clausesSet (ball c r)).inter (measurableSet_codeSet c r)).inter hL7

end HarmonicBalls.FirstPassS11ahLengthBorelClauses

#print axioms HarmonicBalls.FirstPassS11ahLengthBorelClauses.isLengthMetricOn_decoderOn_iff

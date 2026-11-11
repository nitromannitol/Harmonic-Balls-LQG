import HarmonicBalls.FirstPass.S11r.CMTransfer
import HarmonicBalls.FirstPass.S11r.Frozen
import HarmonicBalls.FirstPass.S11ai.RootedInstance
import HarmonicBalls.FirstPass.S11r.UnrootedFixed
import HarmonicBalls.FirstPass.S11c.CoordRooted11_7
import HarmonicBalls.FirstPass.S11c.TranslateField11_7
import HarmonicBalls.Proofs.Sec6.LQGWeylScaling
import HarmonicBalls.Proposed.LQG
import HarmonicBalls.FirstPass.S11r.NoShortcut
import HarmonicBalls.FirstPass.S11d.Dyadic
import HarmonicBalls.FirstPass.S11r.MetricSign
import HarmonicBalls.FirstPass.S11r.RootedTranslate

/-!
# Rooted local identification event


Let `T` be a centred raw pairing (a whole-plane field seen from the root `z`, centred at `0`), `D` a local window,
`κ` the local measure decoder and `m` the local metric decoder (`LocalMeasureKernelStmt`, `LocalMetricReplacementStmt`).
The centred canonical field is `canonFieldOf γ T`; its decoders are `Dμ`, `Dd` (`LQGCanonicalIdentificationStmt`).

* `rootedLocalIdentEvent`: a set of raw pairings `T` such that the centred decoded measure `κ` is proportional to `Dμ`
  on a compact window `S` (checked cross-multiplied on a countable family `A n ⊆ S`, Section 4.3 (3)), and the decoded
  metric `m` is proportional to `Dd` on a countable family of pairs (Section 4.3 (4)).
* `measurableSet_rootedLocalIdentEvent`: this event is measurable for the distribution σ-algebra (Section 4.3).
* `rootedLocalObs_shifted_eq` (Section 4.5): for the root-shifted field `addFunPairing (translatedPairing hC hcirc z ω) u`
  with `u` an admissible root shift, the rooted local observation equals the physical rooted observation
  `campbellReferenceObs γ α₀ D (hC ω) z`. This is an exact pairing identity, with no comparison of decoders.
* `ae_rootedLocalIdent_shifted`: almost-sure transfer of the event to the root-shifted field (Section 4.4), from the base
  conullity `hbase` through the Cameron-Martin transfer `ae_addFunPairing_of_ae` (CMTransfer.lean).

Section 4.4 base conullity, measure clause: `ae_rootedMeasureIdent_base` (conditional on named inputs: the rooted decoder
clause `hκ`, the coordinate change `hCC`, the existence `hνex`, the canonical identification `hIdγ`, a metric existence
`hDex`, and the window geometry `hSb`, `hSQ` with the frozen full-support statement `hPos`; the window positivity and
finiteness are derived in `ae_lqgMeasure_pos_lt_top`, the former input `hPF` is removed). The metric clause of the base conullity is
`ae_rootedMetricIdent_base`, conditional on the locality input `hLoc` (now derived from `ae_rootedWeylMetric_internalMetric_translate`; internal metric under translation and constant
shift; MISSING, to be sourced: Fact 2.2 II, arXiv:2208.11795 p. 9-10) and on the Proposed metric axioms `hAx`. Its
deterministic core `rootedMetricIdent_of_internal` uses the no-shortcut lemma `eq_internalMetric_on_small_ball`.
-/

universe u

namespace HarmonicBalls

open MeasureTheory Set Metric
open scoped ENNReal

/-- Re-centring at the root `z`: `recentrePairing z T ψ = T (ψ (· + z))`, the raw pairing seen from `z`. -/
noncomputable def recentrePairing (z : ℂ) (T : (ℂ → ℝ) → ℝ) : (ℂ → ℝ) → ℝ :=
  fun ψ => T (fun y => ψ (y + z))

/-- The mean-zero test functions supported in the window `D`, the domain of the local decoders `κ`, `m`. -/
abbrev MeanZeroTest (D : Set ℂ) : Type := {φ : ℂ → ℝ // IsTestFunction D φ ∧ ∫ x, φ x = 0}

/-- The γ-rooted local observation at background `0`, in uncentred coordinates, of the centred raw pairing `T`:
`campbellReferenceObs γ 0 D (recentrePairing z T) z`. This is the input of the decoders `κ`, `m`. -/
noncomputable def rootedLocalObs (γ : ℝ) (D : Set ℂ) (z : ℂ) (T : (ℂ → ℝ) → ℝ) : MeanZeroTest D → ℝ :=
  (campbellReferenceObs γ 0 D (recentrePairing z T) z).2

open Classical in
/-- The metric decoder read at the uncentred pair `(x, y)`; `0` outside the window `D × D`. -/
noncomputable def rootedMetricAt (D : Set ℂ) (m : (MeanZeroTest D → ℝ) → C(↥(D ×ˢ D), ℝ)) (γ : ℝ) (z : ℂ)
    (T : (ℂ → ℝ) → ℝ) (x y : ℂ) : ENNReal :=
  if h : (x, y) ∈ D ×ˢ D then ENNReal.ofReal (m (rootedLocalObs γ D z T) ⟨(x, y), h⟩) else 0

/-- Measure clause (Section 4.3 (3)), cross-multiplied so that no scalar is quantified. The centred decoded measure
`ν(B) = κ(obs)((· - z)⁻¹' B)` and the centred canonical measure `K = Dμ(canonFieldOf γ T)` satisfy: `K(S)` and `ν(S)` are
positive and finite, and `ν(A n) K(S) = K(A n) ν(S)` for every `n` (with `A n ⊆ S`, a countable generating family). -/
def rootedMeasureIdent (D : Set ℂ) (κ : (MeanZeroTest D → ℝ) → Measure ℂ) (Dμ : S11n.CanonSpace → Measure ℂ)
    (γ : ℝ) (z : ℂ) (S : Set ℂ) (A : ℕ → Set ℂ) (T : (ℂ → ℝ) → ℝ) : Prop :=
  0 < Dμ (canonFieldOf γ T) S ∧ Dμ (canonFieldOf γ T) S < ∞ ∧
  0 < κ (rootedLocalObs γ D z T) ((fun w => w - z) ⁻¹' S) ∧
  κ (rootedLocalObs γ D z T) ((fun w => w - z) ⁻¹' S) < ∞ ∧
  ∀ n : ℕ, κ (rootedLocalObs γ D z T) ((fun w => w - z) ⁻¹' A n) * Dμ (canonFieldOf γ T) S =
    Dμ (canonFieldOf γ T) (A n) * κ (rootedLocalObs γ D z T) ((fun w => w - z) ⁻¹' S)

/-- Metric clause (Section 4.3 (4)): there is a countable family of reference pairs `pq k` in the balls of radius `R k`
about `0` (centred coordinates), with `Dd(pq k) > 0`, such that for all pairs `X i, X j` of the countable family inside
the window, `m(X i + z, X j + z) Dd(pq k) = Dd(X i, X j) m(pq k + z)`. The decoders `Dd` are centred. -/
def rootedMetricIdent (D : Set ℂ) (m : (MeanZeroTest D → ℝ) → C(↥(D ×ˢ D), ℝ)) (Dd : S11n.CanonSpace → ℂ → ℂ → ℝ)
    (γ : ℝ) (z : ℂ) (X : ℕ → ℂ) (R : ℕ → ℝ) (pq : ℕ → ℂ × ℂ) (T : (ℂ → ℝ) → ℝ) : Prop :=
  ∃ k : ℕ, ‖(pq k).1‖ < R k ∧ ‖(pq k).2‖ < R k ∧ (pq k).1 + z ∈ D ∧ (pq k).2 + z ∈ D ∧
    0 < Dd (canonFieldOf γ T) (pq k).1 (pq k).2 ∧
    ∀ i j : ℕ, ‖X i‖ < R k → ‖X j‖ < R k → X i + z ∈ D → X j + z ∈ D →
      rootedMetricAt D m γ z T (X i + z) (X j + z) * ENNReal.ofReal (Dd (canonFieldOf γ T) (pq k).1 (pq k).2) =
        ENNReal.ofReal (Dd (canonFieldOf γ T) (X i) (X j)) * rootedMetricAt D m γ z T ((pq k).1 + z) ((pq k).2 + z)

/-- **The rooted local identification event** (Section 4.3): the set of centred raw pairings `T` satisfying both the
measure clause and the metric clause. -/
def rootedLocalIdentEvent (D : Set ℂ) (κ : (MeanZeroTest D → ℝ) → Measure ℂ)
    (m : (MeanZeroTest D → ℝ) → C(↥(D ×ˢ D), ℝ)) (Dμ : S11n.CanonSpace → Measure ℂ) (Dd : S11n.CanonSpace → ℂ → ℂ → ℝ)
    (γ : ℝ) (z : ℂ) (S : Set ℂ) (A : ℕ → Set ℂ) (X : ℕ → ℂ) (R : ℕ → ℝ) (pq : ℕ → ℂ × ℂ) :
    Set ((ℂ → ℝ) → ℝ) :=
  {T | rootedMeasureIdent D κ Dμ γ z S A T ∧ rootedMetricIdent D m Dd γ z X R pq T}

/-! ### Measurability (Section 4.3) -/

/-- Translate of a test function on `D` is a test function on `univ`. -/
theorem isTestFunction_univ_add_right {D : Set ℂ} {ψ : ℂ → ℝ} (hψ : IsTestFunction D ψ) (z : ℂ) :
    IsTestFunction univ (fun y => ψ (y + z)) :=
  ⟨hψ.1.comp (contDiff_id.add contDiff_const), hψ.2.1.comp_homeomorph (Homeomorph.addRight z), subset_univ _⟩

theorem measurable_recentre_obs (γ : ℝ) (D : Set ℂ) (z : ℂ) (ψ : MeanZeroTest D) :
    Measurable[distributionMeasurableSpace] (fun T : (ℂ → ℝ) → ℝ => rootedLocalObs γ D z T ψ) := by
  have h : (fun T : (ℂ → ℝ) → ℝ => rootedLocalObs γ D z T ψ) =
      fun T => T (fun y => ψ.1 (y + z)) -
        γ * ∫ w, (Real.log ‖w - z‖ - Real.log (max 1 ‖w‖)) * ψ.1 w := by
    funext T
    simp [rootedLocalObs, campbellReferenceObs, fieldPairing, recentrePairing]
  rw [h]
  exact (measurable_distribution_eval (isTestFunction_univ_add_right ψ.2.1 z)).sub measurable_const

theorem measurable_rootedLocalObs (γ : ℝ) (D : Set ℂ) (z : ℂ) :
    Measurable[distributionMeasurableSpace] (rootedLocalObs γ D z) :=
  by
    let _ : MeasurableSpace ((ℂ → ℝ) → ℝ) := distributionMeasurableSpace
    exact measurable_pi_iff.2 (fun ψ => measurable_recentre_obs γ D z ψ)

theorem measurable_canonFieldOf_distribution (γ : ℝ) :
    Measurable[distributionMeasurableSpace] (fun T : (ℂ → ℝ) → ℝ => canonFieldOf γ T) := by
  let _ : MeasurableSpace ((ℂ → ℝ) → ℝ) := distributionMeasurableSpace
  refine measurable_pi_iff.2 (fun i => ?_)
  have h : (fun T : (ℂ → ℝ) → ℝ => canonFieldOf γ T i) =
      fun T => T i.1 - γ * ∫ x, i.1 x * Real.log ‖x‖ := by
    funext T
    simp [canonFieldOf, fieldPairing]
  rw [h]
  exact (measurable_distribution_eval i.2.1).sub measurable_const

theorem measurable_rootedMetricAt (D : Set ℂ) (m : (MeanZeroTest D → ℝ) → C(↥(D ×ˢ D), ℝ)) (hm : Measurable m)
    (γ : ℝ) (z : ℂ) (x y : ℂ) :
    Measurable[distributionMeasurableSpace] (fun T : (ℂ → ℝ) → ℝ => rootedMetricAt D m γ z T x y) := by
  by_cases h : (x, y) ∈ D ×ˢ D
  · have h' : (fun T : (ℂ → ℝ) → ℝ => rootedMetricAt D m γ z T x y) =
        fun T => ENNReal.ofReal (m (rootedLocalObs γ D z T) ⟨(x, y), h⟩) := by
      funext T
      simp [rootedMetricAt, h]
    rw [h']
    exact ((ContinuousMap.measurable_eval _).comp (hm.comp (measurable_rootedLocalObs γ D z))).ennreal_ofReal
  · have h' : (fun T : (ℂ → ℝ) → ℝ => rootedMetricAt D m γ z T x y) = fun _ => 0 := by
      funext T
      simp [rootedMetricAt, h]
    rw [h']
    exact measurable_const

/-- `{T | p ∧ q T}` is measurable when `{T | q T}` is, for a constant proposition `p`. -/
theorem measurableSet_and_prop_of {p : Prop} {q : ((ℂ → ℝ) → ℝ) → Prop}
    (hq : MeasurableSet[distributionMeasurableSpace] {T | q T}) :
    MeasurableSet[distributionMeasurableSpace] {T | p ∧ q T} := by
  by_cases hp : p
  · simpa [hp] using hq
  · simp [hp]

/-- `{T | p → q T}` is measurable when `{T | q T}` is, for a constant proposition `p`. -/
theorem measurableSet_imp_prop_of {p : Prop} {q : ((ℂ → ℝ) → ℝ) → Prop}
    (hq : MeasurableSet[distributionMeasurableSpace] {T | q T}) :
    MeasurableSet[distributionMeasurableSpace] {T | p → q T} := by
  by_cases hp : p
  · simpa [hp] using hq
  · simp [hp]

/-- A countable intersection of measurable predicates. -/
theorem measurableSet_forall_nat {P : ℕ → ((ℂ → ℝ) → ℝ) → Prop}
    (h : ∀ n, MeasurableSet[distributionMeasurableSpace] {T | P n T}) :
    MeasurableSet[distributionMeasurableSpace] {T | ∀ n, P n T} := by
  have hset : {T : (ℂ → ℝ) → ℝ | ∀ n, P n T} = ⋂ n, {T | P n T} := by
    ext T
    simp
  rw [hset]
  exact MeasurableSet.iInter h

/-- **Measurability of the rooted local identification event** (Section 4.3).
The decoders `κ`, `m` are measurable (`LocalMeasureKernelStmt`, `LocalMetricReplacementStmt`), `Dμ` is measurable and
each `Dd · x y` is measurable on canonical fields. The event is a countable Boolean combination of measurable maps. -/
theorem measurableSet_rootedLocalIdentEvent (D : Set ℂ) (κ : (MeanZeroTest D → ℝ) → Measure ℂ)
    (m : (MeanZeroTest D → ℝ) → C(↥(D ×ˢ D), ℝ)) (Dμ : S11n.CanonSpace → Measure ℂ)
    (Dd : S11n.CanonSpace → ℂ → ℂ → ℝ) (γ : ℝ) (z : ℂ) (S : Set ℂ) (A : ℕ → Set ℂ) (X : ℕ → ℂ) (R : ℕ → ℝ)
    (pq : ℕ → ℂ × ℂ) (hκ : Measurable κ) (hm : Measurable m) (hDμ : Measurable Dμ)
    (hDd : ∀ x y : ℂ, Measurable fun L : S11n.CanonSpace => Dd L x y)
    (hS : MeasurableSet S) (hA : ∀ n, MeasurableSet (A n)) :
    MeasurableSet[distributionMeasurableSpace] (rootedLocalIdentEvent D κ m Dμ Dd γ z S A X R pq) := by
  have hK : Measurable[distributionMeasurableSpace] fun T : (ℂ → ℝ) → ℝ => Dμ (canonFieldOf γ T) :=
    hDμ.comp (measurable_canonFieldOf_distribution γ)
  have hobs : Measurable[distributionMeasurableSpace] (rootedLocalObs γ D z) :=
    measurable_rootedLocalObs γ D z
  have hν : Measurable[distributionMeasurableSpace] fun T : (ℂ → ℝ) → ℝ =>
      κ (rootedLocalObs γ D z T) := hκ.comp hobs
  have hSz : MeasurableSet ((fun w : ℂ => w - z) ⁻¹' S) := (measurable_id.sub_const z) hS
  have hAz : ∀ n, MeasurableSet ((fun w : ℂ => w - z) ⁻¹' A n) := fun n =>
    (measurable_id.sub_const z) (hA n)
  have hKS : Measurable[distributionMeasurableSpace] fun T : (ℂ → ℝ) → ℝ => Dμ (canonFieldOf γ T) S :=
    (Measure.measurable_coe hS).comp hK
  have hKA : ∀ n, Measurable[distributionMeasurableSpace] fun T : (ℂ → ℝ) → ℝ =>
      Dμ (canonFieldOf γ T) (A n) := fun n => (Measure.measurable_coe (hA n)).comp hK
  have hνS : Measurable[distributionMeasurableSpace] fun T : (ℂ → ℝ) → ℝ =>
      κ (rootedLocalObs γ D z T) ((fun w : ℂ => w - z) ⁻¹' S) :=
    (Measure.measurable_coe hSz).comp hν
  have hνA : ∀ n, Measurable[distributionMeasurableSpace] fun T : (ℂ → ℝ) → ℝ =>
      κ (rootedLocalObs γ D z T) ((fun w : ℂ => w - z) ⁻¹' A n) := fun n =>
    (Measure.measurable_coe (hAz n)).comp hν
  have hMI : MeasurableSet[distributionMeasurableSpace]
      {T : (ℂ → ℝ) → ℝ | rootedMeasureIdent D κ Dμ γ z S A T} := by
    unfold rootedMeasureIdent
    refine (measurableSet_lt measurable_const hKS).inter
      ((measurableSet_lt hKS measurable_const).inter
        ((measurableSet_lt measurable_const hνS).inter
          ((measurableSet_lt hνS measurable_const).inter ?_)))
    refine measurableSet_forall_nat fun n => ?_
    have h1 : Measurable[distributionMeasurableSpace] fun T : (ℂ → ℝ) → ℝ =>
        κ (rootedLocalObs γ D z T) ((fun w : ℂ => w - z) ⁻¹' A n) * Dμ (canonFieldOf γ T) S :=
      (hνA n).mul hKS
    have h2 : Measurable[distributionMeasurableSpace] fun T : (ℂ → ℝ) → ℝ =>
        Dμ (canonFieldOf γ T) (A n) * κ (rootedLocalObs γ D z T) ((fun w : ℂ => w - z) ⁻¹' S) :=
      (hKA n).mul hνS
    exact measurableSet_eq_fun h1 h2
  have hMT : MeasurableSet[distributionMeasurableSpace]
      {T : (ℂ → ℝ) → ℝ | rootedMetricIdent D m Dd γ z X R pq T} := by
    have hset : {T : (ℂ → ℝ) → ℝ | rootedMetricIdent D m Dd γ z X R pq T} =
        ⋃ k : ℕ, {T : (ℂ → ℝ) → ℝ | ‖(pq k).1‖ < R k ∧ ‖(pq k).2‖ < R k ∧ (pq k).1 + z ∈ D ∧
          (pq k).2 + z ∈ D ∧ 0 < Dd (canonFieldOf γ T) (pq k).1 (pq k).2 ∧
          ∀ i j : ℕ, ‖X i‖ < R k → ‖X j‖ < R k → X i + z ∈ D → X j + z ∈ D →
            rootedMetricAt D m γ z T (X i + z) (X j + z) * ENNReal.ofReal (Dd (canonFieldOf γ T) (pq k).1 (pq k).2) =
              ENNReal.ofReal (Dd (canonFieldOf γ T) (X i) (X j)) * rootedMetricAt D m γ z T ((pq k).1 + z) ((pq k).2 + z)} := by
      ext T
      simp [rootedMetricIdent]
    rw [hset]
    refine MeasurableSet.iUnion fun k => ?_
    have hpos : MeasurableSet[distributionMeasurableSpace] {T : (ℂ → ℝ) → ℝ |
        0 < Dd (canonFieldOf γ T) (pq k).1 (pq k).2} :=
      measurableSet_lt measurable_const ((hDd _ _).comp (measurable_canonFieldOf_distribution γ))
    have hall : MeasurableSet[distributionMeasurableSpace] {T : (ℂ → ℝ) → ℝ | ∀ i j : ℕ,
        ‖X i‖ < R k → ‖X j‖ < R k → X i + z ∈ D → X j + z ∈ D →
          rootedMetricAt D m γ z T (X i + z) (X j + z) * ENNReal.ofReal (Dd (canonFieldOf γ T) (pq k).1 (pq k).2) =
            ENNReal.ofReal (Dd (canonFieldOf γ T) (X i) (X j)) * rootedMetricAt D m γ z T ((pq k).1 + z) ((pq k).2 + z)} := by
      refine measurableSet_forall_nat fun i => measurableSet_forall_nat fun j => ?_
      refine measurableSet_imp_prop_of (measurableSet_imp_prop_of (measurableSet_imp_prop_of
        (measurableSet_imp_prop_of ?_)))
      have h1 : Measurable[distributionMeasurableSpace] fun T : (ℂ → ℝ) → ℝ =>
          rootedMetricAt D m γ z T (X i + z) (X j + z) * ENNReal.ofReal (Dd (canonFieldOf γ T) (pq k).1 (pq k).2) :=
        (measurable_rootedMetricAt D m hm γ z _ _).mul
          (((hDd _ _).comp (measurable_canonFieldOf_distribution γ)).ennreal_ofReal)
      have h2 : Measurable[distributionMeasurableSpace] fun T : (ℂ → ℝ) → ℝ =>
          ENNReal.ofReal (Dd (canonFieldOf γ T) (X i) (X j)) * rootedMetricAt D m γ z T ((pq k).1 + z) ((pq k).2 + z) :=
        (((hDd _ _).comp (measurable_canonFieldOf_distribution γ)).ennreal_ofReal).mul
          (measurable_rootedMetricAt D m hm γ z _ _)
      exact measurableSet_eq_fun h1 h2
    exact measurableSet_and_prop_of (measurableSet_and_prop_of (measurableSet_and_prop_of
      (measurableSet_and_prop_of (hpos.inter hall))))
  exact hMI.inter hMT

/-! ### Section 4.4 and 4.5: the base reduction and the shifted local observation -/

/-- The base observation: for the translated field, the centred pairing re-centred at `z` is the uncentred field
`hC ω` on mean-zero test functions (the additive constant `hcirc ω 1 z` drops out). -/
theorem rootedLocalObs_translated {Ω : Type*} (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (γ : ℝ)
    (D : Set ℂ) (z : ℂ) (ω : Ω) (ψ : MeanZeroTest D) :
    rootedLocalObs γ D z (S11c.translatedPairing hC hcirc z ω) ψ =
      (campbellReferenceObs γ 0 D (hC ω) z).2 ψ := by
  have hmean : ∫ x, ψ.1 (x + z) = 0 := by
    rw [integral_add_right_eq_self ψ.1 z]
    exact ψ.2.2
  simp [rootedLocalObs, campbellReferenceObs, recentrePairing, S11c.translatedPairing, fieldPairing, hmean]

/-- **Section 4.5 (identity of the shifted local observation).** For an admissible root shift `u` at `z` with
`D ⊆ ball z b`, the rooted local observation of the root-shifted field `addFunPairing (translatedPairing hC hcirc z ω) u`
equals the physical rooted observation `campbellReferenceObs γ α₀ D (hC ω) z` (background `α₀`) on every mean-zero test
function supported in `D`. The two sides differ only by the additive constant of the translated field, which is killed
by the mean-zero condition. -/
theorem rootedLocalObs_shifted_eq {Ω : Type*} (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (γ α₀ : ℝ)
    (D : Set ℂ) (z : ℂ) (ω : Ω) (b : ℝ) (u : ℂ → ℝ) (hadm : FirstPassS11ai.AdmissibleRootShift α₀ z b u)
    (hD : D ⊆ ball z b) (ψ : MeanZeroTest D) :
    rootedLocalObs γ D z (addFunPairing (S11c.translatedPairing hC hcirc z ω) u) ψ =
      (campbellReferenceObs γ α₀ D (hC ω) z).2 ψ := by
  obtain ⟨hψD, hψ0⟩ := ψ.2
  have hmean : ∫ x, ψ.1 (x + z) = 0 := by
    rw [integral_add_right_eq_self ψ.1 z]
    exact hψ0
  have hsupp : ∀ w, w ∉ D → ψ.1 w = 0 := fun w hw =>
    image_eq_zero_of_notMem_tsupport (fun h => hw (hψD.2.2 h))
  have hu : ∫ x, u x * ψ.1 (x + z) = ∫ w, -α₀ * (ψ.1 w * Real.log ‖w‖) := by
    rw [← integral_add_right_eq_self (fun w : ℂ => -α₀ * (ψ.1 w * Real.log ‖w‖)) z]
    congr 1
    funext x
    show u x * ψ.1 (x + z) = -α₀ * (ψ.1 (x + z) * Real.log ‖x + z‖)
    by_cases hx : x + z ∈ D
    · have hxb : x ∈ ball (0 : ℂ) b := by
        have h1 := hD hx
        rw [mem_ball, dist_eq_norm] at h1
        rw [mem_ball, dist_eq_norm]
        simpa using h1
      rw [hadm.2.2.2.2.2.2 x hxb, add_comm z x]
      ring
    · rw [hsupp _ hx]
      simp
  simp only [rootedLocalObs, campbellReferenceObs, recentrePairing, addFunPairing, S11c.translatedPairing,
    fieldPairing, sub_add_cancel, hmean, hu, integral_const_mul, mul_zero, sub_zero, zero_mul]
  ring

/-- **Section 4.4, almost-sure transfer to the root-shifted field.** Given the base conullity
`∀ᵐ ω, translatedPairing hC hcirc z ω ∈ E` of a measurable set `E` of raw pairings (the rooted local identification event
`rootedLocalIdentEvent`), the root-shifted field lies in `E` almost surely. The only input is the Cameron-Martin
transfer `ae_addFunPairing_of_ae` (CMTransfer.lean, frozen `CameronMartinGFFMutualAbsCont`). -/
theorem ae_rootedLocalIdent_shifted {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hCM : CameronMartinGFFMutualAbsCont.{u}) {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {z : ℂ}
    (hTr : IsWholePlaneGFF P (S11c.translatedPairing hC hcirc z) (S11c.translatedCircle hcirc z))
    {α₀ b : ℝ} {u : ℂ → ℝ} (hadm : FirstPassS11ai.AdmissibleRootShift α₀ z b u)
    {E : Set ((ℂ → ℝ) → ℝ)} (hE : MeasurableSet[distributionMeasurableSpace] E)
    (hbase : ∀ᵐ ω ∂P, S11c.translatedPairing hC hcirc z ω ∈ E) :
    ∀ᵐ ω ∂P, addFunPairing (S11c.translatedPairing hC hcirc z ω) u ∈ E :=
  ae_addFunPairing_of_ae P hCM hTr hadm.2.2.2.1 hadm.2.2.2.2.1 hadm.2.2.2.2.2.1 hE hbase

/-! ### Section 4.4, measure clause of the base conullity

Route: the rooted LQG measure at the root `z` of the physical field, with the `(max 1 |·|)`
normalisation, is the Weyl density `exp(γ v)` (v = γ log max(1,|·|), continuous) times the translate of the
centred LQG measure `ν` (coordinate change, `ae_isLQGLimit_rooted_translate`); the rooted clause of
`LocalMeasureKernelStmt` at background `0` then identifies `κ` with it on the window; the centred measure is
identified with the canonical one by `LQGCanonicalIdentificationStmt` at insertion `γ`. -/

/-- The continuous Weyl shift `v(w) = γ log max(1, |w|)`: it vanishes on the unit disc. -/
theorem continuous_gamma_log_max_one (γ : ℝ) :
    Continuous (fun w : ℂ => γ * Real.log (max 1 ‖w‖)) := by
  refine continuous_const.mul (Continuous.log ?_ ?_)
  · exact continuous_const.max continuous_norm
  · intro w
    exact (lt_of_lt_of_le one_pos (le_max_left _ _)).ne'

/-- Continuity in the centre of the rooted circle averages `h_r(x) - γ circleAverage(log|· - z|)(x)` at a fixed
positive radius, from the continuity of the field circle averages and the closed form of the log circle average
(Mathlib `circleAverage_log_norm_sub_const_eq_log_radius_add_posLog`). -/
theorem continuous_rootedCircleAverage_of_field {α γ r : ℝ} {z : ℂ} {h : ℝ → ℂ → ℝ} (hr : 0 < r)
    (hf : Continuous (fun x => fieldCircleAverage α h r x)) :
    Continuous (fun x => rootedCircleAverage α γ z h r x) := by
  have hlog : Continuous (fun x : ℂ => Real.circleAverage (fun y => Real.log ‖y - z‖) x r) := by
    have hfun : (fun x : ℂ => Real.circleAverage (fun y => Real.log ‖y - z‖) x r) =
        fun x => Real.log r + Real.posLog (r⁻¹ * ‖x - z‖) := by
      funext x
      exact circleAverage_log_norm_sub_const_eq_log_radius_add_posLog hr.ne'
    rw [hfun]
    exact continuous_const.add (Real.continuous_posLog.comp
      (continuous_const.mul (continuous_norm.comp (continuous_id.sub continuous_const))))
  unfold rootedCircleAverage
  exact hf.sub (continuous_const.mul hlog)

/-- Weyl density of the rooted profile: the LQG measure of the rooted circle averages, with the
`γ log max(1,|·|)` normalisation, is the translate of the centred measure `ν` weighted by `exp(γ v)`. -/
theorem ae_isLQGLimit_rootedMax {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hG : IsWholePlaneGFF P hC hcirc) (z : ℂ)
    (hCC : LQGMeasureCoordChange P γ γ (S11c.translatedPairing hC hcirc z) (S11c.translatedCircle hcirc z))
    {ν : Ω → Measure ℂ} (hν : IsLQGMeasureOfField P γ γ (S11c.translatedCircle hcirc z) ν) :
    ∀ᵐ ω ∂P, IsLQGLimit γ
      (addCircleAverage (fieldCircleAverage 0 (hcirc ω))
        (fun w => -γ * Real.log ‖w - z‖ + γ * Real.log (max 1 ‖w‖)))
      ((ENNReal.ofReal (Real.exp (γ * hcirc ω 1 z)) • (ν ω).map (fun x => x + z)).withDensity fun w =>
        ENNReal.ofReal (Real.exp (γ * (γ * Real.log (max 1 ‖w‖))))) := by
  have hlim := S11c.ae_isLQGLimit_rooted_translate (P := P) hγ0 hγ2 (hcirc := hcirc)
    (hcirc' := S11c.translatedCircle hcirc z) (hC' := S11c.translatedPairing hC hcirc z) z
    (fun ω r x => rfl) (S11c.isWholePlaneGFF_translate hG z) hCC hν
  have hcont : ∀ᵐ ω ∂P, ∀ n : ℕ, Continuous (fieldCircleAverage 0 (hcirc ω) (dyadicScale n)) :=
    ae_all_iff.mpr (fun n => hG.ae_continuous_fieldCircleAverage 0 (dyadicScale_pos n))
  filter_upwards [hlim, hcont] with ω hω hωc
  have hW := Section6.isLQGLimit_addCircleAverage hω
    (fun n => continuous_rootedCircleAverage_of_field (dyadicScale_pos n) (hωc n))
    (fun w => γ * Real.log (max 1 ‖w‖)) (continuous_gamma_log_max_one γ)
  have heq : addCircleAverage (rootedCircleAverage 0 γ z (hcirc ω)) (fun w => γ * Real.log (max 1 ‖w‖)) =
      addCircleAverage (fieldCircleAverage 0 (hcirc ω))
        (fun w => -γ * Real.log ‖w - z‖ + γ * Real.log (max 1 ‖w‖)) := by
    funext r x
    simp only [addCircleAverage, rootedCircleAverage]
    have hL : CircleIntegrable (fun w : ℂ => Real.log ‖w - z‖) x r := circleIntegrable_log_norm_sub_const r
    have hV : CircleIntegrable (fun w : ℂ => γ * Real.log (max 1 ‖w‖)) x r :=
      (continuous_gamma_log_max_one γ).continuousOn.circleIntegrable'
    have hA : CircleIntegrable (fun w : ℂ => -γ * Real.log ‖w - z‖) x r := hL.const_mul (-γ)
    have hscal : Real.circleAverage (fun w : ℂ => -γ * Real.log ‖w - z‖) x r =
        -γ * Real.circleAverage (fun w : ℂ => Real.log ‖w - z‖) x r := by
      have h1 : (fun w : ℂ => -γ * Real.log ‖w - z‖) = fun w => (-γ) • Real.log ‖w - z‖ := by
        funext w
        simp [smul_eq_mul]
      rw [h1, Real.circleAverage_fun_smul, smul_eq_mul]
    rw [show (fun w : ℂ => -γ * Real.log ‖w - z‖ + γ * Real.log (max 1 ‖w‖)) =
        fun w => (-γ * Real.log ‖w - z‖) + (γ * Real.log (max 1 ‖w‖)) from rfl,
      Real.circleAverage_fun_add hA hV, hscal]
    ring
  rw [heq] at hW
  exact hW

/-- Locality of the Weyl density: if the shift `γ log max(1,|·|)` vanishes on `D`, the weighted measure agrees
with `μ` on `D`. -/
theorem restrict_withDensity_exp_of_zero (μ : Measure ℂ) {D : Set ℂ} (hD : MeasurableSet D) {g : ℂ → ℝ}
    (hg : ∀ x ∈ D, g x = 0) (γ : ℝ) :
    (μ.withDensity fun w => ENNReal.ofReal (Real.exp (γ * g w))).restrict D = μ.restrict D := by
  rw [restrict_withDensity hD]
  have hae : (fun w => ENNReal.ofReal (Real.exp (γ * g w))) =ᵐ[μ.restrict D] fun _ => 1 := by
    refine ae_restrict_of_forall_mem hD (fun x hx => ?_)
    simp [hg x hx]
  rw [withDensity_congr_ae hae, withDensity_const, one_smul]

/-- Pure measure identity on a window: if `κ` restricted to `D` is `a • (μz).restrict D` with `μz` the weighted
translate `c • ν.map (· + z)` (weight `1` on `D`), then for a measurable `B` with `B - z ⊆ D`,
`κ((· - z)⁻¹' B) = a * (c * ν B)`. -/
theorem kappa_preimage_eq {κ' ν : Measure ℂ} {z : ℂ} {D : Set ℂ} (hD : MeasurableSet D) {a c : ENNReal}
    {g : ℂ → ℝ} (hg : ∀ x ∈ D, g x = 0) (γ : ℝ)
    (h : κ'.restrict D = a • ((c • ν.map (fun x => x + z)).withDensity fun w =>
      ENNReal.ofReal (Real.exp (γ * g w))).restrict D)
    {B : Set ℂ} (hB : MeasurableSet B) (hBD : (fun w => w - z) ⁻¹' B ⊆ D) :
    κ' ((fun w => w - z) ⁻¹' B) = a * (c * ν B) := by
  have hpre : MeasurableSet ((fun w => w - z) ⁻¹' B) := hB.preimage (measurable_id.sub_const z)
  have hpre' : (fun x => x + z) ⁻¹' ((fun w => w - z) ⁻¹' B) = B := by
    ext x
    simp
  have h1 : (κ'.restrict D) ((fun w => w - z) ⁻¹' B) = κ' ((fun w => w - z) ⁻¹' B) := by
    rw [Measure.restrict_apply' hD, inter_eq_left.2 hBD]
  have h2 : ((c • ν.map (fun x => x + z)).restrict D) ((fun w => w - z) ⁻¹' B) =
      c * ν B := by
    rw [Measure.restrict_apply' hD, inter_eq_left.2 hBD, Measure.smul_apply, smul_eq_mul,
      Measure.map_apply (measurable_add_const z) hpre, hpre']
  rw [← h1, h, Measure.smul_apply, smul_eq_mul, restrict_withDensity_exp_of_zero _ hD hg γ, h2]

/-- **Positivity and finiteness of the centred LQG mass of a bounded window (derived; replaces the former input `hPF`).**
Let `S` be bounded and contain a closed dyadic square `Q`. For the centred LQG measure `ν` of a whole-plane field
(`IsLQGMeasureOfField P γ γ hcirc ν`, insertion `γ` at the origin), almost surely `0 < ν ω S < ∞`. Positivity: the frozen
full-support statement `LQGMeasureSquarePositiveFrozen` (Rhodes-Vargas, arXiv:1305.6221 Thm 2.12) on `Q`, then monotonicity.
Finiteness: the local finiteness field `isLocallyFiniteMeasure` of `IsLQGLimit` on the compact closure of `S`. The statement
is false for an unbounded `S` (or a null `S`), which is why the geometric hypotheses `hSb`, `hSQ` are threaded from the call
sites (the windows are closed dyadic squares or closed balls). -/
theorem ae_lqgMeasure_pos_lt_top (hPos : LQGMeasureSquarePositiveFrozen.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc)
    {ν : Ω → Measure ℂ} (hν : IsLQGMeasureOfField P γ γ hcirc ν) {S : Set ℂ}
    (hSb : Bornology.IsBounded S) (hSQ : ∃ Q : Set ℂ, IsClosedDyadicSquare Q ∧ Q ⊆ S) :
    ∀ᵐ ω ∂P, 0 < ν ω S ∧ ν ω S < ∞ := by
  obtain ⟨Q, hQ, hQS⟩ := hSQ
  have hpos := hPos γ γ hγ0 hγ2 (S11c.gamma_lt_lqgQ hγ0 hγ2) Ω P hC hcirc ν hG hν Q hQ
  have hν' : ∀ᵐ ω ∂P, IsLQGLimit γ (fun r z => fieldCircleAverage γ (hcirc ω) r z) (ν ω) := hν
  filter_upwards [hpos, hν'] with ω hposω hνω
  have hfin : IsLocallyFiniteMeasure (ν ω) := hνω.isLocallyFiniteMeasure
  refine ⟨lt_of_lt_of_le hposω (measure_mono hQS), ?_⟩
  exact lt_of_le_of_lt (measure_mono subset_closure) hSb.isCompact_closure.measure_lt_top

/-- **Section 4.4, measure clause of the base conullity.** For almost every root `z` in the disc `U = ball c₁ r₁`
(the rooted decoder clause of `LocalMeasureKernelStmt` at background `0`, with decoder `κ` on the window
`D = ball c₂ r₂`), almost surely the translated field satisfies the measure clause `rootedMeasureIdent`
of the rooted local identification event.

Inputs (all named, none proved here): the rooted decoder clause `hκ` (Frozen `LocalMeasureKernelStmt`, second
conjunct, background `0`); the coordinate change `hCC` and the existence `hνex` of the centred LQG measure
(Proposed `LQGMeasureCoordChange`, `LQGMeasureExistence`); the canonical identification `hIdγ` at insertion `γ`
(`LQGCanonicalIdentificationStmt`) with a metric existence `hDex` (the premise of `hIdγ`); and positivity and
finiteness of the centred LQG mass of the window `hPF` (pending, see the report). -/
theorem ae_rootedMeasureIdent_base {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {γ ξ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) {c₁ c₂ : ℂ} {r₁ r₂ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc)
    (hD1 : closedBall c₂ r₂ ⊆ ball (0 : ℂ) 1)
    (κ : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) → Measure ℂ)
    (hκ : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), ∀ μz : Ω → Measure ℂ,
      IsLQGMeasure P γ (fun ω => addCircleAverage (fieldCircleAverage 0 (hcirc ω))
        (fun w => -γ * Real.log ‖w - z‖ + γ * Real.log (max 1 ‖w‖))) μz →
        ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧
          (κ (campbellReferenceObs γ 0 (ball c₂ r₂) (hC ω) z).2).restrict (ball c₂ r₂) =
            ENNReal.ofReal a • (μz ω).restrict (ball c₂ r₂))
    (hCC : ∀ z : ℂ, LQGMeasureCoordChange P γ γ (S11c.translatedPairing hC hcirc z) (S11c.translatedCircle hcirc z))
    (hνex : ∀ z : ℂ, LQGMeasureExistence P γ γ (S11c.translatedPairing hC hcirc z) (S11c.translatedCircle hcirc z))
    (Dμ : S11n.CanonSpace → Measure ℂ) (Dd : S11n.CanonSpace → ℂ → ℂ → ℝ)
    (hIdγ : S11n.LQGCanonicalIdentificationStmt.{u} γ ξ γ Dμ Dd)
    (hDex : ∀ z : ℂ, ∃ D : Ω → ℂ → ℂ → ℝ, IsLQGMetricOfField P γ ξ γ (S11c.translatedPairing hC hcirc z) D)
    (S : Set ℂ) (hS : MeasurableSet S) (A : ℕ → Set ℂ) (hA : ∀ n, MeasurableSet (A n) ∧ A n ⊆ S)
    (hSD : ∀ z ∈ ball c₁ r₁, (fun w => w - z) ⁻¹' S ⊆ ball c₂ r₂)
    (hPos : LQGMeasureSquarePositiveFrozen.{u}) (hSb : Bornology.IsBounded S)
    (hSQ : ∃ Q : Set ℂ, IsClosedDyadicSquare Q ∧ Q ⊆ S) :
    ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), ∀ᵐ ω ∂P,
      rootedMeasureIdent (ball c₂ r₂) κ Dμ γ z S A (S11c.translatedPairing hC hcirc z ω) := by
  filter_upwards [hκ, ae_restrict_mem measurableSet_ball] with z hz hzU
  have hG' := S11c.isWholePlaneGFF_translate hG z
  obtain ⟨ν, hν⟩ := hνex z hG' hγ0 hγ2 (S11c.gamma_lt_lqgQ hγ0 hγ2)
  obtain ⟨D, hDz⟩ := hDex z
  have hPFω := ae_lqgMeasure_pos_lt_top hPos hγ0 hγ2 hG' hν hSb hSQ
  have hIdω := hIdγ Ω P _ _ ν D hG' hν hDz
  have hμz := ae_isLQGLimit_rootedMax hγ0 hγ2 hG z (hCC z) hν
  have hκω := hz (fun ω => (ENNReal.ofReal (Real.exp (γ * hcirc ω 1 z)) • (ν ω).map (fun x => x + z)).withDensity
    fun w => ENNReal.ofReal (Real.exp (γ * (γ * Real.log (max 1 ‖w‖))))) hμz
  filter_upwards [hPFω, hIdω, hκω] with ω hPFω' hIdω' hκω'
  obtain ⟨a', b, ha', -, hνω, -⟩ := hIdω'
  obtain ⟨a, ha, hκeq⟩ := hκω'
  have hνω' : ν ω = ENNReal.ofReal a' • Dμ (canonFieldOf γ (S11c.translatedPairing hC hcirc z ω)) := hνω
  have hνB : ∀ B : Set ℂ, ν ω B = ENNReal.ofReal a' * Dμ (canonFieldOf γ (S11c.translatedPairing hC hcirc z ω)) B :=
    fun B => by rw [hνω', Measure.smul_apply, smul_eq_mul]
  have hobs : rootedLocalObs γ (ball c₂ r₂) z (S11c.translatedPairing hC hcirc z ω) =
      (campbellReferenceObs γ 0 (ball c₂ r₂) (hC ω) z).2 :=
    funext (rootedLocalObs_translated hC hcirc γ (ball c₂ r₂) z ω)
  have hgD : ∀ x ∈ ball c₂ r₂, γ * Real.log (max 1 ‖x‖) = 0 := by
    intro x hx
    have hx1 : x ∈ ball (0 : ℂ) 1 := hD1 (ball_subset_closedBall hx)
    rw [mem_ball_zero_iff] at hx1
    rw [max_eq_left hx1.le, Real.log_one, mul_zero]
  have hkey : ∀ B : Set ℂ, MeasurableSet B → B ⊆ S →
      (κ (campbellReferenceObs γ 0 (ball c₂ r₂) (hC ω) z).2) ((fun w => w - z) ⁻¹' B) =
        ENNReal.ofReal a * (ENNReal.ofReal (Real.exp (γ * hcirc ω 1 z)) * ν ω B) := by
    intro B hB hBS
    have hBD : (fun w => w - z) ⁻¹' B ⊆ ball c₂ r₂ := (preimage_mono hBS).trans (hSD z hzU)
    rw [kappa_preimage_eq measurableSet_ball hgD γ hκeq hB hBD]
  unfold rootedMeasureIdent
  rw [hobs]
  have hpos : 0 < ν ω S := hPFω'.1
  have hfin : ν ω S < ∞ := hPFω'.2
  have hκS := hkey S hS subset_rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine pos_iff_ne_zero.2 (fun h0 => ?_)
    rw [hνB, h0, mul_zero] at hpos
    exact lt_irrefl _ hpos
  · refine lt_top_iff_ne_top.2 (fun htop => ?_)
    rw [hνB, htop, ENNReal.mul_top (ENNReal.ofReal_pos.2 ha').ne'] at hfin
    exact lt_irrefl _ hfin
  · rw [hκS]
    exact ENNReal.mul_pos (ENNReal.ofReal_pos.2 ha).ne'
      (ENNReal.mul_pos (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne' hpos.ne').ne'
  · rw [hκS]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin)
  · intro n
    rw [hkey (A n) (hA n).1 (hA n).2, hκS, hνB, hνB]
    ring

/-! ### Section 4.4, metric clause of the base conullity -/

/-- **Deterministic core of the metric clause.** Given the rooted clause on the window `W` (`hcl`), the locality of the
internal metric under translation and constant shift (`hloc`), and the centred identification `Dc = b' · Dd'` (`hDcd`),
the rooted metric identity holds for a radius `R k` below the no-shortcut radius of the centred metric `Dc`
(`eq_internalMetric_on_small_ball`), with the ENNReal form of the decoder (`rootedMetricAt`). -/
theorem rootedMetricIdent_of_internal {W : Set ℂ} (hW : IsOpen W) {z : ℂ} (hzW : z ∈ W) {γ : ℝ}
    (m : (MeanZeroTest W → ℝ) → C(↥(W ×ˢ W), ℝ)) (T : (ℂ → ℝ) → ℝ) (Dz Dc Dd' : ℂ → ℂ → ℝ) (b b' κ : ℝ)
    (hb' : 0 < b') (hDc : IsEuclideanLengthMetric Dc) (hDcnn : ∀ u v, 0 ≤ Dc u v)
    (hDcd : ∀ u v, Dc u v = b' * Dd' u v)
    (hcl : ∀ x y : ℂ, x ∈ W → y ∈ W → rootedMetricAt W m γ z T x y = ENNReal.ofReal b * internalMetric Dz W x y)
    (hloc : ∀ x y : ℂ, x + z ∈ W → y + z ∈ W →
      internalMetric Dz W (x + z) (y + z) = ENNReal.ofReal κ * internalMetric Dc ((fun u => u + z) ⁻¹' W) x y)
    (X : ℕ → ℂ) (R : ℕ → ℝ) (pq : ℕ → ℂ × ℂ) (hRlim : Filter.Tendsto R Filter.atTop (nhds 0))
    (hpq : ∀ k, ‖(pq k).1‖ < R k ∧ ‖(pq k).2‖ < R k ∧ (pq k).1 ≠ (pq k).2 ∧
      (pq k).1 + z ∈ W ∧ (pq k).2 + z ∈ W) :
    ∃ k : ℕ, ‖(pq k).1‖ < R k ∧ ‖(pq k).2‖ < R k ∧ (pq k).1 + z ∈ W ∧ (pq k).2 + z ∈ W ∧
      0 < Dd' (pq k).1 (pq k).2 ∧
      ∀ i j : ℕ, ‖X i‖ < R k → ‖X j‖ < R k → X i + z ∈ W → X j + z ∈ W →
        rootedMetricAt W m γ z T (X i + z) (X j + z) * ENNReal.ofReal (Dd' (pq k).1 (pq k).2) =
          ENNReal.ofReal (Dd' (X i) (X j)) * rootedMetricAt W m γ z T ((pq k).1 + z) ((pq k).2 + z) := by
  have hU : IsOpen ((fun u => u + z) ⁻¹' W) := hW.preimage (continuous_id.add continuous_const)
  have h0 : (0 : ℂ) ∈ (fun u => u + z) ⁻¹' W := by simpa using hzW
  obtain ⟨ρ, hρ, hNS⟩ := eq_internalMetric_on_small_ball hDc hU h0
  have key : ∀ x y : ℂ, ‖x‖ < ρ → ‖y‖ < ρ → x + z ∈ W → y + z ∈ W →
      rootedMetricAt W m γ z T (x + z) (y + z) =
        ENNReal.ofReal b * (ENNReal.ofReal κ * ENNReal.ofReal (b' * Dd' x y)) := by
    intro x y hx hy hxW hyW
    rw [hcl (x + z) (y + z) hxW hyW, hloc x y hxW hyW,
      ← hNS x (mem_closedBall_zero_iff.2 hx.le) y (mem_closedBall_zero_iff.2 hy.le), hDcd x y]
  obtain ⟨k, hk⟩ : ∃ k, R k < ρ := (hRlim.eventually (gt_mem_nhds hρ)).exists
  refine ⟨k, (hpq k).1, (hpq k).2.1, (hpq k).2.2.2.1, (hpq k).2.2.2.2, ?_, ?_⟩
  · have h1 : 0 < Dc (pq k).1 (pq k).2 :=
      lt_of_le_of_ne (hDcnn _ _) (fun h => (hpq k).2.2.1 (hDc.eq_of_eq_zero _ _ h.symm))
    rw [hDcd] at h1
    exact pos_of_mul_pos_right h1 hb'.le
  · intro i j hXi hXj hXiW hXjW
    have hp1 : ‖(pq k).1‖ < ρ := (hpq k).1.trans hk
    have hp2 : ‖(pq k).2‖ < ρ := (hpq k).2.1.trans hk
    rw [key (X i) (X j) (hXi.trans hk) (hXj.trans hk) hXiW hXjW,
      key (pq k).1 (pq k).2 hp1 hp2 (hpq k).2.2.2.1 (hpq k).2.2.2.2]
    simp only [ENNReal.ofReal_mul hb'.le]
    ring

/-- **Section 4.4, metric clause of the base conullity.** For almost every root `z` in the disc, almost surely the
translated field satisfies the metric clause `rootedMetricIdent` of the rooted local identification event.

Inputs (named, none proved here): the rooted clause (20) of `LocalMetricReplacementStmt` at background `0`, `hclause`;
the locality of the internal metric under translation and constant shift, `hLoc` (derived, see `RootedTranslate.lean`; Fact 2.2 II
of arXiv:2208.11795, with the translation covariance (Fact 2.2 IV) and the additive-constant rule of the Weyl scaling);
the Proposed metric field axioms `hAx` (item I: finiteness and length metric); the canonical identification `hIdγ` at
insertion `γ` with the centred metric; the measure existence `hνex` (premise of `hIdγ`). -/
theorem ae_rootedMetricIdent_base {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {γ ξ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) {c₁ c₂ : ℂ} {r₁ r₂ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc)
    (hsub : closedBall c₁ r₁ ⊆ ball c₂ r₂) (hD1 : closedBall c₂ r₂ ⊆ ball (0 : ℂ) 1)
    {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (m : (MeanZeroTest (ball c₂ r₂) → ℝ) → C(↥(ball c₂ r₂ ×ˢ ball c₂ r₂ : Set (ℂ × ℂ)), ℝ))
    (hclause : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), ∀ᵐ ω ∂P, ∃ b : ℝ, 0 < b ∧
      ∀ p : ↥(ball c₂ r₂ ×ˢ ball c₂ r₂ : Set (ℂ × ℂ)),
        ENNReal.ofReal (m (campbellReferenceObs γ 0 (ball c₂ r₂) (hC ω) z).2 p) =
          ENNReal.ofReal b * internalMetric (rootedWeylMetric 𝔇 ξ γ hC z ω) (ball c₂ r₂) p.1.1 p.1.2)
    (hXi : LQGMetricExponentPositive) (hField : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hU : LQGMetricSatisfiesAxiomsUnivFrozen.{u}) (hLenFr : LQGMetricLengthUnivFrozen.{u})
    (hRootFr : RootedPhysicalMetricContinuousAtInsertionFrozen.{u})
    (hComp : WeylMetricCompositionContinuousOuterFrozen)
    (hAx : ∀ z : ℂ, LQGMetricFieldAxioms P γ ξ γ (S11c.translatedPairing hC hcirc z)
      (S11c.translatedCircle hcirc z))
    (hνex : ∀ z : ℂ, LQGMeasureExistence P γ γ (S11c.translatedPairing hC hcirc z)
      (S11c.translatedCircle hcirc z))
    (Dμ : S11n.CanonSpace → Measure ℂ) (Dd : S11n.CanonSpace → ℂ → ℂ → ℝ)
    (hIdγ : S11n.LQGCanonicalIdentificationStmt.{u} γ ξ γ Dμ Dd)
    (X : ℕ → ℂ) (R : ℕ → ℝ) (pq : ℕ → ℂ × ℂ) (hRlim : Filter.Tendsto R Filter.atTop (nhds 0))
    (hpq : ∀ z ∈ ball c₁ r₁, ∀ k, ‖(pq k).1‖ < R k ∧ ‖(pq k).2‖ < R k ∧ (pq k).1 ≠ (pq k).2 ∧
      (pq k).1 + z ∈ ball c₂ r₂ ∧ (pq k).2 + z ∈ ball c₂ r₂) :
    ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), ∀ᵐ ω ∂P,
      rootedMetricIdent (ball c₂ r₂) m Dd γ z X R pq (S11c.translatedPairing hC hcirc z ω) := by
  -- the locality clause `hLoc` (V_z form), derived from `ae_rootedWeylMetric_internalMetric_translate`
  have hLoc : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), ∀ᵐ ω ∂P, ∃ κ : ℝ, 0 < κ ∧ ∀ x y : ℂ,
      x + z ∈ ball c₂ r₂ → y + z ∈ ball c₂ r₂ →
        internalMetric (rootedWeylMetric 𝔇 ξ γ hC z ω) (ball c₂ r₂) (x + z) (y + z) =
          ENNReal.ofReal κ * internalMetric (centredWeylMetric 𝔇 ξ γ hC hcirc z ω)
            ((fun u => u + z) ⁻¹' ball c₂ r₂) x y := by
    have hz0 : ∀ᵐ z ∂(volume : Measure ℂ), z ≠ 0 := by
      rw [ae_iff]
      simp
    filter_upwards [ae_restrict_of_ae hz0] with z hz
    filter_upwards [ae_rootedWeylMetric_internalMetric_translate hγ0 hγ2 hD1 hG h𝔇 hXi hField hU hLenFr
      hRootFr hComp hz] with ω hω
    exact ⟨Real.exp (ξ * hcirc ω 1 z), Real.exp_pos _, fun x y h1 h2 => hω x y h1 h2⟩
  filter_upwards [hclause, hLoc, ae_restrict_mem measurableSet_ball] with z hclz hlocz hzU
  have hW' := S11c.isWholePlaneGFF_translate hG z
  have hlt := S11c.gamma_lt_lqgQ hγ0 hγ2
  obtain ⟨ν, hν⟩ := hνex z hW' hγ0 hγ2 hlt
  have hAxz := hAx z hW' hγ0 hγ2 hlt 𝔇 h𝔇
  have hzW : z ∈ ball c₂ r₂ := hsub (ball_subset_closedBall hzU)
  have hDmet : IsLQGMetricOfField P γ ξ γ (S11c.translatedPairing hC hcirc z)
      (fun ω => centredWeylMetric 𝔇 ξ γ hC hcirc z ω) := by
    refine ⟨𝔇, h𝔇, ?_⟩
    filter_upwards [hAxz.1] with ω hω
    intro u v
    exact ⟨ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (hω.1 u v).ne⟩
  have hIdω := hIdγ Ω P (S11c.translatedPairing hC hcirc z) (S11c.translatedCircle hcirc z) ν
    (fun ω => centredWeylMetric 𝔇 ξ γ hC hcirc z ω) hW' hν hDmet
  filter_upwards [hclz, hlocz, hIdω, hAxz.1] with ω hclω hlocω hIdω' hI'
  obtain ⟨b, hb, hclω⟩ := hclω
  obtain ⟨κ, -, hlocω⟩ := hlocω
  obtain ⟨a, b', -, hb', -, hbω⟩ := hIdω'
  have hobs : rootedLocalObs γ (ball c₂ r₂) z (S11c.translatedPairing hC hcirc z ω) =
      (campbellReferenceObs γ 0 (ball c₂ r₂) (hC ω) z).2 :=
    funext (rootedLocalObs_translated hC hcirc γ (ball c₂ r₂) z ω)
  have hcl : ∀ x y : ℂ, x ∈ ball c₂ r₂ → y ∈ ball c₂ r₂ →
      rootedMetricAt (ball c₂ r₂) m γ z (S11c.translatedPairing hC hcirc z ω) x y =
        ENNReal.ofReal b * internalMetric (rootedWeylMetric 𝔇 ξ γ hC z ω) (ball c₂ r₂) x y := by
    intro x y hx hy
    have hmem : (x, y) ∈ ball c₂ r₂ ×ˢ ball c₂ r₂ := ⟨hx, hy⟩
    have hval : rootedMetricAt (ball c₂ r₂) m γ z (S11c.translatedPairing hC hcirc z ω) x y =
        ENNReal.ofReal (m (rootedLocalObs γ (ball c₂ r₂) z (S11c.translatedPairing hC hcirc z ω))
          ⟨(x, y), hmem⟩) := by
      simp [rootedMetricAt, hmem]
    rw [hval, hobs]
    exact hclω ⟨(x, y), hmem⟩
  have hDcd : ∀ u v, centredWeylMetric 𝔇 ξ γ hC hcirc z ω u v =
      b' * Dd (canonFieldOf γ (S11c.translatedPairing hC hcirc z ω)) u v :=
    fun u v => hbω u v
  have hDcnn : ∀ u v, 0 ≤ centredWeylMetric 𝔇 ξ γ hC hcirc z ω u v :=
    fun u v => ENNReal.toReal_nonneg
  unfold rootedMetricIdent
  exact rootedMetricIdent_of_internal isOpen_ball hzW m (S11c.translatedPairing hC hcirc z ω)
    (rootedWeylMetric 𝔇 ξ γ hC z ω) (centredWeylMetric 𝔇 ξ γ hC hcirc z ω)
    (fun u v => Dd (canonFieldOf γ (S11c.translatedPairing hC hcirc z ω)) u v) b b' κ hb'
    (hI'.2) hDcnn hDcd hcl (fun x y hx hy => hlocω x y hx hy) X R pq hRlim (hpq z hzU)

/-! ### Section 4.4, joint base conullity and transfer to admissible shifts

`ae_rootedLocalIdent_base` assembles the measure and metric clauses. `ae_rootedLocalIdent_shifted_all` transfers the event
to all admissible root shifts, the null set of roots not depending on the shift. The converse `rootedMeasureIdent_restrict`
(Section 4.3 (3)) turns the cross-multiplied measure clause into a proportionality on `S`, using a countable generating
π-system `f` of the Borel sets (`exists_countable_piSystem_complex`). -/

/-- **Section 4.4, base conullity (measure and metric).** For a.e. root `z` in the disc, almost surely the translated field
lies in the rooted local identification event: the measure clause (`ae_rootedMeasureIdent_base`) and the metric clause
(`ae_rootedMetricIdent_base`) hold together. The locality input `hLoc` (derived in `RootedTranslate.lean` from the frozen field axioms) and the Proposed metric
axioms `hAx` enter through the metric clause only. -/
theorem ae_rootedLocalIdent_base {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {γ ξ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) {c₁ c₂ : ℂ} {r₁ r₂ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc)
    (hD1 : closedBall c₂ r₂ ⊆ ball (0 : ℂ) 1) (hsub : closedBall c₁ r₁ ⊆ ball c₂ r₂)
    (κ : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) → Measure ℂ)
    (hκ : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), ∀ μz : Ω → Measure ℂ,
      IsLQGMeasure P γ (fun ω => addCircleAverage (fieldCircleAverage 0 (hcirc ω))
        (fun w => -γ * Real.log ‖w - z‖ + γ * Real.log (max 1 ‖w‖))) μz →
        ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧
          (κ (campbellReferenceObs γ 0 (ball c₂ r₂) (hC ω) z).2).restrict (ball c₂ r₂) =
            ENNReal.ofReal a • (μz ω).restrict (ball c₂ r₂))
    {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (m : (MeanZeroTest (ball c₂ r₂) → ℝ) → C(↥(ball c₂ r₂ ×ˢ ball c₂ r₂ : Set (ℂ × ℂ)), ℝ))
    (hclause : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), ∀ᵐ ω ∂P, ∃ b : ℝ, 0 < b ∧
      ∀ p : ↥(ball c₂ r₂ ×ˢ ball c₂ r₂ : Set (ℂ × ℂ)),
        ENNReal.ofReal (m (campbellReferenceObs γ 0 (ball c₂ r₂) (hC ω) z).2 p) =
          ENNReal.ofReal b * internalMetric (rootedWeylMetric 𝔇 ξ γ hC z ω) (ball c₂ r₂) p.1.1 p.1.2)
    (hXi : LQGMetricExponentPositive) (hField : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hU : LQGMetricSatisfiesAxiomsUnivFrozen.{u}) (hLenFr : LQGMetricLengthUnivFrozen.{u})
    (hRootFr : RootedPhysicalMetricContinuousAtInsertionFrozen.{u})
    (hComp : WeylMetricCompositionContinuousOuterFrozen)
    (hAx : ∀ z : ℂ, LQGMetricFieldAxioms P γ ξ γ (S11c.translatedPairing hC hcirc z)
      (S11c.translatedCircle hcirc z))
    (hCC : ∀ z : ℂ, LQGMeasureCoordChange P γ γ (S11c.translatedPairing hC hcirc z) (S11c.translatedCircle hcirc z))
    (hνex : ∀ z : ℂ, LQGMeasureExistence P γ γ (S11c.translatedPairing hC hcirc z) (S11c.translatedCircle hcirc z))
    (Dμ : S11n.CanonSpace → Measure ℂ) (Dd : S11n.CanonSpace → ℂ → ℂ → ℝ)
    (hIdγ : S11n.LQGCanonicalIdentificationStmt.{u} γ ξ γ Dμ Dd)
    (hDex : ∀ z : ℂ, ∃ D : Ω → ℂ → ℂ → ℝ, IsLQGMetricOfField P γ ξ γ (S11c.translatedPairing hC hcirc z) D)
    (S : Set ℂ) (hS : MeasurableSet S) (A : ℕ → Set ℂ) (hA : ∀ n, MeasurableSet (A n) ∧ A n ⊆ S)
    (hSD : ∀ z ∈ ball c₁ r₁, (fun w => w - z) ⁻¹' S ⊆ ball c₂ r₂)
    (hPos : LQGMeasureSquarePositiveFrozen.{u}) (hSb : Bornology.IsBounded S)
    (hSQ : ∃ Q : Set ℂ, IsClosedDyadicSquare Q ∧ Q ⊆ S)
    (X : ℕ → ℂ) (R : ℕ → ℝ) (pq : ℕ → ℂ × ℂ) (hRlim : Filter.Tendsto R Filter.atTop (nhds 0))
    (hpq : ∀ z ∈ ball c₁ r₁, ∀ k, ‖(pq k).1‖ < R k ∧ ‖(pq k).2‖ < R k ∧ (pq k).1 ≠ (pq k).2 ∧
      (pq k).1 + z ∈ ball c₂ r₂ ∧ (pq k).2 + z ∈ ball c₂ r₂) :
    ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), ∀ᵐ ω ∂P,
      rootedLocalIdentEvent (ball c₂ r₂) κ m Dμ Dd γ z S A X R pq (S11c.translatedPairing hC hcirc z ω) := by
  filter_upwards [ae_rootedMeasureIdent_base hγ0 hγ2 hG hD1 κ hκ hCC hνex Dμ Dd hIdγ hDex S hS A hA hSD hPos hSb hSQ,
    ae_rootedMetricIdent_base hγ0 hγ2 hG hsub hD1 h𝔇 m hclause hXi hField hU hLenFr hRootFr hComp hAx hνex Dμ Dd
      hIdγ X R pq hRlim hpq]
    with z hz1 hz2
  filter_upwards [hz1, hz2] with ω h1 h2
  exact ⟨h1, h2⟩

/-- **Section 4.4, transfer of the base conullity to all admissible root shifts.** The null set of roots does not depend
on the shift `(b, u)`: for a.e. root `z` and every admissible root shift `u` at `z`, almost surely the root-shifted field
`addFunPairing (translatedPairing hC hcirc z ω) u` lies in the rooted local identification event. This is the ordering of
quantifiers of `hRLI` (`hMass_of_rootedLocalIdent` in S11at.lean). The only transfer is the Cameron-Martin step
`ae_rootedLocalIdent_shifted`, applied for each fixed `(z, b, u)`. -/
theorem ae_rootedLocalIdent_shifted_all {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hCM : CameronMartinGFFMutualAbsCont.{u}) {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hG : IsWholePlaneGFF P hC hcirc) {α₀ γ : ℝ} {c₁ c₂ : ℂ} {r₁ r₂ : ℝ}
    (κ : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) → Measure ℂ)
    (m : (MeanZeroTest (ball c₂ r₂) → ℝ) → C(↥(ball c₂ r₂ ×ˢ ball c₂ r₂ : Set (ℂ × ℂ)), ℝ))
    (Dμ : S11n.CanonSpace → Measure ℂ) (Dd : S11n.CanonSpace → ℂ → ℂ → ℝ)
    (S : Set ℂ) (A : ℕ → Set ℂ) (X : ℕ → ℂ) (R : ℕ → ℝ) (pq : ℕ → ℂ × ℂ)
    (hκm : Measurable κ) (hmm : Measurable m) (hDμ : Measurable Dμ)
    (hDd : ∀ x y : ℂ, Measurable fun L : S11n.CanonSpace => Dd L x y) (hS : MeasurableSet S)
    (hA : ∀ n, MeasurableSet (A n))
    (hbase : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), ∀ᵐ ω ∂P,
      S11c.translatedPairing hC hcirc z ω ∈ rootedLocalIdentEvent (ball c₂ r₂) κ m Dμ Dd γ z S A X R pq) :
    ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), ∀ (b : ℝ) (u : ℂ → ℝ),
      FirstPassS11ai.AdmissibleRootShift α₀ z b u →
        ∀ᵐ ω ∂P, addFunPairing (S11c.translatedPairing hC hcirc z ω) u ∈
          rootedLocalIdentEvent (ball c₂ r₂) κ m Dμ Dd γ z S A X R pq := by
  filter_upwards [hbase] with z hz b u hadm
  exact ae_rootedLocalIdent_shifted P hCM (S11c.isWholePlaneGFF_translate hG z) hadm
    (measurableSet_rootedLocalIdentEvent (ball c₂ r₂) κ m Dμ Dd γ z S A X R pq hκm hmm hDμ hDd hS hA) hz

/-- **A countable generating π-system of `ℂ`.** The finite intersections of the countable basis `countableBasis ℂ`
(together with `univ`), enumerated by `ℕ`: closed under pairwise intersection, containing `univ`, and generating the
Borel σ-algebra. -/
theorem exists_countable_piSystem_complex :
    ∃ f : ℕ → Set ℂ, (∀ m n, ∃ k, f k = f m ∩ f n) ∧ (∃ n, f n = univ) ∧
      borel ℂ = MeasurableSpace.generateFrom (Set.range f) := by
  set 𝔅 := TopologicalSpace.countableBasis ℂ with h𝔅
  set Pfam : Set (Set ℂ) := (fun F : Set (Set ℂ) => ⋂₀ F) '' {F | F.Finite ∧ F ⊆ 𝔅} with hPfam
  have hc : Pfam.Countable :=
    (Set.countable_ofPred_finite_subset (TopologicalSpace.countable_countableBasis ℂ)).image _
  have hne : Pfam.Nonempty := ⟨⋂₀ ∅, ∅, ⟨Set.finite_empty, Set.empty_subset _⟩, rfl⟩
  obtain ⟨f, hf⟩ := hc.exists_eq_range hne
  have hfm : ∀ m, f m ∈ Pfam := fun m => by rw [hf]; exact ⟨m, rfl⟩
  have hmem : ∀ s ∈ Pfam, ∃ F : Set (Set ℂ), F.Finite ∧ F ⊆ 𝔅 ∧ s = ⋂₀ F := by
    rintro s ⟨F, ⟨hF, hFB⟩, rfl⟩
    exact ⟨F, hF, hFB, rfl⟩
  have hopen : ∀ s ∈ Pfam, IsOpen s := by
    intro s hs
    obtain ⟨F, hF, hFB, rfl⟩ := hmem s hs
    exact hF.isOpen_sInter fun t ht => (TopologicalSpace.isBasis_countableBasis ℂ).isOpen (hFB ht)
  refine ⟨f, ?_, ?_, ?_⟩
  · intro m n
    obtain ⟨F, hF, hFB, hFm⟩ := hmem _ (hfm m)
    obtain ⟨G, hG, hGB, hGn⟩ := hmem _ (hfm n)
    have hmem' : f m ∩ f n ∈ Pfam :=
      ⟨F ∪ G, ⟨hF.union hG, Set.union_subset hFB hGB⟩, by
        show ⋂₀ (F ∪ G) = f m ∩ f n
        rw [hFm, hGn, Set.sInter_union]⟩
    rw [hf] at hmem'
    obtain ⟨k, hk⟩ := hmem'
    exact ⟨k, hk⟩
  · have hu : (Set.univ : Set ℂ) ∈ Pfam :=
      ⟨∅, ⟨Set.finite_empty, Set.empty_subset _⟩, Set.sInter_empty⟩
    rw [hf] at hu
    exact hu
  · have hB := TopologicalSpace.isBasis_countableBasis ℂ
    have hsub : TopologicalSpace.countableBasis ℂ ⊆ Pfam := fun B hB' =>
      ⟨{B}, ⟨Set.finite_singleton B, Set.singleton_subset_iff.2 hB'⟩, Set.sInter_singleton B⟩
    rw [← hf]
    refine le_antisymm ?_ (MeasurableSpace.generateFrom_le fun s hs => (hopen s hs).measurableSet)
    rw [hB.borel_eq_generateFrom]
    exact MeasurableSpace.generateFrom_mono hsub

/-- The π-system `{(f m ∩ S) ∪ (f n ∩ Sᶜ)}` built from a family `f` and a set `S`. -/
def restrictPiFamily (S : Set ℂ) (f : ℕ → Set ℂ) : Set (Set ℂ) :=
  {s | ∃ m n, s = (f m ∩ S) ∪ (f n ∩ Sᶜ)}

theorem mem_restrictPiFamily_iff {S : Set ℂ} {f : ℕ → Set ℂ} {s : Set ℂ} :
    s ∈ restrictPiFamily S f ↔ ∃ m n, s = (f m ∩ S) ∪ (f n ∩ Sᶜ) := Iff.rfl

/-- **Uniqueness on a window (Section 4.3 (3), converse).** Let `f` be a countable generating π-system of the Borel sets.
If two finite measures `ν`, `K` satisfy `ν(f n ∩ S) K(S) = K(f n ∩ S) ν(S)` for all `n`, with `0 < K(S) < ∞` and
`ν(S) < ∞`, then `ν` restricted to `S` is the multiple `(ν(S)/K(S))` of `K` restricted to `S`. The sets
`(f m ∩ S) ∪ (f n ∩ Sᶜ)` form the π-system used, since `ν` and `K` vanish on `Sᶜ` after restriction. -/
theorem restrict_eq_smul_of_ratio {ν K : Measure ℂ} {S : Set ℂ} (hS : MeasurableSet S) {f : ℕ → Set ℂ}
    (hfm : ∀ n, MeasurableSet (f n)) (hπ : ∀ m n, ∃ k, f k = f m ∩ f n) (huniv : ∃ n, f n = univ)
    (hgen : borel ℂ = MeasurableSpace.generateFrom (Set.range f))
    (hKpos : 0 < K S) (hKfin : K S ≠ ∞) (hνfin : ν S ≠ ∞)
    (hratio : ∀ n, ν (f n ∩ S) * K S = K (f n ∩ S) * ν S) :
    ν.restrict S = (ν S / K S) • K.restrict S := by
  have hπSfam : IsPiSystem (restrictPiFamily S f) := by
    intro s hs t ht _
    obtain ⟨m1, n1, rfl⟩ := mem_restrictPiFamily_iff.1 hs
    obtain ⟨m2, n2, rfl⟩ := mem_restrictPiFamily_iff.1 ht
    obtain ⟨k, hk⟩ := hπ m1 m2
    obtain ⟨l, hl⟩ := hπ n1 n2
    refine mem_restrictPiFamily_iff.2 ⟨k, l, ?_⟩
    rw [hk, hl]
    ext x
    simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_compl_iff]
    tauto
  have hgenSfam : borel ℂ = MeasurableSpace.generateFrom (restrictPiFamily S f) := by
    refine le_antisymm ?_ (MeasurableSpace.generateFrom_le ?_)
    · rw [hgen]
      refine MeasurableSpace.generateFrom_le ?_
      intro s hs
      obtain ⟨n, rfl⟩ := hs
      apply MeasurableSpace.measurableSet_generateFrom
      exact mem_restrictPiFamily_iff.2 ⟨n, n, (Set.inter_union_compl _ _).symm⟩
    · intro s hs
      obtain ⟨m, n, rfl⟩ := mem_restrictPiFamily_iff.1 hs
      exact ((hfm m).inter hS).union ((hfm n).inter hS.compl)
  obtain ⟨n0, hn0⟩ := huniv
  have hunivSfam : (Set.univ : Set ℂ) ∈ restrictPiFamily S f :=
    mem_restrictPiFamily_iff.2 ⟨n0, n0, by rw [hn0, Set.univ_inter, Set.univ_inter, Set.union_compl_self]⟩
  refine Measure.ext_of_generateFrom_of_cover_subset (T := {Set.univ}) (BorelSpace.measurable_eq.trans hgenSfam)
    hπSfam (Set.singleton_subset_iff.2 hunivSfam) (Set.countable_singleton _) (Set.sUnion_singleton _) ?_ ?_
  · intro s hs
    rw [Set.mem_singleton_iff.1 hs, Measure.restrict_apply_univ]
    exact hνfin
  · intro s hs
    obtain ⟨m, n, rfl⟩ := mem_restrictPiFamily_iff.1 hs
    have hint : ((f m ∩ S) ∪ (f n ∩ Sᶜ)) ∩ S = f m ∩ S := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_compl_iff]
      tauto
    rw [Measure.restrict_apply' hS, Measure.smul_apply, Measure.restrict_apply' hS, hint, smul_eq_mul]
    have hKne : K S ≠ 0 := hKpos.ne'
    calc ν (f m ∩ S) = ν (f m ∩ S) * K S * (K S)⁻¹ := by
          rw [mul_assoc, ENNReal.mul_inv_cancel hKne hKfin, mul_one]
      _ = K (f m ∩ S) * ν S * (K S)⁻¹ := by rw [hratio m]
      _ = ν S / K S * K (f m ∩ S) := by rw [div_eq_mul_inv]; ring

/-- **Section 4.3 (3), converse: the measure clause gives proportionality on `S`.** If the rooted measure clause
`rootedMeasureIdent` holds for the cross-multiplied family `f n ∩ S` (a countable generating π-system `f`), then the
decoded measure, pushed to centred coordinates, is `c` times the centred canonical measure, restricted to `S`, with
`c > 0` finite. -/
theorem rootedMeasureIdent_restrict {D : Set ℂ} {κ : (MeanZeroTest D → ℝ) → Measure ℂ}
    {Dμ : S11n.CanonSpace → Measure ℂ} {γ : ℝ} {z : ℂ} {S : Set ℂ} {f : ℕ → Set ℂ}
    (hS : MeasurableSet S) (hfm : ∀ n, MeasurableSet (f n)) (hπ : ∀ m n, ∃ k, f k = f m ∩ f n)
    (huniv : ∃ n, f n = univ) (hgen : borel ℂ = MeasurableSpace.generateFrom (Set.range f))
    {T : (ℂ → ℝ) → ℝ} (h : rootedMeasureIdent D κ Dμ γ z S (fun n => f n ∩ S) T) :
    ∃ c : ℝ, 0 < c ∧
      ((κ (rootedLocalObs γ D z T)).map (fun w => w - z)).restrict S =
        ENNReal.ofReal c • (Dμ (canonFieldOf γ T)).restrict S := by
  unfold rootedMeasureIdent at h
  obtain ⟨hKpos, hKfin, hνpos, hνfin, hr⟩ := h
  have hmeas : Measurable (fun w : ℂ => w - z) := by fun_prop
  have hνeq : ∀ B, MeasurableSet B →
      ((κ (rootedLocalObs γ D z T)).map (fun w => w - z)) B =
        κ (rootedLocalObs γ D z T) ((fun w => w - z) ⁻¹' B) :=
    fun B hB => Measure.map_apply hmeas hB
  have hratio : ∀ n, ((κ (rootedLocalObs γ D z T)).map (fun w => w - z)) (f n ∩ S) *
      Dμ (canonFieldOf γ T) S = Dμ (canonFieldOf γ T) (f n ∩ S) *
        ((κ (rootedLocalObs γ D z T)).map (fun w => w - z)) S := by
    intro n
    rw [hνeq _ ((hfm n).inter hS), hνeq S hS]
    exact hr n
  have hνS : ((κ (rootedLocalObs γ D z T)).map (fun w => w - z)) S ≠ ∞ := by
    rw [hνeq S hS]; exact hνfin.ne
  have hres := restrict_eq_smul_of_ratio hS hfm hπ huniv hgen hKpos hKfin.ne hνS hratio
  have hpos : 0 < ((κ (rootedLocalObs γ D z T)).map (fun w => w - z)) S / Dμ (canonFieldOf γ T) S := by
    refine ENNReal.div_pos_iff.2 ⟨?_, hKfin.ne⟩
    rw [hνeq S hS]; exact hνpos.ne'
  have hfin : ((κ (rootedLocalObs γ D z T)).map (fun w => w - z)) S / Dμ (canonFieldOf γ T) S ≠ ∞ :=
    (ENNReal.div_lt_top hνS hKpos.ne').ne
  refine ⟨(((κ (rootedLocalObs γ D z T)).map (fun w => w - z)) S / Dμ (canonFieldOf γ T) S).toReal,
    ENNReal.toReal_pos hpos.ne' hfin, ?_⟩
  rw [ENNReal.ofReal_toReal hfin]
  exact hres

/-- **Section 4.4-4.5, restricted identity for admissible shifts (fixed window).** Let `f` be a countable generating
π-system of the Borel sets and `A n = f n ∩ S`. Assume the transferred event `hshift` for all admissible root shifts
(output of `ae_rootedLocalIdent_shifted_all`). Then for a.e. root `z` and every admissible shift `(b, u)` whose ball
`ball z b` contains the window `ball c₂ r₂`, almost surely the decoded measure of the physical rooted observation (background
`α₀`), pushed to centred coordinates, restricted to `S`, is a positive multiple of the centred canonical measure of the
root-shifted field `shiftedCanon γ hC hcirc z u ω`. This is the measure clause of `hRLI` for a fixed window; the buffered
index `j` of `hRLI` is chosen by the caller, with `ball c₂ r₂ = Dj j`. -/
theorem ae_rootedLocalIdent_restrict {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {α₀ γ : ℝ} {c₁ c₂ : ℂ} {r₁ r₂ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (κ : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) → Measure ℂ)
    (m : (MeanZeroTest (ball c₂ r₂) → ℝ) → C(↥(ball c₂ r₂ ×ˢ ball c₂ r₂ : Set (ℂ × ℂ)), ℝ))
    (Dμ : S11n.CanonSpace → Measure ℂ) (Dd : S11n.CanonSpace → ℂ → ℂ → ℝ)
    (S : Set ℂ) (hS : MeasurableSet S) {f : ℕ → Set ℂ} (hfm : ∀ n, MeasurableSet (f n))
    (hπ : ∀ m n, ∃ k, f k = f m ∩ f n) (huniv : ∃ n, f n = univ)
    (hgen : borel ℂ = MeasurableSpace.generateFrom (Set.range f))
    (X : ℕ → ℂ) (R : ℕ → ℝ) (pq : ℕ → ℂ × ℂ)
    (hshift : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), ∀ (b : ℝ) (u : ℂ → ℝ),
      FirstPassS11ai.AdmissibleRootShift α₀ z b u →
        ∀ᵐ ω ∂P, addFunPairing (S11c.translatedPairing hC hcirc z ω) u ∈
          rootedLocalIdentEvent (ball c₂ r₂) κ m Dμ Dd γ z S (fun n => f n ∩ S) X R pq) :
    ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), ∀ (b : ℝ) (u : ℂ → ℝ),
      FirstPassS11ai.AdmissibleRootShift α₀ z b u → ball c₂ r₂ ⊆ ball z b →
        ∀ᵐ ω ∂P, ∃ c : ℝ, 0 < c ∧
          ((κ (campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z).2).map (fun w => w - z)).restrict S =
            ENNReal.ofReal c •
              (Dμ (canonFieldOf γ (addFunPairing (S11c.translatedPairing hC hcirc z ω) u))).restrict S := by
  filter_upwards [hshift] with z hz b u hadm hD
  filter_upwards [hz b u hadm] with ω hω
  obtain ⟨h1, -⟩ := hω
  have hobs : rootedLocalObs γ (ball c₂ r₂) z (addFunPairing (S11c.translatedPairing hC hcirc z ω) u) =
      (campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z).2 :=
    funext (rootedLocalObs_shifted_eq hC hcirc γ α₀ (ball c₂ r₂) z ω b u hadm hD)
  have hrestr := rootedMeasureIdent_restrict hS hfm hπ huniv hgen h1
  rw [hobs] at hrestr
  exact hrestr

/-! ### Section 4.2, countable family of buffered local windows

Concentric rational windows `ball c r/2 ⊆ ball c r` with `closedBall c r ⊆ W` and `0 ∉ closedBall c r`, indexed by
rational triples. An enumeration of the (countable) index set by `ℕ` gives the family `(U_j, D_j)`: each `D_j = ball (dc j) (dr j)` satisfies the hypotheses of `LocalMeasureKernelStmt`
(`closedBall c₁ r₁ ⊆ ball c₂ r₂`, `0 ∉ closedBall c₂ r₂`), and for every root `z ≠ 0` and `b > 0` some `j` has
`z ∈ U_j` and `closedBall (dc j) (dr j) ⊆ ball z b`. -/

/-- The rational complex number `re + im i` of a triple `p = (re, im, r)`. -/
def ratComplex (p : ℚ × ℚ × ℚ) : ℂ := ⟨(p.1 : ℝ), (p.2.1 : ℝ)⟩

/-- The radius `r` of a rational triple `p = (re, im, r)`. -/
def ratRadius (p : ℚ × ℚ × ℚ) : ℝ := (p.2.2 : ℝ)

/-- The index set of buffered windows in `W`: rational concentric balls `closedBall (ratComplex p) (ratRadius p)`
inside `W` and avoiding the origin. -/
def bufferedIndex (W : Set ℂ) : Set (ℚ × ℚ × ℚ) :=
  {p | 0 < ratRadius p ∧ closedBall (ratComplex p) (ratRadius p) ⊆ W ∧
    (0 : ℂ) ∉ closedBall (ratComplex p) (ratRadius p)}

theorem bufferedIndex_props {W : Set ℂ} {p : ℚ × ℚ × ℚ} (h : p ∈ bufferedIndex W) :
    0 < ratRadius p ∧ closedBall (ratComplex p) (ratRadius p) ⊆ W ∧
      (0 : ℂ) ∉ closedBall (ratComplex p) (ratRadius p) := h

/-- **Density of buffered windows.** For an open `W`, a point `z ∈ W` with `z ≠ 0` and `b > 0`, there is a rational
window `p` in the index set with `z` in the buffered disc `ball c (r/2)` and `closedBall c r ⊆ ball z b`. -/
theorem exists_bufferedIndex_mem {W : Set ℂ} (hW : IsOpen W) {z : ℂ} (hz : z ∈ W) (hz0 : z ≠ 0) {b : ℝ}
    (hb : 0 < b) :
    ∃ p ∈ bufferedIndex W, z ∈ ball (ratComplex p) (ratRadius p / 2) ∧
      closedBall (ratComplex p) (ratRadius p) ⊆ ball z b := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hW z hz
  have hMpos : 0 < min (min ε b) ‖z‖ := lt_min (lt_min hε hb) (norm_pos_iff.2 hz0)
  set M : ℝ := min (min ε b) ‖z‖ with hM
  have hMε : M ≤ ε := (min_le_left _ _).trans (min_le_left _ _)
  have hMb : M ≤ b := (min_le_left _ _).trans (min_le_right _ _)
  have hMz : M ≤ ‖z‖ := min_le_right _ _
  obtain ⟨r, hr0, hr1⟩ := exists_rat_btwn (show (0 : ℝ) < M / 4 by positivity)
  obtain ⟨q1, hq1a, hq1b⟩ := exists_rat_btwn (show z.re - (r : ℝ) / 4 < z.re + (r : ℝ) / 4 by linarith)
  obtain ⟨q2, hq2a, hq2b⟩ := exists_rat_btwn (show z.im - (r : ℝ) / 4 < z.im + (r : ℝ) / 4 by linarith)
  set p : ℚ × ℚ × ℚ := (q1, q2, r) with hp
  have hrp : ratRadius p = (r : ℝ) := rfl
  have hcre : (ratComplex p).re = (q1 : ℝ) := rfl
  have hcim : (ratComplex p).im = (q2 : ℝ) := rfl
  have hcz : dist (ratComplex p) z < (r : ℝ) / 2 := by
    rw [Complex.dist_eq]
    have h := Complex.norm_le_abs_re_add_abs_im (ratComplex p - z)
    rw [Complex.sub_re, Complex.sub_im, hcre, hcim] at h
    have h1 : |(q1 : ℝ) - z.re| < (r : ℝ) / 4 := abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩
    have h2 : |(q2 : ℝ) - z.im| < (r : ℝ) / 4 := abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩
    linarith
  have hr_pos : (0 : ℝ) < (r : ℝ) := hr0
  have hMr : 4 * (r : ℝ) < M := by linarith
  have hmem : p ∈ bufferedIndex W := by
    show 0 < ratRadius p ∧ closedBall (ratComplex p) (ratRadius p) ⊆ W ∧
      (0 : ℂ) ∉ closedBall (ratComplex p) (ratRadius p)
    refine ⟨by rw [hrp]; exact hr_pos, ?_, ?_⟩
    · intro w hw
      rw [mem_closedBall, hrp] at hw
      refine hball (mem_ball.2 ?_)
      have := dist_triangle w (ratComplex p) z
      linarith
    · intro h0
      rw [mem_closedBall, hrp] at h0
      have h1 := dist_triangle z (ratComplex p) 0
      rw [dist_zero_right z, dist_comm z (ratComplex p), dist_comm (ratComplex p) 0] at h1
      linarith
  refine ⟨p, hmem, ?_, ?_⟩
  · rw [mem_ball, dist_comm, hrp]
    exact hcz
  · intro w hw
    rw [mem_closedBall, hrp] at hw
    rw [mem_ball]
    have := dist_triangle w (ratComplex p) z
    linarith

/-- **The countable family of buffered windows.** For an open set `W` containing a point
`z ≠ 0`, there are concentric rational windows `U_j = ball (uc j) (ur j)` inside `D_j = ball (dc j) (dr j)`, with
`closedBall (dc j) (dr j) ⊆ W`, `0 ∉ closedBall (dc j) (dr j)`, the buffer inequality `ur j + dist (uc j) (dc j) < dr j`,
and the approximation property: every `z ∈ W \ {0}` and `b > 0` have some `j` with `z ∈ U_j` and
`closedBall (dc j) (dr j) ⊆ ball z b`. -/
theorem exists_buffered_balls {W : Set ℂ} (hW : IsOpen W) (hW0 : ∃ z ∈ W, z ≠ 0) :
    ∃ (uc dc : ℕ → ℂ) (ur dr : ℕ → ℝ), (∀ j, 0 < ur j) ∧ (∀ j, ur j + dist (uc j) (dc j) < dr j) ∧
      (∀ j, closedBall (dc j) (dr j) ⊆ W) ∧ (∀ j, (0 : ℂ) ∉ closedBall (dc j) (dr j)) ∧
      ∀ z ∈ W, z ≠ 0 → ∀ b : ℝ, 0 < b →
        ∃ j, z ∈ ball (uc j) (ur j) ∧ closedBall (dc j) (dr j) ⊆ ball z b := by
  obtain ⟨z0, hz0W, hz00⟩ := hW0
  obtain ⟨p0, hp0, -⟩ := exists_bufferedIndex_mem hW hz0W hz00 one_pos
  have : Nonempty (bufferedIndex W) := ⟨⟨p0, hp0⟩⟩
  obtain ⟨g, hg⟩ := exists_surjective_nat (bufferedIndex W)
  have hprop : ∀ j, 0 < ratRadius (g j).1 ∧ closedBall (ratComplex (g j).1) (ratRadius (g j).1) ⊆ W ∧
      (0 : ℂ) ∉ closedBall (ratComplex (g j).1) (ratRadius (g j).1) :=
    fun j => bufferedIndex_props (g j).2
  refine ⟨fun j => ratComplex (g j).1, fun j => ratComplex (g j).1, fun j => ratRadius (g j).1 / 2,
    fun j => ratRadius (g j).1, fun j => half_pos (hprop j).1, fun j => ?_,
    fun j => (hprop j).2.1, fun j => (hprop j).2.2, ?_⟩
  · simp only [dist_self, add_zero]
    linarith [(hprop j).1]
  · intro z hzW hz0 b hb
    obtain ⟨p, hp, hzp, hsub⟩ := exists_bufferedIndex_mem hW hzW hz0 hb
    obtain ⟨j, hj⟩ := hg ⟨p, hp⟩
    refine ⟨j, ?_, ?_⟩
    · show z ∈ ball (ratComplex (g j).1) (ratRadius (g j).1 / 2)
      rw [hj]
      exact hzp
    · show closedBall (ratComplex (g j).1) (ratRadius (g j).1) ⊆ ball z b
      rw [hj]
      exact hsub

/-- The radius of the buffered window: `dr - (ur + dist uc dc)`. The closed ball of this radius about a root in
`ball uc ur` stays in `ball dc dr` (the buffer). -/
noncomputable def bufferRadius (uc dc : ℂ) (ur dr : ℝ) : ℝ := dr - (ur + dist uc dc)

theorem bufferRadius_pos {uc dc : ℂ} {ur dr : ℝ} (h : ur + dist uc dc < dr) :
    0 < bufferRadius uc dc ur dr :=
  sub_pos.2 h

theorem closedBall_bufferRadius_subset {z uc dc : ℂ} {ur dr : ℝ} (hz : z ∈ ball uc ur) :
    closedBall z (bufferRadius uc dc ur dr) ⊆ ball dc dr := by
  intro w hw
  rw [mem_closedBall] at hw
  rw [mem_ball]
  rw [mem_ball] at hz
  have h1 := dist_triangle w z dc
  have h2 := dist_triangle z uc dc
  unfold bufferRadius at hw
  linarith

/-- **Section 4.4-4.5 with the buffered family (the measure clause of `hRLI`).** Given a family of buffered windows
`(uc j, ur j, dc j, dr j)` with the approximation property `hdens` on the disc `ball c₁ r₁`, and for each `j` the base
conullity `hbase` of the rooted local identification event at the window `ball (dc j) (dr j)` with the buffered radius
`bufferRadius (uc j) (dc j) (ur j) (dr j)` (output of `ae_rootedLocalIdent_base` for the window), almost every root `z` in
the disc is served by some buffered window `j` with `z ∈ U_j`, for every admissible shift `(b, u)`: the rooted decoded
measure, restricted to `closedBall 0 ρ` with `ρ = bufferRadius ...`, is a positive multiple of the centred canonical
measure of the root-shifted field (Section 4.5). This is `hRLI` (measure clause) of S11at.lean for the family `(U_j, D_j)`. -/
theorem ae_rootedLocalIdent_buffered {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (hCM : CameronMartinGFFMutualAbsCont.{u}) {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hG : IsWholePlaneGFF P hC hcirc) {α₀ γ : ℝ} {c₁ : ℂ} {r₁ : ℝ}
    (uc dc : ℕ → ℂ) (ur dr : ℕ → ℝ) (hbuf : ∀ j, ur j + dist (uc j) (dc j) < dr j)
    (hdens : ∀ z ∈ ball c₁ r₁, z ≠ 0 → ∀ b : ℝ, 0 < b →
      ∃ j, z ∈ ball (uc j) (ur j) ∧ closedBall (dc j) (dr j) ⊆ ball z b)
    (Dμ : S11n.CanonSpace → Measure ℂ) (Dd : S11n.CanonSpace → ℂ → ℂ → ℝ)
    (hDμ : Measurable Dμ) (hDd : ∀ x y : ℂ, Measurable fun L : S11n.CanonSpace => Dd L x y)
    {f : ℕ → Set ℂ} (hfm : ∀ n, MeasurableSet (f n)) (hπ : ∀ m n, ∃ k, f k = f m ∩ f n)
    (huniv : ∃ n, f n = univ) (hgen : borel ℂ = MeasurableSpace.generateFrom (Set.range f))
    (κ : (j : ℕ) → ({φ : ℂ → ℝ // IsTestFunction (ball (dc j) (dr j)) φ ∧ ∫ x, φ x = 0} → ℝ) → Measure ℂ)
    (m : (j : ℕ) → (MeanZeroTest (ball (dc j) (dr j)) → ℝ) →
      C(↥(ball (dc j) (dr j) ×ˢ ball (dc j) (dr j) : Set (ℂ × ℂ)), ℝ))
    (X : ℕ → ℕ → ℂ) (R : ℕ → ℕ → ℝ) (pq : ℕ → ℕ → ℂ × ℂ)
    (hκm : ∀ j, Measurable (κ j)) (hmm : ∀ j, Measurable (m j))
    (hbase : ∀ j, ∀ᵐ z ∂(volume.restrict (ball (uc j) (ur j))), ∀ᵐ ω ∂P,
      S11c.translatedPairing hC hcirc z ω ∈ rootedLocalIdentEvent (ball (dc j) (dr j)) (κ j) (m j) Dμ Dd γ z
        (closedBall 0 (bufferRadius (uc j) (dc j) (ur j) (dr j)))
        (fun n => f n ∩ closedBall 0 (bufferRadius (uc j) (dc j) (ur j) (dr j))) (X j) (R j) (pq j)) :
    ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), ∀ (b : ℝ) (u : ℂ → ℝ),
      FirstPassS11ai.AdmissibleRootShift α₀ z b u →
        ∃ j, z ∈ ball (uc j) (ur j) ∧ ∀ᵐ ω ∂P, ∃ ρ c : ℝ, 0 < ρ ∧ 0 < c ∧
          closedBall z ρ ⊆ ball (dc j) (dr j) ∧
          ((κ j (campbellReferenceObs γ α₀ (ball (dc j) (dr j)) (hC ω) z).2).map (fun w => w - z)).restrict
              (closedBall 0 ρ) =
            ENNReal.ofReal c • (Dμ (canonFieldOf γ (addFunPairing (S11c.translatedPairing hC hcirc z ω) u))).restrict
              (closedBall 0 ρ) := by
  have hshift : ∀ j, ∀ᵐ z ∂(volume.restrict (ball (uc j) (ur j))), ∀ (b : ℝ) (u : ℂ → ℝ),
      FirstPassS11ai.AdmissibleRootShift α₀ z b u → ∀ᵐ ω ∂P,
        addFunPairing (S11c.translatedPairing hC hcirc z ω) u ∈
          rootedLocalIdentEvent (ball (dc j) (dr j)) (κ j) (m j) Dμ Dd γ z
            (closedBall 0 (bufferRadius (uc j) (dc j) (ur j) (dr j)))
            (fun n => f n ∩ closedBall 0 (bufferRadius (uc j) (dc j) (ur j) (dr j))) (X j) (R j) (pq j) :=
    fun j => ae_rootedLocalIdent_shifted_all P hCM hG (α₀ := α₀) (κ j) (m j) Dμ Dd _ _ (X j) (R j) (pq j)
      (hκm j) (hmm j) hDμ hDd measurableSet_closedBall (fun n => (hfm n).inter measurableSet_closedBall) (hbase j)
  have hres : ∀ j, ∀ᵐ z ∂(volume.restrict (ball (uc j) (ur j))), ∀ (b : ℝ) (u : ℂ → ℝ),
      FirstPassS11ai.AdmissibleRootShift α₀ z b u → ball (dc j) (dr j) ⊆ ball z b → ∀ᵐ ω ∂P, ∃ c : ℝ, 0 < c ∧
        ((κ j (campbellReferenceObs γ α₀ (ball (dc j) (dr j)) (hC ω) z).2).map (fun w => w - z)).restrict
            (closedBall 0 (bufferRadius (uc j) (dc j) (ur j) (dr j))) =
          ENNReal.ofReal c • (Dμ (canonFieldOf γ (addFunPairing (S11c.translatedPairing hC hcirc z ω) u))).restrict
            (closedBall 0 (bufferRadius (uc j) (dc j) (ur j) (dr j))) :=
    fun j => ae_rootedLocalIdent_restrict (κ j) (m j) Dμ Dd _ measurableSet_closedBall hfm hπ huniv hgen
      (X j) (R j) (pq j) (hshift j)
  have hz0 : ∀ᵐ z ∂(volume : Measure ℂ), z ≠ 0 := compl_mem_ae_iff.2 (measure_singleton (0 : ℂ))
  have hall : ∀ᵐ z ∂(volume : Measure ℂ), ∀ j, z ∈ ball (uc j) (ur j) → ∀ (b : ℝ) (u : ℂ → ℝ),
      FirstPassS11ai.AdmissibleRootShift α₀ z b u → ball (dc j) (dr j) ⊆ ball z b → ∀ᵐ ω ∂P, ∃ c : ℝ, 0 < c ∧
        ((κ j (campbellReferenceObs γ α₀ (ball (dc j) (dr j)) (hC ω) z).2).map (fun w => w - z)).restrict
            (closedBall 0 (bufferRadius (uc j) (dc j) (ur j) (dr j))) =
          ENNReal.ofReal c • (Dμ (canonFieldOf γ (addFunPairing (S11c.translatedPairing hC hcirc z ω) u))).restrict
            (closedBall 0 (bufferRadius (uc j) (dc j) (ur j) (dr j))) :=
    ae_all_iff.2 (fun j => (ae_restrict_iff' (measurableSet_ball : MeasurableSet (ball (uc j) (ur j)))).1 (hres j))
  filter_upwards [ae_restrict_of_ae hall, ae_restrict_of_ae hz0, ae_restrict_mem measurableSet_ball] with
    z hzall hz0' hzball b u hadm
  obtain ⟨j, hzj, hbj⟩ := hdens z hzball hz0' b hadm.1
  refine ⟨j, hzj, ?_⟩
  have hGz := hzall j hzj b u hadm (Metric.ball_subset_closedBall.trans hbj)
  filter_upwards [hGz] with ω hω
  obtain ⟨c, hc, heq⟩ := hω
  exact ⟨bufferRadius (uc j) (dc j) (ur j) (dr j), c, bufferRadius_pos (hbuf j), hc,
    closedBall_bufferRadius_subset hzj, heq⟩


/-! ### Metric converse on a window

The frozen clauses are `ENNReal`-valued; the real window identity is recovered by `eq_const_mul_of_dense_family`
(MetricSign.lean). `windowDecodedMetric` has the same body as `FirstPassS11at.windowMetric` (S11at.lean:761), which
lies downstream and cannot be imported here. -/

open Classical in
/-- The real decoded window metric at the endpoint pair `(x, y)`: the value of the decoder `m` on the window `D × D`,
and `0` outside. (Same body as `FirstPassS11at.windowMetric`.) -/
noncomputable def windowDecodedMetric (D : Set ℂ) (m : (MeanZeroTest D → ℝ) → C(↥(D ×ˢ D), ℝ))
    (φ : MeanZeroTest D → ℝ) : ℂ → ℂ → ℝ :=
  fun x y => if h : (x, y) ∈ D ×ˢ D then m φ ⟨(x, y), h⟩ else 0

theorem rootedMetricAt_eq_ofReal_windowDecoded (D : Set ℂ) (m : (MeanZeroTest D → ℝ) → C(↥(D ×ˢ D), ℝ))
    (γ : ℝ) (z : ℂ) (T : (ℂ → ℝ) → ℝ) (x y : ℂ) :
    rootedMetricAt D m γ z T x y = ENNReal.ofReal (windowDecodedMetric D m (rootedLocalObs γ D z T) x y) := by
  unfold rootedMetricAt windowDecodedMetric
  split_ifs <;> simp_all

/-- **Metric converse on a window (deterministic core).** Let `D` be open with `z ∈ D`, and let the rooted metric
identity `rootedMetricIdent` hold for the reference index `k`, with the countable family `X` dense in every ball `ball 0 r`
(`hXd`), the centred decoder `Dd (canonFieldOf γ T)` a Euclidean length metric and jointly continuous (`hLen`, `hDc`, the
latter from the continuous canonical decoder `d` of `LQGCanonicalDecodersMeasurableExistStmt`), and the decoded window
metric positive at the off-diagonal reference pair (`hpos`, from the window clause and positivity of the internal metric).
Then there are `c > 0` and `ρ > 0` with `closedBall z ρ ⊆ D` and the **real** identity
`windowDecodedMetric D m (rootedLocalObs γ D z T) (x + z) (y + z) = c * Dd (canonFieldOf γ T) x y` on `closedBall 0 ρ`.
No sign input is needed: the sign and diagonal are fixed by `eq_const_mul_of_dense_family`. -/
theorem windowDecoded_eq_const_mul_of_rootedMetricIdent {D : Set ℂ} (hD : IsOpen D) {z : ℂ} (hz : z ∈ D) {γ : ℝ}
    (m : (MeanZeroTest D → ℝ) → C(↥(D ×ˢ D), ℝ)) (Dd : S11n.CanonSpace → ℂ → ℂ → ℝ) (T : (ℂ → ℝ) → ℝ)
    (hLen : IsEuclideanLengthMetric (Dd (canonFieldOf γ T)))
    (hDc : Continuous fun p : ℂ × ℂ => Dd (canonFieldOf γ T) p.1 p.2)
    (X : ℕ → ℂ) (R : ℕ → ℝ) (pq : ℕ → ℂ × ℂ)
    (hXd : ∀ r : ℝ, 0 < r → ∀ x ∈ ball (0 : ℂ) r, ∀ ε > 0, ∃ i, ‖X i‖ < r ∧ dist (X i) x < ε)
    (hmet : rootedMetricIdent D m Dd γ z X R pq T)
    (hpos : ∀ k, (pq k).1 ≠ (pq k).2 → (pq k).1 + z ∈ D → (pq k).2 + z ∈ D →
      0 < windowDecodedMetric D m (rootedLocalObs γ D z T) ((pq k).1 + z) ((pq k).2 + z)) :
    ∃ c ρ : ℝ, 0 < c ∧ 0 < ρ ∧ closedBall z ρ ⊆ D ∧
      ∀ x ∈ closedBall (0 : ℂ) ρ, ∀ y ∈ closedBall (0 : ℂ) ρ,
        windowDecodedMetric D m (rootedLocalObs γ D z T) (x + z) (y + z) = c * Dd (canonFieldOf γ T) x y := by
  obtain ⟨k, hk1, hk2, hk3, hk4, hk5, hk6⟩ := hmet
  have hne : (pq k).1 ≠ (pq k).2 := fun h => by
    have h0 := hk5
    rw [h, hLen.self_eq_zero] at h0
    exact lt_irrefl _ h0
  set D0 := Dd (canonFieldOf γ T) (pq k).1 (pq k).2 with hD0def
  have hD0 : 0 < D0 := hk5
  set m0 := windowDecodedMetric D m (rootedLocalObs γ D z T) ((pq k).1 + z) ((pq k).2 + z) with hm0def
  have hm0 : 0 < m0 := hpos k hne hk3 hk4
  have hRk : 0 < R k := lt_of_le_of_lt (norm_nonneg _) hk1
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hD z hz
  set O : Set ℂ := ((fun x : ℂ => x + z) ⁻¹' D) ∩ ball (0 : ℂ) (R k) with hOdef
  have hO : IsOpen O := (hD.preimage (continuous_id.add continuous_const)).inter isOpen_ball
  -- density of the family in the window O
  have hdense : ∀ x ∈ O, ∀ ε > 0, ∃ i, X i ∈ O ∧ dist (X i) x < ε := by
    intro x hx ε hε
    obtain ⟨hxD, hxB⟩ := hx
    obtain ⟨δ', hδ', hball'⟩ := Metric.isOpen_iff.1 hD (x + z) hxD
    obtain ⟨i, hiB, hid⟩ := hXd (R k) hRk x hxB (min ε δ') (lt_min hε hδ')
    refine ⟨i, ⟨?_, ?_⟩, lt_of_lt_of_le hid (min_le_left _ _)⟩
    · apply hball'
      rw [Metric.mem_ball, dist_add_right]
      exact lt_of_lt_of_le hid (min_le_right _ _)
    · exact mem_ball_zero_iff.2 hiB
  -- the ENNReal identity on the family
  have hfam : ∀ i j, X i ∈ O → X j ∈ O →
      ENNReal.ofReal (windowDecodedMetric D m (rootedLocalObs γ D z T) (X i + z) (X j + z)) =
        ENNReal.ofReal (m0 / D0) * ENNReal.ofReal (Dd (canonFieldOf γ T) (X i) (X j)) := by
    intro i j hi hj
    have hiB : ‖X i‖ < R k := mem_ball_zero_iff.1 hi.2
    have hjB : ‖X j‖ < R k := mem_ball_zero_iff.1 hj.2
    have key := hk6 i j hiB hjB hi.1 hj.1
    rw [rootedMetricAt_eq_ofReal_windowDecoded, rootedMetricAt_eq_ofReal_windowDecoded] at key
    have hd0 : ENNReal.ofReal D0 ≠ 0 := (ENNReal.ofReal_pos.2 hD0).ne'
    have hdt : ENNReal.ofReal D0 ≠ ⊤ := ENNReal.ofReal_ne_top
    calc ENNReal.ofReal (windowDecodedMetric D m (rootedLocalObs γ D z T) (X i + z) (X j + z))
        = ENNReal.ofReal (windowDecodedMetric D m (rootedLocalObs γ D z T) (X i + z) (X j + z)) *
            ENNReal.ofReal D0 * (ENNReal.ofReal D0)⁻¹ := by
          rw [mul_assoc, ENNReal.mul_inv_cancel hd0 hdt, mul_one]
      _ = ENNReal.ofReal (Dd (canonFieldOf γ T) (X i) (X j)) * ENNReal.ofReal m0 * (ENNReal.ofReal D0)⁻¹ := by
          rw [key]
      _ = ENNReal.ofReal (m0 / D0) * ENNReal.ofReal (Dd (canonFieldOf γ T) (X i) (X j)) := by
          rw [ENNReal.ofReal_div_of_pos hD0, div_eq_mul_inv]
          ring
  -- continuity of the window metric on O × O
  have hMc : ContinuousOn (fun p : ℂ × ℂ => windowDecodedMetric D m (rootedLocalObs γ D z T) (p.1 + z) (p.2 + z))
      (O ×ˢ O) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hmem : ∀ p : ↥(O ×ˢ O), ((p : ℂ × ℂ).1 + z, (p : ℂ × ℂ).2 + z) ∈ D ×ˢ D := fun p =>
      ⟨p.2.1.1, p.2.2.1⟩
    have hg : Continuous fun p : ↥(O ×ˢ O) =>
        (⟨((p : ℂ × ℂ).1 + z, (p : ℂ × ℂ).2 + z), hmem p⟩ : ↥(D ×ˢ D)) :=
      Continuous.subtype_mk (by fun_prop) _
    have hcomp : Continuous fun p : ↥(O ×ˢ O) => m (rootedLocalObs γ D z T) (
        ⟨((p : ℂ × ℂ).1 + z, (p : ℂ × ℂ).2 + z), hmem p⟩) := (m (rootedLocalObs γ D z T)).continuous.comp hg
    refine hcomp.congr ?_
    intro p
    simp [Set.domRestrict_apply, windowDecodedMetric, hmem p]
  -- real identity on O × O
  have hreal := eq_const_mul_of_dense_family hLen hO (div_pos hm0 hD0) hdense
    (m := fun x y => windowDecodedMetric D m (rootedLocalObs γ D z T) (x + z) (y + z))
    hMc hDc.continuousOn hfam
  -- the closed ball of radius ρ
  have hρ1 : 0 < min (R k / 2) (δ / 2) := lt_min (half_pos hRk) (half_pos hδ)
  have hρR : min (R k / 2) (δ / 2) ≤ R k / 2 := min_le_left _ _
  have hρδ : min (R k / 2) (δ / 2) ≤ δ / 2 := min_le_right _ _
  refine ⟨m0 / D0, min (R k / 2) (δ / 2), div_pos hm0 hD0, hρ1, ?_, ?_⟩
  · intro x hx
    apply hball
    rw [Metric.mem_closedBall, dist_eq_norm] at hx
    rw [Metric.mem_ball, dist_eq_norm]
    linarith
  · have hO' : ∀ x ∈ closedBall (0 : ℂ) (min (R k / 2) (δ / 2)), x ∈ O := by
      intro x hx
      have hxn : ‖x‖ ≤ min (R k / 2) (δ / 2) := mem_closedBall_zero_iff.1 hx
      refine ⟨?_, mem_ball_zero_iff.2 ?_⟩
      · show x + z ∈ D
        apply hball
        rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_right]
        linarith
      · linarith
    intro x hx y hy
    exact hreal x (hO' x hx) y (hO' y hy)

end HarmonicBalls

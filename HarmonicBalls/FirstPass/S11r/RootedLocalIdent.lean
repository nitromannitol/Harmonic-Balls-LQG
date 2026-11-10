import HarmonicBalls.FirstPass.S11r.CMTransfer
import HarmonicBalls.FirstPass.S11r.Frozen
import HarmonicBalls.FirstPass.S11ai.RootedInstance
import HarmonicBalls.FirstPass.S11r.UnrootedFixed
import HarmonicBalls.FirstPass.S11c.CoordRooted11_7
import HarmonicBalls.FirstPass.S11c.TranslateField11_7
import HarmonicBalls.Proofs.Sec6.LQGWeylScaling
import HarmonicBalls.Proposed.LQG
import HarmonicBalls.FirstPass.S11r.NoShortcut

/-!
# Rooted local identification event (fp-S11r-rooted-local-ident)

Source: ChatGPT chat 201 (PRO), `notes/fp-gaps/CHATGPT-hb-11-13-q1-rooted-ident.md`, Ruling and Section 4 (lines 244-423),
implementation decision (section 7).

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
`hDex`, and the window positivity `hPF`, the last still PENDING a source). The metric clause of the base conullity is
`ae_rootedMetricIdent_base`, conditional on the named locality input `hLoc` (internal metric under translation and constant
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

/-- **Measurability of the rooted local identification event** (Section 4.3, fp-S11r-rooted-local-ident).
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

/-! ### Section 4.4, measure clause of the base conullity (round 2)

Route (notes/n2.md): the rooted LQG measure at the root `z` of the physical field, with the `(max 1 |·|)`
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
    (hPF : ∀ (z : ℂ) (ν : Ω → Measure ℂ), IsLQGMeasureOfField P γ γ (S11c.translatedCircle hcirc z) ν →
      ∀ᵐ ω ∂P, 0 < ν ω S ∧ ν ω S < ∞) :
    ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), ∀ᵐ ω ∂P,
      rootedMeasureIdent (ball c₂ r₂) κ Dμ γ z S A (S11c.translatedPairing hC hcirc z ω) := by
  filter_upwards [hκ, ae_restrict_mem measurableSet_ball] with z hz hzU
  have hG' := S11c.isWholePlaneGFF_translate hG z
  obtain ⟨ν, hν⟩ := hνex z hG' hγ0 hγ2 (S11c.gamma_lt_lqgQ hγ0 hγ2)
  obtain ⟨D, hDz⟩ := hDex z
  have hPFω := hPF z ν hν
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

/-- The rooted Weyl metric of clause (20) of `LocalMetricReplacementStmt` at background `0`: the real part of the Weyl
scaling of `𝔇 (hC ω)` by the rooted weight `-γ log|· - z| + γ log max(1,|·|)`. -/
noncomputable def rootedWeylMetric (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (ξ γ : ℝ) {Ω : Type*} (hC : Ω → (ℂ → ℝ) → ℝ)
    (z : ℂ) (ω : Ω) : ℂ → ℂ → ℝ :=
  fun u v => (weylScaling (𝔇 (hC ω)) ξ
    (fun w => -(0 : ℝ) * Real.log ‖w‖ - γ * Real.log ‖w - z‖ + γ * Real.log (max 1 ‖w‖)) u v).toReal

/-- The centred Weyl metric of the translated normalised field at insertion `γ` (background `α₀ = γ`): the real metric
of `IsLQGMetricOfField P γ ξ γ (translatedPairing hC hcirc z)`. -/
noncomputable def centredWeylMetric (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (ξ γ : ℝ) {Ω : Type*} (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (z : ℂ) (ω : Ω) : ℂ → ℂ → ℝ :=
  fun u v => (weylScaling (𝔇 (S11c.translatedPairing hC hcirc z ω)) ξ (fun x => -γ * Real.log ‖x‖) u v).toReal

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
the locality of the internal metric under translation and constant shift, `hLoc` (MISSING, see the report: Fact 2.2 II
of arXiv:2208.11795, with the translation covariance (Fact 2.2 IV) and the additive-constant rule of the Weyl scaling);
the Proposed metric field axioms `hAx` (item I: finiteness and length metric); the canonical identification `hIdγ` at
insertion `γ` with the centred metric; the measure existence `hνex` (premise of `hIdγ`). -/
theorem ae_rootedMetricIdent_base {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {γ ξ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) {c₁ c₂ : ℂ} {r₁ r₂ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc)
    (hsub : closedBall c₁ r₁ ⊆ ball c₂ r₂)
    {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (m : (MeanZeroTest (ball c₂ r₂) → ℝ) → C(↥(ball c₂ r₂ ×ˢ ball c₂ r₂ : Set (ℂ × ℂ)), ℝ))
    (hclause : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), ∀ᵐ ω ∂P, ∃ b : ℝ, 0 < b ∧
      ∀ p : ↥(ball c₂ r₂ ×ˢ ball c₂ r₂ : Set (ℂ × ℂ)),
        ENNReal.ofReal (m (campbellReferenceObs γ 0 (ball c₂ r₂) (hC ω) z).2 p) =
          ENNReal.ofReal b * internalMetric (rootedWeylMetric 𝔇 ξ γ hC z ω) (ball c₂ r₂) p.1.1 p.1.2)
    (hLoc : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), ∀ᵐ ω ∂P, ∃ κ : ℝ, 0 < κ ∧ ∀ x y : ℂ,
      x + z ∈ ball c₂ r₂ → y + z ∈ ball c₂ r₂ →
        internalMetric (rootedWeylMetric 𝔇 ξ γ hC z ω) (ball c₂ r₂) (x + z) (y + z) =
          ENNReal.ofReal κ * internalMetric (centredWeylMetric 𝔇 ξ γ hC hcirc z ω)
            ((fun u => u + z) ⁻¹' ball c₂ r₂) x y)
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

end HarmonicBalls

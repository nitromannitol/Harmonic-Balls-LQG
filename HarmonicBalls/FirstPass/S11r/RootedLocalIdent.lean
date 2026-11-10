import HarmonicBalls.FirstPass.S11r.CMTransfer
import HarmonicBalls.FirstPass.S11r.Frozen
import HarmonicBalls.FirstPass.S11ai.RootedInstance
import HarmonicBalls.FirstPass.S11r.UnrootedFixed

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

The base conullity `ae_rootedLocalIdent_base` (Section 4.4, `Hz ω ∈ rootedLocalIdentEvent`) is NOT proved in this file.
The argument needs the translation covariance of the LQG measure and metric, which is not yet in the repository; see the
round report.
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
    (T : (ℂ → ℝ) → ℝ) (x y : ℂ) : ℝ :=
  if h : (x, y) ∈ D ×ˢ D then m (rootedLocalObs γ D z T) ⟨(x, y), h⟩ else 0

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
      rootedMetricAt D m γ z T (X i + z) (X j + z) * Dd (canonFieldOf γ T) (pq k).1 (pq k).2 =
        Dd (canonFieldOf γ T) (X i) (X j) * rootedMetricAt D m γ z T ((pq k).1 + z) ((pq k).2 + z)

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
        fun T => m (rootedLocalObs γ D z T) ⟨(x, y), h⟩ := by
      funext T
      simp [rootedMetricAt, h]
    rw [h']
    exact (ContinuousMap.measurable_eval _).comp (hm.comp (measurable_rootedLocalObs γ D z))
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
            rootedMetricAt D m γ z T (X i + z) (X j + z) * Dd (canonFieldOf γ T) (pq k).1 (pq k).2 =
              Dd (canonFieldOf γ T) (X i) (X j) * rootedMetricAt D m γ z T ((pq k).1 + z) ((pq k).2 + z)} := by
      ext T
      simp [rootedMetricIdent]
    rw [hset]
    refine MeasurableSet.iUnion fun k => ?_
    have hpos : MeasurableSet[distributionMeasurableSpace] {T : (ℂ → ℝ) → ℝ |
        0 < Dd (canonFieldOf γ T) (pq k).1 (pq k).2} :=
      measurableSet_lt measurable_const ((hDd _ _).comp (measurable_canonFieldOf_distribution γ))
    have hall : MeasurableSet[distributionMeasurableSpace] {T : (ℂ → ℝ) → ℝ | ∀ i j : ℕ,
        ‖X i‖ < R k → ‖X j‖ < R k → X i + z ∈ D → X j + z ∈ D →
          rootedMetricAt D m γ z T (X i + z) (X j + z) * Dd (canonFieldOf γ T) (pq k).1 (pq k).2 =
            Dd (canonFieldOf γ T) (X i) (X j) * rootedMetricAt D m γ z T ((pq k).1 + z) ((pq k).2 + z)} := by
      refine measurableSet_forall_nat fun i => measurableSet_forall_nat fun j => ?_
      refine measurableSet_imp_prop_of (measurableSet_imp_prop_of (measurableSet_imp_prop_of
        (measurableSet_imp_prop_of ?_)))
      have h1 : Measurable[distributionMeasurableSpace] fun T : (ℂ → ℝ) → ℝ =>
          rootedMetricAt D m γ z T (X i + z) (X j + z) * Dd (canonFieldOf γ T) (pq k).1 (pq k).2 :=
        (measurable_rootedMetricAt D m hm γ z _ _).mul
          ((hDd _ _).comp (measurable_canonFieldOf_distribution γ))
      have h2 : Measurable[distributionMeasurableSpace] fun T : (ℂ → ℝ) → ℝ =>
          Dd (canonFieldOf γ T) (X i) (X j) * rootedMetricAt D m γ z T ((pq k).1 + z) ((pq k).2 + z) :=
        ((hDd _ _).comp (measurable_canonFieldOf_distribution γ)).mul
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

end HarmonicBalls

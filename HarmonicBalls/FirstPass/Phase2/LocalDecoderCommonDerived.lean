import HarmonicBalls.FirstPass.S11r.Frozen
import HarmonicBalls.FirstPass.Frozen.S11c
import HarmonicBalls.FirstPass.S11at.Producers
import HarmonicBalls.FirstPass.S11u.Kernel
import HarmonicBalls.Steps.Sec11.PairingCovarianceLinearity

/-!
# Common local decoder, derived (task fp-phase2-b1-decoder-derive part (2), owner z4)

Targets: `LocalMeasureKernelStmt` (`FirstPass/S11r/Frozen.lean:144`) and `LocalLQGDecoderCommonFrozen`
(`FirstPass/Frozen/S11c.lean:388`). Route: MQ-lh-12 (`notes/fp-gaps/MATH-ANSWERS.md` lines 75-103).

Step 3 of the route (countable Borel coding of continuous functions on a Polish, locally compact space) is proved
here for an arbitrary such space; the square and the profile domain `{(r,x) : closedBall x r ⊆ D}` are instances.

Layer 1: the parameter domain `LocalParam c R = {(r,x) : 0 < r, closedBall x r ⊆ ball c R}` (written as
`dist x c + r < R`), its Polish and locally compact structure, the fixed unit-mass bump `bumpRho`, the mean-zero
test functions `localTest p j = ψ_{j+N_p} - ρ` on the circle `p` (`ψ` = `circleApprox`, supported in the disc for
large index), and the circle coordinates `localCoord p v = lim_j v(localTest p j)` of an observation `v`.
Layer 3: `ae_localCoord_eq`, the coordinate of the GFF observation is the centred circle average a.s.
-/

namespace HarmonicBalls

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal
open FirstPassS11atProducers

universe u

/-- MQ-lh-12 step 3: a countable dense family of a Polish, locally compact space `X` and a measurable decoder
recovering each continuous function `X → ℝ` from its values along the family (Borel embedding of `C(X, ℝ)` into
`ℕ → ℝ`, with a measurable left inverse by `MeasurableEmbedding.exists_measurable_extend`). -/
theorem exists_dense_decode_polish (X : Type*) [TopologicalSpace X] [PolishSpace X] [LocallyCompactSpace X]
    [Nonempty X] :
    ∃ d : ℕ → X, DenseRange d ∧ ∃ decode : (ℕ → ℝ) → C(X, ℝ), Measurable decode ∧
      ∀ f : C(X, ℝ), decode (fun n => f (d n)) = f := by
  let d : ℕ → X := TopologicalSpace.denseSeq X
  have hd : DenseRange d := TopologicalSpace.denseRange_denseSeq X
  let e : C(X, ℝ) → ℕ → ℝ := fun f n => f (d n)
  have he : Measurable e := measurable_pi_iff.mpr fun n => (continuous_eval_const (d n)).measurable
  have hinj : Function.Injective e := by
    intro f g h
    apply ContinuousMap.ext
    have hdense := hd.equalizer f.continuous g.continuous
    apply congrFun (hdense ?_)
    funext n
    exact congrFun h n
  have hemb : MeasurableEmbedding e := he.measurableEmbedding hinj
  obtain ⟨decode, hdecode, hdecode_eq⟩ :=
    hemb.exists_measurable_extend (g := id) measurable_id (fun _ => inferInstance)
  exact ⟨d, hd, decode, hdecode, fun f => congrFun hdecode_eq f⟩

namespace LocalDecoderCommon

/-! ### 1. The parameter domain of a disc -/

/-- The circles `closedBall x r ⊆ ball c R` (`r > 0`), as parameters `(r, x)`, written with the equivalent
condition `dist x c + r < R`: the domain of the local profile of the disc `ball c R`. -/
def LocalParam (c : ℂ) (R : ℝ) : Set (ℝ × ℂ) := {p | 0 < p.1 ∧ dist p.2 c + p.1 < R}

theorem mem_localParam_iff (c : ℂ) (R : ℝ) (p : ℝ × ℂ) :
    p ∈ LocalParam c R ↔ 0 < p.1 ∧ dist p.2 c + p.1 < R := Iff.rfl

theorem isOpen_localParam (c : ℂ) (R : ℝ) : IsOpen (LocalParam c R) := by
  have h : LocalParam c R = {p : ℝ × ℂ | 0 < p.1} ∩ {p : ℝ × ℂ | dist p.2 c + p.1 < R} := rfl
  rw [h]
  exact (isOpen_lt continuous_const continuous_fst).inter
    (isOpen_lt ((continuous_snd.dist continuous_const).add continuous_fst) continuous_const)

instance instPolishLocalParam (c : ℂ) (R : ℝ) : PolishSpace (LocalParam c R) :=
  (isOpen_localParam c R).polishSpace

instance instLocallyCompactLocalParam (c : ℂ) (R : ℝ) : LocallyCompactSpace (LocalParam c R) :=
  (isOpen_localParam c R).locallyCompactSpace

theorem localParam_nonempty (c : ℂ) {R : ℝ} (hR : 0 < R) : Nonempty (LocalParam c R) :=
  ⟨⟨(R / 2, c), (mem_localParam_iff c R _).2 ⟨half_pos hR, by show dist c c + R / 2 < R; rw [dist_self]; linarith⟩⟩⟩

/-- The radius of a parameter of the disc. -/
theorem localParam_radius_pos {c : ℂ} {R : ℝ} (p : LocalParam c R) : 0 < p.1.1 :=
  ((mem_localParam_iff c R p.1).1 p.2).1

/-- The distance condition of a parameter of the disc. -/
theorem localParam_dist_lt {c : ℂ} {R : ℝ} (p : LocalParam c R) : dist p.1.2 c + p.1.1 < R :=
  ((mem_localParam_iff c R p.1).1 p.2).2

/-! ### 2. Circle approximants inside the disc -/

/-- The fixed unit-mass bump `ρ` of the disc `ball c R`: the circle approximant of the circle of radius `R/2`
about `c` (its support lies in `ball c R`). -/
noncomputable def bumpRho (c : ℂ) {R : ℝ} (hR : 0 < R) : ℂ → ℝ :=
  circleApprox (half_pos hR) c 0

theorem eventually_approxEta_lt {r t : ℝ} (ht : 0 < t) :
    ∃ N : ℕ, ∀ j, N ≤ j → approxEta r j < t := by
  have h : Tendsto (fun j : ℕ => r / 4 * (1 / 2 : ℝ) ^ j) atTop (𝓝 (r / 4 * 0)) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).const_mul (r / 4)
  rw [mul_zero] at h
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_order.1 h).2 t ht)
  exact ⟨N, fun j hj => hN j hj⟩

/-- The support of the annular approximant of the circle `(r, x)` lies in the disc `ball c R` as soon as its
width `approxEta r j` is below the margin `R - (dist x c + r)`. -/
theorem tsupport_circleApprox_subset_ball {c x : ℂ} {R r : ℝ} (hr : 0 < r) {j : ℕ}
    (h : approxEta r j < R - (dist x c + r)) :
    tsupport (circleApprox hr x j) ⊆ ball c R := by
  intro y hy
  have hy' : y ∈ tsupport (unitCircleDensity r (r * approxEta r j) (mul_pos hr (approxEta_pos hr j)) x) := hy
  have hsub := tsupport_unitCircleDensity_subset hr (mul_pos hr (approxEta_pos hr j)) (le_refl _) x hy'
  have habs : |‖y - x‖ - r| ≤ approxEta r j := hsub
  have h1 : ‖y - x‖ ≤ r + approxEta r j := by linarith [le_abs_self (‖y - x‖ - r)]
  have htri : dist y c ≤ dist y x + dist x c := dist_triangle y x c
  have hyx : dist y x = ‖y - x‖ := dist_eq_norm y x
  rw [mem_ball]
  linarith

/-- For a circle of the disc, all large indices give approximants supported in the disc. -/
theorem exists_tsupport_circleApprox_subset {c x : ℂ} {R r : ℝ} (hr : 0 < r) (h : dist x c + r < R) :
    ∃ N : ℕ, ∀ j, N ≤ j → tsupport (circleApprox hr x j) ⊆ ball c R := by
  obtain ⟨N, hN⟩ := eventually_approxEta_lt (r := r) (sub_pos.2 h)
  exact ⟨N, fun j hj => tsupport_circleApprox_subset_ball hr (hN j hj)⟩

/-- The index shift `N_p` of the parameter `p`: the approximants of index `≥ N_p` are supported in the disc. -/
noncomputable def localShift (c : ℂ) {R : ℝ} (p : LocalParam c R) : ℕ :=
  Classical.choose (exists_tsupport_circleApprox_subset (localParam_radius_pos p) (localParam_dist_lt p))

theorem localShift_spec (c : ℂ) {R : ℝ} (p : LocalParam c R) (j : ℕ) (hj : localShift c p ≤ j) :
    tsupport (circleApprox (localParam_radius_pos p) p.1.2 j) ⊆ ball c R :=
  Classical.choose_spec (exists_tsupport_circleApprox_subset (localParam_radius_pos p) (localParam_dist_lt p)) j hj

theorem bumpRho_isTest (c : ℂ) {R : ℝ} (hR : 0 < R) :
    IsTestFunction (ball c R) (bumpRho c hR) := by
  have hsub : tsupport (bumpRho c hR) ⊆ ball c R := by
    apply tsupport_circleApprox_subset_ball (half_pos hR)
    unfold approxEta
    rw [dist_self, pow_zero]
    linarith
  exact ⟨(isTestFunction_circleApprox (half_pos hR) c 0).1,
    (isTestFunction_circleApprox (half_pos hR) c 0).2.1, hsub⟩

theorem integral_bumpRho (c : ℂ) {R : ℝ} (hR : 0 < R) : ∫ x, bumpRho c hR x = 1 :=
  integral_circleApprox (half_pos hR) c 0

/-- The mean-zero test `ψ_{j + N_p} - ρ` attached to the parameter `p` (the route's "mean-zero tests
`ψ_n - ρ` read from the code", step 1). -/
noncomputable def localTest (c : ℂ) {R : ℝ} (hR : 0 < R) (p : LocalParam c R) (j : ℕ) : ℂ → ℝ :=
  circleApprox (localParam_radius_pos p) p.1.2 (j + localShift c p) - bumpRho c hR

theorem localTest_isTest (c : ℂ) {R : ℝ} (hR : 0 < R) (p : LocalParam c R) (j : ℕ) :
    IsTestFunction (ball c R) (localTest c hR p j) ∧ ∫ x, localTest c hR p j x = 0 := by
  have hψ := isTestFunction_circleApprox (localParam_radius_pos p) p.1.2 (j + localShift c p)
  have hsub : tsupport (localTest c hR p j) ⊆ ball c R := by
    unfold localTest
    refine (tsupport_sub _ _).trans (Set.union_subset ?_ ?_)
    · exact localShift_spec c p (j + localShift c p) (Nat.le_add_left _ _)
    · exact (bumpRho_isTest c hR).2.2
  refine ⟨⟨hψ.1.sub (bumpRho_isTest c hR).1, hψ.2.1.sub (bumpRho_isTest c hR).2.1, hsub⟩, ?_⟩
  unfold localTest
  have hψi : Integrable (circleApprox (localParam_radius_pos p) p.1.2 (j + localShift c p)) :=
    hψ.1.continuous.integrable_of_hasCompactSupport hψ.2.1
  have hρi : Integrable (bumpRho c hR) :=
    (bumpRho_isTest c hR).1.continuous.integrable_of_hasCompactSupport (bumpRho_isTest c hR).2.1
  simp only [Pi.sub_apply]
  rw [integral_sub hψi hρi, integral_circleApprox, integral_bumpRho, sub_self]

open Classical in
/-- An observation `v` on the mean-zero tests of `D`, read on an arbitrary function `φ` (value `0` when `φ` is not
an admissible test). -/
noncomputable def obsAt {D : Set ℂ} (v : {φ : ℂ → ℝ // IsTestFunction D φ ∧ ∫ x, φ x = 0} → ℝ) (φ : ℂ → ℝ) : ℝ :=
  if h : IsTestFunction D φ ∧ ∫ x, φ x = 0 then v ⟨φ, h⟩ else 0

theorem measurable_obsAt {D : Set ℂ} (φ : ℂ → ℝ) :
    Measurable fun v : {φ : ℂ → ℝ // IsTestFunction D φ ∧ ∫ x, φ x = 0} → ℝ => obsAt v φ := by
  by_cases h : IsTestFunction D φ ∧ ∫ x, φ x = 0
  · have heq : (fun v : {φ : ℂ → ℝ // IsTestFunction D φ ∧ ∫ x, φ x = 0} → ℝ => obsAt v φ) =
        fun v => v ⟨φ, h⟩ := by
      funext v
      simp only [obsAt, h, and_self, ↓reduceDIte]
    rw [heq]
    exact measurable_pi_apply _
  · have heq : (fun v : {φ : ℂ → ℝ // IsTestFunction D φ ∧ ∫ x, φ x = 0} → ℝ => obsAt v φ) =
        fun _ => 0 := by
      funext v
      simp [obsAt, h]
    rw [heq]
    exact measurable_const

/-- The circle coordinate of the observation `v` at the parameter `p`: the limit of the mean-zero pairings
`v(ψ_j - ρ)` along the approximants (route step 2: "take limits of these coordinates"). -/
noncomputable def localCoord (c : ℂ) {R : ℝ} (hR : 0 < R) (p : LocalParam c R)
    (v : {φ : ℂ → ℝ // IsTestFunction (ball c R) φ ∧ ∫ x, φ x = 0} → ℝ) : ℝ :=
  limUnder atTop (fun j => obsAt v (localTest c hR p j))

theorem measurable_localCoord (c : ℂ) {R : ℝ} (hR : 0 < R) (p : LocalParam c R) :
    Measurable fun v : {φ : ℂ → ℝ // IsTestFunction (ball c R) φ ∧ ∫ x, φ x = 0} → ℝ =>
      localCoord c hR p v := by
  have h : ∀ j, Measurable fun v : {φ : ℂ → ℝ // IsTestFunction (ball c R) φ ∧ ∫ x, φ x = 0} → ℝ =>
      obsAt v (localTest c hR p j) := fun j => measurable_obsAt _
  exact (StronglyMeasurable.limUnder fun j => (h j).stronglyMeasurable).measurable

/-! ### 3. Identification of the circle coordinates (almost surely) -/

/-- `φ · log‖·‖` is integrable for a test function `φ` whose support avoids the origin (the integrals in
`fieldPairing` are then genuine Lebesgue integrals). -/
theorem integrable_mul_log_norm {U : Set ℂ} {φ : ℂ → ℝ} (hφ : IsTestFunction U φ) (h0 : (0 : ℂ) ∉ U) :
    Integrable fun x => φ x * Real.log ‖x‖ := by
  have hsub : tsupport φ ⊆ U := hφ.2.2
  have h0' : (0 : ℂ) ∉ tsupport φ := fun h => h0 (hsub h)
  have hc : ContinuousOn (fun x => φ x * Real.log ‖x‖) (tsupport φ) := by
    refine (hφ.1.continuous.continuousOn).mul (ContinuousOn.log continuous_norm.continuousOn ?_)
    intro x hx
    exact norm_ne_zero_iff.2 (fun h => h0' (h ▸ hx))
  have hint : IntegrableOn (fun x => φ x * Real.log ‖x‖) (tsupport φ) :=
    hc.integrableOn_compact hφ.2.1
  have hsupp : Function.support (fun x => φ x * Real.log ‖x‖) ⊆ tsupport φ :=
    fun x hx => subset_tsupport φ (fun h => hx (by simp [h]))
  exact (integrableOn_iff_integrable_of_support_subset hsupp).1 hint

/-- The circle average of the logarithm of the modulus, in the form used by `fieldCircleAverage`. -/
theorem circleAverage_log_norm_eq_max {r : ℝ} (hr : 0 < r) (x : ℂ) :
    Real.circleAverage (fun y : ℂ => Real.log ‖y‖) x r = Real.log (max r ‖x‖) := by
  have h := circleAverage_log_norm_sub_eq x 0 hr
  simpa only [sub_zero] using h

/-- **Circle coordinates of the GFF, a.s.** For a whole-plane GFF `h^ℂ` with circle averages `hcirc`, the
coordinate of the observation `v = localMeanZeroObs α D (hC ω)` at a fixed parameter `p` equals the centred
circle average `h_r(x) - ⟨h, ρ⟩` almost surely (route steps 1-2; the centring constant is `fieldPairing α hC ρ`,
which the decoder cannot see). Linearity of the pairings on the countably many tests `ψ_j - ρ` is
`IsWholePlaneGFF.ae_pairing_linear_combination`; the limits are `ae_tendsto_circleApprox` (a.s.) and
`tendsto_unitCircleDensity_mul_log` (deterministic). -/
theorem ae_localCoord_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (α : ℝ) (c : ℂ) {R : ℝ} (hR : 0 < R) (h0 : (0 : ℂ) ∉ ball c R) (p : LocalParam c R) :
    ∀ᵐ ω ∂P, localCoord c hR p (localMeanZeroObs α (ball c R) (hC ω)) =
      hcirc ω p.1.1 p.1.2 - α * Real.log (max p.1.1 ‖p.1.2‖) - fieldPairing α (hC ω) (bumpRho c hR) := by
  have hr : 0 < p.1.1 := localParam_radius_pos p
  set N := localShift c p with hN_def
  set ψ : ℕ → ℂ → ℝ := fun j => circleApprox hr p.1.2 (j + N) with hψ_def
  have hρ : IsTestFunction univ (bumpRho c hR) :=
    ⟨(bumpRho_isTest c hR).1, (bumpRho_isTest c hR).2.1, subset_univ _⟩
  -- (a) the pairing of the test `ψ_j - ρ` is the difference of the pairings (a.s., all `j`)
  have hlin : ∀ᵐ ω ∂P, ∀ j, hC ω (localTest c hR p j) = hC ω (ψ j) - hC ω (bumpRho c hR) := by
    refine ae_all_iff.2 fun j => ?_
    have hψj : IsTestFunction univ (ψ j) :=
      isTestFunction_circleApprox hr p.1.2 (j + N)
    have h := IsWholePlaneGFF.ae_pairing_linear_combination hGFF hψj hρ 1 (-1)
    filter_upwards [h] with ω hω
    have hfun : (fun y => 1 * ψ j y + (-1) * bumpRho c hR y) = localTest c hR p j := by
      funext y
      simp only [localTest, hψ_def, one_mul, neg_mul, Pi.sub_apply]
      ring
    rw [hfun] at hω
    rw [hω]
    ring
  -- (b) the limit of the pairings of the approximants, a.s. and deterministically
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun j => hC ω (ψ j)) atTop (𝓝 (hcirc ω p.1.1 p.1.2)) := by
    have h := ae_tendsto_circleApprox hGFF hr p.1.2
    filter_upwards [h] with ω hω
    exact (tendsto_add_atTop_iff_nat N).2 hω
  have hlog : Tendsto (fun j => ∫ y, ψ j y * Real.log ‖y‖) atTop
      (𝓝 (Real.log (max p.1.1 ‖p.1.2‖))) := by
    have hδ : ∀ j : ℕ, 0 < p.1.1 * approxEta p.1.1 (j + N) := fun j => mul_pos hr (approxEta_pos hr _)
    have hsmall : ∀ η : ℝ, 0 < η → ∃ M : ℕ, ∀ j, M ≤ j →
        p.1.1 * approxEta p.1.1 (j + N) ≤ p.1.1 * η := by
      intro η hη
      obtain ⟨M, hM⟩ := eventually_approxEta_lt (r := p.1.1) hη
      exact ⟨M, fun j hj => mul_le_mul_of_nonneg_left (le_of_lt (hM (j + N) (by omega))) hr.le⟩
    have h := tendsto_unitCircleDensity_mul_log (r := p.1.1)
      (δ := fun j => p.1.1 * approxEta p.1.1 (j + N)) hr hδ hsmall p.1.2 0
    simp only [sub_zero] at h
    exact h
  -- (c) integrability of the logarithmic integrands (the approximants are tests in the disc)
  have hψD : ∀ j, IsTestFunction (ball c R) (ψ j) := fun j =>
    ⟨(isTestFunction_circleApprox hr p.1.2 (j + N)).1, (isTestFunction_circleApprox hr p.1.2 (j + N)).2.1,
      localShift_spec c p (j + N) (Nat.le_add_left _ _)⟩
  have hI : ∀ j, Integrable fun y => ψ j y * Real.log ‖y‖ := fun j =>
    integrable_mul_log_norm (hψD j) h0
  have hIρ : Integrable fun y => bumpRho c hR y * Real.log ‖y‖ :=
    integrable_mul_log_norm (bumpRho_isTest c hR) h0
  -- (d) the pairing splits as the difference, once the linearity holds at `j`
  have hsplit : ∀ ω, (∀ j, hC ω (localTest c hR p j) = hC ω (ψ j) - hC ω (bumpRho c hR)) →
      ∀ j, fieldPairing α (hC ω) (localTest c hR p j) =
        fieldPairing α (hC ω) (ψ j) - fieldPairing α (hC ω) (bumpRho c hR) := by
    intro ω hω j
    have hint : (∫ y, localTest c hR p j y * Real.log ‖y‖) =
        (∫ y, ψ j y * Real.log ‖y‖) - ∫ y, bumpRho c hR y * Real.log ‖y‖ := by
      rw [← integral_sub (hI j) hIρ]
      congr 1
      funext y
      simp only [localTest, Pi.sub_apply, hψ_def]
      ring
    unfold fieldPairing
    rw [hω j, hint]
    ring
  -- (e) the observation on the tests is the pairing, and the coordinate is the limit
  filter_upwards [hlin, hlim] with ω hωlin hωlim
  have hobs : ∀ j, obsAt (localMeanZeroObs α (ball c R) (hC ω)) (localTest c hR p j) =
      fieldPairing α (hC ω) (localTest c hR p j) := fun j => by
    have hadm := localTest_isTest c hR p j
    simp only [obsAt, hadm, and_self, ↓reduceDIte]
    rfl
  have h1 : Tendsto (fun j => fieldPairing α (hC ω) (ψ j)) atTop
      (𝓝 (hcirc ω p.1.1 p.1.2 - α * Real.log (max p.1.1 ‖p.1.2‖))) := by
    unfold fieldPairing
    exact hωlim.sub (hlog.const_mul α)
  have h2 : Tendsto (fun j => fieldPairing α (hC ω) (localTest c hR p j)) atTop
      (𝓝 (hcirc ω p.1.1 p.1.2 - α * Real.log (max p.1.1 ‖p.1.2‖) - fieldPairing α (hC ω) (bumpRho c hR))) := by
    have heq : (fun j => fieldPairing α (hC ω) (localTest c hR p j)) =
        fun j => fieldPairing α (hC ω) (ψ j) - fieldPairing α (hC ω) (bumpRho c hR) :=
      funext (hsplit ω hωlin)
    rw [heq]
    exact h1.sub_const _
  unfold localCoord
  have heq' : (fun j => obsAt (localMeanZeroObs α (ball c R) (hC ω)) (localTest c hR p j)) =
      fun j => fieldPairing α (hC ω) (localTest c hR p j) := funext hobs
  rw [heq']
  exact h2.limUnder_eq

/-- MQ-lh-12 step 3 for the local domain: a countable dense sequence `d` of `LocalParam c R` and a measurable
decoder `decode` with `decode (n ↦ f (d n)) = f` for every continuous `f` on `LocalParam c R`. -/
theorem exists_localDecoder (c : ℂ) {R : ℝ} (hR : 0 < R) :
    ∃ d : ℕ → LocalParam c R, ∃ decode : (ℕ → ℝ) → C(LocalParam c R, ℝ), Measurable decode ∧
      ∀ f : C(LocalParam c R, ℝ), decode (fun n => f (d n)) = f := by
  have := localParam_nonempty c hR
  obtain ⟨d, -, decode, hm, hdec⟩ := exists_dense_decode_polish (LocalParam c R)
  exact ⟨d, decode, hm, hdec⟩

/-- MQ-lh-12 step 4: almost surely the decoded local profile of the mean-zero observation is the continuous
function `p ↦ h^ℂ_{r}(x) - α log max(r,|x|) - (h, ρ)` on `LocalParam c R` (the centred circle profile). -/
theorem ae_decode_localCoord_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (α : ℝ) (c : ℂ) {R : ℝ} (hR : 0 < R) (h0 : (0 : ℂ) ∉ ball c R)
    (d : ℕ → LocalParam c R) (decode : (ℕ → ℝ) → C(LocalParam c R, ℝ))
    (hdec : ∀ f : C(LocalParam c R, ℝ), decode (fun n => f (d n)) = f) :
    ∀ᵐ ω ∂P, ∃ G : C(LocalParam c R, ℝ),
      (∀ p : LocalParam c R, G p = hcirc ω p.1.1 p.1.2 - α * Real.log (max p.1.1 ‖p.1.2‖) -
        fieldPairing α (hC ω) (bumpRho c hR)) ∧
      decode (fun n => localCoord c hR (d n) (localMeanZeroObs α (ball c R) (hC ω))) = G := by
  have hco : ∀ᵐ ω ∂P, ∀ n, localCoord c hR (d n) (localMeanZeroObs α (ball c R) (hC ω)) =
      hcirc ω (d n).1.1 (d n).1.2 - α * Real.log (max (d n).1.1 ‖(d n).1.2‖) -
        fieldPairing α (hC ω) (bumpRho c hR) :=
    ae_all_iff.2 fun n => ae_localCoord_eq hGFF α c hR h0 (d n)
  filter_upwards [hGFF.ae_continuousOn_circle, hco] with ω hω hωn
  have hpos : ∀ p : LocalParam c R, 0 < p.1.1 := fun p => localParam_radius_pos p
  have hmem : ∀ p : LocalParam c R, ((p.1.1, p.1.2) : ℝ × ℂ) ∈ Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℂ) :=
    fun p => ⟨hpos p, Set.mem_univ _⟩
  have hpair : Continuous fun p : LocalParam c R => ((p.1.1, p.1.2) : ℝ × ℂ) :=
    (continuous_fst.comp continuous_subtype_val).prodMk (continuous_snd.comp continuous_subtype_val)
  have hcirc_c : Continuous fun p : LocalParam c R => hcirc ω p.1.1 p.1.2 :=
    hω.comp_continuous hpair hmem
  have hlog : Continuous fun p : LocalParam c R => Real.log (max p.1.1 ‖p.1.2‖) :=
    Continuous.log ((continuous_fst.comp continuous_subtype_val).max
      (continuous_norm.comp (continuous_snd.comp continuous_subtype_val)))
      fun p => ne_of_gt (lt_of_lt_of_le (hpos p) (le_max_left _ _))
  have hgc : Continuous fun p : LocalParam c R => hcirc ω p.1.1 p.1.2 - α * Real.log (max p.1.1 ‖p.1.2‖) -
      fieldPairing α (hC ω) (bumpRho c hR) :=
    (hcirc_c.sub (continuous_const.mul hlog)).sub continuous_const
  refine ⟨⟨_, hgc⟩, fun p => rfl, ?_⟩
  have hfun : (fun n => localCoord c hR (d n) (localMeanZeroObs α (ball c R) (hC ω))) =
      fun n => (⟨_, hgc⟩ : C(LocalParam c R, ℝ)) (d n) :=
    funext fun n => hωn n
  rw [hfun, hdec]

end LocalDecoderCommon

end HarmonicBalls

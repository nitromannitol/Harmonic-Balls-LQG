import HarmonicBalls.FirstPass.S11r.Frozen
import HarmonicBalls.FirstPass.Frozen.S11c
import HarmonicBalls.FirstPass.S11at.Producers
import HarmonicBalls.FirstPass.S11u.Kernel
import HarmonicBalls.Steps.Sec11.PairingCovarianceLinearity
import HarmonicBalls.Proofs.Sec6.ContinuousWeylCircleAverage

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
theorem ae_tendsto_localPairing {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (α : ℝ) (c : ℂ) {R : ℝ} (hR : 0 < R) (h0 : (0 : ℂ) ∉ ball c R) (p : LocalParam c R) :
    ∀ᵐ ω ∂P, Tendsto (fun j => obsAt (localMeanZeroObs α (ball c R) (hC ω)) (localTest c hR p j)) atTop
      (𝓝 (hcirc ω p.1.1 p.1.2 - α * Real.log (max p.1.1 ‖p.1.2‖) - fieldPairing α (hC ω) (bumpRho c hR))) := by
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
  have heq' : (fun j => obsAt (localMeanZeroObs α (ball c R) (hC ω)) (localTest c hR p j)) =
      fun j => fieldPairing α (hC ω) (localTest c hR p j) := funext hobs
  rw [heq']
  exact h2

/-- **Circle coordinates of the GFF, a.s.** The coordinate of the mean-zero observation at `p` is the centred circle
average `h_r(x) - α log max(r,|x|) - (h, ρ)` almost surely (`ae_tendsto_localPairing` and `Tendsto.limUnder_eq`). -/
theorem ae_localCoord_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (α : ℝ) (c : ℂ) {R : ℝ} (hR : 0 < R) (h0 : (0 : ℂ) ∉ ball c R) (p : LocalParam c R) :
    ∀ᵐ ω ∂P, localCoord c hR p (localMeanZeroObs α (ball c R) (hC ω)) =
      hcirc ω p.1.1 p.1.2 - α * Real.log (max p.1.1 ‖p.1.2‖) - fieldPairing α (hC ω) (bumpRho c hR) := by
  filter_upwards [ae_tendsto_localPairing hGFF α c hR h0 p] with ω hω
  unfold localCoord
  exact hω.limUnder_eq

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

/-! ### Generic countable determination on a locally compact metric space (MQ-lh-12 step 6)

Ported from `ProfileDecoderDerived` (`TestFamily`, `exists_testFamily`) with `ℂ` replaced by a locally compact
metric space `X` and the balls `closedBall 0 n` replaced by a compact exhaustion `K`. Applied to `X = ↥(ball c R)`. -/

section Vague

open scoped CompactlySupported

variable {X : Type*} [MetricSpace X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]

/-- A countable family of compactly supported test functions adapted to a compact exhaustion `K` of `X`:
(i) each `K n` is covered by a member `D m` with `0 ≤ D m` and `1 ≤ D m` on `K n` (mass bound);
(ii) every `f` supported in `K n` is approximated uniformly, to any `δ > 0`, by some `D m` supported in `K n`. -/
structure TestFamilyX (K : ℕ → Set X) where
  D : ℕ → C_c(X, ℝ)
  mass : ∀ n : ℕ, ∃ m : ℕ, (∀ x : X, 0 ≤ D m x) ∧ ∀ x ∈ K n, 1 ≤ D m x
  approx : ∀ (n : ℕ) (f : C_c(X, ℝ)), tsupport ⇑f ⊆ K n → ∀ δ : ℝ, 0 < δ →
    ∃ m : ℕ, tsupport ⇑(D m) ⊆ K n ∧ ∀ x : X, |f x - D m x| ≤ δ

omit [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
/-- Urysohn cut-off in a locally compact Hausdorff space: a nonnegative compactly supported continuous function
equal to `1` on a compact set `K`. -/
theorem exists_cc_one_on {K : Set X} (hK : IsCompact K) :
    ∃ g : C_c(X, ℝ), (∀ x, 0 ≤ g x) ∧ ∀ x ∈ K, 1 ≤ g x := by
  obtain ⟨K', hK'c, hKK', -⟩ := exists_compact_between hK isOpen_univ (subset_univ K)
  obtain ⟨f, hf0, hf1, hfI⟩ := exists_continuous_zero_one_of_isCompact' hK
    (isOpen_interior.isClosed_compl) (Set.disjoint_compl_right_iff_subset.2 hKK')
  have hsupp : HasCompactSupport f := by
    refine HasCompactSupport.intro hK'c fun x hx => hf0 ?_
    exact fun h => hx (interior_subset h)
  exact ⟨{ toContinuousMap := f, hasCompactSupport' := hsupp }, fun x => (hfI x).1,
    fun x hx => le_of_eq (hf1 hx).symm⟩

/-- Restriction of a compactly supported continuous function to a compact piece `K n` of the exhaustion. -/
def restrictK (K : ℕ → Set X) (n : ℕ) (g : C_c(X, ℝ)) : C(K n, ℝ) :=
  ⟨fun x => g x.1, g.continuous.comp continuous_subtype_val⟩

omit [MeasurableSpace X] [BorelSpace X] in
/-- The countable family exists: the countable dense subsets of the restrictions to the compact pieces, lifted
back to test functions supported in `K n`, together with a cut-off for each `n`. -/
theorem exists_testFamilyX (K : ℕ → Set X) (hKc : ∀ n, IsCompact (K n)) : Nonempty (TestFamilyX K) := by
  have hcpt : ∀ n, CompactSpace (K n) := fun n => isCompact_iff_compactSpace.mp (hKc n)
  classical
  let S : ℕ → Set C_c(X, ℝ) := fun n => {g | tsupport ⇑g ⊆ K n}
  have hsep : ∀ n : ℕ, TopologicalSpace.IsSeparable (restrictK K n '' S n) := by
    intro n
    exact TopologicalSpace.IsSeparable.of_separableSpace _
  have hex : ∀ n : ℕ, ∃ t ⊆ restrictK K n '' S n, t.Countable ∧ restrictK K n '' S n ⊆ closure t :=
    fun n => (hsep n).exists_countable_dense_subset
  choose t hts htc hdense using hex
  have hlift : ∀ n, ∀ τ ∈ t n, ∃ g ∈ S n, restrictK K n g = τ := fun n τ hτ => hts n hτ
  choose! lift hliftS hliftR using hlift
  choose cut hcut0 hcut1 using fun n => exists_cc_one_on (hKc n)
  let Dset : Set C_c(X, ℝ) := Set.range cut ∪ ⋃ n, lift n '' t n
  have hcount : Dset.Countable :=
    (countable_range _).union (countable_iUnion fun n => (htc n).image _)
  obtain ⟨D, hD⟩ := hcount.exists_eq_range ⟨cut 0, Or.inl ⟨0, rfl⟩⟩
  have hmemD : ∀ g ∈ Dset, ∃ m, D m = g := fun g hg => by
    rw [hD] at hg
    exact hg
  refine ⟨⟨D, ?_, ?_⟩⟩
  · intro n
    obtain ⟨m, hm⟩ := hmemD (cut n) (Or.inl ⟨n, rfl⟩)
    exact ⟨m, fun x => by rw [hm]; exact hcut0 n x, fun x hx => by rw [hm]; exact hcut1 n x hx⟩
  · intro n f hf δ hδ
    have hfS : f ∈ S n := hf
    obtain ⟨b, hb, hdist⟩ := Metric.mem_closure_iff.1 (hdense n ⟨f, hfS, rfl⟩) δ hδ
    have hdmem : lift n b ∈ Dset := Or.inr (mem_iUnion.2 ⟨n, mem_image_of_mem _ hb⟩)
    obtain ⟨m, hm⟩ := hmemD _ hdmem
    have hdS : tsupport ⇑(lift n b) ⊆ K n := hliftS n b hb
    refine ⟨m, ?_, fun x => ?_⟩
    · rw [hm]
      exact hdS
    · rw [hm]
      by_cases hx : x ∈ K n
      · have h3 : dist (f x) (lift n b x) ≤ dist (restrictK K n f) (restrictK K n (lift n b)) :=
          ContinuousMap.dist_apply_le_dist (f := restrictK K n f)
            (g := restrictK K n (lift n b)) (⟨x, hx⟩ : K n)
        rw [hliftR n b hb] at h3
        rw [Real.dist_eq] at h3
        exact h3.trans hdist.le
      · have hf0 : f x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hf h))
        have hd0 : lift n b x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hdS h))
        rw [hf0, hd0, sub_zero, abs_zero]
        exact hδ.le

theorem integrable_of_ccX (g : C_c(X, ℝ)) (μ : Measure X) [IsLocallyFiniteMeasure μ] :
    Integrable g μ :=
  g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport

/-- Vague convergence is tested on the countable family: if all the integrals of the members `D m` converge, so
do the integrals of every `f ∈ C_c(X, ℝ)` (ε-argument of `ProfileDecoderDerived.tendsto_of_testFamily`). -/
theorem tendsto_of_testFamilyX {K : ℕ → Set X} (hKs : ∀ s : Set X, IsCompact s → ∃ n, s ⊆ K n)
    (T : TestFamilyX K) {ν : ℕ → Measure X} (hν : ∀ k, IsLocallyFiniteMeasure (ν k))
    (hconv : ∀ m : ℕ, ∃ L, Tendsto (fun k => ∫ x, T.D m x ∂(ν k)) atTop (𝓝 L))
    (f : C_c(X, ℝ)) : ∃ L, Tendsto (fun k => ∫ x, f x ∂(ν k)) atTop (𝓝 L) := by
  obtain ⟨n, hsupp⟩ := hKs (tsupport ⇑f) f.hasCompactSupport.isCompact
  obtain ⟨m₀, hm₀nonneg, hm₀one⟩ := T.mass n
  obtain ⟨L₀, hL₀⟩ := hconv m₀
  have hK₀ : 0 < |L₀| + 1 := by positivity
  have hev : ∀ᶠ k in atTop, ∫ x, T.D m₀ x ∂(ν k) < |L₀| + 1 :=
    hL₀.eventually (gt_mem_nhds (by linarith [le_abs_self L₀]))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hev
  have hcauchy : CauchySeq (fun k => ∫ x, f x ∂(ν k)) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    set δ : ℝ := ε / (4 * (|L₀| + 1)) with hδdef
    have hδ : 0 < δ := div_pos hε (by positivity)
    obtain ⟨m₁, hm₁supp, hm₁close⟩ := T.approx n f hsupp δ hδ
    obtain ⟨L₁, hL₁⟩ := hconv m₁
    obtain ⟨N₁, hN₁⟩ := Metric.cauchySeq_iff.1 hL₁.cauchySeq (ε / 2) (by positivity)
    have key : ∀ k, N₀ ≤ k → |∫ x, f x ∂(ν k) - ∫ x, T.D m₁ x ∂(ν k)| ≤ ε / 4 := by
      intro k hk
      have := hν k
      have hpt : ∀ x, ‖f x - T.D m₁ x‖ ≤ δ * T.D m₀ x := by
        intro x
        by_cases hx : x ∈ K n
        · have h1 : ‖f x - T.D m₁ x‖ ≤ δ := by
            rw [Real.norm_eq_abs]
            exact hm₁close x
          have h2 : 1 ≤ T.D m₀ x := hm₀one x hx
          calc ‖f x - T.D m₁ x‖ ≤ δ := h1
            _ = δ * 1 := (mul_one δ).symm
            _ ≤ δ * T.D m₀ x := mul_le_mul_of_nonneg_left h2 hδ.le
        · have hf0 : f x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hsupp h))
          have hd0 : T.D m₁ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hm₁supp h))
          rw [hf0, hd0, sub_zero, norm_zero]
          exact mul_nonneg hδ.le (hm₀nonneg x)
      have hb : ‖∫ x, (f x - T.D m₁ x) ∂(ν k)‖ ≤ ∫ x, δ * T.D m₀ x ∂(ν k) :=
        norm_integral_le_of_norm_le ((integrable_of_ccX (T.D m₀) (ν k)).const_mul δ)
          (Eventually.of_forall hpt)
      rw [integral_const_mul, integral_sub (integrable_of_ccX f _) (integrable_of_ccX (T.D m₁) _),
        Real.norm_eq_abs] at hb
      have hc : ∫ x, T.D m₀ x ∂(ν k) ≤ |L₀| + 1 := (hN₀ k hk).le
      calc |∫ x, f x ∂(ν k) - ∫ x, T.D m₁ x ∂(ν k)| ≤ δ * ∫ x, T.D m₀ x ∂(ν k) := hb
        _ ≤ δ * (|L₀| + 1) := mul_le_mul_of_nonneg_left hc hδ.le
        _ = ε / 4 := by rw [hδdef]; field_simp
    refine ⟨max N₀ N₁, fun p hp q hq => ?_⟩
    have hp' : N₀ ≤ p := (le_max_left _ _).trans hp
    have hq' : N₀ ≤ q := (le_max_left _ _).trans hq
    have hb : |(∫ x, T.D m₁ x ∂(ν p)) - ∫ x, T.D m₁ x ∂(ν q)| < ε / 2 := by
      have := hN₁ p ((le_max_right _ _).trans hp) q ((le_max_right _ _).trans hq)
      rwa [Real.dist_eq] at this
    have kp := key p hp'
    have kq := key q hq'
    have h2 : |(∫ x, T.D m₁ x ∂(ν q)) - ∫ x, f x ∂(ν q)| ≤ ε / 4 := by
      rw [abs_sub_comm]
      exact kq
    have h3 := abs_add_three ((∫ x, f x ∂(ν p)) - ∫ x, T.D m₁ x ∂(ν p))
      ((∫ x, T.D m₁ x ∂(ν p)) - ∫ x, T.D m₁ x ∂(ν q)) ((∫ x, T.D m₁ x ∂(ν q)) - ∫ x, f x ∂(ν q))
    have h4 : |(∫ x, f x ∂(ν p)) - ∫ x, f x ∂(ν q)| =
        |((∫ x, f x ∂(ν p)) - ∫ x, T.D m₁ x ∂(ν p)) + ((∫ x, T.D m₁ x ∂(ν p)) - ∫ x, T.D m₁ x ∂(ν q))
          + ((∫ x, T.D m₁ x ∂(ν q)) - ∫ x, f x ∂(ν q))| := by
      congr 1
      ring
    rw [Real.dist_eq]
    linarith [h3, h4, kp, hb, h2]
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcauchy
  exact ⟨L, hL⟩

/-- The limit of the integrals along a sequence of locally finite measures on which the integrals of all
`C_c(X, ℝ)` functions converge: a positive linear functional on `C_c(X, ℝ)` (port of
`ProfileDecoderDerived.limFunctional`). -/
noncomputable def limFunctionalX {ν : ℕ → Measure X} (hν : ∀ k, IsLocallyFiniteMeasure (ν k))
    (hconv : ∀ g : C_c(X, ℝ), ∃ L, Tendsto (fun k => ∫ x, g x ∂(ν k)) atTop (𝓝 L)) :
    C_c(X, ℝ) →ₚ[ℝ] ℝ where
  toFun g := limUnder atTop (fun k => ∫ x, g x ∂(ν k))
  map_add' f g := by
    show limUnder atTop (fun k => ∫ x, (f + g) x ∂(ν k)) =
      limUnder atTop (fun k => ∫ x, f x ∂(ν k)) + limUnder atTop (fun k => ∫ x, g x ∂(ν k))
    refine tendsto_nhds_unique (tendsto_nhds_limUnder (hconv (f + g))) ?_
    refine Tendsto.congr (fun k => ?_)
      ((tendsto_nhds_limUnder (hconv f)).add (tendsto_nhds_limUnder (hconv g)))
    have := hν k
    simp only [CompactlySupportedContinuousMap.coe_add, Pi.add_apply]
    exact (integral_add (integrable_of_ccX f _) (integrable_of_ccX g _)).symm
  map_smul' c f := by
    show limUnder atTop (fun k => ∫ x, (c • f) x ∂(ν k)) =
      c • limUnder atTop (fun k => ∫ x, f x ∂(ν k))
    rw [smul_eq_mul]
    refine tendsto_nhds_unique (tendsto_nhds_limUnder (hconv (c • f))) ?_
    refine Tendsto.congr (fun k => ?_) ((tendsto_nhds_limUnder (hconv f)).const_mul c)
    have := hν k
    simp only [CompactlySupportedContinuousMap.smul_apply, smul_eq_mul]
    exact (integral_const_mul c _).symm
  monotone' := by
    intro f g hfg
    show limUnder atTop (fun k => ∫ x, f x ∂(ν k)) ≤ limUnder atTop (fun k => ∫ x, g x ∂(ν k))
    refine le_of_tendsto_of_tendsto' (tendsto_nhds_limUnder (hconv f))
      (tendsto_nhds_limUnder (hconv g)) (fun k => ?_)
    have := hν k
    exact integral_mono (integrable_of_ccX f _) (integrable_of_ccX g _) (fun x => hfg x)

/-- Open-set test functions on `X` (port of `exists_open_mass_test_functions`, `LPStage/LQGMeasureDerived.lean:286`):
for an open `U`, continuous compactly supported `f n` with `μ U = ⨆ n, ∫ f n dμ` for every locally finite `μ`. -/
theorem exists_open_mass_test_functionsX {U : Set X} (hU : IsOpen U) :
    ∃ f : ℕ → X → ℝ, (∀ n, Continuous (f n)) ∧ (∀ n, HasCompactSupport (f n)) ∧
      ∀ μ : Measure X, IsLocallyFiniteMeasure μ → μ U = ⨆ n, ENNReal.ofReal (∫ x, f n x ∂μ) := by
  classical
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let K : CompactExhaustion U := CompactExhaustion.choice U
  let C : ℕ → Set X := fun n => Subtype.val '' K n
  have hC (n : ℕ) : IsCompact (C n) := (K.isCompact n).image continuous_subtype_val
  have hCU (n : ℕ) : C n ⊆ U := by
    rintro x ⟨y, -, rfl⟩
    exact y.property
  have hmono : Monotone C := fun i j hij => image_mono (K.subset hij)
  have hcover : (⋃ n, C n) = U := by
    rw [← image_iUnion, K.iUnion_eq, image_univ]
    exact Subtype.range_coe
  have hcut (n : ℕ) : ∃ g : C(X, ℝ), EqOn g 1 (C n) ∧ EqOn g 0 Uᶜ ∧
      HasCompactSupport g ∧ ∀ x, g x ∈ Icc (0 : ℝ) 1 :=
    exists_continuous_one_zero_of_isCompact (hC n) hU.isClosed_compl
      (disjoint_compl_right_iff_subset.mpr (hCU n))
  choose g hgOne hgZero hgComp hgRange using hcut
  refine ⟨fun n => g n, fun n => (g n).continuous, hgComp, ?_⟩
  intro μ hμ
  let _ := hμ
  apply le_antisymm
  · rw [← hcover, hmono.measure_iUnion]
    apply iSup_le
    intro n
    apply le_iSup_of_le n
    apply ((g n).continuous.integrable_of_hasCompactSupport (hgComp n)).measure_le_integral
    · exact Filter.Eventually.of_forall fun x => (hgRange n x).1
    · intro x hx
      simpa using le_of_eq (hgOne n hx).symm
  · apply iSup_le
    intro n
    apply integral_le_measure
    · intro x hx
      exact (hgRange n x).2
    · intro x hx
      exact le_of_eq (hgZero n hx)

/-- A family of locally finite measures on `X` is measurable once its values on open sets are measurable
(port of `measurable_measure_of_isOpen`, `LPStage/LQGMeasureDerived.lean:328`, with the balls replaced by the
interiors of a compact exhaustion of `X`). -/
theorem measurable_measure_of_isOpenX {Ω : Type*} [MeasurableSpace Ω] {ν : Ω → Measure X}
    (hloc : ∀ ω, IsLocallyFiniteMeasure (ν ω))
    (hopen : ∀ U : Set X, IsOpen U → Measurable (fun ω => ν ω U)) : Measurable ν := by
  let K : CompactExhaustion X := CompactExhaustion.choice X
  let B : ℕ → Set X := fun n => interior (K n)
  have hB (n : ℕ) : IsOpen (B n) := isOpen_interior
  have hmono : Monotone B := fun i j hij => interior_mono (K.subset hij)
  have hBU : (⋃ n, B n) = univ := by
    refine eq_univ_of_forall fun x => ?_
    have hx : x ∈ ⋃ n, K n := by rw [K.iUnion_eq]; exact mem_univ x
    obtain ⟨m, hm⟩ := mem_iUnion.1 hx
    exact mem_iUnion.2 ⟨m + 1, K.subset_interior_succ m hm⟩
  have hfinite (n : ℕ) (ω : Ω) : IsFiniteMeasure ((ν ω).restrict (B n)) := by
    let _ := hloc ω
    apply isFiniteMeasure_restrict.mpr
    apply ne_of_lt
    exact lt_of_le_of_lt (measure_mono interior_subset) (K.isCompact n).measure_lt_top
  have hres (n : ℕ) : Measurable (fun ω => (ν ω).restrict (B n)) := by
    let _ : ∀ ω, IsFiniteMeasure ((ν ω).restrict (B n)) := hfinite n
    apply Measurable.measure_of_isPiSystem BorelSpace.measurable_eq isPiSystem_isOpen
    · intro U hU
      change IsOpen U at hU
      simpa only [Measure.restrict_apply hU.measurableSet] using hopen (U ∩ B n) (hU.inter (hB n))
    · simpa only [Measure.restrict_apply MeasurableSet.univ, univ_inter] using hopen (B n) (hB n)
  apply Measure.measurable_measure.mpr
  intro S hS
  have heq (ω : Ω) : ν ω S = ⨆ n, ((ν ω).restrict (B n)) S := by
    simp only [Measure.restrict_apply hS]
    rw [← Monotone.measure_iUnion]
    · congr 1
      rw [← inter_iUnion, hBU, inter_univ]
    · intro i j hij
      exact inter_subset_inter_right S (hmono hij)
  simp_rw [heq]
  exact Measurable.iSup fun n => (Measure.measurable_coe hS).comp (hres n)

section Decoder

variable {Y : Type*} [MeasurableSpace Y]

/-- The parameters at which all test integrals `∫ T.D m dν_k(y)` converge. -/
def convSetX {K : ℕ → Set X} (T : TestFamilyX K) (ν : Y → ℕ → Measure X) : Set Y :=
  {y | ∀ m : ℕ, ∃ L, Tendsto (fun k => ∫ x, T.D m x ∂(ν y k)) atTop (𝓝 L)}

omit [LocallyCompactSpace X] [SecondCountableTopology X] [BorelSpace X] in
theorem measurableSet_convSetX {K : ℕ → Set X} (T : TestFamilyX K) {ν : Y → ℕ → Measure X}
    (hmeas : ∀ (g : C_c(X, ℝ)) (k : ℕ), Measurable fun y => ∫ x, g x ∂(ν y k)) :
    MeasurableSet (convSetX T ν) := by
  have h : convSetX T ν = ⋂ m : ℕ, {y | ∃ L, Tendsto (fun k => ∫ x, T.D m x ∂(ν y k)) atTop (𝓝 L)} := by
    ext y
    simp [convSetX]
  rw [h]
  exact MeasurableSet.iInter fun m => measurableSet_exists_tendsto fun k => hmeas (T.D m) k

open Classical in
/-- The decoded functional: the vague limit of the approximations on `convSetX`, `0` elsewhere. -/
noncomputable def decoderFunctionalX {K : ℕ → Set X} (hKs : ∀ s : Set X, IsCompact s → ∃ n, s ⊆ K n)
    (T : TestFamilyX K) (ν : Y → ℕ → Measure X) (hloc : ∀ y k, IsLocallyFiniteMeasure (ν y k)) (y : Y) :
    C_c(X, ℝ) →ₚ[ℝ] ℝ :=
  if hy : y ∈ convSetX T ν then
    limFunctionalX (fun k => hloc y k)
      (fun g => tendsto_of_testFamilyX hKs T (fun k => hloc y k) hy g)
  else 0

/-- The decoded measure: the Riesz measure of the decoded functional (`RealRMK.rieszMeasure`). -/
noncomputable def decoderX {K : ℕ → Set X} (hKs : ∀ s : Set X, IsCompact s → ∃ n, s ⊆ K n)
    (T : TestFamilyX K) (ν : Y → ℕ → Measure X) (hloc : ∀ y k, IsLocallyFiniteMeasure (ν y k)) (y : Y) :
    Measure X :=
  RealRMK.rieszMeasure (decoderFunctionalX hKs T ν hloc y)

omit [MeasurableSpace Y] in
theorem integral_decoderX {K : ℕ → Set X} (hKs : ∀ s : Set X, IsCompact s → ∃ n, s ⊆ K n)
    (T : TestFamilyX K) (ν : Y → ℕ → Measure X) (hloc : ∀ y k, IsLocallyFiniteMeasure (ν y k))
    (y : Y) (g : C_c(X, ℝ)) :
    ∫ x, g x ∂(decoderX hKs T ν hloc y) = decoderFunctionalX hKs T ν hloc y g :=
  RealRMK.integral_rieszMeasure _ g

omit [MeasurableSpace Y] in
theorem decoderFunctionalX_of_mem {K : ℕ → Set X} (hKs : ∀ s : Set X, IsCompact s → ∃ n, s ⊆ K n)
    (T : TestFamilyX K) (ν : Y → ℕ → Measure X) (hloc : ∀ y k, IsLocallyFiniteMeasure (ν y k))
    {y : Y} (hy : y ∈ convSetX T ν) (g : C_c(X, ℝ)) :
    decoderFunctionalX hKs T ν hloc y g = limUnder atTop (fun k => ∫ x, g x ∂(ν y k)) := by
  unfold decoderFunctionalX
  split_ifs
  rfl

omit [MeasurableSpace Y] in
theorem decoderFunctionalX_of_not_mem {K : ℕ → Set X} (hKs : ∀ s : Set X, IsCompact s → ∃ n, s ⊆ K n)
    (T : TestFamilyX K) (ν : Y → ℕ → Measure X) (hloc : ∀ y k, IsLocallyFiniteMeasure (ν y k))
    {y : Y} (hy : y ∉ convSetX T ν) (g : C_c(X, ℝ)) :
    decoderFunctionalX hKs T ν hloc y g = 0 := by
  unfold decoderFunctionalX
  split_ifs
  simp

/-- Measurability of the decoded functional in the observation (port of `measurable_decoderFunctional_apply`,
`FirstPass/Phase2/ProfileDecoderDerived.lean:356`). -/
theorem measurable_decoderFunctionalX_apply {K : ℕ → Set X}
    (hKs : ∀ s : Set X, IsCompact s → ∃ n, s ⊆ K n)
    (T : TestFamilyX K) (ν : Y → ℕ → Measure X) (hloc : ∀ y k, IsLocallyFiniteMeasure (ν y k))
    (hmeas : ∀ (g : C_c(X, ℝ)) (k : ℕ), Measurable fun y => ∫ x, g x ∂(ν y k)) (g : C_c(X, ℝ)) :
    Measurable fun y => decoderFunctionalX hKs T ν hloc y g := by
  have hind : ∀ k, Measurable fun y => (convSetX T ν).indicator (fun y => ∫ x, g x ∂(ν y k)) y :=
    fun k => (hmeas g k).indicator (measurableSet_convSetX T hmeas)
  refine measurable_of_tendsto_metrizable hind ?_
  refine tendsto_pi_nhds.2 fun y => ?_
  by_cases hy : y ∈ convSetX T ν
  · simp only [Set.indicator_of_mem hy]
    rw [decoderFunctionalX_of_mem hKs T ν hloc hy g]
    obtain ⟨L, hL⟩ := tendsto_of_testFamilyX hKs T (fun k => hloc y k) hy g
    exact tendsto_nhds_limUnder ⟨L, hL⟩
  · simp only [Set.indicator_of_notMem hy]
    rw [decoderFunctionalX_of_not_mem hKs T ν hloc hy g]
    exact tendsto_const_nhds

/-- The decoder is measurable as a map into measures on `X` (route step 3 measurability; port of
`measurable_decoder`, `FirstPass/Phase2/ProfileDecoderDerived.lean:372`). -/
theorem measurable_decoderX {K : ℕ → Set X} (hKs : ∀ s : Set X, IsCompact s → ∃ n, s ⊆ K n)
    (T : TestFamilyX K) (ν : Y → ℕ → Measure X) (hloc : ∀ y k, IsLocallyFiniteMeasure (ν y k))
    (hmeas : ∀ (g : C_c(X, ℝ)) (k : ℕ), Measurable fun y => ∫ x, g x ∂(ν y k)) :
    Measurable (decoderX hKs T ν hloc) := by
  have hl : ∀ y, IsLocallyFiniteMeasure (decoderX hKs T ν hloc y) := fun y => by
    unfold decoderX
    infer_instance
  refine measurable_measure_of_isOpenX hl (fun U hU => ?_)
  obtain ⟨f, hfc, hfcc, hmass⟩ := exists_open_mass_test_functionsX hU
  have heq : (fun y => decoderX hKs T ν hloc y U) =
      fun y => ⨆ n, ENNReal.ofReal (decoderFunctionalX hKs T ν hloc y ⟨⟨f n, hfc n⟩, hfcc n⟩) := by
    funext y
    rw [hmass (decoderX hKs T ν hloc y) (hl y)]
    congr 1
    funext n
    congr 1
    exact integral_decoderX hKs T ν hloc y ⟨⟨f n, hfc n⟩, hfcc n⟩
  rw [heq]
  exact Measurable.iSup fun n => ENNReal.measurable_ofReal.comp
    (measurable_decoderFunctionalX_apply hKs T ν hloc hmeas _)

end Decoder

end Vague

/-! ### Dyadic approximants on the disc `X = ball c R` (MQ-lh-12 step 5, route (b)-(c))

The density `ε^{γ²/2} e^{γ F(ε,z)}` at scale `ε = 2^{-k}` is read on the projected point `projBall`
(the radial retraction onto `closedBall c (R - 2ε)`), so it is a continuous function of `(F, z)` and bounded on
compacta; on the closed disc `closedBall c (R - 2ε)` the projection is the identity. -/
section Approximants

open scoped CompactlySupported

/-- The disc `ball c R` is locally compact (an open subset of `ℂ`). -/
instance locallyCompactSpace_ball (c : ℂ) (R : ℝ) : LocallyCompactSpace (ball c R) :=
  isOpen_ball.locallyCompactSpace

/-- The Lebesgue measure of the disc `ball c R` (the pullback of `volume` under the inclusion; `Subtype.measureSpace`
is not a global instance). -/
noncomputable def ballVol (c : ℂ) (R : ℝ) : Measure (ball c R) :=
  Measure.comap (Subtype.val : ball c R → ℂ) (volume : Measure ℂ)

theorem isLocallyFiniteMeasure_ballVol (c : ℂ) (R : ℝ) : IsLocallyFiniteMeasure (ballVol c R) := by
  refine ⟨fun x => ?_⟩
  have hx : dist (x : ℂ) c < R := mem_ball.1 x.2
  have hρ : 0 < (R - dist (x : ℂ) c) / 2 := by linarith
  refine ⟨Subtype.val ⁻¹' ball (x : ℂ) ((R - dist (x : ℂ) c) / 2), ?_, ?_⟩
  · exact (isOpen_ball.preimage continuous_subtype_val).mem_nhds (mem_ball_self hρ)
  · unfold ballVol
    rw [(MeasurableEmbedding.subtype_coe measurableSet_ball).comap_apply]
    exact (measure_mono (image_preimage_subset _ _)).trans_lt measure_ball_lt_top

/-- The radial retraction of `ℂ` onto the closed disc `closedBall c s` (the identity on that disc). -/
noncomputable def projBall (c : ℂ) (s : ℝ) (z : ℂ) : ℂ :=
  c + (s / max (dist z c) s) • (z - c)

theorem continuous_projBall {c : ℂ} {s : ℝ} (hs : 0 < s) : Continuous (projBall c s) := by
  have h1 : Continuous fun z : ℂ => s / max (dist z c) s :=
    continuous_const.div ((continuous_id.dist continuous_const).max continuous_const)
      fun z => (lt_max_of_lt_right hs).ne'
  have h2 : Continuous fun z : ℂ => z - c := continuous_id.sub continuous_const
  unfold projBall
  exact continuous_const.add (h1.smul h2)

theorem dist_projBall_le {c : ℂ} {s : ℝ} (hs : 0 < s) (z : ℂ) : dist (projBall c s z) c ≤ s := by
  unfold projBall
  rw [dist_eq_norm, add_sub_cancel_left, norm_smul,
    Real.norm_of_nonneg (div_nonneg hs.le (le_max_of_le_right hs.le)), ← dist_eq_norm]
  rw [div_mul_eq_mul_div, div_le_iff₀ (lt_max_of_lt_right hs)]
  exact mul_le_mul_of_nonneg_left (le_max_left _ _) hs.le

theorem projBall_of_dist_le {c : ℂ} {s : ℝ} (hs : 0 < s) {z : ℂ} (hz : dist z c ≤ s) :
    projBall c s z = z := by
  unfold projBall
  rw [max_eq_right hz, div_self hs.ne', one_smul, add_sub_cancel]

/-- The point `(2^{-k}, projBall z)` of `LocalParam c R`, for `2ε < R`. -/
noncomputable def localPoint (c : ℂ) {R ε : ℝ} (hε : 0 < ε) (h2 : 2 * ε < R) (z : ℂ) : LocalParam c R :=
  ⟨(ε, projBall c (R - 2 * ε) z), ⟨hε, by
    show dist (projBall c (R - 2 * ε) z) c + ε < R
    linarith [dist_projBall_le (c := c) (sub_pos.2 h2) z]⟩⟩

theorem continuous_localPoint (c : ℂ) {R ε : ℝ} (hε : 0 < ε) (h2 : 2 * ε < R) :
    Continuous (localPoint c hε h2) :=
  Continuous.subtype_mk (continuous_const.prodMk ((continuous_projBall (sub_pos.2 h2)).comp continuous_id)) _

/-- The real density `ε^{γ²/2} e^{γ F(ε,z)}` of the dyadic approximant at scale `ε = 2^{-k}` (route step 4), read at
the projected point; `0` when `2ε ≥ R` (then no test function of a disc is seen). -/
noncomputable def approxDens (γ : ℝ) (c : ℂ) (R : ℝ) (F : C(LocalParam c R, ℝ)) (k : ℕ) (z : ℂ) : ℝ :=
  if h : 2 * dyadicScale k < R then
    dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * F (localPoint c (dyadicScale_pos k) h z))
  else 0

theorem continuous_approxDens_prod (γ : ℝ) (c : ℂ) (R : ℝ) (k : ℕ) :
    Continuous fun q : C(LocalParam c R, ℝ) × ℂ => approxDens γ c R q.1 k q.2 := by
  by_cases h : 2 * dyadicScale k < R
  · have hE : Continuous fun q : C(LocalParam c R, ℝ) × ℂ =>
        q.1 (localPoint c (dyadicScale_pos k) h q.2) :=
      continuous_eval.comp
        (continuous_fst.prodMk ((continuous_localPoint c (dyadicScale_pos k) h).comp continuous_snd))
    have hEq : (fun q : C(LocalParam c R, ℝ) × ℂ => approxDens γ c R q.1 k q.2) = fun q =>
        dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * q.1 (localPoint c (dyadicScale_pos k) h q.2)) := by
      funext q
      simp only [approxDens, h, ↓reduceDIte]
    rw [hEq]
    exact continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hE))
  · have hEq : (fun q : C(LocalParam c R, ℝ) × ℂ => approxDens γ c R q.1 k q.2) = fun _ => 0 := by
      funext q
      simp only [approxDens, h, ↓reduceDIte]
    rw [hEq]
    exact continuous_const

theorem approxDens_nonneg (γ : ℝ) (c : ℂ) (R : ℝ) (F : C(LocalParam c R, ℝ)) (k : ℕ) (z : ℂ) :
    0 ≤ approxDens γ c R F k z := by
  by_cases h : 2 * dyadicScale k < R
  · simp only [approxDens, h, ↓reduceDIte]
    exact mul_nonneg (Real.rpow_nonneg (dyadicScale_pos k).le _) (Real.exp_pos _).le
  · simp only [approxDens, h, ↓reduceDIte]
    exact le_refl 0

instance sFinite_ballVol (c : ℂ) (R : ℝ) : SFinite (ballVol c R) := by
  haveI := isLocallyFiniteMeasure_ballVol c R
  haveI : LocallyCompactSpace (ball c R) := isOpen_ball.locallyCompactSpace
  infer_instance

/-- The dyadic approximant `ε^{γ²/2} e^{γ F(ε,z)} dz` on the disc `X = ball c R` (the Lebesgue measure of `X`
weighted by `approxDens`). -/
noncomputable def approxX (γ : ℝ) (c : ℂ) (R : ℝ) (F : C(LocalParam c R, ℝ)) (k : ℕ) : Measure (ball c R) :=
  (ballVol c R).withDensity fun x => ENNReal.ofReal (approxDens γ c R F k x.1)

theorem continuous_approxDens_X (γ : ℝ) (c : ℂ) (R : ℝ) (F : C(LocalParam c R, ℝ)) (k : ℕ) :
    Continuous fun x : ball c R => approxDens γ c R F k x.1 :=
  (continuous_approxDens_prod γ c R k).comp (continuous_const.prodMk (continuous_subtype_val))

theorem integral_approxX (γ : ℝ) (c : ℂ) (R : ℝ) (F : C(LocalParam c R, ℝ)) (k : ℕ)
    (g : ball c R → ℝ) :
    ∫ x, g x ∂(approxX γ c R F k) = ∫ x, g x * approxDens γ c R F k x.1 ∂(ballVol c R) := by
  unfold approxX
  rw [integral_withDensity_eq_integral_toReal_smul
    (f := fun x : ball c R => ENNReal.ofReal (approxDens γ c R F k x.1))
    (continuous_approxDens_X γ c R F k).measurable.ennreal_ofReal
    (Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  congr 1
  funext x
  rw [smul_eq_mul, ENNReal.toReal_ofReal (approxDens_nonneg γ c R F k x.1), mul_comm]

theorem isLocallyFiniteMeasure_approxX (γ : ℝ) (c : ℂ) (R : ℝ) (F : C(LocalParam c R, ℝ)) (k : ℕ) :
    IsLocallyFiniteMeasure (approxX γ c R F k) := by
  haveI := isLocallyFiniteMeasure_ballVol c R
  unfold approxX
  exact IsLocallyFiniteMeasure.withDensity_ofReal (continuous_approxDens_X γ c R F k)

theorem measurable_integral_approxX (γ : ℝ) (c : ℂ) (R : ℝ) (k : ℕ) (g : C_c(ball c R, ℝ)) :
    Measurable fun F : C(LocalParam c R, ℝ) =>
      ∫ x, g x * approxDens γ c R F k x.1 ∂(ballVol c R) := by
  have hcont : Continuous fun q : C(LocalParam c R, ℝ) × ball c R =>
      g q.2 * approxDens γ c R q.1 k q.2.1 :=
    (g.continuous.comp continuous_snd).mul
      ((continuous_approxDens_prod γ c R k).comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
  have hSM : StronglyMeasurable (Function.uncurry fun (F : C(LocalParam c R, ℝ)) (x : ball c R) =>
      g x * approxDens γ c R F k x.1) := hcont.stronglyMeasurable
  exact (hSM.integral_prod_right (ν := ballVol c R)).measurable

/-- Extension by zero of a compactly supported continuous function on the disc `ball c R` to `ℂ` (route step 5). -/
theorem exists_extend_zero_ball {c : ℂ} {R : ℝ} (g : C_c(ball c R, ℝ)) :
    ∃ f : C_c(ℂ, ℝ), (∀ x : ball c R, f x.1 = g x) ∧ ∀ z, z ∉ Subtype.val '' tsupport g → f z = 0 := by
  classical
  let K : Set ℂ := Subtype.val '' tsupport g
  have hK : IsCompact K := (g.hasCompactSupport.isCompact).image continuous_subtype_val
  have hKball : K ⊆ ball c R := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  let f : ℂ → ℝ := fun z => if h : z ∈ ball c R then g ⟨z, h⟩ else 0
  have hfx : ∀ x : ball c R, f x.1 = g x := by
    intro x
    simp only [f, x.2, ↓reduceDIte, Subtype.coe_eta]
  have hzero : ∀ z, z ∉ K → f z = 0 := by
    intro z hz
    by_cases hzb : z ∈ ball c R
    · have hnot : (⟨z, hzb⟩ : ball c R) ∉ tsupport g := fun h => hz ⟨_, h, rfl⟩
      simp only [f, hzb, ↓reduceDIte]
      exact image_eq_zero_of_notMem_tsupport hnot
    · simp only [f, hzb, ↓reduceDIte]
  have hcontOn : ContinuousOn f (ball c R) := by
    rw [continuousOn_iff_continuous_restrict]
    have hres : (ball c R).domRestrict f = ⇑g := funext fun x => hfx x
    rw [hres]
    exact g.continuous
  have hcont : Continuous f := by
    refine continuous_iff_continuousAt.2 fun z0 => ?_
    by_cases hz0 : z0 ∈ ball c R
    · exact hcontOn.continuousAt (isOpen_ball.mem_nhds hz0)
    · have hz0K : z0 ∉ K := fun h => hz0 (hKball h)
      refine (continuousAt_const : ContinuousAt (fun _ : ℂ => (0 : ℝ)) z0).congr ?_
      exact Filter.eventually_of_mem (hK.isClosed.isOpen_compl.mem_nhds hz0K)
        fun z hz => (hzero z hz).symm
  exact ⟨⟨⟨f, hcont⟩, HasCompactSupport.intro hK fun z hz => hzero z hz⟩, hfx, hzero⟩

/-- Route step 7 on the closed disc: where `F` is the centred circle profile `fieldCircleAverage - P`, the
approximant density is `e^{γP}` times the Lebesgue density of `lqgApprox` at scale `2^{-k}`. -/
theorem approxDens_mul_exp (γ α P : ℝ) {c : ℂ} {R : ℝ} (hc : ℝ → ℂ → ℝ) (F : C(LocalParam c R, ℝ))
    (hF : ∀ p : LocalParam c R, F p = fieldCircleAverage α hc p.1.1 p.1.2 - P) (k : ℕ)
    (h2 : 2 * dyadicScale k < R) {z : ℂ} (hz : dist z c ≤ R - 2 * dyadicScale k) :
    dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * fieldCircleAverage α hc (dyadicScale k) z) =
      Real.exp (γ * P) * approxDens γ c R F k z := by
  have hε : 0 < dyadicScale k := dyadicScale_pos k
  have hp : projBall c (R - 2 * dyadicScale k) z = z := projBall_of_dist_le (sub_pos.2 h2) hz
  have hFz : F (localPoint c hε h2 z) = fieldCircleAverage α hc (dyadicScale k) z - P := by
    rw [hF]
    show fieldCircleAverage α hc (dyadicScale k) (projBall c (R - 2 * dyadicScale k) z) - P = _
    rw [hp]
  simp only [approxDens, h2, ↓reduceDIte]
  rw [hFz]
  have hexp : Real.exp (γ * fieldCircleAverage α hc (dyadicScale k) z) =
      Real.exp (γ * P) * Real.exp (γ * (fieldCircleAverage α hc (dyadicScale k) z - P)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  ring

/-- Locally finite pull-back of a locally finite measure to the disc (general version of
`isLocallyFiniteMeasure_ballVol`). -/
theorem isLocallyFiniteMeasure_comap_ball (μ : Measure ℂ) [IsLocallyFiniteMeasure μ] (c : ℂ) (R : ℝ) :
    IsLocallyFiniteMeasure (Measure.comap (Subtype.val : ball c R → ℂ) μ) := by
  refine ⟨fun x => ?_⟩
  have hx : dist (x : ℂ) c < R := mem_ball.1 x.2
  have hρ : 0 < (R - dist (x : ℂ) c) / 2 := by linarith
  refine ⟨Subtype.val ⁻¹' ball (x : ℂ) ((R - dist (x : ℂ) c) / 2), ?_, ?_⟩
  · exact (isOpen_ball.preimage continuous_subtype_val).mem_nhds (mem_ball_self hρ)
  · rw [(MeasurableEmbedding.subtype_coe measurableSet_ball).comap_apply]
    exact (measure_mono (image_preimage_subset _ _)).trans_lt measure_ball_lt_top

/-- Route step 7 (identity with `lqgApprox`): for `f` continuous and supported in the disc, `∫ f d(lqgApprox)` is
`e^{γP}` times `∫ f · approxDens`, where `F` is the centred circle profile (`hF`). -/
theorem integral_lqgApprox_eq_approx (γ α P : ℝ) {c : ℂ} {R : ℝ} (hc : ℝ → ℂ → ℝ)
    (hcont : ∀ ε : ℝ, 0 < ε → Continuous (hc ε)) (F : C(LocalParam c R, ℝ))
    (hF : ∀ p : LocalParam c R, F p = fieldCircleAverage α hc p.1.1 p.1.2 - P) (k : ℕ)
    (h2 : 2 * dyadicScale k < R) {f : ℂ → ℝ} (hsupp : ∀ z, f z ≠ 0 → dist z c ≤ R - 2 * dyadicScale k) :
    ∫ z, f z ∂(lqgApprox γ (fieldCircleAverage α hc) (dyadicScale k)) =
      Real.exp (γ * P) * ∫ z, f z * approxDens γ c R F k z := by
  have hε : 0 < dyadicScale k := dyadicScale_pos k
  have hfca : Continuous fun z => fieldCircleAverage α hc (dyadicScale k) z := by
    have h1 : Continuous fun z => hc (dyadicScale k) z := hcont _ hε
    have h3 : Continuous fun z : ℂ => Real.log (max (dyadicScale k) ‖z‖) :=
      (continuous_const.max continuous_norm).log fun z => (lt_max_of_lt_left hε).ne'
    have hEq : (fun z => fieldCircleAverage α hc (dyadicScale k) z) =
        fun z => hc (dyadicScale k) z - α * Real.log (max (dyadicScale k) ‖z‖) := by
      funext z
      unfold fieldCircleAverage
      rw [circleAverage_log_norm_eq_max hε z]
    rw [hEq]
    exact h1.sub (continuous_const.mul h3)
  have hD : Continuous fun z => dyadicScale k ^ (γ ^ 2 / 2) *
      Real.exp (γ * fieldCircleAverage α hc (dyadicScale k) z) :=
    continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hfca))
  unfold lqgApprox
  rw [integral_withDensity_eq_integral_toReal_smul
    (f := fun z => ENNReal.ofReal (dyadicScale k ^ (γ ^ 2 / 2) *
      Real.exp (γ * fieldCircleAverage α hc (dyadicScale k) z)))
    hD.measurable.ennreal_ofReal (Eventually.of_forall fun z => ENNReal.ofReal_lt_top)]
  rw [← integral_const_mul]
  congr 1
  funext z
  by_cases hfz : f z = 0
  · simp [hfz]
  · have hz := hsupp z hfz
    have hnn : 0 ≤ dyadicScale k ^ (γ ^ 2 / 2) *
        Real.exp (γ * fieldCircleAverage α hc (dyadicScale k) z) :=
      mul_nonneg (Real.rpow_nonneg hε.le _) (Real.exp_pos _).le
    rw [smul_eq_mul, ENNReal.toReal_ofReal hnn, approxDens_mul_exp γ α P hc F hF k h2 hz]
    ring

/-- The integral over the disc of the approximant density reduces to the integral over `ℂ` (the support of `f`
lies in the disc). -/
theorem integral_approxX_eq_ball (γ : ℝ) (c : ℂ) (R : ℝ) (F : C(LocalParam c R, ℝ)) (k : ℕ) {f : ℂ → ℝ}
    (hsupp : ∀ z, f z ≠ 0 → dist z c < R) :
    ∫ x : ball c R, f x.1 * approxDens γ c R F k x.1 ∂(ballVol c R) =
      ∫ z, f z * approxDens γ c R F k z := by
  unfold ballVol
  refine (integral_subtype_comap measurableSet_ball (fun z => f z * approxDens γ c R F k z)).trans
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => ?_)
  by_cases hfz : f z = 0
  · simp [hfz]
  · exact absurd (mem_ball.2 (hsupp z hfz)) hz

/-- A compact subset of the disc lies in a closed disc of radius `s < R`. -/
theorem exists_radius_of_compact {c : ℂ} {R : ℝ} (hR : 0 < R) {K : Set ℂ} (hK : IsCompact K)
    (hKb : K ⊆ ball c R) : ∃ s : ℝ, 0 ≤ s ∧ s < R ∧ ∀ z ∈ K, dist z c ≤ s := by
  rcases K.eq_empty_or_nonempty with hE | hne
  · exact ⟨R / 2, by linarith, by linarith, fun z hz => by simp [hE] at hz⟩
  · obtain ⟨z0, hz0, hmax⟩ := hK.exists_isMaxOn hne (continuous_id.dist continuous_const).continuousOn
    exact ⟨dist z0 c, dist_nonneg, mem_ball.1 (hKb hz0), fun z hz => isMaxOn_iff.1 hmax z hz⟩

/-- The dyadic scales eventually satisfy `2 · 2^{-k} < t`. -/
theorem eventually_two_dyadicScale_lt {t : ℝ} (ht : 0 < t) :
    ∀ᶠ k : ℕ in atTop, 2 * dyadicScale k < t := by
  have h : Tendsto (fun k : ℕ => dyadicScale k) atTop (𝓝 0) := by
    unfold dyadicScale
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have h2 : Tendsto (fun k : ℕ => 2 * dyadicScale k) atTop (𝓝 0) := by
    simpa using h.const_mul 2
  exact h2.eventually (gt_mem_nhds ht)

/-- Route step 7 (Riesz limit on the disc): if the centred profile `F` is `fieldCircleAverage - P` and `μ` is the
γ-LQG measure of `hc` (`IsLQGLimit`), the approximants integrate every `g ∈ C_c(ball c R)` to
`∫ g d(comap val (e^{-γP} • μ))`. -/
theorem tendsto_approxX_integral (γ α P : ℝ) {c : ℂ} {R : ℝ} (hR : 0 < R) (hc : ℝ → ℂ → ℝ)
    (hcont : ∀ ε : ℝ, 0 < ε → Continuous (hc ε)) (μ : Measure ℂ)
    (hμ : IsLQGLimit γ (fieldCircleAverage α hc) μ)
    (F : C(LocalParam c R, ℝ))
    (hF : ∀ p : LocalParam c R, F p = fieldCircleAverage α hc p.1.1 p.1.2 - P)
    (g : C_c(ball c R, ℝ)) :
    Tendsto (fun k => ∫ x, g x ∂(approxX γ c R F k)) atTop
      (𝓝 (∫ x, g x ∂(Measure.comap (Subtype.val : ball c R → ℂ)
        (ENNReal.ofReal (Real.exp (-(γ * P))) • μ)))) := by
  obtain ⟨fc, hfg, hfz⟩ := exists_extend_zero_ball g
  have hcompact : IsCompact (Subtype.val '' tsupport g) :=
    (g.hasCompactSupport.isCompact).image continuous_subtype_val
  have hKb : Subtype.val '' tsupport g ⊆ ball c R := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  obtain ⟨s, hs0, hsR, hsK⟩ := exists_radius_of_compact hR hcompact hKb
  have hfsupp : ∀ z, fc z ≠ 0 → dist z c ≤ s := fun z hz =>
    hsK z (by
      by_contra hK
      exact hz (hfz z hK))
  have hev : ∀ᶠ k : ℕ in atTop, 2 * dyadicScale k < R - s :=
    eventually_two_dyadicScale_lt (by linarith)
  have hgf : ∀ x : ball c R, g x = fc x.1 := fun x => (hfg x).symm
  have hL : ∫ x, g x ∂(Measure.comap (Subtype.val : ball c R → ℂ)
      (ENNReal.ofReal (Real.exp (-(γ * P))) • μ)) = Real.exp (-(γ * P)) * ∫ z, fc z ∂μ := by
    simp only [hgf]
    rw [integral_subtype_comap measurableSet_ball (fun z => fc z)]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
      by_contra hne
      exact hz (mem_ball.2 (lt_of_le_of_lt (hfsupp z hne) hsR)))]
    rw [integral_smul_measure, smul_eq_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le]
  have hexp : Real.exp (-(γ * P)) * Real.exp (γ * P) = 1 := by
    rw [← Real.exp_add]
    simp
  have heq : (fun k => ∫ x, g x ∂(approxX γ c R F k)) =ᶠ[atTop] fun k =>
      Real.exp (-(γ * P)) * ∫ z, fc z ∂(lqgApprox γ (fieldCircleAverage α hc) (dyadicScale k)) := by
    filter_upwards [hev] with k hk
    have hk2 : 2 * dyadicScale k < R := by linarith
    have hsupp1 : ∀ z, fc z ≠ 0 → dist z c ≤ R - 2 * dyadicScale k := fun z hz => by
      linarith [hfsupp z hz]
    have hsupp2 : ∀ z, fc z ≠ 0 → dist z c < R := fun z hz => by
      linarith [hfsupp z hz]
    rw [integral_lqgApprox_eq_approx γ α P hc hcont F hF k hk2 hsupp1, ← mul_assoc, hexp, one_mul]
    rw [integral_approxX γ c R F k (fun x => g x)]
    have hcongr : (fun x : ball c R => g x * approxDens γ c R F k x.1) =
        fun x : ball c R => fc x.1 * approxDens γ c R F k x.1 := by
      funext x
      rw [hgf x]
    rw [hcongr, integral_approxX_eq_ball γ c R F k hsupp2]
  have hT := (hμ.tendsto_integral (⇑fc) fc.continuous fc.hasCompactSupport).const_mul (Real.exp (-(γ * P)))
  rw [hL]
  exact Tendsto.congr' heq.symm hT

/-- Locally finite scalar multiples of a locally finite measure (`ENNReal.ofReal r • μ`). -/
instance isLocallyFiniteMeasure_ofReal_smul (μ : Measure ℂ) [IsLocallyFiniteMeasure μ] (r : ℝ) :
    IsLocallyFiniteMeasure (ENNReal.ofReal r • μ) := by
  refine ⟨fun x => ?_⟩
  obtain ⟨U, hU, hμU⟩ := IsLocallyFiniteMeasure.finiteAtNhds (μ := μ) x
  exact ⟨U, hU, by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hμU⟩

/-- A compact exhaustion of the disc `ball c R` (for the vague decoder). -/
theorem ball_exhaustion (c : ℂ) (R : ℝ) :
    ∃ K : ℕ → Set (ball c R), (∀ n, IsCompact (K n)) ∧
      (∀ s : Set (ball c R), IsCompact s → ∃ n, s ⊆ K n) := by
  haveI : LocallyCompactSpace (ball c R) := isOpen_ball.locallyCompactSpace
  let E : CompactExhaustion (ball c R) := CompactExhaustion.choice (ball c R)
  exact ⟨fun n => E n, fun n => E.isCompact n, fun s hs => E.exists_superset_of_isCompact hs⟩

/-- The decoded disc measure: the vague decoder `decoderX` of the dyadic approximants built from the decoded centred
profile `decodeF y` (route step 7). -/
noncomputable def discDecoder {Y : Type*} [MeasurableSpace Y] {c : ℂ} {R γ : ℝ} {K : ℕ → Set (ball c R)}
    (hKs : ∀ s : Set (ball c R), IsCompact s → ∃ n, s ⊆ K n) (T : TestFamilyX K)
    (decodeF : Y → C(LocalParam c R, ℝ)) : Y → Measure (ball c R) :=
  decoderX hKs T (fun y k => approxX γ c R (decodeF y) k)
    (fun y k => isLocallyFiniteMeasure_approxX γ c R (decodeF y) k)

/-- Route step 7 (identity of the decoded measure): if the decoded centred profile of `y` is `fieldCircleAverage - P`
and `μ` is the γ-LQG measure of `hc`, the decoded disc measure is `comap val (e^{-γP} • μ)`. -/
theorem discDecoder_eq_comap {Y : Type*} [MeasurableSpace Y] (γ α P : ℝ) {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hc : ℝ → ℂ → ℝ) (hcont : ∀ ε : ℝ, 0 < ε → Continuous (hc ε)) (μ : Measure ℂ)
    (hμ : IsLQGLimit γ (fieldCircleAverage α hc) μ)
    {K : ℕ → Set (ball c R)} (hKs : ∀ s : Set (ball c R), IsCompact s → ∃ n, s ⊆ K n) (T : TestFamilyX K)
    (decodeF : Y → C(LocalParam c R, ℝ)) (y : Y)
    (hF : ∀ p : LocalParam c R, decodeF y p = fieldCircleAverage α hc p.1.1 p.1.2 - P) :
    discDecoder (γ := γ) hKs T decodeF y =
      Measure.comap (Subtype.val : ball c R → ℂ) (ENNReal.ofReal (Real.exp (-(γ * P))) • μ) := by
  haveI : IsLocallyFiniteMeasure μ := hμ.isLocallyFiniteMeasure
  haveI : LocallyCompactSpace (ball c R) := isOpen_ball.locallyCompactSpace
  haveI : (discDecoder (γ := γ) hKs T decodeF y).Regular := by
    unfold discDecoder decoderX
    infer_instance
  haveI : IsLocallyFiniteMeasure (ENNReal.ofReal (Real.exp (-(γ * P))) • μ) := inferInstance
  haveI := isLocallyFiniteMeasure_comap_ball (ENNReal.ofReal (Real.exp (-(γ * P))) • μ) c R
  haveI : (Measure.comap (Subtype.val : ball c R → ℂ)
      (ENNReal.ofReal (Real.exp (-(γ * P))) • μ)).Regular := inferInstance
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro g
  have hconv : y ∈ convSetX T (fun y k => approxX γ c R (decodeF y) k) := fun m =>
    ⟨_, tendsto_approxX_integral γ α P hR hc hcont μ hμ (decodeF y) hF (T.D m)⟩
  unfold discDecoder
  rw [integral_decoderX hKs T _ _ y g, decoderFunctionalX_of_mem hKs T _ _ hconv g]
  exact (tendsto_approxX_integral γ α P hR hc hcont μ hμ (decodeF y) hF g).limUnder_eq

/-- Route step 7 (the kernel): `κ(y) = (1 + m_y(D))⁻¹ • map val m_y` for the decoded disc measure `m_y`; it is a
finite measure (`≤ 1` in mass), so the kernel is s-finite. -/
noncomputable def kernelMeas {Y : Type*} [MeasurableSpace Y] {c : ℂ} {R γ : ℝ} {K : ℕ → Set (ball c R)}
    (hKs : ∀ s : Set (ball c R), IsCompact s → ∃ n, s ⊆ K n) (T : TestFamilyX K)
    (decodeF : Y → C(LocalParam c R, ℝ)) (y : Y) : Measure ℂ :=
  (1 + discDecoder (γ := γ) hKs T decodeF y univ)⁻¹ •
    Measure.map (Subtype.val : ball c R → ℂ) (discDecoder (γ := γ) hKs T decodeF y)

theorem measurable_kernelMeas {Y : Type*} [MeasurableSpace Y] (γ : ℝ) {c : ℂ} {R : ℝ}
    {K : ℕ → Set (ball c R)} (hKs : ∀ s : Set (ball c R), IsCompact s → ∃ n, s ⊆ K n) (T : TestFamilyX K)
    (decodeF : Y → C(LocalParam c R, ℝ)) (hdec : Measurable decodeF) :
    Measurable (kernelMeas (γ := γ) hKs T decodeF) := by
  have hm : Measurable (discDecoder (γ := γ) hKs T decodeF) := by
    unfold discDecoder
    refine measurable_decoderX hKs T _ _ (fun g k => ?_)
    have hfun : (fun y => ∫ x, g x ∂(approxX γ c R (decodeF y) k)) =
        fun y => ∫ x, g x * approxDens γ c R (decodeF y) k x.1 ∂(ballVol c R) := by
      funext y
      exact integral_approxX γ c R (decodeF y) k g
    rw [hfun]
    exact (measurable_integral_approxX γ c R k g).comp hdec
  refine Measure.measurable_of_measurable_coe _ fun S hS => ?_
  have hfun : (fun y => kernelMeas (γ := γ) hKs T decodeF y S) = fun y =>
      (1 + discDecoder (γ := γ) hKs T decodeF y univ)⁻¹ *
        discDecoder (γ := γ) hKs T decodeF y (Subtype.val ⁻¹' S) := by
    funext y
    rw [kernelMeas, Measure.smul_apply, Measure.map_apply measurable_subtype_coe hS, smul_eq_mul]
  rw [hfun]
  exact ((measurable_const.add ((Measure.measurable_coe MeasurableSet.univ).comp hm)).inv).mul
    ((Measure.measurable_coe (measurable_subtype_coe hS)).comp hm)

/-- Route step 7 (clause A of the kernel, for one observation): on the disc, the kernel of the decoded observation is
a positive multiple of the restricted γ-LQG measure. -/
theorem kernelMeas_restrict_eq (γ α P : ℝ) {c : ℂ} {R : ℝ} (hR : 0 < R) (hc : ℝ → ℂ → ℝ)
    (hcont : ∀ ε : ℝ, 0 < ε → Continuous (hc ε)) (μ : Measure ℂ)
    (hμ : IsLQGLimit γ (fieldCircleAverage α hc) μ)
    {K : ℕ → Set (ball c R)} (hKs : ∀ s : Set (ball c R), IsCompact s → ∃ n, s ⊆ K n) (T : TestFamilyX K)
    {Y : Type*} [MeasurableSpace Y] (decodeF : Y → C(LocalParam c R, ℝ)) (y : Y)
    (hF : ∀ p : LocalParam c R, decodeF y p = fieldCircleAverage α hc p.1.1 p.1.2 - P) :
    ∃ a : ℝ, 0 < a ∧ (kernelMeas (γ := γ) hKs T decodeF y).restrict (ball c R) =
      ENNReal.ofReal a • μ.restrict (ball c R) := by
  have : IsLocallyFiniteMeasure μ := hμ.isLocallyFiniteMeasure
  obtain ⟨ν, hν⟩ : ∃ ν : Measure ℂ, ν = ENNReal.ofReal (Real.exp (-(γ * P))) • μ := ⟨_, rfl⟩
  have hs : 0 < Real.exp (-(γ * P)) := Real.exp_pos _
  have hres : ν.restrict (ball c R) = ENNReal.ofReal (Real.exp (-(γ * P))) • μ.restrict (ball c R) := by
    rw [hν, Measure.restrict_smul]
  have hMfin : ν (ball c R) ≠ ⊤ := by
    rw [hν, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ball_lt_top).ne
  have h1M : (1 + ν (ball c R)) ≠ 0 := fun h => one_ne_zero (add_eq_zero.1 h).1
  have hK0 : (1 + ν (ball c R))⁻¹ * ENNReal.ofReal (Real.exp (-(γ * P))) ≠ 0 :=
    mul_ne_zero (ENNReal.inv_ne_zero.2 (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, hMfin⟩))
      (ENNReal.ofReal_pos.2 hs).ne'
  have hKtop : (1 + ν (ball c R))⁻¹ * ENNReal.ofReal (Real.exp (-(γ * P))) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 h1M) ENNReal.ofReal_ne_top
  refine ⟨((1 + ν (ball c R))⁻¹ * ENNReal.ofReal (Real.exp (-(γ * P)))).toReal,
    ENNReal.toReal_pos hK0 hKtop, ?_⟩
  have hdisc := discDecoder_eq_comap γ α P hR hc hcont μ hμ hKs T decodeF y hF
  unfold kernelMeas
  rw [hdisc, ← hν]
  have hM : Measure.comap (Subtype.val : ball c R → ℂ) ν univ = ν (ball c R) := by
    rw [(MeasurableEmbedding.subtype_coe measurableSet_ball).comap_apply, image_univ, Subtype.range_coe]
  rw [hM, map_comap_subtype_coe measurableSet_ball ν, Measure.restrict_smul,
    Measure.restrict_restrict measurableSet_ball, Set.inter_self, hres, smul_smul,
    ENNReal.ofReal_toReal hKtop]

/-- Route step 7, clause A (unrooted), almost surely: for a whole-plane GFF `h^ℂ` and a γ-LQG measure `μ` of
`h^ℂ - α log|·|` (`IsLQGMeasureOfField`), the kernel `kernelMeas` of the local mean-zero observation is a positive
multiple of `μ` restricted to the disc. -/
theorem clauseA_unrooted (γ α : ℝ) {c : ℂ} {R : ℝ} (hR : 0 < R) (h0 : (0 : ℂ) ∉ ball c R)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (μ : Ω → Measure ℂ) (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (d : ℕ → LocalParam c R) (decode : (ℕ → ℝ) → C(LocalParam c R, ℝ))
    {K : ℕ → Set (ball c R)} (hKs : ∀ s : Set (ball c R), IsCompact s → ∃ n, s ⊆ K n) (T : TestFamilyX K)
    (hdec : ∀ f : C(LocalParam c R, ℝ), decode (fun n => f (d n)) = f) :
    ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧
      (kernelMeas (γ := γ) hKs T (fun y => decode (fun n => localCoord c hR (d n) y))
        (localMeanZeroObs α (ball c R) (hC ω))).restrict (ball c R) =
        ENNReal.ofReal a • (μ ω).restrict (ball c R) := by
  have hμ' : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) (μ ω) := hμ
  filter_upwards [ae_decode_localCoord_eq hGFF α c hR h0 d decode hdec, hGFF.ae_continuousOn_circle, hμ']
    with ω hdecω hcontω hμω
  obtain ⟨G, hG, hGeq⟩ := hdecω
  have hcont' : ∀ ε : ℝ, 0 < ε → Continuous (hcirc ω ε) := fun ε hε =>
    hcontω.comp_continuous (continuous_const.prodMk continuous_id) fun z => ⟨hε, Set.mem_univ z⟩
  have hF : ∀ p : LocalParam c R,
      (fun y => decode (fun n => localCoord c hR (d n) y)) (localMeanZeroObs α (ball c R) (hC ω)) p =
        fieldCircleAverage α (hcirc ω) p.1.1 p.1.2 - fieldPairing α (hC ω) (bumpRho c hR) := by
    intro p
    show decode (fun n => localCoord c hR (d n) (localMeanZeroObs α (ball c R) (hC ω))) p = _
    rw [hGeq, hG p]
    unfold fieldCircleAverage
    rw [circleAverage_log_norm_eq_max (localParam_radius_pos p) p.1.2]
  exact kernelMeas_restrict_eq γ α (fieldPairing α (hC ω) (bumpRho c hR)) hR (hcirc ω) hcont' (μ ω) hμω hKs T
    (fun y => decode (fun n => localCoord c hR (d n) y)) (localMeanZeroObs α (ball c R) (hC ω)) hF

/-! ### Rooted shift (route step 8): the field `h + f_z`, `f_z(w) = -γ log|w-z| + γ log max(1,|w|)` -/

/-- The rooted shift `f_z(w) = -γ log|w - z| + γ log max(1,|w|)` (`campbellReferenceObs`). -/
noncomputable def rootShift (γ : ℝ) (z w : ℂ) : ℝ :=
  -γ * Real.log ‖w - z‖ + γ * Real.log (max 1 ‖w‖)

/-- The reference observation of `campbellReferenceObs` is the pairing of `h + f_z` (algebra; no integrability). -/
theorem campbellReferenceObs_eq (γ α₀ : ℝ) (φ : ℂ → ℝ) (hC : (ℂ → ℝ) → ℝ) (z : ℂ) :
    fieldPairing α₀ hC φ - γ * ∫ w, (Real.log ‖w - z‖ - Real.log (max 1 ‖w‖)) * φ w =
      fieldPairing α₀ hC φ + ∫ w, rootShift γ z w * φ w := by
  have h : ∫ w, rootShift γ z w * φ w = -γ * ∫ w, (Real.log ‖w - z‖ - Real.log (max 1 ‖w‖)) * φ w := by
    rw [← integral_const_mul]
    congr 1
    funext w
    simp only [rootShift]
    ring
  rw [h]
  ring

/-- The circle average of the rooted shift (linearity of `circleAverage` on the two summands). -/
theorem circleAverage_rootShift (γ : ℝ) {r : ℝ} (hr : 0 < r) (z x : ℂ) :
    Real.circleAverage (rootShift γ z) x r =
      -γ * Real.log (max r ‖x - z‖) + γ * Real.circleAverage (fun w => Real.log (max 1 ‖w‖)) x r := by
  have hL : CircleIntegrable (fun w => Real.log ‖w - z‖) x r := circleIntegrable_log_norm_sub_const r
  have hM : CircleIntegrable (fun w => Real.log (max 1 ‖w‖)) x r :=
    (((continuous_const.max continuous_norm).log fun w => (lt_max_of_lt_left one_pos).ne').continuousOn.circleIntegrable hr.le)
  have e1 : rootShift γ z = (fun w => -γ * Real.log ‖w - z‖) + (fun w => γ * Real.log (max 1 ‖w‖)) := rfl
  have hL1 : CircleIntegrable (fun w => -γ * Real.log ‖w - z‖) x r := IntervalIntegrable.const_mul hL (-γ)
  have hM1 : CircleIntegrable (fun w => γ * Real.log (max 1 ‖w‖)) x r := IntervalIntegrable.const_mul hM γ
  rw [e1, Real.circleAverage_add hL1 hM1]
  have e2 : Real.circleAverage (fun w => -γ * Real.log ‖w - z‖) x r =
      -γ * Real.circleAverage (fun w => Real.log ‖w - z‖) x r := by
    have h := Real.circleAverage_smul (a := -γ) (f := fun w => Real.log ‖w - z‖) (c := x) (R := r)
    have hfun : ((-γ) • fun w : ℂ => Real.log ‖w - z‖) = fun w : ℂ => -γ * Real.log ‖w - z‖ := by
      funext w
      rfl
    rw [hfun, smul_eq_mul] at h
    exact h
  have e3 : Real.circleAverage (fun w => γ * Real.log (max 1 ‖w‖)) x r =
      γ * Real.circleAverage (fun w => Real.log (max 1 ‖w‖)) x r := by
    have h := Real.circleAverage_smul (a := γ) (f := fun w => Real.log (max 1 ‖w‖)) (c := x) (R := r)
    have hfun : (γ • fun w : ℂ => Real.log (max 1 ‖w‖)) = fun w : ℂ => γ * Real.log (max 1 ‖w‖) := by
      funext w
      rfl
    rw [hfun, smul_eq_mul] at h
    exact h
  rw [e2, e3, circleAverage_log_norm_sub_eq x z hr]

/-- The logarithm of the local modulus `log max(1,|w|)` is continuous. -/
theorem continuous_log_max_one : Continuous fun w : ℂ => Real.log (max 1 ‖w‖) :=
  (continuous_const.max continuous_norm).log fun w => (lt_max_of_lt_left one_pos).ne'

/-- Route step 8 (deterministic limit): the annular averages `∫ ψ_{j+N} f_z` of the rooted shift converge to the circle
average of `f_z` (the log singularity at `z` is handled by `tendsto_unitCircleDensity_mul_log`, the continuous part by
`tendsto_unitCircleDensity_mul_continuous`). -/
theorem tendsto_circleApprox_rootShift (γ : ℝ) {r : ℝ} (hr : 0 < r) (x z : ℂ) (N : ℕ) :
    Tendsto (fun j : ℕ => ∫ y, circleApprox hr x (j + N) y * rootShift γ z y) atTop
      (𝓝 (Real.circleAverage (rootShift γ z) x r)) := by
  have hδ : ∀ j : ℕ, 0 < r * approxEta r (j + N) := fun j => mul_pos hr (approxEta_pos hr _)
  have hsmall : ∀ η : ℝ, 0 < η → ∃ M : ℕ, ∀ j, M ≤ j → r * approxEta r (j + N) ≤ r * η := by
    intro η hη
    obtain ⟨M, hM⟩ := eventually_approxEta_lt (r := r) hη
    exact ⟨M, fun j hj => mul_le_mul_of_nonneg_left (le_of_lt (hM (j + N) (by omega))) hr.le⟩
  have hL := tendsto_unitCircleDensity_mul_log (r := r) (δ := fun j => r * approxEta r (j + N))
    hr hδ hsmall x z
  have hM := tendsto_unitCircleDensity_mul_continuous (r := r) (δ := fun j => r * approxEta r (j + N))
    hr hδ hsmall x continuous_log_max_one
  have hLim := (hL.const_mul (-γ)).add (hM.const_mul γ)
  have hcirc : Real.circleAverage (rootShift γ z) x r =
      -γ * Real.log (max r ‖x - z‖) + γ * Real.circleAverage (fun w => Real.log (max 1 ‖w‖)) x r :=
    circleAverage_rootShift γ hr z x
  rw [hcirc]
  refine hLim.congr fun j => ?_
  have i1 : Integrable (fun y => unitCircleDensity r (r * approxEta r (j + N)) (hδ j) x y *
      Real.log ‖y - z‖) :=
    integrable_unitCircleDensity_mul_log hr.le (hδ j) x z
  have i2 : Integrable (fun y => unitCircleDensity r (r * approxEta r (j + N)) (hδ j) x y *
      Real.log (max 1 ‖y‖)) :=
    integrable_unitCircleDensity_mul hr.le (hδ j) x continuous_log_max_one
  have e1 : ∫ y, circleApprox hr x (j + N) y * rootShift γ z y =
      ∫ y, (-γ * (unitCircleDensity r (r * approxEta r (j + N)) (hδ j) x y * Real.log ‖y - z‖) +
        γ * (unitCircleDensity r (r * approxEta r (j + N)) (hδ j) x y * Real.log (max 1 ‖y‖))) := by
    congr 1
    funext y
    simp only [rootShift, circleApprox]
    ring
  have e2 : ∫ y, (-γ * (unitCircleDensity r (r * approxEta r (j + N)) (hδ j) x y * Real.log ‖y - z‖) +
        γ * (unitCircleDensity r (r * approxEta r (j + N)) (hδ j) x y * Real.log (max 1 ‖y‖))) =
      -γ * (∫ y, unitCircleDensity r (r * approxEta r (j + N)) (hδ j) x y * Real.log ‖y - z‖) +
        γ * (∫ y, unitCircleDensity r (r * approxEta r (j + N)) (hδ j) x y * Real.log (max 1 ‖y‖)) := by
    rw [integral_add (i1.const_mul (-γ)) (i2.const_mul γ), integral_const_mul, integral_const_mul]
  exact (e1.trans e2).symm

/-- The observation of the rooted field `h + f_z` on the mean-zero tests of `D` (route step 8; the second component of
`campbellReferenceObs`, by `campbellReferenceObs_snd_eq_rootedObs`). -/
noncomputable def rootedObs (γ α : ℝ) (D : Set ℂ) (hC : (ℂ → ℝ) → ℝ) (z : ℂ) :
    {φ : ℂ → ℝ // IsTestFunction D φ ∧ ∫ x, φ x = 0} → ℝ :=
  fun φ => fieldPairing α hC φ.1 + ∫ w, rootShift γ z w * φ.1 w

theorem campbellReferenceObs_snd_eq_rootedObs (γ α : ℝ) (D : Set ℂ) (hC : (ℂ → ℝ) → ℝ) (z : ℂ) :
    (campbellReferenceObs γ α D hC z).2 = rootedObs γ α D hC z :=
  funext fun φ => campbellReferenceObs_eq γ α φ.1 hC z

/-- `bumpRho · log|· - z|` is integrable (the logarithmic singularity at `z` is locally integrable). -/
theorem integrable_bump_mul_log_sub (c : ℂ) {R : ℝ} (hR : 0 < R) (z : ℂ) :
    Integrable fun w => bumpRho c hR w * Real.log ‖w - z‖ := by
  have hcs : HasCompactSupport fun t : ℂ => bumpRho c hR (t + z) :=
    (bumpRho_isTest c hR).2.1.comp_homeomorph (Homeomorph.addRight z)
  have hl : LocallyIntegrable (fun t : ℂ => bumpRho c hR (t + z) * Real.log ‖t‖) volume :=
    (locallyIntegrable_log_norm_complex).continuous_mul
      ((bumpRho_isTest c hR).1.continuous.comp (continuous_id.add continuous_const))
  have hcs2 : HasCompactSupport (fun t : ℂ => bumpRho c hR (t + z) * Real.log ‖t‖) := hcs.mul_right
  have hg : Integrable (fun t : ℂ => bumpRho c hR (t + z) * Real.log ‖t‖) volume :=
    (integrableOn_iff_integrable_of_support_subset (subset_tsupport _)).1
      (hl.integrableOn_isCompact hcs2.isCompact)
  have h2 := hg.comp_sub_right z
  simp only [sub_add_cancel] at h2
  exact h2

theorem integrable_rootShift_mul_bump (γ : ℝ) (c : ℂ) {R : ℝ} (hR : 0 < R) (z : ℂ) :
    Integrable fun w => rootShift γ z w * bumpRho c hR w := by
  have h1 := (integrable_bump_mul_log_sub c hR z).const_mul (-γ)
  have hc2 : Continuous fun w => bumpRho c hR w * Real.log (max 1 ‖w‖) :=
    (bumpRho_isTest c hR).1.continuous.mul continuous_log_max_one
  have h2 : Integrable fun w => bumpRho c hR w * Real.log (max 1 ‖w‖) :=
    hc2.integrable_of_hasCompactSupport (bumpRho_isTest c hR).2.1.mul_right
  refine (h1.add (h2.const_mul γ)).congr (Filter.Eventually.of_forall fun w => ?_)
  simp only [Pi.add_apply, rootShift]
  ring

theorem integrable_circleApprox_mul_rootShift {r : ℝ} (hr : 0 < r) (γ : ℝ) (x z : ℂ) (j : ℕ) :
    Integrable fun y => circleApprox hr x j y * rootShift γ z y := by
  have hδ : 0 < r * approxEta r j := mul_pos hr (approxEta_pos hr j)
  have i1 : Integrable fun y => unitCircleDensity r (r * approxEta r j) hδ x y * Real.log ‖y - z‖ :=
    integrable_unitCircleDensity_mul_log hr.le hδ x z
  have i2 : Integrable fun y => unitCircleDensity r (r * approxEta r j) hδ x y * Real.log (max 1 ‖y‖) :=
    integrable_unitCircleDensity_mul hr.le hδ x continuous_log_max_one
  refine ((i1.const_mul (-γ)).add (i2.const_mul γ)).congr (Filter.Eventually.of_forall fun y => ?_)
  simp only [Pi.add_apply, rootShift, circleApprox]
  ring

/-- Route step 8 (a.s.): the coordinates of the rooted observation converge to the centred rooted circle profile
`h_r(x) - α log max(r,|x|) + (circle average of f_z) - (pairing of h and f_z with ρ)`. -/
theorem ae_tendsto_localRooted {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (γ α : ℝ) (c : ℂ) {R : ℝ} (hR : 0 < R) (h0 : (0 : ℂ) ∉ ball c R) (z : ℂ) (p : LocalParam c R) :
    ∀ᵐ ω ∂P, Tendsto (fun j => obsAt (rootedObs γ α (ball c R) (hC ω) z) (localTest c hR p j)) atTop
      (𝓝 (hcirc ω p.1.1 p.1.2 - α * Real.log (max p.1.1 ‖p.1.2‖) - fieldPairing α (hC ω) (bumpRho c hR) +
        (Real.circleAverage (rootShift γ z) p.1.2 p.1.1 - ∫ w, rootShift γ z w * bumpRho c hR w))) := by
  have hρ := integrable_rootShift_mul_bump γ c hR z
  have hD : Tendsto (fun j : ℕ => ∫ w, rootShift γ z w * localTest c hR p j w) atTop
      (𝓝 (Real.circleAverage (rootShift γ z) p.1.2 p.1.1 - ∫ w, rootShift γ z w * bumpRho c hR w)) := by
    have hsplit : ∀ j : ℕ, (∫ w, rootShift γ z w * localTest c hR p j w) =
        (∫ w, circleApprox (localParam_radius_pos p) p.1.2 (j + localShift c p) w * rootShift γ z w) -
          ∫ w, rootShift γ z w * bumpRho c hR w := by
      intro j
      rw [← integral_sub (integrable_circleApprox_mul_rootShift (localParam_radius_pos p) γ p.1.2 z _) hρ]
      congr 1
      funext w
      simp only [localTest, Pi.sub_apply]
      ring
    have hfun : (fun j : ℕ => ∫ w, rootShift γ z w * localTest c hR p j w) = fun j : ℕ =>
        (∫ w, circleApprox (localParam_radius_pos p) p.1.2 (j + localShift c p) w * rootShift γ z w) -
          ∫ w, rootShift γ z w * bumpRho c hR w := funext hsplit
    rw [hfun]
    exact (tendsto_circleApprox_rootShift γ (localParam_radius_pos p) p.1.2 z (localShift c p)).sub_const _
  filter_upwards [ae_tendsto_localPairing hGFF α c hR h0 p] with ω hω
  have hobs : ∀ j : ℕ, obsAt (rootedObs γ α (ball c R) (hC ω) z) (localTest c hR p j) =
      obsAt (localMeanZeroObs α (ball c R) (hC ω)) (localTest c hR p j) +
        ∫ w, rootShift γ z w * localTest c hR p j w := fun j => by
    have hadm := localTest_isTest c hR p j
    simp only [obsAt, hadm, and_self, ↓reduceDIte, rootedObs, localMeanZeroObs]
  have heq : (fun j => obsAt (rootedObs γ α (ball c R) (hC ω) z) (localTest c hR p j)) =
      fun j => obsAt (localMeanZeroObs α (ball c R) (hC ω)) (localTest c hR p j) +
        ∫ w, rootShift γ z w * localTest c hR p j w := funext hobs
  rw [heq]
  exact hω.add hD

/-- Route step 8 (a.s.): the rooted circle coordinate of the observation of `h + f_z` at `p`. -/
theorem ae_localCoord_rooted {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (γ α : ℝ) (c : ℂ) {R : ℝ} (hR : 0 < R) (h0 : (0 : ℂ) ∉ ball c R) (z : ℂ) (p : LocalParam c R) :
    ∀ᵐ ω ∂P, localCoord c hR p (rootedObs γ α (ball c R) (hC ω) z) =
      hcirc ω p.1.1 p.1.2 - α * Real.log (max p.1.1 ‖p.1.2‖) - fieldPairing α (hC ω) (bumpRho c hR) +
        (Real.circleAverage (rootShift γ z) p.1.2 p.1.1 - ∫ w, rootShift γ z w * bumpRho c hR w) := by
  filter_upwards [ae_tendsto_localRooted hGFF γ α c hR h0 z p] with ω hω
  unfold localCoord
  exact hω.limUnder_eq

/-! ### Rooted clause A (route step 8): the rooted profile `hc' r x = h_r(x) + circleAverage(f_z)(x,r)` -/

/-- The rooted circle profile of `h + f_z`: `hc' r x = h^ℂ_r(x) + circleAverage(f_z)(x,r)`. -/
noncomputable def rootedHc (γ : ℝ) (z : ℂ) (hcirc : ℝ → ℂ → ℝ) : ℝ → ℂ → ℝ :=
  fun r x => hcirc r x + Real.circleAverage (rootShift γ z) x r

theorem fieldCircleAverage_rootedHc (γ α : ℝ) (z : ℂ) (hcirc : ℝ → ℂ → ℝ) :
    fieldCircleAverage α (rootedHc γ z hcirc) =
      addCircleAverage (fieldCircleAverage α hcirc) (rootShift γ z) := by
  funext r x
  unfold fieldCircleAverage rootedHc addCircleAverage
  ring

/-- The circle average of the rooted shift is continuous in the centre (for a fixed positive radius). -/
theorem continuous_circleAverage_rootShift_centre (γ : ℝ) (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    Continuous fun x : ℂ => Real.circleAverage (rootShift γ z) x ε := by
  have hfun : (fun x : ℂ => Real.circleAverage (rootShift γ z) x ε) = fun x : ℂ =>
      -γ * Real.log (max ε ‖x - z‖) + γ * Real.circleAverage (fun w => Real.log (max 1 ‖w‖)) x ε := by
    funext x
    exact circleAverage_rootShift γ hε z x
  rw [hfun]
  have h1 : Continuous fun x : ℂ => Real.log (max ε ‖x - z‖) :=
    (continuous_const.max (continuous_id.sub continuous_const).norm).log fun x => (lt_max_of_lt_left hε).ne'
  have h2 : Continuous fun x : ℂ => Real.circleAverage (fun w => Real.log (max 1 ‖w‖)) x ε :=
    (HarmonicBalls.Section6.continuous_circleAverage_radius_center continuous_log_max_one).comp (continuous_const.prodMk continuous_id)
  exact (continuous_const.mul h1).add (continuous_const.mul h2)

theorem continuous_rootedHc (γ : ℝ) (z : ℂ) (hcirc : ℝ → ℂ → ℝ)
    (hcont : ∀ ε : ℝ, 0 < ε → Continuous (hcirc ε)) :
    ∀ ε : ℝ, 0 < ε → Continuous (rootedHc γ z hcirc ε) := fun ε hε =>
  (hcont ε hε).add (continuous_circleAverage_rootShift_centre γ z hε)

/-- Route step 8 (a.s. decoder identity, rooted): the decoded rooted observation is the continuous rooted profile
on `LocalParam c R`. -/
theorem ae_decode_rooted {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (γ α : ℝ) (c : ℂ) {R : ℝ} (hR : 0 < R) (h0 : (0 : ℂ) ∉ ball c R) (z : ℂ)
    (d : ℕ → LocalParam c R) (decode : (ℕ → ℝ) → C(LocalParam c R, ℝ))
    (hdec : ∀ f : C(LocalParam c R, ℝ), decode (fun n => f (d n)) = f) :
    ∀ᵐ ω ∂P, ∃ G : C(LocalParam c R, ℝ),
      (∀ p : LocalParam c R, G p = hcirc ω p.1.1 p.1.2 - α * Real.log (max p.1.1 ‖p.1.2‖) -
        fieldPairing α (hC ω) (bumpRho c hR) +
        (Real.circleAverage (rootShift γ z) p.1.2 p.1.1 - ∫ w, rootShift γ z w * bumpRho c hR w)) ∧
      decode (fun n => localCoord c hR (d n) (rootedObs γ α (ball c R) (hC ω) z)) = G := by
  have hco : ∀ᵐ ω ∂P, ∀ n, localCoord c hR (d n) (rootedObs γ α (ball c R) (hC ω) z) =
      hcirc ω (d n).1.1 (d n).1.2 - α * Real.log (max (d n).1.1 ‖(d n).1.2‖) -
        fieldPairing α (hC ω) (bumpRho c hR) +
        (Real.circleAverage (rootShift γ z) (d n).1.2 (d n).1.1 - ∫ w, rootShift γ z w * bumpRho c hR w) :=
    ae_all_iff.2 fun n => ae_localCoord_rooted hGFF γ α c hR h0 z (d n)
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
  have hA : Continuous fun p : LocalParam c R => Real.log (max p.1.1 ‖p.1.2 - z‖) :=
    Continuous.log ((continuous_fst.comp continuous_subtype_val).max
      (continuous_norm.comp ((continuous_snd.comp continuous_subtype_val).sub continuous_const)))
      fun p => ne_of_gt (lt_of_lt_of_le (hpos p) (le_max_left _ _))
  have hB : Continuous fun p : LocalParam c R =>
      Real.circleAverage (fun w => Real.log (max 1 ‖w‖)) p.1.2 p.1.1 :=
    (HarmonicBalls.Section6.continuous_circleAverage_radius_center continuous_log_max_one).comp hpair
  have hrsEq : (fun p : LocalParam c R => Real.circleAverage (rootShift γ z) p.1.2 p.1.1) = fun p =>
      -γ * Real.log (max p.1.1 ‖p.1.2 - z‖) + γ * Real.circleAverage (fun w => Real.log (max 1 ‖w‖)) p.1.2 p.1.1 :=
    funext fun p => circleAverage_rootShift γ (hpos p) z p.1.2
  have hrs : Continuous fun p : LocalParam c R => Real.circleAverage (rootShift γ z) p.1.2 p.1.1 := by
    rw [hrsEq]
    exact (continuous_const.mul hA).add (continuous_const.mul hB)
  have hgc : Continuous fun p : LocalParam c R => hcirc ω p.1.1 p.1.2 - α * Real.log (max p.1.1 ‖p.1.2‖) -
      fieldPairing α (hC ω) (bumpRho c hR) +
      (Real.circleAverage (rootShift γ z) p.1.2 p.1.1 - ∫ w, rootShift γ z w * bumpRho c hR w) :=
    (((hcirc_c.sub (continuous_const.mul hlog)).sub continuous_const).add (hrs.sub continuous_const))
  refine ⟨⟨_, hgc⟩, fun p => rfl, ?_⟩
  have hfun : (fun n => localCoord c hR (d n) (rootedObs γ α (ball c R) (hC ω) z)) =
      fun n => (⟨_, hgc⟩ : C(LocalParam c R, ℝ)) (d n) :=
    funext fun n => hωn n
  rw [hfun, hdec]

/-- Route step 8, clause A (rooted, almost surely): the kernel of the rooted observation `h + f_z` is a positive multiple
of the rooted γ-LQG measure `μz` on the disc. -/
theorem clauseA_rooted {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (γ α : ℝ) (c : ℂ) {R : ℝ} (hR : 0 < R) (h0 : (0 : ℂ) ∉ ball c R) (z : ℂ)
    (μz : Ω → Measure ℂ)
    (hμz : IsLQGMeasure P γ (fun ω => addCircleAverage (fieldCircleAverage α (hcirc ω))
      (fun w => -γ * Real.log ‖w - z‖ + γ * Real.log (max 1 ‖w‖))) μz)
    (d : ℕ → LocalParam c R) (decode : (ℕ → ℝ) → C(LocalParam c R, ℝ))
    {K : ℕ → Set (ball c R)} (hKs : ∀ s : Set (ball c R), IsCompact s → ∃ n, s ⊆ K n) (T : TestFamilyX K)
    (hdec : ∀ f : C(LocalParam c R, ℝ), decode (fun n => f (d n)) = f) :
    ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧
      (kernelMeas (γ := γ) hKs T (fun y => decode (fun n => localCoord c hR (d n) y))
        (campbellReferenceObs γ α (ball c R) (hC ω) z).2).restrict (ball c R) =
        ENNReal.ofReal a • (μz ω).restrict (ball c R) := by
  have hμ' : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage α (rootedHc γ z (hcirc ω))) (μz ω) := by
    filter_upwards [hμz] with ω hω
    rw [fieldCircleAverage_rootedHc]
    exact hω
  filter_upwards [ae_decode_rooted hGFF γ α c hR h0 z d decode hdec, hGFF.ae_continuousOn_circle, hμ']
    with ω hdecω hcontω hμω
  obtain ⟨G, hG, hGeq⟩ := hdecω
  have hcont' : ∀ ε : ℝ, 0 < ε → Continuous (rootedHc γ z (hcirc ω) ε) := by
    intro ε hε
    have hcirc_ε : Continuous (hcirc ω ε) := by
      have h := hcontω.comp_continuous (continuous_const.prodMk continuous_id)
        (fun x : ℂ => (⟨hε, Set.mem_univ x⟩ : (ε, x) ∈ Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℂ)))
      exact h
    exact continuous_rootedHc γ z (hcirc ω) (fun ε' hε' => by
      have h := hcontω.comp_continuous (continuous_const.prodMk continuous_id)
        (fun x : ℂ => (⟨hε', Set.mem_univ x⟩ : (ε', x) ∈ Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℂ)))
      exact h) ε hε
  have hF : ∀ p : LocalParam c R,
      (fun y => decode (fun n => localCoord c hR (d n) y)) ((campbellReferenceObs γ α (ball c R) (hC ω) z).2) p =
        fieldCircleAverage α (rootedHc γ z (hcirc ω)) p.1.1 p.1.2 -
          (fieldPairing α (hC ω) (bumpRho c hR) + ∫ w, rootShift γ z w * bumpRho c hR w) := by
    intro p
    show decode (fun n => localCoord c hR (d n) ((campbellReferenceObs γ α (ball c R) (hC ω) z).2)) p = _
    rw [campbellReferenceObs_snd_eq_rootedObs, hGeq, hG p]
    unfold fieldCircleAverage rootedHc
    rw [circleAverage_log_norm_eq_max (localParam_radius_pos p) p.1.2]
    ring
  exact kernelMeas_restrict_eq γ α (fieldPairing α (hC ω) (bumpRho c hR) + ∫ w, rootShift γ z w * bumpRho c hR w)
    hR (rootedHc γ z (hcirc ω)) hcont' (μz ω) hμω hKs T
    (fun y => decode (fun n => localCoord c hR (d n) y)) ((campbellReferenceObs γ α (ball c R) (hC ω) z).2) hF

/-- Route steps 1-8 assembled: the kernel `κ` of `LocalMeasureKernelStmt` (route MQ-lh-12), with the countable decoder
of `exists_localDecoder` and the compact exhaustion of the disc; both clauses (unrooted and rooted) are proved here. -/
theorem localMeasureKernelStmt_derived (γ : ℝ) (c₁ c₂ : ℂ) (r₁ r₂ : ℝ) : LocalMeasureKernelStmt γ c₁ c₂ r₁ r₂ := by
  intro hγ0 hγ2 hr1 hr2 hsub1 hsub2 h0
  obtain ⟨d, decode, hdm, hdec⟩ := exists_localDecoder c₂ hr2
  obtain ⟨K, hKc, hKs⟩ := ball_exhaustion c₂ r₂
  obtain ⟨T⟩ := exists_testFamilyX K hKc
  have h0b : (0 : ℂ) ∉ ball c₂ r₂ := fun h => h0 (ball_subset_closedBall h)
  have hdm' : Measurable fun y => decode (fun n => localCoord c₂ hr2 (d n) y) :=
    hdm.comp (measurable_pi_iff.mpr fun n => measurable_localCoord c₂ hr2 (d n))
  refine ⟨kernelMeas (γ := γ) hKs T (fun y => decode (fun n => localCoord c₂ hr2 (d n) y)),
    measurable_kernelMeas γ hKs T _ hdm', ?_, ?_⟩
  · intro α _ Ω _ P _ hC hcirc μ hGFF hμ
    exact clauseA_unrooted γ α hr2 h0b hGFF μ hμ d decode hKs T hdec
  · intro α _ Ω _ P _ hC hcirc hGFF
    refine Filter.Eventually.of_forall fun z => ?_
    intro μz hμz
    exact clauseA_rooted hGFF γ α c₂ hr2 h0b z μz hμz d decode hKs T hdec

/-! ### Rooted clause 2 (route step 8, without the logarithmic cut-off): the field `h - γ log|· - z|` -/

/-- The rooted shift `w ↦ -γ log|w - z|` (`rootedCircleAverage`, `rootedMeanZeroObs`). -/
noncomputable def rootShift0 (γ : ℝ) (z w : ℂ) : ℝ := -γ * Real.log ‖w - z‖

/-- The observation of `rootedMeanZeroObs` is the pairing of `h - γ log|·-z|` (algebra). -/
theorem rootedMeanZeroObs_eq (γ α₀ : ℝ) (φ : ℂ → ℝ) (hC : (ℂ → ℝ) → ℝ) (z : ℂ) :
    fieldPairing α₀ hC φ - γ * ∫ w, Real.log ‖w - z‖ * φ w =
      fieldPairing α₀ hC φ + ∫ w, rootShift0 γ z w * φ w := by
  have h : ∫ w, rootShift0 γ z w * φ w = -γ * ∫ w, Real.log ‖w - z‖ * φ w := by
    rw [← integral_const_mul]
    congr 1
    funext w
    simp only [rootShift0]
    ring
  rw [h]
  ring

/-- The circle average of `-γ log|·-z|` (no linearity needed). -/
theorem circleAverage_rootShift0 (γ : ℝ) {r : ℝ} (hr : 0 < r) (z x : ℂ) :
    Real.circleAverage (rootShift0 γ z) x r = -γ * Real.log (max r ‖x - z‖) := by
  have h := Real.circleAverage_smul (a := -γ) (f := fun w => Real.log ‖w - z‖) (c := x) (R := r)
  have hfun : ((-γ) • fun w : ℂ => Real.log ‖w - z‖) = fun w : ℂ => -γ * Real.log ‖w - z‖ := by
    funext w
    rfl
  rw [hfun, smul_eq_mul] at h
  have e : rootShift0 γ z = fun w : ℂ => -γ * Real.log ‖w - z‖ := rfl
  rw [e, h, circleAverage_log_norm_sub_eq x z hr]

theorem integrable_rootShift0_mul_bump (γ : ℝ) (c : ℂ) {R : ℝ} (hR : 0 < R) (z : ℂ) :
    Integrable fun w => rootShift0 γ z w * bumpRho c hR w := by
  have h1 := (integrable_bump_mul_log_sub c hR z).const_mul (-γ)
  refine h1.congr (Filter.Eventually.of_forall fun w => ?_)
  simp only [rootShift0]
  ring

theorem integrable_circleApprox_mul_rootShift0 {r : ℝ} (hr : 0 < r) (γ : ℝ) (x z : ℂ) (j : ℕ) :
    Integrable fun y => circleApprox hr x j y * rootShift0 γ z y := by
  have hδ : 0 < r * approxEta r j := mul_pos hr (approxEta_pos hr j)
  have i1 : Integrable fun y => unitCircleDensity r (r * approxEta r j) hδ x y * Real.log ‖y - z‖ :=
    integrable_unitCircleDensity_mul_log hr.le hδ x z
  refine (i1.const_mul (-γ)).congr (Filter.Eventually.of_forall fun y => ?_)
  simp only [rootShift0, circleApprox]
  ring

/-- Route step 8 (deterministic limit, no cut-off): the annular averages of `-γ log|·-z|` converge. -/
theorem tendsto_circleApprox_rootShift0 (γ : ℝ) {r : ℝ} (hr : 0 < r) (x z : ℂ) (N : ℕ) :
    Tendsto (fun j : ℕ => ∫ y, circleApprox hr x (j + N) y * rootShift0 γ z y) atTop
      (𝓝 (Real.circleAverage (rootShift0 γ z) x r)) := by
  have hδ : ∀ j : ℕ, 0 < r * approxEta r (j + N) := fun j => mul_pos hr (approxEta_pos hr _)
  have hsmall : ∀ η : ℝ, 0 < η → ∃ M : ℕ, ∀ j, M ≤ j → r * approxEta r (j + N) ≤ r * η := by
    intro η hη
    obtain ⟨M, hM⟩ := eventually_approxEta_lt (r := r) hη
    exact ⟨M, fun j hj => mul_le_mul_of_nonneg_left (le_of_lt (hM (j + N) (by omega))) hr.le⟩
  have hL := tendsto_unitCircleDensity_mul_log (r := r) (δ := fun j => r * approxEta r (j + N))
    hr hδ hsmall x z
  rw [circleAverage_rootShift0 γ hr z x]
  refine (hL.const_mul (-γ)).congr fun j => ?_
  have e : ∫ y, circleApprox hr x (j + N) y * rootShift0 γ z y =
      -γ * ∫ y, unitCircleDensity r (r * approxEta r (j + N)) (hδ j) x y * Real.log ‖y - z‖ := by
    rw [← integral_const_mul]
    congr 1
    funext y
    simp only [rootShift0, circleApprox]
    ring
  exact e.symm

/-- The rooted observation of `h - γ log|·-z|` on the mean-zero tests of `D`. -/
noncomputable def rootedObs0 (γ α : ℝ) (D : Set ℂ) (hC : (ℂ → ℝ) → ℝ) (z : ℂ) :
    {φ : ℂ → ℝ // IsTestFunction D φ ∧ ∫ x, φ x = 0} → ℝ :=
  fun φ => fieldPairing α hC φ.1 + ∫ w, rootShift0 γ z w * φ.1 w

theorem ae_tendsto_localRooted0 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (γ α : ℝ) (c : ℂ) {R : ℝ} (hR : 0 < R) (h0 : (0 : ℂ) ∉ ball c R) (z : ℂ) (p : LocalParam c R) :
    ∀ᵐ ω ∂P, Tendsto (fun j => obsAt (rootedObs0 γ α (ball c R) (hC ω) z) (localTest c hR p j)) atTop
      (𝓝 (hcirc ω p.1.1 p.1.2 - α * Real.log (max p.1.1 ‖p.1.2‖) - fieldPairing α (hC ω) (bumpRho c hR) +
        (Real.circleAverage (rootShift0 γ z) p.1.2 p.1.1 - ∫ w, rootShift0 γ z w * bumpRho c hR w))) := by
  have hρ := integrable_rootShift0_mul_bump γ c hR z
  have hD : Tendsto (fun j : ℕ => ∫ w, rootShift0 γ z w * localTest c hR p j w) atTop
      (𝓝 (Real.circleAverage (rootShift0 γ z) p.1.2 p.1.1 - ∫ w, rootShift0 γ z w * bumpRho c hR w)) := by
    have hsplit : ∀ j : ℕ, (∫ w, rootShift0 γ z w * localTest c hR p j w) =
        (∫ w, circleApprox (localParam_radius_pos p) p.1.2 (j + localShift c p) w * rootShift0 γ z w) -
          ∫ w, rootShift0 γ z w * bumpRho c hR w := by
      intro j
      rw [← integral_sub (integrable_circleApprox_mul_rootShift0 (localParam_radius_pos p) γ p.1.2 z _) hρ]
      congr 1
      funext w
      simp only [localTest, Pi.sub_apply]
      ring
    have hfun : (fun j : ℕ => ∫ w, rootShift0 γ z w * localTest c hR p j w) = fun j : ℕ =>
        (∫ w, circleApprox (localParam_radius_pos p) p.1.2 (j + localShift c p) w * rootShift0 γ z w) -
          ∫ w, rootShift0 γ z w * bumpRho c hR w := funext hsplit
    rw [hfun]
    exact (tendsto_circleApprox_rootShift0 γ (localParam_radius_pos p) p.1.2 z (localShift c p)).sub_const _
  filter_upwards [ae_tendsto_localPairing hGFF α c hR h0 p] with ω hω
  have hobs : ∀ j : ℕ, obsAt (rootedObs0 γ α (ball c R) (hC ω) z) (localTest c hR p j) =
      obsAt (localMeanZeroObs α (ball c R) (hC ω)) (localTest c hR p j) +
        ∫ w, rootShift0 γ z w * localTest c hR p j w := fun j => by
    have hadm := localTest_isTest c hR p j
    simp only [obsAt, hadm, and_self, ↓reduceDIte, rootedObs0, localMeanZeroObs]
  have heq : (fun j => obsAt (rootedObs0 γ α (ball c R) (hC ω) z) (localTest c hR p j)) =
      fun j => obsAt (localMeanZeroObs α (ball c R) (hC ω)) (localTest c hR p j) +
        ∫ w, rootShift0 γ z w * localTest c hR p j w := funext hobs
  rw [heq]
  exact hω.add hD

/-- The rooted circle profile of `h - γ log|·-z|`: `hc0 r x = h^ℂ_r(x) + circleAverage(-γ log|·-z|)(x,r)`. -/
noncomputable def rootedHc0 (γ : ℝ) (z : ℂ) (hcirc : ℝ → ℂ → ℝ) : ℝ → ℂ → ℝ :=
  fun r x => hcirc r x + Real.circleAverage (rootShift0 γ z) x r

theorem rootedCircleAverage_eq_fieldCircleAverage (γ α₀ : ℝ) (z : ℂ) (hcirc : ℝ → ℂ → ℝ) {r : ℝ} (hr : 0 < r)
    (x : ℂ) : rootedCircleAverage α₀ γ z hcirc r x = fieldCircleAverage α₀ (rootedHc0 γ z hcirc) r x := by
  unfold rootedCircleAverage fieldCircleAverage rootedHc0
  rw [circleAverage_rootShift0 γ hr z x, circleAverage_log_norm_sub_eq x z hr]
  ring

theorem continuous_rootedHc0 (γ : ℝ) (z : ℂ) (hcirc : ℝ → ℂ → ℝ)
    (hcont : ∀ ε : ℝ, 0 < ε → Continuous (hcirc ε)) :
    ∀ ε : ℝ, 0 < ε → Continuous (rootedHc0 γ z hcirc ε) := fun ε hε => by
  have h2 : Continuous fun x : ℂ => Real.circleAverage (rootShift0 γ z) x ε := by
    have hfun : (fun x : ℂ => Real.circleAverage (rootShift0 γ z) x ε) =
        fun x : ℂ => -γ * Real.log (max ε ‖x - z‖) :=
      funext fun x => circleAverage_rootShift0 γ hε z x
    rw [hfun]
    exact continuous_const.mul
      ((continuous_const.max (continuous_id.sub continuous_const).norm).log fun x => (lt_max_of_lt_left hε).ne')
  exact (hcont ε hε).add h2

/-- The γ-LQG limit property is invariant under changing the circle profile at positive radii (only the dyadic scales
enter `lqgApprox`). -/
theorem isLQGLimit_congr {γ : ℝ} {f g : ℝ → ℂ → ℝ} (h : ∀ r : ℝ, 0 < r → ∀ x : ℂ, f r x = g r x) {m : Measure ℂ}
    (hm : IsLQGLimit γ f m) : IsLQGLimit γ g m := by
  refine ⟨hm.isLocallyFiniteMeasure, fun φ hφc hφs => ?_⟩
  have hfg : ∀ k : ℕ, lqgApprox γ g (dyadicScale k) = lqgApprox γ f (dyadicScale k) := by
    intro k
    unfold lqgApprox
    congr 1
    funext x
    rw [← h (dyadicScale k) (dyadicScale_pos k) x]
  simp only [hfg]
  exact hm.tendsto_integral φ hφc hφs

theorem ae_localCoord_rooted0 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (γ α : ℝ) (c : ℂ) {R : ℝ} (hR : 0 < R) (h0 : (0 : ℂ) ∉ ball c R) (z : ℂ) (p : LocalParam c R) :
    ∀ᵐ ω ∂P, localCoord c hR p (rootedObs0 γ α (ball c R) (hC ω) z) =
      hcirc ω p.1.1 p.1.2 - α * Real.log (max p.1.1 ‖p.1.2‖) - fieldPairing α (hC ω) (bumpRho c hR) +
        (Real.circleAverage (rootShift0 γ z) p.1.2 p.1.1 - ∫ w, rootShift0 γ z w * bumpRho c hR w) := by
  filter_upwards [ae_tendsto_localRooted0 hGFF γ α c hR h0 z p] with ω hω
  unfold localCoord
  exact hω.limUnder_eq

theorem ae_decode_rooted0 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (γ α : ℝ) (c : ℂ) {R : ℝ} (hR : 0 < R) (h0 : (0 : ℂ) ∉ ball c R) (z : ℂ)
    (d : ℕ → LocalParam c R) (decode : (ℕ → ℝ) → C(LocalParam c R, ℝ))
    (hdec : ∀ f : C(LocalParam c R, ℝ), decode (fun n => f (d n)) = f) :
    ∀ᵐ ω ∂P, ∃ G : C(LocalParam c R, ℝ),
      (∀ p : LocalParam c R, G p = hcirc ω p.1.1 p.1.2 - α * Real.log (max p.1.1 ‖p.1.2‖) -
        fieldPairing α (hC ω) (bumpRho c hR) +
        (Real.circleAverage (rootShift0 γ z) p.1.2 p.1.1 - ∫ w, rootShift0 γ z w * bumpRho c hR w)) ∧
      decode (fun n => localCoord c hR (d n) (rootedObs0 γ α (ball c R) (hC ω) z)) = G := by
  have hco : ∀ᵐ ω ∂P, ∀ n, localCoord c hR (d n) (rootedObs0 γ α (ball c R) (hC ω) z) =
      hcirc ω (d n).1.1 (d n).1.2 - α * Real.log (max (d n).1.1 ‖(d n).1.2‖) -
        fieldPairing α (hC ω) (bumpRho c hR) +
        (Real.circleAverage (rootShift0 γ z) (d n).1.2 (d n).1.1 - ∫ w, rootShift0 γ z w * bumpRho c hR w) :=
    ae_all_iff.2 fun n => ae_localCoord_rooted0 hGFF γ α c hR h0 z (d n)
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
  have hA : Continuous fun p : LocalParam c R => Real.log (max p.1.1 ‖p.1.2 - z‖) :=
    Continuous.log ((continuous_fst.comp continuous_subtype_val).max
      (continuous_norm.comp ((continuous_snd.comp continuous_subtype_val).sub continuous_const)))
      fun p => ne_of_gt (lt_of_lt_of_le (hpos p) (le_max_left _ _))
  have hrsEq : (fun p : LocalParam c R => Real.circleAverage (rootShift0 γ z) p.1.2 p.1.1) = fun p =>
      -γ * Real.log (max p.1.1 ‖p.1.2 - z‖) :=
    funext fun p => circleAverage_rootShift0 γ (hpos p) z p.1.2
  have hrs : Continuous fun p : LocalParam c R => Real.circleAverage (rootShift0 γ z) p.1.2 p.1.1 := by
    rw [hrsEq]
    exact continuous_const.mul hA
  have hgc : Continuous fun p : LocalParam c R => hcirc ω p.1.1 p.1.2 - α * Real.log (max p.1.1 ‖p.1.2‖) -
      fieldPairing α (hC ω) (bumpRho c hR) +
      (Real.circleAverage (rootShift0 γ z) p.1.2 p.1.1 - ∫ w, rootShift0 γ z w * bumpRho c hR w) :=
    (((hcirc_c.sub (continuous_const.mul hlog)).sub continuous_const).add (hrs.sub continuous_const))
  refine ⟨⟨_, hgc⟩, fun p => rfl, ?_⟩
  have hfun : (fun n => localCoord c hR (d n) (rootedObs0 γ α (ball c R) (hC ω) z)) =
      fun n => (⟨_, hgc⟩ : C(LocalParam c R, ℝ)) (d n) :=
    funext fun n => hωn n
  rw [hfun, hdec]

theorem rootedMeanZeroObs_eq_rootedObs0 (γ α : ℝ) (D : Set ℂ) (hC : (ℂ → ℝ) → ℝ) (z : ℂ) :
    rootedMeanZeroObs α γ D z hC = rootedObs0 γ α D hC z :=
  funext fun φ => rootedMeanZeroObs_eq γ α φ.1 hC z

/-- Route step 8, clause 2 (rooted, almost surely): the kernel of `rootedMeanZeroObs` (the observation of
`h - γ log|·-z|`) is a positive multiple of the rooted γ-LQG measure `μz` on the disc. -/
theorem clauseA_rooted0 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (γ α : ℝ) (c : ℂ) {R : ℝ} (hR : 0 < R) (h0 : (0 : ℂ) ∉ ball c R) (z : ℂ)
    (μz : Ω → Measure ℂ)
    (hμz : IsLQGMeasure P γ (fun ω => rootedCircleAverage α γ z (hcirc ω)) μz)
    (d : ℕ → LocalParam c R) (decode : (ℕ → ℝ) → C(LocalParam c R, ℝ))
    {K : ℕ → Set (ball c R)} (hKs : ∀ s : Set (ball c R), IsCompact s → ∃ n, s ⊆ K n) (T : TestFamilyX K)
    (hdec : ∀ f : C(LocalParam c R, ℝ), decode (fun n => f (d n)) = f) :
    ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧
      (kernelMeas (γ := γ) hKs T (fun y => decode (fun n => localCoord c hR (d n) y))
        (rootedMeanZeroObs α γ (ball c R) z (hC ω))).restrict (ball c R) =
        ENNReal.ofReal a • (μz ω).restrict (ball c R) := by
  have hμ' : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage α (rootedHc0 γ z (hcirc ω))) (μz ω) := by
    filter_upwards [hμz] with ω hω
    exact isLQGLimit_congr (fun r hr x => rootedCircleAverage_eq_fieldCircleAverage γ α z (hcirc ω) hr x) hω
  filter_upwards [ae_decode_rooted0 hGFF γ α c hR h0 z d decode hdec, hGFF.ae_continuousOn_circle, hμ']
    with ω hdecω hcontω hμω
  obtain ⟨G, hG, hGeq⟩ := hdecω
  have hcont' : ∀ ε : ℝ, 0 < ε → Continuous (rootedHc0 γ z (hcirc ω) ε) := by
    refine continuous_rootedHc0 γ z (hcirc ω) fun ε hε => ?_
    have h := hcontω.comp_continuous (continuous_const.prodMk continuous_id)
      (fun x : ℂ => (⟨hε, Set.mem_univ x⟩ : (ε, x) ∈ Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℂ)))
    exact h
  have hF : ∀ p : LocalParam c R,
      (fun y => decode (fun n => localCoord c hR (d n) y)) (rootedMeanZeroObs α γ (ball c R) z (hC ω)) p =
        fieldCircleAverage α (rootedHc0 γ z (hcirc ω)) p.1.1 p.1.2 -
          (fieldPairing α (hC ω) (bumpRho c hR) + ∫ w, rootShift0 γ z w * bumpRho c hR w) := by
    intro p
    show decode (fun n => localCoord c hR (d n) (rootedMeanZeroObs α γ (ball c R) z (hC ω))) p = _
    rw [rootedMeanZeroObs_eq_rootedObs0, hGeq, hG p]
    unfold fieldCircleAverage rootedHc0
    rw [circleAverage_log_norm_eq_max (localParam_radius_pos p) p.1.2]
    ring
  exact kernelMeas_restrict_eq γ α
    (fieldPairing α (hC ω) (bumpRho c hR) + ∫ w, rootShift0 γ z w * bumpRho c hR w)
    hR (rootedHc0 γ z (hcirc ω)) hcont' (μz ω) hμω hKs T
    (fun y => decode (fun n => localCoord c hR (d n) y)) (rootedMeanZeroObs α γ (ball c R) z (hC ω)) hF

/-- The kernel measure has total mass at most `1` (`κ(y)(ℂ) = (1+m)⁻¹ m ≤ 1`): the kernel is finite. -/
theorem kernelMeas_univ_le {Y : Type*} [MeasurableSpace Y] (γ : ℝ) {c : ℂ} {R : ℝ} {K : ℕ → Set (ball c R)}
    (hKs : ∀ s : Set (ball c R), IsCompact s → ∃ n, s ⊆ K n) (T : TestFamilyX K)
    (decodeF : Y → C(LocalParam c R, ℝ)) (y : Y) : kernelMeas (γ := γ) hKs T decodeF y univ ≤ 1 := by
  unfold kernelMeas
  rw [Measure.smul_apply, Measure.map_apply measurable_subtype_coe MeasurableSet.univ, Set.preimage_univ,
    smul_eq_mul]
  rcases eq_or_ne (discDecoder (γ := γ) hKs T decodeF y univ) ⊤ with h | h
  · simp [h]
  · have h1 : (1 + discDecoder (γ := γ) hKs T decodeF y univ) ≠ ⊤ :=
      ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, h⟩
    have h0 : (1 + discDecoder (γ := γ) hKs T decodeF y univ) ≠ 0 := by simp
    calc (1 + discDecoder (γ := γ) hKs T decodeF y univ)⁻¹ * discDecoder (γ := γ) hKs T decodeF y univ
        ≤ (1 + discDecoder (γ := γ) hKs T decodeF y univ)⁻¹ *
            (1 + discDecoder (γ := γ) hKs T decodeF y univ) :=
          by gcongr; exact le_add_self
      _ = 1 := ENNReal.inv_mul_cancel h0 h1

/-- The kernel measure is concentrated on the disc: `κ(y) = κ(y).restrict D`. -/
theorem kernelMeas_eq_restrict {Y : Type*} [MeasurableSpace Y] (γ : ℝ) {c : ℂ} {R : ℝ}
    {K : ℕ → Set (ball c R)} (hKs : ∀ s : Set (ball c R), IsCompact s → ∃ n, s ⊆ K n) (T : TestFamilyX K)
    (decodeF : Y → C(LocalParam c R, ℝ)) (y : Y) :
    kernelMeas (γ := γ) hKs T decodeF y = (kernelMeas (γ := γ) hKs T decodeF y).restrict (ball c R) := by
  have hzero : kernelMeas (γ := γ) hKs T decodeF y (ball c R)ᶜ = 0 := by
    unfold kernelMeas
    rw [Measure.smul_apply, Measure.map_apply measurable_subtype_coe measurableSet_ball.compl]
    have hpre : (Subtype.val : ball c R → ℂ) ⁻¹' (ball c R)ᶜ = ∅ := by
      ext x
      exact ⟨fun h => absurd x.2 h, fun h => h.elim⟩
    rw [hpre, measure_empty, smul_zero]
  exact (Measure.restrict_eq_self_of_ae_mem (ae_iff.2 hzero)).symm

/-- Route steps 1-8 assembled for `LocalLQGDecoderCommonFrozen`: the single kernel `κ` (the same as in
`localMeasureKernelStmt_derived`) satisfies both clauses (unrooted and rooted) and is finite. -/
theorem localLQGDecoderCommonFrozen_derived : LocalLQGDecoderCommonFrozen := by
  intro γ _ _ c₂ r₂ hr₂ h0
  have h0b : (0 : ℂ) ∉ ball c₂ r₂ := fun h => h0 (ball_subset_closedBall h)
  obtain ⟨d, decode, hdm, hdec⟩ := exists_localDecoder c₂ hr₂
  obtain ⟨K, hKc, hKs⟩ := ball_exhaustion c₂ r₂
  obtain ⟨T⟩ := exists_testFamilyX K hKc
  have hdm' : Measurable fun y => decode (fun n => localCoord c₂ hr₂ (d n) y) :=
    hdm.comp (measurable_pi_iff.mpr fun n => measurable_localCoord c₂ hr₂ (d n))
  have hmK := measurable_kernelMeas γ hKs T (fun y => decode (fun n => localCoord c₂ hr₂ (d n) y)) hdm'
  refine ⟨⟨kernelMeas (γ := γ) hKs T (fun y => decode (fun n => localCoord c₂ hr₂ (d n) y)), hmK⟩, ?_, ?_, ?_⟩
  · haveI : ProbabilityTheory.IsFiniteKernel
        (⟨kernelMeas (γ := γ) hKs T (fun y => decode (fun n => localCoord c₂ hr₂ (d n) y)), hmK⟩ :
          ProbabilityTheory.Kernel _ ℂ) :=
      ⟨⟨1, ENNReal.one_lt_top, fun y => kernelMeas_univ_le γ hKs T
        (fun y => decode (fun n => localCoord c₂ hr₂ (d n) y)) y⟩⟩
    infer_instance
  · intro α₀ _ Ω _ P _ hC hcirc μ hGFF hμ
    filter_upwards [clauseA_unrooted γ α₀ hr₂ h0b hGFF μ hμ d decode hKs T hdec] with ω ⟨a, ha, hres⟩
    refine ⟨ENNReal.ofReal a, ENNReal.ofReal_pos.2 ha, ENNReal.ofReal_lt_top, ?_⟩
    change kernelMeas (γ := γ) hKs T (fun y => decode (fun n => localCoord c₂ hr₂ (d n) y))
      (localMeanZeroObs α₀ (ball c₂ r₂) (hC ω)) = _
    rw [kernelMeas_eq_restrict, hres]
  · intro α₀ _ z Ω _ P _ hC hcirc μz hGFF hμz
    filter_upwards [clauseA_rooted0 hGFF γ α₀ c₂ hr₂ h0b z μz hμz d decode hKs T hdec] with ω ⟨a, ha, hres⟩
    refine ⟨ENNReal.ofReal a, ENNReal.ofReal_pos.2 ha, ENNReal.ofReal_lt_top, ?_⟩
    change kernelMeas (γ := γ) hKs T (fun y => decode (fun n => localCoord c₂ hr₂ (d n) y))
      (rootedMeanZeroObs α₀ γ (ball c₂ r₂) z (hC ω)) = _
    rw [kernelMeas_eq_restrict, hres]

end Approximants

end LocalDecoderCommon

end HarmonicBalls

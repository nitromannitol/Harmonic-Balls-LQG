import HarmonicBalls.Steps.Sec4.LeastSupersolutionHolder

/-!
# Lemma 4.3 (lemma:harmonic-ball, line 755): reduction to Sections 2-3 and three potential-theoretic steps

`clusterSubharmonicBall_of_steps : ClusterSubharmonicBallStmt`.

## The printed proof (lines 764-789)

Let `Λ = Λ_{B_r;z}(t)` with `closure Λ ⊆ B_r` and `μ_h(∂Λ) = 0`, `O ⊇ closure Λ` open and
`f = ∫_O G_O(·,y) dν(y) + q` a test function (eq:sub-harmonic-potential). By Lemmas 3.2, 3.4 and Proposition 2.3,
`Λ` is open, `μ_h(Λ) = t` and the odometer `u` satisfies eq:v-characterization (lines 766-771): `u = 0` on `∂B_r`,
`Δu = -t δ_z + μ_h|_Λ` on `B_r` (`ν|_{∂Λ} = 0` since `ν ≤ μ_h` and `μ_h(∂Λ) = 0`).

1. (lines 773-779) Integration by parts against `u` on a smooth `Λ' ⊇ Λ` gives `t q(z) = ∫_Λ q dμ_h` for `q`
   harmonic on `O`.
2. (lines 781-786) `t (f-q)(z) - ∫_Λ (f-q) dμ_h = ∫∫ (G_O(z,x) - G_O(y,x)) dν(x) dμ_h(y)`; Fubini; the inner
   integral is `u(x)`; and `∫ u dν ≤ 0` as `u ≥ 0`, `ν|_Λ ≤ 0`.

## Gap G5 and the steps

The printed computation integrates `ν` over `Λ` only and writes `v(z)` for `u(x)` (line 785). But `ν` lives on a
compact subset of `O`, not of `Λ`, and the identity needed is
`t G_O(z,x) - ∫_Λ G_O(y,x) μ_h(dy) = ũ(x)` for all `x ∈ O \ {z}`, where `ũ = 1_Λ u` is the odometer extended by `0`. It holds for every open `O ⊇ closure Λ` (for non-Greenian `O`, `G_O` is the Newtonian
kernel, Defs/Green.lean): `ũ` has compact support and `Δũ = -t δ_z + μ_h|_Λ` on `ℂ`, so `ũ` is the Newtonian
potential of that measure (total mass `0`); the harmonic correction `G_O = N - H` contributes
`t H(z,x) - ∫_Λ H(y,x) μ_h(dy) = 0` by step 1 applied to the harmonic function `H(·,x)`. Then `ν = ν₁ - ν₂` with
`ν₁(Λ) = 0` (the class `subharmonicBallTestClass`, Draft/Section4.lean) gives `∫ ũ dν₁ = 0` and `∫ ũ dν₂ ≥ 0`.

The deterministic data of eq:v-characterization is `IsClusterOdometer μ R Λ z t u`; it includes the Green
representation `u = t G_{B_R}(z,·) - ∫_Λ G_{B_R}(·,x) μ(dx)` on `B_R` (Riesz decomposition of the least
supersolution `v = u - t G_{B_R}(z,·)`, `GreenRepresentationBallStep`, as in Lemma 4.2). The steps:

* `ClusterHarmonicQuadratureStep` — step 1 (integration by parts).
* `ClusterGreenPotentialIdentityStep` — step 2 as corrected by G5: Fubini on `Λ × K` and the identity above, giving
  `∫_Λ G_O ν dμ = t G_O ν(z) - ∫ ũ dν` for every finite `ν` on a compact `K ⊆ O` not charging `z` with
  `G_O(z,·) ∈ L¹(ν)`.
* `GreenHarmonicCorrectionBalayageStep` — the potential theory of the general open set `O` used by step 2: the
  harmonic correction `H(x,·) = I_O[N(x,·)]` (`G_O = N - H`) is jointly measurable, locally bounded, and is swept
  by every measure `m` on a compact `L ⊆ O` whose (regularized) Newtonian potential equals that of `t δ_z` away
  from `L`: `∫ H(x,y) m(dx) = t H(z,y)`. `ClusterGreenPotentialIdentityStep` is proved from it and step 1
  (Proofs/Sec4/ClusterGreenIdentity.lean).
* `GreenFunctionIntegrableAwayFromPoleStep` — `G_O(z,·) ∈ L¹(ν₁)` (the class requires it for `ν₂` only; `ν₁` lives
  on the compact `K \ Λ ∌ z`, where `G_O(z,·)` is bounded).

The reduction (`isSubharmonicBall_of_isClusterOdometer`) is proved: integrability of `f` on `Λ` and
`μ_h(Λ) f(z) = t f(z) ≤ ∫_Λ f dμ_h`.

## Hypotheses consumed

Input I2, Proposition 2.3, Lemmas 3.1, 3.2, 3.4 (Draft statements) and the three steps.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter

universe u

/-- **The data of eq:v-characterization** (lines 766-771), deterministic form. `Λ` is an open set with `z ∈ Λ` and
`closure Λ ⊆ B_R`; `u` is continuous on `B_R \ {z}`, nonnegative on `B_R` off the pole, zero on `B_R \ Λ`, and
`Δu = -t δ_z + μ|_Λ` on `B_R` in the distributional sense, and `u` has the Green representation
`u(y) = t G_{B_R}(z,y) - ∫_Λ G_{B_R}(y,x) μ(dx)` on `B_R`. For the cluster `Λ_{B_r;z}(t)` with
`closure Λ ⊆ B_r` and `μ_h(∂Λ) = 0` and its odometer this is `isClusterOdometer_cluster`. -/
def IsClusterOdometer (μ : Measure ℂ) (R : ℝ) (Λ : Set ℂ) (z : ℂ) (t : ℝ) (u : ℂ → ℝ) : Prop :=
  0 < R ∧ 0 < t ∧ IsOpen Λ ∧ z ∈ Λ ∧ closure Λ ⊆ ball 0 R ∧ ContinuousOn u (ball 0 R \ {z}) ∧
    (∀ x ∈ ball (0 : ℂ) R \ Λ, u x = 0) ∧ (∀ x ∈ ball (0 : ℂ) R, x ≠ z → 0 ≤ u x) ∧
    HasLaplacian u (μ.restrict Λ) (ENNReal.ofReal t • Measure.dirac z) (ball 0 R) ∧
    ∀ y ∈ ball (0 : ℂ) R, IntegrableOn (greenFunction (ball 0 R) y) Λ μ ∧
      u y = t * greenFunction (ball 0 R) z y - ∫ x in Λ, greenFunction (ball 0 R) y x ∂μ

/-! ## Steps -/

/-- **Lemma 4.3, Step 1 (quadrature for harmonic functions, lines 773-779).** Under eq:v-characterization, every
`q` harmonic on an open `O ⊇ closure Λ` is `μ`-integrable on `Λ` and `t q(z) = ∫_Λ q dμ`.
Printed argument: integration by parts of `∫ Δq · u` on a smooth `Λ' ⊇ Λ`. Route: choose `χ ∈ C_c^∞(O ∩ B_R)` with
`χ = 1` near the compact `closure Λ`; test `Δu = -t δ_z + μ|_Λ` against `φ = q χ` (a test function: `q` is
`C^∞` on `O`, harmonic functions being real-analytic, although `HarmonicAt` only asks for `C²`): `φ = q` on `Λ` (integrability
from the definition of `HasLaplacian`), `φ(z) = q(z)`, and `u Δφ = 0` everywhere (`Δφ = Δq = 0` near `closure Λ`,
`u = 0` on `B_R \ Λ`, `φ = 0` off `B_R`). Ingredient: smooth Urysohn cut-off. -/
def ClusterHarmonicQuadratureStep : Prop :=
  ∀ (μ : Measure ℂ) (R : ℝ) (Λ : Set ℂ) (z : ℂ) (t : ℝ) (u : ℂ → ℝ), IsClusterOdometer μ R Λ z t u →
    ∀ (O : Set ℂ) (q : ℂ → ℝ), IsOpen O → closure Λ ⊆ O → InnerProductSpace.HarmonicOnNhd q O →
      IntegrableOn q Λ μ ∧ t * q z = ∫ x in Λ, q x ∂μ

/-- **Lemma 4.3, Step 2 (lines 781-786, corrected by G5).** Let `μ` be Radon with the volume growth condition on
`B_R` and let eq:v-characterization hold. For `O ⊇ closure Λ` open and `ν` a finite measure on a compact `K ⊆ O`
with `ν({z}) = 0` and `G_O(z,·) ∈ L¹(ν)`: the Green potential `G_O ν` is `μ`-integrable on `Λ`, `ũ = 1_Λ u` is
`ν`-integrable and `∫_Λ G_O ν dμ = t G_O ν(z) - ∫ ũ dν`.
Route: (i) the identity `∫_Λ G_O(x,y) μ(dx) = t G_O(z,y) - ũ(y)` for `y ≠ z` (G5): `ũ` is continuous off `z` with
compact support and `Δũ = -t δ_z + μ|_Λ` on `ℂ`, hence (Weyl, Liouville, total mass `μ(Λ) = t`) `ũ` equals the
Newtonian potential `t N(z,·) - ∫_Λ N(x,·) μ(dx)` off `z` (continuity of the logarithmic potential of `μ|_Λ` from
the volume growth bound); the harmonic part `H` of `G_O = N - H` contributes `0` by Step 1 applied to `H(·,y)`
(symmetry of `G_O`); (ii) Fubini on `Λ × K`, `G_O` being jointly measurable and bounded below on bounded sets
(`G_O ≥ min (0, N)`), with `∫_Λ |log |x - y|| μ(dx)` bounded in `y` by the volume growth bound.
 -/
def ClusterGreenPotentialIdentityStep : Prop :=
  ∀ μ : Measure ℂ, IsLocallyFiniteMeasure μ → ∀ R βminus βplus : ℝ, VolumeGrowth μ R βminus βplus →
  ∀ (Λ : Set ℂ) (z : ℂ) (t : ℝ) (u : ℂ → ℝ), IsClusterOdometer μ R Λ z t u →
  ∀ (O K : Set ℂ) (ν : Measure ℂ), IsOpen O → closure Λ ⊆ O → IsCompact K → K ⊆ O → IsFiniteMeasure ν →
    ν Kᶜ = 0 → ν {z} = 0 → Integrable (greenFunction O z) ν →
    IntegrableOn (greenPotential O ν) Λ μ ∧ Integrable (Λ.indicator u) ν ∧
      ∫ x in Λ, greenPotential O ν x ∂μ = t * greenPotential O ν z - ∫ y, Λ.indicator u y ∂ν

/-- **Lemma 4.3, auxiliary step (the Green function is bounded away from its pole).** For `O` open, `z ∈ O` and a
finite measure `ν` concentrated on a compact `K ⊆ O` with `z ∉ K`, `G_O(z,·)` is `ν`-integrable.
Route: `G_O(z,·)` is continuous on `O \ {z}` (harmonic there for Greenian `O`, AG01 Thm 4.1.9 / Cor 4.1.5; the
Newtonian kernel otherwise), hence bounded and measurable on `K`. -/
def GreenFunctionIntegrableAwayFromPoleStep : Prop :=
  ∀ (O K : Set ℂ) (z : ℂ) (ν : Measure ℂ), IsOpen O → z ∈ O → IsCompact K → K ⊆ O → z ∉ K →
    IsFiniteMeasure ν → ν Kᶜ = 0 → Integrable (greenFunction O z) ν

/-- The logarithmic potential `N_ε(x,y) = -(2π)⁻¹ log max(|x - y|, ε)` of the normalized arc length on the circle
`∂B_ε(x)`: the Newtonian kernel capped at its value `-(2π)⁻¹ log ε` on `∂B_ε(x)`. It is continuous and
superharmonic, equals `N(x,y)` for `|x - y| ≥ ε`, and for `closedBall x ε ⊆ O` it has the same harmonic minorants on
`O` as `N(x,·)` (maximum principle on `B_ε(x)`). -/
noncomputable def regularizedNewtonKernel (ε : ℝ) (x y : ℂ) : ℝ :=
  -(2 * Real.pi)⁻¹ * Real.log (max ‖x - y‖ ε)

/-- **Lemma 4.3, Step 2: the harmonic correction of the Green function of an open set** (G5; Armitage–Gardiner
§§3.6, 4.1). Let `O` be open, `L ⊆ O` compact with `cthickening (3ε) L ⊆ O`, `z ∈ L`, and `m` a finite measure on `L`
whose regularized Newtonian potential equals that of `t δ_z` at distance `> ε` from `L`. Then the harmonic
correction `H(x,y) = I_O[N(x,·)](y)` of `G_O = N - H` (`0` for non-Greenian `O`) agrees on `L × O` with a jointly
measurable function, bounded on `L × K` for compact `K ⊆ O`, and `∫ H(x,y) m(dx) = t H(z,y)` for `y ∈ O`.
Route (proved in Proofs/Sec4/GreenBalayage.lean): sweeping (iterated Poisson modification on the rational discs of
`O`, each visited infinitely often) decreases a continuous superharmonic function to its greatest harmonic minorant;
it is linear and commutes with `∫ · m(dx)`, and the swept regularized potential of `m - t δ_z`, a continuous
function with compact support in `O`, tends to `0`. -/
def GreenHarmonicCorrectionBalayageStep : Prop :=
  ∀ (O L : Set ℂ) (m : Measure ℂ) (z : ℂ) (t ε : ℝ), IsOpen O → IsCompact L → IsFiniteMeasure m → m Lᶜ = 0 →
    z ∈ L → 0 < ε → cthickening (3 * ε) L ⊆ O →
    (∀ w : ℂ, (∀ x ∈ L, ε < ‖x - w‖) →
      ∫ x, regularizedNewtonKernel ε x w ∂m = t * regularizedNewtonKernel ε z w) →
    ∃ H : ℂ → ℂ → ℝ, Measurable (Function.uncurry H) ∧
      (∀ x ∈ L, ∀ y ∈ O, (greatestHarmonicMinorant O (newtonKernelEReal x) y).toReal = H x y) ∧
      (∀ K : Set ℂ, IsCompact K → K ⊆ O → ∃ C : ℝ, ∀ x ∈ L, ∀ y ∈ K, |H x y| ≤ C) ∧
      ∀ y ∈ O, ∫ x, H x y ∂m = t * H z y

/-! ## Reduction -/

/-- **eq:v-characterization for the cluster** (lines 764-771): from Lemmas 3.1-3.2, Proposition 2.3 and
`μ_h(∂Λ) = 0`, `closure Λ ⊆ B_r`. The boundary part `ν|_{∂Λ}` of Lemma 3.2 vanishes since `ν ≤ μ_h` on `B_r`. -/
theorem isClusterOdometer_cluster (h23 : GreenFunctionBallStmt) (hRep : GreenRepresentationBallStep)
    {μ ν : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {r t βm βp : ℝ} {z : ℂ} (hV : VolumeGrowth μ r βm βp)
    (hr : 0 < r) (ht : 0 < t) (hz : z ∈ ball (0 : ℂ) r)
    (hv : ContinuousOn (leastSupersolution μ r z t) (closedBall 0 r))
    (hv0 : ∀ x ∈ sphere (0 : ℂ) r, leastSupersolution μ r z t x = 0) (hopen : IsOpen (cluster μ r z t))
    (hle : ν.restrict (ball 0 r) ≤ μ.restrict (ball 0 r))
    (hvLap : HasLaplacian (leastSupersolution μ r z t)
      (μ.restrict (cluster μ r z t) + ν.restrict (frontier (cluster μ r z t))) 0 (ball 0 r))
    (hLap : HasLaplacian (odometer μ r z t)
      (μ.restrict (cluster μ r z t) + ν.restrict (frontier (cluster μ r z t)))
      (ENNReal.ofReal t • Measure.dirac z) (ball 0 r))
    (hcl : closure (cluster μ r z t) ⊆ ball 0 r) (hfr : μ (frontier (cluster μ r z t)) = 0) :
    IsClusterOdometer μ r (cluster μ r z t) z t (odometer μ r z t) := by
  have hνfr : ν.restrict (frontier (cluster μ r z t)) = 0 := by
    rw [Measure.restrict_eq_zero]
    have hsub : frontier (cluster μ r z t) ⊆ ball 0 r := frontier_subset_closure.trans hcl
    have h := Measure.le_iff'.1 hle (frontier (cluster μ r z t))
    rw [Measure.restrict_eq_self (μ := ν) hsub, Measure.restrict_eq_self (μ := μ) hsub, hfr] at h
    exact le_antisymm h zero_le
  rw [hνfr, add_zero] at hLap hvLap
  refine ⟨hr, ht, hopen, self_mem_cluster hz, hcl,
    (continuousOn_odometer h23 hr hz hv).mono (sdiff_subset_sdiff_left ball_subset_closedBall),
    fun x hx => odometer_eq_zero_of_notMem_cluster ht.le hx.1 hx.2,
    fun x hx hxz => odometer_nonneg ht.le (ball_subset_closedBall hx) hxz, hLap, fun y hy => ?_⟩
  have hΛB : cluster μ r z t ⊆ ball 0 r := subset_closure.trans hcl
  have hres : (μ.restrict (cluster μ r z t)).restrict (ball 0 r) = μ.restrict (cluster μ r z t) := by
    rw [Measure.restrict_restrict measurableSet_ball, inter_eq_right.2 hΛB]
  have hσ : (μ.restrict (cluster μ r z t)).restrict (ball 0 r) ≤ μ.restrict (ball 0 r) := by
    rw [hres]
    exact Measure.restrict_mono hΛB le_rfl
  obtain ⟨hi, he⟩ := hRep μ hμ r βm βp hr hV _ _ hσ hv hv0 hvLap y hy
  rw [IntegrableOn, hres] at hi
  rw [hres] at he
  refine ⟨hi, ?_⟩
  rw [odometer, he]
  ring

/-- **Lemma 4.3, deterministic form.** Under eq:v-characterization with `μ(Λ) = t`, for a Radon measure with the
volume growth condition on `B_R`, `Λ` is a subharmonic ball centred at `z`. -/
theorem isSubharmonicBall_of_isClusterOdometer (hS1 : ClusterHarmonicQuadratureStep)
    (hS2 : ClusterGreenPotentialIdentityStep) (hS3 : GreenFunctionIntegrableAwayFromPoleStep)
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ} (hV : VolumeGrowth μ R βm βp) {Λ : Set ℂ}
    {z : ℂ} {t : ℝ} {u : ℂ → ℝ} (hU : IsClusterOdometer μ R Λ z t u) (hmass : μ Λ = ENNReal.ofReal t) :
    IsSubharmonicBall μ Λ z := by
  obtain ⟨-, ht, hΛo, hzΛ, hclR, -, -, hnn, -, -⟩ := id hU
  refine ⟨hΛo, hzΛ, by rw [hmass]; exact ENNReal.ofReal_pos.2 ht, by rw [hmass]; exact ENNReal.ofReal_lt_top,
    ?_⟩
  rintro f ⟨O, K, ν₁, ν₂, q, hO, hΛO, hK, hKO, hν₁, hν₂, hν₁K, hν₂K, hν₁Λ, hq, hν₂z, hGz, rfl⟩
  obtain ⟨hqi, hqeq⟩ := hS1 μ R Λ z t u hU O q hO hΛO hq
  have hν₁z : ν₁ {z} = 0 := measure_mono_null (singleton_subset_iff.2 hzΛ) hν₁Λ
  have hG₁ : Integrable (greenFunction O z) ν₁ := by
    refine hS3 O (K \ Λ) z ν₁ hO (hΛO (subset_closure hzΛ)) (hK.diff hΛo) (sdiff_subset.trans hKO)
      (fun h => h.2 hzΛ) hν₁ ?_
    rw [compl_sdiff]
    exact measure_union_null hν₁Λ hν₁K
  obtain ⟨hi₁, -, he₁⟩ := hS2 μ hμ R βm βp hV Λ z t u hU O K ν₁ hO hΛO hK hKO hν₁ hν₁K hν₁z hG₁
  obtain ⟨hi₂, -, he₂⟩ := hS2 μ hμ R βm βp hV Λ z t u hU O K ν₂ hO hΛO hK hKO hν₂ hν₂K hν₂z hGz
  have h0 : ∫ y, Λ.indicator u y ∂ν₁ = 0 := by
    refine integral_eq_zero_of_ae ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hν₁Λ] with y hy
    exact indicator_of_notMem hy u
  have hpos : 0 ≤ ∫ y, Λ.indicator u y ∂ν₂ := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hν₂z] with y hy
    by_cases hyΛ : y ∈ Λ
    · rw [indicator_of_mem hyΛ]
      exact hnn y (hclR (subset_closure hyΛ)) hy
    · rw [indicator_of_notMem hyΛ]
      rfl
  have hreal : μ.real Λ = t := by rw [measureReal_def, hmass, ENNReal.toReal_ofReal ht.le]
  refine ⟨(hqi.add hi₁).sub hi₂, ?_⟩
  rw [hreal, integral_sub' (hqi.add hi₁) hi₂, integral_add' hqi hi₁, ← hqeq, he₁, he₂, h0]
  simp only [Pi.add_apply, Pi.sub_apply]
  linarith

/-- **Lemma 4.3 from Sections 2-3** (lines 764-789, with the repair G5), and the steps
`ClusterHarmonicQuadratureStep`, `ClusterGreenPotentialIdentityStep`, `GreenFunctionIntegrableAwayFromPoleStep`, and
`GreenRepresentationBallStep` (the Green representation of the odometer on `B_r`, as in Lemma 4.2). -/
theorem clusterSubharmonicBall_of_steps (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h23 : GreenFunctionBallStmt)
    (h31 : LeastSupersolutionMemStmt.{u}) (h32 : ClusterOpenLaplacianStmt.{u})
    (h34 : ClusterConservationOfMassStmt.{u}) (hRep : GreenRepresentationBallStep)
    (hS1 : ClusterHarmonicQuadratureStep)
    (hS2 : ClusterGreenPotentialIdentityStep) (hS3 : GreenFunctionIntegrableAwayFromPoleStep) :
    ClusterSubharmonicBallStmt.{u} := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  obtain ⟨βm, βp, hae⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  filter_upwards [hae, h31 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ, h32 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    h34 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hω h1 h2 h4
  intro r t hr ht z hz hcl hfr
  obtain ⟨hopen, -, ν, -, -, hle, hvLap, hLap⟩ := h2 t r ht hr z hz
  exact isSubharmonicBall_of_isClusterOdometer hS1 hS2 hS3 hω.1 (hω.2 r hr)
    (isClusterOdometer_cluster h23 hRep hω.1 (hω.2 r hr) hr ht hz (h1 t r ht hr z hz).2.1
      (fun x hx => leastSupersolution_eq_zero_of_mem_sphere (h4 r t hr ht z hz).2.1 hx) hopen hle hvLap hLap hcl
      hfr)
    ((h4 r t hr ht z hz).2.2 hcl hfr)

end HarmonicBalls

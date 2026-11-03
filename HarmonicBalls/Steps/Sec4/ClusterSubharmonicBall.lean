import HarmonicBalls.Steps.Sec4.Basic

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
`t G_O(z,x) - ∫_Λ G_O(y,x) μ_h(dy) = ũ(x)` for all `x ∈ O \ {z}`, where `ũ = 1_Λ u` is the odometer extended by `0`
(docs/campaign/GRAPH.md G5). It holds for every open `O ⊇ closure Λ` (for non-Greenian `O`, `G_O` is the Newtonian
kernel, Defs/Green.lean): `ũ` has compact support and `Δũ = -t δ_z + μ_h|_Λ` on `ℂ`, so `ũ` is the Newtonian
potential of that measure (total mass `0`); the harmonic correction `G_O = N - H` contributes
`t H(z,x) - ∫_Λ H(y,x) μ_h(dy) = 0` by step 1 applied to the harmonic function `H(·,x)`. Then `ν = ν₁ - ν₂` with
`ν₁(Λ) = 0` (the class `subharmonicBallTestClass`, Draft/Section4.lean) gives `∫ ũ dν₁ = 0` and `∫ ũ dν₂ ≥ 0`.

The deterministic data of eq:v-characterization is `IsClusterOdometer μ R Λ z t u`. The steps:

* `ClusterHarmonicQuadratureStep` — step 1 (integration by parts).
* `ClusterGreenPotentialIdentityStep` — step 2 as corrected by G5: Fubini on `Λ × K` and the identity above, giving
  `∫_Λ G_O ν dμ = t G_O ν(z) - ∫ ũ dν` for every finite `ν` on a compact `K ⊆ O` not charging `z` with
  `G_O(z,·) ∈ L¹(ν)`.
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
`Δu = -t δ_z + μ|_Λ` on `B_R` in the distributional sense. For the cluster `Λ_{B_r;z}(t)` with `closure Λ ⊆ B_r`
and `μ_h(∂Λ) = 0` and its odometer this is `isClusterOdometer_cluster`. -/
def IsClusterOdometer (μ : Measure ℂ) (R : ℝ) (Λ : Set ℂ) (z : ℂ) (t : ℝ) (u : ℂ → ℝ) : Prop :=
  0 < R ∧ 0 < t ∧ IsOpen Λ ∧ z ∈ Λ ∧ closure Λ ⊆ ball 0 R ∧ ContinuousOn u (ball 0 R \ {z}) ∧
    (∀ x ∈ ball (0 : ℂ) R \ Λ, u x = 0) ∧ (∀ x ∈ ball (0 : ℂ) R, x ≠ z → 0 ≤ u x) ∧
    HasLaplacian u (μ.restrict Λ) (ENNReal.ofReal t • Measure.dirac z) (ball 0 R)

/-! ## Steps -/

/-- **Lemma 4.3, Step 1 (quadrature for harmonic functions, lines 773-779).** Under eq:v-characterization, every
`q` harmonic on an open `O ⊇ closure Λ` is `μ`-integrable on `Λ` and `t q(z) = ∫_Λ q dμ`.
Printed argument: integration by parts of `∫ Δq · u` on a smooth `Λ' ⊇ Λ`. Route: choose `χ ∈ C_c^∞(O ∩ B_R)` with
`χ = 1` near the compact `closure Λ`; test `Δu = -t δ_z + μ|_Λ` against `φ = q χ` (a test function: `q` is
`C^∞` on `O`, harmonic functions being real-analytic, although `HarmonicAt` only asks for `C²`): `φ = q` on `Λ` (integrability
from the definition of `HasLaplacian`), `φ(z) = q(z)`, and `u Δφ = 0` everywhere (`Δφ = Δq = 0` near `closure Λ`,
`u = 0` on `B_R \ Λ`, `φ = 0` off `B_R`). Difficulty: medium (1-2 rounds; smooth Urysohn cut-off). -/
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
Difficulty: hard (3+ rounds). -/
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
Newtonian kernel otherwise), hence bounded and measurable on `K`. Difficulty: medium (1-2 rounds). -/
def GreenFunctionIntegrableAwayFromPoleStep : Prop :=
  ∀ (O K : Set ℂ) (z : ℂ) (ν : Measure ℂ), IsOpen O → z ∈ O → IsCompact K → K ⊆ O → z ∉ K →
    IsFiniteMeasure ν → ν Kᶜ = 0 → Integrable (greenFunction O z) ν

/-! ## Reduction -/

/-- **eq:v-characterization for the cluster** (lines 764-771): from Lemmas 3.1-3.2, Proposition 2.3 and
`μ_h(∂Λ) = 0`, `closure Λ ⊆ B_r`. The boundary part `ν|_{∂Λ}` of Lemma 3.2 vanishes since `ν ≤ μ_h` on `B_r`. -/
theorem isClusterOdometer_cluster (h23 : GreenFunctionBallStmt) {μ ν : Measure ℂ} {r t : ℝ} {z : ℂ}
    (hr : 0 < r) (ht : 0 < t) (hz : z ∈ ball (0 : ℂ) r)
    (hv : ContinuousOn (leastSupersolution μ r z t) (closedBall 0 r)) (hopen : IsOpen (cluster μ r z t))
    (hle : ν.restrict (ball 0 r) ≤ μ.restrict (ball 0 r))
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
  rw [hνfr, add_zero] at hLap
  exact ⟨hr, ht, hopen, self_mem_cluster hz, hcl,
    (continuousOn_odometer h23 hr hz hv).mono (sdiff_subset_sdiff_left ball_subset_closedBall),
    fun x hx => odometer_eq_zero_of_notMem_cluster ht.le hx.1 hx.2,
    fun x hx hxz => odometer_nonneg ht.le (ball_subset_closedBall hx) hxz, hLap⟩

/-- **Lemma 4.3, deterministic form.** Under eq:v-characterization with `μ(Λ) = t`, for a Radon measure with the
volume growth condition on `B_R`, `Λ` is a subharmonic ball centred at `z`. -/
theorem isSubharmonicBall_of_isClusterOdometer (hS1 : ClusterHarmonicQuadratureStep)
    (hS2 : ClusterGreenPotentialIdentityStep) (hS3 : GreenFunctionIntegrableAwayFromPoleStep)
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ} (hV : VolumeGrowth μ R βm βp) {Λ : Set ℂ}
    {z : ℂ} {t : ℝ} {u : ℂ → ℝ} (hU : IsClusterOdometer μ R Λ z t u) (hmass : μ Λ = ENNReal.ofReal t) :
    IsSubharmonicBall μ Λ z := by
  obtain ⟨-, ht, hΛo, hzΛ, hclR, -, -, hnn, -⟩ := id hU
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
`ClusterHarmonicQuadratureStep`, `ClusterGreenPotentialIdentityStep`, `GreenFunctionIntegrableAwayFromPoleStep`. -/
theorem clusterSubharmonicBall_of_steps (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h23 : GreenFunctionBallStmt)
    (h31 : LeastSupersolutionMemStmt.{u}) (h32 : ClusterOpenLaplacianStmt.{u})
    (h34 : ClusterConservationOfMassStmt.{u}) (hS1 : ClusterHarmonicQuadratureStep)
    (hS2 : ClusterGreenPotentialIdentityStep) (hS3 : GreenFunctionIntegrableAwayFromPoleStep) :
    ClusterSubharmonicBallStmt.{u} := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  obtain ⟨βm, βp, hae⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  filter_upwards [hae, h31 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ, h32 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    h34 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hω h1 h2 h4
  intro r t hr ht z hz hcl hfr
  obtain ⟨hopen, -, ν, -, -, hle, -, hLap⟩ := h2 t r ht hr z hz
  exact isSubharmonicBall_of_isClusterOdometer hS1 hS2 hS3 hω.1 (hω.2 r hr)
    (isClusterOdometer_cluster h23 hr ht hz (h1 t r ht hr z hz).2.1 hopen hle hLap hcl hfr)
    ((h4 r t hr ht z hz).2.2 hcl hfr)

end HarmonicBalls

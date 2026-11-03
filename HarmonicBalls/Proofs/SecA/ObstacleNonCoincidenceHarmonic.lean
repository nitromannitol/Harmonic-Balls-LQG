import HarmonicBalls.Steps.SecA.ObstacleNonCoincidenceHarmonic
import HarmonicBalls.Proofs.SecA.ObstacleLeastSuperharmonicMajorant
import Mathlib.Analysis.Complex.Harmonic.MeanValue

/-!
# Lemma A.2: proofs of Steps 2 and 3

Proofs of the steps `ObstacleNonCoincidenceHarmonicStep2` (`ṽ_t` is subharmonic on `Λ_t`, lines 3661-3712) and
`ObstacleNonCoincidenceHarmonicStep3` (no open `W ⊆ Λ_t` away from the pole with `∂W ∩ Λ_t = ∅`, lines 3714-3716)
of `Steps/SecA/ObstacleNonCoincidenceHarmonic.lean`, for a general radius `R > 0` and pole `z ∈ B_R`.

* Step 2. Instead of the printed contradiction argument (lines 3661-3712), the local mean value inequality is proved
  directly: near each `x ∈ Λ_t` there is a closed disc on which `inf ṽ_t ≥ L ≥ sup β_t` (eq:lies-way-above; at the
  pole `β_t → -∞` and `ṽ_t ≥ 0`). For every smaller disc `B_r(x)` the Poisson modification `g` of `ṽ_t` is a
  superharmonic majorant of `β_t` (eq:above-obstacle: `g ≥ min_{∂B_r(x)} ṽ_t ≥ L` inside), so `ṽ_t = f_t ≤ g` and
  `ṽ_t(x) ≤ g(x) = M(ṽ_t; x, r)`. The local sub-mean-value property is global (AG01 Thm 3.2.2,
  `circleAverage_le_of_localSuperMean`).
* Step 3. The odometer `v_t = ṽ_t - β_t = ṽ_t + t G_{B_R}(z,·) - q_{B_R}` has the sub-mean-value property on `W`
  (Step 2, harmonicity of `G_{B_R}(z,·)` off the pole, superharmonicity of `q_{B_R}`), is positive on `W`, continuous
  on `closure W` and `≤ 0` on `∂W` (off `Λ_t` inside `B_R`; on `∂B_R`, `ṽ_t ≤ q_{B_R} = 0 = β_t`, the content of
  Lemma A.4 used by the printed proof). The maximum principle `eq_empty_of_pos_of_subMean` (a point of maximal real
  part among the maximizers) gives `W = ∅`.

Both steps are proved from Lemma A.1 (general form, `ObstacleLeastSuperharmonicMajorantGeneral`); Step 3 also uses
the superharmonicity of `q_{B_R}` (property 2 of `q_{B_R}`, line 3539).

## Lemma A.1 without `GreenPotentialBallLaplacianStep`, and the `_holds` theorems

* `isSuperharmonicOn_greenPotentialBall`: `q_{B_R}` is superharmonic in `B_R` (classical sense) under the volume
  growth condition: `M(G_{B_R}(y,·); x, r) ≤ G_{B_R}(y,x)` for `y ≠ x` (`G = N(y,·) - h_y`, Jensen's formula), `μ` has
  no atoms (`VolumeGrowth.measure_singleton`), and Fubini over `[0, 2π] × B_R` with the uniform bound
  `M(G_{B_R}(y,·); x, r) ≤ (2π)⁻¹ (log (2R²) - log R - log r)`.
* `obstacleLeastSuperharmonicMajorantGeneral_holds`: the reduction `obstacleLeastSuperharmonicMajorantGeneral_of_steps`
  used `GreenPotentialBallLaplacianStep` (`Δ q_{B_R} = -μ`) only for `Δ q_{B_R} ≤ 0`, which now follows from the
  superharmonicity of `q_{B_R}` and `laplacianLEOfSuperharmonicStep_holds`; with the steps of
  Proofs/SecA/ObstacleLeastSuperharmonicMajorant.lean this proves Lemma A.1 (`obstacleLeastSuperharmonicMajorant_holds`).
* `obstacleNonCoincidenceHarmonicStep2_holds`, `obstacleNonCoincidenceHarmonicStep3_holds`, and Lemma A.2
  (`obstacleNonCoincidenceHarmonicGeneral_holds`, `obstacleNonCoincidenceHarmonic_holds`).
-/

namespace HarmonicBalls

open MeasureTheory Metric Filter Topology Set

/-! ## Circle averages and a maximum principle -/

theorem circleAverage_neg_fun (f : ℂ → ℝ) (c : ℂ) (r : ℝ) :
    Real.circleAverage (-f) c r = -Real.circleAverage f c r := by
  have h : (-f) = fun y => (-1 : ℝ) • f y := by
    funext y
    simp
  rw [h, Real.circleAverage_fun_smul]
  simp

/-- A function continuous on a circle and `≤ m` there, with a value `< m` at the point `c + r`, has circle
average `< m`. -/
theorem circleAverage_lt_of_le_of_lt {f : ℂ → ℝ} {c : ℂ} {r m : ℝ} (hr : 0 < r)
    (hf : ContinuousOn f (sphere c r)) (hle : ∀ y ∈ sphere c r, f y ≤ m) (hlt : f (c + r) < m) :
    Real.circleAverage f c r < m := by
  rw [Real.circleAverage_def, smul_eq_mul]
  have h2π : 0 < 2 * Real.pi := Real.two_pi_pos
  have hcont : ContinuousOn (fun θ => f (circleMap c r θ)) (Icc 0 (2 * Real.pi)) :=
    hf.comp (continuous_circleMap c r).continuousOn (fun θ _ => circleMap_mem_sphere c hr.le θ)
  have hint : ∫ θ in (0 : ℝ)..2 * Real.pi, f (circleMap c r θ) < ∫ _ in (0 : ℝ)..2 * Real.pi, m :=
    intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt h2π hcont continuousOn_const
      (fun θ _ => hle _ (circleMap_mem_sphere c hr.le θ)) ⟨0, ⟨le_rfl, h2π.le⟩, by simpa [circleMap] using hlt⟩
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hint
  calc (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, f (circleMap c r θ)
      < (2 * Real.pi)⁻¹ * (2 * Real.pi * m) := mul_lt_mul_of_pos_left hint (inv_pos.2 h2π)
    _ = m := by field_simp

/-- **Maximum principle** for the sub-mean-value property: a function continuous on the closure of a bounded open
set `W`, positive on `W`, `≤ 0` on `∂W` and with the sub-mean-value property on some disc around each point of `W`
forces `W = ∅`. (Among the maximizers on `closure W`, which lie in `W`, one of maximal real part `p` has
`f = max f` on a circle around `p` by the strict mean value inequality, hence at `p + r`.) -/
theorem eq_empty_of_pos_of_subMean {W : Set ℂ} {f : ℂ → ℝ} (hWb : Bornology.IsBounded W)
    (hfc : ContinuousOn f (closure W)) (hpos : ∀ x ∈ W, 0 < f x) (hfr : ∀ x ∈ frontier W, f x ≤ 0)
    (hsub : ∀ x ∈ W, ∃ r > 0, closedBall x r ⊆ W ∧ f x ≤ Real.circleAverage f x r) : W = ∅ := by
  by_contra hne
  obtain ⟨w₀, hw₀⟩ := nonempty_iff_ne_empty.2 hne
  have hK : IsCompact (closure W) := hWb.isCompact_closure
  obtain ⟨p, hpK, hpmax⟩ := hK.exists_isMaxOn ⟨w₀, subset_closure hw₀⟩ hfc
  have hSc : IsCompact (closure W ∩ f ⁻¹' {f p}) :=
    hK.of_isClosed_subset (hfc.preimage_isClosed_of_isClosed isClosed_closure isClosed_singleton)
      inter_subset_left
  obtain ⟨p', hp'S, hp'max⟩ := hSc.exists_isMaxOn ⟨p, hpK, rfl⟩ Complex.continuous_re.continuousOn
  have hm : 0 < f p := (hpos w₀ hw₀).trans_le (isMaxOn_iff.1 hpmax w₀ (subset_closure hw₀))
  have hp'eq : f p' = f p := hp'S.2
  have hp'W : p' ∈ W := by
    by_contra hp'W
    have hfr' := hfr p' ⟨hp'S.1, fun hint => hp'W (interior_subset hint)⟩
    linarith
  obtain ⟨r, hr, hsubW, hmean⟩ := hsub p' hp'W
  have hsphW : sphere p' r ⊆ W := sphere_subset_closedBall.trans hsubW
  have hle : ∀ y ∈ sphere p' r, f y ≤ f p := fun y hy => isMaxOn_iff.1 hpmax y (subset_closure (hsphW hy))
  have hfsph : ContinuousOn f (sphere p' r) := hfc.mono (hsphW.trans subset_closure)
  have hmem : p' + r ∈ sphere p' r := by
    simpa [circleMap_zero] using circleMap_mem_sphere p' hr.le 0
  have hq : f (p' + r) = f p := by
    by_contra hne'
    have hlt := circleAverage_lt_of_le_of_lt hr hfsph hle (lt_of_le_of_ne (hle _ hmem) hne')
    linarith
  have hre := isMaxOn_iff.1 hp'max (p' + r) ⟨subset_closure (hsphW hmem), hq⟩
  simp at hre
  linarith

/-! ## The non-coincidence set near a point -/

section NonCoincidence

variable {μ : Measure ℂ} {R βm βp : ℝ} {z : ℂ} {t : ℝ}

/-- `Λ_t` is open (Step 1 of Lemma A.2, lines 3657-3659, as in `obstacleNonCoincidenceHarmonicGeneral_of_steps`). -/
theorem isOpen_nonCoincidenceSet_of (hA1 : ObstacleLeastSuperharmonicMajorantGeneral)
    (hμ : IsLocallyFiniteMeasure μ) (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) (hz : z ∈ ball (0 : ℂ) R)
    (ht : 0 < t) : IsOpen (nonCoincidenceSet μ R z t) := by
  obtain ⟨-, hvc, -, -, -⟩ := hA1 μ hμ R βm βp hR hV z hz t ht
  have hqc := greenPotentialBallContinuousStep_holds μ hμ R βm βp hR hV
  have hβc := continuousOn_obstacle (t := t) greenFunctionBall hR hz hqc
  have hvcont : ∀ x ∈ ball (0 : ℂ) R, ContinuousAt (shiftedLeastSupersolution μ R z t) x := fun x hx =>
    hvc.continuousAt (mem_of_superset (isOpen_ball.mem_nhds hx) ball_subset_closedBall)
  rw [isOpen_iff_mem_nhds]
  intro x hx
  by_cases hxz : x = z
  · subst hxz
    have hlow : ∀ᶠ y in 𝓝 x, shiftedLeastSupersolution μ R x t x - 1 < shiftedLeastSupersolution μ R x t y :=
      (hvcont x hx.1).eventually (lt_mem_nhds (by linarith))
    have hβ : ∀ᶠ y in 𝓝[≠] x, obstacle μ R x t y < shiftedLeastSupersolution μ R x t x - 1 :=
      (obstacleTendstoAtBotStep_holds μ R x t hR hz ht hqc).eventually (eventually_lt_atBot _)
    rw [eventually_nhdsWithin_iff] at hβ
    filter_upwards [isOpen_ball.mem_nhds hx.1, hlow, hβ] with y hyb hyv hyβ
    refine ⟨hyb, ?_⟩
    by_cases hyx : y = x
    · exact Or.inl hyx
    · exact Or.inr ((hyβ hyx).trans hyv)
  · have hxb : x ∈ ball (0 : ℂ) R := hx.1
    have hlt : obstacle μ R z t x < shiftedLeastSupersolution μ R z t x := hx.2.resolve_left hxz
    have hβx : ContinuousAt (obstacle μ R z t) x := by
      refine hβc.continuousAt (mem_of_superset
        ((isOpen_ball.sdiff isClosed_singleton).mem_nhds ⟨hxb, hxz⟩) ?_)
      exact fun y hy => ⟨ball_subset_closedBall hy.1, hy.2⟩
    filter_upwards [isOpen_ball.mem_nhds hxb, hβx.eventually_lt (hvcont x hxb) hlt] with y hyb hy
    exact ⟨hyb, Or.inr hy⟩

/-- Near a point `x ∈ Λ_t` the least supersolution lies above a level `L` and the obstacle below it, on a closed disc
(eq:lies-way-above, line 3690; at the pole `β_t → -∞` and `ṽ_t ≥ 0`, so `L = 0`). -/
theorem exists_closedBall_obstacle_le_of_mem (hA1 : ObstacleLeastSuperharmonicMajorantGeneral)
    (hμ : IsLocallyFiniteMeasure μ) (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) (hz : z ∈ ball (0 : ℂ) R)
    (ht : 0 < t) {x : ℂ} (hx : x ∈ nonCoincidenceSet μ R z t) :
    ∃ δ > 0, closedBall x δ ⊆ ball (0 : ℂ) R ∧ ∃ L : ℝ,
      (∀ ζ ∈ closedBall x δ, L ≤ shiftedLeastSupersolution μ R z t ζ) ∧
      ∀ y ∈ closedBall x δ, y ≠ z → obstacle μ R z t y ≤ L := by
  obtain ⟨-, hvc, -, hv0, -⟩ := hA1 μ hμ R βm βp hR hV z hz t ht
  have hqc := greenPotentialBallContinuousStep_holds μ hμ R βm βp hR hV
  obtain ⟨δ₂, hδ₂, hδ₂sub⟩ := Metric.isOpen_iff.1 isOpen_ball x hx.1
  by_cases hxz : x = z
  · subst hxz
    have hβ := (obstacleTendstoAtBotStep_holds μ R x t hR hz ht hqc).eventually (eventually_lt_atBot 0)
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hβ
    obtain ⟨ε, hε, hεβ⟩ := hβ
    refine ⟨min (ε / 2) (δ₂ / 2), by positivity, ?_, 0, fun ζ hζ => ?_, fun y hy hyx => ?_⟩
    · exact (closedBall_subset_ball (lt_of_le_of_lt (min_le_right _ _) (by linarith))).trans hδ₂sub
    · exact hv0 ζ (ball_subset_closedBall (hδ₂sub (closedBall_subset_ball
        (lt_of_le_of_lt (min_le_right _ _) (by linarith)) hζ)))
    · refine (hεβ ?_ hyx).le
      exact lt_of_le_of_lt (mem_closedBall.1 hy) (lt_of_le_of_lt (min_le_left _ _) (by linarith))
  · have hlt : obstacle μ R z t x < shiftedLeastSupersolution μ R z t x := hx.2.resolve_left hxz
    set η := (shiftedLeastSupersolution μ R z t x - obstacle μ R z t x) / 3 with hηdef
    have hη : 0 < η := by rw [hηdef]; linarith
    have hβc := continuousOn_obstacle (t := t) greenFunctionBall hR hz hqc
    have hβx : ContinuousAt (obstacle μ R z t) x := by
      refine hβc.continuousAt (mem_of_superset
        ((isOpen_ball.sdiff isClosed_singleton).mem_nhds ⟨hx.1, hxz⟩) ?_)
      exact fun y hy => ⟨ball_subset_closedBall hy.1, hy.2⟩
    have hvx : ContinuousAt (shiftedLeastSupersolution μ R z t) x :=
      hvc.continuousAt (mem_of_superset (isOpen_ball.mem_nhds hx.1) ball_subset_closedBall)
    obtain ⟨δ₁, hδ₁, hδ₁v⟩ := Metric.continuousAt_iff.1 hvx η hη
    obtain ⟨δ₃, hδ₃, hδ₃β⟩ := Metric.continuousAt_iff.1 hβx η hη
    set δ := min (min (δ₁ / 2) (δ₃ / 2)) (δ₂ / 2) with hδdef
    have hδ0 : 0 < δ := by positivity
    have hδ1 : δ < δ₁ := lt_of_le_of_lt ((min_le_left _ _).trans (min_le_left _ _)) (by linarith)
    have hδ3 : δ < δ₃ := lt_of_le_of_lt ((min_le_left _ _).trans (min_le_right _ _)) (by linarith)
    have hδ2 : δ < δ₂ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    refine ⟨δ, hδ0, (closedBall_subset_ball hδ2).trans hδ₂sub,
      shiftedLeastSupersolution μ R z t x - η, fun ζ hζ => ?_, fun y hy _ => ?_⟩
    · have h1 := hδ₁v (lt_of_le_of_lt (mem_closedBall.1 hζ) hδ1)
      rw [Real.dist_eq, abs_lt] at h1
      linarith
    · have h1 := hδ₃β (lt_of_le_of_lt (mem_closedBall.1 hy) hδ3)
      rw [Real.dist_eq, abs_lt] at h1
      linarith

end NonCoincidence

/-! ## Step 2: `ṽ_t` is subharmonic on `Λ_t` -/

/-- **Lemma A.2, Step 2** (lines 3661-3712), given Lemma A.1 (general form). -/
theorem obstacleNonCoincidenceHarmonicStep2_of (hA1 : ObstacleLeastSuperharmonicMajorantGeneral) :
    ObstacleNonCoincidenceHarmonicStep2 := by
  intro μ hμ R βm βp hR hV z hz t ht
  obtain ⟨-, hvc, hvS, -, heq⟩ := hA1 μ hμ R βm βp hR hV z hz t ht
  set v := shiftedLeastSupersolution μ R z t with hvdef
  have hopen := isOpen_nonCoincidenceSet_of hA1 hμ hR hV hz ht
  have hΛsub : nonCoincidenceSet μ R z t ⊆ ball 0 R := fun x hx => hx.1
  have hvsh : IsSuperharmonicOn (ball 0 R) v :=
    superharmonicOfLaplacianLEStep_holds _ v isOpen_ball (hvc.mono ball_subset_closedBall) hvS.2.1
  have hvF : v ∈ superharmonicMajorants μ R z t := ⟨hvsh, hvS.2.2⟩
  obtain ⟨hfle, -, -⟩ := lscLeastMajorant_facts greenFunctionBall greenPotentialBallContinuousStep_holds hμ hR
    hV hz ht hvF
  have hvle : ∀ g ∈ superharmonicMajorants μ R z t, ∀ x ∈ closedBall (0 : ℂ) R, v x ≤ g x := by
    intro g hg x hx
    rw [heq hx]
    exact hfle g hg x hx
  have hvci : ∀ {x : ℂ} {r : ℝ}, 0 < r → closedBall x r ⊆ ball 0 R → CircleIntegrable v x r :=
    fun hr hsub => (hvc.mono ((sphere_subset_closedBall.trans hsub).trans ball_subset_closedBall)).circleIntegrable
      hr.le
  have hloc : ∀ x ∈ nonCoincidenceSet μ R z t, ∃ r₀ > 0, ∀ r ∈ Ioo 0 r₀,
      CircleIntegrable (-v) x r ∧ Real.circleAverage (-v) x r ≤ (-v) x := by
    intro x hx
    obtain ⟨δ, hδ, hsub, L, hL, hβL⟩ := exists_closedBall_obstacle_le_of_mem hA1 hμ hR hV hz ht hx
    refine ⟨δ, hδ, fun r hr => ?_⟩
    have hrδ : closedBall x r ⊆ closedBall x δ := closedBall_subset_closedBall hr.2.le
    have hrsub : closedBall x r ⊆ ball 0 R := hrδ.trans hsub
    have hvi : CircleIntegrable v x r := hvci hr.1 hrsub
    obtain ⟨hgsh, -⟩ := isSuperharmonicOn_poissonModification isOpen_ball hvsh hr.1 hrsub
    have hgF : poissonModification v x r ∈ superharmonicMajorants μ R z t := by
      refine ⟨hgsh, fun y hy hyz => ?_⟩
      by_cases hyb : y ∈ ball x r
      · rw [poissonModification_of_mem hyb]
        exact (hβL y (hrδ (ball_subset_closedBall hyb)) hyz).trans
          (le_discPoissonIntegral hvi hyb fun ζ hζ => hL ζ (hrδ (sphere_subset_closedBall hζ)))
      · rw [poissonModification_of_notMem hyb]
        exact hvS.2.2 y hy hyz
    have h1 := hvle _ hgF x (ball_subset_closedBall (hsub (mem_closedBall_self hδ.le)))
    rw [poissonModification_of_mem (mem_ball_self hr.1), discPoissonIntegral_center hr.1.ne'] at h1
    refine ⟨hvi.neg, ?_⟩
    rw [circleAverage_neg_fun, Pi.neg_apply]
    linarith
  unfold IsSubharmonicOn
  refine ⟨(hvc.mono (hΛsub.trans ball_subset_closedBall)).neg.lowerSemicontinuousOn, fun x hx r hr hsub => ?_⟩
  have hvi : CircleIntegrable (-v) x r := (hvci hr (hsub.trans hΛsub)).neg
  exact ⟨hvi, circleAverage_le_of_localSuperMean
    (hvc.mono (hΛsub.trans ball_subset_closedBall)).neg.lowerSemicontinuousOn hloc hr hsub hvi⟩

/-! ## Step 3: no component of `Λ_t` away from the pole -/

/-- **Lemma A.2, Step 3** (lines 3714-3716), given Lemma A.1 (general form) and the superharmonicity of `q_{B_R}`
(property 2 of `q_{B_R}`, line 3539). -/
theorem obstacleNonCoincidenceHarmonicStep3_of (hA1 : ObstacleLeastSuperharmonicMajorantGeneral)
    (hqsh : ∀ μ : Measure ℂ, IsLocallyFiniteMeasure μ → ∀ R βm βp : ℝ, 0 < R → VolumeGrowth μ R βm βp →
      IsSuperharmonicOn (ball 0 R) (greenPotentialBall μ R)) :
    ObstacleNonCoincidenceHarmonicStep3 := by
  intro μ hμ R βm βp hR hV z hz t ht W hWo hWΛ hzW hfr
  obtain ⟨-, hvc, -, -, -⟩ := hA1 μ hμ R βm βp hR hV z hz t ht
  set v := shiftedLeastSupersolution μ R z t with hvdef
  set β := obstacle μ R z t with hβdef
  set q := greenPotentialBall μ R with hqdef
  set G := greenFunction (ball (0 : ℂ) R) z with hGdef
  have hqc : ContinuousOn q (closedBall 0 R) := greenPotentialBallContinuousStep_holds μ hμ R βm βp hR hV
  have hqsh' := hqsh μ hμ R βm βp hR hV
  have hqLE : LaplacianLE q 0 (ball 0 R) :=
    laplacianLEOfSuperharmonicStep_holds _ q isOpen_ball (hqc.mono ball_subset_closedBall) hqsh'
  have hqS : q ∈ shiftedSupersolutions μ R z t := greenPotentialBall_mem_shiftedSupersolutions ht.le hqc hqLE
  have hβc : ContinuousOn β (closedBall 0 R \ {z}) := continuousOn_obstacle (t := t) greenFunctionBall hR hz hqc
  have h2 := obstacleNonCoincidenceHarmonicStep2_of hA1 μ hμ R βm βp hR hV z hz t ht
  have hWball : W ⊆ ball 0 R := fun x hx => (hWΛ hx).1
  have hclW : closure W ⊆ closedBall 0 R :=
    closure_minimal (hWball.trans ball_subset_closedBall) isClosed_closedBall
  have hclWz : closure W ⊆ closedBall 0 R \ {z} := fun x hx => ⟨hclW hx, fun h => hzW (h ▸ hx)⟩
  refine eq_empty_of_pos_of_subMean (f := fun x => v x - β x) (isBounded_ball.subset hWball)
    ((hvc.mono hclW).sub (hβc.mono hclWz)) (fun x hx => ?_) (fun x hx => ?_) (fun x hx => ?_)
  · have hxz : x ≠ z := fun h => hzW (h ▸ subset_closure hx)
    have := (hWΛ hx).2.resolve_left hxz
    show 0 < v x - β x
    linarith
  · have hxcl : x ∈ closure W := frontier_subset_closure hx
    have hxz : x ≠ z := (hclWz hxcl).2
    have hxΛ : x ∉ nonCoincidenceSet μ R z t := fun h => Set.disjoint_left.1 hfr hx h
    show v x - β x ≤ 0
    by_cases hxb : x ∈ ball (0 : ℂ) R
    · have : ¬ (β x < v x) := fun h => hxΛ ⟨hxb, Or.inr h⟩
      linarith [not_lt.1 this]
    · have hβ0 : β x = 0 := obstacle_eq_zero_of_notMem hxb
      have hvq : v x ≤ q x := shiftedLeastSupersolution_le hqS (hclW hxcl) hxz
      have hq0 : q x = 0 := greenPotentialBall_eq_zero_of_notMem hxb
      linarith
  · obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.1 hWo x hx
    have hρ : 0 < r / 2 := half_pos hr
    have hsubW : closedBall x (r / 2) ⊆ W := (closedBall_subset_ball (half_lt_self hr)).trans hrsub
    refine ⟨r / 2, hρ, hsubW, ?_⟩
    have hsubΛ : closedBall x (r / 2) ⊆ nonCoincidenceSet μ R z t := hsubW.trans hWΛ
    have hsubB : closedBall x (r / 2) ⊆ ball 0 R := hsubW.trans hWball
    have hsubz : closedBall x (r / 2) ⊆ ball 0 R \ {z} := fun y hy =>
      ⟨hsubB hy, fun h => hzW (h ▸ subset_closure (hsubW hy))⟩
    have hsph : sphere x (r / 2) ⊆ closedBall x (r / 2) := sphere_subset_closedBall
    have hvi : CircleIntegrable v x (r / 2) :=
      (hvc.mono ((hsph.trans hsubB).trans ball_subset_closedBall)).circleIntegrable hρ.le
    have hGi : CircleIntegrable G x (r / 2) :=
      ((continuousOn_greenFunction_ball hz).mono fun y hy => (hsubz (hsph hy)).2).circleIntegrable hρ.le
    have hqi : CircleIntegrable q x (r / 2) :=
      (hqc.mono ((hsph.trans hsubB).trans ball_subset_closedBall)).circleIntegrable hρ.le
    have hβi : CircleIntegrable β x (r / 2) :=
      (hβc.mono fun y hy => ⟨ball_subset_closedBall (hsubz (hsph hy)).1, (hsubz (hsph hy)).2⟩).circleIntegrable
        hρ.le
    have hvsub : v x ≤ Real.circleAverage v x (r / 2) := by
      have := (h2.2 x (hsubΛ (mem_closedBall_self hρ.le)) (r / 2) hρ hsubΛ).2
      rw [circleAverage_neg_fun, Pi.neg_apply] at this
      linarith
    have hGeq : Real.circleAverage G x (r / 2) = G x :=
      InnerProductSpace.HarmonicOnNhd.circleAverage_eq
        ((harmonicOnNhd_greenFunction_ball hz).mono (by rw [abs_of_pos hρ]; exact hsubz))
    have hqsup : Real.circleAverage q x (r / 2) ≤ q x :=
      (hqsh'.2 x (hsubB (mem_closedBall_self hρ.le)) (r / 2) hρ hsubB).2
    have hβfun : β = fun y => (-t) • G y + q y := by
      funext y
      simp only [hβdef, obstacle, hGdef, hqdef, smul_eq_mul]
    have hGi' : CircleIntegrable (fun y => (-t) • G y) x (r / 2) := hGi.const_smul
    have hβavg : Real.circleAverage β x (r / 2) = -t * G x + Real.circleAverage q x (r / 2) := by
      rw [hβfun, Real.circleAverage_fun_add hGi' hqi, Real.circleAverage_fun_smul, hGeq, smul_eq_mul]
    have hβx : β x = -t * G x + q x := by simp only [hβdef, obstacle, hGdef, hqdef]
    show v x - β x ≤ Real.circleAverage (fun y => v y - β y) x (r / 2)
    rw [Real.circleAverage_fun_sub hvi hβi]
    linarith

/-! ## Superharmonicity of `q_{B_R}` (property 2 of `q_{B_R}`, line 3539) -/

section GreenPotential

open ComplexConjugate

/-- Off the pole, `G_{B_R}(y,·) = N(y,·) - h_y` on `B_R` (`h_y = greatestHarmonicMinorantBall R y`). -/
theorem greenFunction_ball_eq_sub {R : ℝ} {y w : ℂ} (hy : y ∈ ball (0 : ℂ) R) (hw : w ∈ ball (0 : ℂ) R)
    (hyw : y ≠ w) :
    greenFunction (ball 0 R) y w = newtonKernel y w - greatestHarmonicMinorantBall R y w := by
  have hR : 0 < R := (norm_nonneg y).trans_lt (mem_ball_zero_iff.1 hy)
  rw [greenFunction_ball hy hw hyw, ← newtonKernel_sub_greenBall hR hyw
    (norm_sub_conj_mul_pos hR (mem_ball_zero_iff.1 hy) (mem_ball_zero_iff.1 hw).le).ne']
  ring

/-- Circle averages of the Newtonian kernel: `M(N(y,·); x, r) ≤ -(2π)⁻¹ log r`, and `≤ N(y,x)` for `y ≠ x`
(Jensen's formula for a pole inside the circle, the mean value property otherwise). -/
theorem circleAverage_newtonKernel_le {x y : ℂ} {r : ℝ} (hr : 0 < r) :
    Real.circleAverage (newtonKernel y) x r ≤ -(2 * Real.pi)⁻¹ * Real.log r ∧
      (y ≠ x → Real.circleAverage (newtonKernel y) x r ≤ newtonKernel y x) := by
  have hπ : 0 < (2 * Real.pi)⁻¹ := by positivity
  by_cases hyx : ‖y - x‖ ≤ r
  · rw [circleAverage_newtonKernel hr hyx]
    refine ⟨le_rfl, fun hne => ?_⟩
    have hpos : 0 < ‖y - x‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
    have := Real.log_le_log hpos hyx
    rw [newtonKernel]
    nlinarith
  · rw [not_le] at hyx
    have hharm : InnerProductSpace.HarmonicOnNhd (newtonKernel y) (closedBall x |r|) := by
      intro w hw
      refine harmonicAt_newtonKernel fun hwy => ?_
      rw [hwy, mem_closedBall, abs_of_pos hr, dist_eq_norm] at hw
      linarith
    rw [InnerProductSpace.HarmonicOnNhd.circleAverage_eq hharm]
    refine ⟨?_, fun _ => le_rfl⟩
    have := Real.log_le_log hr hyx.le
    rw [newtonKernel]
    nlinarith

/-- **Circle averages of `G_{B_R}(y,·)`** over a circle in `B_R`, for a pole `y ∈ B_R`: circle integrable, bounded by
`-(2π)⁻¹ log r - h_y(x)`, and the super-mean-value inequality `M(G(y,·); x, r) ≤ G(y,x)` for `y ≠ x`. -/
theorem circleAverage_greenFunction_ball_le {R : ℝ} {x y : ℂ} {r : ℝ} (hr : 0 < r) (hy : y ∈ ball (0 : ℂ) R)
    (hsub : closedBall x r ⊆ ball 0 R) :
    CircleIntegrable (greenFunction (ball 0 R) y) x r ∧
      Real.circleAverage (greenFunction (ball 0 R) y) x r ≤
        -(2 * Real.pi)⁻¹ * Real.log r - greatestHarmonicMinorantBall R y x ∧
      (y ≠ x → Real.circleAverage (greenFunction (ball 0 R) y) x r ≤ greenFunction (ball 0 R) y x) := by
  have hR : 0 < R := (norm_nonneg y).trans_lt (mem_ball_zero_iff.1 hy)
  have hsph : sphere x |r| ⊆ ball 0 R := by
    rw [abs_of_pos hr]
    exact sphere_subset_closedBall.trans hsub
  have hharm : InnerProductSpace.HarmonicOnNhd (greatestHarmonicMinorantBall R y) (closedBall x |r|) := by
    intro w hw
    rw [abs_of_pos hr] at hw
    exact harmonicAt_greatestHarmonicMinorantBall (norm_pos_iff.1 (norm_sub_conj_mul_pos hR
      (mem_ball_zero_iff.1 hy) (mem_ball_zero_iff.1 (hsub hw)).le))
  have hcae : greenFunction (ball 0 R) y =ᶠ[codiscreteWithin (sphere x |r|)]
      fun w => newtonKernel y w - greatestHarmonicMinorantBall R y w := by
    show {w | greenFunction (ball 0 R) y w = newtonKernel y w - greatestHarmonicMinorantBall R y w} ∈ _
    rw [mem_codiscreteWithin]
    intro p _
    rw [disjoint_principal_right]
    have hy' : ({y} : Set ℂ)ᶜ ∈ 𝓝[≠] p := by
      by_cases hp : p = y
      · rw [hp]
        exact self_mem_nhdsWithin
      · exact mem_nhdsWithin_of_mem_nhds (isOpen_compl_singleton.mem_nhds hp)
    refine mem_of_superset hy' fun w hw hwS => hwS.2 ?_
    exact greenFunction_ball_eq_sub hy (hsph hwS.1) (Ne.symm hw)
  have hNi : CircleIntegrable (newtonKernel y) x r := by
    have h := (circleIntegrable_log_norm_sub_const (a := y) (c := x) r).const_smul (a := -(2 * Real.pi)⁻¹)
    refine (circleIntegrable_congr (fun w _ => ?_)).1 h
    simp [newtonKernel, norm_sub_rev, smul_eq_mul]
  have hhi : CircleIntegrable (greatestHarmonicMinorantBall R y) x r :=
    ContinuousOn.circleIntegrable' fun w hw =>
      (hharm w (sphere_subset_closedBall hw)).1.continuousAt.continuousWithinAt
  have hGi : CircleIntegrable (greenFunction (ball 0 R) y) x r :=
    (circleIntegrable_congr_codiscreteWithin hcae).2 (hNi.sub hhi)
  have havg : Real.circleAverage (greenFunction (ball 0 R) y) x r =
      Real.circleAverage (newtonKernel y) x r - greatestHarmonicMinorantBall R y x := by
    rw [Real.circleAverage_congr_codiscreteWithin hcae hr.ne', Real.circleAverage_fun_sub hNi hhi,
      InnerProductSpace.HarmonicOnNhd.circleAverage_eq hharm]
  obtain ⟨hN1, hN2⟩ := circleAverage_newtonKernel_le (x := x) (y := y) hr
  refine ⟨hGi, by rw [havg]; linarith, fun hyx => ?_⟩
  rw [havg, greenFunction_ball_eq_sub hy (hsub (mem_closedBall_self hr.le)) hyx]
  linarith [hN2 hyx]

/-- Under the volume growth condition, `μ` has no atoms in `B_R`. -/
theorem VolumeGrowth.measure_singleton {μ : Measure ℂ} {R βm βp : ℝ} (hV : VolumeGrowth μ R βm βp) {x : ℂ}
    (hx : x ∈ ball (0 : ℂ) R) : μ {x} = 0 := by
  obtain ⟨-, hβ, r₀, hr₀, hgr⟩ := hV
  have hle : ∀ᶠ r in 𝓝[>] (0 : ℝ), μ {x} ≤ ENNReal.ofReal (r ^ βp) := by
    filter_upwards [Ioo_mem_nhdsGT hr₀] with r hr
    exact (measure_mono (singleton_subset_iff.2 (mem_ball_self hr.1))).trans (hgr r hr.1 hr.2 x hx).2
  have ht : Tendsto (fun r : ℝ => ENNReal.ofReal (r ^ βp)) (𝓝[>] 0) (𝓝 0) := by
    have h0 : Tendsto (fun r : ℝ => r ^ βp) (𝓝 0) (𝓝 0) := by
      have := (Real.continuousAt_rpow_const 0 βp (Or.inr hβ.le)).tendsto
      rwa [Real.zero_rpow hβ.ne'] at this
    simpa using ENNReal.tendsto_ofReal (h0.mono_left nhdsWithin_le_nhds)
  exact le_antisymm (ge_of_tendsto ht hle) zero_le

/-- **`q_{B_R}` is superharmonic in `B_R`** (property 2 of `q_{B_R}`, line 3539; AG01 Thm 4.3.8 gives
`Δ q_{B_R} = -μ`, of which only `Δ q_{B_R} ≤ 0` is used in Appendix A). The super-mean-value inequality
`M(q; x, r) ≤ q(x)` follows from that of `G_{B_R}(y,·)` for `y ≠ x` (`μ` has no atoms) by Fubini; the circle
averages of `G_{B_R}(y,·)` are bounded uniformly in `y ∈ B_R`. -/
theorem isSuperharmonicOn_greenPotentialBall {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) :
    IsSuperharmonicOn (ball 0 R) (greenPotentialBall μ R) := by
  classical
  have := hμ
  have hqc := greenPotentialBallContinuousStep_holds μ hμ R βm βp hR hV
  refine ⟨(hqc.mono ball_subset_closedBall).lowerSemicontinuousOn, fun x hx r hr hsub => ?_⟩
  have hqi : CircleIntegrable (greenPotentialBall μ R) x r :=
    (hqc.mono ((sphere_subset_closedBall.trans hsub).trans ball_subset_closedBall)).circleIntegrable hr.le
  refine ⟨hqi, ?_⟩
  set ν := μ.restrict (ball (0 : ℂ) R) with hνdef
  have : IsFiniteMeasure ν := isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  set G : ℂ → ℂ → ℝ := fun y w => greenFunction (ball (0 : ℂ) R) y w with hGdef
  set F : ℝ → ℂ → ℝ := fun θ y => G y (circleMap x r θ) with hFdef
  set I := Ioc (0 : ℝ) (2 * Real.pi) with hIdef
  have h2π : 0 < 2 * Real.pi := Real.two_pi_pos
  -- joint measurability of the Green function
  have hGm : Measurable (fun p : ℂ × ℂ => G p.1 p.2) := by
    have heq : (fun p : ℂ × ℂ => G p.1 p.2) = fun p =>
        if p.1 ∈ ball (0 : ℂ) R ∧ p.2 ∈ ball (0 : ℂ) R ∧ p.1 ≠ p.2 then greenBall R p.1 p.2 else 0 := by
      funext p
      split_ifs with h
      · exact greenFunction_ball h.1 h.2.1 h.2.2
      · show greenFunction (ball 0 R) p.1 p.2 = 0
        rw [greenFunction, ite_eq_right_iff]
        exact fun hc => absurd hc h
    rw [heq]
    refine Measurable.ite ?_ ?_ measurable_const
    · exact (measurableSet_ball.preimage measurable_fst).inter
        ((measurableSet_ball.preimage measurable_snd).inter isClosed_diagonal.measurableSet.compl)
    · unfold greenBall
      fun_prop
  have hFm : Measurable (Function.uncurry F) :=
    hGm.comp (measurable_snd.prodMk ((continuous_circleMap x r).measurable.comp measurable_fst))
  have hG0 : ∀ y w, 0 ≤ G y w := fun y w => greenFunction_nonneg isBounded_ball y w
  -- uniform bound on the circle averages
  set C := -(2 * Real.pi)⁻¹ * Real.log r + (2 * Real.pi)⁻¹ * (Real.log (2 * R ^ 2) - Real.log R) with hCdef
  have hbd : ∀ y ∈ ball (0 : ℂ) R, Real.circleAverage (G y) x r ≤ C := by
    intro y hy
    have h := (circleAverage_greenFunction_ball_le hr hy hsub).2.1
    have hx' : ‖x‖ < R := mem_ball_zero_iff.1 hx
    have hy' : ‖y‖ < R := mem_ball_zero_iff.1 hy
    have hpos := norm_sub_conj_mul_pos hR hy' hx'.le
    have hle : ‖(R : ℂ) ^ 2 - conj y * x‖ ≤ 2 * R ^ 2 := by
      calc ‖(R : ℂ) ^ 2 - conj y * x‖ ≤ ‖(R : ℂ) ^ 2‖ + ‖conj y * x‖ := norm_sub_le _ _
        _ = R ^ 2 + ‖y‖ * ‖x‖ := by
          rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR, norm_mul, Complex.norm_conj]
        _ ≤ 2 * R ^ 2 := by nlinarith [norm_nonneg x, norm_nonneg y]
    have hlog := Real.log_le_log hpos hle
    have hπ : 0 < (2 * Real.pi)⁻¹ := by positivity
    simp only [greatestHarmonicMinorantBall] at h
    rw [hCdef]
    nlinarith
  -- the inner integrals
  have hFint : ∀ y ∈ ball (0 : ℂ) R, ∫ θ in I, F θ y = 2 * Real.pi * Real.circleAverage (G y) x r := by
    intro y _
    rw [Real.circleAverage_def, smul_eq_mul, hIdef, ← intervalIntegral.integral_of_le h2π.le]
    field_simp
    rfl
  have hFiθ : ∀ y ∈ ball (0 : ℂ) R, Integrable (fun θ => F θ y) (volume.restrict I) := by
    intro y hy
    have h := (circleAverage_greenFunction_ball_le hr hy hsub).1
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le h2π.le).1 h
  have hmem : ∀ᵐ y ∂ν, y ∈ ball (0 : ℂ) R := ae_restrict_mem measurableSet_ball
  have hFint_nonneg : ∀ y, 0 ≤ ∫ θ in I, F θ y := fun y => integral_nonneg fun θ => hG0 _ _
  have hprod : Integrable (Function.uncurry F) ((volume.restrict I).prod ν) := by
    refine (integrable_prod_iff' hFm.aestronglyMeasurable).2 ⟨?_, ?_⟩
    · filter_upwards [hmem] with y hy using hFiθ y hy
    · refine Integrable.of_bound
        ((hFm.norm.stronglyMeasurable.integral_prod_left' (μ := volume.restrict I)).aestronglyMeasurable)
        (2 * Real.pi * max C 0) ?_
      filter_upwards [hmem] with y hy
      have hn : (fun θ => ‖F θ y‖) = fun θ => F θ y := funext fun θ => Real.norm_of_nonneg (hG0 _ _)
      show ‖∫ θ, ‖Function.uncurry F (θ, y)‖ ∂(volume.restrict I)‖ ≤ 2 * Real.pi * max C 0
      simp only [Function.uncurry_apply_pair]
      rw [hn, Real.norm_of_nonneg (hFint_nonneg y), hFint y hy]
      exact mul_le_mul_of_nonneg_left ((hbd y hy).trans (le_max_left _ _)) h2π.le
  -- Fubini
  have hcA : Real.circleAverage (greenPotentialBall μ R) x r =
      (2 * Real.pi)⁻¹ * ∫ y, (∫ θ in I, F θ y) ∂ν := by
    rw [Real.circleAverage_def, smul_eq_mul, intervalIntegral.integral_of_le h2π.le, ← hIdef,
      ← integral_integral_swap hprod]
    rfl
  have hGxi : Integrable (fun y => G y x) ν := by
    obtain ⟨hI, -⟩ := greenPotential_ball_holderOnWith hR hV (memLp_top_const (1 : ℝ))
    refine ((hI x (ball_subset_closedBall hx)).congr ?_)
    filter_upwards with y
    simp only [mul_one, hGdef]
    exact greenFunction_ball_comm R x y
  have hmono : ∫ y, (∫ θ in I, F θ y) ∂ν ≤ ∫ y, 2 * Real.pi * G y x ∂ν := by
    refine integral_mono_ae hprod.integral_prod_right (hGxi.const_mul _) ?_
    have hne : ∀ᵐ y ∂ν, y ≠ x := by
      have h0 : ν {x} = 0 :=
        le_antisymm ((Measure.restrict_apply_le _ _).trans_eq (hV.measure_singleton hx)) zero_le
      rw [ae_iff]
      simpa using h0
    filter_upwards [hmem, hne] with y hy hyx
    rw [hFint y hy]
    exact mul_le_mul_of_nonneg_left ((circleAverage_greenFunction_ball_le hr hy hsub).2.2 hyx) h2π.le
  rw [hcA]
  calc (2 * Real.pi)⁻¹ * ∫ y, (∫ θ in I, F θ y) ∂ν ≤ (2 * Real.pi)⁻¹ * ∫ y, 2 * Real.pi * G y x ∂ν :=
        mul_le_mul_of_nonneg_left hmono (by positivity)
    _ = greenPotentialBall μ R x := by
      rw [integral_const_mul]
      field_simp
      rfl

end GreenPotential

/-! ## Lemma A.1 (general form) without `GreenPotentialBallLaplacianStep` -/

/-- **Lemma A.1, general radius and pole**, proved: the reduction `obstacleLeastSuperharmonicMajorantGeneral_of_steps`
uses `GreenPotentialBallLaplacianStep` only through `Δ q_{B_R} ≤ 0`, which follows from
`isSuperharmonicOn_greenPotentialBall` and the converse of Weyl's lemma. -/
theorem obstacleLeastSuperharmonicMajorantGeneral_holds : ObstacleLeastSuperharmonicMajorantGeneral := by
  intro μ hμ R βm βp hR hV z hz t ht
  have hW := superharmonicOfLaplacianLEStep_holds
  have hW' := laplacianLEOfSuperharmonicStep_holds
  have h1 := obstacleLeastSuperharmonicMajorantStep1_holds
  have h2 := obstacleLeastSuperharmonicMajorantStep2_holds
  have h3 := obstacleLeastSuperharmonicMajorantStep3_holds
  have h4 := obstacleLeastSuperharmonicMajorantStep4_holds
  have hqc : ContinuousOn (greenPotentialBall μ R) (closedBall 0 R) :=
    greenPotentialBallContinuousStep_holds μ hμ R βm βp hR hV
  have hqLE : LaplacianLE (greenPotentialBall μ R) 0 (ball 0 R) :=
    hW' _ _ isOpen_ball (hqc.mono ball_subset_closedBall) (isSuperharmonicOn_greenPotentialBall hμ hR hV)
  have hbs : ball (0 : ℂ) R ⊆ closedBall 0 R := ball_subset_closedBall
  have hSA : shiftedSupersolutions μ R z t ⊆ superharmonicMajorants μ R z t := fun w hw =>
    ⟨hW _ w isOpen_ball (hw.1.mono hbs) hw.2.1, hw.2.2⟩
  have hqS : greenPotentialBall μ R ∈ shiftedSupersolutions μ R z t :=
    greenPotentialBall_mem_shiftedSupersolutions ht.le hqc hqLE
  have hqA := hSA hqS
  have hg0 := h1 μ hμ R βm βp hR hV z hz t ht
  have hbdd : ∀ x ∈ closedBall (0 : ℂ) R,
      BddBelow ((fun g : ℂ → ℝ => g x) '' superharmonicMajorants μ R z t) := fun x hx =>
    ⟨0, by rintro _ ⟨g, hg, rfl⟩; exact hg0 g hg x hx⟩
  have hne : ∀ x, ((fun g : ℂ → ℝ => g x) '' superharmonicMajorants μ R z t).Nonempty := fun x =>
    ⟨_, _, hqA, rfl⟩
  have hf_le : ∀ g ∈ superharmonicMajorants μ R z t, ∀ x ∈ closedBall (0 : ℂ) R,
      lscLeastMajorant μ R z t x ≤ g x := fun g hg x hx => csInf_le (hbdd x hx) ⟨g, hg, rfl⟩
  have hf_nonneg : ∀ x ∈ closedBall (0 : ℂ) R, 0 ≤ lscLeastMajorant μ R z t x := fun x hx =>
    le_csInf (hne x) (by rintro _ ⟨g, hg, rfl⟩; exact hg0 g hg x hx)
  have hf_obs : ∀ x ∈ closedBall (0 : ℂ) R, x ≠ z → obstacle μ R z t x ≤ lscLeastMajorant μ R z t x :=
    fun x hx hxz => le_csInf (hne x) (by rintro _ ⟨g, hg, rfl⟩; exact hg.2 x hx hxz)
  have hf2 := h2 μ hμ R βm βp hR hV z hz t ht
  have hfc : ContinuousOn (lscLeastMajorant μ R z t) (closedBall 0 R) := by
    intro x hx
    by_cases hxb : x ∈ ball (0 : ℂ) R
    · have hlsc : LowerSemicontinuousAt (lscLeastMajorant μ R z t) x :=
        fun y hy => by
          have := hf2.1 x hxb y hy
          rwa [nhdsWithin_eq_nhds.2 (isOpen_ball.mem_nhds hxb)] at this
      have husc : UpperSemicontinuousAt (lscLeastMajorant μ R z t) x := by
        by_cases hxz : x = z
        · subst hxz; exact h4 μ hμ R βm βp hR hV x hz t ht
        · exact h3 μ hμ R βm βp hR hV z hz t ht x hxb hxz
      exact (continuousAt_iff_lower_upperSemicontinuousAt.2 ⟨hlsc, husc⟩).continuousWithinAt
    · have hqx : greenPotentialBall μ R x = 0 := greenPotentialBall_eq_zero_of_notMem hxb
      have hfx : lscLeastMajorant μ R z t x = 0 :=
        le_antisymm (hqx ▸ hf_le _ hqA x hx) (hf_nonneg x hx)
      have hqt : Tendsto (greenPotentialBall μ R) (𝓝[closedBall 0 R] x) (𝓝 0) := by
        have := hqc x hx
        rwa [ContinuousWithinAt, hqx] at this
      rw [ContinuousWithinAt, hfx]
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hqt ?_ ?_
      · filter_upwards [self_mem_nhdsWithin] with y hy using hf_nonneg y hy
      · filter_upwards [self_mem_nhdsWithin] with y hy using hf_le _ hqA y hy
  have hfS : lscLeastMajorant μ R z t ∈ shiftedSupersolutions μ R z t :=
    ⟨hfc, hW' _ _ isOpen_ball (hfc.mono hbs) hf2, hf_obs⟩
  have hS_bdd : ∀ x ∈ closedBall (0 : ℂ) R,
      BddBelow ((fun w : ℂ → ℝ => w x) '' shiftedSupersolutions μ R z t) := fun x hx =>
    (hbdd x hx).mono (image_mono hSA)
  have heq : EqOn (shiftedLeastSupersolution μ R z t) (lscLeastMajorant μ R z t) (closedBall 0 R) := by
    intro x hx
    apply le_antisymm
    · exact csInf_le (hS_bdd x hx) ⟨_, hfS, rfl⟩
    · exact csInf_le_csInf (hbdd x hx) ⟨_, _, hfS, rfl⟩ (image_mono hSA)
  refine ⟨hS_bdd, hfc.congr heq, ⟨hfc.congr heq, ?_, ?_⟩, fun x hx => (heq hx).symm ▸ hf_nonneg x hx, heq⟩
  · exact hfS.2.1.congr_eqOn measurableSet_ball fun x hx => (heq (hbs hx)).symm
  · intro x hx hxz
    rw [heq hx]
    exact hf_obs x hx hxz

/-- **Lemma A.1** (lemma:appendix-basic-properties, line 3589) as printed (`R = 1`, pole `0`). -/
theorem obstacleLeastSuperharmonicMajorant_holds : ObstacleLeastSuperharmonicMajorantStmt :=
  obstacleLeastSuperharmonicMajorant_of_general obstacleLeastSuperharmonicMajorantGeneral_holds

/-! ## Lemma A.2 -/

/-- **Lemma A.2, Step 2.** -/
theorem obstacleNonCoincidenceHarmonicStep2_holds : ObstacleNonCoincidenceHarmonicStep2 :=
  obstacleNonCoincidenceHarmonicStep2_of obstacleLeastSuperharmonicMajorantGeneral_holds

/-- **Lemma A.2, Step 3.** -/
theorem obstacleNonCoincidenceHarmonicStep3_holds : ObstacleNonCoincidenceHarmonicStep3 :=
  obstacleNonCoincidenceHarmonicStep3_of obstacleLeastSuperharmonicMajorantGeneral_holds
    fun _ hμ _ _ _ hR hV => isSuperharmonicOn_greenPotentialBall hμ hR hV

/-- **Lemma A.2, general radius and pole.** -/
theorem obstacleNonCoincidenceHarmonicGeneral_holds : ObstacleNonCoincidenceHarmonicGeneral :=
  obstacleNonCoincidenceHarmonicGeneral_of_steps obstacleLeastSuperharmonicMajorantGeneral_holds greenFunctionBall
    laplacianLEOfSuperharmonicStep_holds hasLaplacianOfLaplacianLEGEStep_holds greenPotentialBallContinuousStep_holds
    obstacleTendstoAtBotStep_holds obstacleNonCoincidenceHarmonicStep2_holds obstacleNonCoincidenceHarmonicStep3_holds

/-- **Lemma A.2** (lemma:appendix-non-coincedence-open-harmonic, line 3652) as printed (`R = 1`, pole `0`). -/
theorem obstacleNonCoincidenceHarmonic_holds : ObstacleNonCoincidenceHarmonicStmt :=
  obstacleNonCoincidenceHarmonic_of_general obstacleNonCoincidenceHarmonicGeneral_holds

end HarmonicBalls

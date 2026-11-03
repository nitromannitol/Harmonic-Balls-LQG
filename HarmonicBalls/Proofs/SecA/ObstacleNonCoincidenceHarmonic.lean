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

end HarmonicBalls

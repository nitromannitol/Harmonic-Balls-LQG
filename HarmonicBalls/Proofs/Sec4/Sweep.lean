import HarmonicBalls.Proofs.Potential.DiscPoisson
import HarmonicBalls.Defs.Green

/-!
# Sweeping: iterated Poisson modification and the greatest harmonic minorant

Generic potential theory in the plane for Lemma 4.3 (lemma:harmonic-ball) of Bou-Rabee and Gwynne, *Harmonic balls
in Liouville quantum gravity* (arXiv:2208.11795): the greatest harmonic minorant on a general open set `O`
(Armitage–Gardiner, *Classical potential theory*, §3.6) is obtained by *sweeping*.

* `discSweep O c ρ f`: the Poisson modification of `f` on the disc `B_ρ(c)` (when `closedBall c ρ ⊆ O`): `f` is
  replaced in `B_ρ(c)` by the Poisson integral of its values on `∂B_ρ(c)`.
* `sweep O f k`: `k` successive Poisson modifications over an enumeration of the rational discs of `O`, each disc
  being visited infinitely often.
* `sweep_limit`: for `f` continuous on `O` with the local super-mean-value property and a harmonic minorant, the
  sweeps decrease to a harmonic function `H ≤ f` above every harmonic minorant of `f`; hence `H = I_O[f]`
  (`greatestHarmonicMinorant_eq_of_sweep_limit`).
* Sweeping is linear (`sweep_add`, `sweep_smul`), monotone (`sweep_mono`), fixes harmonic functions
  (`sweep_harmonic`) and commutes with integration of bounded measurable families (`sweep_integral`).
-/

namespace HarmonicBalls

open Complex Metric Real Filter Topology Set MeasureTheory InnerProductSpace Function

/-- The local super-mean-value property on `U` (as in the hypotheses of `discPoissonIntegral_le`). -/
def HasLocalSuperMean (U : Set ℂ) (u : ℂ → ℝ) : Prop :=
  ∀ x ∈ U, ∃ r₀ > 0, ∀ r ∈ Ioo 0 r₀, CircleIntegrable u x r ∧ Real.circleAverage u x r ≤ u x

/-- A disc admissible for sweeping in `O`: positive radius and closure in `O`. -/
def IsSweepDisc (O : Set ℂ) (c : ℂ) (ρ : ℝ) : Prop :=
  0 < ρ ∧ closedBall c ρ ⊆ O

open Classical in
/-- The **Poisson modification** of `f` on the disc `B_ρ(c)` (identity unless `closedBall c ρ ⊆ O`, `ρ > 0`). -/
noncomputable def discSweep (O : Set ℂ) (c : ℂ) (ρ : ℝ) (f : ℂ → ℝ) (y : ℂ) : ℝ :=
  if IsSweepDisc O c ρ ∧ y ∈ ball c ρ then discPoissonIntegral f c ρ y else f y

section DiscSweep

variable {O : Set ℂ} {c : ℂ} {ρ : ℝ} {f g : ℂ → ℝ} {y : ℂ}

theorem discSweep_of_not (h : ¬(IsSweepDisc O c ρ ∧ y ∈ ball c ρ)) : discSweep O c ρ f y = f y := by
  rw [discSweep, ite_eq_right h]

theorem discSweep_of_mem (hD : IsSweepDisc O c ρ) (hy : y ∈ ball c ρ) :
    discSweep O c ρ f y = discPoissonIntegral f c ρ y := by
  rw [discSweep, ite_eq_left ⟨hD, hy⟩]

theorem IsSweepDisc.sphere_subset (hD : IsSweepDisc O c ρ) : sphere c ρ ⊆ O :=
  sphere_subset_closedBall.trans hD.2

theorem IsSweepDisc.circleIntegrable (hD : IsSweepDisc O c ρ) (hf : ContinuousOn f O) :
    CircleIntegrable f c ρ :=
  (hf.mono hD.sphere_subset).circleIntegrable hD.1.le

/-- Poisson modification fixes harmonic functions. -/
theorem discSweep_harmonic {h : ℂ → ℝ} (hh : HarmonicOnNhd h O) : discSweep O c ρ h = h := by
  funext y
  by_cases H : IsSweepDisc O c ρ ∧ y ∈ ball c ρ
  · rw [discSweep_of_mem H.1 H.2, discPoissonIntegral]
    exact HarmonicOnNhd.circleAverage_poissonKernel_smul (fun x hx => hh x (H.1.2 hx)) H.2
  · exact discSweep_of_not H

theorem discSweep_add (hf : ContinuousOn f O) (hg : ContinuousOn g O) :
    discSweep O c ρ (f + g) = discSweep O c ρ f + discSweep O c ρ g := by
  funext y
  by_cases H : IsSweepDisc O c ρ ∧ y ∈ ball c ρ
  · simp only [Pi.add_apply, discSweep_of_mem H.1 H.2, discPoissonIntegral]
    rw [smul_add, Real.circleAverage_add (CircleIntegrable.poissonKernel_smul (H.1.circleIntegrable hf) H.2)
      (CircleIntegrable.poissonKernel_smul (H.1.circleIntegrable hg) H.2)]
  · simp only [Pi.add_apply, discSweep_of_not H]

theorem discSweep_smul (a : ℝ) : discSweep O c ρ (a • f) = a • discSweep O c ρ f := by
  funext y
  by_cases H : IsSweepDisc O c ρ ∧ y ∈ ball c ρ
  · simp only [Pi.smul_apply, discSweep_of_mem H.1 H.2, discPoissonIntegral]
    rw [smul_comm, Real.circleAverage_smul]
  · simp only [Pi.smul_apply, discSweep_of_not H]

theorem discSweep_mono (hf : ContinuousOn f O) (hg : ContinuousOn g O) (hle : ∀ y ∈ O, f y ≤ g y) :
    ∀ y ∈ O, discSweep O c ρ f y ≤ discSweep O c ρ g y := by
  intro y hy
  by_cases H : IsSweepDisc O c ρ ∧ y ∈ ball c ρ
  · rw [discSweep_of_mem H.1 H.2, discSweep_of_mem H.1 H.2]
    exact discPoissonIntegral_mono (H.1.circleIntegrable hf) (H.1.circleIntegrable hg) H.2
      (fun ζ hζ => hle ζ (H.1.sphere_subset hζ))
  · rw [discSweep_of_not H, discSweep_of_not H]
    exact hle y hy

theorem continuousOn_discSweep (hO : IsOpen O) (hf : ContinuousOn f O) :
    ContinuousOn (discSweep O c ρ f) O := by
  by_cases hD : IsSweepDisc O c ρ
  swap
  · have : discSweep O c ρ f = f := funext fun y => discSweep_of_not (fun h => hD h.1)
    rw [this]
    exact hf
  intro y hy
  refine ContinuousAt.continuousWithinAt ?_
  have hfy : ContinuousAt f y := hf.continuousAt (hO.mem_nhds hy)
  have hout : ∀ w ∉ ball c ρ, discSweep O c ρ f w = f w := fun w hw => discSweep_of_not (fun h => hw h.2)
  by_cases hyb : y ∈ ball c ρ
  · have heq : discSweep O c ρ f =ᶠ[𝓝 y] discPoissonIntegral f c ρ := by
      filter_upwards [isOpen_ball.mem_nhds hyb] with w hw using discSweep_of_mem hD hw
    refine ContinuousAt.congr ?_ heq.symm
    exact (continuousOn_discPoissonIntegral (hD.circleIntegrable hf)).continuousAt (isOpen_ball.mem_nhds hyb)
  · rw [← continuousWithinAt_univ, ← union_compl_self (ball c ρ)]
    refine ContinuousWithinAt.union ?_ ?_
    · by_cases hys : y ∈ sphere c ρ
      · have h1 := tendsto_discPoissonIntegral_of_continuousOn hD.1 (hf.mono hD.sphere_subset) hys
        rw [ContinuousWithinAt, hout y hyb]
        refine h1.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with w hw using (discSweep_of_mem hD hw).symm
      · have hyc : y ∉ closedBall c ρ := fun h => by
          rcases (mem_closedBall.1 h).lt_or_eq with h' | h'
          · exact hyb (mem_ball.2 h')
          · exact hys (mem_sphere.2 h')
        exact continuousWithinAt_of_notMem_closure fun h => hyc (closure_ball_subset_closedBall h)
    · exact (hfy.continuousWithinAt).congr (fun w hw => hout w hw) (hout y hyb)

theorem discSweep_le (hf : ContinuousOn f O) (hm : HasLocalSuperMean O f) :
    ∀ y ∈ O, discSweep O c ρ f y ≤ f y := by
  intro y hy
  by_cases H : IsSweepDisc O c ρ ∧ y ∈ ball c ρ
  · rw [discSweep_of_mem H.1 H.2]
    exact discPoissonIntegral_le hf.lowerSemicontinuousOn hm H.1.1 H.1.2 (H.1.circleIntegrable hf) y H.2
  · rw [discSweep_of_not H]

theorem hasLocalSuperMean_discSweep (hO : IsOpen O) (hf : ContinuousOn f O) (hm : HasLocalSuperMean O f) :
    HasLocalSuperMean O (discSweep O c ρ f) := by
  have hc := continuousOn_discSweep (c := c) (ρ := ρ) hO hf
  have hle := discSweep_le (c := c) (ρ := ρ) hf hm
  intro y hy
  obtain ⟨δ, hδ, hδO⟩ := Metric.isOpen_iff.1 hO y hy
  by_cases H : IsSweepDisc O c ρ ∧ y ∈ ball c ρ
  · have hpos : 0 < ρ - dist y c := sub_pos.2 (mem_ball.1 H.2)
    refine ⟨ρ - dist y c, hpos, fun r hr => ?_⟩
    have hsub : closedBall y |r| ⊆ ball c ρ := by
      intro w hw
      rw [abs_of_pos hr.1] at hw
      rw [mem_ball]
      calc dist w c ≤ dist w y + dist y c := dist_triangle _ _ _
        _ < ρ := by linarith [mem_closedBall.1 hw, hr.2]
    have hsO : sphere y r ⊆ O := fun w hw => H.1.2 (ball_subset_closedBall
      (hsub (by rw [abs_of_pos hr.1]; exact sphere_subset_closedBall hw)))
    refine ⟨(hc.mono hsO).circleIntegrable hr.1.le, le_of_eq ?_⟩
    rw [discSweep_of_mem H.1 H.2, ← circleAverage_discPoissonIntegral (H.1.circleIntegrable hf) hsub]
    refine Real.circleAverage_congr_sphere fun w hw => ?_
    exact discSweep_of_mem H.1 (hsub (sphere_subset_closedBall hw))
  · obtain ⟨r₀, hr₀, hr₀m⟩ := hm y hy
    refine ⟨min r₀ (δ / 2), lt_min hr₀ (half_pos hδ), fun r hr => ?_⟩
    have hr1 : r < r₀ := hr.2.trans_le (min_le_left _ _)
    have hr2 : r < δ := hr.2.trans_le ((min_le_right _ _).trans (half_le_self hδ.le))
    have hsO : sphere y r ⊆ O := fun w hw => hδO (mem_ball.2 ((mem_sphere.1 hw).trans_lt hr2))
    have hsO' : sphere y |r| ⊆ O := by rwa [abs_of_pos hr.1]
    obtain ⟨hfi, hfm⟩ := hr₀m r ⟨hr.1, hr1⟩
    refine ⟨(hc.mono hsO).circleIntegrable hr.1.le, ?_⟩
    rw [discSweep_of_not H]
    exact (Real.circleAverage_mono ((hc.mono hsO).circleIntegrable hr.1.le) hfi
      (fun w hw => hle w (hsO' hw))).trans hfm

end DiscSweep

/-! ## The sweep over the rational discs -/

/-- A surjective enumeration of `ℚ × ℚ × ℚ` (centre `(a, b)`, radius `ρ`). -/
noncomputable def ratDisc : ℕ → ℚ × ℚ × ℚ :=
  Classical.choose (exists_surjective_nat (ℚ × ℚ × ℚ))

theorem ratDisc_surjective : Surjective ratDisc :=
  Classical.choose_spec (exists_surjective_nat (ℚ × ℚ × ℚ))

/-- The centre of the disc used at step `k`: disc number `(unpair k).1`, so that each disc is used infinitely
often. -/
noncomputable def sweepCenter (k : ℕ) : ℂ :=
  ⟨(ratDisc (Nat.unpair k).1).1, (ratDisc (Nat.unpair k).1).2.1⟩

/-- The radius of the disc used at step `k`. -/
noncomputable def sweepRadius (k : ℕ) : ℝ :=
  (ratDisc (Nat.unpair k).1).2.2

/-- The **sweep**: `k` successive Poisson modifications of `f` over the rational discs of `O`. -/
noncomputable def sweep (O : Set ℂ) (f : ℂ → ℝ) : ℕ → ℂ → ℝ
  | 0 => f
  | k + 1 => discSweep O (sweepCenter k) (sweepRadius k) (sweep O f k)

theorem sweep_zero (O : Set ℂ) (f : ℂ → ℝ) : sweep O f 0 = f := rfl

theorem sweep_succ (O : Set ℂ) (f : ℂ → ℝ) (k : ℕ) :
    sweep O f (k + 1) = discSweep O (sweepCenter k) (sweepRadius k) (sweep O f k) := rfl

theorem sweepCenter_pair (n j : ℕ) : sweepCenter (Nat.pair n j) = sweepCenter (Nat.pair n 0) := by
  simp [sweepCenter, Nat.unpair_pair]

theorem sweepRadius_pair (n j : ℕ) : sweepRadius (Nat.pair n j) = sweepRadius (Nat.pair n 0) := by
  simp [sweepRadius, Nat.unpair_pair]

/-- Every point of an open set lies in a rational sweep disc. -/
theorem exists_sweepDisc {O : Set ℂ} (hO : IsOpen O) {y : ℂ} (hy : y ∈ O) :
    ∃ n : ℕ, IsSweepDisc O (sweepCenter (Nat.pair n 0)) (sweepRadius (Nat.pair n 0)) ∧
      y ∈ ball (sweepCenter (Nat.pair n 0)) (sweepRadius (Nat.pair n 0)) := by
  obtain ⟨δ, hδ, hδO⟩ := Metric.isOpen_iff.1 hO y hy
  obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn (show y.re - δ / 8 < y.re + δ / 8 by linarith)
  obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn (show y.im - δ / 8 < y.im + δ / 8 by linarith)
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show δ / 4 < δ / 2 by linarith)
  obtain ⟨n, hn⟩ := ratDisc_surjective (a, b, q)
  refine ⟨n, ?_⟩
  have hc : sweepCenter (Nat.pair n 0) = ⟨a, b⟩ := by simp [sweepCenter, Nat.unpair_pair, hn]
  have hρ : sweepRadius (Nat.pair n 0) = q := by simp [sweepRadius, Nat.unpair_pair, hn]
  rw [hc, hρ]
  have hyc : dist y ⟨a, b⟩ < δ / 4 := by
    rw [dist_eq_norm]
    refine (norm_le_abs_re_add_abs_im _).trans_lt ?_
    simp only [sub_re, sub_im]
    have h1 : |y.re - a| < δ / 8 := abs_lt.2 ⟨by linarith, by linarith⟩
    have h2 : |y.im - b| < δ / 8 := abs_lt.2 ⟨by linarith, by linarith⟩
    linarith
  refine ⟨⟨by linarith, fun w hw => hδO ?_⟩, mem_ball.2 (hyc.trans hq1)⟩
  rw [mem_ball]
  calc dist w y ≤ dist w ⟨a, b⟩ + dist (⟨a, b⟩ : ℂ) y := dist_triangle _ _ _
    _ < δ := by rw [dist_comm (⟨a, b⟩ : ℂ) y]; linarith [mem_closedBall.1 hw]

section Sweep

variable {O : Set ℂ} {f g : ℂ → ℝ}

theorem continuousOn_sweep (hO : IsOpen O) (hf : ContinuousOn f O) (k : ℕ) :
    ContinuousOn (sweep O f k) O := by
  induction k with
  | zero => exact hf
  | succ k ih => exact continuousOn_discSweep hO ih

theorem sweep_invariants (hO : IsOpen O) (hf : ContinuousOn f O) (hm : HasLocalSuperMean O f) (k : ℕ) :
    HasLocalSuperMean O (sweep O f k) ∧ ∀ y ∈ O, sweep O f (k + 1) y ≤ sweep O f k y := by
  induction k with
  | zero => exact ⟨hm, discSweep_le hf hm⟩
  | succ k ih =>
    have hm' := hasLocalSuperMean_discSweep (c := sweepCenter k) (ρ := sweepRadius k) hO
      (continuousOn_sweep hO hf k) ih.1
    exact ⟨hm', discSweep_le (continuousOn_sweep hO hf (k + 1)) hm'⟩

theorem sweep_harmonic {h : ℂ → ℝ} (hh : HarmonicOnNhd h O) (k : ℕ) : sweep O h k = h := by
  induction k with
  | zero => rfl
  | succ k ih => rw [sweep_succ, ih, discSweep_harmonic hh]

theorem sweep_add (hO : IsOpen O) (hf : ContinuousOn f O) (hg : ContinuousOn g O) (k : ℕ) :
    sweep O (f + g) k = sweep O f k + sweep O g k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [sweep_succ, sweep_succ, sweep_succ, ih,
      discSweep_add (continuousOn_sweep hO hf k) (continuousOn_sweep hO hg k)]

theorem sweep_smul (a : ℝ) (k : ℕ) : sweep O (a • f) k = a • sweep O f k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [sweep_succ, sweep_succ, ih, discSweep_smul]

theorem sweep_mono (hO : IsOpen O) (hf : ContinuousOn f O) (hg : ContinuousOn g O)
    (hle : ∀ y ∈ O, f y ≤ g y) (k : ℕ) : ∀ y ∈ O, sweep O f k y ≤ sweep O g k y := by
  induction k with
  | zero => exact hle
  | succ k ih => exact discSweep_mono (continuousOn_sweep hO hf k) (continuousOn_sweep hO hg k) ih

theorem harmonicOnNhd_continuousOn {h : ℂ → ℝ} (hh : HarmonicOnNhd h O) : ContinuousOn h O :=
  fun y hy => (hh y hy).1.continuousAt.continuousWithinAt

/-- **Sweeping converges to the greatest harmonic minorant.** For `f` continuous on the open set `O` with the local
super-mean-value property and a harmonic minorant `h₀`, the sweeps of `f` decrease to a function `H` harmonic on
`O`, `H ≤ f`, which lies above every harmonic minorant of `f` (Armitage–Gardiner Thm 3.6.? via Poisson
modification; the limit is harmonic on each rational disc, being the Poisson integral of its boundary values). -/
theorem sweep_limit (hO : IsOpen O) (hf : ContinuousOn f O) (hm : HasLocalSuperMean O f) {h₀ : ℂ → ℝ}
    (hh₀ : HarmonicOnNhd h₀ O) (hh₀f : ∀ y ∈ O, h₀ y ≤ f y) :
    HarmonicOnNhd (fun y => ⨅ k, sweep O f k y) O ∧ (∀ y ∈ O, (⨅ k, sweep O f k y) ≤ f y) ∧
      (∀ y ∈ O, Tendsto (fun k => sweep O f k y) atTop (𝓝 (⨅ k, sweep O f k y))) ∧
      ∀ h : ℂ → ℝ, HarmonicOnNhd h O → (∀ y ∈ O, h y ≤ f y) → ∀ y ∈ O, h y ≤ ⨅ k, sweep O f k y := by
  set H : ℂ → ℝ := fun y => ⨅ k, sweep O f k y with hHdef
  have hlow : ∀ h : ℂ → ℝ, HarmonicOnNhd h O → (∀ y ∈ O, h y ≤ f y) → ∀ k, ∀ y ∈ O, h y ≤ sweep O f k y := by
    intro h hh hhf k y hy
    have := sweep_mono hO (harmonicOnNhd_continuousOn hh) hf hhf k y hy
    rwa [sweep_harmonic hh] at this
  have hbdd : ∀ y ∈ O, BddBelow (range fun k => sweep O f k y) :=
    fun y hy => ⟨h₀ y, by rintro _ ⟨k, rfl⟩; exact hlow h₀ hh₀ hh₀f k y hy⟩
  have hanti : ∀ y ∈ O, Antitone fun k => sweep O f k y :=
    fun y hy => antitone_nat_of_succ_le fun k => (sweep_invariants hO hf hm k).2 y hy
  have htend : ∀ y ∈ O, Tendsto (fun k => sweep O f k y) atTop (𝓝 (H y)) :=
    fun y hy => tendsto_atTop_ciInf (hanti y hy) (hbdd y hy)
  have hHf : ∀ y ∈ O, H y ≤ f y := fun y hy => ciInf_le (hbdd y hy) 0
  have hHlow : ∀ h : ℂ → ℝ, HarmonicOnNhd h O → (∀ y ∈ O, h y ≤ f y) → ∀ y ∈ O, h y ≤ H y :=
    fun h hh hhf y hy => le_ciInf fun k => hlow h hh hhf k y hy
  refine ⟨?_, hHf, htend, hHlow⟩
  intro y hy
  obtain ⟨n, hD, hyD⟩ := exists_sweepDisc hO hy
  set c := sweepCenter (Nat.pair n 0)
  set ρ := sweepRadius (Nat.pair n 0)
  have hsO := hD.sphere_subset
  -- the visits `k_j = pair n j`
  have hkj : Tendsto (fun j => Nat.pair n j + 1) atTop atTop :=
    tendsto_atTop_mono (fun j => (Nat.right_le_pair n j).trans (Nat.le_succ _)) tendsto_id
  have hkj' : Tendsto (fun j => Nat.pair n j) atTop atTop :=
    tendsto_atTop_mono (fun j => Nat.right_le_pair n j) tendsto_id
  have hG : CircleIntegrable (fun ζ => |f ζ| + |h₀ ζ|) c ρ :=
    ((hf.abs.add (harmonicOnNhd_continuousOn hh₀).abs).mono hsO).circleIntegrable hD.1.le
  have hbound : ∀ j, ∀ ζ ∈ sphere c ρ, |sweep O f (Nat.pair n j) ζ| ≤ |f ζ| + |h₀ ζ| := by
    intro j ζ hζ
    have h1 := hlow h₀ hh₀ hh₀f (Nat.pair n j) ζ (hsO hζ)
    have h2 : sweep O f (Nat.pair n j) ζ ≤ f ζ :=
      ((hanti ζ (hsO hζ)) (Nat.zero_le _)).trans_eq rfl
    rw [abs_le]
    constructor <;> [linarith [neg_abs_le (h₀ ζ), abs_nonneg (f ζ)]; linarith [le_abs_self (f ζ),
      abs_nonneg (h₀ ζ)]]
  have hHi : CircleIntegrable H c ρ := by
    refine hG.mono_fun' ?_ ?_
    · have hmeas : Measurable fun θ => H (circleMap c ρ θ) := by
        refine Measurable.iInf fun k => ?_
        exact ((continuousOn_sweep hO hf k).comp_continuous (continuous_circleMap c ρ)
          (fun θ => hsO (circleMap_mem_sphere c hD.1.le θ))).measurable
      exact hmeas.aestronglyMeasurable
    · refine Eventually.of_forall fun θ => ?_
      have hζ := circleMap_mem_sphere c hD.1.le θ
      have h1 := hHlow h₀ hh₀ hh₀f _ (hsO hζ)
      have h2 := hHf _ (hsO hζ)
      simp only [Real.norm_eq_abs]
      rw [abs_le]
      constructor <;> [linarith [neg_abs_le (h₀ (circleMap c ρ θ)), abs_nonneg (f (circleMap c ρ θ))];
        linarith [le_abs_self (f (circleMap c ρ θ)), abs_nonneg (h₀ (circleMap c ρ θ))]]
  have hPoisson : ∀ w ∈ ball c ρ, H w = discPoissonIntegral H c ρ w := by
    intro w hw
    have hlimP := tendsto_discPoissonIntegral (Φ := fun j => sweep O f (Nat.pair n j)) hw
      (fun j => hD.circleIntegrable (continuousOn_sweep hO hf _)) hG hbound
      (fun ζ hζ => (htend ζ (hsO hζ)).comp hkj')
    have hlimS : Tendsto (fun j => sweep O f (Nat.pair n j + 1) w) atTop (𝓝 (H w)) :=
      (htend w (hD.2 (ball_subset_closedBall hw))).comp hkj
    have heq : (fun j => sweep O f (Nat.pair n j + 1) w) =
        fun j => discPoissonIntegral (sweep O f (Nat.pair n j)) c ρ w := by
      funext j
      rw [sweep_succ, sweepCenter_pair, sweepRadius_pair]
      exact discSweep_of_mem hD hw
    rw [heq] at hlimS
    exact tendsto_nhds_unique hlimS hlimP
  have hev : H =ᶠ[𝓝 y] discPoissonIntegral H c ρ := by
    filter_upwards [isOpen_ball.mem_nhds hyD] with w hw using hPoisson w hw
  exact (harmonicAt_congr_nhds hev).2 (harmonicOnNhd_discPoissonIntegral hHi y hyD)

/-- The limit of the sweeps is the greatest harmonic minorant. -/
theorem greatestHarmonicMinorant_eq_of_sweep_limit (hO : IsOpen O) (hf : ContinuousOn f O)
    (hm : HasLocalSuperMean O f) {h₀ : ℂ → ℝ} (hh₀ : HarmonicOnNhd h₀ O) (hh₀f : ∀ y ∈ O, h₀ y ≤ f y) :
    ∀ y ∈ O, greatestHarmonicMinorant O (fun w => (f w : EReal)) y = ((⨅ k, sweep O f k y : ℝ) : EReal) := by
  obtain ⟨hH, hHf, -, hHlow⟩ := sweep_limit hO hf hm hh₀ hh₀f
  intro y hy
  refine le_antisymm (iSup₂_le fun h hh => ?_) ?_
  · exact EReal.coe_le_coe_iff.2 (hHlow h hh.1 (fun w hw => EReal.coe_le_coe_iff.1 (hh.2 w hw)) y hy)
  · exact IsHarmonicMinorant.le_greatestHarmonicMinorant
      ⟨hH, fun w hw => EReal.coe_le_coe_iff.2 (hHf w hw)⟩ y

end Sweep

/-! ## Sweeping commutes with integration -/

theorem measurable_poissonKernel_comp (c : ℂ) (ρ : ℝ) :
    Measurable fun q : ℂ × ℝ => poissonKernel c q.1 (circleMap c ρ q.2) := by
  unfold poissonKernel
  fun_prop

theorem measurable_poissonKernel_comp' (c y : ℂ) : Measurable fun ζ : ℂ => poissonKernel c y ζ := by
  unfold poissonKernel
  fun_prop

/-- Circle averages commute with integration of bounded jointly measurable families. -/
theorem circleAverage_integral_swap {m : Measure ℂ} [IsFiniteMeasure m] {G : ℂ → ℂ → ℝ} {c : ℂ} {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hG : Measurable (uncurry G)) {B : ℝ} (hB : ∀ x, ∀ ζ ∈ sphere c ρ, |G x ζ| ≤ B) :
    Real.circleAverage (fun ζ => ∫ x, G x ζ ∂m) c ρ = ∫ x, Real.circleAverage (G x) c ρ ∂m := by
  have : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) (2 * π))) :=
    isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
  simp only [Real.circleAverage]
  rw [integral_smul]
  congr 1
  rw [intervalIntegral.integral_of_le two_pi_pos.le]
  simp only [intervalIntegral.integral_of_le two_pi_pos.le]
  refine integral_integral_swap ?_
  refine Integrable.of_bound ?_ B (Eventually.of_forall fun q => ?_)
  · exact (hG.comp (measurable_snd.prodMk
      ((continuous_circleMap c ρ).measurable.comp measurable_fst))).aestronglyMeasurable
  · rw [Real.norm_eq_abs]
    exact hB q.2 _ (circleMap_mem_sphere c hρ q.1)

section SweepIntegral

variable {O : Set ℂ}

/-- One Poisson modification commutes with integration of a bounded jointly measurable family and preserves joint
measurability. -/
theorem discSweep_integral {m : Measure ℂ} [IsFiniteMeasure m] {G : ℂ → ℂ → ℝ}
    (hGm : Measurable (uncurry G)) {c : ℂ} {ρ B : ℝ}
    (hB : IsSweepDisc O c ρ → ∀ x, ∀ ζ ∈ sphere c ρ, |G x ζ| ≤ B) :
    Measurable (uncurry fun x y => discSweep O c ρ (G x) y) ∧
      ∀ y, discSweep O c ρ (fun y => ∫ x, G x y ∂m) y = ∫ x, discSweep O c ρ (G x) y ∂m := by
  classical
  by_cases hD : IsSweepDisc O c ρ
  swap
  · have hid : ∀ (f : ℂ → ℝ), discSweep O c ρ f = f := fun f => funext fun y =>
      discSweep_of_not (fun h => hD h.1)
    constructor
    · simp only [hid]
      exact hGm
    · intro y
      simp only [hid]
  have hB' := hB hD
  have hmap : Measurable fun q : (ℂ × ℂ) × ℝ => (q.1.1, circleMap c ρ q.2) :=
    (measurable_fst.comp measurable_fst).prodMk ((continuous_circleMap c ρ).measurable.comp measurable_snd)
  have hmapP : Measurable fun q : (ℂ × ℂ) × ℝ => (q.1.2, q.2) :=
    (measurable_snd.comp measurable_fst).prodMk measurable_snd
  have hΦ : Measurable fun q : (ℂ × ℂ) × ℝ =>
      poissonKernel c q.1.2 (circleMap c ρ q.2) * G q.1.1 (circleMap c ρ q.2) :=
    ((measurable_poissonKernel_comp c ρ).comp hmapP).mul (hGm.comp hmap)
  have e : (fun p : ℂ × ℂ => discPoissonIntegral (G p.1) c ρ p.2) = fun p =>
      (2 * π)⁻¹ * ∫ θ in Ioc 0 (2 * π), poissonKernel c p.2 (circleMap c ρ θ) * G p.1 (circleMap c ρ θ) := by
    funext p
    simp only [discPoissonIntegral, Real.circleAverage, intervalIntegral.integral_of_le two_pi_pos.le,
      smul_eq_mul, Pi.mul_apply]
  have hmeasP : Measurable fun p : ℂ × ℂ => discPoissonIntegral (G p.1) c ρ p.2 := by
    rw [e]
    exact (hΦ.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioc (0 : ℝ) (2 * π)))).measurable.const_mul _
  refine ⟨?_, fun y => ?_⟩
  · have heq : (uncurry fun x y => discSweep O c ρ (G x) y) = fun p =>
        if p.2 ∈ ball c ρ then discPoissonIntegral (G p.1) c ρ p.2 else G p.1 p.2 := by
      funext p
      simp only [uncurry]
      by_cases hp : p.2 ∈ ball c ρ
      · rw [ite_eq_left hp, discSweep_of_mem hD hp]
      · rw [ite_eq_right hp, discSweep_of_not (fun h => hp h.2)]
    rw [heq]
    exact Measurable.ite (measurable_snd measurableSet_ball) hmeasP hGm
  · by_cases hy : y ∈ ball c ρ
    · simp only [discSweep_of_mem hD hy, discPoissonIntegral]
      have hP : (poissonKernel c y • fun ζ => ∫ x, G x ζ ∂m) =
          fun ζ => ∫ x, poissonKernel c y ζ * G x ζ ∂m := by
        funext ζ
        simp only [smul_eq_mul, Pi.mul_apply, integral_const_mul]
      rw [hP]
      obtain ⟨Bp, hBp⟩ := (isCompact_sphere c |ρ|).exists_bound_of_continuousOn
        (continuousOn_poissonKernel (c := c) (ρ := ρ) hy)
      rw [abs_of_pos hD.1] at hBp
      rw [circleAverage_integral_swap hD.1.le (B := Bp * B) ?_ ?_]
      · rfl
      · exact ((measurable_poissonKernel_comp' c y).comp measurable_snd).mul hGm
      · intro x ζ hζ
        rw [abs_mul]
        have := hBp ζ hζ
        rw [Real.norm_eq_abs] at this
        exact mul_le_mul this (hB' x ζ hζ) (abs_nonneg _) ((abs_nonneg _).trans this)
    · simp only [discSweep_of_not (fun h : IsSweepDisc O c ρ ∧ y ∈ ball c ρ => hy h.2)]

/-- **Sweeping commutes with integration** of a bounded jointly measurable family of continuous functions, and
preserves joint measurability. -/
theorem sweep_integral (hO : IsOpen O) {m : Measure ℂ} [IsFiniteMeasure m] {F : ℂ → ℂ → ℝ}
    (hFm : Measurable (uncurry F)) (hFc : ∀ x, ContinuousOn (F x) O) {lo : ℂ → ℝ} {M : ℝ}
    (hlo : HarmonicOnNhd lo O) (hb : ∀ x, ∀ y ∈ O, lo y ≤ F x y ∧ F x y ≤ M) (k : ℕ) :
    Measurable (uncurry fun x y => sweep O (F x) k y) ∧
      ∀ y, sweep O (fun y => ∫ x, F x y ∂m) k y = ∫ x, sweep O (F x) k y ∂m := by
  have hbk : ∀ k x, ∀ y ∈ O, lo y ≤ sweep O (F x) k y ∧ sweep O (F x) k y ≤ M := by
    intro k x y hy
    have h1 := sweep_mono hO (harmonicOnNhd_continuousOn hlo) (hFc x) (fun w hw => (hb x w hw).1) k y hy
    have h2 := sweep_mono hO (hFc x) continuousOn_const (fun w hw => (hb x w hw).2) k y hy
    rw [sweep_harmonic hlo] at h1
    rw [sweep_harmonic (harmonicOnNhd_const M)] at h2
    exact ⟨h1, h2⟩
  induction k with
  | zero => exact ⟨hFm, fun y => rfl⟩
  | succ k ih =>
    have hbd : IsSweepDisc O (sweepCenter k) (sweepRadius k) → ∃ B : ℝ, ∀ x, ∀ ζ ∈ sphere (sweepCenter k)
        (sweepRadius k), |sweep O (F x) k ζ| ≤ B := by
      intro hD
      obtain ⟨Blo, hBlo⟩ := (isCompact_sphere _ _).exists_bound_of_continuousOn
        ((harmonicOnNhd_continuousOn hlo).mono hD.sphere_subset)
      refine ⟨Blo + |M|, fun x ζ hζ => ?_⟩
      obtain ⟨h1, h2⟩ := hbk k x ζ (hD.sphere_subset hζ)
      have h3 := hBlo ζ hζ
      rw [Real.norm_eq_abs] at h3
      rw [abs_le] at h3 ⊢
      constructor <;> linarith [le_abs_self M, neg_abs_le M]
    obtain ⟨B, hB⟩ : ∃ B : ℝ, IsSweepDisc O (sweepCenter k) (sweepRadius k) → ∀ x, ∀ ζ ∈ sphere (sweepCenter k)
        (sweepRadius k), |sweep O (F x) k ζ| ≤ B := by
      by_cases hD : IsSweepDisc O (sweepCenter k) (sweepRadius k)
      · obtain ⟨B, hB⟩ := hbd hD
        exact ⟨B, fun _ => hB⟩
      · exact ⟨0, fun h => absurd h hD⟩
    obtain ⟨h1, h2⟩ := discSweep_integral (m := m) ih.1 hB
    refine ⟨h1, fun y => ?_⟩
    rw [sweep_succ, funext ih.2]
    exact h2 y

end SweepIntegral

end HarmonicBalls

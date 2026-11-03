import HarmonicBalls.Steps.Sec6.LowMass
import HarmonicBalls.Proofs.Sec6.HarnackIteration
import HarmonicBalls.Proofs.Sec6.Localization

/-!
# Lemma 6.13 from the decay step and the maximum principle on discs

The combinatorial part of the proof of Lemma 6.13 (lines 1725-1810 of paper/lqg_harmonic_ball-corrected.tex), with
the corrections [C15] (`closure B_ρ(x₀) ⊂ B_1 \ {z}`) and GRAPH G23 (all `N ≥ C₃ log₇ ε_j^{-1/2}` good radii are used,
which gives `b^N` instead of `b^{N-1}`, so that every `C₃ > 0` is allowed). Let `ε = ε_j`, `x ∈ Λ̃_t ∩ S_j`.

* Covering (line 1731): a lattice point `w ∈ (ερ/100) ℤ²` with `|x - w| ≤ ερ/100` (`exists_lattice_near`).
* (VG-iii) at `w` gives the set `R` of good radii `r ∈ [ερ, ε^{1/2} ρ] ∩ {ρ 7^{-k}}`, `|R| ≥ C₃ log₇ ε^{-1/2}`.
* Step 1 (lines 1739-1748): for `r ∈ R`, `𝔸_{r,7r}(w) ⊂ B_{8ε^{1/2}ρ}(x) ⊂ 𝔸_{ρ/2,d^+_j}(x₀)` (Lemma 6.12), so the mass
  hypothesis gives `μ_h(Λ̃_t ∩ 𝔸_{3r,5r}(w)) ≤ a M_ρ(x₀) ε^{β⁻} ≤ a μ_h(B_{ερ}(w + 4r)) ≤ a μ_h(𝔸_{3r,5r}(w))`.
* Step 2 is `GoodAnnulusOdometerDecayStep`; Step 3 (lines 1784-1799) iterates it over `R` from the largest radius
  down (`iterate_over_radii`; consecutive radii differ by a factor `≥ 7`, so `𝔸_{3r,5r}(w) ⊂ B_{4r'}(w)`), giving
  `v^z_t(x) ≤ b^{|R|} sup_{Λ̃_t ∩ 𝔸_{ρ/2,d^+_j}(x₀)} v^z_t`.
* Lines 1801-1806: `𝔸_{ρ/2,d^+_{j+1}}(x₀) ⊂ B_{d_j}(x₀)` and `∂B_{d_j}(x₀) ⊂ S_j`, and `ComponentOdometerDiscMaxStep`.

The universal constant is `C' = log 2 / (2 log 7)`, so that `C₃ log₇ ε_j^{-1/2} = C' C₃ (N₀ + j)`.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal Pointwise

open Section6

universe u

namespace Section6

/-- A point of `(δ ℤ²)` within distance `δ` of `x`. -/
theorem exists_lattice_near (x : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ j k : ℤ, ‖x - (δ : ℂ) * ((j : ℂ) + (k : ℂ) * Complex.I)‖ ≤ δ := by
  refine ⟨round (x.re / δ), round (x.im / δ), ?_⟩
  set w : ℂ := (δ : ℂ) * ((round (x.re / δ) : ℂ) + (round (x.im / δ) : ℂ) * Complex.I)
  have hre : (x - w).re = δ * (x.re / δ - round (x.re / δ)) := by
    simp [w, Complex.mul_re]; field_simp
  have him : (x - w).im = δ * (x.im / δ - round (x.im / δ)) := by
    simp [w, Complex.mul_im]; field_simp
  have h1 : |(x - w).re| ≤ δ / 2 := by
    rw [hre, abs_mul, abs_of_pos hδ]
    nlinarith [abs_sub_round (x.re / δ)]
  have h2 : |(x - w).im| ≤ δ / 2 := by
    rw [him, abs_mul, abs_of_pos hδ]
    nlinarith [abs_sub_round (x.im / δ)]
  calc ‖x - w‖ ≤ |(x - w).re| + |(x - w).im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ δ := by linarith

/-- The iteration over the good radii (Step 3), abstractly: `f r ≤ B g r`, `g r ≤ S₀`, and `g r ≤ f r'` for
`r < r'` give `f r ≤ B^{#{r' ∈ F : r ≤ r'}} S₀`. -/
theorem iterate_over_radii {F : Finset ℝ} {f g : ℝ → ℝ≥0∞} {B S₀ : ℝ≥0∞}
    (hfg : ∀ r ∈ F, f r ≤ B * g r) (hg : ∀ r ∈ F, g r ≤ S₀)
    (hgf : ∀ r ∈ F, ∀ r' ∈ F, r < r' → g r ≤ f r') :
    ∀ r ∈ F, f r ≤ B ^ (F.filter (r ≤ ·)).card * S₀ := by
  induction F using Finset.induction_on_min with
  | empty => intro r hr; simp at hr
  | insert a s ha ih =>
    have ih' := ih (fun r hr => hfg r (Finset.mem_insert_of_mem hr))
      (fun r hr => hg r (Finset.mem_insert_of_mem hr))
      (fun r hr r' hr' h => hgf r (Finset.mem_insert_of_mem hr) r' (Finset.mem_insert_of_mem hr') h)
    intro r hr
    rcases Finset.mem_insert.1 hr with rfl | hrs
    · have has : r ∉ s := fun h => lt_irrefl _ (ha r h)
      have hcard : ((insert r s).filter (r ≤ ·)).card = s.card + 1 := by
        rw [Finset.filter_true_of_mem (fun x hx => ?_), Finset.card_insert_of_notMem has]
        rcases Finset.mem_insert.1 hx with rfl | hxs
        · exact le_rfl
        · exact (ha x hxs).le
      rw [hcard]
      by_cases hs : s.Nonempty
      · have hm : s.min' hs ∈ s := Finset.min'_mem s hs
        have h1 := ih' (s.min' hs) hm
        have hcard' : (s.filter (s.min' hs ≤ ·)).card = s.card := by
          rw [Finset.filter_true_of_mem (fun x hx => Finset.min'_le s x hx)]
        rw [hcard'] at h1
        calc f r ≤ B * g r := hfg r hr
          _ ≤ B * f (s.min' hs) := mul_le_mul_right (hgf r hr _ (Finset.mem_insert_of_mem hm) (ha _ hm)) _
          _ ≤ B * (B ^ s.card * S₀) := mul_le_mul_right h1 _
          _ = B ^ (s.card + 1) * S₀ := by ring
      · rw [Finset.not_nonempty_iff_eq_empty.1 hs, Finset.card_empty]
        calc f r ≤ B * g r := hfg r hr
          _ ≤ B * S₀ := mul_le_mul_right (hg r hr) _
          _ = B ^ (0 + 1) * S₀ := by ring
    · have hra : ¬ r ≤ a := fun h => lt_irrefl _ (lt_of_lt_of_le (ha r hrs) h)
      have hfilter : (insert a s).filter (r ≤ ·) = s.filter (r ≤ ·) := by
        rw [Finset.filter_insert]; simp only [hra, ↓reduceIte]
      rw [hfilter]
      exact ih' r hrs

/-- `B_{8 ε_j^{1/2} ρ}(x) ⊂ 𝔸_{ρ/2,d^+_j}(x₀)` for `x ∈ S_j` (eq:annulus-contained-in-ball). -/
theorem ball_subset_of_mem_shell {ρ : ℝ} (hρ : 0 < ρ) {N₀ : ℕ} (hN₀ : 200 ≤ N₀) {x₀ x : ℂ} {j : ℕ}
    (hx : x ∈ shell x₀ ρ j) :
    ball x (8 * Real.sqrt (shellScale N₀ j) * ρ) ⊆ annulus x₀ (ρ / 2) (shellOuterRadius ρ j) := by
  have hL : ρ * (2 : ℝ)⁻¹ ^ 50 ≤ ρ / 2 ^ 40 := by
    have : (2 : ℝ)⁻¹ ^ 50 ≤ 1 / 2 ^ 40 := by norm_num
    calc ρ * (2 : ℝ)⁻¹ ^ 50 ≤ ρ * (1 / 2 ^ 40) := mul_le_mul_of_nonneg_left this hρ.le
      _ = ρ / 2 ^ 40 := by ring
  have h1 := abs_lt.1 (abs_dist_sub_lt_of_mem_shell hx)
  have h2 := shellRadius_ge hρ j
  have h4 := shellWidth_le hρ j
  have h5 := eight_sqrt_shellScale_mul_le hρ hN₀ j
  intro y hy
  have hyw := mem_ball.1 hy
  have t1 := dist_triangle y x x₀
  have t2 := dist_triangle x y x₀
  rw [dist_comm x y] at t2
  refine ⟨mem_ball.2 ?_, fun hc => ?_⟩
  · rw [shellOuterRadius]; linarith
  · have := mem_closedBall.1 hc
    linarith

end Section6

/-- **Lemma 6.13** (corrected by [C15], every `C₃ > 0`) from the decay step (Step 2) and the maximum principle on
discs, with `C' = log 2 / (2 log 7)`. -/
theorem lowMassSmallOdometerStmt_of_steps (hdec : GoodAnnulusOdometerDecayStep.{u})
    (hdisc : ComponentOdometerDiscMaxStep.{u}) : LowMassSmallOdometerStmt.{u} := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog7 : 0 < Real.log 7 := Real.log_pos (by norm_num)
  refine ⟨Real.log 2 / (2 * Real.log 7), by positivity, fun γ α₀ hγ hγ2 hα₀ β hβ Ω _ P hC hcirc μ hGFF hμ => ?_⟩
  filter_upwards [hdec γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ, hdisc γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ]
    with ω hdω hmω
  intro z hz t ht a _ b hb N₀ hN₀ C₃ hC₃ ρ hρ x₀ hball hVG3 Λ hΛ j hmass
  have hβ0 : 0 < β := lt_of_le_of_lt (by positivity) hβ
  set ε := shellScale N₀ j with hεdef
  set S₀ := ⨆ x ∈ Λ ∩ annulus x₀ (ρ / 2) (shellOuterRadius ρ j), odometerExt (μ ω) z t x with hS₀
  set M := annulusBallMassSize (μ ω) β ρ x₀ with hMdef
  have hε0 : 0 < ε := by rw [hεdef, shellScale, dyadicScale]; positivity
  have hεsmall : ε ≤ (2 : ℝ)⁻¹ ^ 200 := by
    rw [hεdef, shellScale, dyadicScale]
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hε1 : ε ≤ 1 := hεsmall.trans (by norm_num)
  have hsq : ε ≤ Real.sqrt ε := Real.le_sqrt_of_sq_le (by nlinarith)
  have hsq0 : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε0
  have hερ0 : 0 < ε * ρ := by positivity
  have hsqρ : ε * ρ ≤ Real.sqrt ε * ρ := mul_le_mul_of_nonneg_right hsq hρ.le
  have hερs : ε * ρ ≤ (2 : ℝ)⁻¹ ^ 200 * ρ := mul_le_mul_of_nonneg_right hεsmall hρ.le
  have hΛsub : Λ ⊆ cluster (μ ω) 1 z t ∩ ball x₀ ρ := by
    obtain ⟨y, -, rfl⟩ := hΛ; exact connectedComponentIn_subset _ _
  have hB1 : ball x₀ ρ ⊆ ball 0 1 := fun x hx => (hball (ball_subset_closedBall hx)).1
  have hjρ : shellOuterRadius ρ j ≤ 7 / 8 * ρ := shellOuterRadius_le hρ j
  have hA0ρ : annulus x₀ (ρ / 2) (shellOuterRadius ρ j) ⊆ ball x₀ ρ :=
    sdiff_subset.trans (ball_subset_ball (by linarith))
  -- the bound at points of `Λ̃_t ∩ S_j`
  have key : ∀ x ∈ Λ ∩ shell x₀ ρ j,
      odometerExt (μ ω) z t x ≤ ENNReal.ofReal (b ^ (Real.log 2 / (2 * Real.log 7) * C₃ * ((N₀ : ℝ) + j))) * S₀ := by
    rintro x ⟨hxΛ, hxS⟩
    have hδ : 0 < ε * ρ / 100 := by positivity
    obtain ⟨jj, kk, hxw⟩ := exists_lattice_near x hδ
    set w : ℂ := ((ε * ρ / 100 : ℝ) : ℂ) * ((jj : ℂ) + (kk : ℂ) * Complex.I) with hw_def
    have hbx := ball_subset_of_mem_shell hρ hN₀ hxS
    rw [← hεdef] at hbx
    have hxw' : dist w x ≤ ε * ρ / 100 := by rw [dist_comm, dist_eq_norm]; exact hxw
    have hin : ∀ y : ℂ, ∀ s : ℝ, dist y w < s → s + ε * ρ / 100 < 8 * Real.sqrt ε * ρ →
        y ∈ annulus x₀ (ρ / 2) (shellOuterRadius ρ j) := fun y s hy hs =>
      hbx (mem_ball.2 (by linarith [dist_triangle y w x]))
    have h8 : ε * ρ / 100 < 8 * Real.sqrt ε * ρ := by linarith
    have hwA : w ∈ annulus x₀ (ρ / 2) ρ :=
      annulus_subset_annulus le_rfl (by linarith) (hin w (ε * ρ / 100 / 2) (by rw [dist_self]; positivity)
        (by linarith))
    have hw1 : w ∈ ball (0 : ℂ) 1 := hB1 hwA.1
    -- (VG-iii) at `w`, scale `n = N₀ + j`
    have hvg := hVG3 (N₀ + j) (Nat.le_add_right _ _) w ⟨⟨jj, kk, rfl⟩, hwA⟩
    set R : Set ℝ := {r : ℝ | r ∈ Icc (dyadicScale (N₀ + j) * ρ) (Real.sqrt (dyadicScale (N₀ + j)) * ρ) ∧
      (∃ k : ℕ, 1 ≤ k ∧ r = ρ * (7 : ℝ)⁻¹ ^ k) ∧ IsGoodAnnulus (μ ω) r w a b} with hRdef
    have hRfin : R.Finite :=
      finite_of_geometric (q := (7 : ℝ)⁻¹) (A := ρ) (lo := ε * ρ) (by norm_num) (by norm_num) (by positivity)
        fun r hr => ⟨hr.1.1, by obtain ⟨k, -, hk⟩ := hr.2.1; exact ⟨k, hk⟩⟩
    -- facts at each good radius
    have hR : ∀ r ∈ R, ε * ρ ≤ r ∧ r ≤ Real.sqrt ε * ρ ∧ IsGoodAnnulus (μ ω) r w a b ∧
        ∃ k : ℕ, 1 ≤ k ∧ r = ρ * (7 : ℝ)⁻¹ ^ k := fun r hr => ⟨hr.1.1, hr.1.2, hr.2.2, hr.2.1⟩
    have hann7 : ∀ r ∈ R, annulus w r (7 * r) ⊆ annulus x₀ (ρ / 2) (shellOuterRadius ρ j) := by
      intro r hr y hy
      obtain ⟨h1, h2, -, -⟩ := hR r hr
      exact hin y (7 * r) hy.1 (by linarith)
    have h35 : ∀ r : ℝ, 0 < r → annulus w (3 * r) (5 * r) ⊆ annulus w r (7 * r) :=
      fun r hr => annulus_subset_annulus (by linarith) (by linarith)
    have hdecay : ∀ r ∈ R, ⨆ y ∈ Λ ∩ ball w (4 * r), odometerExt (μ ω) z t y ≤
        ENNReal.ofReal b * ⨆ y ∈ Λ ∩ annulus w (3 * r) (5 * r), odometerExt (μ ω) z t y := by
      intro r hr
      obtain ⟨h1, h2, hgood, -⟩ := hR r hr
      have hr0 : 0 < r := lt_of_lt_of_le (by positivity) h1
      have hcl : closedBall w (5 * r) ⊆ ball x₀ ρ := fun y hy =>
        hA0ρ (hin y (5 * r + ε * ρ / 200) (lt_of_le_of_lt (mem_closedBall.1 hy) (by linarith))
          (by linarith))
      -- Step 1: the mass condition
      have hm1 := hmass r hr0 w hw1 (hann7 r hr)
      set c : ℂ := w + ((4 * r : ℝ) : ℂ) with hc_def
      have hcw : dist c w = 4 * r := by
        rw [hc_def, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by positivity)]
      have hcA : c ∈ annulus x₀ (ρ / 2) ρ :=
        annulus_subset_annulus le_rfl (by linarith) (hin c (4 * r + ε * ρ / 200) (by linarith)
          (by linarith))
      have hερ : ε * ρ ∈ Ioo 0 (ρ / 4) := ⟨hερ0, by norm_num at hερs ⊢; linarith⟩
      have hMc : M ≤ μ ω (ball c (ε * ρ)) / ENNReal.ofReal ((ε * ρ / ρ) ^ β) :=
        iInf₂_le_of_le c hcA (iInf₂_le (ε * ρ) hερ)
      rw [mul_div_cancel_right₀ ε hρ.ne'] at hMc
      have hεβ : ENNReal.ofReal (ε ^ β) ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
      have hMc' : M * ENNReal.ofReal (ε ^ β) ≤ μ ω (ball c (ε * ρ)) :=
        (ENNReal.le_div_iff_mul_le (Or.inl hεβ) (Or.inl ENNReal.ofReal_ne_top)).1 hMc
      have hballc : ball c (ε * ρ) ⊆ annulus w (3 * r) (5 * r) := by
        intro y hy
        have hyc := mem_ball.1 hy
        have t1 := dist_triangle y c w
        have t2 := dist_triangle c y w
        rw [dist_comm c y] at t2
        refine ⟨mem_ball.2 (by linarith), fun hc' => ?_⟩
        have := mem_closedBall.1 hc'
        linarith
      have hmass' : μ ω (Λ ∩ annulus w (3 * r) (5 * r)) ≤
          ENNReal.ofReal a * μ ω (annulus w (3 * r) (5 * r)) := by
        calc μ ω (Λ ∩ annulus w (3 * r) (5 * r)) ≤ ENNReal.ofReal a * M * ENNReal.ofReal (ε ^ β) := hm1
          _ = ENNReal.ofReal a * (M * ENNReal.ofReal (ε ^ β)) := by ring
          _ ≤ ENNReal.ofReal a * μ ω (ball c (ε * ρ)) := mul_le_mul_right hMc' _
          _ ≤ ENNReal.ofReal a * μ ω (annulus w (3 * r) (5 * r)) := mul_le_mul_right (measure_mono hballc) _
      exact hdω z hz t ht ρ hρ x₀ hball Λ hΛ a b r hr0 w hcl hgood hmass'
    -- Step 3: the iteration
    set F := hRfin.toFinset with hF
    have hmemF : ∀ r, r ∈ F ↔ r ∈ R := fun r => Set.Finite.mem_toFinset hRfin
    have hiter := iterate_over_radii (F := F) (B := ENNReal.ofReal b) (S₀ := S₀)
      (f := fun r => ⨆ y ∈ Λ ∩ ball w (4 * r), odometerExt (μ ω) z t y)
      (g := fun r => ⨆ y ∈ Λ ∩ annulus w (3 * r) (5 * r), odometerExt (μ ω) z t y)
      (fun r hr => hdecay r ((hmemF r).1 hr))
      (fun r hr => biSup_mono fun y hy =>
        ⟨hy.1, hann7 r ((hmemF r).1 hr) (h35 r (lt_of_lt_of_le (by positivity) ((hR r ((hmemF r).1 hr)).1)) hy.2)⟩)
      (fun r hr r' hr' hlt => by
        obtain ⟨h1, -, -, k, -, hk⟩ := hR r ((hmemF r).1 hr)
        obtain ⟨-, -, -, k', -, hk'⟩ := hR r' ((hmemF r').1 hr')
        have hr0 : 0 < r := lt_of_lt_of_le (by positivity) h1
        have h7 : 7 * r ≤ r' := by
          rw [hk, hk'] at hlt ⊢
          have hkk : k' < k := by
            by_contra hcon
            have : (7 : ℝ)⁻¹ ^ k' ≤ (7 : ℝ)⁻¹ ^ k :=
              pow_le_pow_of_le_one (by norm_num) (by norm_num) (not_lt.1 hcon)
            have := mul_le_mul_of_nonneg_left this hρ.le
            linarith
          have : (7 : ℝ)⁻¹ ^ (k' + 1) ≥ (7 : ℝ)⁻¹ ^ k :=
            pow_le_pow_of_le_one (by norm_num) (by norm_num) hkk
          rw [pow_succ] at this
          have h7ρ := mul_le_mul_of_nonneg_left this (le_of_lt (by positivity : (0 : ℝ) < 7 * ρ))
          linarith
        exact biSup_mono fun y hy => ⟨hy.1, ball_subset_ball (by linarith) hy.2.1⟩)
    -- the smallest good radius covers `x`
    have hcount : C₃ * Real.logb 7 (dyadicScale (N₀ + j) ^ (-(1 / 2 : ℝ))) ≤ (R.ncard : ℝ) := hvg
    have hRne : F.Nonempty := by
      by_contra hne
      rw [Finset.not_nonempty_iff_eq_empty] at hne
      have h0 : R.ncard = 0 := by rw [Set.ncard_eq_toFinset_card R hRfin, ← hF, hne, Finset.card_empty]
      rw [h0, Nat.cast_zero] at hcount
      have hpos : 0 < Real.logb 7 (dyadicScale (N₀ + j) ^ (-(1 / 2 : ℝ))) := by
        refine Real.logb_pos (by norm_num) ?_
        refine Real.one_lt_rpow_of_pos_of_lt_one_of_neg hε0 ?_ (by norm_num)
        exact lt_of_le_of_lt hεsmall (by norm_num)
      linarith [mul_pos hC₃ hpos]
    set rm := F.min' hRne with hrm
    have hrmF : rm ∈ F := Finset.min'_mem F hRne
    obtain ⟨hrm1, -, -, -⟩ := hR rm ((hmemF rm).1 hrmF)
    have hxball : x ∈ Λ ∩ ball w (4 * rm) := ⟨hxΛ, mem_ball.2 (by rw [dist_comm]; linarith)⟩
    have hfilter : (F.filter (rm ≤ ·)).card = R.ncard := by
      rw [Finset.filter_true_of_mem (fun r hr => Finset.min'_le F r hr), Set.ncard_eq_toFinset_card R hRfin]
    have h1 : odometerExt (μ ω) z t x ≤ ENNReal.ofReal b ^ R.ncard * S₀ := by
      have := hiter rm hrmF
      rw [hfilter] at this
      exact le_trans (le_iSup₂_of_le (f := fun y (_ : y ∈ Λ ∩ ball w (4 * rm)) => odometerExt (μ ω) z t y)
        x hxball le_rfl) this
    refine h1.trans (mul_le_mul_left ?_ _)
    rw [← ENNReal.ofReal_pow hb.1.le]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← Real.rpow_natCast]
    refine Real.rpow_le_rpow_of_exponent_ge hb.1 hb.2.le ?_
    -- `C' C₃ (N₀ + j) = C₃ log₇ ε^{-1/2} ≤ |R|`
    have hlogb : Real.logb 7 (dyadicScale (N₀ + j) ^ (-(1 / 2 : ℝ))) =
        Real.log 2 / (2 * Real.log 7) * ((N₀ : ℝ) + j) := by
      rw [dyadicScale, two_inv_pow_rpow, Real.logb, Real.log_rpow (by norm_num)]
      push_cast
      ring
    rw [hlogb] at hcount
    calc Real.log 2 / (2 * Real.log 7) * C₃ * ((N₀ : ℝ) + j)
        = C₃ * (Real.log 2 / (2 * Real.log 7) * ((N₀ : ℝ) + j)) := by ring
      _ ≤ _ := hcount
  -- the disc step
  have hdj : sphere x₀ (shellRadius ρ j) ⊆ shell x₀ ρ j := fun s hs =>
    ⟨s, hs, 0, mem_ball_self (shellWidth_pos hρ j), add_zero s⟩
  have hdpos : 0 < shellRadius ρ j := by
    have := shellRadius_ge hρ j
    have : ρ * (2 : ℝ)⁻¹ ^ 50 ≤ ρ / 2 ^ 40 := by
      have h : (2 : ℝ)⁻¹ ^ 50 ≤ 1 / 2 ^ 40 := by norm_num
      calc ρ * (2 : ℝ)⁻¹ ^ 50 ≤ ρ * (1 / 2 ^ 40) := mul_le_mul_of_nonneg_left h hρ.le
        _ = ρ / 2 ^ 40 := by ring
    linarith
  have hsucc : shellOuterRadius ρ (j + 1) < shellRadius ρ j := by
    have h1 := shellRadius_le_sub_of_lt hρ (Nat.lt_succ_self j)
    have h2 := shellWidth_anti hρ (Nat.le_succ j)
    have h3 := shellWidth_pos hρ j
    rw [shellOuterRadius]
    linarith
  have hcl : closedBall x₀ (shellRadius ρ j) ⊆ ball x₀ ρ :=
    closedBall_subset_ball (by linarith [shellRadius_le hρ j])
  calc ⨆ x ∈ Λ ∩ annulus x₀ (ρ / 2) (shellOuterRadius ρ (j + 1)), odometerExt (μ ω) z t x
      ≤ ⨆ x ∈ Λ ∩ ball x₀ (shellRadius ρ j), odometerExt (μ ω) z t x :=
        biSup_mono fun x hx => ⟨hx.1, ball_subset_ball hsucc.le hx.2.1⟩
    _ ≤ ⨆ x ∈ Λ ∩ sphere x₀ (shellRadius ρ j), odometerExt (μ ω) z t x :=
        hmω z hz t ht ρ hρ x₀ hball Λ hΛ x₀ _ hdpos hcl
    _ ≤ ENNReal.ofReal (b ^ (Real.log 2 / (2 * Real.log 7) * C₃ * ((N₀ : ℝ) + j))) * S₀ :=
        iSup₂_le fun x hx => key x ⟨hx.1, hdj hx.2⟩

end HarmonicBalls

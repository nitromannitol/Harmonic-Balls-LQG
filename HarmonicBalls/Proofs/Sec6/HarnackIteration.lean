import HarmonicBalls.Steps.Sec6.HarnackIteration
import HarmonicBalls.Proofs.Sec6.ShellDecomposition

/-!
# Lemma 6.11 from Lemmas 6.8, 6.10, 6.12, 6.13

The proof of Lemma 6.11 (lines 1828-1949 of paper/lqg_harmonic_ball-corrected.tex), with the corrections
(base case through Lemma 6.10 with `(s₁,s₂,s₃,s₄) = (1/4,1/2,7/8,1)` and domain monotonicity of `SG`, plus the
case `𝔸_{ρ/2,7ρ/8}(x₀) ⊆ Λ^z_t` excluded by the mass of a ball `B_{ρ/8}(y)`), (all `C₃ > 0`; `b` from the
universal `C'` of Lemma 6.13: `b := 2^{-2β⁻/(C'C₃)}`, so `b^{C'C₃ n} = 2^{-2β⁻ n}`; this replaces the slip at
line 1916) and (`Λ̃_t` is the statement's component of `Λ^z_t ∩ B_ρ(x₀)`).

Constants (chosen before `α₀`, as printed): `C₄` of Lemma 6.8 at `(1,3,5,7)`, `c` of Lemma 6.10 at
`(1/4,1/2,7/8,1)`, `C'` of Lemma 6.13; `θ = a 2^{-β⁻} C₁⁻ / ((C₄ ∨ 1) c C₂⁺)`,
`N₁ = max(200, ⌈-log θ / (β⁻ log 2)⌉)` (eq:choice-of-N1) and `α = a 2^{-N₀β⁻} (C₁⁻ ∧ 1) 8^{-β⁻} / 2`
(eq:choice-of-alpha, corrected).

The deterministic core `harnack_core` runs the induction of lines 1857-1948 with `K_j = a M_ρ(x₀) ε_j^{β⁻}`:
the mass bound at shell `j` gives, by Lemma 6.13, the odometer bound at `j+1`, which gives, by Lemma 6.8 (in the form
eq:small-odometer-implies-low-mass), the mass bound at `j+1`. Then `v^z_t = 0` on `Λ̃_t ∩ 𝔸_{ρ/2,d}(x₀)` with
`d = 3ρ/4 - 224 · 2^{-50} ρ ≤ d^+_j`, so `Λ̃_t` misses that annulus, and `ClusterComponentInnerBallStep` concludes.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

open Section6

universe u

namespace Section6

/-- Open annuli in `ℂ` are preconnected: the image of `(r, R) × ℝ` under polar coordinates about `x₀`. -/
theorem isPreconnected_annulus (x₀ : ℂ) {r : ℝ} (hr : 0 ≤ r) (R : ℝ) : IsPreconnected (annulus x₀ r R) := by
  have hf : Continuous fun p : ℝ × ℝ => x₀ + (p.1 : ℂ) * Complex.exp (p.2 * Complex.I) := by fun_prop
  have heq : annulus x₀ r R =
      (fun p : ℝ × ℝ => x₀ + (p.1 : ℂ) * Complex.exp (p.2 * Complex.I)) '' (Ioo r R ×ˢ univ) := by
    ext x
    constructor
    · intro hx
      have h1 : dist x x₀ < R := hx.1
      have h2 : ¬ dist x x₀ ≤ r := hx.2
      refine ⟨(‖x - x₀‖, Complex.arg (x - x₀)), ⟨⟨?_, ?_⟩, mem_univ _⟩, ?_⟩
      · rw [← dist_eq_norm]; exact lt_of_not_ge h2
      · rw [← dist_eq_norm]; exact h1
      · show x₀ + ((‖x - x₀‖ : ℝ) : ℂ) * Complex.exp (((Complex.arg (x - x₀) : ℝ) : ℂ) * Complex.I) = x
        rw [Complex.norm_mul_exp_arg_mul_I]
        ring
    · rintro ⟨⟨s, θ⟩, ⟨hs, -⟩, rfl⟩
      show x₀ + (s : ℂ) * Complex.exp (θ * Complex.I) ∈ annulus x₀ r R
      have hs0 : 0 < s := lt_of_le_of_lt hr hs.1
      have hn : ‖x₀ + (s : ℂ) * Complex.exp (θ * Complex.I) - x₀‖ = s := by
        rw [add_sub_cancel_left, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos hs0]
      refine ⟨?_, ?_⟩
      · rw [mem_ball, dist_eq_norm, hn]; exact hs.2
      · rw [mem_closedBall, dist_eq_norm, hn]; exact not_le.2 hs.1
  rw [heq]
  exact (isPreconnected_Ioo.prod isPreconnected_univ).image _ hf.continuousOn

/-- (VG-i)-type ratio bounds force `0 < Y < ∞`, `0 < M < ∞`, `lo Y ≤ M ≤ hi Y`. -/
theorem ratio_facts {M Y : ℝ≥0∞} {lo hi : ℝ} (hlo : 0 < lo)
    (h : M / Y ∈ Icc (ENNReal.ofReal lo) (ENNReal.ofReal hi)) :
    Y ≠ 0 ∧ Y ≠ ⊤ ∧ M ≠ 0 ∧ M ≠ ⊤ ∧ ENNReal.ofReal lo * Y ≤ M ∧ M ≤ ENNReal.ofReal hi * Y := by
  have hl : ENNReal.ofReal lo ≠ 0 := (ENNReal.ofReal_pos.2 hlo).ne'
  have hYt : Y ≠ ⊤ := by
    rintro rfl
    rw [ENNReal.div_top] at h
    exact hl (le_zero_iff.1 h.1)
  have hM0 : M ≠ 0 := by
    rintro rfl
    rw [ENNReal.zero_div] at h
    exact hl (le_zero_iff.1 h.1)
  have hY0 : Y ≠ 0 := by
    rintro rfl
    rw [ENNReal.div_zero hM0] at h
    exact ENNReal.ofReal_ne_top (top_le_iff.1 h.2)
  have hMt : M ≠ ⊤ := by
    rintro rfl
    rw [ENNReal.top_div_of_ne_top hYt] at h
    exact ENNReal.ofReal_ne_top (top_le_iff.1 h.2)
  exact ⟨hY0, hYt, hM0, hMt, (ENNReal.le_div_iff_mul_le (Or.inl hY0) (Or.inl hYt)).1 h.1,
    (ENNReal.div_le_iff hY0 hYt).1 h.2⟩

theorem annulus_subset_annulus {x₀ : ℂ} {r₁ r₂ R₁ R₂ : ℝ} (hr : r₂ ≤ r₁) (hR : R₁ ≤ R₂) :
    annulus x₀ r₁ R₁ ⊆ annulus x₀ r₂ R₂ :=
  fun _ hx => ⟨ball_subset_ball hR hx.1, fun h => hx.2 (closedBall_subset_closedBall hr h)⟩

theorem two_inv_pow_rpow (n : ℕ) (β : ℝ) : ((2 : ℝ)⁻¹ ^ n) ^ β = (2 : ℝ) ^ (-((n : ℝ) * β)) := by
  rw [inv_pow, Real.inv_rpow (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
    Real.rpow_neg (by norm_num)]

theorem shellScale_rpow (N₀ j : ℕ) (β : ℝ) :
    shellScale N₀ j ^ β = (2 : ℝ) ^ (-(((N₀ : ℝ) + j) * β)) := by
  simp only [shellScale, dyadicScale, two_inv_pow_rpow, Nat.cast_add]

theorem shellOuterRadius_le {ρ : ℝ} (hρ : 0 < ρ) (j : ℕ) : shellOuterRadius ρ j ≤ 7 / 8 * ρ := by
  have h1 := shellRadius_le hρ j
  have h2 := shellWidth_le hρ j
  have h3 : ρ * (2 : ℝ)⁻¹ ^ 50 ≤ ρ / 2 ^ 40 := by
    have : (2 : ℝ)⁻¹ ^ 50 ≤ 1 / 2 ^ 40 := by norm_num
    calc ρ * (2 : ℝ)⁻¹ ^ 50 ≤ ρ * (1 / 2 ^ 40) := mul_le_mul_of_nonneg_left this hρ.le
      _ = ρ / 2 ^ 40 := by ring
  rw [shellOuterRadius]
  linarith

theorem le_shellOuterRadius {ρ : ℝ} (hρ : 0 < ρ) (j : ℕ) :
    3 / 4 * ρ - 224 * (ρ * (2 : ℝ)⁻¹ ^ 50) ≤ shellOuterRadius ρ j := by
  rw [shellOuterRadius]
  linarith [shellRadius_ge hρ j, shellWidth_pos hρ j]

/-- The deterministic core of Lemma 6.11 (lines 1828-1949), for one sample of the field. -/
theorem harnack_core {μ : Measure ℂ} {β : ℝ} (hβ : 0 < β) {z x₀ : ℂ} {t ρ : ℝ} (hρ : 0 < ρ)
    (hball : closedBall x₀ ρ ⊆ ball 0 1 \ {z})
    {Λ : Set ℂ} (hΛ : Λ ∈ connectedComponentsIn (cluster μ 1 z t ∩ ball x₀ ρ))
    {N₀ : ℕ} {a b C₁m C₁p C₂m C₂p C₃ C' C₄ c α : ℝ}
    (ha : 0 < a) (h1m : 0 < C₁m) (hC₄ : 0 < C₄) (hc : 0 < c) (h2p : 0 < C₂p)
    (hv1 : annulusBallMassSize μ β ρ x₀ / μ (annulus x₀ (ρ / 4) (2 * ρ)) ∈
      Icc (ENNReal.ofReal C₁m) (ENNReal.ofReal C₁p))
    (hv2 : annulusGreenPotentialSup μ x₀ (ρ / 4) (2 * ρ) / μ (annulus x₀ (ρ / 4) (2 * ρ)) ∈
      Icc (ENNReal.ofReal C₂m) (ENNReal.ofReal C₂p))
    (hmass : μ (Λ ∩ annulus x₀ (ρ / 2) ρ) ≤ ENNReal.ofReal α * μ (annulus x₀ (ρ / 2) ρ))
    (hα1 : α ≤ a * (2 : ℝ) ^ (-((N₀ : ℝ) * β)) * C₁m) (hα2 : α < C₁m * (8 : ℝ) ^ (-β)) (hα0 : 0 ≤ α)
    (hbpow : ∀ j : ℕ, b ^ (C' * C₃ * ((N₀ : ℝ) + j)) = (2 : ℝ) ^ (-(2 * β * ((N₀ : ℝ) + j))))
    (hb0 : 0 ≤ b)
    (hN₀ : max C₄ 1 * (2 : ℝ) ^ (-(2 * β * N₀)) * c * C₂p / C₁m ≤
      a * (2 : ℝ) ^ (-(((N₀ : ℝ) + 1) * β)))
    (h68 : ∀ r : ℝ, 0 < r → ∀ w : ℂ, annulus w r (7 * r) ⊆ ball 0 1 → z ∉ annulus w r (7 * r) →
      ∀ Λ' : Set ℂ, Λ' ⊆ annulus w r (7 * r) ∩ cluster μ 1 z t →
      (∀ x ∈ Λ', connectedComponentIn (annulus w r (7 * r) ∩ cluster μ 1 z t) x ⊆ Λ') →
      μ (annulus w (3 * r) (5 * r) ∩ Λ') ≤ ENNReal.ofReal C₄ * ⨆ x ∈ Λ', odometerExt μ z t x)
    (h610 : ((cluster μ 1 z t)ᶜ ∩ annulus x₀ (ρ / 2) (7 / 8 * ρ)).Nonempty →
      ⨆ x ∈ annulus x₀ (ρ / 2) (7 / 8 * ρ), odometerExt μ z t x ≤
        ENNReal.ofReal c * annulusGreenPotentialSup μ x₀ (ρ / 4) ρ)
    (hE : annulusGreenPotentialSup μ x₀ (ρ / 4) ρ ≤ annulusGreenPotentialSup μ x₀ (ρ / 4) (2 * ρ))
    (h613 : ∀ j : ℕ, (∀ r : ℝ, 0 < r → ∀ w ∈ ball (0 : ℂ) 1,
        annulus w r (7 * r) ⊆ annulus x₀ (ρ / 2) (shellOuterRadius ρ j) →
        μ (Λ ∩ annulus w (3 * r) (5 * r)) ≤
          ENNReal.ofReal a * annulusBallMassSize μ β ρ x₀ * ENNReal.ofReal (shellScale N₀ j ^ β)) →
      ⨆ x ∈ Λ ∩ annulus x₀ (ρ / 2) (shellOuterRadius ρ (j + 1)), odometerExt μ z t x ≤
        ENNReal.ofReal (b ^ (C' * C₃ * ((N₀ : ℝ) + j))) *
          ⨆ x ∈ Λ ∩ annulus x₀ (ρ / 2) (shellOuterRadius ρ j), odometerExt μ z t x)
    (hD : ∀ d ∈ Ioo (ρ / 2) ρ, Λ ∩ annulus x₀ (ρ / 2) d = ∅ → Λ ∩ closedBall x₀ (ρ / 2) = ∅) :
    Λ ∩ closedBall x₀ (ρ / 2) = ∅ := by
  set M := annulusBallMassSize μ β ρ x₀ with hMdef
  set A' := annulus x₀ (ρ / 4) (2 * ρ) with hA'def
  obtain ⟨hY0, hYt, hM0, hMt, hMlo, -⟩ := ratio_facts h1m hv1
  have hSG : annulusGreenPotentialSup μ x₀ (ρ / 4) (2 * ρ) ≤ ENNReal.ofReal C₂p * μ A' :=
    (ENNReal.div_le_iff hY0 hYt).1 hv2.2
  have hΛsub : Λ ⊆ cluster μ 1 z t ∩ ball x₀ ρ := by
    obtain ⟨y, -, rfl⟩ := hΛ; exact connectedComponentIn_subset _ _
  have hΛeq : ∀ x ∈ Λ, connectedComponentIn (cluster μ 1 z t ∩ ball x₀ ρ) x = Λ := by
    obtain ⟨y, -, rfl⟩ := hΛ; intro x hx; exact (connectedComponentIn_eq hx).symm
  have hzB : z ∉ closedBall x₀ ρ := fun h => (hball h).2 rfl
  have hB1 : ball x₀ ρ ⊆ ball 0 1 := fun x hx => (hball (ball_subset_closedBall hx)).1
  have hAA : annulus x₀ (ρ / 2) ρ ⊆ A' := annulus_subset_annulus (by linarith) (by linarith)
  have hC4' : 0 < max C₄ 1 := lt_max_of_lt_right one_pos
  -- the case `𝔸_{ρ/2,7ρ/8}(x₀) ⊆ Λ^z_t`
  by_cases hne : ((cluster μ 1 z t)ᶜ ∩ annulus x₀ (ρ / 2) (7 / 8 * ρ)).Nonempty
  swap
  · by_contra hcon
    have hmeet : (Λ ∩ annulus x₀ (ρ / 2) (7 / 8 * ρ)).Nonempty := by
      by_contra h
      exact hcon (hD (7 / 8 * ρ) ⟨by linarith, by linarith⟩ (not_nonempty_iff_eq_empty.1 h))
    obtain ⟨x, hxΛ, hxA⟩ := hmeet
    have hAcl : annulus x₀ (ρ / 2) (7 / 8 * ρ) ⊆ cluster μ 1 z t :=
      fun y hy => by_contra fun h => hne ⟨y, h, hy⟩
    have hAsub : annulus x₀ (ρ / 2) (7 / 8 * ρ) ⊆ Λ := by
      rw [← hΛeq x hxΛ]
      exact (isPreconnected_annulus x₀ (by linarith) _).subset_connectedComponentIn hxA
        fun y hy => ⟨hAcl hy, ball_subset_ball (by linarith) hy.1⟩
    set y : ℂ := x₀ + ((11 / 16 * ρ : ℝ) : ℂ) with hy_def
    have hyd : dist y x₀ = 11 / 16 * ρ := by
      rw [hy_def, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
    have hBy : ball y (ρ / 8) ⊆ annulus x₀ (ρ / 2) (7 / 8 * ρ) := by
      intro w hw
      have h1 := mem_ball.1 hw
      have t1 := dist_triangle w y x₀
      have t2 := dist_triangle y w x₀
      rw [dist_comm y w] at t2
      refine ⟨mem_ball.2 (by linarith), fun hc => ?_⟩
      have := mem_closedBall.1 hc
      linarith
    have hyA : y ∈ annulus x₀ (ρ / 2) ρ :=
      ⟨mem_ball.2 (by linarith), fun hc => by have := mem_closedBall.1 hc; linarith⟩
    have hMy : M ≤ μ (ball y (ρ / 8)) / ENNReal.ofReal ((ρ / 8 / ρ) ^ β) :=
      iInf₂_le_of_le y hyA (iInf₂_le (ρ / 8) ⟨by positivity, by linarith⟩)
    have hpow : (ρ / 8 / ρ) ^ β = (8 : ℝ) ^ (-β) := by
      rw [show ρ / 8 / ρ = (8 : ℝ)⁻¹ by field_simp [hρ.ne'], Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num)]
    rw [hpow] at hMy
    have h8 : ENNReal.ofReal ((8 : ℝ) ^ (-β)) ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
    have hMy' : M * ENNReal.ofReal ((8 : ℝ) ^ (-β)) ≤ μ (ball y (ρ / 8)) :=
      (ENNReal.le_div_iff_mul_le (Or.inl h8) (Or.inl ENNReal.ofReal_ne_top)).1 hMy
    have hball_sub : ball y (ρ / 8) ⊆ Λ ∩ annulus x₀ (ρ / 2) ρ :=
      fun w hw => ⟨hAsub (hBy hw), annulus_subset_annulus le_rfl (by linarith) (hBy hw)⟩
    have hlow : ENNReal.ofReal (C₁m * (8 : ℝ) ^ (-β)) * μ (annulus x₀ (ρ / 2) ρ) ≤
        μ (Λ ∩ annulus x₀ (ρ / 2) ρ) := by
      calc ENNReal.ofReal (C₁m * (8 : ℝ) ^ (-β)) * μ (annulus x₀ (ρ / 2) ρ)
          ≤ ENNReal.ofReal (C₁m * (8 : ℝ) ^ (-β)) * μ A' := mul_le_mul_right (measure_mono hAA) _
        _ = ENNReal.ofReal C₁m * μ A' * ENNReal.ofReal ((8 : ℝ) ^ (-β)) := by
            rw [ENNReal.ofReal_mul h1m.le]; ring
        _ ≤ M * ENNReal.ofReal ((8 : ℝ) ^ (-β)) := mul_le_mul_left hMlo _
        _ ≤ μ (ball y (ρ / 8)) := hMy'
        _ ≤ μ (Λ ∩ annulus x₀ (ρ / 2) ρ) := measure_mono hball_sub
    have hpos : μ (annulus x₀ (ρ / 2) ρ) ≠ 0 := by
      intro h0
      have : μ (ball y (ρ / 8)) = 0 :=
        le_zero_iff.1 ((measure_mono (hball_sub.trans inter_subset_right)).trans h0.le)
      rw [this] at hMy'
      exact (mul_ne_zero hM0 h8) (le_zero_iff.1 hMy')
    have hfin : μ (annulus x₀ (ρ / 2) ρ) ≠ ⊤ := ne_top_of_le_ne_top hYt (measure_mono hAA)
    have h1 := (ENNReal.mul_le_mul_iff_left hpos hfin).1 (hlow.trans hmass)
    have h2 := (ENNReal.ofReal_le_ofReal_iff hα0).1 h1
    linarith
  -- the main case: the iteration of Lemmas 6.13 and 6.8
  set C₄' := max C₄ 1 with hC4'def
  set V : ℕ → ℝ≥0∞ := fun j =>
    ⨆ x ∈ Λ ∩ annulus x₀ (ρ / 2) (shellOuterRadius ρ j), odometerExt μ z t x with hVdef
  obtain ⟨k, hk⟩ : ∃ k : ℕ → ℝ, ∀ j, k j = a * shellScale N₀ j ^ β := ⟨_, fun _ => rfl⟩
  have hk' : ∀ j, k j = a * (2 : ℝ) ^ (-(((N₀ : ℝ) + j) * β)) := fun j => by rw [hk, shellScale_rpow]
  have hkpos : ∀ j, 0 ≤ k j := fun j => by rw [hk']; positivity
  have hKform : ∀ j, ENNReal.ofReal a * M * ENNReal.ofReal (shellScale N₀ j ^ β) =
      ENNReal.ofReal (k j) * M := fun j => by
    rw [hk, ENNReal.ofReal_mul ha.le]; ring
  have hsub_ρ : ∀ j, annulus x₀ (ρ / 2) (shellOuterRadius ρ j) ⊆ annulus x₀ (ρ / 2) ρ :=
    fun j => annulus_subset_annulus le_rfl (by linarith [shellOuterRadius_le hρ j])
  have hann : ∀ (w : ℂ) (r : ℝ), 0 < r → annulus w (3 * r) (5 * r) ⊆ annulus w r (7 * r) :=
    fun w r hr => annulus_subset_annulus (by linarith) (by linarith)
  have hV0 : V 0 ≤ ENNReal.ofReal c * (ENNReal.ofReal C₂p * μ A') := by
    refine le_trans ?_ ((h610 hne).trans (mul_le_mul_right (hE.trans hSG) _))
    exact biSup_mono fun x hx =>
      annulus_subset_annulus le_rfl (shellOuterRadius_le hρ 0) hx.2
  have hmass0 : ∀ r : ℝ, 0 < r → ∀ w ∈ ball (0 : ℂ) 1,
      annulus w r (7 * r) ⊆ annulus x₀ (ρ / 2) (shellOuterRadius ρ 0) →
      μ (Λ ∩ annulus w (3 * r) (5 * r)) ≤ ENNReal.ofReal a * M * ENNReal.ofReal (shellScale N₀ 0 ^ β) := by
    intro r hr w _ hsub
    rw [hKform, hk']
    calc μ (Λ ∩ annulus w (3 * r) (5 * r)) ≤ μ (Λ ∩ annulus x₀ (ρ / 2) ρ) :=
          measure_mono (inter_subset_inter_right _ ((hann w r hr).trans (hsub.trans (hsub_ρ 0))))
      _ ≤ ENNReal.ofReal α * μ (annulus x₀ (ρ / 2) ρ) := hmass
      _ ≤ ENNReal.ofReal α * μ A' := mul_le_mul_right (measure_mono hAA) _
      _ ≤ ENNReal.ofReal (a * (2 : ℝ) ^ (-((N₀ : ℝ) * β))) * (ENNReal.ofReal C₁m * μ A') := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
          gcongr
      _ ≤ ENNReal.ofReal (a * (2 : ℝ) ^ (-((N₀ : ℝ) * β))) * M := mul_le_mul_right hMlo _
      _ = ENNReal.ofReal (a * (2 : ℝ) ^ (-(((N₀ : ℝ) + ((0 : ℕ) : ℝ)) * β))) * M := by norm_num
  have hmass_succ : ∀ j : ℕ, ENNReal.ofReal C₄' * V (j + 1) ≤ ENNReal.ofReal (k (j + 1)) * M →
      ∀ r : ℝ, 0 < r → ∀ w ∈ ball (0 : ℂ) 1,
      annulus w r (7 * r) ⊆ annulus x₀ (ρ / 2) (shellOuterRadius ρ (j + 1)) →
      μ (Λ ∩ annulus w (3 * r) (5 * r)) ≤
        ENNReal.ofReal a * M * ENNReal.ofReal (shellScale N₀ (j + 1) ^ β) := by
    intro j hj r hr w _ hsub
    rw [hKform]
    have hAB : annulus w r (7 * r) ⊆ ball x₀ ρ := (hsub.trans (hsub_ρ _)).trans sdiff_subset
    have hcomp : ∀ x ∈ annulus w r (7 * r) ∩ Λ,
        connectedComponentIn (annulus w r (7 * r) ∩ cluster μ 1 z t) x ⊆ annulus w r (7 * r) ∩ Λ := by
      intro x hx
      have hC := isPreconnected_connectedComponentIn (F := annulus w r (7 * r) ∩ cluster μ 1 z t) (x := x)
      have hxC : x ∈ connectedComponentIn (annulus w r (7 * r) ∩ cluster μ 1 z t) x :=
        mem_connectedComponentIn ⟨hx.1, (hΛsub hx.2).1⟩
      have hCsub := connectedComponentIn_subset (annulus w r (7 * r) ∩ cluster μ 1 z t) x
      intro y hy
      refine ⟨(hCsub hy).1, ?_⟩
      rw [← hΛeq x hx.2]
      exact hC.subset_connectedComponentIn (F := cluster μ 1 z t ∩ ball x₀ ρ) hxC
        (fun y (hy : y ∈ connectedComponentIn (annulus w r (7 * r) ∩ cluster μ 1 z t) x) =>
          (⟨(hCsub hy).2, hAB (hCsub hy).1⟩ : y ∈ cluster μ 1 z t ∩ ball x₀ ρ)) hy
    have h1 := h68 r hr w (hAB.trans hB1) (fun hz => hzB (ball_subset_closedBall (hAB hz)))
      (annulus w r (7 * r) ∩ Λ) (fun x hx => ⟨hx.1, (hΛsub hx.2).1⟩) hcomp
    calc μ (Λ ∩ annulus w (3 * r) (5 * r)) ≤ μ (annulus w (3 * r) (5 * r) ∩ (annulus w r (7 * r) ∩ Λ)) :=
          measure_mono fun x (hx : x ∈ Λ ∩ annulus w (3 * r) (5 * r)) =>
            (⟨hx.2, hann w r hr hx.2, hx.1⟩ : x ∈ annulus w (3 * r) (5 * r) ∩ (annulus w r (7 * r) ∩ Λ))
      _ ≤ ENNReal.ofReal C₄ * ⨆ x ∈ annulus w r (7 * r) ∩ Λ, odometerExt μ z t x := h1
      _ ≤ ENNReal.ofReal C₄' * V (j + 1) :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_left _ _))
            (biSup_mono fun x hx => ⟨hx.2, hsub hx.1⟩)
      _ ≤ ENNReal.ofReal (k (j + 1)) * M := hj
  have hP : ∀ j : ℕ, ENNReal.ofReal C₄' * V (j + 1) ≤ ENNReal.ofReal (k (j + 1)) * M := by
    intro j
    induction j with
    | zero =>
      have h1 := h613 0 hmass0
      have hμA : μ A' ≤ ENNReal.ofReal (1 / C₁m) * M := by
        calc μ A' = ENNReal.ofReal (1 / C₁m * C₁m) * μ A' := by
              rw [one_div_mul_cancel h1m.ne', ENNReal.ofReal_one, one_mul]
          _ = ENNReal.ofReal (1 / C₁m) * (ENNReal.ofReal C₁m * μ A') := by
              rw [ENNReal.ofReal_mul (by positivity), mul_assoc]
          _ ≤ ENNReal.ofReal (1 / C₁m) * M := mul_le_mul_right hMlo _
      have hreal : C₄' * (2 : ℝ) ^ (-(2 * β * ((N₀ : ℝ) + ((0 : ℕ) : ℝ)))) * c * C₂p * (1 / C₁m) ≤
          k (0 + 1) := by
        have e1 : (2 : ℝ) ^ (-(2 * β * ((N₀ : ℝ) + ((0 : ℕ) : ℝ)))) = (2 : ℝ) ^ (-(2 * β * N₀)) := by norm_num
        have e2 : k (0 + 1) = a * (2 : ℝ) ^ (-(((N₀ : ℝ) + 1) * β)) := by rw [hk']; norm_num
        rw [e1, e2, mul_one_div]
        exact hN₀
      calc ENNReal.ofReal C₄' * V (0 + 1) ≤
          ENNReal.ofReal C₄' * (ENNReal.ofReal (b ^ (C' * C₃ * ((N₀ : ℝ) + ((0 : ℕ) : ℝ)))) * V 0) :=
            mul_le_mul_right h1 _
        _ ≤ ENNReal.ofReal C₄' * (ENNReal.ofReal ((2 : ℝ) ^ (-(2 * β * ((N₀ : ℝ) + ((0 : ℕ) : ℝ))))) *
            (ENNReal.ofReal c * (ENNReal.ofReal C₂p * (ENNReal.ofReal (1 / C₁m) * M)))) := by
            rw [hbpow]; gcongr; exact hV0.trans (by gcongr)
        _ = ENNReal.ofReal (C₄' * (2 : ℝ) ^ (-(2 * β * ((N₀ : ℝ) + ((0 : ℕ) : ℝ)))) * c * C₂p *
            (1 / C₁m)) * M := by
            rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
              ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
            ring
        _ ≤ ENNReal.ofReal (k (0 + 1)) * M := mul_le_mul_left (ENNReal.ofReal_le_ofReal hreal) _
    | succ j ih =>
      have h1 := h613 (j + 1) (hmass_succ j ih)
      have hbj : 0 ≤ b ^ (C' * C₃ * ((N₀ : ℝ) + ((j + 1 : ℕ) : ℝ))) := Real.rpow_nonneg hb0 _
      have hreal : b ^ (C' * C₃ * ((N₀ : ℝ) + ((j + 1 : ℕ) : ℝ))) * k (j + 1) ≤ k (j + 1 + 1) := by
        have h2 : (2 : ℝ) ^ (-(2 * β * ((N₀ : ℝ) + ((j + 1 : ℕ) : ℝ)))) ≤ (2 : ℝ) ^ (-β) := by
          refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
          push_cast
          nlinarith [mul_nonneg hβ.le (Nat.cast_nonneg (α := ℝ) N₀),
            mul_nonneg hβ.le (Nat.cast_nonneg (α := ℝ) j)]
        have e : k (j + 1 + 1) = (2 : ℝ) ^ (-β) * k (j + 1) := by
          rw [hk', hk', mul_left_comm, ← Real.rpow_add (by norm_num)]
          congr 2
          push_cast
          ring
        rw [hbpow, e]
        exact mul_le_mul_of_nonneg_right h2 (hkpos _)
      calc ENNReal.ofReal C₄' * V (j + 1 + 1) ≤
          ENNReal.ofReal C₄' * (ENNReal.ofReal (b ^ (C' * C₃ * ((N₀ : ℝ) + ((j + 1 : ℕ) : ℝ)))) *
            V (j + 1)) := mul_le_mul_right h1 _
        _ = ENNReal.ofReal (b ^ (C' * C₃ * ((N₀ : ℝ) + ((j + 1 : ℕ) : ℝ)))) *
            (ENNReal.ofReal C₄' * V (j + 1)) := by ring
        _ ≤ ENNReal.ofReal (b ^ (C' * C₃ * ((N₀ : ℝ) + ((j + 1 : ℕ) : ℝ)))) *
            (ENNReal.ofReal (k (j + 1)) * M) := mul_le_mul_right ih _
        _ = ENNReal.ofReal (b ^ (C' * C₃ * ((N₀ : ℝ) + ((j + 1 : ℕ) : ℝ))) * k (j + 1)) * M := by
            rw [ENNReal.ofReal_mul hbj]; ring
        _ ≤ ENNReal.ofReal (k (j + 1 + 1)) * M := mul_le_mul_left (ENNReal.ofReal_le_ofReal hreal) _
  -- conclusion: the odometer vanishes on `Λ̃_t ∩ 𝔸_{ρ/2,d}(x₀)`
  have hL : ρ * (2 : ℝ)⁻¹ ^ 50 ≤ ρ / 2 ^ 40 := by
    have : (2 : ℝ)⁻¹ ^ 50 ≤ 1 / 2 ^ 40 := by norm_num
    calc ρ * (2 : ℝ)⁻¹ ^ 50 ≤ ρ * (1 / 2 ^ 40) := mul_le_mul_of_nonneg_left this hρ.le
      _ = ρ / 2 ^ 40 := by ring
  have hL0 : 0 ≤ ρ * (2 : ℝ)⁻¹ ^ 50 := by positivity
  refine hD (3 / 4 * ρ - 224 * (ρ * (2 : ℝ)⁻¹ ^ 50)) ⟨by linarith, by linarith⟩
    (eq_empty_iff_forall_notMem.2 fun x hx => ?_)
  obtain ⟨hxΛ, hxA⟩ := hx
  have hxj : ∀ j : ℕ, ENNReal.ofReal C₄' * odometerExt μ z t x ≤ ENNReal.ofReal (k (j + 1)) * M := by
    intro j
    refine le_trans (mul_le_mul_right ?_ _) (hP j)
    exact le_iSup₂_of_le (f := fun x (_ : x ∈ Λ ∩ annulus x₀ (ρ / 2) (shellOuterRadius ρ (j + 1))) =>
      odometerExt μ z t x) x ⟨hxΛ, annulus_subset_annulus le_rfl (le_shellOuterRadius hρ (j + 1)) hxA⟩ le_rfl
  have hlim : Tendsto (fun j : ℕ => ENNReal.ofReal (k (j + 1)) * M) atTop (𝓝 0) := by
    have hs : Tendsto (fun j : ℕ => shellScale N₀ (j + 1)) atTop (𝓝 0) := by
      simp only [shellScale, dyadicScale]
      exact (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
        (tendsto_atTop_mono (f := id) (g := fun j : ℕ => N₀ + (j + 1))
          (fun j => show j ≤ N₀ + (j + 1) by omega) tendsto_id)
    have hs' : Tendsto (fun j : ℕ => shellScale N₀ (j + 1) ^ β) atTop (𝓝 0) := by
      have := (Real.continuousAt_rpow_const 0 β (Or.inr hβ.le)).tendsto.comp hs
      rwa [Real.zero_rpow hβ.ne'] at this
    have hq : Tendsto (fun j : ℕ => k (j + 1)) atTop (𝓝 0) := by
      simp_rw [hk]
      simpa using hs'.const_mul a
    have := ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal hq) (Or.inr hMt)
    simpa using this
  have h0 : ENNReal.ofReal C₄' * odometerExt μ z t x ≤ 0 := ge_of_tendsto' hlim hxj
  have hx0 : odometerExt μ z t x = 0 :=
    (mul_eq_zero.1 (le_zero_iff.1 h0)).resolve_left (ENNReal.ofReal_pos.2 hC4').ne'
  have hxB : x ∈ ball x₀ ρ := (hΛsub hxΛ).2
  have hxz : x ≠ z := fun h => hzB (h ▸ ball_subset_closedBall hxB)
  simp only [odometerExt, hxz, ↓reduceIte, ENNReal.ofReal_eq_zero] at hx0
  have hcl := ((hΛsub hxΛ).1).2.resolve_left hxz
  rw [odometer] at hx0
  linarith

end Section6

/-- **Lemma 6.11** (printed order, `b`, `N₁`, `α` chosen before `α₀`) from Lemmas 6.8, 6.10, 6.13,
the shell decomposition (Lemma 6.12, proved), the maximum principle on components and domain monotonicity of `SG`. -/
theorem veryGoodAnnulusHarnackTypeStmt_of_lemmas (h68 : AnnulusMassBoundByOdometerStmt.{u})
    (h610 : OdometerBoundByAnnulusMassStmt.{u}) (h613 : LowMassSmallOdometerStmt.{u})
    (hD : ClusterComponentInnerBallStep.{u}) (hE : GreenPotentialSupMonoStep) :
    VeryGoodAnnulusHarnackTypeStmt.{u} := by
  obtain ⟨C', hC', h613⟩ := h613
  obtain ⟨C₄, hC₄, h68⟩ := h68 1 3 5 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨c, hc, h610⟩ := h610 (1 / 4) (1 / 2) (7 / 8) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  intro γ hγ hγ2 β hβ C₃ hC₃
  have hβ0 : 0 < β := lt_of_le_of_lt (by positivity) hβ
  have hCC : 0 < C' * C₃ := mul_pos hC' hC₃
  set b : ℝ := (2 : ℝ) ^ (-(2 * β) / (C' * C₃)) with hb_def
  have hb0 : 0 < b := Real.rpow_pos_of_pos (by norm_num) _
  have hb1 : b < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (div_neg_of_neg_of_pos (by linarith) hCC)
  have hbpow : ∀ (N₀ : ℕ) (j : ℕ), b ^ (C' * C₃ * ((N₀ : ℝ) + j)) = (2 : ℝ) ^ (-(2 * β * ((N₀ : ℝ) + j))) := by
    intro N₀ j
    rw [hb_def, ← Real.rpow_mul (by norm_num)]
    congr 1
    rw [div_mul_eq_mul_div, div_eq_iff hCC.ne']
    ring
  set θ : ℝ → ℝ → ℝ → ℝ := fun a C₁m C₂p => a * (2 : ℝ) ^ (-β) * C₁m / (max C₄ 1 * c * C₂p) with hθ
  set N₁f : ℝ → ℝ → ℝ → ℕ := fun a C₁m C₂p =>
    max 200 ⌈-Real.log (θ a C₁m C₂p) / (β * Real.log 2)⌉₊ with hN₁f
  set αf : ℝ → ℕ → ℝ → ℝ := fun a N₀ C₁m =>
    a * (2 : ℝ) ^ (-((N₀ : ℝ) * β)) * min C₁m 1 * (8 : ℝ) ^ (-β) / 2 with hαf
  have h8le : (8 : ℝ) ^ (-β) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have h2le : ∀ N₀ : ℕ, (2 : ℝ) ^ (-((N₀ : ℝ) * β)) ≤ 1 := fun N₀ =>
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by nlinarith [Nat.cast_nonneg (α := ℝ) N₀])
  have hαprop : ∀ a ∈ Ioo (0 : ℝ) 1, ∀ C₁m : ℝ, 0 < C₁m → ∀ N₀ : ℕ,
      0 < αf a N₀ C₁m ∧ αf a N₀ C₁m < 1 ∧ αf a N₀ C₁m ≤ a * (2 : ℝ) ^ (-((N₀ : ℝ) * β)) * C₁m ∧
      αf a N₀ C₁m < C₁m * (8 : ℝ) ^ (-β) := by
    intro a ha C₁m h1m N₀
    have ha0 := ha.1
    have hm0 : 0 < min C₁m 1 := lt_min h1m one_pos
    have hm1 : min C₁m 1 ≤ C₁m := min_le_left _ _
    have hm2 : min C₁m 1 ≤ 1 := min_le_right _ _
    have h2p : 0 < (2 : ℝ) ^ (-((N₀ : ℝ) * β)) := by positivity
    have h8p : 0 < (8 : ℝ) ^ (-β) := by positivity
    have hA : a * (2 : ℝ) ^ (-((N₀ : ℝ) * β)) < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_right ha.1.le (h2le N₀)) ha.2
    have hA0 : 0 < a * (2 : ℝ) ^ (-((N₀ : ℝ) * β)) := mul_pos ha.1 h2p
    simp only [hαf]
    have hA' := hA.le
    refine ⟨by positivity, ?_, ?_, ?_⟩
    · have : a * (2 : ℝ) ^ (-((N₀ : ℝ) * β)) * min C₁m 1 * (8 : ℝ) ^ (-β) ≤
          a * (2 : ℝ) ^ (-((N₀ : ℝ) * β)) := by
        calc a * (2 : ℝ) ^ (-((N₀ : ℝ) * β)) * min C₁m 1 * (8 : ℝ) ^ (-β) ≤
            a * (2 : ℝ) ^ (-((N₀ : ℝ) * β)) * 1 * 1 := by gcongr
          _ = a * (2 : ℝ) ^ (-((N₀ : ℝ) * β)) := by ring
      linarith
    · have h1 : min C₁m 1 * (8 : ℝ) ^ (-β) / 2 ≤ C₁m := by
        calc min C₁m 1 * (8 : ℝ) ^ (-β) / 2 ≤ C₁m * 1 / 2 := by gcongr
          _ ≤ C₁m := by linarith
      calc a * (2 : ℝ) ^ (-((N₀ : ℝ) * β)) * min C₁m 1 * (8 : ℝ) ^ (-β) / 2
          = a * (2 : ℝ) ^ (-((N₀ : ℝ) * β)) * (min C₁m 1 * (8 : ℝ) ^ (-β) / 2) := by ring
        _ ≤ a * (2 : ℝ) ^ (-((N₀ : ℝ) * β)) * C₁m := by gcongr
    · calc a * (2 : ℝ) ^ (-((N₀ : ℝ) * β)) * min C₁m 1 * (8 : ℝ) ^ (-β) / 2
          ≤ 1 * C₁m * (8 : ℝ) ^ (-β) / 2 := by gcongr
        _ < C₁m * (8 : ℝ) ^ (-β) := by have := mul_pos h1m h8p; linarith
  have hN₁prop : ∀ a ∈ Ioo (0 : ℝ) 1, ∀ C₁m C₂p : ℝ, 0 < C₁m → 0 < C₂p → ∀ N₀ : ℕ, N₁f a C₁m C₂p ≤ N₀ →
      max C₄ 1 * (2 : ℝ) ^ (-(2 * β * N₀)) * c * C₂p / C₁m ≤ a * (2 : ℝ) ^ (-(((N₀ : ℝ) + 1) * β)) := by
    intro a ha C₁m C₂p h1m h2p N₀ hN₀
    have hC4' : 0 < max C₄ 1 := lt_max_of_lt_right one_pos
    have hθpos : 0 < θ a C₁m C₂p := by simp only [hθ]; have := ha.1; positivity
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hc' : ⌈-Real.log (θ a C₁m C₂p) / (β * Real.log 2)⌉₊ ≤ N₀ := (le_max_right 200 _).trans hN₀
    have hceil : -Real.log (θ a C₁m C₂p) / (β * Real.log 2) ≤ N₀ :=
      (Nat.le_ceil _).trans (by exact_mod_cast hc')
    have hX : (2 : ℝ) ^ (-(β * N₀)) ≤ θ a C₁m C₂p := by
      rw [Real.rpow_def_of_pos (by norm_num), ← Real.exp_log hθpos]
      refine Real.exp_le_exp.2 ?_
      rw [div_le_iff₀ (mul_pos hβ0 hlog2)] at hceil
      nlinarith
    have e1 : (2 : ℝ) ^ (-(2 * β * N₀)) = (2 : ℝ) ^ (-(β * N₀)) * (2 : ℝ) ^ (-(β * N₀)) := by
      rw [← Real.rpow_add (by norm_num)]; congr 1; ring
    have e2 : (2 : ℝ) ^ (-(((N₀ : ℝ) + 1) * β)) = (2 : ℝ) ^ (-β) * (2 : ℝ) ^ (-(β * N₀)) := by
      rw [← Real.rpow_add (by norm_num)]; congr 1; ring
    have hX0 : 0 ≤ (2 : ℝ) ^ (-(β * N₀)) := by positivity
    have hK : 0 ≤ max C₄ 1 * c * C₂p / C₁m := by positivity
    calc max C₄ 1 * (2 : ℝ) ^ (-(2 * β * N₀)) * c * C₂p / C₁m
        = (max C₄ 1 * c * C₂p / C₁m * (2 : ℝ) ^ (-(β * N₀))) * (2 : ℝ) ^ (-(β * N₀)) := by rw [e1]; ring
      _ ≤ (max C₄ 1 * c * C₂p / C₁m * θ a C₁m C₂p) * (2 : ℝ) ^ (-(β * N₀)) := by gcongr
      _ = a * (2 : ℝ) ^ (-β) * (2 : ℝ) ^ (-(β * N₀)) := by
          simp only [hθ]; field_simp
      _ = a * (2 : ℝ) ^ (-(((N₀ : ℝ) + 1) * β)) := by rw [e2]; ring
  refine ⟨b, ⟨hb0, hb1⟩, N₁f, αf, fun a ha C₁m C₂p h1m _ =>
    ⟨le_max_left _ _, fun N₀ _ => ⟨(hαprop a ha C₁m h1m N₀).1, (hαprop a ha C₁m h1m N₀).2.1⟩⟩, ?_⟩
  intro α₀ hα₀ Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [h68 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ, h610 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ,
    h613 γ α₀ hγ hγ2 hα₀ β hβ Ω P hC hcirc μ hGFF hμ, hD γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ]
    with ω h68ω h610ω h613ω hDω
  intro a ha C₁m C₁p C₂m C₂p h1m _ _ h2p N₀ hN₀ z hz t ht ρ hρ x₀ _ hball hVG Λ hΛ hmass
  obtain ⟨hv1, hv2, hv3⟩ := hVG
  have hN200 : 200 ≤ N₀ := (le_max_left _ _).trans hN₀
  obtain ⟨-, -, hα1, hα2⟩ := hαprop a ha C₁m h1m N₀
  have e2 : (1 / 2 : ℝ) * ρ = ρ / 2 := by ring
  have e4 : (1 / 4 : ℝ) * ρ = ρ / 4 := by ring
  refine harnack_core hβ0 hρ.1 hball hΛ ha.1 h1m hC₄ hc h2p hv1 hv2 hmass hα1 hα2
    (hαprop a ha C₁m h1m N₀).1.le (hbpow N₀) hb0.le (hN₁prop a ha C₁m C₂p h1m h2p N₀ hN₀) ?_ ?_
    (hE (μ ω) x₀ (ρ / 4) ρ (2 * ρ) (by linarith [hρ.1]) (by linarith [hρ.1]) (by linarith [hρ.1]))
    (h613ω z hz t ht a ha b ⟨hb0, hb1⟩ N₀ hN200 C₃ hC₃ ρ hρ.1 x₀ hball
      (fun n hn w hw => hv3 n hn w hw.2 hw.1) Λ hΛ)
    (hDω z hz t ht ρ hρ.1 x₀ hball Λ hΛ)
  · intro r hr w
    have := h68ω z hz t ht r hr w
    rwa [one_mul] at this
  · have := h610ω z hz t ht ρ hρ.1 x₀
    rw [e2, e4, one_mul] at this
    exact this (fun y hy => hball (ball_subset_closedBall hy.1))

end HarmonicBalls

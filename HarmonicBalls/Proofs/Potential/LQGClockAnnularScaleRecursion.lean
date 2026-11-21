import HarmonicBalls.Proofs.Potential.LQGClockAnnularFineFractionalMoment

/-! # Scale recursion for stopped annular occupation moments

A moment profile indexed by the smoothing scale that satisfies a contracting
recursion towards larger scales is bounded uniformly on all small scales. For a
subcritical order, the square decomposition of the half disc, combined with a
logarithmic return factor, has a contracting coefficient.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Set
open scoped ENNReal NNReal Topology
open Filter

namespace HarmonicBalls

/-- A nonnegative profile on smoothing scales that contracts towards larger
scales and is bounded on one scale window is bounded on all smaller scales. -/
theorem le_of_scale_recursion {M : ℝ → ℝ≥0∞} {ρ η : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hη : 0 < η) {A B θ : ℝ≥0∞} (hθ : θ < 1)
    (hrec : ∀ ε, 0 < ε → ε < η → M ε ≤ A + θ * M (ε / ρ))
    (hbase : ∀ ε, η ≤ ε → ε < η / ρ → M ε ≤ B) :
    ∀ ε, 0 < ε → ε < η / ρ → M ε ≤ A * (1 - θ)⁻¹ + B := by
  set K := A * (1 - θ)⁻¹ + B with hK
  have h1 : (1 - θ) ≠ 0 := (tsub_pos_of_lt hθ).ne'
  have h2 : (1 - θ) ≠ ⊤ := ENNReal.sub_ne_top ENNReal.one_ne_top
  have hinv : (1 - θ)⁻¹ = 1 + θ * (1 - θ)⁻¹ := by
    calc
      (1 - θ)⁻¹ = ((1 - θ) + θ) * (1 - θ)⁻¹ := by rw [tsub_add_cancel_of_le hθ.le, one_mul]
      _ = 1 + θ * (1 - θ)⁻¹ := by rw [add_mul, ENNReal.mul_inv_cancel h1 h2]
  have hstep : A + θ * K ≤ K := by
    calc
      A + θ * K = A * (1 + θ * (1 - θ)⁻¹) + θ * B := by
        rw [hK]
        ring
      _ = A * (1 - θ)⁻¹ + θ * B := by rw [← hinv]
      _ ≤ K := by
        rw [hK]
        exact add_le_add le_rfl (mul_le_of_le_one_left zero_le hθ.le)
  have hBK : B ≤ K := le_add_self
  have hind : ∀ n : ℕ, ∀ ε, η * ρ ^ n ≤ ε → ε < η / ρ → M ε ≤ K := by
    intro n
    induction n with
    | zero =>
      intro ε hε hε2
      simp only [pow_zero, mul_one] at hε
      exact (hbase ε hε hε2).trans hBK
    | succ n ih =>
      intro ε hε hε2
      by_cases hεη : η ≤ ε
      · exact (hbase ε hεη hε2).trans hBK
      · replace hεη : ε < η := not_le.mp hεη
        have hεpos : 0 < ε := lt_of_lt_of_le (by positivity) hε
        have hn : η * ρ ^ n ≤ ε / ρ := by
          rw [le_div_iff₀ hρ, mul_assoc, ← pow_succ]
          exact hε
        have hn2 : ε / ρ < η / ρ := div_lt_div_of_pos_right hεη hρ
        calc
          M ε ≤ A + θ * M (ε / ρ) := hrec ε hεpos hεη
          _ ≤ A + θ * K := by gcongr; exact ih (ε / ρ) hn hn2
          _ ≤ K := hstep
  intro ε hε hε2
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show 0 < ε / η by positivity) hρ1
  apply hind n ε _ hε2
  have := (lt_div_iff₀ hη).mp hn
  linarith [mul_comm η (ρ ^ n)]

/-- For a subcritical order there is a grid scale at which the square
coefficient, multiplied by the logarithmic return factor, is below one half. -/
theorem exists_annular_square_return_coefficient_lt_half {γ q : ℝ}
    (hq : 1 < q) (hγq : q * γ ^ 2 < 4) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 10 ∧
      18 * ((LatticeProb.squareIndex r).card : ℝ) * ((4 * r) ^ 2) ^ q *
        Real.exp (q * (q - 1) * (-γ ^ 2 * Real.log (4 * r)) / 2) *
        ((1 - ((Real.log 2 - Real.log (3 * r / 2)) /
          (Real.log 2 - Real.log r)) ^ (1 / q))⁻¹) ^ q < 1 / 2 := by
  let ζ : ℝ := q * (2 + γ ^ 2 / 2) - q ^ 2 * γ ^ 2 / 2
  have hζ : 0 < ζ - 2 := by
    have heq : ζ - 2 = (q - 1) * (4 - q * γ ^ 2) / 2 := by dsimp [ζ]; ring
    rw [heq]
    apply div_pos (mul_pos (by linarith) (by linarith)) (by norm_num)
  have hq0 : 0 < q := by linarith
  have hl32 : 0 < Real.log (3 / 2) := Real.log_pos (by norm_num)
  let K : ℝ := 4608 * (4 : ℝ) ^ (ζ - 2) * (2 * q / Real.log (3 / 2)) ^ q
  have hK : 0 < K := by positivity
  have hlim : Tendsto (fun L : ℝ => L ^ q * Real.exp (-(ζ - 2) * L)) atTop (𝓝 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero q (ζ - 2) hζ
  obtain ⟨L, hLsmall, hL10⟩ := ((hlim.eventually (gt_mem_nhds
    (show (0 : ℝ) < 1 / (2 * K) by positivity))).and
    (eventually_ge_atTop (Real.log 10))).exists
  have hl2 : Real.log 2 ≤ Real.log 10 := Real.log_le_log (by norm_num) (by norm_num)
  have hl2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : 0 < L := by linarith
  let r : ℝ := Real.exp (-L)
  have hr : 0 < r := Real.exp_pos _
  have hlogr : Real.log r = -L := Real.log_exp _
  have hr10 : r ≤ 1 / 10 := by
    have h10 : Real.exp (-Real.log 10) = 1 / 10 := by
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 10)]
      norm_num
    calc r = Real.exp (-L) := rfl
      _ ≤ Real.exp (-Real.log 10) := Real.exp_le_exp.mpr (by linarith)
      _ = 1 / 10 := h10
  refine ⟨r, hr, hr10, ?_⟩
  set R : ℝ := 4 * r with hRdef
  have hR : 0 < R := by positivity
  have hR1 : R ≤ 1 := by rw [hRdef]; linarith
  -- the square coefficient
  have hN : ((LatticeProb.squareIndex r).card : ℝ) ≤ 256 / R ^ 2 := by
    have hc := LatticeProb.card_squareIndex_le hr (by linarith : r ≤ 1)
    have heq : 16 / r ^ 2 = 256 / R ^ 2 := by rw [hRdef]; field_simp; ring
    rwa [heq] at hc
  have hid : (R ^ 2) ^ q * Real.exp (q * (q - 1) * (-γ ^ 2 * Real.log R) / 2) = R ^ ζ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hR.le]
    rw [Real.rpow_def_of_pos hR, Real.rpow_def_of_pos hR, ← Real.exp_add]
    congr 1
    dsimp [ζ]
    ring
  have hpow : R ^ ζ = R ^ (ζ - 2) * R ^ 2 := by
    rw [← Real.rpow_two, ← Real.rpow_add hR]
    congr 1
    ring
  have hsq : 18 * ((LatticeProb.squareIndex r).card : ℝ) * (R ^ 2) ^ q *
      Real.exp (q * (q - 1) * (-γ ^ 2 * Real.log R) / 2) ≤ 4608 * R ^ (ζ - 2) := by
    calc
      _ = 18 * ((LatticeProb.squareIndex r).card : ℝ) * R ^ ζ := by rw [← hid]; ring
      _ ≤ 18 * (256 / R ^ 2) * R ^ ζ := by gcongr
      _ = 4608 * R ^ (ζ - 2) := by rw [hpow]; field_simp; norm_num
  have hRpow : R ^ (ζ - 2) = (4 : ℝ) ^ (ζ - 2) * Real.exp (-(ζ - 2) * L) := by
    rw [hRdef, Real.mul_rpow (by norm_num) hr.le, Real.rpow_def_of_pos hr, hlogr]
    congr 2
    ring
  -- the return factor
  set t : ℝ := (Real.log 2 - Real.log (3 * r / 2)) / (Real.log 2 - Real.log r) with htdef
  have hden : 0 < Real.log 2 - Real.log r := by rw [hlogr]; linarith
  have hlog32 : Real.log (3 * r / 2) = Real.log (3 / 2) + Real.log r := by
    rw [show 3 * r / 2 = (3 / 2) * r by ring, Real.log_mul (by norm_num) hr.ne']
  have h1t : 1 - t = Real.log (3 / 2) / (Real.log 2 - Real.log r) := by
    rw [htdef]
    field_simp
    rw [hlog32]
    ring
  have ht0 : 0 ≤ t := by
    rw [htdef]
    apply div_nonneg _ hden.le
    rw [hlog32, hlogr]
    have h3 : Real.log (3 / 2) ≤ Real.log 2 := Real.log_le_log (by norm_num) (by norm_num)
    linarith
  have ht1 : 0 < 1 - t := by rw [h1t]; positivity
  have hbern : t ^ (1 / q) ≤ 1 + 1 / q * (t - 1) := by
    have h := rpow_one_add_le_one_add_mul_self (s := t - 1) (by linarith)
      (p := 1 / q) (by positivity) (by rw [div_le_one hq0]; linarith)
    simpa using h
  have hgap : (1 - t) / q ≤ 1 - t ^ (1 / q) := by
    have : 1 / q * (t - 1) = -((1 - t) / q) := by ring
    linarith
  have hgap0 : 0 < (1 - t) / q := by positivity
  have hinv : (1 - t ^ (1 / q))⁻¹ ≤ 2 * q / Real.log (3 / 2) * L := by
    calc
      (1 - t ^ (1 / q))⁻¹ ≤ ((1 - t) / q)⁻¹ := by
        gcongr
      _ = q * (Real.log 2 - Real.log r) / Real.log (3 / 2) := by
        rw [h1t]
        field_simp
      _ ≤ q * (2 * L) / Real.log (3 / 2) := by
        gcongr
        rw [hlogr]
        linarith
      _ = 2 * q / Real.log (3 / 2) * L := by ring
  have hinv0 : 0 ≤ (1 - t ^ (1 / q))⁻¹ := (inv_pos.mpr (lt_of_lt_of_le hgap0 hgap)).le
  have hret : ((1 - t ^ (1 / q))⁻¹) ^ q ≤ (2 * q / Real.log (3 / 2)) ^ q * L ^ q := by
    rw [← Real.mul_rpow (by positivity) hL.le]
    exact Real.rpow_le_rpow hinv0 hinv hq0.le
  have hsq0 : 0 ≤ 18 * ((LatticeProb.squareIndex r).card : ℝ) * (R ^ 2) ^ q *
      Real.exp (q * (q - 1) * (-γ ^ 2 * Real.log R) / 2) := by positivity
  calc
    _ ≤ (4608 * R ^ (ζ - 2)) * ((2 * q / Real.log (3 / 2)) ^ q * L ^ q) :=
      mul_le_mul hsq hret (by positivity) (by positivity)
    _ = K * (L ^ q * Real.exp (-(ζ - 2) * L)) := by rw [hRpow]; ring
    _ < K * (1 / (2 * K)) := mul_lt_mul_of_pos_left hLsmall hK
    _ = 1 / 2 := by field_simp

end HarmonicBalls

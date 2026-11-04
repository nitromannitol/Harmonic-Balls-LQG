import HarmonicBalls.Proofs.Sec10.CrossingPrevalence
import HarmonicBalls.Proofs.Sec7.DyadicInterpolation
import HarmonicBalls.Proofs.Sec7.LatticeApproximation

/-!
# Selecting a good radius in the exact interval

Two distinct powers of one eighth cannot both lie in an interval whose
endpoints differ by less than a factor of two. This lets the prevalence count
discard a possible radius above the desired upper endpoint.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology Section6

universe u

/-- An interval `(a,b]` with `b ≤ 2a` contains at most one power of `1/8`. -/
theorem eighth_powers_eq_of_short_interval {a b : ℝ} (ha : 0 < a) (hab : b ≤ 2 * a)
    {m n : ℕ} (hm : a < (8 : ℝ)⁻¹ ^ m ∧ (8 : ℝ)⁻¹ ^ m ≤ b)
    (hn : a < (8 : ℝ)⁻¹ ^ n ∧ (8 : ℝ)⁻¹ ^ n ≤ b) : m = n := by
  by_contra h
  rcases lt_or_gt_of_ne h with hmn | hnm
  · have hp : (8 : ℝ)⁻¹ ^ n ≤ (8 : ℝ)⁻¹ ^ (m + 1) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    rw [pow_succ] at hp
    norm_num at hp
    linarith
  · have hp : (8 : ℝ)⁻¹ ^ m ≤ (8 : ℝ)⁻¹ ^ (n + 1) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    rw [pow_succ] at hp
    norm_num at hp
    linarith

/-- If at least two geometric good radii lie in `[δ, √δ]` and
`ε ≤ δ ≤ 2ε`, one of them belongs to `[ε, √ε]`. -/
theorem exists_exact_good_radius {ε δ : ℝ} (hε : 0 < ε) (hεδ : ε ≤ δ)
    (hδε : δ ≤ 2 * ε) {P : ℝ → Prop}
    (hcount : 1 < {ρ : ℝ | ρ ∈ Icc δ (Real.sqrt δ) ∧
      (∃ n : ℕ, ρ = (8 : ℝ)⁻¹ ^ n) ∧ P ρ}.ncard) :
    ∃ ρ ∈ Icc ε (Real.sqrt ε), P ρ := by
  by_contra hnone
  let S : Set ℝ := {ρ : ℝ | ρ ∈ Icc δ (Real.sqrt δ) ∧
    (∃ n : ℕ, ρ = (8 : ℝ)⁻¹ ^ n) ∧ P ρ}
  have hSfin : S.Finite := Set.finite_of_ncard_pos (by dsimp [S] at *; omega)
  have hεsqrt : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have hroot : Real.sqrt δ ≤ 2 * Real.sqrt ε := by
    have hδnn : 0 ≤ δ := hε.le.trans hεδ
    have hsδ := Real.sq_sqrt hδnn
    have hsε := Real.sq_sqrt hε.le
    have hsδnn := Real.sqrt_nonneg δ
    nlinarith
  have hlarge : ∀ ρ ∈ S, Real.sqrt ε < ρ := by
    intro ρ hρ
    by_contra h
    exact hnone ⟨ρ, ⟨hεδ.trans hρ.1.1, le_of_not_gt h⟩, hρ.2.2⟩
  have hsub : ∀ x ∈ S, ∀ y ∈ S, x = y := by
    intro x hx y hy
    obtain ⟨m, rfl⟩ := hx.2.1
    obtain ⟨n, rfl⟩ := hy.2.1
    have := eighth_powers_eq_of_short_interval hεsqrt hroot
      ⟨hlarge _ hx, hx.1.2⟩ ⟨hlarge _ hy, hy.1.2⟩
    rw [this]
  have hle : S.ncard ≤ 1 := (Set.ncard_le_one hSfin).2 hsub
  dsimp [S] at hle
  omega

/-- The prevalence count eventually supplies at least two good geometric
radii at every grid point of each dyadic scale. -/
theorem ae_eventually_dyadic_two_good_radii
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {c : ℝ} (hc : 0 < c)
    {E : ℝ → ℂ → Set Ω}
    (hprev : PolyHighProb P (fun ε => {ω | ∀ x₀ ∈ prevalenceGrid ε,
      c * Real.log (ε ^ (-(1 / 2 : ℝ))) ≤
        ({ρ : ℝ | ρ ∈ Icc ε (Real.sqrt ε) ∧ (∃ n : ℕ, ρ = (8 : ℝ)⁻¹ ^ n) ∧
          ω ∈ E ρ x₀}.ncard : ℝ)})) :
    ∀ᵐ ω ∂P, ∀ᶠ k : ℕ in atTop,
      ∀ x₀ ∈ prevalenceGrid ((2 : ℝ)⁻¹ ^ k),
        1 < {ρ : ℝ | ρ ∈ Icc ((2 : ℝ)⁻¹ ^ k) (Real.sqrt ((2 : ℝ)⁻¹ ^ k)) ∧
          (∃ n : ℕ, ρ = (8 : ℝ)⁻¹ ^ n) ∧ ω ∈ E ρ x₀}.ncard := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let a : ℝ := c * Real.log 2 / 2
  have ha : 0 < a := by dsimp [a]; positivity
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / a)
  filter_upwards [hprev.ae_eventually_dyadic] with ω hω
  filter_upwards [hω, eventually_ge_atTop N] with k hk hkN
  intro x₀ hx₀
  have hformula : c * Real.log (((2 : ℝ)⁻¹ ^ k) ^ (-(1 / 2 : ℝ))) = a * k := by
    rw [Real.log_rpow (by positivity), Real.log_pow, Real.log_inv]
    dsimp [a]
    ring
  have hklarge : 1 < a * k := by
    have hNk : (N : ℝ) ≤ k := by exact_mod_cast hkN
    have hmul : 1 < a * N := by
      have := (div_lt_iff₀ ha).mp hN
      linarith
    exact hmul.trans_le (mul_le_mul_of_nonneg_left hNk ha.le)
  have hcount := hk x₀ hx₀
  rw [hformula] at hcount
  exact_mod_cast hklarge.trans_le hcount

/-- The localized crossing estimate with the exact radius interval of Lemma
10.1. The boundary and pole margins remain explicit. -/
theorem ae_eventually_localized_crossings_exact_radius
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h6 : HarnackTypeComponentStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ α ∈ Ioo (0 : ℝ) 1,
    ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∀ w ∈ ball (0 : ℂ) 1 \ ball 0 (20 * Real.sqrt ε),
      ∃ ρ ∈ Icc ε (Real.sqrt ε),
        ∀ z ∈ ball (0 : ℂ) 1, ∀ t : ℝ, 0 < t →
          dist w 0 + 2 * ρ < 1 → 2 * ρ < dist z w →
          (crossingComponents (cluster (μ ω) 1 z t ∩ ball w (2 * ρ)) w (ρ / 3)
            (2 * ρ)).encard ≤ ⌈1 / α⌉₊ := by
  obtain ⟨c, hc, hcount⟩ := localizedCrossingCount_of_harnack hI2 h6
  intro γ hγ hγ2
  obtain ⟨α, hα, hcount⟩ := hcount γ hγ hγ2
  let a : ℝ := min α (1 / 2)
  have ha : 0 < a := lt_min hα (by norm_num)
  have haα : a ≤ α := min_le_left _ _
  have ha1 : a < 1 := (min_le_right α (1 / 2)).trans_lt (by norm_num)
  refine ⟨a, ⟨ha, ha1⟩, ?_⟩
  intro α₀ hα₀ Ω _ P hC hcirc μ hGFF hμ
  obtain ⟨E, hprev, hbound⟩ := hcount α₀ hα₀ Ω P hC hcirc μ hGFF hμ
  filter_upwards [ae_eventually_dyadic_two_good_radii hc hprev, hbound] with ω hgood hbound
  rw [eventually_atTop] at hgood
  obtain ⟨N, hN⟩ := hgood
  have hthreshold : 0 < min 1 (((2 : ℝ)⁻¹) ^ N) := by positivity
  filter_upwards [(eventually_lt_nhds hthreshold).filter_mono nhdsWithin_le_nhds,
    (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))] with ε hsmall hε
  change 0 < ε at hε
  have hε1 : ε < 1 := hsmall.trans_le (min_le_left _ _)
  have hεN : ε < ((2 : ℝ)⁻¹) ^ N := hsmall.trans_le (min_le_right _ _)
  obtain ⟨n, hnN, hnlo, hnhi⟩ := exists_late_dyadic_scale N hε hεN
  let δ : ℝ := ((2 : ℝ)⁻¹) ^ n
  have hδpos : 0 < δ := by dsimp [δ]; positivity
  have hδε : δ ≤ 2 * ε := hnhi.le
  have hsqrt : Real.sqrt δ ≤ (3 / 2 : ℝ) * Real.sqrt ε := by
    have hδsq := Real.sq_sqrt hδpos.le
    have hεsq := Real.sq_sqrt hε.le
    have hδnn := Real.sqrt_nonneg δ
    have hεnn := Real.sqrt_nonneg ε
    nlinarith
  have hεsqrt : ε ≤ Real.sqrt ε := by
    have hs := Real.sq_sqrt hε.le
    have hsn := Real.sqrt_nonneg ε
    nlinarith
  intro w hw
  have haw : 10 * Real.sqrt δ + δ ≤ dist w 0 := by
    have hw' : 20 * Real.sqrt ε ≤ dist w 0 := by
      simpa [mem_ball, not_lt] using hw.2
    linarith
  obtain ⟨x₀, hx₀, hnear⟩ := exists_prevalenceGrid_dist_lt hδpos hw.1 haw
  obtain ⟨ρ, hρ, hE⟩ := exists_exact_good_radius hε hnlo hδε (hN n hnN x₀ hx₀)
  refine ⟨ρ, hρ, ?_⟩
  have hρpos : 0 < ρ := hε.trans_le hρ.1
  have hρlt : ρ < 1 := by
    have hs : Real.sqrt ε < 1 := by simpa using Real.sqrt_lt_sqrt hε.le hε1
    exact hρ.2.trans_lt hs
  have hnear' : dist w x₀ < ρ / 6 := by linarith [hρ.1]
  intro z hz t ht hboundary hpole
  refine (hbound ρ ⟨hρpos, hρlt⟩ x₀ hE z hz t ht w hnear' hboundary hpole).trans ?_
  exact_mod_cast Nat.ceil_mono (one_div_le_one_div_of_le ha haα)

end HarmonicBalls

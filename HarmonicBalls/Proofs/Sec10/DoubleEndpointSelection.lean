import HarmonicBalls.Proofs.Sec10.ExpandedDiscCrossings
import HarmonicBalls.Proofs.Sec10.ContainedInnerBallCrossings

/-! # Excluding both endpoint outliers from the geometric good radii -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology Section6
open scoped Pointwise

/-- An interval whose upper endpoint is at most four times its positive
lower endpoint contains at most one power of one eighth. -/
theorem eighth_powers_eq_of_factor_four_interval {a b : ℝ} (ha : 0 < a)
    (hab : b ≤ 4 * a) {m n : ℕ}
    (hm : a < (8 : ℝ)⁻¹ ^ m ∧ (8 : ℝ)⁻¹ ^ m ≤ b)
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

/-- Three good powers of one eighth suffice to remove a possible outlier at
both ends of the target interval. -/
theorem exists_good_radius_after_doubling_lower_endpoint {ε δ : ℝ}
    (hε : 0 < ε) (hεδ : ε ≤ δ) (hδε : δ ≤ 2 * ε) {P : ℝ → Prop}
    (hcount : 2 < {ρ : ℝ | ρ ∈ Icc δ (Real.sqrt δ) ∧
      (∃ n : ℕ, ρ = (8 : ℝ)⁻¹ ^ n) ∧ P ρ}.ncard) :
    ∃ ρ ∈ Icc (2 * ε) (Real.sqrt ε), P ρ := by
  by_contra hnone
  let S : Set ℝ := {ρ : ℝ | ρ ∈ Icc δ (Real.sqrt δ) ∧
    (∃ n : ℕ, ρ = (8 : ℝ)⁻¹ ^ n) ∧ P ρ}
  let A : Set ℝ := {ρ ∈ S | ρ < 2 * ε}
  let B : Set ℝ := {ρ ∈ S | Real.sqrt ε < ρ}
  have hSfin : S.Finite := Set.finite_of_ncard_pos (by dsimp [S] at *; omega)
  have hAfin : A.Finite := hSfin.subset (by intro x hx; exact hx.1)
  have hBfin : B.Finite := hSfin.subset (by intro x hx; exact hx.1)
  have hroot : Real.sqrt δ ≤ 2 * Real.sqrt ε := by
    have hδnn : 0 ≤ δ := hε.le.trans hεδ
    have hsδ := Real.sq_sqrt hδnn
    have hsε := Real.sq_sqrt hε.le
    have hsδnn := Real.sqrt_nonneg δ
    have hsεnn := Real.sqrt_nonneg ε
    nlinarith
  have hA : A.ncard ≤ 1 := (Set.ncard_le_one hAfin).2 (by
    intro x hx y hy
    obtain ⟨m, hm⟩ := hx.1.2.1
    obtain ⟨n, hn⟩ := hy.1.2.1
    subst x; subst y
    have hm' : ε / 2 < (8 : ℝ)⁻¹ ^ m ∧ (8 : ℝ)⁻¹ ^ m ≤ 2 * ε := by
      constructor <;> linarith [hx.1.1.1, hx.2]
    have hn' : ε / 2 < (8 : ℝ)⁻¹ ^ n ∧ (8 : ℝ)⁻¹ ^ n ≤ 2 * ε := by
      constructor <;> linarith [hy.1.1.1, hy.2]
    have : m = n := eighth_powers_eq_of_factor_four_interval (by linarith) (by linarith) hm' hn'
    rw [this])
  have hB : B.ncard ≤ 1 := (Set.ncard_le_one hBfin).2 (by
    intro x hx y hy
    obtain ⟨m, hm⟩ := hx.1.2.1
    obtain ⟨n, hn⟩ := hy.1.2.1
    subst x; subst y
    have : m = n := eighth_powers_eq_of_short_interval (Real.sqrt_pos.2 hε) hroot
      ⟨hx.2, hx.1.1.2⟩ ⟨hy.2, hy.1.1.2⟩
    rw [this])
  have hsub : S ⊆ A ∪ B := by
    intro x hx
    by_cases hsmall : x < 2 * ε
    · exact Or.inl ⟨hx, hsmall⟩
    · right
      refine ⟨hx, ?_⟩
      by_contra hbig
      exact hnone ⟨x, ⟨le_of_not_gt hsmall, le_of_not_gt hbig⟩, hx.2.2⟩
  have hle := (Set.ncard_le_ncard hsub (hAfin.union hBfin)).trans (Set.ncard_union_le A B)
  dsimp [S] at hle
  omega

/-- Prevalence supplies three distinct good radii at every late dyadic grid. -/
theorem ae_eventually_dyadic_three_good_radii
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {c : ℝ} (hc : 0 < c)
    {E : ℝ → ℂ → Set Ω}
    (hprev : PolyHighProb P (fun ε => {ω | ∀ x₀ ∈ prevalenceGrid ε,
      c * Real.log (ε ^ (-(1 / 2 : ℝ))) ≤
        ({ρ : ℝ | ρ ∈ Icc ε (Real.sqrt ε) ∧ (∃ n : ℕ, ρ = (8 : ℝ)⁻¹ ^ n) ∧
          ω ∈ E ρ x₀}.ncard : ℝ)})) :
    ∀ᵐ ω ∂P, ∀ᶠ k : ℕ in atTop,
      ∀ x₀ ∈ prevalenceGrid ((2 : ℝ)⁻¹ ^ k),
        2 < {ρ : ℝ | ρ ∈ Icc ((2 : ℝ)⁻¹ ^ k) (Real.sqrt ((2 : ℝ)⁻¹ ^ k)) ∧
          (∃ n : ℕ, ρ = (8 : ℝ)⁻¹ ^ n) ∧ ω ∈ E ρ x₀}.ncard := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let a : ℝ := c * Real.log 2 / 2
  have ha : 0 < a := by dsimp [a]; positivity
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / a)
  filter_upwards [hprev.ae_eventually_dyadic] with ω hω
  filter_upwards [hω, eventually_ge_atTop N] with k hk hkN
  intro x₀ hx₀
  have hformula : c * Real.log (((2 : ℝ)⁻¹ ^ k) ^ (-(1 / 2 : ℝ))) = a * k := by
    rw [Real.log_rpow (by positivity), Real.log_pow, Real.log_inv]
    dsimp [a]
    ring
  have hklarge : 2 < a * k := by
    have hNk : (N : ℝ) ≤ k := by exact_mod_cast hkN
    have hmul : 2 < a * N := by
      have := (div_lt_iff₀ ha).mp hN
      linarith
    exact hmul.trans_le (mul_le_mul_of_nonneg_left hNk ha.le)
  have hcount := hk x₀ hx₀
  rw [hformula] at hcount
  exact_mod_cast hklarge.trans_le hcount

universe u

/-- The sharp-margin crossing bound retains a good radius even after doubling
the lower endpoint; prevalence excludes both possible endpoint outliers. -/
theorem ae_eventually_crossings_with_doubled_lower_radius
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h6 : HarnackTypeComponentStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ α ∈ Ioo (0 : ℝ) 1,
    ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∀ w ∈ ball (0 : ℂ) 1 \ ball 0 (20 * Real.sqrt ε),
      ∃ ρ ∈ Icc (2 * ε) (Real.sqrt ε),
        ∀ z ∈ ball (0 : ℂ) 1, ∀ t : ℝ, 0 < t →
          dist w 0 + (ρ + ρ / 50) < 1 → ρ + ρ / 50 < dist z w →
          (crossingComponents (cluster (μ ω) 1 z t ∩ ball w (2 * ρ)) w (ρ / 3)
            (2 * ρ)).encard ≤ ⌈1 / α⌉₊ := by
  obtain ⟨c, hc, h6⟩ := h6
  intro γ hγ hγ2
  obtain ⟨α, hα, h6⟩ := h6 γ hγ hγ2
  let a : ℝ := min α (1 / 2)
  have ha : 0 < a := lt_min hα (by norm_num)
  have haα : a ≤ α := min_le_left _ _
  have ha1 : a < 1 := (min_le_right α (1 / 2)).trans_lt (by norm_num)
  refine ⟨a, ⟨ha, ha1⟩, ?_⟩
  intro α₀ hα₀ Ω _ P hC hcirc μ hGFF hμ
  obtain ⟨E, hgood, hprev⟩ := h6 α₀ hα₀ Ω P hC hcirc μ hGFF hμ
  obtain ⟨βm, βp, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα₀ hGFF hμ
  filter_upwards [ae_eventually_dyadic_three_good_radii hc hprev, hV,
    clusterOpenLaplacian_proved hI2 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ] with ω hgoodscale hV hopen
  let : IsLocallyFiniteMeasure (μ ω) := hV.1
  rw [eventually_atTop] at hgoodscale
  obtain ⟨N, hN⟩ := hgoodscale
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
  have hcount : 2 < {r : ℝ | r ∈ Icc δ (Real.sqrt δ) ∧
      (∃ k : ℕ, r = (8 : ℝ)⁻¹ ^ k) ∧ (δ ≤ r ∧ ω ∈ E r x₀)}.ncard := by
    convert hN n hnN x₀ hx₀ using 1
    congr 1
    ext r
    simp only [mem_ofPred_eq]
    constructor
    · rintro ⟨hr, hk, _, he⟩
      exact ⟨hr, hk, he⟩
    · rintro ⟨hr, hk, he⟩
      exact ⟨hr, hk, hr.1, he⟩
  obtain ⟨ρ, hρ, hδρ, hE⟩ := exists_good_radius_after_doubling_lower_endpoint hε hnlo hδε hcount
  have hρpos : 0 < ρ := by linarith [hρ.1]
  have hρlt : ρ < 1 := by
    have hs : Real.sqrt ε < 1 := by simpa using Real.sqrt_lt_sqrt hε.le hε1
    exact hρ.2.trans_lt hs
  have hnear50 : dist w x₀ < ρ / 50 := by linarith
  have hnear6 : dist w x₀ < ρ / 6 := by linarith
  refine ⟨ρ, hρ, ?_⟩
  intro z hz t ht hboundary hpole
  have hdomain : closedBall x₀ ρ ⊆ ball (0 : ℂ) 1 \ {z} := by
    intro y hy
    have hyx : dist y x₀ ≤ ρ := mem_closedBall.mp hy
    have hxw : dist x₀ w < ρ / 50 := by simpa [dist_comm] using hnear50
    have hyw : dist y w < ρ + ρ / 50 := by
      have := dist_triangle y x₀ w
      linarith
    refine ⟨mem_ball.mpr ?_, ?_⟩
    · have := dist_triangle y w (0 : ℂ)
      linarith
    · intro hyz
      have : y = z := mem_singleton_iff.mp hyz
      subst y
      linarith
  have hcount := encard_crossingComponents_of_nearby_harnack (μ ω) (cluster (μ ω) 1 z t)
    (hopen t 1 ht zero_lt_one z hz).1 hα w x₀ hρpos hnear6
    (ne_top_of_le_ne_top (measure_ball_lt_top (μ := μ ω)).ne (measure_mono sdiff_subset))
    (hgood ω ρ ⟨hρpos, hρlt⟩ x₀ hE z hz t ht hdomain)
  exact hcount.trans (by exact_mod_cast Nat.ceil_mono (one_div_le_one_div_of_le ha haα))



/-- The strengthened unit-scale selection gives the exact lower endpoint
after dilation and compatibility of clusters in nested discs. -/
theorem crossings_of_larger_disc_normalization_exact
    (μ ν : Measure ℂ) (a α ε : ℝ) (ha : 0 < a) (hε : 0 < ε) (hεsmall : ε < 1 / 16)
    (hunit : ∀ w ∈ ball (0 : ℂ) 1 \ ball 0 (20 * Real.sqrt (ε / 4)),
      ∃ ρ ∈ Icc (2 * (ε / 4)) (Real.sqrt (ε / 4)),
        ∀ z ∈ ball (0 : ℂ) 1, ∀ t : ℝ, 0 < t →
          dist w 0 + (ρ + ρ / 50) < 1 → ρ + ρ / 50 < dist z w →
          (crossingComponents (cluster ν 1 z t ∩ ball w (2 * ρ)) w (ρ / 3)
            (2 * ρ)).encard ≤ ⌈1 / α⌉₊)
    (hscale : ∀ z ∈ ball (0 : ℂ) 1, ∀ t : ℝ, 0 < t →
      cluster ν 1 z t = (2 : ℝ)⁻¹ • cluster μ 2 ((2 : ℝ) • z) (a * t))
    (hcompat : ∀ z ∈ ball (0 : ℂ) 1, ∀ t : ℝ, 0 < t →
      closure (cluster μ 1 z t) ⊆ ball 0 1 → cluster μ 2 z t = cluster μ 1 z t) :
    ∀ w ∈ ball (0 : ℂ) 1 \ ball 0 (20 * Real.sqrt ε),
      ∃ ρ ∈ Icc ε (Real.sqrt ε), ∀ z ∈ ball (0 : ℂ) 1, ∀ t : ℝ, 0 < t →
        closure (cluster μ 1 z t) ⊆ ball 0 1 → ρ + ρ / 50 < dist z w →
        (crossingComponents (cluster μ 1 z t ∩ ball w (2 * ρ)) w (ρ / 3)
          (2 * ρ)).encard ≤ ⌈1 / α⌉₊ := by
  have hhalf (x y : ℂ) : dist ((2 : ℝ)⁻¹ • x) ((2 : ℝ)⁻¹ • y) = dist x y / 2 := by
    rw [dist_smul₀]
    norm_num [Real.norm_eq_abs, div_eq_mul_inv, mul_comm]
  have hsqrt : Real.sqrt (ε / 4) = Real.sqrt ε / 2 := by
    rw [Real.sqrt_div hε.le]
    norm_num
  have hsqrtsmall : Real.sqrt ε < 1 / 4 := by
    have h := Real.sqrt_lt_sqrt hε.le hεsmall
    norm_num at h
    exact h
  intro w hw
  have hw' : (2 : ℝ)⁻¹ • w ∈ ball (0 : ℂ) 1 \ ball 0 (20 * Real.sqrt (ε / 4)) := by
    have hd : dist ((2 : ℝ)⁻¹ • w) 0 = dist w 0 / 2 := by simpa using hhalf w 0
    have hwd : dist w 0 < 1 := mem_ball.mp hw.1
    have hwa : 20 * Real.sqrt ε ≤ dist w 0 := by simpa [mem_ball, not_lt] using hw.2
    constructor
    · exact mem_ball.mpr (by linarith)
    · rw [mem_ball, not_lt, hsqrt, hd]
      linarith
  obtain ⟨r, hr, hbound⟩ := hunit _ hw'
  refine ⟨2 * r, ⟨by linarith [hr.1], by rw [hsqrt] at hr; linarith [hr.2]⟩, ?_⟩
  intro z hz t ht hcl hpole
  have hz' : (2 : ℝ)⁻¹ • z ∈ ball (0 : ℂ) 1 := by
    have hd : dist ((2 : ℝ)⁻¹ • z) 0 = dist z 0 / 2 := by simpa using hhalf z 0
    exact mem_ball.mpr (by rw [hd]; linarith [mem_ball.mp hz])
  have hd : dist ((2 : ℝ)⁻¹ • w) 0 = dist w 0 / 2 := by simpa using hhalf w 0
  have hdzw := hhalf z w
  have hboundary : dist ((2 : ℝ)⁻¹ • w) 0 + (r + r / 50) < 1 := by
    rw [hd, hsqrt] at *
    linarith [mem_ball.mp hw.1, hr.2]
  have hpole' : r + r / 50 < dist ((2 : ℝ)⁻¹ • z) ((2 : ℝ)⁻¹ • w) := by
    rw [hdzw]
    linarith
  have ht' : 0 < t / a := div_pos ht ha
  have hscale' := hscale ((2 : ℝ)⁻¹ • z) hz' (t / a) ht'
  have hzscale : (2 : ℝ) • ((2 : ℝ)⁻¹ • z) = z := by simp
  have htscale : a * (t / a) = t := by field_simp
  rw [hzscale, htscale] at hscale'
  have hcount := hbound ((2 : ℝ)⁻¹ • z) hz' (t / a) ht' hboundary hpole'
  have htrans := encard_ball_crossings_of_cluster_scale μ ν z w t (t / a) (2 * r) 2
    (by norm_num) hscale'
  have hcompat' := hcompat z hz t ht hcl
  rw [hcompat'] at htrans
  have hrscale : 2 * r / 2 = r := by ring
  rw [hrscale] at htrans
  exact htrans.trans_le hcount


/-- After enlargement to the disc of radius two, the crossing estimate holds
at all admissible unit-disc centers without a boundary margin. The affine
invariance and coordinate-change hypotheses are staged inputs. -/
theorem ae_crossings_without_boundary_margin_exact_of_scaledField
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h6 : HarnackTypeComponentStmt.{u})
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ α₀ hC hcirc) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ α ∈ Ioo (0 : ℝ) 1,
    ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∀ w ∈ ball (0 : ℂ) 1 \ ball 0 (20 * Real.sqrt ε),
      ∃ ρ ∈ Icc ε (Real.sqrt ε), ∀ z ∈ ball (0 : ℂ) 1, ∀ t : ℝ, 0 < t →
        closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 → ρ + ρ / 50 < dist z w →
        (crossingComponents (cluster (μ ω) 1 z t ∩ ball w (2 * ρ)) w (ρ / 3)
          (2 * ρ)).encard ≤ ⌈1 / α⌉₊ := by
  intro γ hγ hγ2
  obtain ⟨α, hα, hbound⟩ := ae_eventually_crossings_with_doubled_lower_radius hI2 h6 γ hγ hγ2
  refine ⟨α, hα, ?_⟩
  intro α₀ hα₀ Ω _ P hC hcirc μ hGFF hμ
  let hC' := affinePairing hC hcirc (2 : ℂ) 0
  let hcirc' : Ω → ℝ → ℂ → ℝ := fun ω r z =>
    hcirc ω (2 * r) ((2 : ℝ) • z) - hcirc ω 2 0
  have hGFF' : IsWholePlaneGFF P hC' hcirc' := by
    have hcirc_eq : hcirc' = affineCircle hcirc (2 : ℂ) 0 := by
      funext ω r z
      simp [hcirc', affineCircle, Complex.real_smul]
    rw [hcirc_eq]
    exact hAff Ω P hC hcirc hGFF (2 : ℂ) (by norm_num) 0
  have hμ' : IsLQGMeasureOfField P γ α₀ hcirc'
      (fun ω => normalizedPullbackMeasure γ α₀ 2 (hcirc ω) (μ ω)) := by
    exact isLQGMeasureOfField_normalizedPullback (hCC Ω P γ α₀ hC hcirc)
      hGFF hγ hγ2 hα₀ hμ (by norm_num)
  have hunit := hbound α₀ hα₀ Ω P hC' hcirc'
    (fun ω => normalizedPullbackMeasure γ α₀ 2 (hcirc ω) (μ ω)) hGFF' hμ'
  have hscale := clusterPathwiseScaleStep_proved γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ 2 (by norm_num)
  have hcompat := clusterCompatibility_proved hI2 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ 2 (by norm_num)
  filter_upwards [hunit, hscale, hcompat] with ω hunit hscale hcompat
  have htend : Tendsto (fun ε : ℝ => ε / 4) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using (continuous_id.div_const 4).tendsto (0 : ℝ) |>.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      change 0 < ε / 4
      exact div_pos (show 0 < ε from hε) (by norm_num)
  filter_upwards [htend.eventually hunit,
    (eventually_lt_nhds (show (0 : ℝ) < 1 / 16 by norm_num)).filter_mono nhdsWithin_le_nhds,
    (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))] with ε hunit hεsmall hε
  apply crossings_of_larger_disc_normalization_exact (μ ω)
    (normalizedPullbackMeasure γ α₀ 2 (hcirc ω) (μ ω))
    (Real.exp (γ * (lqgQ γ * Real.log 2 + fieldCircleAverage α₀ (hcirc ω) 2 0)))
    α ε (Real.exp_pos _) hε hεsmall hunit hscale
  intro z hz t ht hcl
  have heq := hcompat t ht 1 (by norm_num) z hz 1 (by norm_num) hcl 2 (by norm_num)
  exact heq

/-- The same boundary-free estimate holds for all poles, since clusters
whose pole lies outside the unit disc are empty. -/
theorem ae_crossings_without_boundary_margin_exact_all_poles
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h6 : HarnackTypeComponentStmt.{u})
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ α₀ hC hcirc) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ α ∈ Ioo (0 : ℝ) 1,
    ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∀ w ∈ ball (0 : ℂ) 1 \ ball 0 (20 * Real.sqrt ε),
      ∃ ρ ∈ Icc ε (Real.sqrt ε), ∀ z : ℂ, ∀ t : ℝ, 0 < t →
        closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 → ρ + ρ / 50 < dist z w →
        (crossingComponents (cluster (μ ω) 1 z t ∩ ball w (2 * ρ)) w (ρ / 3)
          (2 * ρ)).encard ≤ ⌈1 / α⌉₊ := by
  intro γ hγ hγ2
  obtain ⟨α, hα, hbound⟩ :=
    ae_crossings_without_boundary_margin_exact_of_scaledField hI2 h6 hAff hCC γ hγ hγ2
  refine ⟨α, hα, ?_⟩
  intro α₀ hα₀ Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [hbound α₀ hα₀ Ω P hC hcirc μ hGFF hμ] with ω hω
  filter_upwards [hω] with ε hε
  intro w hw
  obtain ⟨ρ, hρ, hρbound⟩ := hε w hw
  refine ⟨ρ, hρ, ?_⟩
  intro z t ht hcl hpole
  by_cases hz : z ∈ ball (0 : ℂ) 1
  · exact hρbound z hz t ht hcl hpole
  · rw [cluster_eq_empty_of_pole_not_mem hz ht.le]
    simp [crossingComponents, connectedComponentsIn]



/-- The exact-radius estimate also covers any near-pole cluster containing
the inner sphere, with no fixed boundary margin. -/
theorem ae_crossings_without_boundary_margin_exact_inner_sphere_or_pole_margin
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h6 : HarnackTypeComponentStmt.{u})
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ α₀ hC hcirc) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ α ∈ Ioo (0 : ℝ) 1,
    ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∀ w ∈ ball (0 : ℂ) 1 \ ball 0 (20 * Real.sqrt ε),
      ∃ ρ ∈ Icc ε (Real.sqrt ε), ∀ z : ℂ, ∀ t : ℝ, 0 < t →
        closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
        (sphere w (ρ / 3) ⊆ cluster (μ ω) 1 z t ∨ ρ + ρ / 50 < dist z w) →
        (crossingComponents (cluster (μ ω) 1 z t ∩ ball w (2 * ρ)) w (ρ / 3)
          (2 * ρ)).encard ≤ ⌈1 / α⌉₊ := by
  intro γ hγ hγ2
  obtain ⟨α, hα, hbound⟩ :=
    ae_crossings_without_boundary_margin_exact_all_poles hI2 h6 hAff hCC γ hγ hγ2
  refine ⟨α, hα, ?_⟩
  intro α₀ hα₀ Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [hbound α₀ hα₀ Ω P hC hcirc μ hGFF hμ,
    clusterOpenLaplacian_proved hI2 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ] with ω hbound hopen
  filter_upwards [hbound, (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))] with ε hbound hε
  intro w hw
  obtain ⟨ρ, hρ, hρbound⟩ := hbound w hw
  have hρpos : 0 < ρ := hε.trans_le hρ.1
  refine ⟨ρ, hρ, ?_⟩
  intro z t ht hcl hcase
  rcases hcase with hsphere | hpole
  · by_cases hz : z ∈ ball (0 : ℂ) 1
    · apply (encard_crossingComponents_le_one_of_inner_sphere
        (hopen t 1 ht zero_lt_one z hz).1 (by positivity) (by linarith) hsphere).trans
      exact_mod_cast (Nat.ceil_pos.mpr (one_div_pos.mpr hα.1))
    · rw [cluster_eq_empty_of_pole_not_mem hz ht.le]
      simp [crossingComponents, connectedComponentsIn]
  · exact hρbound z t ht hcl hpole


end HarmonicBalls

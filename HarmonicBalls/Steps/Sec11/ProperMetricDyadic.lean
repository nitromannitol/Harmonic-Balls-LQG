import HarmonicBalls.Steps.Sec11.ProperMetricIntermediate

/-!
# Dyadic limits in proper length metrics

Finite isometric subdivisions lie in one compact metric ball. Compactness of
its countable power gives a subsequence convergent at every dyadic parameter.
-/

namespace HarmonicBalls

open Metric Set Filter
open scoped Topology

/-- Dyadic finite subdivisions admit a common subsequence which converges at
every dyadic parameter. This uses only compactness of the closed ball centered
at the initial point with radius equal to the endpoint distance. -/
theorem IsEuclideanLengthMetric.exists_dyadic_subsequence
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y)
    (hcompact : ∀ x : ℂ, ∀ R : ℝ, IsCompact {z : ℂ | D x z ≤ R})
    (x y : ℂ) :
    ∃ (f : ℕ → ℕ → ℂ) (φ : ℕ → ℕ) (g : ℕ × ℕ → ℂ),
      (∀ n, f n 0 = x ∧ f n (2 ^ n) = y ∧
        ∀ i j : ℕ, i ≤ j → j ≤ 2 ^ n →
          D (f n i) (f n j) = ((j : ℝ) - i) * (D x y / (2 ^ n : ℕ))) ∧
      StrictMono φ ∧
      ∀ m k : ℕ, k ≤ 2 ^ m →
        Tendsto (fun n => f (φ n) (k * 2 ^ (φ n - m))) atTop (𝓝 (g (m, k))) := by
  classical
  choose f hf using fun n : ℕ =>
    hD.exists_isometric_subdivision hnonneg hcompact (2 ^ n) (by positivity) x y
  let K : Set ℂ := {z | D x z ≤ D x y}
  have hK : IsCompact K := hcompact x (D x y)
  let q : ℕ → (ℕ × ℕ → ℂ) := fun n a =>
    if a.1 ≤ n ∧ a.2 ≤ 2 ^ a.1 then f n (a.2 * 2 ^ (n - a.1)) else x
  have hq : ∀ n, q n ∈ Set.pi Set.univ (fun _ : ℕ × ℕ => K) := by
    intro n a _
    dsimp only [q]
    split_ifs with ha
    · have hp : a.2 * 2 ^ (n - a.1) ≤ 2 ^ n := by
        calc
          a.2 * 2 ^ (n - a.1) ≤ 2 ^ a.1 * 2 ^ (n - a.1) :=
            Nat.mul_le_mul_right _ ha.2
          _ = 2 ^ n := by rw [← pow_add, Nat.add_sub_of_le ha.1]
      change D x (f n (a.2 * 2 ^ (n - a.1))) ≤ D x y
      have hdist := (hf n).2.2 0 (a.2 * 2 ^ (n - a.1)) (Nat.zero_le _) hp
      rw [(hf n).1] at hdist
      have hden : (0 : ℝ) < ((2 ^ n : ℕ) : ℝ) := by positivity
      have hle : ((a.2 * 2 ^ (n - a.1) : ℕ) : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) := by
        exact_mod_cast hp
      have hd := hnonneg x y
      simp only [Nat.cast_zero, sub_zero] at hdist
      rw [hdist]
      have hfrac : ((a.2 * 2 ^ (n - a.1) : ℕ) : ℝ) / (2 ^ n : ℕ) ≤ 1 :=
        (div_le_one hden).2 hle
      calc
        ((a.2 * 2 ^ (n - a.1) : ℕ) : ℝ) * (D x y / (2 ^ n : ℕ)) =
            (((a.2 * 2 ^ (n - a.1) : ℕ) : ℝ) / (2 ^ n : ℕ)) * D x y := by ring
        _ ≤ D x y := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hfrac hd
    · change D x x ≤ D x y
      rw [hD.self_eq_zero]
      exact hnonneg x y
  have hprod : IsCompact (Set.pi Set.univ (fun _ : ℕ × ℕ => K)) :=
    isCompact_univ_pi fun _ => hK
  obtain ⟨g, _, φ, hφ, hlim⟩ := hprod.tendsto_subseq hq
  refine ⟨f, φ, g, hf, hφ, ?_⟩
  intro m k hk
  have hcoord := (tendsto_pi_nhds.mp hlim) (m, k)
  have hevent : ∀ᶠ n in atTop, m ≤ φ n := hφ.tendsto_atTop.eventually_ge_atTop m
  apply hcoord.congr'
  filter_upwards [hevent] with n hn
  simp only [Function.comp_apply, q, hn, hk, and_self, ↓reduceIte]

/-- A metric inducing the Euclidean topology is jointly continuous in its two
arguments for that topology. -/
theorem IsEuclideanLengthMetric.continuous_pair {D : ℂ → ℂ → ℝ}
    (hD : IsEuclideanLengthMetric D) : Continuous fun p : ℂ × ℂ => D p.1 p.2 := by
  rw [Metric.continuous_iff]
  intro p ε hε
  have h₁ : Continuous fun q : ℂ × ℂ => D q.1 p.1 :=
    (hD.continuous_left p.1).comp continuous_fst
  have h₂ : Continuous fun q : ℂ × ℂ => D q.2 p.2 :=
    (hD.continuous_left p.2).comp continuous_snd
  obtain ⟨δ₁, hδ₁, hp₁⟩ := Metric.continuous_iff.mp h₁ p (ε / 2) (by linarith)
  obtain ⟨δ₂, hδ₂, hp₂⟩ := Metric.continuous_iff.mp h₂ p (ε / 2) (by linarith)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  intro q hq
  have ha := hp₁ q (lt_of_lt_of_le hq (min_le_left _ _))
  have hb := hp₂ q (lt_of_lt_of_le hq (min_le_right _ _))
  simp only [hD.self_eq_zero, Real.dist_eq, sub_zero] at ha hb
  have ha' : D q.1 p.1 < ε / 2 := lt_of_le_of_lt (le_abs_self _) ha
  have hb' : D q.2 p.2 < ε / 2 := lt_of_le_of_lt (le_abs_self _) hb
  have ht₁ := hD.triangle q.1 p.1 q.2
  have ht₂ := hD.triangle p.1 p.2 q.2
  have ht₃ := hD.triangle p.1 q.1 p.2
  have ht₄ := hD.triangle q.1 q.2 p.2
  rw [hD.symm p.2 q.2] at ht₂
  rw [hD.symm p.1 q.1] at ht₃
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- Refining a dyadic mesh does not change the represented real parameter. -/
theorem dyadic_refinement_ratio {m n k : ℕ} (hmn : m ≤ n) :
    ((k * 2 ^ (n - m) : ℕ) : ℝ) / (2 ^ n : ℕ) = (k : ℝ) / (2 ^ m : ℕ) := by
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  have hp : (2 : ℝ) ^ n = 2 ^ m * 2 ^ (n - m) := by
    rw [← pow_add, Nat.add_sub_of_le hmn]
  rw [hp]
  have hne : (2 : ℝ) ^ (n - m) ≠ 0 := by positivity
  field_simp

/-- A subdivision preserves the distance between any two mesh points, with
no ordering restriction on their indices. -/
theorem IsEuclideanLengthMetric.subdivision_distance
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {N : ℕ} {d : ℝ} {f : ℕ → ℂ}
    (h : ∀ i j : ℕ, i ≤ j → j ≤ N →
      D (f i) (f j) = ((j : ℝ) - i) * d)
    {i j : ℕ} (hi : i ≤ N) (hj : j ≤ N) :
    D (f i) (f j) = |(i : ℝ) - (j : ℝ)| * d := by
  rcases le_total i j with hij | hji
  · have hh : (i : ℝ) ≤ j := by exact_mod_cast hij
    rw [h i j hij hj, abs_of_nonpos (sub_nonpos.mpr hh)]
    ring
  · have hh : (j : ℝ) ≤ i := by exact_mod_cast hji
    rw [hD.symm (f i) (f j), h j i hji hi, abs_of_nonneg (sub_nonneg.mpr hh)]

/-- Refining a dyadic index keeps it within the refined mesh. -/
theorem dyadic_refinement_index_le {m n k : ℕ} (hmn : m ≤ n) (hk : k ≤ 2 ^ m) :
    k * 2 ^ (n - m) ≤ 2 ^ n := by
  calc
    k * 2 ^ (n - m) ≤ 2 ^ m * 2 ^ (n - m) := Nat.mul_le_mul_right _ hk
    _ = 2 ^ n := by rw [← pow_add, Nat.add_sub_of_le hmn]

/-- The dyadic limit of the finite subdivisions preserves the distance between
any two dyadic parameters. -/
theorem IsEuclideanLengthMetric.exists_isometric_dyadic_map
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y)
    (hcompact : ∀ x : ℂ, ∀ R : ℝ, IsCompact {z : ℂ | D x z ≤ R})
    (x y : ℂ) :
    ∃ g : ℕ × ℕ → ℂ, g (0, 0) = x ∧ g (0, 1) = y ∧
      ∀ m k l j : ℕ, k ≤ 2 ^ m → j ≤ 2 ^ l →
        D (g (m, k)) (g (l, j)) =
          |(k : ℝ) / (2 ^ m : ℕ) - (j : ℝ) / (2 ^ l : ℕ)| * D x y := by
  obtain ⟨f, φ, g, hf, hφ, hlim⟩ :=
    hD.exists_dyadic_subsequence hnonneg hcompact x y
  have hzero : g (0, 0) = x := by
    apply tendsto_nhds_unique (hlim 0 0 (by simp))
    simpa only [Nat.zero_mul, (hf _).1] using (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => x) atTop (𝓝 x))
  have hone : g (0, 1) = y := by
    apply tendsto_nhds_unique (hlim 0 1 (by simp))
    simpa only [Nat.sub_zero, one_mul, (hf _).2.1] using (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => y) atTop (𝓝 y))
  refine ⟨g, hzero, hone, ?_⟩
  intro m k l j hk hj
  have hlimD := (hD.continuous_pair.tendsto (g (m, k), g (l, j))).comp
    ((hlim m k hk).prodMk_nhds (hlim l j hj))
  have hev : ∀ᶠ n in atTop, m ≤ φ n ∧ l ≤ φ n :=
    (hφ.tendsto_atTop.eventually_ge_atTop m).and (hφ.tendsto_atTop.eventually_ge_atTop l)
  have heq : ∀ᶠ n in atTop,
      D (f (φ n) (k * 2 ^ (φ n - m))) (f (φ n) (j * 2 ^ (φ n - l))) =
        |(k : ℝ) / (2 ^ m : ℕ) - (j : ℝ) / (2 ^ l : ℕ)| * D x y := by
    filter_upwards [hev] with n hn
    have hk' := dyadic_refinement_index_le hn.1 hk
    have hj' := dyadic_refinement_index_le hn.2 hj
    rw [hD.subdivision_distance (hf (φ n)).2.2 hk' hj']
    have hden : (0 : ℝ) < ((2 ^ φ n : ℕ) : ℝ) := by positivity
    calc
      _ = |(((k * 2 ^ (φ n - m) : ℕ) : ℝ) -
            ((j * 2 ^ (φ n - l) : ℕ) : ℝ)) / (2 ^ φ n : ℕ)| * D x y := by
        rw [abs_div, abs_of_pos hden]
        ring
      _ = _ := by
        rw [sub_div, dyadic_refinement_ratio hn.1, dyadic_refinement_ratio hn.2]
  apply tendsto_nhds_unique hlimD
  exact tendsto_const_nhds.congr' (heq.mono fun _ h => h.symm)

/-- Dyadic points in the unit interval approximate every point of the interval
arbitrarily closely. -/
theorem exists_dyadic_approximation {t ε : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hε : 0 < ε) : ∃ m k : ℕ, k ≤ 2 ^ m ∧
      |(k : ℝ) / (2 ^ m : ℕ) - t| < ε := by
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
  have hm' : (1 : ℝ) / (2 ^ m : ℕ) < ε := by
    simpa only [div_pow, one_pow, Nat.cast_pow, Nat.cast_ofNat] using hm
  let d : ℝ := (2 ^ m : ℕ)
  have hd : 0 < d := by dsimp [d]; positivity
  let k : ℕ := ⌊t * d⌋₊
  have hnonneg : 0 ≤ t * d := mul_nonneg ht.1 (le_of_lt hd)
  have hlo : (k : ℝ) ≤ t * d := Nat.floor_le hnonneg
  have hhi : t * d < (k : ℝ) + 1 := Nat.lt_floor_add_one _
  have hbound : k ≤ 2 ^ m := by
    have hh : (k : ℝ) ≤ (2 ^ m : ℕ) := by
      change (k : ℝ) ≤ d
      nlinarith [ht.2]
    exact_mod_cast hh
  have hlower : (k : ℝ) / d ≤ t := (div_le_iff₀ hd).2 hlo
  have hdiff : t - (k : ℝ) / d < 1 / d := by
    apply (lt_div_iff₀ hd).2
    have hcancel : (k : ℝ) / d * d = k := div_mul_cancel₀ _ (ne_of_gt hd)
    nlinarith
  refine ⟨m, k, hbound, ?_⟩
  change |(k : ℝ) / d - t| < ε
  rw [abs_of_nonpos (sub_nonpos.mpr hlower)]
  have h := lt_trans hdiff hm'
  linarith

end HarmonicBalls

import HarmonicBalls.Proofs.Metric.SummablePathWeightedLength
import HarmonicBalls.Steps.Sec11.MetricArcLength
import HarmonicBalls.Steps.Sec11.WeylPathReverse
import HarmonicBalls.Steps.Sec11.PathCrossings
import HarmonicBalls.Steps.Sec11.CurveLengthReparam
import HarmonicBalls.Steps.Sec11.LocalPathLength

/-!
# Small weighted paths

The deterministic path construction associated with the logarithmic weight.
We acknowledge Leonardo Bonanno's contributions through the pinned
Lattice-Probability development.
-/

namespace HarmonicBalls

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

/-- Every positive radius below the initial scale lies in a later annular band. -/
theorem exists_radius_band {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 0))
    {i : ℕ} {u : ℝ} (hu : 0 < u) (hi : u ≤ r i) :
    ∃ j, i ≤ j ∧ r (j + 1) < u ∧ u ≤ r j := by
  have hev : ∀ᶠ n : ℕ in atTop, r n < u :=
    hr.eventually (eventually_lt_nhds hu)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  have hex : ∃ n : ℕ, r (i + n + 1) < u := by
    refine ⟨N, hN _ ?_⟩
    omega
  let n := Nat.find hex
  have hn : r (i + n + 1) < u := Nat.find_spec hex
  refine ⟨i + n, by omega, hn, ?_⟩
  cases hnval : n with
  | zero => simpa only [hnval, add_zero] using hi
  | succ k =>
    have hmin := Nat.find_min hex (show k < Nat.find hex by
      change k < n
      rw [hnval]
      omega)
    have hle : u ≤ r (i + k + 1) := le_of_not_gt hmin
    simpa only [Nat.add_succ] using hle

/-- The cost assigned to the annular piece between consecutive radii. -/
noncomputable def smallPathCost (r L : ℕ → ℝ) (β : ℝ) (i : ℕ) : ℝ :=
  2 * L i * (if 0 ≤ β then (r (i + 1)) ^ (-β) else (2 * r i) ^ (-β))

/-- Exact target of the deterministic small-path construction. -/
def SmallWeightedPathExistence (D : ℂ → ℂ → ℝ) (r L : ℕ → ℝ) (β : ℝ) : Prop :=
  IsEuclideanLengthMetric D →
  (∀ i, 0 < r i) → StrictAnti r → Tendsto r atTop (𝓝 0) →
  (∀ i, 0 < L i) → Summable L → Summable (smallPathCost r L β) →
  (∀ i y z, y ∈ closedBall (0 : ℂ) (r i) → z ∈ closedBall (0 : ℂ) (r i) →
    internalMetric D (ball 0 (2 * r i)) y z ≤ ENNReal.ofReal (L i)) →
  ∀ i x, ‖x‖ ≤ r i → ∃ T : ℝ, ∃ p : ℝ → ℂ,
    IsLengthParametrized D p T ∧ p 0 = 0 ∧ p T = x ∧
    (∀ t ∈ Icc 0 T, p t ∈ ball (0 : ℂ) (2 * r i)) ∧
    (∀ t ∈ Ioc 0 T, p t ≠ 0) ∧
    T ≤ 2 * (∑' n, L (i + n)) ∧
    (∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (-β * Real.log ‖p t‖))) ≤
      ENNReal.ofReal (∑' n, smallPathCost r L β (i + n))

/-- The tails of a summable real sequence tend to zero. -/
theorem tendsto_smallPath_tail (a : ℕ → ℝ) :
    Tendsto (fun i => ∑' n, a (i + n)) atTop (𝓝 0) := by
  simpa only [Nat.add_comm] using (tendsto_sum_nat_add a)

/-- Tails of a nonnegative summable sequence decrease with their starting index. -/
theorem tsum_tail_le {a : ℕ → ℝ} (ha : Summable a) (h₀ : ∀ n, 0 ≤ a n)
    {i j : ℕ} (hij : i ≤ j) : (∑' n, a (j + n)) ≤ ∑' n, a (i + n) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
  have hs : Summable (fun n => a (i + n)) := by
    simpa only [Nat.add_comm] using (summable_nat_add_iff i).2 ha
  have heq := hs.sum_add_tsum_nat_add k
  have hnonneg : 0 ≤ ∑ n ∈ Finset.range k, a (i + n) :=
    Finset.sum_nonneg fun n _ => h₀ (i + n)
  have ht : (∑' n, a (i + (n + k))) ≤ ∑' n, a (i + n) := by linarith
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ht

/-- The annular cost sequence is nonnegative for positive radii and lengths. -/
theorem smallPathCost_nonneg {r L : ℕ → ℝ} {β : ℝ}
    (hr : ∀ n, 0 < r n) (hL : ∀ n, 0 < L n) (n : ℕ) :
    0 ≤ smallPathCost r L β n := by
  have hrn := hr n
  have hrs := hr (n + 1)
  have hLn := hL n
  unfold smallPathCost
  split <;> positivity

/-- A path connecting a point outside a sphere to a point inside it has a
first visit to the sphere, and stays outside the smaller ball until that visit. -/
theorem path_first_sphere {x y : ℂ} (P : Path x y) {ρ : ℝ}
    (hx : ρ ≤ ‖x‖) (hy : ‖y‖ ≤ ρ) :
    ∃ s ∈ Icc (0 : ℝ) 1, ‖P.extend s‖ = ρ ∧
      ∀ t ∈ Icc (0 : ℝ) s, ρ ≤ ‖P.extend t‖ := by
  let f : ℝ → ℝ := fun t => ‖P.extend t‖
  let A : Set ℝ := Icc 0 1 ∩ {t | f t = ρ}
  have hf : Continuous f := P.continuous_extend.norm
  have hclosed : IsClosed A := isClosed_Icc.inter (isClosed_eq hf continuous_const)
  have hne : A.Nonempty := by
    obtain ⟨t, ht, heq⟩ := path_meets_sphere_between P (z := 0)
      (by simpa only [dist_zero_right] using hx)
      (by simpa only [dist_zero_right] using hy)
    refine ⟨t, ht, ?_⟩
    change f t = ρ
    simpa only [mem_sphere, dist_zero_right, f] using heq
  have hbdd : BddBelow A := ⟨0, fun t ht => ht.1.1⟩
  let s := sInf A
  have hs : s ∈ A := hclosed.csInf_mem hne hbdd
  have hs2 : f s = ρ := hs.2
  refine ⟨s, hs.1, hs2, ?_⟩
  intro t ht
  by_contra hnot
  have hft : f t < ρ := lt_of_not_ge hnot
  have hstart : ρ ≤ f 0 := by simpa only [f, P.extend_zero] using hx
  obtain ⟨u, hu, hfu⟩ := intermediate_value_Icc' ht.1 hf.continuousOn ⟨hft.le, hstart⟩
  have huA : u ∈ A := ⟨⟨hu.1, hu.2.trans (ht.2.trans hs.1.2)⟩, hfu⟩
  have hsu : s ≤ u := csInf_le hbdd huA
  have hut : u ≤ t := hu.2
  have hst : s ≤ t := hsu.trans hut
  have hts : t = s := le_antisymm ht.2 hst
  have : f t = ρ := by simpa only [hts] using hs2
  linarith

/-- A finite upper bound for internal distance gives a path with the
specified strict length bound. -/
theorem exists_path_of_internalMetric_le {D : ℂ → ℂ → ℝ} {U : Set ℂ}
    {x y : ℂ} {L : ℝ} (hL : 0 < L)
    (hbound : internalMetric D U x y ≤ ENNReal.ofReal L) :
    ∃ P : Path x y, (∀ t, P t ∈ U) ∧ pathLength D P < ENNReal.ofReal (2 * L) := by
  have hlt : internalMetric D U x y < ENNReal.ofReal (2 * L) :=
    hbound.trans_lt ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hL.le).2 (by linarith))
  simpa only [internalMetric, iInf_lt_iff, exists_prop] using hlt

/-- Stop a path at its first visit to a smaller sphere, without increasing
its length or leaving its original range. -/
theorem exists_first_sphere_subpath {D : ℂ → ℂ → ℝ} {x : ℂ}
    (P : Path x 0) {ρ : ℝ} (hρ : 0 ≤ ρ) (hx : ρ ≤ ‖x‖) :
    ∃ z : ℂ, ‖z‖ = ρ ∧ ∃ Q : Path x z,
      (∀ t, ρ ≤ ‖Q t‖) ∧ Set.range Q ⊆ Set.range P ∧
      pathLength D Q ≤ pathLength D P := by
  obtain ⟨s, hs, hnorm, hbefore⟩ := path_first_sphere P hx (by simpa using hρ)
  let u : unitInterval := ⟨s, hs⟩
  let Q := P.subpath 0 u
  have hu0 : (0 : unitInterval) ≤ u := u.property.1
  have hrange : Set.range Q = P '' Icc (0 : unitInterval) u :=
    P.range_subpath_of_le 0 u hu0
  have hQ : ∀ t, ρ ≤ ‖Q t‖ := by
    intro t
    have hm : Q t ∈ P '' Icc (0 : unitInterval) u := hrange ▸ mem_range_self t
    obtain ⟨v, hv, heq⟩ := hm
    rw [← heq, ← Path.extend_apply P v.property]
    exact hbefore v ⟨v.property.1, hv.2⟩
  have hsubset : Set.range Q ⊆ Set.range P := by
    rw [hrange]
    exact Set.image_subset_range _ _
  have hlen := pathLength_subpath_le D P 0 u hu0
  refine ⟨P u, ?_, Q.cast P.source.symm rfl, ?_, ?_, ?_⟩
  · simpa only [u, ← Path.extend_apply P hs] using hnorm
  · simpa only [Path.cast_coe] using hQ
  · simpa only [Path.cast_coe] using hsubset
  · simpa only [pathLength, Path.extend_cast] using hlen

/-- Arc-length parametrization preserves the image of a finite-length curve. -/
theorem IsEuclideanLengthMetric.exists_lengthParametrized_with_image
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {p : ℝ → ℂ} {T : ℝ} (hT : 0 ≤ T) (hp : ContinuousOn p (Icc 0 T))
    (hfinite : curveLength D p 0 T < ∞) :
    ∃ q : ℝ → ℂ, IsLengthParametrized D q (curveLength D p 0 T).toReal ∧
      q 0 = p 0 ∧ q (curveLength D p 0 T).toReal = p T ∧
      q '' Icc 0 (curveLength D p 0 T).toReal = p '' Icc 0 T := by
  obtain ⟨q, hq, hq0, hqT, htrack⟩ :=
    hD.exists_lengthParametrized_with_tracking hT hp hfinite
  have himage := (hD.cumulative_curveLength_properties hT hp hfinite).2.2.2
  refine ⟨q, hq, hq0, hqT, ?_⟩
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨u, hu, heu⟩ := (show t ∈ (fun v => (curveLength D p 0 v).toReal) '' Icc 0 T from
      himage.symm ▸ ht)
    change (curveLength D p 0 u).toReal = t at heu
    exact ⟨u, hu, by rw [← htrack u hu, heu]⟩
  · rintro ⟨t, ht, rfl⟩
    refine ⟨(curveLength D p 0 t).toReal, ?_, htrack t ht⟩
    rw [← himage]
    exact ⟨t, ht, rfl⟩

/-- A bounded internal distance supplies one arc-length-parametrized annular
piece, stopped on its first visit to the inner sphere. -/
theorem IsEuclideanLengthMetric.exists_short_annular_piece
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {x : ℂ} {ρ R L : ℝ} (hρ : 0 ≤ ρ) (hx : ρ ≤ ‖x‖) (hL : 0 < L)
    (hbound : internalMetric D (ball 0 R) x 0 ≤ ENNReal.ofReal L) :
    ∃ z : ℂ, ∃ T : ℝ, ∃ p : ℝ → ℂ,
      ‖z‖ = ρ ∧ IsLengthParametrized D p T ∧ p 0 = x ∧ p T = z ∧
      T < 2 * L ∧ ∀ t ∈ Icc 0 T, ρ ≤ ‖p t‖ ∧ p t ∈ ball (0 : ℂ) R := by
  obtain ⟨P, hPU, hPlen⟩ := exists_path_of_internalMetric_le hL hbound
  obtain ⟨z, hz, Q, hQnorm, hQrange, hQlen⟩ :=
    exists_first_sphere_subpath P hρ hx
  have hlt : pathLength D Q < ENNReal.ofReal (2 * L) := hQlen.trans_lt hPlen
  have hfinite : curveLength D Q.extend 0 1 < ∞ :=
    hlt.trans_le le_top
  obtain ⟨p, hp, hp0, hpT, himage⟩ :=
    hD.exists_lengthParametrized_with_image (by norm_num) Q.continuous_extend.continuousOn hfinite
  have hT : (curveLength D Q.extend 0 1).toReal < 2 * L := by
    have h := (ENNReal.toReal_lt_toReal hfinite.ne ENNReal.ofReal_ne_top).2 hlt
    simpa only [ENNReal.toReal_ofReal (by linarith : 0 ≤ 2 * L)] using h
  refine ⟨z, _, p, hz, hp, ?_, ?_, hT, ?_⟩
  · simpa only [Path.extend_zero] using hp0
  · simpa only [Path.extend_one] using hpT
  · intro t ht
    have hm : p t ∈ Q.extend '' Icc (0 : ℝ) 1 := himage ▸ ⟨t, ht, rfl⟩
    obtain ⟨v, hv, hvp⟩ := hm
    let u : unitInterval := ⟨v, hv⟩
    have heq : Q u = p t := by simpa only [u, Path.extend_apply Q hv] using hvp
    have hpRange : p t ∈ Set.range P := hQrange ⟨u, heq⟩
    obtain ⟨w, hw⟩ := hpRange
    constructor
    · rw [← heq]
      exact hQnorm u
    · rw [← hw]
      exact hPU w

/-- The logarithmic weight is bounded on an annulus by the appropriate
endpoint power, for either sign of the exponent. -/
theorem exp_neg_mul_log_le_annulus {β a b u : ℝ} (ha : 0 < a)
    (hau : a ≤ u) (hub : u ≤ b) :
    Real.exp (-β * Real.log u) ≤
      (if 0 ≤ β then a ^ (-β) else b ^ (-β)) := by
  have hu : 0 < u := ha.trans_le hau
  have hb : 0 < b := hu.trans_le hub
  by_cases hβ : 0 ≤ β
  · rw [ite_eq_left hβ, Real.rpow_def_of_pos ha]
    apply Real.exp_le_exp.mpr
    have hlog := Real.log_le_log ha hau
    nlinarith
  · rw [ite_eq_right hβ, Real.rpow_def_of_pos hb]
    apply Real.exp_le_exp.mpr
    have hlog := Real.log_le_log hu hub
    have hβ' : β < 0 := lt_of_not_ge hβ
    nlinarith

/-- The cost of a path staying in an annulus is bounded by its duration
times the endpoint power bound. -/
theorem annular_path_cost_le {β a b T : ℝ} {p : ℝ → ℂ}
    (ha : 0 < a) (hT : 0 ≤ T)
    (hp : ∀ t ∈ Icc 0 T, a ≤ ‖p t‖ ∧ ‖p t‖ ≤ b) :
    (∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (-β * Real.log ‖p t‖))) ≤
      ENNReal.ofReal (T * (if 0 ≤ β then a ^ (-β) else b ^ (-β))) := by
  let K : ℝ := if 0 ≤ β then a ^ (-β) else b ^ (-β)
  have hb : 0 < b := ha.trans_le ((hp 0 ⟨le_rfl, hT⟩).1.trans (hp 0 ⟨le_rfl, hT⟩).2)
  have hK : 0 ≤ K := by
    dsimp only [K]
    split <;> positivity
  calc
    _ ≤ ∫⁻ _ in Icc (0 : ℝ) T, ENNReal.ofReal K := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact ENNReal.ofReal_le_ofReal (exp_neg_mul_log_le_annulus ha (hp t ht).1 (hp t ht).2)
    _ = ENNReal.ofReal (T * K) := by
      simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc, sub_zero,
        ← ENNReal.ofReal_mul hK, mul_comm]

/-- A bounded internal distance supplies an annular piece with its explicit
logarithmic weighted-length bound. -/
theorem IsEuclideanLengthMetric.exists_short_weighted_annular_piece
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {x : ℂ} {ρ R L β : ℝ} (hρ : 0 < ρ) (hx : ρ ≤ ‖x‖) (hL : 0 < L)
    (hbound : internalMetric D (ball 0 R) x 0 ≤ ENNReal.ofReal L) :
    ∃ z : ℂ, ∃ T : ℝ, ∃ p : ℝ → ℂ,
      ‖z‖ = ρ ∧ IsLengthParametrized D p T ∧ p 0 = x ∧ p T = z ∧
      T ≤ 2 * L ∧ (∀ t ∈ Icc 0 T, ρ ≤ ‖p t‖ ∧ p t ∈ ball (0 : ℂ) R) ∧
      (∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (-β * Real.log ‖p t‖))) ≤
        ENNReal.ofReal (2 * L * (if 0 ≤ β then ρ ^ (-β) else R ^ (-β))) := by
  obtain ⟨z, T, p, hz, hp, hp0, hpT, hT, hann⟩ :=
    hD.exists_short_annular_piece hρ.le hx hL hbound
  have hann' : ∀ t ∈ Icc 0 T, ρ ≤ ‖p t‖ ∧ ‖p t‖ ≤ R := by
    intro t ht
    exact ⟨(hann t ht).1, (show ‖p t‖ < R by
      simpa only [mem_ball, dist_zero_right] using (hann t ht).2).le⟩
  have hR : 0 < R := hρ.trans_le ((hann' 0 ⟨le_rfl, hp.1⟩).1.trans
    (hann' 0 ⟨le_rfl, hp.1⟩).2)
  have hK : 0 ≤ (if 0 ≤ β then ρ ^ (-β) else R ^ (-β)) := by
    split <;> positivity
  refine ⟨z, T, p, hz, hp, hp0, hpT, hT.le, hann, ?_⟩
  exact (annular_path_cost_le hρ hp.1 hann').trans
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hT.le hK))

/-- Choose compatible weighted annular pieces, beginning with a point in
the specified band. -/
theorem IsEuclideanLengthMetric.exists_weighted_annular_pieces
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {r L : ℕ → ℝ} {β : ℝ} (hr : ∀ n, 0 < r n) (hanti : StrictAnti r)
    (hL : ∀ n, 0 < L n)
    (hdiam : ∀ n y z, y ∈ closedBall (0 : ℂ) (r n) →
      z ∈ closedBall (0 : ℂ) (r n) →
      internalMetric D (ball 0 (2 * r n)) y z ≤ ENNReal.ofReal (L n))
    {j : ℕ} {x : ℂ} (hx : ‖x‖ ≤ r j) (hx' : r (j + 1) ≤ ‖x‖) :
    ∃ z : ℕ → ℂ, ∃ T : ℕ → ℝ, ∃ p : ℕ → ℝ → ℂ,
      z 0 = x ∧ ∀ n,
        ‖z (n + 1)‖ = r (j + n + 1) ∧
        IsLengthParametrized D (p n) (T n) ∧ p n 0 = z n ∧ p n (T n) = z (n + 1) ∧
        T n ≤ 2 * L (j + n) ∧
        (∀ t ∈ Icc 0 (T n), r (j + n + 1) ≤ ‖p n t‖ ∧
          p n t ∈ ball (0 : ℂ) (2 * r (j + n))) ∧
        (∫⁻ t in Icc 0 (T n), ENNReal.ofReal (Real.exp (-β * Real.log ‖p n t‖))) ≤
          ENNReal.ofReal (smallPathCost r L β (j + n)) := by
  classical
  let State (n : ℕ) := {y : ℂ // ‖y‖ ≤ r (j + n) ∧ r (j + n + 1) ≤ ‖y‖}
  have hstep (n : ℕ) (y : State n) : ∃ z : ℂ, ∃ T : ℝ, ∃ p : ℝ → ℂ,
      ‖z‖ = r (j + n + 1) ∧ IsLengthParametrized D p T ∧ p 0 = y.1 ∧ p T = z ∧
      T ≤ 2 * L (j + n) ∧
      (∀ t ∈ Icc 0 T, r (j + n + 1) ≤ ‖p t‖ ∧
        p t ∈ ball (0 : ℂ) (2 * r (j + n))) ∧
      (∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (-β * Real.log ‖p t‖))) ≤
        ENNReal.ofReal (smallPathCost r L β (j + n)) := by
    have hy : y.1 ∈ closedBall (0 : ℂ) (r (j + n)) := by
      simpa only [mem_closedBall, dist_zero_right] using y.2.1
    have hzero : (0 : ℂ) ∈ closedBall 0 (r (j + n)) :=
      mem_closedBall_self (hr (j + n)).le
    simpa only [smallPathCost] using
      hD.exists_short_weighted_annular_piece (β := β) (hr (j + n + 1)) y.2.2
        (hL (j + n)) (hdiam (j + n) y.1 0 hy hzero)
  choose z T p hz hp hp0 hpT hT hpos hcost using hstep
  let next (n : ℕ) (y : State n) : State (n + 1) := ⟨z n y, by
    constructor
    · simpa only [Nat.add_succ] using (hz n y).le
    · have h := (hanti (show j + n + 1 < j + n + 1 + 1 by omega)).le
      simpa only [Nat.add_succ, ← hz n y] using h⟩
  let start : State 0 := ⟨x, by simpa only [add_zero] using ⟨hx, hx'⟩⟩
  let seq : (n : ℕ) → State n := fun n => Nat.rec start next n
  refine ⟨fun n => (seq n).1, fun n => T n (seq n), fun n => p n (seq n), rfl, ?_⟩
  intro n
  have hnext : (seq (n + 1)).1 = z n (seq n) := rfl
  refine ⟨?_, hp n (seq n), hp0 n (seq n), ?_, hT n (seq n),
    hpos n (seq n), hcost n (seq n)⟩
  · change ‖(seq (n + 1)).1‖ = r (j + n + 1)
    rw [hnext]; exact hz n (seq n)
  · change p n (seq n) (T n (seq n)) = (seq (n + 1)).1
    rw [hnext]; exact hpT n (seq n)

/-- Every time before the terminal time of a summable concatenation belongs
to one of its constituent pieces. -/
theorem IsEuclideanLengthMetric.summablePath_before_end_eq_piece
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {L : ℕ → ℝ} {p : ℕ → ℝ → ℂ} {S t : ℝ}
    (hp : ∀ n, IsLengthParametrized D (p n) (L n))
    (hjoin : ∀ n, p n (L n) = p (n + 1) 0) (hsum : HasSum L S)
    (hend : Tendsto (fun n => p n (L n)) atTop (𝓝 0)) (ht : t ∈ Ico 0 S) :
    ∃ n u, u ∈ Icc 0 (L n) ∧ summablePath L p S t = p n u := by
  have hL : ∀ n, 0 ≤ L n := fun n => (hp n).1
  have ht' : t ∈ ⋃ n, Ico (pathPieceStart L n) (pathPieceStart L (n + 1)) := by
    rw [iUnion_piece_intervals hL hsum]
    exact ht
  obtain ⟨n, hn⟩ := mem_iUnion.mp ht'
  let u := t - pathPieceStart L n
  have hu : u ∈ Icc 0 (L n) := by
    constructor
    · dsimp only [u]; linarith [hn.1]
    · have hn' := hn.2
      rw [pathPieceStart_succ] at hn'
      dsimp only [u]
      linarith
  refine ⟨n, u, hu, ?_⟩
  have heq := hD.summablePath_eq_piece hp hjoin hsum hend n hu
  have ht_eq : pathPieceStart L n + u = t := by dsimp [u]; ring
  simpa only [ht_eq] using heq

/-- If every constituent piece avoids the origin, their concatenation avoids it
at every time strictly before the terminal time. -/
theorem IsEuclideanLengthMetric.summablePath_ne_zero_before_end
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {L : ℕ → ℝ} {p : ℕ → ℝ → ℂ} {S t : ℝ}
    (hp : ∀ n, IsLengthParametrized D (p n) (L n))
    (hjoin : ∀ n, p n (L n) = p (n + 1) 0) (hsum : HasSum L S)
    (hend : Tendsto (fun n => p n (L n)) atTop (𝓝 0))
    (havoid : ∀ n u, u ∈ Icc 0 (L n) → p n u ≠ 0) (ht : t ∈ Ico 0 S) :
    summablePath L p S t ≠ 0 := by
  obtain ⟨n, u, hu, heq⟩ := hD.summablePath_before_end_eq_piece hp hjoin hsum hend ht
  rw [heq]
  exact havoid n u hu

/-- Pointwise properties enjoyed by all pieces hold for the concatenation
at every time strictly before its terminal time. -/
theorem IsEuclideanLengthMetric.summablePath_mem_before_end
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {L : ℕ → ℝ} {p : ℕ → ℝ → ℂ} {S t : ℝ} {A : Set ℂ}
    (hp : ∀ n, IsLengthParametrized D (p n) (L n))
    (hjoin : ∀ n, p n (L n) = p (n + 1) 0) (hsum : HasSum L S)
    (hend : Tendsto (fun n => p n (L n)) atTop (𝓝 0))
    (hmem : ∀ n u, u ∈ Icc 0 (L n) → p n u ∈ A) (ht : t ∈ Ico 0 S) :
    summablePath L p S t ∈ A := by
  obtain ⟨n, u, hu, heq⟩ := hD.summablePath_before_end_eq_piece hp hjoin hsum hend ht
  rw [heq]
  exact hmem n u hu

/-- Reverse a summable concatenation: the resulting path starts at the
origin, avoids it thereafter, and its weighted cost is the sum of the costs
of its pieces. -/
theorem IsEuclideanLengthMetric.reverse_summablePath
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {L : ℕ → ℝ} {p : ℕ → ℝ → ℂ} {S : ℝ} {A : Set ℂ}
    (hp : ∀ n, IsLengthParametrized D (p n) (L n))
    (hjoin : ∀ n, p n (L n) = p (n + 1) 0) (hsum : HasSum L S)
    (hend : Tendsto (fun n => p n (L n)) atTop (𝓝 0))
    (havoid : ∀ n u, u ∈ Icc 0 (L n) → p n u ≠ 0)
    (hmem : ∀ n u, u ∈ Icc 0 (L n) → p n u ∈ A) (h0 : (0 : ℂ) ∈ A)
    (F : ℂ → ℝ≥0∞) :
    ∃ q : ℝ → ℂ, IsLengthParametrized D q S ∧ q 0 = 0 ∧ q S = p 0 0 ∧
      (∀ t ∈ Icc 0 S, q t ∈ A) ∧ (∀ t ∈ Ioc 0 S, q t ≠ 0) ∧
      (∫⁻ t in Icc 0 S, F (q t)) =
        ∑' n, ∫⁻ t in Icc 0 (L n), F (p n t) := by
  let P := summablePath L p S
  let q : ℝ → ℂ := fun t => P (S - t)
  have hP : IsLengthParametrized D P S := hD.summablePath_parametrized hp hjoin hsum hend
  have hPS : P S = 0 := by simp [P, summablePath]
  have hP0 : P 0 = p 0 0 := by
    exact hD.summablePath_eq_first_piece hp hjoin hsum hend ⟨le_rfl, (hp 0).1⟩
  refine ⟨q, hD.isLengthParametrized_reverse hP, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [q, sub_zero] using hPS
  · simpa only [q, sub_self] using hP0
  · intro t ht
    by_cases ht0 : t = 0
    · simpa only [q, ht0, sub_zero, hPS] using h0
    · have hpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
      apply hD.summablePath_mem_before_end hp hjoin hsum hend hmem
      constructor <;> linarith [ht.2]
  · intro t ht
    apply hD.summablePath_ne_zero_before_end hp hjoin hsum hend havoid
    constructor <;> linarith [ht.1, ht.2]
  · calc
      _ = ∫⁻ t in Icc 0 S, F (P t) := lintegral_Icc_reverse (fun t => F (P t)) S
      _ = _ := hD.lintegral_summablePath hp hjoin hsum hend F

/-- A point in a given band can be joined to the origin with the bounds
associated with that band and all smaller scales. -/
theorem IsEuclideanLengthMetric.exists_smallWeightedPath_in_band
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {r L : ℕ → ℝ} {β : ℝ} (hr : ∀ n, 0 < r n) (hanti : StrictAnti r)
    (hrlim : Tendsto r atTop (𝓝 0)) (hL : ∀ n, 0 < L n) (hsL : Summable L)
    (hsU : Summable (smallPathCost r L β))
    (hdiam : ∀ n y z, y ∈ closedBall (0 : ℂ) (r n) →
      z ∈ closedBall (0 : ℂ) (r n) →
      internalMetric D (ball 0 (2 * r n)) y z ≤ ENNReal.ofReal (L n))
    {j : ℕ} {x : ℂ} (hx : ‖x‖ ≤ r j) (hx' : r (j + 1) ≤ ‖x‖) :
    ∃ T : ℝ, ∃ p : ℝ → ℂ, IsLengthParametrized D p T ∧ p 0 = 0 ∧ p T = x ∧
      (∀ t ∈ Icc 0 T, p t ∈ ball (0 : ℂ) (2 * r j)) ∧
      (∀ t ∈ Ioc 0 T, p t ≠ 0) ∧ T ≤ 2 * (∑' n, L (j + n)) ∧
      (∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (-β * Real.log ‖p t‖))) ≤
        ENNReal.ofReal (∑' n, smallPathCost r L β (j + n)) := by
  obtain ⟨z, T, p, hz0, hpiece⟩ :=
    hD.exists_weighted_annular_pieces hr hanti hL hdiam hx hx'
  have hp : ∀ n, IsLengthParametrized D (p n) (T n) := fun n => (hpiece n).2.1
  have hjoin : ∀ n, p n (T n) = p (n + 1) 0 := by
    intro n
    exact (hpiece n).2.2.2.1.trans ((hpiece (n + 1)).2.2.1.symm)
  have hsL' : Summable (fun n => L (j + n)) := by
    simpa only [Nat.add_comm] using (summable_nat_add_iff j).2 hsL
  have hsU' : Summable (fun n => smallPathCost r L β (j + n)) := by
    simpa only [Nat.add_comm] using (summable_nat_add_iff j).2 hsU
  have hsT : Summable T := Summable.of_nonneg_of_le (fun n => (hp n).1)
    (fun n => (hpiece n).2.2.2.2.1) (hsL'.mul_left 2)
  have hrshift : Tendsto (fun n => r (j + n)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.add_comm] using hrlim.comp (tendsto_add_atTop_nat j)
  have hr2 : Tendsto (fun n => 2 * r (j + n)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hrshift.const_mul 2
  have hball : ∀ n t, t ∈ Icc 0 (T n) → ‖p n t‖ ≤ 2 * r (j + n) := by
    intro n t ht
    exact (show ‖p n t‖ < 2 * r (j + n) by
      simpa only [mem_ball, dist_zero_right] using ((hpiece n).2.2.2.2.2.1 t ht).2).le
  have hend := tendsto_piece_endpoints_of_norm_le (fun n => (hp n).1) hr2 hball
  have havoid : ∀ n t, t ∈ Icc 0 (T n) → p n t ≠ 0 := by
    intro n t ht hzero
    have h := ((hpiece n).2.2.2.2.2.1 t ht).1
    rw [hzero, norm_zero] at h
    exact (not_le_of_gt (hr (j + n + 1))) h
  have hmem : ∀ n t, t ∈ Icc 0 (T n) → p n t ∈ ball (0 : ℂ) (2 * r j) := by
    intro n t ht
    have hrad : r (j + n) ≤ r j := hanti.antitone (by omega)
    apply (ball_subset_ball (by linarith : 2 * r (j + n) ≤ 2 * r j))
    exact ((hpiece n).2.2.2.2.2.1 t ht).2
  have h0 : (0 : ℂ) ∈ ball 0 (2 * r j) := mem_ball_self (by linarith [hr j])
  obtain ⟨q, hq, hq0, hqT, hqmem, hqavoid, hqcost⟩ :=
    hD.reverse_summablePath hp hjoin hsT.hasSum hend havoid hmem h0
      (fun x => ENNReal.ofReal (Real.exp (-β * Real.log ‖x‖)))
  have hlen : (∑' n, T n) ≤ 2 * (∑' n, L (j + n)) := by
    have h := Summable.tsum_le_tsum (fun n => (hpiece n).2.2.2.2.1) hsT (hsL'.mul_left 2)
    simpa only [tsum_mul_left] using h
  have hcost : (∑' n, ∫⁻ t in Icc 0 (T n),
      ENNReal.ofReal (Real.exp (-β * Real.log ‖p n t‖))) ≤
      ENNReal.ofReal (∑' n, smallPathCost r L β (j + n)) := by
    rw [ENNReal.ofReal_tsum_of_nonneg (fun n => smallPathCost_nonneg hr hL (j + n)) hsU']
    exact ENNReal.tsum_le_tsum (fun n => (hpiece n).2.2.2.2.2.2)
  refine ⟨_, q, hq, hq0, ?_, hqmem, hqavoid, hlen, hqcost.le.trans hcost⟩
  rw [hqT, (hpiece 0).2.2.1, hz0]

/-- The constant path on a zero-length interval is length-parametrized. -/
theorem IsEuclideanLengthMetric.isLengthParametrized_const_zero
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) (x : ℂ) :
    IsLengthParametrized D (fun _ => x) 0 := by
  refine ⟨le_rfl, continuousOn_const, ?_⟩
  intro s t hs hst ht
  have hs0 : s = 0 := le_antisymm (hst.trans ht) hs
  have ht0 : t = 0 := le_antisymm ht (hs.trans hst)
  subst s
  subst t
  simp [curveLength, hD.self_eq_zero]

/-- Diameter bounds and summable annular costs construct a small weighted
path from the origin to every point of the initial closed ball. -/
theorem IsEuclideanLengthMetric.smallWeightedPathExistence
    {D : ℂ → ℂ → ℝ} {r L : ℕ → ℝ} {β : ℝ} :
    SmallWeightedPathExistence D r L β := by
  intro hD hr hanti hrlim hL hsL hsU hdiam i x hx
  by_cases hx0 : x = 0
  · subst x
    refine ⟨0, fun _ => 0, hD.isLengthParametrized_const_zero 0, rfl, rfl, ?_, ?_, ?_, ?_⟩
    · intro t ht
      exact mem_ball_self (by linarith [hr i])
    · intro t ht
      exact (not_lt_of_ge ht.2 ht.1).elim
    · have htail : 0 ≤ ∑' n, L (i + n) := tsum_nonneg (fun n => (hL (i + n)).le)
      linarith
    · simp [lintegral_const]
  · have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    obtain ⟨j, hij, hjlt, hjle⟩ := exists_radius_band hrlim hnorm hx
    obtain ⟨T, p, hp, hp0, hpT, hmem, havoid, hlen, hcost⟩ :=
      hD.exists_smallWeightedPath_in_band hr hanti hrlim hL hsL hsU hdiam hjle hjlt.le
    have hrad : r j ≤ r i := hanti.antitone hij
    have hlen' : 2 * (∑' n, L (j + n)) ≤ 2 * (∑' n, L (i + n)) :=
      mul_le_mul_of_nonneg_left (tsum_tail_le hsL (fun n => (hL n).le) hij) (by norm_num)
    have hcost' : (∑' n, smallPathCost r L β (j + n)) ≤
        ∑' n, smallPathCost r L β (i + n) :=
      tsum_tail_le hsU (smallPathCost_nonneg hr hL) hij
    refine ⟨T, p, hp, hp0, hpT, ?_, havoid, hlen.trans hlen',
      hcost.trans (ENNReal.ofReal_le_ofReal hcost')⟩
    intro t ht
    exact ball_subset_ball (by linarith : 2 * r j ≤ 2 * r i) (hmem t ht)

/-- The constructed path, once available, bounds the corresponding Weyl distance. -/
theorem weylScaling_le_of_smallWeightedPath {D : ℂ → ℂ → ℝ} {β B T : ℝ}
    {p : ℝ → ℂ} {x : ℂ} (hp : IsLengthParametrized D p T)
    (hp0 : p 0 = 0) (hpT : p T = x)
    (hcost : (∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (-β * Real.log ‖p t‖))) ≤
      ENNReal.ofReal B) :
    weylScaling D 1 (fun z => -β * Real.log ‖z‖) 0 x ≤ ENNReal.ofReal B := by
  calc
    _ ≤ ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (1 * (-β * Real.log ‖p t‖))) :=
      (iInf₂_le T p).trans ((iInf₂_le hp hp0).trans (iInf_le _ hpT))
    _ ≤ ENNReal.ofReal B := by simpa only [one_mul] using hcost
/-- The Weyl distance from the origin is bounded by the tail of the
annular weighted costs. -/
theorem IsEuclideanLengthMetric.weylScaling_le_smallPathCost_tail
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {r L : ℕ → ℝ} {β : ℝ} (hr : ∀ n, 0 < r n) (hanti : StrictAnti r)
    (hrlim : Tendsto r atTop (𝓝 0)) (hL : ∀ n, 0 < L n) (hsL : Summable L)
    (hsU : Summable (smallPathCost r L β))
    (hdiam : ∀ n y z, y ∈ closedBall (0 : ℂ) (r n) →
      z ∈ closedBall (0 : ℂ) (r n) →
      internalMetric D (ball 0 (2 * r n)) y z ≤ ENNReal.ofReal (L n))
    (i : ℕ) {x : ℂ} (hx : ‖x‖ ≤ r i) :
    weylScaling D 1 (fun z => -β * Real.log ‖z‖) 0 x ≤
      ENNReal.ofReal (∑' n, smallPathCost r L β (i + n)) := by
  obtain ⟨T, p, hp, hp0, hpT, _, _, _, hcost⟩ :=
    IsEuclideanLengthMetric.smallWeightedPathExistence hD hr hanti hrlim hL hsL hsU hdiam i x hx
  exact weylScaling_le_of_smallWeightedPath hp hp0 hpT hcost

/-- The Weyl-distance bounds hold uniformly on shrinking closed balls and
converge to zero as the scale index tends to infinity. -/
theorem IsEuclideanLengthMetric.uniform_weylScaling_small_closedBall
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {r L : ℕ → ℝ} {β : ℝ} (hr : ∀ n, 0 < r n) (hanti : StrictAnti r)
    (hrlim : Tendsto r atTop (𝓝 0)) (hL : ∀ n, 0 < L n) (hsL : Summable L)
    (hsU : Summable (smallPathCost r L β))
    (hdiam : ∀ n y z, y ∈ closedBall (0 : ℂ) (r n) →
      z ∈ closedBall (0 : ℂ) (r n) →
      internalMetric D (ball 0 (2 * r n)) y z ≤ ENNReal.ofReal (L n)) :
    ∀ ε : ℝ, 0 < ε → ∃ N, ∀ i ≥ N, ∀ x : ℂ, ‖x‖ ≤ r i →
      weylScaling D 1 (fun z => -β * Real.log ‖z‖) 0 x ≤ ENNReal.ofReal ε := by
  intro ε hε
  have hev : ∀ᶠ i : ℕ in atTop, (∑' n, smallPathCost r L β (i + n)) < ε :=
    (tendsto_smallPath_tail (smallPathCost r L β)).eventually (eventually_lt_nhds hε)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine ⟨N, ?_⟩
  intro i hi x hx
  exact (hD.weylScaling_le_smallPathCost_tail hr hanti hrlim hL hsL hsU hdiam i hx).trans
    (ENNReal.ofReal_le_ofReal (hN i hi).le)



end HarmonicBalls
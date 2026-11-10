import HarmonicBalls.FirstPass.S11m.ClearanceLocal
import HarmonicBalls.Steps.Sec11.InternalMetricContinuity
import HarmonicBalls.Steps.Sec11.InternalMetricPaths
import HarmonicBalls.Steps.Sec11.LocalPathLength
import HarmonicBalls.FirstPass.S11r.CurveLengthPieces
import HarmonicBalls.Steps.Sec11.WeylPathConcatenation
import HarmonicBalls.FirstPass.S11m.Finiteness

/-!
# Internalization of the localized clearance chains (fp-S11m, owner z4)

Route: `notes/fp-gaps/CHATGPT-z4-11-12-local-certificate.md`, section 4.3 (internalization is a countable operation),
deterministic identity (L-EQ). Let `D` be a Euclidean length metric, `V` open, `O ⊆ V` open, `S ⊆ V` with `O ⊆ closure S`
(the vertices) and `Q ⊆ V \ O` with `V \ O ⊆ closure Q` (the clearance set). Then the localized chain infimum with cost
`internalMetric D V` (the internal, i.e. path, distance of `D` in `V`; Armitage-Gardiner terminology) equals the
internal distance `internalMetric D O` on `O`.

The first inequality: a permitted edge is realised inside `O` by a path almost as short as its `V`-cost
(`internalMetric_O_le_of_clearance`, a first-exit argument). The second: a path in `O` is cut into a fine grid, whose
vertices are dense vertices near the path (`exists_localClearanceChain`).
-/

namespace HarmonicBalls.S11m

open Set Metric Topology Filter unitInterval
open scoped ENNReal

variable {D : ℂ → ℂ → ℝ}

/-- The real internal distance of `V`: the cost of the localized chains of `ClearanceLocal`. -/
noncomputable def internalCost (D : ℂ → ℂ → ℝ) (V : Set ℂ) (v w : ℂ) : ℝ :=
  (internalMetric D V v w).toReal

theorem clearanceEq_nonneg (hD : IsEuclideanLengthMetric D) (x y : ℂ) : 0 ≤ D x y := by
  have ht := hD.triangle x y x
  rw [hD.self_eq_zero, hD.symm y x] at ht
  linarith

theorem ofReal_le_of_le_toReal {δ : ℝ} {x : ℝ≥0∞} (h : δ ≤ x.toReal) : ENNReal.ofReal δ ≤ x := by
  rcases eq_or_ne x ⊤ with rfl | hx
  · exact le_top
  · exact (ENNReal.ofReal_le_iff_le_toReal hx).2 h

/-- A prefix of a path lying in `V` is a path in `V`, so the `V`-distance to its endpoint is at most the length of the
whole path. -/
theorem internalMetric_le_pathLength_prefix {V : Set ℂ} {v w : ℂ} (P : Path v w) (hP : ∀ t, P t ∈ V) (t : I) :
    internalMetric D V v (P t) ≤ pathLength D P := by
  let q : Path v (P t) := (P.subpath 0 t).cast P.source.symm rfl
  calc internalMetric D V v (P t) ≤ pathLength D q := iInf₂_le q (fun τ => hP _)
    _ ≤ pathLength D P := pathLength_subpath_le D P 0 t (Subtype.coe_le_coe.mp (by simpa using t.2.1))

/-- The `V`-distance from a point of `V` is continuous in its second variable (`V` open). -/
theorem continuousAt_internalMetric_right (hD : IsEuclideanLengthMetric D) {V : Set ℂ} (hVo : IsOpen V) {z : ℂ}
    (hz : z ∈ V) : ContinuousAt (fun q => internalMetric D V z q) z := by
  have h := hD.continuousOn_internalMetric_pair (clearanceEq_nonneg hD) hVo
  have hc : ContinuousOn (fun q => internalMetric D V z q) V :=
    h.comp (continuous_const.prodMk continuous_id).continuousOn fun q hq => ⟨hz, hq⟩
  exact hc.continuousAt (hVo.mem_nhds hz)

/-- The `V`-distance to a point of `V` is continuous in its first variable (`V` open). -/
theorem continuousAt_internalMetric_left (hD : IsEuclideanLengthMetric D) {V : Set ℂ} (hVo : IsOpen V) {z : ℂ}
    (hz : z ∈ V) : ContinuousAt (fun q => internalMetric D V q z) z := by
  have h := hD.continuousOn_internalMetric_pair (clearanceEq_nonneg hD) hVo
  have hc : ContinuousOn (fun q => internalMetric D V q z) V :=
    h.comp (continuous_id.prodMk continuous_const).continuousOn fun q hq => ⟨hq, hz⟩
  exact hc.continuousAt (hVo.mem_nhds hz)

theorem internalMetric_self_zero (hD : IsEuclideanLengthMetric D) {V : Set ℂ} (hVo : IsOpen V) {z : ℂ}
    (hz : z ∈ V) : internalMetric D V z z = 0 :=
  hD.internalMetric_self_of_mem_open (clearanceEq_nonneg hD) hVo hz

/-- Permitted edges stay in `O` (route 4.3, first inequality). If the `V`-cost from `v` to `w` is below `δ`, and every
point of `Q` has `V`-cost at least `δ` from `v`, then the internal distance of `O` between `v` and `w` is at most their
`V`-distance. Proof: a path in `V` of nearly minimal length which leaves `O` passes through `V \ O ⊆ closure Q`, and a
point `q ∈ Q` near that exit point has `V`-cost from `v` below `δ`, a contradiction. -/
theorem internalMetric_O_le_of_clearance (hD : IsEuclideanLengthMetric D) {V O Q : Set ℂ} (hVo : IsOpen V)
    (hQd : V \ O ⊆ closure Q) {v w : ℂ} (hfin : internalMetric D V v w ≠ ⊤) {δ : ℝ}
    (hedge : internalCost D V v w < δ) (hcl : ∀ q ∈ Q, δ ≤ internalCost D V v q) :
    internalMetric D O v w ≤ internalMetric D V v w := by
  set a := internalCost D V v w with ha_def
  have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
  have hwe : internalMetric D V v w = ENNReal.ofReal a := by
    rw [ha_def]
    unfold internalCost
    exact (ENNReal.ofReal_toReal hfin).symm
  have key : ∀ ε : ℝ, 0 < ε → 2 * ε < δ - a → internalMetric D O v w ≤ ENNReal.ofReal (a + ε) := by
    intro ε hε hεδ
    have hlt : internalMetric D V v w < ENNReal.ofReal (a + ε) := by
      rw [hwe]
      exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
    obtain ⟨P, hP⟩ := iInf_lt_iff.mp hlt
    obtain ⟨hPV, hPc⟩ := iInf_lt_iff.mp hP
    have hPO : ∀ t, P t ∈ O := by
      intro t
      by_contra htO
      have hzV : P t ∈ V \ O := ⟨hPV t, htO⟩
      have hev : ∀ᶠ q in 𝓝 (P t), internalMetric D V (P t) q < ENNReal.ofReal ε := by
        have h0 : internalMetric D V (P t) (P t) < ENNReal.ofReal ε := by
          rw [internalMetric_self_zero hD hVo (hPV t)]
          exact ENNReal.ofReal_pos.2 hε
        exact (continuousAt_internalMetric_right hD hVo (hPV t)).eventually_lt continuousAt_const h0
      obtain ⟨q, hq, hqQ⟩ := (mem_closure_iff_nhds.mp (hQd hzV)) _ hev
      have h1 : internalMetric D V v (P t) < ENNReal.ofReal (a + ε) :=
        lt_of_le_of_lt (internalMetric_le_pathLength_prefix P hPV t) hPc
      have h3 : internalMetric D V v q < ENNReal.ofReal (a + 2 * ε) := by
        rw [show a + 2 * ε = (a + ε) + ε by ring, ENNReal.ofReal_add (by linarith) hε.le]
        exact (hD.internalMetric_triangle V v (P t) q).trans_lt (ENNReal.add_lt_add h1 hq)
      have h4 : ENNReal.ofReal δ ≤ internalMetric D V v q := ofReal_le_of_le_toReal (hcl q hqQ)
      have h5 : δ < a + 2 * ε := (ENNReal.ofReal_lt_ofReal_iff (by linarith)).1 (h4.trans_lt h3)
      linarith
    calc internalMetric D O v w ≤ pathLength D P := iInf₂_le P hPO
      _ ≤ ENNReal.ofReal (a + ε) := hPc.le
  rw [hwe]
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hgap : 0 < δ - a := by linarith
  have hη0 : 0 < min (ε : ℝ) ((δ - a) / 4) := lt_min (by exact_mod_cast hε) (by linarith)
  have hηε : min (ε : ℝ) ((δ - a) / 4) ≤ ε := min_le_left _ _
  have hηg : min (ε : ℝ) ((δ - a) / 4) ≤ (δ - a) / 4 := min_le_right _ _
  calc internalMetric D O v w ≤ ENNReal.ofReal (a + min (ε : ℝ) ((δ - a) / 4)) :=
        key _ hη0 (by linarith)
    _ = ENNReal.ofReal a + ENNReal.ofReal (min (ε : ℝ) ((δ - a) / 4)) :=
        ENNReal.ofReal_add ha0 hη0.le
    _ ≤ ENNReal.ofReal a + ε := by
        gcongr
        exact (ENNReal.ofReal_le_ofReal hηε).trans_eq ENNReal.ofReal_coe_nnreal

/-- The vertices of a dense chain lie in `V`, when its endpoints and its vertex set do. -/
theorem denseChainVertex_mem {S V : Set ℂ} (hSV : S ⊆ V) {x y : ℂ} (hx : x ∈ V) (hy : y ∈ V)
    (k : Σ n : ℕ, Fin n → S) {i : ℕ} : denseChainVertex x y k i ∈ V := by
  unfold denseChainVertex
  split_ifs with h0 h
  · exact hx
  · exact hSV (k.2 ⟨i - 1, by omega⟩).2
  · exact hy

/-- Lower bound (route 4.3, first inequality): every localized chain from `x` to `y` in `O` costs at least the internal
distance of `O` between `x` and `y`, by the permitted-edge lemma and the triangle inequality of `O`. -/
theorem internalMetric_le_localClearanceCost (hD : IsEuclideanLengthMetric D) {V O S Q : Set ℂ} (hVo : IsOpen V)
    (hO : IsOpen O) (hOV : O ⊆ V) (hSV : S ⊆ V) (hQd : V \ O ⊆ closure Q)
    (hfin : ∀ v ∈ V, ∀ w ∈ V, internalMetric D V v w ≠ ⊤) {x y : ℂ} (hx : x ∈ O) (hy : y ∈ O)
    (k : Σ n : ℕ, Fin n → S) :
    internalMetric D O x y ≤ localClearanceCost Q (internalCost D V) x y k := by
  unfold localClearanceCost
  split_ifs with hcond
  swap
  · exact le_top
  have hedge : ∀ i < k.1 + 1, internalMetric D O (denseChainVertex x y k i) (denseChainVertex x y k (i + 1)) ≤
      ENNReal.ofReal (internalCost D V (denseChainVertex x y k i) (denseChainVertex x y k (i + 1))) := by
    intro i hi
    obtain ⟨δ, -, h1, h2⟩ := hcond i hi
    have hv := denseChainVertex_mem hSV (hOV hx) (hOV hy) k (i := i)
    have hw := denseChainVertex_mem hSV (hOV hx) (hOV hy) k (i := i + 1)
    have hfinE := hfin _ hv _ hw
    calc internalMetric D O (denseChainVertex x y k i) (denseChainVertex x y k (i + 1))
        ≤ internalMetric D V (denseChainVertex x y k i) (denseChainVertex x y k (i + 1)) :=
          internalMetric_O_le_of_clearance hD hVo hQd hfinE h1 h2
      _ = ENNReal.ofReal (internalCost D V (denseChainVertex x y k i) (denseChainVertex x y k (i + 1))) :=
          (ENNReal.ofReal_toReal hfinE).symm
  have hstep : ∀ j ≤ k.1 + 1, internalMetric D O x (denseChainVertex x y k j) ≤
      ∑ i ∈ Finset.range j, ENNReal.ofReal (internalCost D V (denseChainVertex x y k i)
        (denseChainVertex x y k (i + 1))) := by
    intro j
    induction j with
    | zero =>
      intro _
      rw [denseChainVertex_start, Finset.range_zero, Finset.sum_empty]
      rw [hD.internalMetric_self_of_mem_open (clearanceEq_nonneg hD) hO hx]
    | succ j ih =>
      intro hj
      calc internalMetric D O x (denseChainVertex x y k (j + 1))
          ≤ internalMetric D O x (denseChainVertex x y k j) +
            internalMetric D O (denseChainVertex x y k j) (denseChainVertex x y k (j + 1)) :=
            hD.internalMetric_triangle O _ _ _
        _ ≤ (∑ i ∈ Finset.range j, ENNReal.ofReal (internalCost D V (denseChainVertex x y k i)
              (denseChainVertex x y k (i + 1)))) +
            ENNReal.ofReal (internalCost D V (denseChainVertex x y k j) (denseChainVertex x y k (j + 1))) :=
            add_le_add (ih (by omega)) (hedge j (by omega))
        _ = ∑ i ∈ Finset.range (j + 1), ENNReal.ofReal (internalCost D V (denseChainVertex x y k i)
              (denseChainVertex x y k (i + 1))) := (Finset.sum_range_succ _ _).symm
  have := hstep (k.1 + 1) le_rfl
  rw [denseChainVertex_end] at this
  exact this

/-- Lower bound for the localized infimum: `internalMetric D O x y ≤ localClearanceInf`. -/
theorem internalMetric_le_localClearanceInf (hD : IsEuclideanLengthMetric D) {V O S Q : Set ℂ} (hVo : IsOpen V)
    (hO : IsOpen O) (hOV : O ⊆ V) (hSV : S ⊆ V) (hQd : V \ O ⊆ closure Q)
    (hfin : ∀ v ∈ V, ∀ w ∈ V, internalMetric D V v w ≠ ⊤) {x y : ℂ} (hx : x ∈ O) (hy : y ∈ O) :
    internalMetric D O x y ≤ localClearanceInf S Q (internalCost D V) x y := by
  unfold localClearanceInf
  exact le_iInf fun k => internalMetric_le_localClearanceCost hD hVo hO hOV hSV hQd hfin hx hy k

theorem internalCost_nonneg (D : ℂ → ℂ → ℝ) (V : Set ℂ) (v w : ℂ) : 0 ≤ internalCost D V v w :=
  ENNReal.toReal_nonneg

theorem internalCost_symm (hD : IsEuclideanLengthMetric D) (V : Set ℂ) (v w : ℂ) :
    internalCost D V v w = internalCost D V w v := by
  unfold internalCost
  rw [hD.internalMetric_symm V v w]

/-- The real `V`-cost satisfies the triangle inequality on `V`. -/
theorem internalCost_triangle (hD : IsEuclideanLengthMetric D) {V : Set ℂ}
    (hfin : ∀ v ∈ V, ∀ w ∈ V, internalMetric D V v w ≠ ⊤) {v z w : ℂ} (hv : v ∈ V) (hz : z ∈ V) (hw : w ∈ V) :
    internalCost D V v w ≤ internalCost D V v z + internalCost D V z w := by
  unfold internalCost
  rw [← ENNReal.toReal_add (hfin v hv z hz) (hfin z hz w hw)]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin v hv z hz, hfin z hz w hw⟩)
    (hD.internalMetric_triangle V v z w)

/-- The `V`-cost dominates the Euclidean-length distance `D` of the ambient length metric. -/
theorem dist_le_internalCost (hD : IsEuclideanLengthMetric D) {V : Set ℂ} {z w : ℂ}
    (hzw : internalMetric D V z w ≠ ⊤) : D z w ≤ internalCost D V z w := by
  unfold internalCost
  rw [← ENNReal.ofReal_le_iff_le_toReal hzw, hD.ofReal_eq_internalMetric z w]
  exact internalMetric_anti D (subset_univ V) z w

/-- The length of the subarc `γ([s, t])` bounds the internal distance between its endpoints. -/
theorem internalMetric_le_curveLength_arc {x y : ℂ} (γ : Path x y) {V : Set ℂ} (hγV : ∀ t, γ t ∈ V) {s t : I}
    (hst : s ≤ t) :
    internalMetric D V (γ s) (γ t) ≤ curveLength D γ.extend (s : ℝ) (t : ℝ) := by
  have hst' : (s : ℝ) ≤ t := hst
  have heq : EqOn (γ.subpath s t).extend (fun τ => γ.extend ((s : ℝ) + τ * ((t : ℝ) - s))) (Icc (0 : ℝ) 1) := by
    intro u hu
    dsimp only
    have hmem : (s : ℝ) + u * ((t : ℝ) - s) ∈ Icc (0 : ℝ) 1 := by
      constructor
      · nlinarith [s.2.1, mul_nonneg hu.1 (sub_nonneg.2 hst')]
      · nlinarith [mul_nonneg (sub_nonneg.2 hu.2) (sub_nonneg.2 s.2.2),
          mul_nonneg hu.1 (sub_nonneg.2 t.2.2)]
    rw [Path.extend_apply _ hu, Path.extend_apply _ hmem]
    exact congrArg γ (Subtype.ext (by simp [Icc.convexComb]; ring))
  calc internalMetric D V (γ s) (γ t) ≤ pathLength D (γ.subpath s t) :=
        iInf₂_le (γ.subpath s t) (fun τ => hγV _)
    _ = curveLength D (γ.subpath s t).extend 0 1 := rfl
    _ = curveLength D (fun τ => γ.extend ((s : ℝ) + τ * ((t : ℝ) - s))) 0 1 :=
        curveLength_eq_of_eqOn heq
    _ ≤ curveLength D γ.extend (s : ℝ) (t : ℝ) := curveLength_affine_reparam_le D γ.extend hst'

/-- Superadditivity of curve length over a monotone partition. -/
theorem sum_curveLength_le (D : ℂ → ℂ → ℝ) (p : ℝ → ℂ) {u : ℕ → ℝ} (hu : Monotone u) (N : ℕ) :
    ∑ i ∈ Finset.range N, curveLength D p (u i) (u (i + 1)) ≤ curveLength D p (u 0) (u N) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    calc ∑ i ∈ Finset.range N, curveLength D p (u i) (u (i + 1)) + curveLength D p (u N) (u (N + 1))
        ≤ curveLength D p (u 0) (u N) + curveLength D p (u N) (u (N + 1)) := add_le_add ih le_rfl
      _ ≤ curveLength D p (u 0) (u (N + 1)) :=
          curveLength_add_le_general D p (hu (Nat.zero_le N)) (hu (Nat.le_succ N))

/-- Uniform clearance (route 4.3): a path in the open set `O` has a positive common `D`-clearance from `Oᶜ`. The
image of the path is compact and covered by half-radius `D`-balls, so finitely many suffice. -/
theorem exists_uniform_clearance (hD : IsEuclideanLengthMetric D) {O : Set ℂ} (hO : IsOpen O) {x y : ℂ}
    (γ : Path x y) (hγ : ∀ t, γ t ∈ O) : ∃ c : ℝ, 0 < c ∧ ∀ t : I, ∀ z ∉ O, c ≤ D (γ t) z := by
  have hρ : ∀ t : I, ∃ ρ : ℝ, 0 < ρ ∧ ∀ z, D (γ t) z < ρ → z ∈ O := by
    intro t
    obtain ⟨ρ, hρ, hball⟩ := (hD.isOpen_iff O).1 hO (γ t) (hγ t)
    exact ⟨ρ, hρ, hball⟩
  choose ρ hρpos hρO using hρ
  have hUo : ∀ t : I, IsOpen {z | D (γ t) z < ρ t / 2} := by
    intro t
    refine (hD.isOpen_iff _).2 fun z hz => ⟨ρ t / 2 - D (γ t) z, ?_, fun w hw => ?_⟩
    · have hz' : D (γ t) z < ρ t / 2 := hz
      linarith
    · have hz' : D (γ t) z < ρ t / 2 := hz
      have ht := hD.triangle (γ t) z w
      show D (γ t) w < ρ t / 2
      linarith
  have hcov : range γ ⊆ ⋃ t : I, {z | D (γ t) z < ρ t / 2} := by
    rintro _ ⟨t, rfl⟩
    refine mem_iUnion.2 ⟨t, ?_⟩
    show D (γ t) (γ t) < ρ t / 2
    rw [hD.self_eq_zero]
    exact half_pos (hρpos t)
  obtain ⟨T, hT⟩ := (isCompact_range γ.continuous).elim_finite_subcover _ hUo hcov
  have hTne : T.Nonempty := by
    rcases T.eq_empty_or_nonempty with h | h
    · have h0 := hT (mem_range_self (0 : I))
      simp [h] at h0
    · exact h
  obtain ⟨t₀, ht₀, hmin⟩ := Finset.exists_min_image T (fun t => ρ t) hTne
  refine ⟨ρ t₀ / 2, half_pos (hρpos t₀), fun s z hz => ?_⟩
  obtain ⟨t, htT, hst⟩ := mem_iUnion₂.1 (hT (mem_range_self s))
  have hm : ρ t₀ ≤ ρ t := hmin t htT
  have hst' : D (γ t) (γ s) < ρ t / 2 := hst
  have h1 : ρ t ≤ D (γ t) z := not_lt.1 fun h => hz (hρO t z h)
  have ht := hD.triangle (γ t) (γ s) z
  linarith

/-- Upper bound (route 4.3, second inequality): a path `γ` in `O` yields, for each `η > 0`, a localized chain from `x`
to `y` whose cost is at most `pathLength γ + η`. Grid `g i = min (i/(n+1)) 1`; `c` is the uniform clearance of `γ`
from `Oᶜ`; `δ` comes from the uniform continuity of the `V`-cost along `γ`, so consecutive grid points are `c/4`-close;
the interior vertices lie in `S` within `ε ≤ c/8` of `γ (g i)`, with `2 ε (n+1) ≤ η`. -/
theorem exists_localClearanceChain (hD : IsEuclideanLengthMetric D) {V O S Q : Set ℂ} (hO : IsOpen O)
    (hVo : IsOpen V) (hOV : O ⊆ V) (hSV : S ⊆ V) (hS : O ⊆ closure S) (hQV : Q ⊆ V \ O)
    (hfin : ∀ v ∈ V, ∀ w ∈ V, internalMetric D V v w ≠ ⊤) {x y : ℂ} (hx : x ∈ O) (hy : y ∈ O)
    (γ : Path x y) (hγ : ∀ t, γ t ∈ O) {η : ℝ} (hη : 0 < η) :
    ∃ k : Σ n : ℕ, Fin n → S,
      localClearanceCost Q (internalCost D V) x y k ≤ pathLength D γ + ENNReal.ofReal η := by
  obtain ⟨c, hc, hcle⟩ := exists_uniform_clearance hD hO γ hγ
  have hγV : ∀ t, γ t ∈ V := fun t => hOV (hγ t)
  have hG : Continuous fun p : I × I => internalCost D V (γ p.1) (γ p.2) := by
    have hc2 := hD.continuousOn_internalMetric_pair (clearanceEq_nonneg hD) hVo
    have hcomp : ContinuousOn (fun p : I × I => internalMetric D V (γ p.1) (γ p.2)) univ :=
      hc2.comp ((γ.continuous.comp continuous_fst).prodMk (γ.continuous.comp continuous_snd)).continuousOn
        fun p _ => ⟨hγV p.1, hγV p.2⟩
    exact continuousOn_univ.1
      (ENNReal.continuousOn_toReal.comp hcomp fun p _ => hfin _ (hγV p.1) _ (hγV p.2))
  obtain ⟨δ, hδ, hδG⟩ := Metric.uniformContinuous_iff.1
    (CompactSpace.uniformContinuous_of_continuous hG) (c / 4) (by positivity)
  have hGlt : ∀ s t : I, dist s t < δ → internalCost D V (γ s) (γ t) < c / 4 := by
    intro s t hst
    have hss : internalCost D V (γ s) (γ s) = 0 := by
      unfold internalCost
      rw [internalMetric_self_zero hD hVo (hγV s), ENNReal.toReal_zero]
    have h := hδG (show dist ((s, s) : I × I) (s, t) < δ from by
      rw [Prod.dist_eq]
      exact max_lt (by simpa using hδ) hst)
    dsimp only at h
    rw [Real.dist_eq, hss, zero_sub, abs_neg, abs_of_nonneg (internalCost_nonneg D V _ _)] at h
    exact h
  -- the grid
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  let g : ℕ → I := fun i =>
    ⟨min ((i : ℝ) / ((n : ℝ) + 1)) 1, le_min (by positivity) zero_le_one, min_le_right _ _⟩
  have hgval : ∀ i ≤ n + 1, ((g i : I) : ℝ) = (i : ℝ) / ((n : ℝ) + 1) := by
    intro i hi
    have hi' : (i : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hi
    exact min_eq_left ((div_le_one hn1).2 hi')
  have hgmono : Monotone g := by
    intro i j hij
    have hdiv : (i : ℝ) / ((n : ℝ) + 1) ≤ (j : ℝ) / ((n : ℝ) + 1) :=
      div_le_div_of_nonneg_right (by exact_mod_cast hij) hn1.le
    exact Subtype.coe_le_coe.1 (min_le_min_right _ hdiv)
  have hg0 : g 0 = 0 := Subtype.ext
    (show min (((0 : ℕ) : ℝ) / ((n : ℝ) + 1)) 1 = ((0 : I) : ℝ) by
      rw [Nat.cast_zero, zero_div, min_eq_left zero_le_one]
      try rfl)
  have hgN : g (n + 1) = 1 := by
    have h1 : ((n + 1 : ℕ) : ℝ) / ((n : ℝ) + 1) = 1 := by
      push_cast
      exact div_self hn1.ne'
    exact Subtype.ext (show min (((n + 1 : ℕ) : ℝ) / ((n : ℝ) + 1)) 1 = ((1 : I) : ℝ) by
      rw [h1, min_self]
      try rfl)
  have hgdist : ∀ i < n + 1, dist (g i) (g (i + 1)) < δ := by
    intro i hi
    have hi1 : i ≤ n + 1 := by omega
    have hi2 : i + 1 ≤ n + 1 := by omega
    rw [Subtype.dist_eq, Real.dist_eq, hgval i hi1, hgval (i + 1) hi2]
    have hsub : (i : ℝ) / ((n : ℝ) + 1) - ((i + 1 : ℕ) : ℝ) / ((n : ℝ) + 1) = -(1 / ((n : ℝ) + 1)) := by
      push_cast
      field_simp
      ring
    rw [hsub, abs_neg, abs_of_pos (by positivity)]
    exact hn
  -- the vertex tolerance
  set ε : ℝ := min (c / 8) (η / (2 * ((n : ℝ) + 1))) with hε_def
  have hε : 0 < ε := lt_min (by positivity) (by positivity)
  have hεc : ε ≤ c / 8 := min_le_left _ _
  have hεη : 2 * ((n : ℝ) + 1) * ε ≤ η := by
    have h1 : ε ≤ η / (2 * ((n : ℝ) + 1)) := min_le_right _ _
    have h2 := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * ((n : ℝ) + 1))).1 h1
    linarith [mul_comm ε (2 * ((n : ℝ) + 1))]
  have hvert : ∀ i : ℕ, ∃ s ∈ S, internalMetric D V s (γ (g i)) < ENNReal.ofReal ε := by
    intro i
    have h0 : internalMetric D V (γ (g i)) (γ (g i)) < ENNReal.ofReal ε := by
      rw [internalMetric_self_zero hD hVo (hγV _)]
      exact ENNReal.ofReal_pos.2 hε
    have hev : ∀ᶠ s in 𝓝 (γ (g i)), internalMetric D V s (γ (g i)) < ENNReal.ofReal ε :=
      (continuousAt_internalMetric_left hD hVo (hγV _)).eventually_lt continuousAt_const h0
    obtain ⟨s, hs, hsS⟩ := (mem_closure_iff_nhds.mp (hS (hγ _))) _ hev
    exact ⟨s, hsS, hs⟩
  choose w hwS hwε using hvert
  -- the chain: interior vertices `w 1, …, w n`, endpoints `x`, `y`
  let k : Σ m : ℕ, Fin m → S := ⟨n, fun j => ⟨w (j.1 + 1), hwS (j.1 + 1)⟩⟩
  refine ⟨k, ?_⟩
  have hk1 : k.1 = n := rfl
  have hvtx_zero : denseChainVertex x y k 0 = x := denseChainVertex_start x y k
  have hvtx_end : denseChainVertex x y k (n + 1) = y := denseChainVertex_end x y k
  have hvtx_mid : ∀ i, 1 ≤ i → i ≤ n → denseChainVertex x y k i = w i := by
    intro i h1 h2
    unfold denseChainVertex
    split_ifs
    · omega
    · show w (i - 1 + 1) = w i
      congr 1
      omega
  have hvtx_V : ∀ i, denseChainVertex x y k i ∈ V := fun i =>
    denseChainVertex_mem hSV (hOV hx) (hOV hy) k (i := i)
  have hclose : ∀ i ≤ n + 1, internalMetric D V (denseChainVertex x y k i) (γ (g i)) < ENNReal.ofReal ε := by
    intro i hi
    by_cases h0 : i = 0
    · subst h0
      rw [hvtx_zero, hg0, γ.source, internalMetric_self_zero hD hVo (hOV hx)]
      exact ENNReal.ofReal_pos.2 hε
    by_cases hN : i = n + 1
    · subst hN
      rw [hvtx_end, hgN, γ.target, internalMetric_self_zero hD hVo (hOV hy)]
      exact ENNReal.ofReal_pos.2 hε
    rw [hvtx_mid i (by omega) (by omega)]
    exact hwε i
  have hRclose : ∀ i ≤ n + 1, internalCost D V (denseChainVertex x y k i) (γ (g i)) < ε :=
    fun i hi => ENNReal.toReal_lt_of_lt_ofReal (hclose i hi)
  -- edge estimates
  have hedgeR : ∀ i < n + 1, internalCost D V (denseChainVertex x y k i) (denseChainVertex x y k (i + 1)) ≤
      internalCost D V (γ (g i)) (γ (g (i + 1))) + 2 * ε := by
    intro i hi
    have hpa := hRclose i (by omega)
    have hqb : internalCost D V (γ (g (i + 1))) (denseChainVertex x y k (i + 1)) < ε := by
      rw [internalCost_symm hD]
      exact hRclose (i + 1) (by omega)
    have t1 := internalCost_triangle hD hfin (hvtx_V i) (hγV (g i)) (hγV (g (i + 1)))
    have t2 := internalCost_triangle hD hfin (hvtx_V i) (hγV (g (i + 1))) (hvtx_V (i + 1))
    linarith
    -- clearance of the edge endpoints from the clearance set
  have hedgeC : ∀ i < n + 1, ∀ q ∈ Q, c - ε ≤ internalCost D V (denseChainVertex x y k i) q := by
    intro i hi q hq
    have hqV : q ∈ V := (hQV hq).1
    have hqO : q ∉ O := (hQV hq).2
    have h1 : c ≤ internalCost D V (γ (g i)) q :=
      (hcle (g i) q hqO).trans (dist_le_internalCost hD (hfin (γ (g i)) (hγV (g i)) q hqV))
    have h2 := internalCost_triangle hD hfin (hγV (g i)) (hvtx_V i) hqV
    have h3 : internalCost D V (γ (g i)) (denseChainVertex x y k i) < ε := by
      rw [internalCost_symm hD]
      exact hRclose i (by omega)
    linarith
  -- the edges are permitted with rational gaps
  have hcond : ∀ i < k.1 + 1, ∃ r : ℚ, 0 < r ∧
      internalCost D V (denseChainVertex x y k i) (denseChainVertex x y k (i + 1)) < (r : ℝ) ∧
      ∀ q ∈ Q, (r : ℝ) ≤ internalCost D V (denseChainVertex x y k i) q := by
    intro i hi
    have hi' : i < n + 1 := hi
    have hlt : internalCost D V (denseChainVertex x y k i) (denseChainVertex x y k (i + 1)) < c - ε := by
      have h1 := hedgeR i hi'
      have h2 := hGlt (g i) (g (i + 1)) (hgdist i hi')
      linarith
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn hlt
    refine ⟨r, Rat.cast_pos.1 (lt_of_le_of_lt (internalCost_nonneg D V _ _) hr1), hr1, fun q hq => ?_⟩
    exact hr2.le.trans (hedgeC i hi' q hq)
  have hcost : localClearanceCost Q (internalCost D V) x y k =
      ∑ i ∈ Finset.range (n + 1), ENNReal.ofReal (internalCost D V (denseChainVertex x y k i)
        (denseChainVertex x y k (i + 1))) := by
    unfold localClearanceCost
    split_ifs
    rw [hk1]
  have hsumle : ∑ i ∈ Finset.range (n + 1), ENNReal.ofReal (internalCost D V (denseChainVertex x y k i)
      (denseChainVertex x y k (i + 1))) ≤
      ∑ i ∈ Finset.range (n + 1), (internalMetric D V (γ (g i)) (γ (g (i + 1))) + ENNReal.ofReal (2 * ε)) := by
    apply Finset.sum_le_sum
    intro i hi
    have hi' : i < n + 1 := Finset.mem_range.1 hi
    calc ENNReal.ofReal (internalCost D V (denseChainVertex x y k i) (denseChainVertex x y k (i + 1)))
        ≤ ENNReal.ofReal (internalCost D V (γ (g i)) (γ (g (i + 1))) + 2 * ε) :=
          ENNReal.ofReal_le_ofReal (hedgeR i hi')
      _ = ENNReal.ofReal (internalCost D V (γ (g i)) (γ (g (i + 1)))) + ENNReal.ofReal (2 * ε) :=
          ENNReal.ofReal_add (internalCost_nonneg D V _ _) (by positivity)
      _ = internalMetric D V (γ (g i)) (γ (g (i + 1))) + ENNReal.ofReal (2 * ε) := by
          unfold internalCost
          rw [ENNReal.ofReal_toReal (hfin _ (hγV (g i)) _ (hγV (g (i + 1))))]
  have hsumlen : ∑ i ∈ Finset.range (n + 1), internalMetric D V (γ (g i)) (γ (g (i + 1))) ≤
      pathLength D γ := by
    have hmono : Monotone fun i => ((g i : I) : ℝ) := fun i j hij => Subtype.coe_le_coe.2 (hgmono hij)
    calc ∑ i ∈ Finset.range (n + 1), internalMetric D V (γ (g i)) (γ (g (i + 1)))
        ≤ ∑ i ∈ Finset.range (n + 1), curveLength D γ.extend ((g i : I) : ℝ) ((g (i + 1) : I) : ℝ) :=
          Finset.sum_le_sum fun i _ => internalMetric_le_curveLength_arc γ hγV (hgmono (Nat.le_succ i))
      _ ≤ curveLength D γ.extend ((g 0 : I) : ℝ) ((g (n + 1) : I) : ℝ) :=
          sum_curveLength_le D γ.extend hmono (n + 1)
      _ = pathLength D γ := by
          rw [hg0, hgN]
          rfl
  have hconstle : ∑ i ∈ Finset.range (n + 1), ENNReal.ofReal (2 * ε) ≤ ENNReal.ofReal η := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (by
      push_cast
      linarith [hεη, show ((n : ℝ) + 1) * (2 * ε) = 2 * ((n : ℝ) + 1) * ε by ring])
  calc localClearanceCost Q (internalCost D V) x y k
      = ∑ i ∈ Finset.range (n + 1), ENNReal.ofReal (internalCost D V (denseChainVertex x y k i)
          (denseChainVertex x y k (i + 1))) := hcost
    _ ≤ ∑ i ∈ Finset.range (n + 1), (internalMetric D V (γ (g i)) (γ (g (i + 1))) +
          ENNReal.ofReal (2 * ε)) := hsumle
    _ = ∑ i ∈ Finset.range (n + 1), internalMetric D V (γ (g i)) (γ (g (i + 1))) +
          ∑ i ∈ Finset.range (n + 1), ENNReal.ofReal (2 * ε) := Finset.sum_add_distrib
    _ ≤ pathLength D γ + ENNReal.ofReal η := add_le_add hsumlen hconstle

/-- Upper bound for the localized infimum (route 4.3): every path in `O` gives a localized chain of cost at most its
length plus any `η > 0`. -/
theorem localClearanceInf_le_internalMetric (hD : IsEuclideanLengthMetric D) {V O S Q : Set ℂ} (hO : IsOpen O)
    (hVo : IsOpen V) (hOV : O ⊆ V) (hSV : S ⊆ V) (hS : O ⊆ closure S) (hQV : Q ⊆ V \ O)
    (hfin : ∀ v ∈ V, ∀ w ∈ V, internalMetric D V v w ≠ ⊤) {x y : ℂ} (hx : x ∈ O) (hy : y ∈ O) :
    localClearanceInf S Q (internalCost D V) x y ≤ internalMetric D O x y := by
  refine ENNReal.le_of_forall_pos_le_add fun η hη hd => ?_
  set e : ℝ := (η : ℝ) / 2 with he_def
  have he : 0 < e := half_pos (NNReal.coe_pos.2 hη)
  have hlt : internalMetric D O x y < internalMetric D O x y + ENNReal.ofReal e :=
    ENNReal.lt_add_right hd.ne (ENNReal.ofReal_pos.2 he).ne'
  obtain ⟨γ, hγ⟩ := iInf_lt_iff.mp hlt
  obtain ⟨hγO, hγc⟩ := iInf_lt_iff.mp hγ
  obtain ⟨k, hk⟩ := exists_localClearanceChain hD hO hVo hOV hSV hS hQV hfin hx hy γ hγO he
  have hk' : localClearanceInf S Q (internalCost D V) x y ≤ localClearanceCost Q (internalCost D V) x y k :=
    iInf_le _ k
  have h2e : ENNReal.ofReal e + ENNReal.ofReal e = (η : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_add he.le he.le, show e + e = (η : ℝ) from by rw [he_def]; ring,
      ENNReal.ofReal_coe_nnreal]
  calc localClearanceInf S Q (internalCost D V) x y ≤ localClearanceCost Q (internalCost D V) x y k := hk'
    _ ≤ pathLength D γ + ENNReal.ofReal e := hk
    _ ≤ (internalMetric D O x y + ENNReal.ofReal e) + ENNReal.ofReal e := add_le_add hγc.le le_rfl
    _ = internalMetric D O x y + (ENNReal.ofReal e + ENNReal.ofReal e) := add_assoc _ _ _
    _ = internalMetric D O x y + η := by rw [h2e]

/-- **L-EQ** (route 4.3, identity (14) before the punctured limit): for a Euclidean length metric `D`, an open
`O ⊆ V`, a vertex set `S ⊆ V` dense in `O`, and a clearance set `Q ⊆ V \ O` dense in `V \ O`, the localized chain
infimum with the `V`-internal cost equals the internal distance of `O`, given that the `V`-distances are finite. -/
theorem localClearanceInf_eq_internalMetric (hD : IsEuclideanLengthMetric D) {V O S Q : Set ℂ} (hO : IsOpen O)
    (hVo : IsOpen V) (hOV : O ⊆ V) (hSV : S ⊆ V) (hS : O ⊆ closure S) (hQV : Q ⊆ V \ O)
    (hQd : V \ O ⊆ closure Q) (hfin : ∀ v ∈ V, ∀ w ∈ V, internalMetric D V v w ≠ ⊤) {x y : ℂ} (hx : x ∈ O)
    (hy : y ∈ O) :
    localClearanceInf S Q (internalCost D V) x y = internalMetric D O x y :=
  le_antisymm (localClearanceInf_le_internalMetric hD hO hVo hOV hSV hS hQV hfin hx hy)
    (internalMetric_le_localClearanceInf hD hVo hO hOV hSV hQd hfin hx hy)

/-- **L-EQ** with the finiteness hypothesis discharged by connectedness of `V` (the punctured ball `B_R \ {0}` is
connected, so its internal distances are finite: `internalMetric_ne_top_of_isConnected`). -/
theorem localClearanceInf_eq_internalMetric_of_isConnected (hD : IsEuclideanLengthMetric D) {V O S Q : Set ℂ}
    (hO : IsOpen O) (hVo : IsOpen V) (hconn : IsConnected V) (hOV : O ⊆ V) (hSV : S ⊆ V) (hS : O ⊆ closure S)
    (hQV : Q ⊆ V \ O) (hQd : V \ O ⊆ closure Q) {x y : ℂ} (hx : x ∈ O) (hy : y ∈ O) :
    localClearanceInf S Q (internalCost D V) x y = internalMetric D O x y :=
  localClearanceInf_eq_internalMetric hD hO hVo hOV hSV hS hQV hQd
    (fun _ hv _ hw => internalMetric_ne_top_of_isConnected hD hVo hconn hv hw) hx hy

end HarmonicBalls.S11m

#print axioms HarmonicBalls.S11m.localClearanceInf_eq_internalMetric
#print axioms HarmonicBalls.S11m.localClearanceInf_eq_internalMetric_of_isConnected

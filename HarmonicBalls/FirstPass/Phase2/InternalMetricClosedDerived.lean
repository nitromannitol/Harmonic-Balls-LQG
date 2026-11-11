import HarmonicBalls.FirstPass.Frozen.S11g
import HarmonicBalls.Steps.Sec11.MetricArcLength
import HarmonicBalls.Steps.Sec11.CurveLengthReparam
import HarmonicBalls.FirstPass.Phase2.WeylInternalClosedDerived

/-! # The closed-set internal metric is derived (Phase 2, task fp-phase2-internal-metric-closed-derive)

`InternalMetricClosedEqIInfThickeningFrozen` (`FirstPass/Frozen/S11g.lean`) is derived with no new hypothesis.
The frozen Prop itself is not edited. Written route: `notes/fp-gaps/CHATGPT-K1-proof-z4-F4.md` section 1 (1.1-1.4),
checked step by step. Lean route:

* `internalMetric_anti_set`, `iSup_thickening_le_internalMetric`: domain monotonicity (route (1.11)).
* `arcLength_param`: arc-length parametrization of a path inside a set, with range (route 1.2; Lean lemmas
  `IsEuclideanLengthMetric.exists_lengthParametrized_with_tracking`, `...cumulative_curveLength_properties`).
* `exists_clusterPt_family`: a cluster point in the product topology replaces the diagonal extraction of route 1.3.
  Neighbourhoods are `D`-balls, which are Euclidean-open because `D` induces the Euclidean topology.
* `internalMetric_le_iSup_thickening`: route (1.10) for compact sets; the limit path has length at most the supremum.
* `internalMetric_closed_eq_iInf_sup`: route (1.13)-(1.14), exhaustion `C ∩ closedBall 0 (n+1)`.
-/

namespace HarmonicBalls

open Set Filter Topology
open scoped ENNReal NNReal

/-- Domain monotonicity of the internal metric: a larger set has more admissible paths. -/
theorem internalMetric_anti_set {D : ℂ → ℂ → ℝ} {U V : Set ℂ} (h : U ⊆ V) (z w : ℂ) :
    internalMetric D V z w ≤ internalMetric D U z w := by
  unfold internalMetric
  exact le_iInf₂ fun P hP => iInf₂_le P (fun t => h (hP t))

/-- Route 1.3, (1.11): a thickening of `A` contains `A`, so its internal metric is at most that of `A`. -/
theorem iSup_thickening_le_internalMetric {D : ℂ → ℂ → ℝ} (A : Set ℂ) (x y : ℂ) :
    (⨆ k : ℕ, internalMetric D (Metric.thickening (((k : ℝ) + 1)⁻¹) A) x y) ≤ internalMetric D A x y :=
  iSup_le fun k => internalMetric_anti_set (Metric.self_subset_thickening (by positivity) A) x y

theorem euclid_D_nonneg {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) (z w : ℂ) : 0 ≤ D z w := by
  have h := hD.triangle z w z
  rw [hD.self_eq_zero, hD.symm w z] at h
  linarith

/-- The `D`-ball `{z | D z w < ε}` is Euclidean-open (`D` induces the Euclidean topology). -/
theorem isOpen_D_lt {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) (w : ℂ) (ε : ℝ) :
    IsOpen {z : ℂ | D z w < ε} := by
  rw [hD.isOpen_iff]
  intro z hz
  refine ⟨ε - D z w, sub_pos.mpr hz, fun z' hz' => ?_⟩
  have h1 := hD.triangle z' z w
  rw [hD.symm z' z] at h1
  have h2 : D z z' < ε - D z w := hz'
  show D z' w < ε
  linarith

/-- `D`-small implies Euclidean-small, at a fixed point. -/
theorem exists_D_small_dist {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) (z : ℂ) {r : ℝ} (hr : 0 < r) :
    ∃ η > 0, ∀ w : ℂ, D z w < η → dist w z < r := by
  obtain ⟨η, hη, h⟩ :=
    (hD.isOpen_iff (Metric.ball z r)).mp Metric.isOpen_ball z (Metric.mem_ball_self hr)
  exact ⟨η, hη, fun w hw => Metric.mem_ball.mp (h w hw)⟩

theorem eq_of_forall_D_lt {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {z w : ℂ}
    (h : ∀ ε > 0, D z w < ε) : z = w := by
  have h0 : D z w = 0 :=
    le_antisymm (le_of_forall_pos_lt_add fun ε hε => by simpa using h ε hε) (euclid_D_nonneg hD z w)
  exact hD.eq_of_eq_zero z w h0

theorem inv_succ_lt_half {e : ℝ} (he : 0 < e) {K k : ℕ} (hK : 2 / e < K) (hkK : K ≤ k) :
    ((k : ℝ) + 1)⁻¹ < e / 2 := by
  rw [div_lt_iff₀ he] at hK
  have hk : (K : ℝ) ≤ k := by exact_mod_cast hkK
  rw [inv_eq_one_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

theorem dist_le_of_lengthParam_aux {D : ℂ → ℂ → ℝ} {q : ℝ → ℂ} {ℓ : ℝ}
    (hq : IsLengthParametrized D q ℓ) {s t : ℝ} (hs : s ∈ Icc 0 ℓ) (ht : t ∈ Icc 0 ℓ) (hst : s ≤ t) :
    D (q t) (q s) ≤ t - s := by
  have hc : curveLength D q s t = ENNReal.ofReal (t - s) := hq.2.2 s t hs.1 hst ht.2
  have hmono : Monotone (fun i : ℕ => if i = 0 then s else t) := by
    intro i j hij
    dsimp only
    split_ifs <;> first | exact le_refl _ | exact hst | (exfalso; omega)
  have hmem : ∀ i : ℕ, (fun i : ℕ => if i = 0 then s else t) i ∈ Icc s t := by
    intro i
    dsimp only
    split_ifs
    · exact ⟨le_refl _, hst⟩
    · exact ⟨hst, le_refl _⟩
  have hle : ENNReal.ofReal (D (q t) (q s)) ≤ curveLength D q s t := by
    unfold curveLength
    refine le_iSup_of_le ⟨1, ⟨fun i : ℕ => if i = 0 then s else t, hmono, hmem⟩⟩ ?_
    simp
  rw [hc] at hle
  exact (ENNReal.ofReal_le_ofReal_iff (sub_nonneg.mpr hst)).mp hle

/-- Lipschitz bound of an arc-length parametrization: `D (q s) (q t) ≤ |s - t|`. -/
theorem dist_le_of_lengthParam {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {q : ℝ → ℂ} {ℓ : ℝ}
    (hq : IsLengthParametrized D q ℓ) {s t : ℝ} (hs : s ∈ Icc 0 ℓ) (ht : t ∈ Icc 0 ℓ) :
    D (q s) (q t) ≤ |s - t| := by
  rcases le_total s t with hst | hst
  · rw [hD.symm, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hst)]
    exact dist_le_of_lengthParam_aux hq hs ht hst
  · rw [abs_of_nonneg (sub_nonneg.mpr hst)]
    exact dist_le_of_lengthParam_aux hq ht hs hst

/-- Route 1.2: a path inside `U` of finite `D`-length has an arc-length parametrization on `[0, ℓ]`,
`ℓ = len(P; D)`, with the same endpoints and image inside `U`. -/
theorem arcLength_param {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {U : Set ℂ} {x y : ℂ}
    (P : Path x y) (hU : ∀ t, P t ∈ U) (hfin : pathLength D P ≠ ⊤) :
    ∃ q : ℝ → ℂ, IsLengthParametrized D q (pathLength D P).toReal ∧ q 0 = x ∧
      q (pathLength D P).toReal = y ∧ ∀ s ∈ Icc 0 (pathLength D P).toReal, q s ∈ U := by
  unfold pathLength at hfin ⊢
  have hcont : ContinuousOn P.extend (Icc 0 1) := P.continuous_extend.continuousOn
  have hlt : curveLength D P.extend 0 1 < ⊤ := lt_top_iff_ne_top.mpr hfin
  obtain ⟨q, hq, hq0, hqT, htrack⟩ := hD.exists_lengthParametrized_with_tracking zero_le_one hcont hlt
  obtain ⟨_, _, _, himg⟩ := hD.cumulative_curveLength_properties zero_le_one hcont hlt
  refine ⟨q, hq, ?_, ?_, ?_⟩
  · rw [hq0]
    simp
  · rw [hqT]
    simp
  · intro s hs
    have hs' : s ∈ (fun t => (curveLength D P.extend 0 t).toReal) '' Icc 0 1 := by
      rw [himg]
      exact hs
    obtain ⟨t, ht, rfl⟩ := hs'
    show q (curveLength D P.extend 0 t).toReal ∈ U
    rw [htrack t ht]
    have hI : t ∈ unitInterval := ⟨ht.1, ht.2⟩
    have h2 : P.extend t = P ⟨t, hI⟩ := P.extend_extends' ⟨t, ht⟩
    rw [h2]
    exact hU ⟨t, hI⟩

/-- Cluster-point extraction in the product topology: a family of maps `ι → ℂ` with values in a compact set
has a cluster point `g`, and every finite set of coordinates is `ε`-approximated by the family at arbitrarily
large indices. This replaces the diagonal extraction of route 1.3. -/
theorem exists_clusterPt_family {ι : Type*} {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {E : Set ℂ}
    (hE : IsCompact E) (F : ℕ → ι → ℂ) (hF : ∀ k t, F k t ∈ E) :
    ∃ g : ι → ℂ, (∀ t, g t ∈ E) ∧
      ∀ (S : Finset ι) {ε : ℝ}, 0 < ε → ∀ K₀ : ℕ, ∃ k, K₀ ≤ k ∧ ∀ t ∈ S, D (F k t) (g t) < ε := by
  have hpi : IsCompact (Set.pi univ fun _ : ι => E) := isCompact_univ_pi fun _ => hE
  have hle : Filter.map F atTop ≤ 𝓟 (Set.pi univ fun _ : ι => E) := by
    rw [le_principal_iff]
    exact mem_map.mpr (univ_mem' fun k => fun t _ => hF k t)
  obtain ⟨g, hgmem, hcl⟩ := hpi.exists_clusterPt hle
  refine ⟨g, fun t => mem_univ_pi.mp hgmem t, ?_⟩
  intro S ε hε K₀
  let V : Set (ι → ℂ) := ⋂ t ∈ S, (fun h : ι → ℂ => h t) ⁻¹' {z : ℂ | D z (g t) < ε}
  have hVopen : IsOpen V :=
    isOpen_biInter_finset fun t _ => (isOpen_D_lt hD (g t) ε).preimage (continuous_apply t)
  have hgV : g ∈ V := by
    simp only [V, mem_iInter, mem_preimage, Set.mem_ofPred_eq]
    intro t _
    rw [hD.self_eq_zero]
    exact hε
  have hfreq := clusterPt_iff_frequently.mp hcl V (hVopen.mem_nhds hgV)
  rw [Filter.frequently_map] at hfreq
  obtain ⟨b, hb, hbV⟩ := Filter.frequently_atTop.mp hfreq K₀
  refine ⟨b, hb, ?_⟩
  intro t ht
  have h3 := hbV
  simp only [V, mem_iInter, mem_preimage, Set.mem_ofPred_eq] at h3
  exact h3 t ht

/-- Route 1.3, (1.10), for a compact set `A`: the internal metric of `A` is the supremum of the internal metrics of
the thickenings `thickening ((k+1)⁻¹) A`. A near-minimizing path in each thickening is arc-length parametrized,
the parametrizations are `D`-Lipschitz with a common constant, a cluster point `g` of the family is a `D`-Lipschitz
path in `A` with the same endpoints, and its length is at most the supremum. -/
theorem internalMetric_le_iSup_thickening {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {A : Set ℂ}
    (hA : IsCompact A) (x y : ℂ) :
    internalMetric D A x y ≤ ⨆ k : ℕ, internalMetric D (Metric.thickening (((k : ℝ) + 1)⁻¹) A) x y := by
  set a : ℝ≥0∞ := ⨆ k : ℕ, internalMetric D (Metric.thickening (((k : ℝ) + 1)⁻¹) A) x y with ha
  by_cases htop : a = ⊤
  · rw [htop]
    exact le_top
  -- Step 1: near-minimizing paths in the thickenings.
  have hchoose : ∀ k : ℕ, ∃ P : Path x y, (∀ t, P t ∈ Metric.thickening (((k : ℝ) + 1)⁻¹) A) ∧
      pathLength D P < a + ENNReal.ofReal (((k : ℝ) + 1)⁻¹) := by
    intro k
    have hpos : (0 : ℝ) < ((k : ℝ) + 1)⁻¹ := by positivity
    have hlt : internalMetric D (Metric.thickening (((k : ℝ) + 1)⁻¹) A) x y <
        a + ENNReal.ofReal (((k : ℝ) + 1)⁻¹) :=
      lt_of_le_of_lt
        (le_iSup (fun k : ℕ => internalMetric D (Metric.thickening (((k : ℝ) + 1)⁻¹) A) x y) k)
        (ENNReal.lt_add_right htop (ENNReal.ofReal_pos.mpr hpos).ne')
    unfold internalMetric at hlt
    obtain ⟨P, hP⟩ := iInf_lt_iff.mp hlt
    obtain ⟨hPU, hPlt⟩ := iInf_lt_iff.mp hP
    exact ⟨P, hPU, hPlt⟩
  choose P hPU hPlt using hchoose
  -- Step 2: lengths.
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℕ → ℝ, ∀ k, ℓ k = (pathLength D (P k)).toReal := ⟨_, fun k => rfl⟩
  have hℓ0 : ∀ k, 0 ≤ ℓ k := fun k => by
    rw [hℓ k]
    exact ENNReal.toReal_nonneg
  have hℓle : ∀ k : ℕ, ℓ k ≤ a.toReal + 1 := by
    intro k
    have h1 : pathLength D (P k) ≤ a + ENNReal.ofReal (((k : ℝ) + 1)⁻¹) := (hPlt k).le
    have h2 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨htop, ENNReal.ofReal_ne_top⟩) h1
    rw [ENNReal.toReal_add htop ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal (by positivity)] at h2
    have h3 : ((k : ℝ) + 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) k])
    rw [hℓ k]
    linarith
  -- Step 3: arc-length parametrizations inside the thickenings.
  have hq : ∀ k, ∃ q : ℝ → ℂ, IsLengthParametrized D q (ℓ k) ∧ q 0 = x ∧ q (ℓ k) = y ∧
      ∀ s ∈ Icc 0 (ℓ k), q s ∈ Metric.thickening (((k : ℝ) + 1)⁻¹) A := by
    intro k
    obtain ⟨q, h1, h2, h3, h4⟩ := arcLength_param hD (P k) (hPU k) (ne_top_of_lt (hPlt k))
    exact ⟨q, by rw [hℓ k]; exact h1, h2, by rw [hℓ k]; exact h3, by rw [hℓ k]; exact h4⟩
  choose q hqP hq0 hqℓ hqU using hq
  obtain ⟨Φ, hΦdef⟩ : ∃ Φ : ℕ → unitInterval → ℂ, ∀ k t, Φ k t = q k (ℓ k * (t : ℝ)) :=
    ⟨fun k t => q k (ℓ k * (t : ℝ)), fun k t => rfl⟩
  have hΦmem : ∀ (k : ℕ) (t : unitInterval), Φ k t ∈ Metric.thickening (((k : ℝ) + 1)⁻¹) A := by
    intro k t
    rw [hΦdef]
    exact hqU k _ ⟨mul_nonneg (hℓ0 k) (unitInterval.nonneg t), mul_le_of_le_one_right (hℓ0 k) (unitInterval.le_one t)⟩
  have hΦlip : ∀ (k : ℕ) (s t : unitInterval), D (Φ k s) (Φ k t) ≤ (a.toReal + 1) * |(s : ℝ) - t| := by
    intro k s t
    rw [hΦdef, hΦdef]
    have hs : ℓ k * (s : ℝ) ∈ Icc 0 (ℓ k) :=
      ⟨mul_nonneg (hℓ0 k) (unitInterval.nonneg s), mul_le_of_le_one_right (hℓ0 k) (unitInterval.le_one s)⟩
    have ht : ℓ k * (t : ℝ) ∈ Icc 0 (ℓ k) :=
      ⟨mul_nonneg (hℓ0 k) (unitInterval.nonneg t), mul_le_of_le_one_right (hℓ0 k) (unitInterval.le_one t)⟩
    have h1 := dist_le_of_lengthParam hD (hqP k) hs ht
    have h2 : |ℓ k * (s : ℝ) - ℓ k * (t : ℝ)| = ℓ k * |(s : ℝ) - t| := by
      rw [← mul_sub, abs_mul, abs_of_nonneg (hℓ0 k)]
    have h3 : ℓ k * |(s : ℝ) - t| ≤ (a.toReal + 1) * |(s : ℝ) - t| :=
      mul_le_mul_of_nonneg_right (hℓle k) (abs_nonneg _)
    rw [h2] at h1
    exact h1.trans h3
  have hΦ0 : ∀ k, Φ k 0 = x := by
    intro k
    rw [hΦdef]
    simp [hq0 k]
  have hΦ1 : ∀ k, Φ k 1 = y := by
    intro k
    rw [hΦdef]
    simp [hqℓ k]
  -- Step 4: cluster point of the family.
  obtain ⟨R, hR⟩ := hA.isBounded.subset_closedBall 0
  have hΦE : ∀ (k : ℕ) (t : unitInterval), Φ k t ∈ Metric.closedBall (0 : ℂ) (R + 1) := by
    intro k t
    obtain ⟨z, hzA, hz⟩ := Metric.mem_thickening_iff.mp (hΦmem k t)
    have hz0 : dist z 0 ≤ R := Metric.mem_closedBall.mp (hR hzA)
    have hδ : ((k : ℝ) + 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) k])
    rw [Metric.mem_closedBall]
    linarith [dist_triangle (Φ k t) z 0]
  obtain ⟨g, -, hgcl⟩ := exists_clusterPt_family hD (isCompact_closedBall (0 : ℂ) (R + 1)) Φ hΦE
  have hglip : ∀ s t : unitInterval, D (g s) (g t) ≤ (a.toReal + 1) * |(s : ℝ) - t| := by
    intro s t
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    obtain ⟨k, -, hk⟩ := hgcl {s, t} (half_pos hε) 0
    have hs := hk s (by simp)
    have ht := hk t (by simp)
    have h := hΦlip k s t
    linarith [hD.triangle (g s) (Φ k s) (g t), hD.triangle (Φ k s) (Φ k t) (g t),
      hD.symm (g s) (Φ k s)]
  have hgA : ∀ t : unitInterval, g t ∈ A := by
    intro t
    by_contra hgt
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hA.isClosed.isOpen_compl (g t) hgt
    obtain ⟨η, hη, hηd⟩ := exists_D_small_dist hD (g t) (half_pos hr)
    obtain ⟨K₀, hK₀⟩ := exists_nat_gt (2 / r)
    obtain ⟨k, hkK, hk⟩ := hgcl {t} hη K₀
    have hδk : ((k : ℝ) + 1)⁻¹ < r / 2 := inv_succ_lt_half hr hK₀ hkK
    have h1 : dist (Φ k t) (g t) < r / 2 := by
      apply hηd
      rw [hD.symm]
      exact hk t (by simp)
    obtain ⟨z, hzA, hz⟩ := Metric.mem_thickening_iff.mp (hΦmem k t)
    have h2 : z ∈ Metric.ball (g t) r := by
      rw [Metric.mem_ball]
      linarith [dist_triangle z (Φ k t) (g t), dist_comm z (Φ k t)]
    exact hball h2 hzA
  have hg0 : g 0 = x := by
    refine eq_of_forall_D_lt hD fun ε hε => ?_
    obtain ⟨k, -, hk⟩ := hgcl {0} hε 0
    have h := hk 0 (by simp)
    rw [hΦ0 k, hD.symm] at h
    exact h
  have hg1 : g 1 = y := by
    refine eq_of_forall_D_lt hD fun ε hε => ?_
    obtain ⟨k, -, hk⟩ := hgcl {1} hε 0
    have h := hk 1 (by simp)
    rw [hΦ1 k, hD.symm] at h
    exact h
  have hgc : Continuous g := by
    rw [Metric.continuous_iff]
    intro b ε hε
    obtain ⟨η, hη, hηd⟩ := exists_D_small_dist hD (g b) hε
    have hLc : 0 < a.toReal + 1 := by positivity
    refine ⟨η / (a.toReal + 1), div_pos hη hLc, fun s hs => ?_⟩
    have h1 := hglip b s
    rw [Subtype.dist_eq, Real.dist_eq, abs_sub_comm, lt_div_iff₀ hLc] at hs
    apply hηd (g s)
    linarith
  -- Step 5: the limit path `γ` and its length.
  let γ : Path x y :=
    { toFun := g
      continuous_toFun := hgc
      source' := hg0
      target' := hg1 }
  have hext : ∀ (u : ℕ → ℝ) (i : ℕ) (hi : u i ∈ Icc (0:ℝ) 1), γ.extend (u i) = g ⟨u i, hi⟩ :=
    fun u i hi => γ.extend_extends' ⟨u i, hi⟩
  have hpartΦ : ∀ (k N : ℕ) (u : ℕ → ℝ), Monotone u → (∀ i, u i ∈ Icc (0:ℝ) 1) →
      ∑ i ∈ Finset.range N, ENNReal.ofReal (D (q k (ℓ k * u (i + 1))) (q k (ℓ k * u i))) ≤
        ENNReal.ofReal (ℓ k) := by
    intro k N u hu hI
    have hc : curveLength D (q k) 0 (ℓ k) = ENNReal.ofReal (ℓ k - 0) :=
      (hqP k).2.2 0 (ℓ k) le_rfl (hℓ0 k) le_rfl
    have hmono : Monotone (fun i => ℓ k * u i) := fun i j hij =>
      mul_le_mul_of_nonneg_left (hu hij) (hℓ0 k)
    have hmem : ∀ i, (fun i => ℓ k * u i) i ∈ Icc 0 (ℓ k) := fun i =>
      ⟨mul_nonneg (hℓ0 k) (hI i).1, mul_le_of_le_one_right (hℓ0 k) (hI i).2⟩
    calc ∑ i ∈ Finset.range N, ENNReal.ofReal (D (q k (ℓ k * u (i + 1))) (q k (ℓ k * u i)))
        ≤ curveLength D (q k) 0 (ℓ k) := by
          unfold curveLength
          exact le_iSup_of_le ⟨N, ⟨fun i => ℓ k * u i, hmono, hmem⟩⟩ le_rfl
      _ = ENNReal.ofReal (ℓ k) := by rw [hc, sub_zero]
  have hlen : pathLength D γ ≤ a := by
    unfold pathLength
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    refine curveLength_le_of_partition_bound fun N u hu hI => ?_
    have he : (0 : ℝ) < ε := NNReal.coe_pos.mpr hε
    obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = (ε : ℝ) / (4 * ((N : ℝ) + 1)) := ⟨_, rfl⟩
    have hδ : 0 < δ := by
      rw [hδdef]
      positivity
    obtain ⟨K₀, hK₀⟩ := exists_nat_gt (2 / (ε : ℝ))
    obtain ⟨k, hkK, hk⟩ :=
      hgcl ((Finset.range (N + 1)).image fun i => (⟨u i, hI i⟩ : unitInterval)) hδ K₀
    have hkδ : ((k : ℝ) + 1)⁻¹ < (ε : ℝ) / 2 := inv_succ_lt_half he hK₀ hkK
    have hterm : ∀ i ∈ Finset.range N,
        ENNReal.ofReal (D (γ.extend (u (i + 1))) (γ.extend (u i))) ≤
          ENNReal.ofReal (D (q k (ℓ k * u (i + 1))) (q k (ℓ k * u i))) + ENNReal.ofReal (2 * δ) := by
      intro i hi
      have hi' : i < N := Finset.mem_range.mp hi
      have ha1 : (⟨u (i + 1), hI (i + 1)⟩ : unitInterval) ∈
          (Finset.range (N + 1)).image fun i => (⟨u i, hI i⟩ : unitInterval) :=
        Finset.mem_image.mpr ⟨i + 1, Finset.mem_range.mpr (by omega), rfl⟩
      have hb1 : (⟨u i, hI i⟩ : unitInterval) ∈
          (Finset.range (N + 1)).image fun i => (⟨u i, hI i⟩ : unitInterval) :=
        Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by omega), rfl⟩
      have hA1 := hk _ ha1
      have hB1 := hk _ hb1
      have e1 : D (q k (ℓ k * u (i + 1))) (q k (ℓ k * u i)) =
          D (Φ k ⟨u (i + 1), hI (i + 1)⟩) (Φ k ⟨u i, hI i⟩) := by
        rw [hΦdef, hΦdef]
      rw [hext u (i + 1) (hI (i + 1)), hext u i (hI i), e1]
      have hab : D (g ⟨u (i + 1), hI (i + 1)⟩) (g ⟨u i, hI i⟩) ≤
          D (Φ k ⟨u (i + 1), hI (i + 1)⟩) (Φ k ⟨u i, hI i⟩) + 2 * δ := by
        linarith [hD.triangle (g ⟨u (i + 1), hI (i + 1)⟩) (Φ k ⟨u (i + 1), hI (i + 1)⟩) (g ⟨u i, hI i⟩),
          hD.triangle (Φ k ⟨u (i + 1), hI (i + 1)⟩) (Φ k ⟨u i, hI i⟩) (g ⟨u i, hI i⟩),
          hD.symm (g ⟨u (i + 1), hI (i + 1)⟩) (Φ k ⟨u (i + 1), hI (i + 1)⟩)]
      exact (ENNReal.ofReal_le_ofReal hab).trans ENNReal.ofReal_add_le
    have hNle : (N : ℝ) * (2 * δ) ≤ (ε : ℝ) / 2 := by
      have h1 : (N : ℝ) * (2 * δ) = ((ε : ℝ) / 2) * ((N : ℝ) / ((N : ℝ) + 1)) := by
        rw [hδdef]
        field_simp
        ring
      rw [h1]
      apply mul_le_of_le_one_right (by positivity)
      rw [div_le_one (by positivity)]
      linarith
    have hNδ : (N : ℝ≥0∞) * ENNReal.ofReal (2 * δ) ≤ ENNReal.ofReal ((ε : ℝ) / 2) := by
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      exact ENNReal.ofReal_le_ofReal hNle
    have hℓP : ENNReal.ofReal (ℓ k) ≤ a + ENNReal.ofReal ((ε : ℝ) / 2) := by
      rw [hℓ k, ENNReal.ofReal_toReal (ne_top_of_lt (hPlt k))]
      exact (hPlt k).le.trans (add_le_add_right (ENNReal.ofReal_le_ofReal hkδ.le) a)
    calc ∑ i ∈ Finset.range N, ENNReal.ofReal (D (γ.extend (u (i + 1))) (γ.extend (u i)))
        ≤ ∑ i ∈ Finset.range N, (ENNReal.ofReal (D (q k (ℓ k * u (i + 1))) (q k (ℓ k * u i))) +
            ENNReal.ofReal (2 * δ)) := Finset.sum_le_sum hterm
      _ = ∑ i ∈ Finset.range N, ENNReal.ofReal (D (q k (ℓ k * u (i + 1))) (q k (ℓ k * u i))) +
            (N : ℝ≥0∞) * ENNReal.ofReal (2 * δ) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ ENNReal.ofReal (ℓ k) + ENNReal.ofReal ((ε : ℝ) / 2) :=
          add_le_add (hpartΦ k N u hu hI) hNδ
      _ ≤ a + ENNReal.ofReal ((ε : ℝ) / 2) + ENNReal.ofReal ((ε : ℝ) / 2) :=
          add_le_add_left hℓP _
      _ = a + (ε : ℝ≥0∞) := by
          rw [add_assoc, ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_coe_nnreal]
          congr 2
          ring
  have hle : internalMetric D A x y ≤ pathLength D γ := by
    unfold internalMetric
    exact iInf₂_le γ fun t => hgA t
  exact hle.trans hlen

/-- Route 1.4, (1.13)-(1.14): for a closed `C`, the internal metric is the infimum over `n` of the suprema over `k`
of the internal metrics of `thickening ((k+1)⁻¹) (C ∩ closedBall 0 (n+1))`. -/
theorem internalMetric_closed_eq_iInf_sup {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) (C : Set ℂ)
    (hC : IsClosed C) (x y : ℂ) :
    internalMetric D C x y = ⨅ n : ℕ, ⨆ k : ℕ,
      internalMetric D (Metric.thickening (((k : ℝ) + 1)⁻¹) (C ∩ Metric.closedBall 0 ((n : ℝ) + 1))) x y := by
  apply le_antisymm
  · refine le_iInf fun n => ?_
    exact (internalMetric_anti_set Set.inter_subset_left x y).trans
      (internalMetric_le_iSup_thickening hD ((isCompact_closedBall (0 : ℂ) ((n : ℝ) + 1)).inter_left hC) x y)
  · refine le_trans (iInf_mono fun n => iSup_thickening_le_internalMetric _ x y) ?_
    unfold internalMetric
    refine le_iInf₂ fun P hP => ?_
    obtain ⟨R, hR⟩ := (isCompact_range P.continuous).isBounded.subset_closedBall 0
    obtain ⟨N, hN⟩ := exists_nat_ge R
    refine (iInf_le _ N).trans (iInf₂_le P fun t => ⟨hP t, ?_⟩)
    have h1 := Metric.mem_closedBall.mp (hR (Set.mem_range_self t))
    exact Metric.mem_closedBall.mpr (by linarith)

/-- The derived statement: the frozen closed-set exhaustion of the internal metric, with no new hypothesis. -/
theorem internalMetricClosedEqIInfThickening_derived : InternalMetricClosedEqIInfThickeningFrozen := by
  intro D C hC hD x y _ _
  exact internalMetric_closed_eq_iInf_sup hD C hC x y

end HarmonicBalls

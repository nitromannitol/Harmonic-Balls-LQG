import HarmonicBalls.FirstPass.S11r.CurveLengthPieces

/-! # Deleting one point from a length metric (CHATGPT-n3-B1-B2.md, section 4.3)

Local-to-global step for two length metrics `d`, `e` on an open set `U` whose internal metrics agree
on a neighbourhood of each point of `U \ {p}`. Terminology: internal metric `D(z, w; U)` as in
Armitage-Gardiner / Armstrong-Kuusi-Mourrat; `curveLength` as in `Defs/LQGMetric.lean`. -/

namespace HarmonicBalls

open Set Filter Topology
open scoped ENNReal

/-- Piece bound: if `γ([s, t])` lies in an open `V ⊆ U` on which the internal metrics of `d` and `e`
agree, then `d(γ s, γ t)` is at most the `e`-length of `γ` on `[s, t]`. -/
theorem ofReal_dist_le_curveLength_of_piece {d e : ℂ → ℂ → ℝ} {U V : Set ℂ} (hVU : V ⊆ U)
    (hd_len : ∀ x ∈ U, ∀ y ∈ U, ENNReal.ofReal (d x y) = internalMetric d U x y)
    (hagree : ∀ x ∈ V, ∀ y ∈ V, internalMetric d V x y = internalMetric e V x y)
    {γ : ℝ → ℂ} (hγ : Continuous γ) {s t : ℝ} (hst : s ≤ t) (hV : ∀ τ ∈ Icc s t, γ τ ∈ V) :
    ENNReal.ofReal (d (γ s) (γ t)) ≤ curveLength e γ s t := by
  have hs : γ s ∈ V := hV s ⟨le_rfl, hst⟩
  have ht : γ t ∈ V := hV t ⟨hst, le_rfl⟩
  calc ENNReal.ofReal (d (γ s) (γ t)) = internalMetric d U (γ s) (γ t) :=
        hd_len _ (hVU hs) _ (hVU ht)
    _ ≤ internalMetric d V (γ s) (γ t) := internalMetric_anti d hVU _ _
    _ = internalMetric e V (γ s) (γ t) := hagree _ hs _ ht
    _ ≤ curveLength e γ s t := internalMetric_le_curveLength_of_subset e hγ hst hV

/-- Local-to-global step on an interval avoiding `p`: the `d`-distance between the endpoints of
`γ` on `[a, b]` is at most the `e`-length of `γ` on `[a, b]`. Proof: a Lebesgue number for the cover
`γ⁻¹' V τ`, a uniform partition, and a chain of triangle inequalities with superadditivity. -/
theorem ofReal_dist_le_curveLength_of_avoid {d e : ℂ → ℂ → ℝ} {U : Set ℂ} {p : ℂ}
    (hd_tri : ∀ x ∈ U, ∀ y ∈ U, ∀ z ∈ U, d x z ≤ d x y + d y z)
    (hd_len : ∀ x ∈ U, ∀ y ∈ U, ENNReal.ofReal (d x y) = internalMetric d U x y)
    (hloc : ∀ q ∈ U, q ≠ p → ∃ V : Set ℂ, IsOpen V ∧ q ∈ V ∧ V ⊆ U ∧
      ∀ x ∈ V, ∀ y ∈ V, internalMetric d V x y = internalMetric e V x y)
    {γ : ℝ → ℂ} (hγ : Continuous γ) {a b : ℝ} (hab : a ≤ b)
    (havoid : ∀ τ ∈ Icc a b, γ τ ∈ U ∧ γ τ ≠ p) :
    ENNReal.ofReal (d (γ a) (γ b)) ≤ curveLength e γ a b := by
  have hV : ∀ τ : Icc a b, ∃ V : Set ℂ, IsOpen V ∧ γ τ.1 ∈ V ∧ V ⊆ U ∧
      ∀ x ∈ V, ∀ y ∈ V, internalMetric d V x y = internalMetric e V x y :=
    fun τ => hloc (γ τ.1) (havoid τ.1 τ.2).1 (havoid τ.1 τ.2).2
  choose V hVo hVmem hVU hVag using hV
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric
    (c := fun i : Icc a b => γ ⁻¹' V i) isCompact_Icc
    (fun i => (hVo i).preimage hγ)
    (fun τ hτ => mem_iUnion.2 ⟨⟨τ, hτ⟩, hVmem ⟨τ, hτ⟩⟩)
  obtain ⟨N, hN⟩ := exists_nat_gt ((b - a) / δ)
  have hδN : 0 ≤ (b - a) / δ := div_nonneg (sub_nonneg.2 hab) hδ.le
  have hNpos : (0 : ℝ) < N := lt_of_le_of_lt hδN hN
  have hN1 : 0 < N := by exact_mod_cast hNpos
  set h : ℝ := (b - a) / N with hh_def
  have hh0 : 0 ≤ h := div_nonneg (sub_nonneg.2 hab) hNpos.le
  have hhδ : h < δ := by
    rw [hh_def, div_lt_iff₀ hNpos]
    rw [div_lt_iff₀ hδ] at hN
    linarith
  have hNh : (N : ℝ) * h = b - a := by
    rw [hh_def]
    field_simp
  set t : ℕ → ℝ := fun k => a + (k : ℝ) * h with ht_def
  have ht_mem : ∀ k ≤ N, t k ∈ Icc a b := by
    intro k hk
    have hk' : (k : ℝ) ≤ N := by exact_mod_cast hk
    have h1 : (k : ℝ) * h ≤ N * h := mul_le_mul_of_nonneg_right hk' hh0
    have h0 : 0 ≤ (k : ℝ) * h := mul_nonneg (Nat.cast_nonneg k) hh0
    exact ⟨by simp only [ht_def]; linarith, by simp only [ht_def]; linarith⟩
  have ht_ge : ∀ k, a ≤ t k := fun k => by
    have h0 : 0 ≤ (k : ℝ) * h := mul_nonneg (Nat.cast_nonneg k) hh0
    simp only [ht_def]
    linarith
  have ht_succ : ∀ k, t (k + 1) = t k + h := fun k => by
    simp only [ht_def]
    push_cast
    ring
  have ht_le : ∀ k, t k ≤ t (k + 1) := fun k => by
    rw [ht_succ]
    linarith
  have hpiece : ∀ k < N, ENNReal.ofReal (d (γ (t k)) (γ (t (k + 1))))
      ≤ curveLength e γ (t k) (t (k + 1)) := by
    intro k hk
    obtain ⟨i, hi⟩ := hball (t k) (ht_mem k hk.le)
    have hV' : ∀ τ ∈ Icc (t k) (t (k + 1)), γ τ ∈ V i := by
      intro τ hτ
      have hball_mem : τ ∈ Metric.ball (t k) δ := by
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        constructor <;> linarith [hτ.1, hτ.2, ht_succ k]
      exact hi hball_mem
    exact ofReal_dist_le_curveLength_of_piece (hVU i) hd_len (hVag i) hγ (ht_le k) hV'
  have htri : ∀ x ∈ U, ∀ y ∈ U, ∀ z ∈ U,
      ENNReal.ofReal (d x z) ≤ ENNReal.ofReal (d x y) + ENNReal.ofReal (d y z) :=
    fun x hx y hy z hz => (ENNReal.ofReal_le_ofReal (hd_tri x hx y hy z hz)).trans ENNReal.ofReal_add_le
  have hmemU : ∀ k ≤ N, γ (t k) ∈ U := fun k hk => (havoid (t k) (ht_mem k hk)).1
  have hstep : ∀ k, k < N →
      ENNReal.ofReal (d (γ a) (γ (t (k + 1)))) ≤ curveLength e γ a (t (k + 1)) := by
    intro k
    induction k with
    | zero =>
      intro hk
      have h0 : t 0 = a := by simp [ht_def]
      have := hpiece 0 hk
      rw [h0] at this
      exact this
    | succ k ih =>
      intro hk
      have hA : γ a ∈ U := (havoid a ⟨le_rfl, hab⟩).1
      have hsup := curveLength_add_le_general e γ (ht_ge (k + 1)) (ht_le (k + 1))
      calc ENNReal.ofReal (d (γ a) (γ (t (k + 1 + 1))))
          ≤ ENNReal.ofReal (d (γ a) (γ (t (k + 1))))
            + ENNReal.ofReal (d (γ (t (k + 1))) (γ (t (k + 1 + 1)))) :=
            htri _ hA _ (hmemU (k + 1) hk.le) _ (hmemU (k + 1 + 1) hk)
        _ ≤ curveLength e γ a (t (k + 1)) + curveLength e γ (t (k + 1)) (t (k + 1 + 1)) :=
            add_le_add (ih (by omega)) (hpiece (k + 1) hk)
        _ ≤ curveLength e γ a (t (k + 1 + 1)) := hsup
  have hfin := hstep (N - 1) (by omega)
  have hNm : N - 1 + 1 = N := by omega
  have htN : t N = b := by
    simp only [ht_def]
    linarith [hNh]
  rw [hNm, htN] at hfin
  exact hfin

/-- Triangle inequality for the truncated metric `ofReal ∘ d` on `U`. -/
theorem ofReal_dist_le_add_of_tri {d : ℂ → ℂ → ℝ} {U : Set ℂ}
    (hd_tri : ∀ x ∈ U, ∀ y ∈ U, ∀ z ∈ U, d x z ≤ d x y + d y z) {x y z : ℂ}
    (hx : x ∈ U) (hy : y ∈ U) (hz : z ∈ U) :
    ENNReal.ofReal (d x z) ≤ ENNReal.ofReal (d x y) + ENNReal.ofReal (d y z) :=
  (ENNReal.ofReal_le_ofReal (hd_tri x hx y hy z hz)).trans ENNReal.ofReal_add_le

/-- `d(p, p) ≤ 0`, from the triangle inequality through points of `U` near `p` and the continuity of
`d(·, p)` at `p` within `U`. -/
theorem dist_self_le_zero_of_cont {d : ℂ → ℂ → ℝ} {U : Set ℂ} {p : ℂ} (hU : IsOpen U) (hp : p ∈ U)
    (hd_symm : ∀ x y, d x y = d y x)
    (hd_tri : ∀ x ∈ U, ∀ y ∈ U, ∀ z ∈ U, d x z ≤ d x y + d y z)
    (hd_cont : Tendsto (fun z => d z p) (𝓝[U] p) (𝓝 0)) : d p p ≤ 0 := by
  have hnb : (𝓝[U] p).NeBot := by
    rw [hU.nhdsWithin_eq hp]
    infer_instance
  have h2 : Tendsto (fun z => d z p + d z p) (𝓝[U] p) (𝓝 (0 + 0)) := hd_cont.add hd_cont
  rw [add_zero] at h2
  have hle : ∀ᶠ z in 𝓝[U] p, d p p ≤ d z p + d z p :=
    eventually_nhdsWithin_of_forall fun z hz => by
      have h := hd_tri p hp z hz p hp
      rw [hd_symm p z] at h
      exact h
  exact ge_of_tendsto h2 hle

/-- Left endpoint bound: `γ` avoids `p` on `[a, b)` and reaches `p` at `b`; then `d(γ a, p)` is at
most the `e`-length of `γ` on `[a, b]`. -/
theorem ofReal_dist_left_le_curveLength_of_hit {d e : ℂ → ℂ → ℝ} {U : Set ℂ} {p : ℂ}
    (hp : p ∈ U)
    (hd_tri : ∀ x ∈ U, ∀ y ∈ U, ∀ z ∈ U, d x z ≤ d x y + d y z)
    (hd_len : ∀ x ∈ U, ∀ y ∈ U, ENNReal.ofReal (d x y) = internalMetric d U x y)
    (hd_cont : Tendsto (fun z => d z p) (𝓝[U] p) (𝓝 0))
    (hloc : ∀ q ∈ U, q ≠ p → ∃ V : Set ℂ, IsOpen V ∧ q ∈ V ∧ V ⊆ U ∧
      ∀ x ∈ V, ∀ y ∈ V, internalMetric d V x y = internalMetric e V x y)
    {γ : ℝ → ℂ} (hγ : Continuous γ) {a b : ℝ} (hab : a < b)
    (havoid : ∀ τ ∈ Ico a b, γ τ ∈ U ∧ γ τ ≠ p) (hγb : γ b = p) :
    ENNReal.ofReal (d (γ a) p) ≤ curveLength e γ a b := by
  have hA : γ a ∈ U := (havoid a ⟨le_rfl, hab⟩).1
  have hγtend : Tendsto γ (𝓝[<] b) (𝓝[U] p) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have h1 : Tendsto γ (𝓝 b) (𝓝 p) := by
        have := hγ.tendsto b
        rwa [hγb] at this
      exact h1.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsLT hab] with τ hτ
      exact (havoid τ ⟨hτ.1.le, hτ.2⟩).1
  have hd0 : Tendsto (fun τ => ENNReal.ofReal (d (γ τ) p)) (𝓝[<] b) (𝓝 0) := by
    have h : Tendsto (fun τ => ENNReal.ofReal (d (γ τ) p)) (𝓝[<] b) (𝓝 (ENNReal.ofReal 0)) :=
      ENNReal.tendsto_ofReal (hd_cont.comp hγtend)
    rwa [ENNReal.ofReal_zero] at h
  have hlim : Tendsto (fun τ => curveLength e γ a b + ENNReal.ofReal (d (γ τ) p)) (𝓝[<] b)
      (𝓝 (curveLength e γ a b + 0)) := tendsto_const_nhds.add hd0
  rw [add_zero] at hlim
  refine ge_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsLT hab] with τ hτ
  have hτU : γ τ ∈ U := (havoid τ ⟨hτ.1.le, hτ.2⟩).1
  calc ENNReal.ofReal (d (γ a) p)
      ≤ ENNReal.ofReal (d (γ a) (γ τ)) + ENNReal.ofReal (d (γ τ) p) :=
        ofReal_dist_le_add_of_tri hd_tri hA hτU hp
    _ ≤ curveLength e γ a τ + ENNReal.ofReal (d (γ τ) p) :=
        add_le_add (ofReal_dist_le_curveLength_of_avoid hd_tri hd_len hloc hγ hτ.1.le
          (fun τ' hτ' => havoid τ' ⟨hτ'.1, lt_of_le_of_lt hτ'.2 hτ.2⟩)) le_rfl
    _ ≤ curveLength e γ a b + ENNReal.ofReal (d (γ τ) p) :=
        add_le_add (curveLength_mono_Icc e γ le_rfl hτ.2.le) le_rfl

/-- Right endpoint bound: `γ` leaves `p` at `a` and avoids `p` on `(a, b]`; then `d(p, γ b)` is at
most the `e`-length of `γ` on `[a, b]`. -/
theorem ofReal_dist_right_le_curveLength_of_hit {d e : ℂ → ℂ → ℝ} {U : Set ℂ} {p : ℂ}
    (hp : p ∈ U)
    (hd_tri : ∀ x ∈ U, ∀ y ∈ U, ∀ z ∈ U, d x z ≤ d x y + d y z)
    (hd_len : ∀ x ∈ U, ∀ y ∈ U, ENNReal.ofReal (d x y) = internalMetric d U x y)
    (hd_symm : ∀ x y, d x y = d y x)
    (hd_cont : Tendsto (fun z => d z p) (𝓝[U] p) (𝓝 0))
    (hloc : ∀ q ∈ U, q ≠ p → ∃ V : Set ℂ, IsOpen V ∧ q ∈ V ∧ V ⊆ U ∧
      ∀ x ∈ V, ∀ y ∈ V, internalMetric d V x y = internalMetric e V x y)
    {γ : ℝ → ℂ} (hγ : Continuous γ) {a b : ℝ} (hab : a < b)
    (havoid : ∀ τ ∈ Ioc a b, γ τ ∈ U ∧ γ τ ≠ p) (hγa : γ a = p) :
    ENNReal.ofReal (d p (γ b)) ≤ curveLength e γ a b := by
  have hB : γ b ∈ U := (havoid b ⟨hab, le_rfl⟩).1
  have hγtend : Tendsto γ (𝓝[>] a) (𝓝[U] p) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have h1 : Tendsto γ (𝓝 a) (𝓝 p) := by
        have := hγ.tendsto a
        rwa [hγa] at this
      exact h1.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsGT hab] with τ hτ
      exact (havoid τ ⟨hτ.1, hτ.2.le⟩).1
  have hd0 : Tendsto (fun τ => ENNReal.ofReal (d (γ τ) p)) (𝓝[>] a) (𝓝 0) := by
    have h : Tendsto (fun τ => ENNReal.ofReal (d (γ τ) p)) (𝓝[>] a) (𝓝 (ENNReal.ofReal 0)) :=
      ENNReal.tendsto_ofReal (hd_cont.comp hγtend)
    rwa [ENNReal.ofReal_zero] at h
  have hlim : Tendsto (fun τ => curveLength e γ a b + ENNReal.ofReal (d (γ τ) p)) (𝓝[>] a)
      (𝓝 (curveLength e γ a b + 0)) := tendsto_const_nhds.add hd0
  rw [add_zero] at hlim
  refine ge_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsGT hab] with τ hτ
  have hτU : γ τ ∈ U := (havoid τ ⟨hτ.1, hτ.2.le⟩).1
  calc ENNReal.ofReal (d p (γ b))
      ≤ ENNReal.ofReal (d p (γ τ)) + ENNReal.ofReal (d (γ τ) (γ b)) :=
        ofReal_dist_le_add_of_tri hd_tri hp hτU hB
    _ ≤ ENNReal.ofReal (d p (γ τ)) + curveLength e γ a b :=
        add_le_add le_rfl ((ofReal_dist_le_curveLength_of_avoid hd_tri hd_len hloc hγ hτ.2.le
          (fun τ' hτ' => havoid τ' ⟨lt_of_lt_of_le hτ.1 hτ'.1, hτ'.2⟩)).trans
            (curveLength_mono_Icc e γ hτ.1.le le_rfl))
    _ = curveLength e γ a b + ENNReal.ofReal (d (γ τ) p) := by
        rw [hd_symm p (γ τ), add_comm]

/-- Global bound along a path: for a continuous `γ` with values in `U` on `[0, 1]`,
`d(γ 0, γ 1) ≤ len_e(γ)`. The hitting set of `p` is compact; split at its first and last point. -/
theorem ofReal_dist_le_curveLength_of_path {d e : ℂ → ℂ → ℝ} {U : Set ℂ} {p : ℂ}
    (hU : IsOpen U) (hp : p ∈ U)
    (hd_symm : ∀ x y, d x y = d y x)
    (hd_tri : ∀ x ∈ U, ∀ y ∈ U, ∀ z ∈ U, d x z ≤ d x y + d y z)
    (hd_len : ∀ x ∈ U, ∀ y ∈ U, ENNReal.ofReal (d x y) = internalMetric d U x y)
    (hd_cont : Tendsto (fun z => d z p) (𝓝[U] p) (𝓝 0))
    (hloc : ∀ q ∈ U, q ≠ p → ∃ V : Set ℂ, IsOpen V ∧ q ∈ V ∧ V ⊆ U ∧
      ∀ x ∈ V, ∀ y ∈ V, internalMetric d V x y = internalMetric e V x y)
    {γ : ℝ → ℂ} (hγ : Continuous γ) (hγU : ∀ τ ∈ Icc (0 : ℝ) 1, γ τ ∈ U) :
    ENNReal.ofReal (d (γ 0) (γ 1)) ≤ curveLength e γ 0 1 := by
  have hpp : ENNReal.ofReal (d p p) = 0 :=
    ENNReal.ofReal_eq_zero.2 (dist_self_le_zero_of_cont hU hp hd_symm hd_tri hd_cont)
  have hγ0 : γ 0 ∈ U := hγU 0 ⟨le_rfl, zero_le_one⟩
  have hγ1 : γ 1 ∈ U := hγU 1 ⟨zero_le_one, le_rfl⟩
  set T : Set ℝ := Icc (0 : ℝ) 1 ∩ {τ | γ τ = p} with hT_def
  have hTc : IsCompact T := isCompact_Icc.inter_right (isClosed_eq hγ continuous_const)
  by_cases hTe : T.Nonempty
  · have hs : sInf T ∈ T := hTc.sInf_mem hTe
    have ht : sSup T ∈ T := hTc.sSup_mem hTe
    have hst : sInf T ≤ sSup T := csInf_le hTc.bddBelow ht
    set s := sInf T with hs_def
    set t := sSup T with ht_def
    have hs01 : s ∈ Icc (0 : ℝ) 1 := hs.1
    have ht01 : t ∈ Icc (0 : ℝ) 1 := ht.1
    have hγs : γ s = p := hs.2
    have hγt : γ t = p := ht.2
    have hleft : ∀ τ ∈ Ico (0 : ℝ) s, γ τ ∈ U ∧ γ τ ≠ p := by
      intro τ hτ
      refine ⟨hγU τ ⟨hτ.1, by linarith [hτ.2, hs01.2]⟩, fun h => ?_⟩
      have hle : s ≤ τ := csInf_le hTc.bddBelow ⟨⟨hτ.1, by linarith [hτ.2, hs01.2]⟩, h⟩
      linarith [hτ.2]
    have hright : ∀ τ ∈ Ioc t 1, γ τ ∈ U ∧ γ τ ≠ p := by
      intro τ hτ
      refine ⟨hγU τ ⟨by linarith [hτ.1, ht01.1], hτ.2⟩, fun h => ?_⟩
      have hle : τ ≤ t := le_csSup hTc.bddAbove ⟨⟨by linarith [hτ.1, ht01.1], hτ.2⟩, h⟩
      linarith [hτ.1]
    have hL : ENNReal.ofReal (d (γ 0) p) ≤ curveLength e γ 0 s := by
      rcases eq_or_lt_of_le hs01.1 with h0 | hpos
      · have hγ0p : γ 0 = p := by
          rw [h0]
          exact hγs
        rw [hγ0p, hpp]
        exact zero_le
      · exact ofReal_dist_left_le_curveLength_of_hit hp hd_tri hd_len hd_cont hloc hγ hpos hleft hγs
    have hR : ENNReal.ofReal (d p (γ 1)) ≤ curveLength e γ t 1 := by
      rcases eq_or_lt_of_le ht01.2 with h1 | hlt
      · have hγ1p : γ 1 = p := by
          rw [← h1]
          exact hγt
        rw [hγ1p, hpp]
        exact zero_le
      · exact ofReal_dist_right_le_curveLength_of_hit hp hd_tri hd_len hd_symm hd_cont hloc hγ
          hlt hright hγt
    have hmid : curveLength e γ t 1 ≤ curveLength e γ s 1 := curveLength_mono_Icc e γ hst le_rfl
    have hsplit : curveLength e γ 0 s + curveLength e γ s 1 ≤ curveLength e γ 0 1 :=
      curveLength_add_le_general e γ hs01.1 hs01.2
    calc ENNReal.ofReal (d (γ 0) (γ 1))
        ≤ ENNReal.ofReal (d (γ 0) p) + ENNReal.ofReal (d p (γ 1)) :=
          ofReal_dist_le_add_of_tri hd_tri hγ0 hp hγ1
      _ ≤ curveLength e γ 0 s + curveLength e γ t 1 := add_le_add hL hR
      _ ≤ curveLength e γ 0 s + curveLength e γ s 1 := add_le_add le_rfl hmid
      _ ≤ curveLength e γ 0 1 := hsplit
  · exact ofReal_dist_le_curveLength_of_avoid hd_tri hd_len hloc hγ zero_le_one
      (fun τ hτ => ⟨hγU τ hτ, fun h => hTe ⟨τ, ⟨hτ, h⟩⟩⟩)

/-- One-sided comparison: under the hypotheses of `eq_of_local_internalMetric_agreement_off_point`
(with `d` as the metric being bounded above), `d x y ≤ e x y` on `U`. -/
theorem le_of_local_agreement {d e : ℂ → ℂ → ℝ} {U : Set ℂ} {p : ℂ} (hU : IsOpen U) (hp : p ∈ U)
    (hd_symm : ∀ x y, d x y = d y x)
    (hd_tri : ∀ x ∈ U, ∀ y ∈ U, ∀ z ∈ U, d x z ≤ d x y + d y z)
    (hd_len : ∀ x ∈ U, ∀ y ∈ U, ENNReal.ofReal (d x y) = internalMetric d U x y)
    (hd_cont : Tendsto (fun z => d z p) (𝓝[U] p) (𝓝 0))
    (he_len : ∀ x ∈ U, ∀ y ∈ U, ENNReal.ofReal (e x y) = internalMetric e U x y)
    (he_nonneg : ∀ x ∈ U, ∀ y ∈ U, 0 ≤ e x y)
    (hloc : ∀ q ∈ U, q ≠ p → ∃ V : Set ℂ, IsOpen V ∧ q ∈ V ∧ V ⊆ U ∧
      ∀ x ∈ V, ∀ y ∈ V, internalMetric d V x y = internalMetric e V x y) :
    ∀ x ∈ U, ∀ y ∈ U, d x y ≤ e x y := by
  intro x hx y hy
  have hle : ENNReal.ofReal (d x y) ≤ ENNReal.ofReal (e x y) := by
    rw [he_len x hx y hy]
    unfold internalMetric
    refine le_iInf₂ fun P hP => ?_
    have hγU : ∀ τ ∈ Icc (0 : ℝ) 1, P.extend τ ∈ U := fun τ hτ => by
      have h := Path.extend_extends' P ⟨τ, hτ⟩
      rw [show P.extend τ = P ⟨τ, hτ⟩ from h]
      exact hP _
    have key := ofReal_dist_le_curveLength_of_path hU hp hd_symm hd_tri hd_len hd_cont hloc
      P.continuous_extend hγU
    rw [Path.extend_zero, Path.extend_one] at key
    exact key
  exact (ENNReal.ofReal_le_ofReal_iff (he_nonneg x hx y hy)).1 hle

/-- A real function on `U × U` which is symmetric and satisfies the triangle inequality on `U` is nonnegative on `U`:
`d x x ≤ d x x + d x x` gives `0 ≤ d x x`, and `d x x ≤ d x y + d y x = 2 d x y` (CHATGPT-n2-hII.md, section 3.1). -/
theorem nonneg_of_symm_triangle_on {X : Type*} {U : Set X} {d : X → X → ℝ}
    (hsymm : ∀ x y, d x y = d y x)
    (htri : ∀ x ∈ U, ∀ y ∈ U, ∀ z ∈ U, d x z ≤ d x y + d y z) :
    ∀ x ∈ U, ∀ y ∈ U, 0 ≤ d x y := by
  intro x hx y hy
  have hdiag := htri x hx x hx x hx
  have hloop := htri x hx y hy x hx
  rw [hsymm y x] at hloop
  linarith

/-- Deleting one point (CHATGPT-n3-B1-B2.md, section 4.3): two length metrics `d`, `e` (symmetric, with the
triangle inequality on `U`, and internal-metric identities on `U`) on an open `U` whose internal metrics agree on a
neighbourhood of each point of `U \ {p}`, and which tend to `0` at `p` (within `U`), coincide on `U`. Nonnegativity
is not assumed: it follows from symmetry and the triangle inequality (`nonneg_of_symm_triangle_on`). -/
theorem eq_of_local_internalMetric_agreement_off_point
    {U : Set ℂ} (hU : IsOpen U) {p : ℂ} (hp : p ∈ U)
    {d e : ℂ → ℂ → ℝ}
    (hd_symm : ∀ x y, d x y = d y x) (he_symm : ∀ x y, e x y = e y x)
    (hd_tri : ∀ x ∈ U, ∀ y ∈ U, ∀ z ∈ U, d x z ≤ d x y + d y z)
    (he_tri : ∀ x ∈ U, ∀ y ∈ U, ∀ z ∈ U, e x z ≤ e x y + e y z)
    (hd_len : ∀ x ∈ U, ∀ y ∈ U, ENNReal.ofReal (d x y) = internalMetric d U x y)
    (he_len : ∀ x ∈ U, ∀ y ∈ U, ENNReal.ofReal (e x y) = internalMetric e U x y)
    (hd_cont : Tendsto (fun z => d z p) (𝓝[U] p) (𝓝 0))
    (he_cont : Tendsto (fun z => e z p) (𝓝[U] p) (𝓝 0))
    (hloc : ∀ q ∈ U, q ≠ p → ∃ V : Set ℂ, IsOpen V ∧ q ∈ V ∧ V ⊆ U ∧
      ∀ x ∈ V, ∀ y ∈ V, internalMetric d V x y = internalMetric e V x y)
    :
    ∀ x ∈ U, ∀ y ∈ U, d x y = e x y := by
  have hd_nonneg : ∀ x ∈ U, ∀ y ∈ U, 0 ≤ d x y := nonneg_of_symm_triangle_on hd_symm hd_tri
  have he_nonneg : ∀ x ∈ U, ∀ y ∈ U, 0 ≤ e x y := nonneg_of_symm_triangle_on he_symm he_tri
  have hloc': ∀ q ∈ U, q ≠ p → ∃ V : Set ℂ, IsOpen V ∧ q ∈ V ∧ V ⊆ U ∧
      ∀ x ∈ V, ∀ y ∈ V, internalMetric e V x y = internalMetric d V x y := by
    intro q hq hqp
    obtain ⟨V, h1, h2, h3, h4⟩ := hloc q hq hqp
    exact ⟨V, h1, h2, h3, fun x hx y hy => (h4 x hx y hy).symm⟩
  intro x hx y hy
  exact le_antisymm
    (le_of_local_agreement hU hp hd_symm hd_tri hd_len hd_cont he_len he_nonneg hloc x hx y hy)
    (le_of_local_agreement hU hp he_symm he_tri he_len he_cont hd_len hd_nonneg hloc' x hx y hy)

end HarmonicBalls

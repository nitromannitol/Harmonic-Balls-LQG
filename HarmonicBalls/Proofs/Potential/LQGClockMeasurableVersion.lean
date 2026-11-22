import Mathlib

/-! # Jointly measurable versions of quenched limits in probability

Two measure-theoretic facts used to pass from clocks defined for each fixed field to statements
under the joint law of the field and the path.

* If jointly measurable random variables `A k (ω, b)` converge, for almost every `ω`, in
  probability in `b` to some (not necessarily measurable) `F ω b`, then they are Cauchy in
  probability under the product measure (dominated convergence for the sections), so a
  subsequence converges almost surely, by the Borel-Cantelli lemma, to a jointly measurable
  limit `G`; `A k` converges to `G` in probability under the product measure, and for almost every
  `ω` the limit `G (ω, ·)` agrees almost surely with `F ω`.
* Limits in probability of identically distributed sequences are identically distributed: along a
  common subsequence both sequences converge almost surely, and the upper limit along that
  subsequence is a measurable function of the whole sequence.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace HarmonicBalls

/-- Limits in probability of identically distributed sequences of real random variables are
identically distributed. -/
theorem identDistrib_of_tendstoInMeasure {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {μ' : Measure Ω'} {A : ℕ → Ω → ℝ} {A' : ℕ → Ω' → ℝ} {G : Ω → ℝ}
    {G' : Ω' → ℝ} (hid : IdentDistrib (fun ω k => A k ω) (fun ω k => A' k ω) μ μ')
    (hA : TendstoInMeasure μ A atTop G) (hA' : TendstoInMeasure μ' A' atTop G') :
    IdentDistrib G G' μ μ' := by
  obtain ⟨ns, hns, hns_ae⟩ := hA.exists_seq_tendsto_ae
  have hA'ns : TendstoInMeasure μ' (fun i => A' (ns i)) atTop G' :=
    fun ε hε => (hA' ε hε).comp hns.tendsto_atTop
  obtain ⟨ns2, hns2, hns2_ae⟩ := hA'ns.exists_seq_tendsto_ae
  let φ : ℕ → ℕ := fun i => ns (ns2 i)
  let L : (ℕ → ℝ) → ℝ := fun x => limsup (fun i => x (φ i)) atTop
  have hL : Measurable L := Measurable.limsup fun i => measurable_pi_apply (φ i)
  have h1 : (L ∘ fun ω k => A k ω) =ᵐ[μ] G := by
    filter_upwards [hns_ae] with ω hω
    exact (hω.comp hns2.tendsto_atTop).limsup_eq
  have h2 : (L ∘ fun ω k => A' k ω) =ᵐ[μ'] G' := by
    filter_upwards [hns2_ae] with ω hω
    exact hω.limsup_eq
  have hcomp := hid.comp hL
  exact ((IdentDistrib.of_ae_eq hcomp.aemeasurable_fst h1).symm.trans hcomp).trans
    (IdentDistrib.of_ae_eq hcomp.aemeasurable_snd h2)

/-- Jointly measurable random variables that converge in probability in the second coordinate
for almost every first coordinate have a jointly measurable limit in probability under the
product measure, which agrees for almost every first coordinate almost surely with the limits of
the sections. -/
theorem exists_measurable_tendstoInMeasure_prod {Ω X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] {P : Measure Ω} {ν : Measure X} [IsProbabilityMeasure P]
    [IsProbabilityMeasure ν] {A : ℕ → Ω × X → ℝ} (hA : ∀ k, Measurable (A k)) {F : Ω → X → ℝ}
    (hconv : ∀ᵐ ω ∂P, TendstoInMeasure ν (fun k b => A k (ω, b)) atTop (F ω)) :
    ∃ G : Ω × X → ℝ, Measurable G ∧ TendstoInMeasure (P.prod ν) A atTop G ∧
      ∀ᵐ ω ∂P, ∀ᵐ b ∂ν, G (ω, b) = F ω b := by
  -- Cauchy in probability under the product measure
  have hcauchy : ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun kl : ℕ × ℕ =>
      (P.prod ν) {p | ε ≤ edist (A kl.1 p) (A kl.2 p)}) atTop (𝓝 0) := by
    intro ε hε
    have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
    have hS (kl : ℕ × ℕ) : MeasurableSet {p : Ω × X | ε ≤ edist (A kl.1 p) (A kl.2 p)} :=
      measurableSet_le measurable_const ((hA kl.1).edist (hA kl.2))
    have happly (kl : ℕ × ℕ) : (P.prod ν) {p | ε ≤ edist (A kl.1 p) (A kl.2 p)} =
        ∫⁻ ω, ν (Prod.mk ω ⁻¹' {p | ε ≤ edist (A kl.1 p) (A kl.2 p)}) ∂P :=
      Measure.prod_apply (hS kl)
    have hsection : ∀ ω, TendstoInMeasure ν (fun k b => A k (ω, b)) atTop (F ω) →
        Tendsto (fun kl : ℕ × ℕ =>
          ν (Prod.mk ω ⁻¹' {p | ε ≤ edist (A kl.1 p) (A kl.2 p)})) atTop (𝓝 0) := by
      intro ω hω
      have h1 : Tendsto (fun kl : ℕ × ℕ => ν {b | ε / 2 ≤ edist (A kl.1 (ω, b)) (F ω b)}) atTop
          (𝓝 0) := (hω (ε / 2) hε2).comp (tendsto_fst.mono_left prod_atTop_atTop_eq.ge)
      have h2 : Tendsto (fun kl : ℕ × ℕ => ν {b | ε / 2 ≤ edist (A kl.2 (ω, b)) (F ω b)}) atTop
          (𝓝 0) := (hω (ε / 2) hε2).comp (tendsto_snd.mono_left prod_atTop_atTop_eq.ge)
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (by simpa only [add_zero] using h1.add h2) (fun kl => zero_le) fun kl => ?_
      refine le_trans (measure_mono ?_) (measure_union_le _ _)
      intro b hb
      simp only [mem_preimage, mem_ofPred_eq] at hb
      by_contra hcon
      simp only [mem_union, mem_ofPred_eq, not_or, not_le] at hcon
      have htri := edist_triangle_right (A kl.1 (ω, b)) (A kl.2 (ω, b)) (F ω b)
      have : edist (A kl.1 (ω, b)) (A kl.2 (ω, b)) < ε := by
        calc edist (A kl.1 (ω, b)) (A kl.2 (ω, b))
            ≤ edist (A kl.1 (ω, b)) (F ω b) + edist (A kl.2 (ω, b)) (F ω b) := htri
          _ < ε / 2 + ε / 2 := ENNReal.add_lt_add hcon.1 hcon.2
          _ = ε := ENNReal.add_halves ε
      exact absurd hb (not_le.mpr this)
    simp_rw [happly]
    have hsec : ∀ᵐ ω ∂P, Tendsto (fun kl : ℕ × ℕ =>
        ν (Prod.mk ω ⁻¹' {p | ε ≤ edist (A kl.1 p) (A kl.2 p)})) atTop (𝓝 0) := by
      filter_upwards [hconv] with ω hω
      exact hsection ω hω
    have hlim := tendsto_lintegral_filter_of_dominated_convergence (μ := P) (l := atTop)
      (F := fun (kl : ℕ × ℕ) ω => ν (Prod.mk ω ⁻¹' {p | ε ≤ edist (A kl.1 p) (A kl.2 p)}))
      (f := fun _ => 0) (fun _ => 1)
      (Eventually.of_forall fun kl => measurable_measure_prodMk_left (hS kl))
      (Eventually.of_forall fun kl => Eventually.of_forall fun ω => prob_le_one)
      (by simp) hsec
    simpa using hlim
  -- a fast subsequence
  have hfast (j : ℕ) : ∃ K : ℕ, ∀ k l : ℕ, K ≤ k → K ≤ l →
      (P.prod ν) {p | ENNReal.ofReal ((1 / 2 : ℝ) ^ j) ≤ edist (A k p) (A l p)} <
        ENNReal.ofReal ((1 / 2 : ℝ) ^ j) := by
    have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal ((1 / 2 : ℝ) ^ j) :=
      ENNReal.ofReal_pos.mpr (by positivity)
    obtain ⟨N, hN⟩ := eventually_atTop.mp ((hcauchy _ hpos).eventually (gt_mem_nhds hpos))
    exact ⟨max N.1 N.2, fun k l hk hl => hN (k, l)
      ⟨(le_max_left _ _).trans hk, (le_max_right _ _).trans hl⟩⟩
  choose K hK using hfast
  let kk : ℕ → ℕ := fun j => j + ∑ i ∈ Finset.range (j + 1), K i
  have hkk_mono : StrictMono kk := by
    refine strictMono_nat_of_lt_succ fun j => ?_
    simp only [kk, Finset.sum_range_succ]
    omega
  have hkkK (j : ℕ) : K j ≤ kk j := by
    simp only [kk]
    have := Finset.single_le_sum (f := K) (fun i _ => Nat.zero_le (K i))
      (Finset.self_mem_range_succ j)
    omega
  let B : ℕ → Set (Ω × X) := fun j =>
    {p | ENNReal.ofReal ((1 / 2 : ℝ) ^ j) ≤ edist (A (kk j) p) (A (kk (j + 1)) p)}
  have hB (j : ℕ) : (P.prod ν) (B j) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ j) :=
    (hK j (kk j) (kk (j + 1)) (hkkK j) ((hkkK j).trans (hkk_mono.monotone (Nat.le_succ j)))).le
  have hsum : (∑' j, (P.prod ν) (B j)) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hB)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity)
      (summable_geometric_of_lt_one (by norm_num) (by norm_num))]
    exact ENNReal.ofReal_ne_top
  have hconvsub : ∀ᵐ p ∂(P.prod ν), ∃ L : ℝ, Tendsto (fun j => A (kk j) p) atTop (𝓝 L) := by
    filter_upwards [ae_eventually_notMem hsum] with p hp
    obtain ⟨N, hN⟩ := eventually_atTop.mp hp
    have hdist (j : ℕ) : dist (A (kk (j + N)) p) (A (kk (j + N + 1)) p) ≤ (1 / 2 : ℝ) ^ (j + N) := by
      have h := hN (j + N) (Nat.le_add_left N j)
      simp only [B, mem_ofPred_eq, not_le] at h
      rw [edist_dist] at h
      exact ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp h).le
    have hsumm : Summable fun j => dist (A (kk (j + N)) p) (A (kk (j + 1 + N)) p) := by
      refine Summable.of_nonneg_of_le (fun j => dist_nonneg) (fun j => ?_)
        ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num : (1 / 2 : ℝ) < 1)).mul_left ((1 / 2 : ℝ) ^ N))
      rw [show j + 1 + N = j + N + 1 by omega]
      calc _ ≤ (1 / 2 : ℝ) ^ (j + N) := hdist j
        _ = (1 / 2 : ℝ) ^ N * (1 / 2 : ℝ) ^ j := by rw [pow_add, mul_comm]
    have hc : CauchySeq fun j => A (kk (j + N)) p := cauchySeq_of_summable_dist hsumm
    obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc
    exact ⟨L, (tendsto_add_atTop_iff_nat N).mp hL⟩
  let G : Ω × X → ℝ := fun p => limsup (fun j => A (kk j) p) atTop
  have hGm : Measurable G := Measurable.limsup fun j => hA (kk j)
  have hGlim : ∀ᵐ p ∂(P.prod ν), Tendsto (fun j => A (kk j) p) atTop (𝓝 (G p)) := by
    filter_upwards [hconvsub] with p ⟨L, hL⟩
    have : G p = L := hL.limsup_eq
    rw [this]
    exact hL
  refine ⟨G, hGm, ?_, ?_⟩
  · -- convergence in probability of the whole sequence
    have hsubG : TendstoInMeasure (P.prod ν) (fun j => A (kk j)) atTop G :=
      tendstoInMeasure_of_tendsto_ae (fun j => (hA (kk j)).aestronglyMeasurable) hGlim
    intro ε hε
    have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
    have hdiag : Tendsto (fun k : ℕ => (k, kk k)) atTop (atTop : Filter (ℕ × ℕ)) := by
      rw [← prod_atTop_atTop_eq]
      exact tendsto_id.prodMk hkk_mono.tendsto_atTop
    have h1 := (hcauchy (ε / 2) hε2).comp hdiag
    have h2 := hsubG (ε / 2) hε2
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa only [add_zero] using h1.add h2) (fun k => zero_le) fun k => ?_
    refine le_trans (measure_mono ?_) (measure_union_le _ _)
    intro p hp
    simp only [mem_ofPred_eq] at hp
    by_contra hcon
    simp only [mem_union, mem_ofPred_eq, not_or, not_le] at hcon
    have : edist (A k p) (G p) < ε := by
      calc edist (A k p) (G p) ≤ edist (A k p) (A (kk k) p) + edist (A (kk k) p) (G p) :=
            edist_triangle _ _ _
        _ < ε / 2 + ε / 2 := ENNReal.add_lt_add hcon.1 hcon.2
        _ = ε := ENNReal.add_halves ε
    exact absurd hp (not_le.mpr this)
  · -- identification with the quenched limits
    filter_upwards [Measure.ae_ae_of_ae_prod hGlim, hconv] with ω hω hωF
    have hsub : TendstoInMeasure ν (fun j b => A (kk j) (ω, b)) atTop (F ω) :=
      fun ε hε => (hωF ε hε).comp hkk_mono.tendsto_atTop
    obtain ⟨ns, hns, hns_ae⟩ := hsub.exists_seq_tendsto_ae
    filter_upwards [hω, hns_ae] with b hb1 hb2
    exact tendsto_nhds_unique (hb1.comp hns.tendsto_atTop) hb2

end HarmonicBalls

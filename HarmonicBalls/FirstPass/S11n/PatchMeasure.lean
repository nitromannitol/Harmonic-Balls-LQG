import Mathlib

/-!
# Patching local LQG measure decoders over a countable cover of `ℂ \ {0}`

Deterministic core of the measure part (B1-μ) of `LQGCanonicalIdentificationStmt`. Given open balls `B j` avoiding `0`
and covering `ℂ \ {0}`, and measures `ν j = c j • μ.restrict (B j)` with constants `c j ∈ (0, ∞)` (the local LQG
decoders of `LocalLQGDecoderCommonFrozen`, Frozen/S11c.lean), the measure `μ` is a fixed multiple of the patched measure
`Σ_j ρ_j • ν_j.restrict (A_j)`. Here `A_j = B_j \ ⋃_{i<j} B_i` is the disjointified cover and `ρ_j` is the product of the
overlap ratios `ν_a(B_a ∩ B_b) / ν_b(B_a ∩ B_b)` along a chain from the base ball `i₀` to `j`. The chain product is
independent of the chain (it is `c_{i₀} / c_j`), and the nerve of the cover is connected because `ℂ \ {0}` is connected
(Mathlib `isConnected_compl_singleton_of_one_lt_rank`). No probability is used here.
-/

noncomputable section

namespace HarmonicBalls.S11n.PatchMeasure

open MeasureTheory Set Function
open scoped ENNReal

/-- Overlap of two balls of the cover (the nerve relation). -/
def Ov (B : ℕ → Set ℂ) (a b : ℕ) : Prop := (B a ∩ B b).Nonempty

/-- Disjointified cover `A j = B j \ ⋃ i < j, B i`. -/
def disj (B : ℕ → Set ℂ) (j : ℕ) : Set ℂ := B j \ ⋃ i < j, B i

/-- Last vertex of the chain `a :: l`. -/
def lastOf (a : ℕ) (l : List ℕ) : ℕ := (a :: l).getLast (List.cons_ne_nil _ _)

/-- Product of the overlap ratios `R a b` along the chain `l` started at `a`. -/
def chainScale (R : ℕ → ℕ → ℝ≥0∞) : ℕ → List ℕ → ℝ≥0∞
  | _, [] => 1
  | a, b :: l => R a b * chainScale R b l

/-- Overlap ratio `ν_a(B_a ∩ B_b) / ν_b(B_a ∩ B_b)`. -/
def ratioOf (B : ℕ → Set ℂ) (ν : ℕ → Measure ℂ) (a b : ℕ) : ℝ≥0∞ :=
  ν a (B a ∩ B b) / ν b (B a ∩ B b)

/-- The patched measure `Σ_j ρ_j • ν_j|A_j`, with `ρ_j` the chain product along the chain `L j` from `i₀`. -/
def patchMeasure (B : ℕ → Set ℂ) (ν : ℕ → Measure ℂ) (L : ℕ → List ℕ) (i₀ : ℕ) : Measure ℂ :=
  Measure.sum fun j => chainScale (ratioOf B ν) i₀ (L j) • (ν j).restrict (disj B j)

theorem lastOf_cons (a b : ℕ) (l : List ℕ) : lastOf a (b :: l) = lastOf b l := by
  simp [lastOf]

theorem chainScale_edge (R : ℕ → ℕ → ℝ≥0∞) (B : ℕ → Set ℂ) (c : ℕ → ℝ≥0∞) :
    ∀ (l : List ℕ) (a : ℕ), List.IsChain (Ov B) (a :: l) → (∀ x y, Ov B x y → R x y * c y = c x) →
      chainScale R a l * c (lastOf a l) = c a
  | [], a, _, _ => by simp [chainScale, lastOf]
  | b :: l, a, hch, hedge => by
    rw [List.isChain_cons_cons] at hch
    have ih := chainScale_edge R B c l b hch.2 hedge
    rw [chainScale, lastOf_cons, mul_assoc, ih]
    exact hedge a b hch.1

theorem reach_of_cover {B : ℕ → Set ℂ} (hopen : ∀ j, IsOpen (B j))
    (hcov : ∀ z : ℂ, z ≠ 0 → ∃ j, z ∈ B j) (hsub : ∀ j, (0 : ℂ) ∉ B j) (hne : ∀ j, (B j).Nonempty) (i j : ℕ) :
    Relation.ReflTransGen (Ov B) i j := by
  set R : Set ℕ := {k | Relation.ReflTransGen (Ov B) i k} with hR
  set U : Set ℂ := ⋃ k ∈ R, B k with hU
  set V : Set ℂ := ⋃ k ∈ Rᶜ, B k with hV
  have hUo : IsOpen U := isOpen_biUnion fun k _ => hopen k
  have hVo : IsOpen V := isOpen_biUnion fun k _ => hopen k
  have hdisj : Disjoint U V := by
    rw [Set.disjoint_left]
    intro z hzU hzV
    simp only [hU, hV, Set.mem_iUnion] at hzU hzV
    obtain ⟨k, hk, hzk⟩ := hzU
    obtain ⟨k', hk', hzk'⟩ := hzV
    exact hk' (Relation.ReflTransGen.tail hk ⟨z, hzk, hzk'⟩)
  have hcover : ({0}ᶜ : Set ℂ) ⊆ U ∪ V := by
    intro z hz
    obtain ⟨j, hj⟩ := hcov z hz
    by_cases hjR : Relation.ReflTransGen (Ov B) i j
    · exact Or.inl (Set.mem_biUnion (show j ∈ R from hjR) hj)
    · exact Or.inr (Set.mem_biUnion (show j ∈ Rᶜ from hjR) hj)
  have hconn : IsPreconnected ({0}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by rw [Complex.rank_real_complex]; norm_num) (0 : ℂ)).isPreconnected
  obtain ⟨x0, hx0⟩ := hne i
  have hsU : ({0}ᶜ : Set ℂ) ⊆ U :=
    hconn.subset_left_of_subset_union hUo hVo hdisj hcover
      ⟨x0, fun h => hsub i (h ▸ hx0), Set.mem_biUnion (show i ∈ R from Relation.ReflTransGen.refl) hx0⟩
  obtain ⟨xj, hxj⟩ := hne j
  have hxjU : xj ∈ U := hsU (fun h => hsub j (h ▸ hxj))
  simp only [hU, Set.mem_iUnion] at hxjU
  obtain ⟨k, hk, hxk⟩ := hxjU
  exact Relation.ReflTransGen.tail hk ⟨xj, hxk, hxj⟩

theorem exists_chain {B : ℕ → Set ℂ} (hopen : ∀ j, IsOpen (B j))
    (hcov : ∀ z : ℂ, z ≠ 0 → ∃ j, z ∈ B j) (hsub : ∀ j, (0 : ℂ) ∉ B j) (hne : ∀ j, (B j).Nonempty) (i j : ℕ) :
    ∃ l : List ℕ, List.IsChain (Ov B) (i :: l) ∧ lastOf i l = j :=
  List.exists_isChain_cons_of_relationReflTransGen (reach_of_cover hopen hcov hsub hne i j)

theorem ratioOf_edge {B : ℕ → Set ℂ} (hopen : ∀ j, IsOpen (B j)) (μ : Measure ℂ) (ν : ℕ → Measure ℂ)
    (c : ℕ → ℝ≥0∞) (hc0 : ∀ j, c j ≠ 0) (hcT : ∀ j, c j ≠ ⊤) (hν : ∀ j, ν j = c j • μ.restrict (B j))
    (hfin : ∀ a b, Ov B a b → μ (B a ∩ B b) ≠ 0 ∧ μ (B a ∩ B b) ≠ ⊤) (a b : ℕ) (hab : Ov B a b) :
    ratioOf B ν a b * c b = c a := by
  have hS : MeasurableSet (B a ∩ B b) := ((hopen a).inter (hopen b)).measurableSet
  have hna : ν a (B a ∩ B b) = c a * μ (B a ∩ B b) := by
    rw [hν a, Measure.smul_apply, Measure.restrict_apply hS, Set.inter_eq_left.2 inter_subset_left, smul_eq_mul]
  have hnb : ν b (B a ∩ B b) = c b * μ (B a ∩ B b) := by
    rw [hν b, Measure.smul_apply, Measure.restrict_apply hS, Set.inter_eq_left.2 inter_subset_right, smul_eq_mul]
  obtain ⟨h0, hT⟩ := hfin a b hab
  unfold ratioOf
  rw [hna, hnb, ENNReal.mul_div_mul_right _ _ h0 hT, ENNReal.div_mul_cancel (hc0 b) (hcT b)]

theorem patchMeasure_identity {B : ℕ → Set ℂ} (hopen : ∀ j, IsOpen (B j))
    (hcov : ∀ z : ℂ, z ≠ 0 → ∃ j, z ∈ B j)
    (μ : Measure ℂ) (hμ0 : μ {0} = 0) (ν : ℕ → Measure ℂ) (c : ℕ → ℝ≥0∞)
    (hc0 : ∀ j, c j ≠ 0) (hcT : ∀ j, c j ≠ ⊤) (hν : ∀ j, ν j = c j • μ.restrict (B j))
    (hfin : ∀ a b, Ov B a b → μ (B a ∩ B b) ≠ 0 ∧ μ (B a ∩ B b) ≠ ⊤)
    (i₀ : ℕ) (L : ℕ → List ℕ) (hL : ∀ j, List.IsChain (Ov B) (i₀ :: L j) ∧ lastOf i₀ (L j) = j) :
    c i₀ • μ = patchMeasure B ν L i₀ := by
  have hAo : ∀ j, MeasurableSet (disj B j) := fun j =>
    (hopen j).measurableSet.diff (isOpen_iUnion fun i => isOpen_iUnion fun _ => hopen i).measurableSet
  have hAdisj : Pairwise (Disjoint on disj B) := by
    intro j k hjk
    rcases Nat.lt_or_gt_of_ne hjk with h | h
    · refine Set.disjoint_left.2 fun z hzj hzk => hzk.2 ?_
      exact Set.mem_iUnion₂.2 ⟨j, h, hzj.1⟩
    · refine Set.disjoint_left.2 fun z hzk hzj => hzk.2 ?_
      exact Set.mem_iUnion₂.2 ⟨k, h, hzj.1⟩
  have hAcov : ∀ z : ℂ, z ≠ 0 → ∃ j, z ∈ disj B j := by
    intro z hz
    classical
    have hex := hcov z hz
    refine ⟨Nat.find hex, Nat.find_spec hex, fun hmem => ?_⟩
    obtain ⟨i, hi, hzi⟩ := Set.mem_iUnion₂.1 hmem
    exact Nat.find_min hex hi hzi
  have hcompl : (⋃ j, disj B j)ᶜ ⊆ {0} := by
    intro z hz
    by_contra h0
    have hz0 : z ≠ 0 := fun h => h0 (Set.mem_singleton_iff.2 h)
    exact hz (Set.mem_iUnion.2 (hAcov z hz0))
  have hμsplit : μ = Measure.sum fun j => μ.restrict (disj B j) := by
    have h1 : μ.restrict (⋃ j, disj B j) = μ := by
      have hc : μ.restrict (⋃ j, disj B j)ᶜ = 0 :=
        Measure.restrict_eq_zero.2 (measure_mono_null hcompl hμ0)
      have h2 := Measure.restrict_add_restrict_compl (μ := μ) (MeasurableSet.iUnion hAo)
      rw [hc, add_zero] at h2
      exact h2
    calc μ = μ.restrict (⋃ j, disj B j) := h1.symm
      _ = Measure.sum fun j => μ.restrict (disj B j) := Measure.restrict_iUnion hAdisj hAo
  have hpiece : ∀ j, c i₀ • μ.restrict (disj B j) =
      chainScale (ratioOf B ν) i₀ (L j) • (ν j).restrict (disj B j) := by
    intro j
    have hchain := chainScale_edge (ratioOf B ν) B c (L j) i₀ (hL j).1
      (fun x y hxy => ratioOf_edge hopen μ ν c hc0 hcT hν hfin x y hxy)
    rw [(hL j).2] at hchain
    rw [hν j, Measure.restrict_smul, Measure.restrict_restrict (hAo j),
      Set.inter_eq_left.2 (fun x hx => hx.1), ← hchain, mul_smul]
  calc c i₀ • μ = c i₀ • Measure.sum fun j => μ.restrict (disj B j) := by rw [← hμsplit]
    _ = Measure.sum fun j => c i₀ • μ.restrict (disj B j) := by
        ext s hs
        rw [Measure.smul_apply, Measure.sum_apply _ hs, Measure.sum_apply _ hs]
        simp only [Measure.smul_apply, smul_eq_mul, ENNReal.tsum_mul_left]
    _ = patchMeasure B ν L i₀ := by
        unfold patchMeasure
        congr 1
        funext j
        exact hpiece j

end HarmonicBalls.S11n.PatchMeasure

end

import Mathlib

/-!
# Patching local measures over a countable cover of a preconnected set (fp-S11m, owner z4)

Generalisation of `HarmonicBalls.S11n.PatchMeasure` (a cover of `ℂ \ {0}`) to a cover of an arbitrary preconnected set
`X ⊆ ℂ` by open sets `B j ⊆ X`, for instance `X = B₇(0) \ {0}` in the measure decoder of Lemma 11.12 (route
`notes/fp-gaps/CHATGPT-z4-11-12-local-certificate.md`, section 3, equations (8)-(11)). The local measures are
`ν j = c j • μ.restrict (B j)`; the patch is `Σ_j ρ_j • ν_j.restrict (disj B j)` with `ρ_j` the product of the overlap
ratios along a chain from the base ball `i₀` to `j`. Connectedness of `X` replaces the connectedness of `ℂ \ {0}` used in
`PatchMeasure.reach_of_cover`. Deterministic; no probability.
-/

noncomputable section

namespace HarmonicBalls.S11m.PatchOpen

open MeasureTheory Set Function
open scoped ENNReal

/-- The nerve relation of the cover: two balls overlap. -/
def Ov (B : ℕ → Set ℂ) (a b : ℕ) : Prop := (B a ∩ B b).Nonempty

theorem Ov.symm' {B : ℕ → Set ℂ} {a b : ℕ} (h : Ov B a b) : Ov B b a := by
  rw [Ov, Set.inter_comm]; exact h

/-- The disjointified cover `disj B j = B j \ ⋃ i < j, B i`. -/
def disj (B : ℕ → Set ℂ) (j : ℕ) : Set ℂ := B j \ ⋃ i < j, B i

/-- Last vertex of the chain `a :: l`. -/
def lastOf (a : ℕ) (l : List ℕ) : ℕ := (a :: l).getLast (List.cons_ne_nil _ _)

theorem lastOf_cons (a b : ℕ) (l : List ℕ) : lastOf a (b :: l) = lastOf b l := rfl

/-- Product of the ratios `R a b` along the chain `a :: l`. -/
def chainScale (R : ℕ → ℕ → ℝ≥0∞) : ℕ → List ℕ → ℝ≥0∞
  | _, [] => 1
  | a, b :: l => R a b * chainScale R b l

/-- Along an admissible chain the ratios telescope: `chainScale R a l * c (lastOf a l) = c a`. -/
theorem chainScale_mul_last (B : ℕ → Set ℂ) (R : ℕ → ℕ → ℝ≥0∞) (c : ℕ → ℝ≥0∞)
    (hR : ∀ a b, Ov B a b → R a b * c b = c a) :
    ∀ (a : ℕ) (l : List ℕ), List.IsChain (Ov B) (a :: l) → chainScale R a l * c (lastOf a l) = c a
  | a, [], _ => by simp [chainScale, lastOf]
  | a, b :: l, h => by
    obtain ⟨hab, ht⟩ := List.isChain_cons_cons.1 h
    rw [chainScale, lastOf_cons, mul_assoc, chainScale_mul_last B R c hR b l ht, hR a b hab]

/-- Reachability in the nerve of a cover of a preconnected set `X` by open subsets of `X`. The proof is the one of
`PatchMeasure.reach_of_cover`, with the connectedness of `ℂ \ {0}` replaced by that of `X`. -/
theorem reach_of_cover {X : Set ℂ} (hX : IsPreconnected X) {B : ℕ → Set ℂ} (hopen : ∀ j, IsOpen (B j))
    (hsub : ∀ j, B j ⊆ X) (hcov : X ⊆ ⋃ j, B j) (hne : ∀ j, (B j).Nonempty) (i j : ℕ) :
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
  have hcover : X ⊆ U ∪ V := by
    intro z hz
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (hcov hz)
    by_cases hjR : Relation.ReflTransGen (Ov B) i j
    · exact Or.inl (Set.mem_biUnion (show j ∈ R from hjR) hj)
    · exact Or.inr (Set.mem_biUnion (show j ∈ Rᶜ from hjR) hj)
  obtain ⟨x0, hx0⟩ := hne i
  have hsU : X ⊆ U :=
    hX.subset_left_of_subset_union hUo hVo hdisj hcover
      ⟨x0, hsub i hx0, Set.mem_biUnion (show i ∈ R from Relation.ReflTransGen.refl) hx0⟩
  obtain ⟨xj, hxj⟩ := hne j
  obtain ⟨k, hk, hxk⟩ := Set.mem_iUnion₂.1 (hsU (hsub j hxj))
  exact Relation.ReflTransGen.tail hk ⟨xj, hxk, hxj⟩

/-- A chain from `i` to every ball of the cover. -/
theorem exists_chain {X : Set ℂ} (hX : IsPreconnected X) {B : ℕ → Set ℂ} (hopen : ∀ j, IsOpen (B j))
    (hsub : ∀ j, B j ⊆ X) (hcov : X ⊆ ⋃ j, B j) (hne : ∀ j, (B j).Nonempty) (i j : ℕ) :
    ∃ l : List ℕ, List.IsChain (Ov B) (i :: l) ∧ lastOf i l = j :=
  List.exists_isChain_cons_of_relationReflTransGen (reach_of_cover hX hopen hsub hcov hne i j)

theorem disj_subset (B : ℕ → Set ℂ) (j : ℕ) : disj B j ⊆ B j := fun _ hx => hx.1

theorem disj_measurable {B : ℕ → Set ℂ} (hopen : ∀ j, IsOpen (B j)) (j : ℕ) :
    MeasurableSet (disj B j) :=
  (hopen j).measurableSet.diff
    (MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ => (hopen i).measurableSet)

theorem disj_pairwise (B : ℕ → Set ℂ) : Pairwise (Disjoint on disj B) := by
  intro j k hjk
  show Disjoint (disj B j) (disj B k)
  rcases lt_or_gt_of_ne hjk with h | h
  · refine Set.disjoint_left.2 fun z hzj hzk => ?_
    exact hzk.2 (Set.mem_iUnion₂.2 ⟨j, h, hzj.1⟩)
  · refine Set.disjoint_left.2 fun z hzj hzk => ?_
    exact hzj.2 (Set.mem_iUnion₂.2 ⟨k, h, hzk.1⟩)

theorem iUnion_disj (B : ℕ → Set ℂ) : ⋃ j, disj B j = ⋃ j, B j := by
  apply subset_antisymm
  · exact iUnion_mono fun j => disj_subset B j
  · intro z hz
    classical
    have hex : ∃ j, z ∈ B j := Set.mem_iUnion.1 hz
    refine Set.mem_iUnion.2 ⟨Nat.find hex, ⟨Nat.find_spec hex, fun h => ?_⟩⟩
    obtain ⟨i, hi, hzi⟩ := Set.mem_iUnion₂.1 h
    exact Nat.find_min hex hi hzi

/-- The patched measure `Σ_j ρ_j • ν_j.restrict (disj B j)`, with `ρ_j` the chain product of the ratios `R` along the
chain `L j` from `i₀`. -/
def patchMeasure (B : ℕ → Set ℂ) (ν : ℕ → Measure ℂ) (R : ℕ → ℕ → ℝ≥0∞) (L : ℕ → List ℕ) (i₀ : ℕ) :
    Measure ℂ :=
  Measure.sum fun j => chainScale R i₀ (L j) • (ν j).restrict (disj B j)

/-- Patch identity: if `ν j = c j • μ.restrict (B j)` and the ratios satisfy `R a b * c b = c a` on the overlaps, the
patched measure is `c i₀ • μ.restrict X`. No finiteness or positivity of `μ` is needed here: it is absorbed in `R`. -/
theorem patchMeasure_eq {X : Set ℂ} {B : ℕ → Set ℂ} (hopen : ∀ j, IsOpen (B j)) (hsub : ∀ j, B j ⊆ X)
    (hcov : X ⊆ ⋃ j, B j) (μ : Measure ℂ) (c : ℕ → ℝ≥0∞) (ν : ℕ → Measure ℂ)
    (hν : ∀ j, ν j = c j • μ.restrict (B j)) (R : ℕ → ℕ → ℝ≥0∞) (hR : ∀ a b, Ov B a b → R a b * c b = c a)
    (i₀ : ℕ) (L : ℕ → List ℕ) (hL : ∀ j, List.IsChain (Ov B) (i₀ :: L j) ∧ lastOf i₀ (L j) = j) :
    patchMeasure B ν R L i₀ = c i₀ • μ.restrict X := by
  have hpiece : ∀ j, chainScale R i₀ (L j) • (ν j).restrict (disj B j) = c i₀ • μ.restrict (disj B j) := by
    intro j
    have hchain := chainScale_mul_last B R c hR i₀ (L j) (hL j).1
    rw [(hL j).2] at hchain
    rw [hν j, Measure.restrict_smul, Measure.restrict_restrict (disj_measurable hopen j),
      Set.inter_eq_left.2 (disj_subset B j), smul_smul, hchain]
  have hunion : ⋃ j, disj B j = X := by
    rw [iUnion_disj]; exact subset_antisymm (iUnion_subset hsub) hcov
  unfold patchMeasure
  calc (Measure.sum fun j => chainScale R i₀ (L j) • (ν j).restrict (disj B j))
      = Measure.sum fun j => c i₀ • μ.restrict (disj B j) := by
        congr 1; funext j; exact hpiece j
    _ = c i₀ • Measure.sum fun j => μ.restrict (disj B j) := by
        ext s hs
        rw [Measure.smul_apply, Measure.sum_apply _ hs, Measure.sum_apply _ hs]
        simp only [Measure.smul_apply, smul_eq_mul, ENNReal.tsum_mul_left]
    _ = c i₀ • μ.restrict X := by
        rw [← hunion, Measure.restrict_iUnion (disj_pairwise B) (disj_measurable hopen)]

/-- Evaluation of the patched measure on a measurable set (used for measurability in the observation). -/
theorem patchMeasure_apply (B : ℕ → Set ℂ) (ν : ℕ → Measure ℂ) (R : ℕ → ℕ → ℝ≥0∞) (L : ℕ → List ℕ) (i₀ : ℕ)
    {s : Set ℂ} (hs : MeasurableSet s) :
    patchMeasure B ν R L i₀ s = ∑' j, chainScale R i₀ (L j) * ν j (s ∩ disj B j) := by
  unfold patchMeasure
  rw [Measure.sum_apply _ hs]
  refine tsum_congr fun j => ?_
  rw [Measure.smul_apply, Measure.restrict_apply hs, smul_eq_mul]

end HarmonicBalls.S11m.PatchOpen

end

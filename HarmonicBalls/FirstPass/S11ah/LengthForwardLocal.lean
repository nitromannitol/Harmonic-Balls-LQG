import Mathlib
import HarmonicBalls.FirstPass.S11ah.LengthBorelClauses
import HarmonicBalls.FirstPass.S11ah.LengthTransport
import HarmonicBalls.FirstPass.S11ah.LQGDecoder
import HarmonicBalls.FirstPass.S11r.RootedTriangle

/-!
# Uniform near-geodesics in a length metric (B1, forward implication, owner n3)

Ruling chat 236, section 6 (forward implication, `uniform_compact_near_geodesics`). Let `D` be a length
metric on the open set `B` (`IsLengthMetricOn B D`), and let `K ⊆ B` be compact. For `η > 0` there is a
compact `K' ⊆ B` such that any two points `a, b ∈ K` are joined by a path in `K'` with
`pathLength D P ≤ ofReal (D a b + 7η)`.

Proof. For each `p ∈ B` a small Euclidean ball `ball p (θ p)` has the property that `D`-almost-geodesics
from `a` to `p` (or from `p` to `a`) with `a` in that ball stay in the closed ball `closedBall p (δ p)`,
which is compact in `B` (the `V2` condition gives the containment). Cover `K` by finitely many such balls
and join any two centres by a path in `B` of length `≤ D + η`; `K'` is the finite union of the local
closed balls and of the ranges of these paths. Concatenate the three pieces.
-/

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal
noncomputable section

namespace HarmonicBalls.FirstPassS11ahLengthForwardLocal

open HarmonicBalls.FirstPassS11ahLengthBorelClauses FirstPassS11ah HarmonicBalls

/-- **Subpoint bound.** For a path `P` and parameters `s ≤ t`, `D(P t, P s) ≤ pathLength D P`. -/
lemma ofReal_le_pathLength_sub {D : ℂ → ℂ → ℝ} {x y : ℂ} (P : Path x y) {s t : unitInterval}
    (hst : s ≤ t) : ENNReal.ofReal (D (P t) (P s)) ≤ pathLength D P := by
  unfold pathLength curveLength
  have hmem : ∀ i : ℕ, (if i = 0 then (s : ℝ) else (t : ℝ)) ∈ Icc (0 : ℝ) 1 := fun i => by
    split_ifs
    · exact s.2
    · exact t.2
  have hmono : Monotone (fun i : ℕ => if i = 0 then (s : ℝ) else (t : ℝ)) := by
    intro i j hij
    dsimp only
    have hst' : (s : ℝ) ≤ t := hst
    split_ifs <;> first | exact le_rfl | exact hst' | omega
  refine le_iSup_of_le (1, ⟨fun i : ℕ => if i = 0 then (s : ℝ) else (t : ℝ), hmono, hmem⟩) ?_
  rw [Finset.sum_range_one]
  apply le_of_eq
  congr 1
  simp [Path.extend_extends' P t, Path.extend_extends' P s]

/-- `V2` from the length property. -/
lemma V2_of_isLengthMetricOn {B : Set ℂ} {D : ℂ → ℂ → ℝ} (hB : IsOpen B)
    (hD : IsLengthMetricOn B D) : V2 B D :=
  (isOpen_iff_of_V2 hB hD.continuousOn hD.self_eq_zero).1 hD.isOpen_iff

/-- Small values of `D (p, ·)` near `p` (continuity at `(p, p)`). -/
lemma small_near_of_continuousOn {B : Set ℂ} {D : ℂ → ℂ → ℝ}
    (hcont : ContinuousOn (fun q : ℂ × ℂ => D q.1 q.2) (B ×ˢ B))
    (hself : ∀ z ∈ B, D z z = 0) {p : ℂ} (hp : p ∈ B) {e : ℝ} (he : 0 < e) :
    ∃ θ > 0, ∀ a ∈ B, dist a p < θ → D p a < e := by
  have hc := hcont (p, p) ⟨hp, hp⟩
  rw [Metric.continuousWithinAt_iff] at hc
  obtain ⟨θ, hθ, hθ'⟩ := hc e he
  refine ⟨θ, hθ, fun a ha hd => ?_⟩
  have hdist : dist ((p, a) : ℂ × ℂ) (p, p) < θ := by
    rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg]
    exact hd
  have h := hθ' (x := (p, a)) ⟨hp, ha⟩ hdist
  rw [hself p hp, Real.dist_eq, sub_zero] at h
  exact lt_of_le_of_lt (le_abs_self _) h

/-- A path from `z` to `w` in `B` with length at most `D z w + ρ` (from the length property). -/
lemma exists_path_in_of_isLengthMetricOn {B : Set ℂ} {D : ℂ → ℂ → ℝ} (hD : IsLengthMetricOn B D)
    {p p' : ℂ} (hp : p ∈ B) (hp' : p' ∈ B) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ γ : Path p p', (∀ t, γ t ∈ B) ∧ pathLength D γ ≤ ENNReal.ofReal (D p p' + ρ) := by
  have h1 : ENNReal.ofReal (D p p') < ENNReal.ofReal (D p p' + ρ) :=
    (ENNReal.ofReal_lt_ofReal_iff (by linarith [hD.nonneg hp hp'])).2 (by linarith)
  rw [hD.ofReal_eq_internalMetric p hp p' hp'] at h1
  unfold internalMetric at h1
  obtain ⟨γ, hγ⟩ := iInf_lt_iff.1 h1
  obtain ⟨hγB, hγL⟩ := iInf_lt_iff.1 hγ
  exact ⟨γ, hγB, le_of_lt hγL⟩

/-- **Local data.** Near `p ∈ B`: a closed ball `closedBall p δ ⊆ B` and a radius `θ` such that every
`a` within `θ` of `p` is joined to `p` (in both directions) by paths inside `closedBall p δ`, of length at
most `D(·,·) + ρ`, with `D a p < ρ` and `D p a < ρ`. -/
lemma local_data {B : Set ℂ} {D : ℂ → ℂ → ℝ} (hB : IsOpen B) (hD : IsLengthMetricOn B D)
    {p : ℂ} (hp : p ∈ B) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ δ > 0, ∃ θ > 0, closedBall p δ ⊆ B ∧ ∀ a ∈ B, dist a p < θ →
      D a p < ρ ∧ D p a < ρ ∧
      (∃ α : Path a p, (∀ t, α t ∈ closedBall p δ) ∧
        pathLength D α ≤ ENNReal.ofReal (D a p + ρ)) ∧
      (∃ β : Path p a, (∀ t, β t ∈ closedBall p δ) ∧
        pathLength D β ≤ ENNReal.ofReal (D p a + ρ)) := by
  obtain ⟨δ0, hδ0, hball⟩ := Metric.isOpen_iff.1 hB p hp
  have hV := V2_of_isLengthMetricOn hB hD
  obtain ⟨e, he, hVe⟩ := hV p hp (δ0 / 2) (half_pos hδ0)
  have hcl : closedBall p (δ0 / 2) ⊆ B :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  set ρ0 := min ρ (e / 4) with hρ0def
  have hρ0 : 0 < ρ0 := lt_min hρ (by linarith)
  obtain ⟨θ, hθ, hθD⟩ := small_near_of_continuousOn hD.continuousOn hD.self_eq_zero hp hρ0
  refine ⟨δ0 / 2, half_pos hδ0, θ, hθ, hcl, fun a ha hd => ?_⟩
  have hpD : D p a < ρ0 := hθD a ha hd
  have haD : D a p < ρ0 := by rw [hD.symm a ha p hp]; exact hpD
  -- the path from `a` to `p`
  have hlt : ENNReal.ofReal (D a p) < ENNReal.ofReal (D a p + ρ0) :=
    (ENNReal.ofReal_lt_ofReal_iff (by linarith [hD.nonneg ha hp, hρ0])).2 (by linarith)
  have hlt' := hlt
  rw [hD.ofReal_eq_internalMetric a ha p hp] at hlt'
  unfold internalMetric at hlt'
  obtain ⟨α, hα⟩ := iInf_lt_iff.1 hlt'
  obtain ⟨hαB, hαL⟩ := iInf_lt_iff.1 hα
  have hαmem : ∀ t, α t ∈ closedBall p (δ0 / 2) := by
    intro t
    have ht1 : t ≤ (1 : unitInterval) := Subtype.coe_le_coe.1 t.2.2
    have h1 := ofReal_le_pathLength_sub (D := D) α (s := t) (t := 1) ht1
    rw [α.target] at h1
    have h2 : ENNReal.ofReal (D p (α t)) < ENNReal.ofReal (D a p + ρ0) :=
      lt_of_le_of_lt h1 hαL
    have h3 : D p (α t) < D a p + ρ0 := (ENNReal.ofReal_lt_ofReal_iff'.1 h2).1
    rw [mem_closedBall]
    by_contra hfar
    have hfar' : δ0 / 2 ≤ dist (α t) p := (not_le.1 hfar).le
    have h4 := hVe (α t) (hαB t) hfar'
    have h5 : D p (α t) < e := by
      have : D p (α t) < 2 * ρ0 := by linarith
      have : 2 * ρ0 ≤ e / 2 := by
        have := min_le_right ρ (e / 4)
        rw [← hρ0def] at this
        linarith
      linarith
    linarith
  -- the path from `p` to `a`
  have hlt2 : ENNReal.ofReal (D p a) < ENNReal.ofReal (D p a + ρ0) :=
    (ENNReal.ofReal_lt_ofReal_iff (by linarith [hD.nonneg hp ha, hρ0])).2 (by linarith)
  have hlt2' := hlt2
  rw [hD.ofReal_eq_internalMetric p hp a ha] at hlt2'
  unfold internalMetric at hlt2'
  obtain ⟨β, hβ⟩ := iInf_lt_iff.1 hlt2'
  obtain ⟨hβB, hβL⟩ := iInf_lt_iff.1 hβ
  have hβmem : ∀ t, β t ∈ closedBall p (δ0 / 2) := by
    intro t
    have h0t : (0 : unitInterval) ≤ t := Subtype.coe_le_coe.1 t.2.1
    have h1 := ofReal_le_pathLength_sub (D := D) β (s := 0) (t := t) h0t
    rw [β.source] at h1
    have h2 : ENNReal.ofReal (D (β t) p) < ENNReal.ofReal (D p a + ρ0) :=
      lt_of_le_of_lt h1 hβL
    have h3 : D (β t) p < D p a + ρ0 := (ENNReal.ofReal_lt_ofReal_iff'.1 h2).1
    rw [mem_closedBall]
    by_contra hfar
    have hfar' : δ0 / 2 ≤ dist (β t) p := (not_le.1 hfar).le
    have h4 := hVe (β t) (hβB t) hfar'
    have h5 : D p (β t) < e := by
      rw [hD.symm p hp (β t) (hβB t)]
      have : D (β t) p < 2 * ρ0 := by linarith
      have : 2 * ρ0 ≤ e / 2 := by
        have := min_le_right ρ (e / 4)
        rw [← hρ0def] at this
        linarith
      linarith
    linarith
  have hρle : ρ0 ≤ ρ := min_le_left _ _
  refine ⟨lt_of_lt_of_le haD hρle, lt_of_lt_of_le hpD hρle, ⟨α, hαmem, ?_⟩, ⟨β, hβmem, ?_⟩⟩
  · exact le_trans hαL.le (ENNReal.ofReal_le_ofReal (by linarith))
  · exact le_trans hβL.le (ENNReal.ofReal_le_ofReal (by linarith))

/-! ### The uniform compact set of near-geodesics -/

lemma mem_trans_of {S : Set ℂ} {x y z : ℂ} {P : Path x y} {Q : Path y z}
    (hP : ∀ t, P t ∈ S) (hQ : ∀ t, Q t ∈ S) : ∀ t, (P.trans Q) t ∈ S := by
  intro t
  rw [Path.trans_apply]
  split_ifs
  · exact hP _
  · exact hQ _

/-- **Uniform near-geodesics** (ruling 236, section 6, `uniform_compact_near_geodesics`). For a compact
`K ⊆ B` and `ρ > 0` there is a compact `K' ⊆ B` such that any `a, b ∈ K` are joined by a path in `K'` of
`D`-length at most `D a b + 7ρ`. `hgs` is the global symmetry of `D` (true for `decoderOn B d`). -/
theorem uniform_near_geodesics {B : Set ℂ} {D : ℂ → ℂ → ℝ} (hB : IsOpen B)
    (hD : IsLengthMetricOn B D) (hgs : ∀ x y, D x y = D y x) {K : Set ℂ} (hK : IsCompact K)
    (hKB : K ⊆ B) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ K' : Set ℂ, IsCompact K' ∧ K' ⊆ B ∧ ∀ a ∈ K, ∀ b ∈ K, ∃ P : Path a b,
      (∀ t, P t ∈ K') ∧ pathLength D P ≤ ENNReal.ofReal (D a b + 7 * ρ) := by
  have hloc : ∀ p ∈ B, ∃ δ > 0, ∃ θ > 0, closedBall p δ ⊆ B ∧ ∀ a ∈ B, dist a p < θ →
      D a p < ρ ∧ D p a < ρ ∧
      (∃ α : Path a p, (∀ t, α t ∈ closedBall p δ) ∧
        pathLength D α ≤ ENNReal.ofReal (D a p + ρ)) ∧
      (∃ β : Path p a, (∀ t, β t ∈ closedBall p δ) ∧
        pathLength D β ≤ ENNReal.ofReal (D p a + ρ)) :=
    fun p hp => local_data hB hD hp hρ
  choose! δ hδ θ hθ hcl hloc' using hloc
  obtain ⟨T, hTK, hcover⟩ := hK.elim_nhds_subcover (fun p => ball p (θ p))
    (fun p hp => ball_mem_nhds p (hθ p (hKB hp)))
  have hTB : ∀ p ∈ T, p ∈ B := fun p hp => hKB (hTK p hp)
  have hpair : ∀ p ∈ B, ∀ p' ∈ B, ∃ S : Set ℂ, IsCompact S ∧ S ⊆ B ∧
      ∃ γ : Path p p', (∀ t, γ t ∈ S) ∧ pathLength D γ ≤ ENNReal.ofReal (D p p' + ρ) := by
    intro p hp p' hp'
    obtain ⟨γ, hγB, hγL⟩ := exists_path_in_of_isLengthMetricOn hD hp hp' hρ
    exact ⟨range γ, isCompact_range γ.continuous, by rintro _ ⟨t, rfl⟩; exact hγB t, γ,
      fun t => ⟨t, rfl⟩, hγL⟩
  choose! S hS using hpair
  set K' : Set ℂ := (⋃ p ∈ T, closedBall p (δ p)) ∪ ⋃ p ∈ T, ⋃ p' ∈ T, S p p' with hK'def
  have hK'c : IsCompact K' :=
    (T.isCompact_biUnion fun p _ => isCompact_closedBall p (δ p)).union
      (T.isCompact_biUnion fun p hp => T.isCompact_biUnion fun p' hp' =>
        (hS p (hTB p hp) p' (hTB p' hp')).1)
  have hK'B : K' ⊆ B :=
    union_subset (iUnion₂_subset fun p hp => hcl p (hTB p hp))
      (iUnion₂_subset fun p hp => iUnion₂_subset fun p' hp' => (hS p (hTB p hp) p' (hTB p' hp')).2.1)
  refine ⟨K', hK'c, hK'B, fun a ha b hb => ?_⟩
  obtain ⟨p, hpT, hap⟩ := mem_iUnion₂.1 (hcover ha)
  obtain ⟨p', hp'T, hbp⟩ := mem_iUnion₂.1 (hcover hb)
  have haB : a ∈ B := hKB ha
  have hbB : b ∈ B := hKB hb
  have hpB : p ∈ B := hTB p hpT
  have hp'B : p' ∈ B := hTB p' hp'T
  obtain ⟨haD, -, ⟨α, hαK, hαL⟩, -⟩ := hloc' p hpB a haB (mem_ball.1 hap)
  obtain ⟨-, hbD, -, ⟨β, hβK, hβL⟩⟩ := hloc' p' hp'B b hbB (mem_ball.1 hbp)
  obtain ⟨-, -, γ, hγK, hγL⟩ := hS p hpB p' hp'B
  have hαK' : ∀ t, α t ∈ K' := fun t => Or.inl (mem_iUnion₂.2 ⟨p, hpT, hαK t⟩)
  have hβK' : ∀ t, β t ∈ K' := fun t => Or.inl (mem_iUnion₂.2 ⟨p', hp'T, hβK t⟩)
  have hγK' : ∀ t, γ t ∈ K' := fun t => Or.inr (mem_iUnion₂.2 ⟨p, hpT,
    mem_iUnion₂.2 ⟨p', hp'T, hγK t⟩⟩)
  have hsub : ∀ t, (α.trans (γ.trans β)) t ∈ K' := mem_trans_of hαK' (mem_trans_of hγK' hβK')
  refine ⟨α.trans (γ.trans β), hsub, ?_⟩
  have hαB : ∀ t, α t ∈ B := fun t => hK'B (hαK' t)
  have hγB : ∀ t, γ t ∈ B := fun t => hK'B (hγK' t)
  have hβB : ∀ t, β t ∈ B := fun t => hK'B (hβK' t)
  have hγβB : ∀ t, (γ.trans β) t ∈ B := fun t => hK'B (mem_trans_of hγK' hβK' t)
  have h1 : pathLength D (α.trans (γ.trans β)) ≤ pathLength D α + pathLength D (γ.trans β) :=
    pathLength_trans_le_of_symm D hgs hD.self_eq_zero hD.triangle α (γ.trans β) hαB hγβB
  have h2 : pathLength D (γ.trans β) ≤ pathLength D γ + pathLength D β :=
    pathLength_trans_le_of_symm D hgs hD.self_eq_zero hD.triangle γ β hγB hβB
  have hnn1 : 0 ≤ D a p := hD.nonneg haB hpB
  have hnn3 : 0 ≤ D p' b := hD.nonneg hp'B hbB
  have hsymA : D p a = D a p := hD.symm p hpB a haB
  have hsymB : D b p' = D p' b := hD.symm b hbB p' hp'B
  have htri1 : D p p' ≤ D p a + D a p' := hD.triangle p hpB a haB p' hp'B
  have htri2 : D a p' ≤ D a b + D b p' := hD.triangle a haB b hbB p' hp'B
  have hX : 0 ≤ D a p + ρ := by linarith
  have hY : 0 ≤ D p p' + ρ := by linarith [hD.nonneg hpB hp'B]
  have hZ : 0 ≤ D p' b + ρ := by linarith
  calc pathLength D (α.trans (γ.trans β))
      ≤ pathLength D α + (pathLength D γ + pathLength D β) := h1.trans (add_le_add le_rfl h2)
    _ ≤ ENNReal.ofReal (D a p + ρ) + (ENNReal.ofReal (D p p' + ρ) + ENNReal.ofReal (D p' b + ρ)) :=
        add_le_add hαL (add_le_add hγL hβL)
    _ = ENNReal.ofReal ((D a p + ρ) + ((D p p' + ρ) + (D p' b + ρ))) := by
        rw [ENNReal.ofReal_add hX (add_nonneg hY hZ), ENNReal.ofReal_add hY hZ]
    _ ≤ ENNReal.ofReal (D a b + 7 * ρ) := by
        apply ENNReal.ofReal_le_ofReal
        linarith

end HarmonicBalls.FirstPassS11ahLengthForwardLocal

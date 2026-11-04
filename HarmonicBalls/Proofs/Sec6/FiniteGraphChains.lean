import HarmonicBalls.Proofs.Sec6.ConnectedAnnulusCover

/-! # Uniform chains in a finite connected graph -/

namespace HarmonicBalls.Section6

/-- A reflexive transitive graph path can be indexed by a finite initial
segment of the natural numbers. -/
theorem exists_nat_chain_of_reflTransGen {α : Type*} {r : α → α → Prop} {a b : α}
    (h : Relation.ReflTransGen r a b) :
    ∃ n : ℕ, ∃ p : ℕ → α, p 0 = a ∧ p n = b ∧ ∀ i < n, r (p i) (p (i + 1)) := by
  induction h with
  | refl => exact ⟨0, fun _ => a, rfl, rfl, by simp⟩
  | @tail b c hab hbc ih =>
    obtain ⟨n, p, hp0, hpn, hstep⟩ := ih
    let q : ℕ → α := fun i => if i ≤ n then p i else c
    refine ⟨n + 1, q, ?_, ?_, ?_⟩
    · simpa [q] using hp0
    · simp [q]
    · intro i hi
      by_cases hin : i < n
      · have hi1 : i + 1 ≤ n := by omega
        simpa [q, Nat.le_of_lt hin, hi1] using hstep i hin
      · have hie : i = n := by omega
        subst i
        simpa [q, hpn] using hbc

/-- In a finite connected reflexive graph, paths between all pairs can be
chosen to have one common length. -/
theorem exists_uniform_nat_chain_of_finite {α : Type*} [Finite α]
    (r : α → α → Prop) (hrefl : ∀ x, r x x)
    (hconn : ∀ x y, Relation.ReflTransGen r x y) :
    ∃ N : ℕ, ∀ a b, ∃ p : ℕ → α,
      p 0 = a ∧ p N = b ∧ ∀ i < N, r (p i) (p (i + 1)) := by
  classical
  let : Fintype α := Fintype.ofFinite α
  let P : α × α → ℕ → Prop := fun ab n => ∃ p : ℕ → α,
    p 0 = ab.1 ∧ p n = ab.2 ∧ ∀ i < n, r (p i) (p (i + 1))
  have hex : ∀ ab, ∃ n, P ab n := fun ab => exists_nat_chain_of_reflTransGen (hconn ab.1 ab.2)
  let N := Finset.univ.sup (fun ab : α × α => Nat.find (hex ab))
  refine ⟨N, ?_⟩
  intro a b
  let n := Nat.find (hex (a, b))
  have hnN : n ≤ N := Finset.le_sup (f := fun ab : α × α => Nat.find (hex ab)) (Finset.mem_univ (a, b))
  obtain ⟨p, hp0, hpn, hstep⟩ := Nat.find_spec (hex (a, b))
  let q : ℕ → α := fun i => p (min i n)
  refine ⟨q, ?_, ?_, ?_⟩
  · simpa [q] using hp0
  · simpa [q, min_eq_right hnN] using hpn
  · intro i hi
    by_cases hin : i < n
    · have hi1 : i + 1 ≤ n := by omega
      simpa [q, min_eq_left (Nat.le_of_lt hin), min_eq_left hi1] using hstep i hin
    · have hni : n ≤ i := by omega
      simpa [q, min_eq_right hni, min_eq_right (le_trans hni (Nat.le_succ i))] using hrefl (p n)

/-- A connected finite annulus-cover graph admits a common path length for
all pairs of its centres. -/
theorem exists_uniform_middle_annulus_cover_graph {s₁ s₂ s₃ s₄ : ℝ}
    (h1 : 0 < s₁) (h12 : s₁ < s₂) (h23 : s₂ < s₃) (h34 : s₃ < s₄) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ T : Set ℂ, T.Finite ∧ T ⊆ annulus 0 s₂ s₃ ∧
      annulus 0 s₂ s₃ ⊆ ⋃ x ∈ T, Metric.ball x δ ∧
      (∀ x ∈ T, Metric.closedBall x (2 * δ) ⊆ annulus 0 s₁ s₄) ∧
      ∃ N : ℕ, ∀ x ∈ T, ∀ y ∈ T, ∃ p : ℕ → ℂ,
        p 0 = x ∧ p N = y ∧
        ∀ i < N, p i ∈ T ∧ p (i + 1) ∈ T ∧
          (Metric.ball (p i) δ ∩ Metric.ball (p (i + 1)) δ).Nonempty := by
  obtain ⟨δ, hδ, T, hfin, hsub, hcover, hdisc, hgraph⟩ :=
    exists_connected_middle_annulus_cover h1 h12 h23 h34
  let : Finite T := hfin.to_subtype
  let r : T → T → Prop := fun x y => (Metric.ball x.1 δ ∩ Metric.ball y.1 δ).Nonempty
  have hrefl : ∀ x, r x x := fun x => ⟨x.1, Metric.mem_ball_self hδ, Metric.mem_ball_self hδ⟩
  have hconn : ∀ x y : T, Relation.ReflTransGen r x y := by
    intro x y
    have haux {a b : ℂ} (ha : a ∈ T)
        (h : Relation.ReflTransGen
          (fun a b : ℂ => (Metric.ball a δ ∩ Metric.ball b δ).Nonempty ∧ a ∈ T ∧ b ∈ T) a b) :
        ∃ hb : b ∈ T, Relation.ReflTransGen r ⟨a, ha⟩ ⟨b, hb⟩ := by
      induction h with
      | refl => exact ⟨ha, Relation.ReflTransGen.refl⟩
      | @tail b c hab hbc ih =>
        obtain ⟨hb, hp⟩ := ih
        exact ⟨hbc.2.2, hp.tail hbc.1⟩
    obtain ⟨_, hp⟩ := haux x.2 (hgraph x.1 x.2 y.1 y.2)
    exact hp
  obtain ⟨N, hN⟩ := exists_uniform_nat_chain_of_finite r hrefl hconn
  refine ⟨δ, hδ, T, hfin, hsub, hcover, hdisc, N, ?_⟩
  intro x hx y hy
  obtain ⟨p, hp0, hpN, hstep⟩ := hN ⟨x, hx⟩ ⟨y, hy⟩
  refine ⟨fun i => (p i).1, ?_, ?_, ?_⟩
  · simpa using congrArg Subtype.val hp0
  · simpa using congrArg Subtype.val hpN
  · intro i hi
    exact ⟨(p i).2, (p (i + 1)).2, hstep i hi⟩

end HarmonicBalls.Section6

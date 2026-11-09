import HarmonicBalls.Defs.LQGMetric

/-!
# Crossing and chaining for an ambient length metric (Lemma 11.13, step 4)

For an ambient metric `D` which is a length metric (`IsEuclideanLengthMetric`, `HarmonicBalls/Defs/LQGMetric.lean`),
two deterministic facts used in step 4 of `notes/fp-gaps/CHATGPT-11-13-proof.md`:

* `crossing_dist_ge`: a path from `z` to a point at distance `R` from `z` crosses the circles of radii
  `r₁ < r₂ < r₃ < R`, so `D(z, x)` is at least the sum of the three successive sphere distances
  (`D(z, ∂B_{r₁}) + D(∂B_{r₁}, ∂B_{r₂}) + D(∂B_{r₂}, ∂B_{r₃})`, Euclidean-annular crossings);
* `ofReal_dist_le_chain`: the diameter of a union of three sets chained through two intersection points is at most
  the sum of the three diameters (the joining argument `diam_D(T) ≤ d₀ + d₂ + d₁`).

Only the length-metric axioms are used; no property of the LQG field enters.
-/

open Metric Set
open scoped ENNReal

namespace FirstPassS11i

open HarmonicBalls

variable {D : ℂ → ℂ → ℝ}

lemma dist_nonneg_of_lengthMetric (hD : IsEuclideanLengthMetric D) (z w : ℂ) : 0 ≤ D z w := by
  have h := hD.triangle z w z
  rw [hD.self_eq_zero, hD.symm w z] at h
  linarith

/-- `D(A, B) ≤ D(x, y)` for `x ∈ A`, `y ∈ B`. -/
lemma setDist_le_of_mem (hD : IsEuclideanLengthMetric D) {A B : Set ℂ} {x y : ℂ} (hx : x ∈ A) (hy : y ∈ B) :
    setDist D A B ≤ D x y := by
  unfold setDist
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro _ ⟨a, -, b, -, rfl⟩
    exact dist_nonneg_of_lengthMetric hD a b
  · exact mem_image2_of_mem hx hy

/-- `D(A, B) ≤ D(y, x)` for `x ∈ A`, `y ∈ B` (symmetry of `D`). -/
lemma setDist_le_of_mem' (hD : IsEuclideanLengthMetric D) {A B : Set ℂ} {x y : ℂ} (hx : x ∈ A) (hy : y ∈ B) :
    setDist D A B ≤ D y x := by
  rw [hD.symm]
  exact setDist_le_of_mem hD hx hy

/-- A lower bound for `D(A, B)` by a constant bounding all pairs. -/
lemma le_setDist_of_forall {A B : Set ℂ} {c : ℝ} (hA : A.Nonempty) (hB : B.Nonempty)
    (h : ∀ x ∈ A, ∀ y ∈ B, c ≤ D x y) : c ≤ setDist D A B := by
  unfold setDist
  apply le_csInf (hA.image2 hB)
  rintro _ ⟨x, hx, y, hy, rfl⟩
  exact h x hx y hy

lemma setDist_nonneg (hD : IsEuclideanLengthMetric D) {A B : Set ℂ} (hA : A.Nonempty) (hB : B.Nonempty) :
    0 ≤ setDist D A B :=
  le_setDist_of_forall hA hB (fun x _ y _ => dist_nonneg_of_lengthMetric hD x y)

/-- Partition lower bound for the `D`-length of a curve. -/
lemma sum_le_curveLength (p : ℝ → ℂ) {a b : ℝ} (n : ℕ) (u : ℕ → ℝ) (hu : Monotone u)
    (hmem : ∀ i, u i ∈ Icc a b) :
    ∑ i ∈ Finset.range n, ENNReal.ofReal (D (p (u (i + 1))) (p (u i))) ≤ curveLength D p a b :=
  le_iSup_of_le (n, ⟨u, hu, hmem⟩) le_rfl

/-- Intermediate value theorem for the distance to a centre along a path. -/
lemma ivt_dist_path {z x : ℂ} (P : Path z x) {a b c : ℝ} (hab : a ≤ b) (h₁ : dist (P.extend a) z ≤ c)
    (h₂ : c ≤ dist (P.extend b) z) : ∃ t ∈ Icc a b, dist (P.extend t) z = c := by
  have hg : Continuous fun t => dist (P.extend t) z := P.continuous_extend.dist continuous_const
  exact intermediate_value_Icc hab hg.continuousOn ⟨h₁, h₂⟩

/-- Crossing lower bound on one path: the `D`-length of a path from `z` to `x` with `dist x z = R` dominates the
three successive sphere distances for `r₁ < r₂ < r₃ < R`. -/
lemma crossing_pathLength_ge (hD : IsEuclideanLengthMetric D) {z x : ℂ} (P : Path z x) {r₁ r₂ r₃ R : ℝ}
    (h₀ : 0 < r₁) (h₁₂ : r₁ < r₂) (h₂₃ : r₂ < r₃) (h₃R : r₃ < R) (hx : dist x z = R) :
    ENNReal.ofReal (setDist D {z} (sphere z r₁) + setDist D (sphere z r₁) (sphere z r₂)
        + setDist D (sphere z r₂) (sphere z r₃)) ≤ pathLength D P := by
  have e0 : dist (P.extend 0) z = 0 := by rw [Path.extend_zero, dist_self]
  have e1 : dist (P.extend 1) z = R := by rw [Path.extend_one, hx]
  obtain ⟨t₁, ⟨ht₁a, ht₁b⟩, f₁⟩ := ivt_dist_path (c := r₁) P zero_le_one (by rw [e0]; exact h₀.le)
    (by rw [e1]; linarith)
  obtain ⟨t₂, ⟨ht₂a, ht₂b⟩, f₂⟩ := ivt_dist_path (c := r₂) P ht₁b (by rw [f₁]; linarith) (by rw [e1]; linarith)
  obtain ⟨t₃, ⟨ht₃a, ht₃b⟩, f₃⟩ := ivt_dist_path (c := r₃) P ht₂b (by rw [f₂]; linarith) (by rw [e1]; linarith)
  obtain ⟨u, hu_def⟩ : ∃ u : ℕ → ℝ, ∀ i, u i =
      if i = 0 then 0 else if i = 1 then t₁ else if i = 2 then t₂ else if i = 3 then t₃ else 1 :=
    ⟨_, fun i => rfl⟩
  have hmono : Monotone u := by
    refine monotone_nat_of_le_succ (fun n => ?_)
    rcases n with _ | _ | _ | _ | n <;> simp [hu_def] <;> linarith
  have hmem : ∀ i, u i ∈ Icc (0 : ℝ) 1 := by
    intro i
    rw [hu_def, Set.mem_Icc]
    split_ifs <;> constructor <;> linarith
  have hsum := sum_le_curveLength (D := D) P.extend 4 u hmono hmem
  norm_num [Finset.sum_range_succ, hu_def, Path.extend_zero, Path.extend_one] at hsum
  have b0 : setDist D {z} (sphere z r₁) ≤ D (P.extend t₁) z :=
    setDist_le_of_mem' hD (mem_singleton z) (mem_sphere.mpr f₁)
  have b1 : setDist D (sphere z r₁) (sphere z r₂) ≤ D (P.extend t₂) (P.extend t₁) :=
    setDist_le_of_mem' hD (mem_sphere.mpr f₁) (mem_sphere.mpr f₂)
  have b2 : setDist D (sphere z r₂) (sphere z r₃) ≤ D (P.extend t₃) (P.extend t₂) :=
    setDist_le_of_mem' hD (mem_sphere.mpr f₂) (mem_sphere.mpr f₃)
  unfold pathLength
  calc ENNReal.ofReal (setDist D {z} (sphere z r₁) + setDist D (sphere z r₁) (sphere z r₂)
          + setDist D (sphere z r₂) (sphere z r₃))
      ≤ ENNReal.ofReal (setDist D {z} (sphere z r₁) + setDist D (sphere z r₁) (sphere z r₂))
          + ENNReal.ofReal (setDist D (sphere z r₂) (sphere z r₃)) := ENNReal.ofReal_add_le
    _ ≤ (ENNReal.ofReal (setDist D {z} (sphere z r₁)) + ENNReal.ofReal (setDist D (sphere z r₁) (sphere z r₂)))
          + ENNReal.ofReal (setDist D (sphere z r₂) (sphere z r₃)) :=
        add_le_add ENNReal.ofReal_add_le le_rfl
    _ ≤ (ENNReal.ofReal (D (P.extend t₁) z) + ENNReal.ofReal (D (P.extend t₂) (P.extend t₁)))
          + ENNReal.ofReal (D (P.extend t₃) (P.extend t₂)) :=
        add_le_add (add_le_add (ENNReal.ofReal_le_ofReal b0) (ENNReal.ofReal_le_ofReal b1))
          (ENNReal.ofReal_le_ofReal b2)
    _ ≤ _ := le_self_add.trans hsum

/-- Crossing lower bound on the ambient distance: `D(z, x) ≥ D(z, ∂B_{r₁}) + D(∂B_{r₁}, ∂B_{r₂}) +
D(∂B_{r₂}, ∂B_{r₃})` for `dist x z = R > r₃`. -/
lemma crossing_dist_ge (hD : IsEuclideanLengthMetric D) {z x : ℂ} {r₁ r₂ r₃ R : ℝ}
    (h₀ : 0 < r₁) (h₁₂ : r₁ < r₂) (h₂₃ : r₂ < r₃) (h₃R : r₃ < R) (hx : dist x z = R) :
    setDist D {z} (sphere z r₁) + setDist D (sphere z r₁) (sphere z r₂)
        + setDist D (sphere z r₂) (sphere z r₃) ≤ D z x := by
  have key : ENNReal.ofReal (setDist D {z} (sphere z r₁) + setDist D (sphere z r₁) (sphere z r₂)
        + setDist D (sphere z r₂) (sphere z r₃)) ≤ internalMetric D univ z x :=
    le_iInf₂ (fun P _ => crossing_pathLength_ge hD P h₀ h₁₂ h₂₃ h₃R hx)
  rw [← hD.ofReal_eq_internalMetric] at key
  exact (ENNReal.ofReal_le_ofReal_iff (dist_nonneg_of_lengthMetric hD z x)).mp key

/-- Two-step chaining of the ambient metric through a point. -/
lemma ofReal_dist_le_two (hD : IsEuclideanLengthMetric D) {x y m : ℂ} {a b : ℝ≥0∞}
    (h₁ : ENNReal.ofReal (D x m) ≤ a) (h₂ : ENNReal.ofReal (D m y) ≤ b) :
    ENNReal.ofReal (D x y) ≤ a + b := by
  have tri : D x y ≤ D x m + D m y := hD.triangle x m y
  calc ENNReal.ofReal (D x y) ≤ ENNReal.ofReal (D x m + D m y) := ENNReal.ofReal_le_ofReal tri
    _ ≤ ENNReal.ofReal (D x m) + ENNReal.ofReal (D m y) := ENNReal.ofReal_add_le
    _ ≤ a + b := add_le_add h₁ h₂

/-- Joining the diameters of three sets `K₀ ∋ p`, `K₂ ∋ p, q`, `K₁ ∋ q` in a chain: the diameter of `K₀ ∪ K₁ ∪ K₂`
is at most `d₀ + d₁ + d₂` (Step 4 of the 11.13 proof, `diam_D(T) ≤ d₀ + d₂ + d₁`). -/
lemma ofReal_dist_le_chain (hD : IsEuclideanLengthMetric D) {K₀ K₁ K₂ : Set ℂ} {d₀ d₁ d₂ : ℝ≥0∞}
    (h₀ : ∀ x ∈ K₀, ∀ y ∈ K₀, ENNReal.ofReal (D x y) ≤ d₀)
    (h₁ : ∀ x ∈ K₁, ∀ y ∈ K₁, ENNReal.ofReal (D x y) ≤ d₁)
    (h₂ : ∀ x ∈ K₂, ∀ y ∈ K₂, ENNReal.ofReal (D x y) ≤ d₂)
    {p q : ℂ} (hp₀ : p ∈ K₀) (hp₂ : p ∈ K₂) (hq₂ : q ∈ K₂) (hq₁ : q ∈ K₁)
    {x y : ℂ} (hx : x ∈ K₀ ∨ x ∈ K₁ ∨ x ∈ K₂) (hy : y ∈ K₀ ∨ y ∈ K₁ ∨ y ∈ K₂) :
    ENNReal.ofReal (D x y) ≤ d₀ + d₁ + d₂ := by
  have hcomm : ∀ a b : ℂ, ENNReal.ofReal (D a b) = ENNReal.ofReal (D b a) :=
    fun a b => congrArg ENNReal.ofReal (hD.symm a b)
  have pairs01 : ∀ a ∈ K₀, ∀ b ∈ K₁, ENNReal.ofReal (D a b) ≤ d₀ + d₁ + d₂ := by
    intro a ha b hb
    have s1 := ofReal_dist_le_two hD (h₀ a ha p hp₀) (h₂ p hp₂ q hq₂)
    exact (ofReal_dist_le_two hD s1 (h₁ q hq₁ b hb)).trans (le_of_eq (by ring))
  have pairs02 : ∀ a ∈ K₀, ∀ b ∈ K₂, ENNReal.ofReal (D a b) ≤ d₀ + d₁ + d₂ := by
    intro a ha b hb
    exact (ofReal_dist_le_two hD (h₀ a ha p hp₀) (h₂ p hp₂ b hb)).trans (add_le_add le_self_add le_rfl)
  have pairs12 : ∀ a ∈ K₁, ∀ b ∈ K₂, ENNReal.ofReal (D a b) ≤ d₀ + d₁ + d₂ := by
    intro a ha b hb
    exact (ofReal_dist_le_two hD (h₁ a ha q hq₁) (h₂ q hq₂ b hb)).trans (add_le_add le_add_self le_rfl)
  have d₀le : d₀ ≤ d₀ + d₁ + d₂ := le_self_add.trans le_self_add
  have d₁le : d₁ ≤ d₀ + d₁ + d₂ := le_add_self.trans le_self_add
  have d₂le : d₂ ≤ d₀ + d₁ + d₂ := le_add_self
  rcases hx with hx | hx | hx <;> rcases hy with hy | hy | hy
  · exact (h₀ x hx y hy).trans d₀le
  · exact pairs01 x hx y hy
  · exact pairs02 x hx y hy
  · exact (le_of_eq (hcomm x y)).trans (pairs01 y hy x hx)
  · exact (h₁ x hx y hy).trans d₁le
  · exact pairs12 x hx y hy
  · exact (le_of_eq (hcomm x y)).trans (pairs02 y hy x hx)
  · exact (le_of_eq (hcomm x y)).trans (pairs12 y hy x hx)
  · exact (h₂ x hx y hy).trans d₂le

end FirstPassS11i

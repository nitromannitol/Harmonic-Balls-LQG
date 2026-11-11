import HarmonicBalls.FirstPass.S11r.RootedLocalBall
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-! # Internal Weyl metrics agree on a connected open set (R1, part 2)

Main result `internalMetric_weylScaling_eq_of_eventuallyEq`: let `d` be a Euclidean length metric, `ξ ∈ ℝ`, `f`
continuous with compact support, and `g` any function with `f = g` near each point of an open connected set `V`.
Then the internal metrics on `V` of the Weyl-scaled length metrics `e^{ξ g} · d` and `e^{ξ f} · d` coincide
(`internalMetric D V x y = inf_P len(P; D)` over paths in `V`, Gwynne-Miller arXiv:1905.00383v3 §1.2, eq. (1.8)).

No global finiteness or length property of the scaled metric of `g` is assumed: it is finite on `V × V` by
connectedness (`weylScaling_ne_top_of_connected`), and the lengths of paths in `V` agree by a Lebesgue-number
subdivision into pieces on which the two metrics coincide pointwise (`curveLength_eq_of_local_on`). The additivity of
`curveLength` over adjacent intervals is read as additivity of a variation on the subtype `V`
(`curveLength_add_on`, same device as `S11ac/PathSubdivision.lean`).

The local comparison is
`RootedLocal.weylScaling_eq_near` (RootedLocalBall.lean). -/

namespace HarmonicBalls

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace RootedLocal

variable {d : ℂ → ℂ → ℝ}

/-! ## Finiteness on a connected open set -/

/-- Local finiteness of the Weyl distance near each point of a preconnected set `V` gives finiteness on `V × V`
(connectedness argument: the sets of points at finite and at infinite distance from `u` are open in `V`). -/
theorem weylScaling_ne_top_of_connected (hd : IsEuclideanLengthMetric d) {ξ : ℝ} {k : ℂ → ℝ} {V : Set ℂ}
    (hV : IsOpen V) (hVc : IsPreconnected V)
    (hloc : ∀ x ∈ V, ∃ t > 0, ∀ a b, d x a < t → d x b < t → weylScaling d ξ k a b ≠ ⊤)
    {u : ℂ} (hu : u ∈ V) {y : ℂ} (hy : y ∈ V) : weylScaling d ξ k u y ≠ ⊤ := by
  have huu : weylScaling d ξ k u u ≠ ⊤ := by
    obtain ⟨t, ht, h⟩ := hloc u hu
    apply h u u
    · rw [hd.self_eq_zero]
      exact ht
    · rw [hd.self_eq_zero]
      exact ht
  have hU1 : IsOpen (V ∩ {w | weylScaling d ξ k u w ≠ ⊤}) := by
    rw [isOpen_iff_forall_mem_open]
    rintro w ⟨hwV, hwf⟩
    obtain ⟨t, ht, h⟩ := hloc w hwV
    refine ⟨{v | d w v < t} ∩ V, ?_, (isOpen_dBall hd w t).inter hV, ⟨?_, hwV⟩⟩
    · rintro v ⟨hvt, hvV⟩
      refine ⟨hvV, fun hvtop => ?_⟩
      have h1 := hd.weylScaling_triangle ξ k u w v
      have h2 : weylScaling d ξ k w v ≠ ⊤ := h w v (by rw [hd.self_eq_zero]; exact ht) hvt
      exact (ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hwf, h2⟩) h1) hvtop
    · rw [mem_ofPred_eq, hd.self_eq_zero]
      exact ht
  have hU2 : IsOpen (V ∩ {w | weylScaling d ξ k u w = ⊤}) := by
    rw [isOpen_iff_forall_mem_open]
    rintro w ⟨hwV, hwtop⟩
    obtain ⟨t, ht, h⟩ := hloc w hwV
    refine ⟨{v | d w v < t} ∩ V, ?_, (isOpen_dBall hd w t).inter hV, ⟨?_, hwV⟩⟩
    · rintro v ⟨hvt, hvV⟩
      refine ⟨hvV, ?_⟩
      by_contra hvfin
      have h1 := hd.weylScaling_triangle ξ k u v w
      have h2 : weylScaling d ξ k v w ≠ ⊤ := h v w hvt (by rw [hd.self_eq_zero]; exact ht)
      have h3 : weylScaling d ξ k u w ≠ ⊤ :=
        ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hvfin, h2⟩) h1
      exact h3 hwtop
    · rw [mem_ofPred_eq, hd.self_eq_zero]
      exact ht
  have hdisj : Disjoint (V ∩ {w | weylScaling d ξ k u w ≠ ⊤}) (V ∩ {w | weylScaling d ξ k u w = ⊤}) :=
    Set.disjoint_left.mpr fun w h1 h2 => h1.2 h2.2
  have hcover : V ⊆ (V ∩ {w | weylScaling d ξ k u w ≠ ⊤}) ∪ (V ∩ {w | weylScaling d ξ k u w = ⊤}) := by
    intro w hw
    by_cases h : weylScaling d ξ k u w = ⊤
    · exact Or.inr ⟨hw, h⟩
    · exact Or.inl ⟨hw, h⟩
  have hne : (V ∩ (V ∩ {w | weylScaling d ξ k u w ≠ ⊤})).Nonempty := ⟨u, hu, hu, huu⟩
  have hsub := hVc.subset_left_of_subset_union hU1 hU2 hdisj hcover hne
  exact (hsub hy).2

/-! ## Real-valued Weyl distances on a set where they are finite -/

/-- The triangle inequality for the real-valued Weyl distance, where it is finite. -/
theorem toReal_triangle_on (hd : IsEuclideanLengthMetric d) {ξ : ℝ} {k : ℂ → ℝ} {x y z : ℂ}
    (hxy : weylScaling d ξ k x y ≠ ⊤) (hyz : weylScaling d ξ k y z ≠ ⊤) :
    (weylScaling d ξ k x z).toReal ≤ (weylScaling d ξ k x y).toReal + (weylScaling d ξ k y z).toReal := by
  have h := hd.weylScaling_triangle ξ k x y z
  calc (weylScaling d ξ k x z).toReal
      ≤ (weylScaling d ξ k x y + weylScaling d ξ k y z).toReal :=
        ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hxy, hyz⟩) h
    _ = (weylScaling d ξ k x y).toReal + (weylScaling d ξ k y z).toReal :=
        ENNReal.toReal_add hxy hyz

/-! ## Curve lengths: congruence on pieces and additivity on a set -/

/-- `curveLength` on an interval depends only on the metric on a set `B` containing the image of the interval. -/
theorem curveLength_congr_on_piece {E1 E2 : ℂ → ℂ → ℝ} {γ : ℝ → ℂ} {a c : ℝ} {B : Set ℂ}
    (hγ : ∀ τ ∈ Icc a c, γ τ ∈ B) (h : ∀ x ∈ B, ∀ y ∈ B, E1 x y = E2 x y) :
    curveLength E1 γ a c = curveLength E2 γ a c := by
  unfold curveLength
  congr 1
  funext q
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [h _ (hγ _ (q.2.2.2 (i + 1))) _ (hγ _ (q.2.2.2 i))]

/-- Points of a set `V ⊆ ℂ` as a fresh type (not the subtype `↥V`, which carries the Euclidean metric of `ℂ`). -/
structure VPt (V : Set ℂ) where
  /-- The underlying point. -/
  val : ℂ
  /-- The point lies in `V`. -/
  mem : val ∈ V

/-- The pseudo-metric on `VPt V` given by `E`, which is symmetric, vanishes on the diagonal of `V` and satisfies the
triangle inequality on `V` (the same device as `lenMetric` in `S11ac/PathSubdivision.lean`). -/
@[instance_reducible]
noncomputable def vptMetric {E : ℂ → ℂ → ℝ} {V : Set ℂ} (hsymm : ∀ x y, E x y = E y x)
    (hself : ∀ x ∈ V, E x x = 0) (htri : ∀ x ∈ V, ∀ y ∈ V, ∀ z ∈ V, E x z ≤ E x y + E y z) :
    PseudoMetricSpace (VPt V) where
  dist x y := E x.val y.val
  dist_self x := hself x.val x.mem
  dist_comm x y := hsymm x.val y.val
  dist_triangle x y z := htri x.val x.mem y.val y.mem z.val z.mem

/-- Additivity of `curveLength` over adjacent intervals, for a metric which satisfies symmetry, vanishing on the
diagonal and the triangle inequality on a set `V` containing the image of the path. The proof reads `curveLength` as
the variation of the path in the pseudo-metric space `VPt V` with distance `E` (as in `S11ac/PathSubdivision.lean`). -/
theorem curveLength_add_on {E : ℂ → ℂ → ℝ} {V : Set ℂ} (hsymm : ∀ x y, E x y = E y x)
    (hself : ∀ x ∈ V, E x x = 0) (htri : ∀ x ∈ V, ∀ y ∈ V, ∀ z ∈ V, E x z ≤ E x y + E y z)
    {x0 : ℂ} (hx0 : x0 ∈ V) (p : ℝ → ℂ) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (hp : ∀ τ ∈ Icc a c, p τ ∈ V) :
    curveLength E p a b + curveLength E p b c = curveLength E p a c := by
  classical
  let inst : PseudoMetricSpace (VPt V) := vptMetric hsymm hself htri
  let F : ℝ → VPt V := fun τ => if h : p τ ∈ V then ⟨p τ, h⟩ else ⟨x0, hx0⟩
  have hF : ∀ τ ∈ Icc a c, (F τ).val = p τ := fun τ hτ => by
    simp [F, hp τ hτ]
  have hcurve : ∀ s t, a ≤ s → s ≤ t → t ≤ c → curveLength E p s t = eVariationOn F (Icc s t) := by
    intro s t hs hst htc
    unfold curveLength eVariationOn
    congr 1
    funext q
    refine Finset.sum_congr rfl fun i _ => ?_
    have hu : q.2.1 (i + 1) ∈ Icc a c := ⟨le_trans hs (q.2.2.2 (i + 1)).1, le_trans (q.2.2.2 (i + 1)).2 htc⟩
    have hv : q.2.1 i ∈ Icc a c := ⟨le_trans hs (q.2.2.2 i).1, le_trans (q.2.2.2 i).2 htc⟩
    refine (congrArg ENNReal.ofReal ?_).trans (edist_dist _ _).symm
    show E (p (q.2.1 (i + 1))) (p (q.2.1 i)) = E (F (q.2.1 (i + 1))).val (F (q.2.1 i)).val
    rw [hF _ hu, hF _ hv]
  have h := eVariationOn.Icc_add_Icc F (s := Icc a c) hab hbc ⟨hab, hbc⟩
  rw [inter_eq_right.mpr (Icc_subset_Icc le_rfl hbc), inter_eq_right.mpr (Icc_subset_Icc hab le_rfl),
    inter_self] at h
  rw [hcurve a b le_rfl hab hbc, hcurve b c hab hbc le_rfl, hcurve a c le_rfl (hab.trans hbc) le_rfl]
  exact h

/-- **Lengths of paths in `V` agree.** Let `E1, E2` be symmetric, vanish on the diagonal of `V`, satisfy the triangle
inequality on `V`, and agree pointwise on a neighbourhood of each point of the path `γ([0,1]) ⊆ V`. Then their
`curveLength` over `[0,1]` agree. Proof: a Lebesgue number for the cover by these neighbourhoods gives a subdivision
into pieces on which the two metrics coincide; additivity and induction on the pieces conclude. -/
theorem curveLength_eq_of_local_on {E1 E2 : ℂ → ℂ → ℝ} {V : Set ℂ}
    (hs1 : ∀ x y, E1 x y = E1 y x) (hs2 : ∀ x y, E2 x y = E2 y x)
    (hself1 : ∀ x ∈ V, E1 x x = 0) (hself2 : ∀ x ∈ V, E2 x x = 0)
    (htri1 : ∀ x ∈ V, ∀ y ∈ V, ∀ z ∈ V, E1 x z ≤ E1 x y + E1 y z)
    (htri2 : ∀ x ∈ V, ∀ y ∈ V, ∀ z ∈ V, E2 x z ≤ E2 x y + E2 y z)
    {γ : ℝ → ℂ} (hγc : Continuous γ) (hγV : ∀ τ ∈ Icc (0 : ℝ) 1, γ τ ∈ V)
    (hloc : ∀ τ ∈ Icc (0 : ℝ) 1, ∃ B : Set ℂ, IsOpen B ∧ γ τ ∈ B ∧
      ∀ x ∈ B, ∀ y ∈ B, E1 x y = E2 x y) :
    curveLength E1 γ 0 1 = curveLength E2 γ 0 1 := by
  choose! B hBo hBγ hBeq using hloc
  have hcover : Icc (0 : ℝ) 1 ⊆ ⋃ i : Icc (0 : ℝ) 1, γ ⁻¹' (B i.1) := fun σ hσ =>
    mem_iUnion.mpr ⟨⟨σ, hσ⟩, by simpa using hBγ σ hσ⟩
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric isCompact_Icc
    (fun i : Icc (0 : ℝ) 1 => (hBo i.1 i.2).preimage hγc) hcover
  -- pieces of length `< δ` are handled by a single neighbourhood
  have hpiece : ∀ a c : ℝ, 0 ≤ a → a ≤ c → c ≤ 1 → c - a < δ →
      curveLength E1 γ a c = curveLength E2 γ a c := by
    intro a c ha hac hc1 hlen
    obtain ⟨i, hi⟩ := hleb a ⟨ha, by linarith⟩
    refine curveLength_congr_on_piece (B := B i.1) ?_ (hBeq i.1 i.2)
    intro τ hτ
    have hball : τ ∈ ball a δ := by
      rw [mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hτ.1, hτ.2]
    exact hi hball
  -- subdivision into `n + 1` pieces of length `h < δ`
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  set h : ℝ := 1 / ((n : ℝ) + 1) with hh
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have hhpos : 0 < h := by rw [hh]; positivity
  have hnh : ((n : ℝ) + 1) * h = 1 := by
    rw [hh, mul_one_div_cancel hn1]
  have hk : ∀ k : ℕ, (k : ℝ) ≤ (n : ℝ) + 1 → curveLength E1 γ 0 ((k : ℝ) * h) =
      curveLength E2 γ 0 ((k : ℝ) * h) := by
    intro k
    induction k with
    | zero =>
      intro _
      simp only [Nat.cast_zero, zero_mul]
      exact hpiece 0 0 le_rfl le_rfl (by norm_num) (by simpa using hδ)
    | succ m ih =>
      intro hm
      push_cast at hm ih ⊢
      have hm1 : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := hm
      have hmh : 0 ≤ (m : ℝ) * h := mul_nonneg (Nat.cast_nonneg m) hhpos.le
      have hmh' : (m : ℝ) * h ≤ ((m : ℝ) + 1) * h :=
        mul_le_mul_of_nonneg_right (by linarith) hhpos.le
      have hc1 : ((m : ℝ) + 1) * h ≤ 1 := by
        have := mul_le_mul_of_nonneg_right hm1 hhpos.le
        linarith [hnh]
      have hV0 : ∀ τ ∈ Icc (0 : ℝ) (((m : ℝ) + 1) * h), γ τ ∈ V := fun τ hτ =>
        hγV τ ⟨hτ.1, hτ.2.trans hc1⟩
      have hadd1 := curveLength_add_on (E := E1) hs1 (fun x hx => hself1 x hx) htri1
        (x0 := γ 0) (hγV 0 ⟨le_rfl, zero_le_one⟩) γ hmh hmh' hV0
      have hadd2 := curveLength_add_on (E := E2) hs2 (fun x hx => hself2 x hx) htri2
        (x0 := γ 0) (hγV 0 ⟨le_rfl, zero_le_one⟩) γ hmh hmh' hV0
      have hlen : ((m : ℝ) + 1) * h - (m : ℝ) * h = h := by ring
      have hpc := hpiece ((m : ℝ) * h) (((m : ℝ) + 1) * h) hmh hmh' hc1 (by linarith)
      rw [← hadd1, ← hadd2, ih (by linarith), hpc]
  have := hk (n + 1) (by norm_num)
  push_cast at this
  rw [hnh] at this
  exact this

/-! ## Main result -/

/-- **Internal Weyl metrics agree on a connected open set.** Let `d` be a Euclidean length metric, `f` continuous with
compact support, and `g` with `f = g` near each point of an open connected `V`. Then for `x, y ∈ V` the internal
distances on `V` of the Weyl-scaled metrics of `g` and of `f` coincide. (the length property of the scaled metric of `f` is supplied by `weylScaling_continuous_compactSupport_length`.) -/
theorem internalMetric_weylScaling_eq_of_eventuallyEq (hd : IsEuclideanLengthMetric d) {ξ : ℝ}
    {f g : ℂ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    {V : Set ℂ} (hV : IsOpen V) (hVc : IsConnected V) (hfg : ∀ x ∈ V, f =ᶠ[𝓝 x] g)
    {x y : ℂ} :
    internalMetric (fun a b => (weylScaling d ξ g a b).toReal) V x y =
      internalMetric (fun a b => (weylScaling d ξ f a b).toReal) V x y := by
  obtain ⟨hfin, hfL⟩ := weylScaling_continuous_compactSupport_length d ξ f hd hf hfc
  -- local data at each point of `V`
  have hlocal : ∀ z ∈ V, ∃ t > 0, (∀ a b, d z a < t → d z b < t →
      weylScaling d ξ f a b = weylScaling d ξ g a b) ∧
      (∀ a b, d z a < t → d z b < t → weylScaling d ξ f a b ≠ ⊤) := by
    intro z hz
    obtain ⟨ρ, hρ, hρf⟩ := Metric.eventually_nhds_iff.mp (hfg z hz : ∀ᶠ w in 𝓝 z, f w = g w)
    obtain ⟨t, ht, heq, hne⟩ := weylScaling_eq_near hd (ξ := ξ) hf hρ (fun w hw => hρf hw)
    exact ⟨t, ht, fun a b ha hb => heq a b ha hb, fun a b ha hb => hne a b ha hb⟩
  have hfinG : ∀ z ∈ V, ∃ t > 0, ∀ a b, d z a < t → d z b < t → weylScaling d ξ g a b ≠ ⊤ := by
    intro z hz
    obtain ⟨t, ht, heq, hne⟩ := hlocal z hz
    exact ⟨t, ht, fun a b ha hb => by rw [← heq a b ha hb]; exact hne a b ha hb⟩
  have hGtop : ∀ u ∈ V, ∀ w ∈ V, weylScaling d ξ g u w ≠ ⊤ := fun u hu w hw =>
    weylScaling_ne_top_of_connected hd hV hVc.isPreconnected hfinG hu hw
  have hFtop : ∀ u w, weylScaling d ξ f u w ≠ ⊤ := fun u w => (hfin u w).ne
  -- the two real-valued metrics on `V`
  have hsymG : ∀ a b, (weylScaling d ξ g a b).toReal = (weylScaling d ξ g b a).toReal := fun a b => by
    rw [hd.weylScaling_symm ξ g a b]
  have hsymF : ∀ a b, (weylScaling d ξ f a b).toReal = (weylScaling d ξ f b a).toReal := fun a b => by
    rw [hd.weylScaling_symm ξ f a b]
  have hselfF : ∀ a ∈ V, (weylScaling d ξ f a a).toReal = 0 := fun a _ => hfL.self_eq_zero a
  have hselfG : ∀ a ∈ V, (weylScaling d ξ g a a).toReal = 0 := by
    intro a ha
    obtain ⟨t, ht, heq, -⟩ := hlocal a ha
    rw [← heq a a (by rw [hd.self_eq_zero]; exact ht) (by rw [hd.self_eq_zero]; exact ht)]
    exact hselfF a ha
  have htriG : ∀ a ∈ V, ∀ b ∈ V, ∀ c ∈ V, (weylScaling d ξ g a c).toReal ≤
      (weylScaling d ξ g a b).toReal + (weylScaling d ξ g b c).toReal := fun a ha b hb c hc =>
    toReal_triangle_on hd (hGtop a ha b hb) (hGtop b hb c hc)
  have htriF : ∀ a ∈ V, ∀ b ∈ V, ∀ c ∈ V, (weylScaling d ξ f a c).toReal ≤
      (weylScaling d ξ f a b).toReal + (weylScaling d ξ f b c).toReal := fun a _ b _ c _ =>
    toReal_triangle_on hd (hFtop a b) (hFtop b c)
  -- equal lengths of every path in `V`
  have hpath : ∀ (P : Path x y), (∀ t, P t ∈ V) →
      curveLength (fun a b => (weylScaling d ξ g a b).toReal) P.extend 0 1 =
        curveLength (fun a b => (weylScaling d ξ f a b).toReal) P.extend 0 1 := by
    intro P hP
    have hγV : ∀ τ ∈ Icc (0 : ℝ) 1, P.extend τ ∈ V := fun τ hτ => by
      rw [Path.extend_extends' P ⟨τ, hτ⟩]
      exact hP _
    refine curveLength_eq_of_local_on (V := V) hsymG hsymF hselfG hselfF htriG htriF
      P.continuous_extend hγV ?_
    intro τ hτ
    obtain ⟨t, ht, heq, -⟩ := hlocal _ (hγV τ hτ)
    refine ⟨{w | d (P.extend τ) w < t}, isOpen_dBall hd _ t, ?_, ?_⟩
    · rw [mem_ofPred_eq, hd.self_eq_zero]
      exact ht
    · intro a ha b hb
      rw [mem_ofPred_eq] at ha hb
      show (weylScaling d ξ g a b).toReal = (weylScaling d ξ f a b).toReal
      rw [heq a b ha hb]
  unfold internalMetric
  exact le_antisymm
    (le_iInf₂ fun P hP => (iInf₂_le P hP).trans_eq (hpath P hP))
    (le_iInf₂ fun P hP => (iInf₂_le P hP).trans_eq (hpath P hP).symm)

end RootedLocal

end HarmonicBalls


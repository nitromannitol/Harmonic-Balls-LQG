import Mathlib
import HarmonicBalls.Proofs.Potential.PerronLift

/-!
# The Perron function is harmonic

Let `Ω ⊆ ℂ` be a bounded open set and `φ` a function that is bounded on the frontier of `Ω`.
A *Perron subfunction* is a function continuous on `closure Ω`, with the local sub-mean-value
property in `Ω`, and bounded above by `φ` on the frontier.  The *Perron function* `perronFun Ω φ` is
the pointwise supremum of the Perron subfunctions.  It is harmonic in `Ω`
(Gilbarg–Trudinger, *Elliptic Partial Differential Equations of Second Order*, Theorem 2.12,
pp. 24–25).

* `HarmonicBalls.IsPerronSub`, `HarmonicBalls.perronFun`: the definitions;
* `HarmonicBalls.IsPerronSub.const`, `.sup`, `.le_bound`, `.harmonicLift`: closure properties;
* `HarmonicBalls.harmonicOnNhd_perronFun`: harmonicity of the Perron function.
-/

namespace HarmonicBalls

open Metric Set Filter Topology InnerProductSpace

/-- A Perron subfunction for the data `φ` on the frontier of `Ω`. -/
def IsPerronSub (Ω : Set ℂ) (φ : ℂ → ℝ) (v : ℂ → ℝ) : Prop :=
  ContinuousOn v (closure Ω) ∧ IsLocalSubMean Ω v ∧ ∀ z ∈ frontier Ω, v z ≤ φ z

/-- The Perron function: the pointwise supremum of the Perron subfunctions. -/
noncomputable def perronFun (Ω : Set ℂ) (φ : ℂ → ℝ) (z : ℂ) : ℝ :=
  sSup {t | ∃ v, IsPerronSub Ω φ v ∧ v z = t}

section Closure

variable {Ω : Set ℂ} {φ : ℂ → ℝ}

theorem IsPerronSub.const {m : ℝ} (hΩ : IsOpen Ω) (hm : ∀ z ∈ frontier Ω, m ≤ φ z) :
    IsPerronSub Ω φ (fun _ => m) :=
  ⟨continuousOn_const, IsLocalSubMean.of_harmonicOnNhd hΩ (harmonicOnNhd_const m), hm⟩

theorem IsPerronSub.sup {v w : ℂ → ℝ} (hv : IsPerronSub Ω φ v) (hw : IsPerronSub Ω φ w) :
    IsPerronSub Ω φ (fun z => max (v z) (w z)) :=
  ⟨ContinuousOn.sup hv.1 hw.1,
    IsLocalSubMean.sup hv.2.1 hw.2.1 (hv.1.mono subset_closure) (hw.1.mono subset_closure),
    fun z hz => max_le (hv.2.2 z hz) (hw.2.2 z hz)⟩

theorem IsPerronSub.le_bound {v : ℂ → ℝ} {M : ℝ} (hΩ : IsOpen Ω) (hbdd : Bornology.IsBounded Ω)
    (hv : IsPerronSub Ω φ v) (hM : ∀ z ∈ frontier Ω, φ z ≤ M) : ∀ z ∈ Ω, v z ≤ M :=
  IsLocalSubMean.le_of_le_frontier hΩ hbdd hv.1 hv.2.1 fun z hz => (hv.2.2 z hz).trans (hM z hz)

theorem IsPerronSub.harmonicLift {v : ℂ → ℝ} {c : ℂ} {ρ : ℝ} (hΩ : IsOpen Ω)
    (hv : IsPerronSub Ω φ v) (hρ : 0 < ρ) (hball : closedBall c ρ ⊆ Ω) :
    IsPerronSub Ω φ (harmonicLift c ρ v) := by
  refine ⟨continuousOn_harmonicLift hρ hv.1
    (sphere_subset_closedBall.trans (hball.trans subset_closure)),
    isLocalSubMean_harmonicLift hρ hball hv.1 hv.2.1, fun z hz => ?_⟩
  have hzΩ : z ∉ Ω := by
    rw [frontier, hΩ.interior_eq] at hz
    exact hz.2
  rw [harmonicLift_of_notMem fun h => hzΩ (hball (ball_subset_closedBall h))]
  exact hv.2.2 z hz

end Closure

/-- The running maximum of a sequence of functions, started at the constant `m`. -/
def supSeq (m : ℝ) (v : ℕ → ℂ → ℝ) : ℕ → ℂ → ℝ
  | 0 => fun z => max m (v 0 z)
  | n + 1 => fun z => max (supSeq m v n z) (v (n + 1) z)

theorem le_supSeq (m : ℝ) (v : ℕ → ℂ → ℝ) (n : ℕ) (z : ℂ) : v n z ≤ supSeq m v n z := by
  cases n with
  | zero => exact le_max_right _ _
  | succ n => exact le_max_right _ _

theorem const_le_supSeq (m : ℝ) (v : ℕ → ℂ → ℝ) (n : ℕ) (z : ℂ) : m ≤ supSeq m v n z := by
  induction n with
  | zero => exact le_max_left _ _
  | succ n ih => exact ih.trans (le_max_left _ _)

theorem supSeq_succ_ge (m : ℝ) (v : ℕ → ℂ → ℝ) (n : ℕ) (z : ℂ) :
    supSeq m v n z ≤ supSeq m v (n + 1) z := le_max_left _ _

theorem isPerronSub_supSeq {Ω : Set ℂ} {φ : ℂ → ℝ} {m : ℝ} {v : ℕ → ℂ → ℝ} (hΩ : IsOpen Ω)
    (hm : ∀ z ∈ frontier Ω, m ≤ φ z) (hv : ∀ n, IsPerronSub Ω φ (v n)) (n : ℕ) :
    IsPerronSub Ω φ (supSeq m v n) := by
  induction n with
  | zero => exact (IsPerronSub.const hΩ hm).sup (hv 0)
  | succ n ih => exact ih.sup (hv (n + 1))

/-- A bounded pointwise limit of functions continuous on a circle is circle integrable. -/
theorem circleIntegrable_of_tendsto {F : ℕ → ℂ → ℝ} {g : ℂ → ℝ} {c : ℂ} {ρ C : ℝ} (hρ : 0 < ρ)
    (hF : ∀ n, ContinuousOn (F n) (sphere c ρ)) (hb : ∀ n, ∀ z ∈ sphere c ρ, |F n z| ≤ C)
    (hlim : ∀ z ∈ sphere c ρ, Tendsto (fun n => F n z) atTop (𝓝 (g z))) :
    CircleIntegrable g c ρ := by
  have hmem : ∀ θ, circleMap c ρ θ ∈ sphere c ρ := fun θ => circleMap_mem_sphere c hρ.le θ
  have hmeas : Measurable fun θ => g (circleMap c ρ θ) :=
    measurable_of_tendsto_metrizable (f := fun n θ => F n (circleMap c ρ θ))
      (fun n => ((hF n).comp_continuous (continuous_circleMap c ρ) hmem).measurable)
      (tendsto_pi_nhds.2 fun θ => hlim _ (hmem θ))
  have hbg : ∀ θ, |g (circleMap c ρ θ)| ≤ C := fun θ =>
    le_of_tendsto' (hlim _ (hmem θ)).abs fun n => hb n _ (hmem θ)
  exact (intervalIntegrable_const (c := C)).mono_fun' hmeas.aestronglyMeasurable
    (Eventually.of_forall fun θ => by simpa using hbg θ)

section Main

variable {Ω : Set ℂ} {φ : ℂ → ℝ}

/-- A monotone, bounded sequence of Perron subfunctions has a limit on a circle in `Ω` whose Poisson
integral is harmonic, dominates every term and is dominated by the Perron function; the Poisson
integrals of the terms converge to it. -/
theorem exists_perron_limit {m M : ℝ} (hΩ : IsOpen Ω) (hbdd : Bornology.IsBounded Ω)
    (hM : ∀ z ∈ frontier Ω, φ z ≤ M) {y : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hball : closedBall y ρ ⊆ Ω)
    {W : ℕ → ℂ → ℝ} (hW : ∀ n, IsPerronSub Ω φ (W n)) (hmono : ∀ n z, W n z ≤ W (n + 1) z)
    (hm : ∀ n z, m ≤ W n z) :
    ∃ g : ℂ → ℝ, CircleIntegrable g y ρ ∧
      HarmonicOnNhd (discPoissonIntegral g y ρ) (ball y ρ) ∧
      (∀ z ∈ sphere y ρ, Tendsto (fun n => W n z) atTop (𝓝 (g z))) ∧
      (∀ x ∈ ball y ρ, discPoissonIntegral g y ρ x ≤ perronFun Ω φ x) ∧
      (∀ x ∈ ball y ρ, ∀ n, W n x ≤ discPoissonIntegral g y ρ x) := by
  have hmono' : ∀ {n k : ℕ}, n ≤ k → ∀ z, W n z ≤ W k z := fun {n k} hnk z =>
    monotone_nat_of_le_succ (fun n => hmono n z) hnk
  have hsphΩ : sphere y ρ ⊆ Ω := sphere_subset_closedBall.trans hball
  have hcont : ∀ n, ContinuousOn (W n) (sphere y ρ) := fun n =>
    (hW n).1.mono (hsphΩ.trans subset_closure)
  have hupp : ∀ n, ∀ z ∈ sphere y ρ, W n z ≤ M := fun n z hz =>
    (hW n).le_bound hΩ hbdd hM z (hsphΩ hz)
  have habs : ∀ n, ∀ z ∈ sphere y ρ, |W n z| ≤ max |m| |M| := fun n z hz =>
    abs_le_max_abs_abs (hm n z) (hupp n z hz)
  have hlim : ∀ z ∈ sphere y ρ, Tendsto (fun n => W n z) atTop (𝓝 (⨆ n, W n z)) := fun z hz =>
    tendsto_atTop_ciSup (monotone_nat_of_le_succ fun n => hmono n z)
      ⟨M, by rintro _ ⟨n, rfl⟩; exact hupp n z hz⟩
  have hgi : CircleIntegrable (fun z => ⨆ n, W n z) y ρ :=
    circleIntegrable_of_tendsto hρ hcont habs hlim
  have hlimx : ∀ x ∈ ball y ρ, Tendsto (fun n => harmonicLift y ρ (W n) x) atTop
      (𝓝 (discPoissonIntegral (fun z => ⨆ n, W n z) y ρ x)) := by
    intro x hx
    have h := tendsto_discPoissonIntegral (φ := fun z => ⨆ n, W n z) (Φ := W)
      (G := fun _ => max |m| |M|) hx (fun n => (hcont n).circleIntegrable hρ.le)
      (circleIntegrable_const _ _ _) habs hlim
    exact h.congr fun n => (harmonicLift_of_mem hx).symm
  have hbd : ∀ x ∈ Ω, BddAbove {t | ∃ v, IsPerronSub Ω φ v ∧ v x = t} := fun x hx =>
    ⟨M, by rintro t ⟨v, hv, rfl⟩; exact hv.le_bound hΩ hbdd hM x hx⟩
  refine ⟨fun z => ⨆ n, W n z, hgi, harmonicOnNhd_discPoissonIntegral hgi, hlim, ?_, ?_⟩
  · intro x hx
    refine le_of_tendsto' (hlimx x hx) fun n => ?_
    exact le_csSup (hbd x (hball (ball_subset_closedBall hx)))
      ⟨harmonicLift y ρ (W n), (hW n).harmonicLift hΩ hρ hball, rfl⟩
  · intro x hx n
    refine ge_of_tendsto (hlimx x hx) (eventually_atTop.2 ⟨n, fun k hk => ?_⟩)
    exact (hmono' hk x).trans
      (le_harmonicLift hρ hball ((hW k).1.mono (hball.trans subset_closure)) (hW k).2.1 x)

/-- **The Perron function is harmonic** (Gilbarg–Trudinger, Theorem 2.12). -/
theorem harmonicOnNhd_perronFun {m M : ℝ} (hΩ : IsOpen Ω) (hbdd : Bornology.IsBounded Ω)
    (hm : ∀ z ∈ frontier Ω, m ≤ φ z) (hM : ∀ z ∈ frontier Ω, φ z ≤ M) :
    HarmonicOnNhd (perronFun Ω φ) Ω := by
  have hbd : ∀ z ∈ Ω, BddAbove {t | ∃ v, IsPerronSub Ω φ v ∧ v z = t} := fun z hz =>
    ⟨M, by rintro t ⟨v, hv, rfl⟩; exact hv.le_bound hΩ hbdd hM z hz⟩
  have hne : ∀ z, {t | ∃ v, IsPerronSub Ω φ v ∧ v z = t}.Nonempty := fun z =>
    ⟨m, fun _ => m, IsPerronSub.const hΩ hm, rfl⟩
  intro y hy
  obtain ⟨r, hr, hrΩ⟩ := Metric.isOpen_iff.mp hΩ y hy
  have hρ : 0 < r / 2 := by positivity
  have hball : closedBall y (r / 2) ⊆ Ω := (closedBall_subset_ball (by linarith)).trans hrΩ
  have hseq : ∀ n : ℕ, ∃ v, IsPerronSub Ω φ v ∧ perronFun Ω φ y - 1 / ((n : ℝ) + 1) < v y := by
    intro n
    have h1 : perronFun Ω φ y - 1 / ((n : ℝ) + 1) <
        sSup {t | ∃ v, IsPerronSub Ω φ v ∧ v y = t} := sub_lt_self _ (by positivity)
    obtain ⟨t, ⟨v, hv, rfl⟩, ht⟩ := exists_lt_of_lt_csSup (hne y) h1
    exact ⟨v, hv, ht⟩
  choose v hv hvy using hseq
  have hW : ∀ n, IsPerronSub Ω φ (supSeq m v n) := isPerronSub_supSeq hΩ hm hv
  obtain ⟨g, hgi, hgh, hgsph, hgle, hgge⟩ := exists_perron_limit hΩ hbdd hM hρ hball hW
    (supSeq_succ_ge m v) (const_le_supSeq m v)
  have hy' : y ∈ ball y (r / 2) := mem_ball_self hρ
  have hVy : discPoissonIntegral g y (r / 2) y = perronFun Ω φ y := by
    refine le_antisymm (hgle y hy') ?_
    have ht : Tendsto (fun n : ℕ => perronFun Ω φ y - 1 / ((n : ℝ) + 1)) atTop
        (𝓝 (perronFun Ω φ y - 0)) :=
      tendsto_const_nhds.sub tendsto_one_div_add_atTop_nhds_zero_nat
    rw [sub_zero] at ht
    refine le_of_tendsto' ht fun n => ?_
    exact ((hvy n).trans_le (le_supSeq m v n y)).le.trans (hgge y hy' n)
  have hVu : ∀ x ∈ ball y (r / 2), discPoissonIntegral g y (r / 2) x = perronFun Ω φ x := by
    by_contra hcon
    push Not at hcon
    obtain ⟨z, hz, hne'⟩ := hcon
    have hlt : discPoissonIntegral g y (r / 2) z < perronFun Ω φ z := lt_of_le_of_ne (hgle z hz) hne'
    obtain ⟨t, ⟨w, hw, rfl⟩, hwt⟩ := exists_lt_of_lt_csSup (hne z) hlt
    have hW' : ∀ n, IsPerronSub Ω φ (fun x => max (supSeq m v n x) (w x)) := fun n =>
      (hW n).sup hw
    obtain ⟨g', hg'i, hg'h, hg'sph, hg'le, hg'ge⟩ := exists_perron_limit hΩ hbdd hM hρ hball hW'
      (fun n x => max_le_max (supSeq_succ_ge m v n x) le_rfl)
      (fun n x => (const_le_supSeq m v n x).trans (le_max_left _ _))
    have hgg' : ∀ ζ ∈ sphere y (r / 2), g ζ ≤ g' ζ := fun ζ hζ =>
      le_of_tendsto_of_tendsto' (hgsph ζ hζ) (hg'sph ζ hζ) fun n => le_max_left _ _
    have hVV : ∀ x ∈ ball y (r / 2),
        discPoissonIntegral g y (r / 2) x ≤ discPoissonIntegral g' y (r / 2) x := fun x hx =>
      discPoissonIntegral_mono hgi hg'i hx hgg'
    have hy'' : discPoissonIntegral g' y (r / 2) y = discPoissonIntegral g y (r / 2) y :=
      le_antisymm ((hg'le y hy').trans hVy.ge) (hVV y hy')
    have hD : HarmonicOnNhd (fun x => discPoissonIntegral g y (r / 2) x -
        discPoissonIntegral g' y (r / 2) x) (ball y (r / 2)) := hgh.sub hg'h
    have hDeq := IsLocalSubMean.eq_of_isMaxOn (isConnected_ball hρ)
      (IsLocalSubMean.of_harmonicOnNhd isOpen_ball hD) hD.continuousOn hy' (fun x hx => by
        have h1 := hVV x hx
        have h2 := hVV y hy'
        linarith) z hz
    have hz2 : w z ≤ discPoissonIntegral g' y (r / 2) z :=
      (le_max_right _ _).trans (hg'ge z hz 0)
    linarith
  have hHarm : HarmonicAt (discPoissonIntegral g y (r / 2)) y := hgh y hy'
  refine (harmonicAt_congr_nhds ?_).mp hHarm
  filter_upwards [isOpen_ball.mem_nhds hy'] with x hx
  exact hVu x hx

end Main

end HarmonicBalls

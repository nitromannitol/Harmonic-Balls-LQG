import HarmonicBalls.FirstPass.S11i.Step8CorrectedMarked
import HarmonicBalls.FirstPass.S11at.Producers

/-! # Cylinder π-system for the joint law of (field, circle profile, root)

On the joint sample space `DMSJointX := ((ℂ → ℝ) → ℝ) × (CircleParameter → ℝ) × ℂ` (a field `T`, a circle-average profile,
and a root `z`), `mX` is the product of the pairing σ-algebra on the field factor (the σ-algebra of the test-function
evaluations, `pairingSigmaAlgebra (fun T => T) univ`) with the product σ-algebra on the profile and root factors.

* `obs φ c` evaluates the field at finitely many test functions `φ i`, the profile at finitely many circle parameters `c k`,
  and keeps the root.
* `cyl` is the family of cylinders `obs φ c ⁻¹' E` with `E` measurable and every `φ i` a test function on `univ`.
  It contains the whole space (`univ_mem_cyl`), is a π-system (`isPiSystem_cyl`), and generates `mX` (`generateFrom_cyl`).

Terminology: pairing σ-algebra and test-function evaluations (Duplantier-Miller-Sheffield, arXiv:1409.7055, Appendix A),
circle averages of the whole-plane field (Armitage-Gardiner), rooted LQG measures (Duplantier-Sheffield, arXiv:0808.1560, §3.3).
-/

open MeasureTheory Set Function
open HarmonicBalls.FirstPassS11iStep8Corrected

namespace HarmonicBalls.DMSJointPosCylinder

/-- The joint sample space: a field `T : (ℂ → ℝ) → ℝ`, a circle-average profile `CircleParameter → ℝ`, and a root `ℂ`. -/
abbrev DMSJointX : Type := ((ℂ → ℝ) → ℝ) × (CircleParameter → ℝ) × ℂ

/-- The σ-algebra `mX` on `DMSJointX`: the pairing σ-algebra on the field factor, times the product σ-algebra on the
profile and root factors. -/
noncomputable abbrev mX : MeasurableSpace DMSJointX :=
  (pairingSigmaAlgebra (fun T : (ℂ → ℝ) → ℝ => T) Set.univ).prod inferInstance

/-- The observation map: the field at the test functions `φ i`, the profile at the parameters `c k`, and the root. -/
def obs {n m : ℕ} (φ : Fin n → ℂ → ℝ) (c : Fin m → CircleParameter) (x : DMSJointX) :
    (Fin n → ℝ) × (Fin m → ℝ) × ℂ :=
  (fun i => x.1 (φ i), fun k => x.2.1 (c k), x.2.2)

/-- The cylinder sets: preimages under `obs φ c` of measurable sets, for finitely many test functions `φ i`. -/
def cyl : Set (Set DMSJointX) :=
  {S | ∃ (n m : ℕ) (φ : Fin n → ℂ → ℝ) (c : Fin m → CircleParameter)
      (E : Set ((Fin n → ℝ) × (Fin m → ℝ) × ℂ)),
      (∀ i, IsTestFunction Set.univ (φ i)) ∧ MeasurableSet E ∧ S = obs φ c ⁻¹' E}

/-- The observation map is `mX`-measurable when every `φ i` is a test function on `univ`. -/
theorem measurable_obs {n m : ℕ} {φ : Fin n → ℂ → ℝ} {c : Fin m → CircleParameter}
    (hφ : ∀ i, IsTestFunction Set.univ (φ i)) : Measurable[mX] (obs φ c) := by
  let _ : MeasurableSpace ((ℂ → ℝ) → ℝ) := pairingSigmaAlgebra (fun T : (ℂ → ℝ) → ℝ => T) Set.univ
  unfold obs
  refine Measurable.prodMk (measurable_pi_iff.2 fun i => ?_)
    (Measurable.prodMk (measurable_pi_iff.2 fun k => ?_) (measurable_snd.comp measurable_snd))
  · exact (measurable_eval_pairingSigmaAlgebra (φ i) (hφ i)).comp measurable_fst
  · exact (measurable_pi_apply (c k)).comp (measurable_fst.comp measurable_snd)

/-- The whole space is a cylinder (`n = m = 0`, `E = univ`). -/
theorem univ_mem_cyl : (Set.univ : Set DMSJointX) ∈ cyl :=
  ⟨0, 0, Fin.elim0, Fin.elim0, Set.univ, fun i => Fin.elim0 i, MeasurableSet.univ, Set.preimage_univ.symm⟩

/-- The evaluation of the field at a test function is measurable for the cylinder σ-algebra. -/
theorem measurableSet_eval_cyl {A : Set ℝ} (hA : MeasurableSet A) {φ : ℂ → ℝ}
    (hφ : IsTestFunction Set.univ φ) :
    MeasurableSet[MeasurableSpace.generateFrom cyl] ((fun x : DMSJointX => x.1 φ) ⁻¹' A) := by
  have hφ1 : ∀ i : Fin 1, IsTestFunction Set.univ (![φ] i) := fun i => by
    fin_cases i
    simpa using hφ
  have hE : MeasurableSet {w : (Fin 1 → ℝ) × (Fin 0 → ℝ) × ℂ | w.1 0 ∈ A} :=
    ((measurable_pi_apply 0).comp measurable_fst) hA
  have hset : (fun x : DMSJointX => x.1 φ) ⁻¹' A = obs ![φ] Fin.elim0 ⁻¹' {w | w.1 0 ∈ A} := by
    ext x
    simp [obs]
  rw [hset]
  exact MeasurableSpace.measurableSet_generateFrom
    ⟨1, 0, ![φ], Fin.elim0, {w | w.1 0 ∈ A}, hφ1, hE, rfl⟩

/-- The circle-average profile at a fixed circle parameter is measurable for the cylinder σ-algebra. -/
theorem measurableSet_profile_cyl {A : Set ℝ} (hA : MeasurableSet A) (p : CircleParameter) :
    MeasurableSet[MeasurableSpace.generateFrom cyl] ((fun x : DMSJointX => x.2.1 p) ⁻¹' A) := by
  have hE : MeasurableSet {w : (Fin 0 → ℝ) × (Fin 1 → ℝ) × ℂ | w.2.1 0 ∈ A} :=
    ((measurable_pi_apply 0).comp (measurable_fst.comp measurable_snd)) hA
  have hset : (fun x : DMSJointX => x.2.1 p) ⁻¹' A = obs Fin.elim0 ![p] ⁻¹' {w | w.2.1 0 ∈ A} := by
    ext x
    simp [obs]
  rw [hset]
  exact MeasurableSpace.measurableSet_generateFrom
    ⟨0, 1, Fin.elim0, ![p], {w | w.2.1 0 ∈ A}, fun i => Fin.elim0 i, hE, rfl⟩

/-- The root is measurable for the cylinder σ-algebra. -/
theorem measurableSet_root_cyl {A : Set ℂ} (hA : MeasurableSet A) :
    MeasurableSet[MeasurableSpace.generateFrom cyl] ((fun x : DMSJointX => x.2.2) ⁻¹' A) := by
  have hE : MeasurableSet {w : (Fin 0 → ℝ) × (Fin 0 → ℝ) × ℂ | w.2.2 ∈ A} :=
    (measurable_snd.comp measurable_snd) hA
  have hset : (fun x : DMSJointX => x.2.2) ⁻¹' A = obs Fin.elim0 Fin.elim0 ⁻¹' {w | w.2.2 ∈ A} := by
    ext x
    simp [obs]
  rw [hset]
  exact MeasurableSpace.measurableSet_generateFrom
    ⟨0, 0, Fin.elim0, Fin.elim0, {w | w.2.2 ∈ A}, fun i => Fin.elim0 i, hE, rfl⟩

/-- The identity from the cylinder σ-algebra to `mX` is measurable: the field component is pairing-measurable by
`measurable_into_pairing`, the profile and root components by the cylinder evaluations above. -/
theorem measurable_id_cyl :
    @Measurable DMSJointX DMSJointX (MeasurableSpace.generateFrom cyl) mX id := by
  let _ : MeasurableSpace DMSJointX := MeasurableSpace.generateFrom cyl
  let _ : MeasurableSpace ((ℂ → ℝ) → ℝ) := pairingSigmaAlgebra (fun T : (ℂ → ℝ) → ℝ => T) Set.univ
  show @Measurable DMSJointX DMSJointX (MeasurableSpace.generateFrom cyl) mX (fun x => (x.1, x.2.1, x.2.2))
  refine Measurable.prodMk ?_ (Measurable.prodMk ?_ ?_)
  · exact @FirstPassS11atProducers.measurable_into_pairing DMSJointX (MeasurableSpace.generateFrom cyl) (fun x => x.1)
      (fun φ hφ A hA => measurableSet_eval_cyl hA hφ)
  · exact measurable_pi_iff.2 fun p A hA => measurableSet_profile_cyl hA p
  · exact fun A hA => measurableSet_root_cyl hA

/-- The cylinder family generates the joint σ-algebra: `mX = generateFrom cyl`. -/
theorem generateFrom_cyl : mX = MeasurableSpace.generateFrom cyl := by
  refine le_antisymm (fun s hs => measurable_id_cyl hs) (MeasurableSpace.generateFrom_le fun s hs => ?_)
  obtain ⟨n, m, φ, c, E, hφ, hE, rfl⟩ := hs
  exact measurable_obs hφ hE

/-- The cylinders form a π-system. The intersection of two cylinders is the cylinder of the concatenated families
`Fin.append φ φ'`, `Fin.append c c'`, with the set cut out by the two reindexings `Fin.castAdd` and `Fin.natAdd`. -/
theorem isPiSystem_cyl : IsPiSystem cyl := by
  rintro _ ⟨n, m, φ, c, E, hφ, hE, rfl⟩ _ ⟨n', m', φ', c', E', hφ', hE', rfl⟩ _
  have hL : Measurable fun w : (Fin (n + n') → ℝ) × (Fin (m + m') → ℝ) × ℂ =>
      ((fun i : Fin n => w.1 (Fin.castAdd n' i)), (fun k : Fin m => w.2.1 (Fin.castAdd m' k)), w.2.2) :=
    Measurable.prodMk (measurable_pi_iff.2 fun i => (measurable_pi_apply _).comp measurable_fst)
      (Measurable.prodMk (measurable_pi_iff.2 fun k =>
        (measurable_pi_apply _).comp (measurable_fst.comp measurable_snd)) (measurable_snd.comp measurable_snd))
  have hR : Measurable fun w : (Fin (n + n') → ℝ) × (Fin (m + m') → ℝ) × ℂ =>
      ((fun i : Fin n' => w.1 (Fin.natAdd n i)), (fun k : Fin m' => w.2.1 (Fin.natAdd m k)), w.2.2) :=
    Measurable.prodMk (measurable_pi_iff.2 fun i => (measurable_pi_apply _).comp measurable_fst)
      (Measurable.prodMk (measurable_pi_iff.2 fun k =>
        (measurable_pi_apply _).comp (measurable_fst.comp measurable_snd)) (measurable_snd.comp measurable_snd))
  refine ⟨n + n', m + m', Fin.append φ φ', Fin.append c c',
    (fun w : (Fin (n + n') → ℝ) × (Fin (m + m') → ℝ) × ℂ =>
        ((fun i : Fin n => w.1 (Fin.castAdd n' i)), (fun k : Fin m => w.2.1 (Fin.castAdd m' k)), w.2.2)) ⁻¹' E ∩
      (fun w : (Fin (n + n') → ℝ) × (Fin (m + m') → ℝ) × ℂ =>
        ((fun i : Fin n' => w.1 (Fin.natAdd n i)), (fun k : Fin m' => w.2.1 (Fin.natAdd m k)), w.2.2)) ⁻¹' E',
    ?_, ?_, ?_⟩
  · intro i
    refine Fin.addCases (motive := fun i => IsTestFunction Set.univ (Fin.append φ φ' i))
      (fun j => ?_) (fun j => ?_) i
    · rw [Fin.append_left]
      exact hφ j
    · rw [Fin.append_right]
      exact hφ' j
  · exact (hE.preimage hL).inter (hE'.preimage hR)
  · ext x
    simp [obs, Fin.append_left, Fin.append_right]

end HarmonicBalls.DMSJointPosCylinder

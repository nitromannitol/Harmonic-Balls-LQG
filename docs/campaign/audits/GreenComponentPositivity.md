# Green function positivity on a connected component

`greenFunction_pos_of_mem_connectedComponentIn` proves that for any bounded open `U ⊆ ℂ`, `z ∈ U`, and `x` in the connected component of `z` with `x ≠ z`, the actual `greenFunction U z x` is strictly positive. No positivity premise or additional literature input is used. This extends the ball positivity in Proposition 2.3 of the corrected paper (lines 480–485) to arbitrary bounded open sets and their components.

The proof uses the existing near-pole lower bound, symmetry, off-pole harmonicity, nonnegativity and the planar Harnack estimate. Positivity together with the pole forms an open set; the off-pole zero set is open by Harnack. Connectedness forces the pole's component into the first set. This avoids needing a separate punctured-connectedness theorem.

`greenFunction_pos_iff_mem_connectedComponentIn` gives the converse as well. `greenFunction_eq_zero_iff_not_mem_component_or_eq` explicitly characterizes the exterior, other-component and diagonal zeros. The zero diagonal is the Lean definition's convention; it differs from the infinite diagonal of the classical Green kernel and the printed positivity must be read off the diagonal for this real-valued representation. The potential-theoretic infrastructure uses work of Leonardo Bonanno.

The lock-free Lean check and module build passed. All three declarations print only `propext`, `Classical.choice`, and `Quot.sound`; no forbidden proof placeholders or heartbeat overrides occur.

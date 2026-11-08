# Green bounds on compact products

`exists_pos_bounds_greenFunction_compact_product` proves strictly positive uniform lower and finite upper bounds for the actual real-valued `greenFunction U z x` on `K × L`, for nonempty compact sets in a single connected component of a bounded open planar set. `Disjoint K L` explicitly excludes the diagonal. Each pair is interior and off diagonal, so the existing `continuousAt_greenFunction_uncurry` and `greenFunction_pos_of_mem_connectedComponentIn` apply; compact-product extrema give both bounds. No regularity at the boundary of `U` is assumed.

`exists_pos_lower_bound_integral_greenFunction_compact` integrates the lower bound against the restriction of any measure with finite nonzero mass on `L`. `exists_pos_lower_bound_greenPotential_of_ae_mem_compact` gives the corresponding full integral when the measure is concentrated on `L`. The positive bound is `c * μ.real L`. Integrability follows from continuity on `L` and finite mass; no independent integrability premise is imposed.

These are derived potential-theoretic helpers, not numbered-result closure claims or additional literature inputs. The corrected paper introduces the Green function and ball properties at `paper/lqg_harmonic_ball-corrected.tex:472` and `:480`; its infinite diagonal is distinct from the real-valued Lean convention, which is why disjointness matters. The potential-theoretic infrastructure uses work of Leonardo Bonanno.

The lock-free check and shared module build passed. Each declaration prints only `propext`, `Classical.choice`, and `Quot.sound`; the proof file contains no forbidden placeholders or heartbeat overrides.

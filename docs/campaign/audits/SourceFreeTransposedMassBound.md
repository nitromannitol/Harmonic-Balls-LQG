# Source-free transposed Green mass bound

`HarmonicBalls.Proofs.Potential.SourceFreeTransposedMassBound` proves a uniform bound for finite measures concentrated in `V \ U`, with the constant chosen independently of the measure. It uses `exists_uniform_bound_transposed_green_of_source_free`, applies the bound almost everywhere, and integrates it using `norm_integral_le_of_norm_le_const`. The latter also respects the totalized Bochner integral when the integrand is not integrable.

The convergence theorem combines this estimate with convergence of the total masses and the existing `harmonicOnNhd_transposed_greenIntegral_of_finite_source`. It gives an explicit uniform epsilon formulation on the compact set and retains harmonicity on `U` for every potential. Empty compact sets are included.

The potential-theoretic infrastructure is due to Leonardo Bonanno. No new literature inputs are introduced.

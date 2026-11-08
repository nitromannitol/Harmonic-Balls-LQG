# Observer Green adjoint dominated continuity

The finite-source Green adjoint has source-a.e. sequential continuity for uniformly bounded observer L∞ classes converging observer-a.e. The proof uses the integrable Green row from `green_row_bound_of_local_upper_growth` and dominated convergence, then applies dominated convergence again against an arbitrary source L¹ class. The source measure is finite, supported on V almost everywhere; V is an open subset of a bounded complex ball. Green rows retain the orientation `greenFunction V y x`.

`observer_green_adjoint_representative_dominated_continuity` permits arbitrary almost-everywhere representatives of the observer classes and source test. Countable intersections handle all sequence representatives simultaneously. It proves convergence of both orders of the actual mixed Green integrals, using the existing Green adjoint duality and integrability before subtracting integrals. No L∞ norm convergence or everywhere regularity is asserted. The potential-theoretic infrastructure uses work of Leonardo Bonanno.

The two declarations print only `propext`, `Classical.choice`, and `Quot.sound`. No new literature input is used; this is a helper for E51, not a numbered-result closure.

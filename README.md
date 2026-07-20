# Harmonic PDE Principles Formalization

This package contains the verified Lean development for:

- local constancy at an interior maximum;
- the two-dimensional disc mean-value bridge;
- boundary maximum propagation;
- harmonic comparison;
- Poisson-Dirichlet uniqueness on `closure U`.

The general-dimensional APIs are conditional on an explicit ball mean-value
provider. This is a formalization boundary, not a mathematical claim that
higher-dimensional harmonic functions lack the mean-value property.

The two-dimensional wrappers derive the provider from the complex-plane circle
mean-value theorem and polar coordinates.

The package currently expects the sibling project dependency at
`../.lake/packages/mathlib`, as configured in `lakefile.toml`.

Build from this directory with:

```text
lake build
```

`LocalMaximumBall-2.lean` is intentionally excluded because it contains an
older, incompatible maximum-attainment API.

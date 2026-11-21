# Weak-Head Normalizability of λenv and its Characterization by Intersection Types (Lean 4)

Lean 4 formalization accompanying the paper

> Shin-ya Nishizaki and Shogo Murasaki.
> *Weak-Head Normalizability of λenv and its Characterization by Intersection Types, Formalized in Isabelle/HOL.*

The paper's primary formalization is in Isabelle/HOL
(<https://github.com/nisizaki/lambda-env-weak-head-normalizability-intersection-types>). This repository contains a port of that
development to Lean 4: one Lean file per Isabelle theory, with the same definitions and
theorem names.

## Main results (`LambdaEnvWH/Final.lean` and others)

```lean
theorem lambda_env_WHN_characterization : (Typ M ↔ CFWHN M) ∧ (Typ M ↔ CFWHSN M)
theorem WHNF_unique : WhSteps M N1 → WHNF N1 → WhSteps M N2 → WHNF N2 → N1 = N2
theorem E1 : pure M → (lam_WHN (rb M dB.DVar) ↔ CFWHN M) ∧ (CFWHN M ↔ CFWHSN M)
theorem pure_characterization : pure M → (Typ M ↔ lam_WHN (rb M dB.DVar))
theorem classical_WHN : lam_WHN t ↔ ∃ Γ A, cty_of Γ t A ∧ cess A = true
theorem E2 : pure M → (Typ M ↔ ∃ Γ A, cty_of Γ (rb M dB.DVar) A ∧ cess A = true)
```

All 16 Isabelle theories are ported (one Lean file each, same names). There is no
`sorry` or `axiom`; `#print axioms` for the main theorems reports only `propext`,
`Classical.choice` and `Quot.sound`. `autoImplicit` is disabled.

## Adaptations

- Sets of terms are predicates (`t ∈ S` becomes `S t`); `rtranclp` is `Star`.
- `Id`, `Extn`, `Comp` are the constructors `iden`, `extn`, `comp`; the types `ty`, `sub`,
  `hasty` are `Ty`, `Sub` (`≼`), `Hasty` (`⊢`).
- In `Sub`, the rule `s_env` is a theorem; the constructor `s_env_core` splits its
  existential premise (equivalent because `map_of` is functional).
- `cess` and the flag of environment types are `Bool`-valued.
- `snf` (σ-normal form) uses `Classical.choose` instead of Isabelle's `SOME`.

## Building

Requires Lean 4 v4.33.1 (installed automatically by `elan` from `lean-toolchain`).
There are no dependencies beyond the Lean core library (no Mathlib).

```bash
lake build
```

To list the axioms used by a theorem, e.g.

```lean
import LambdaEnvWH
#print axioms LambdaEnvWH.lambda_env_WHN_characterization
```

## File layout

```
LambdaEnvWH.lean          root module (imports all files)
LambdaEnvWH/*.lean        the 16 files, one per Isabelle theory
lakefile.toml, lean-toolchain, lake-manifest.json
```

## Related repositories

- Isabelle/HOL original (primary formalization of the paper):
  <https://github.com/nisizaki/lambda-env-weak-head-normalizability-intersection-types>
- Call-by-value counterpart:
  <https://github.com/nisizaki/lambda-env-call-by-value-termination-intersection-types>
  (Isabelle/HOL) and
  <https://github.com/nisizaki/lambda-env-call-by-value-termination-intersection-types-lean>
  (Lean 4)
- The same questions for λpenv:
  <https://github.com/nisizaki/lambda-penv-weak-head-normalizability-intersection-types-lean>

## Authors

Shin-ya Nishizaki and Shogo Murasaki

## How to cite

Please cite the paper:

> Shin-ya Nishizaki and Shogo Murasaki.
> Weak-Head Normalizability of λenv and its Characterization by Intersection Types,
> Formalized in Isabelle/HOL.

## License

MIT License (see [LICENSE](LICENSE)).

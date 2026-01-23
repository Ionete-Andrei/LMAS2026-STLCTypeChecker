# STLC Type Inference, Verified in Lean 4

A formally verified type inference algorithm for the Simply Typed Lambda Calculus.

## File Structure

Single file: `STLCTypeChecker.lean`

## Main Definitions

| Name | Type | Description |
|------|------|-------------|
| `SimpleType` | inductive | Types: base types and arrow (function) types |
| `Term` | inductive | Lambda calculus terms: var, lam, app |
| `Context` | def | List of (variable, type) pairs |
| `WellTyped` | inductive | Predicate declaring when a term has a type |
| `inferType` | def | Algorithm that computes a term's type |

## Main Theorems

| Name | Statement | Meaning |
|------|-----------|---------|
| `inferType_sound` | `inferType ctx t = some τ → WellTyped ctx t τ` | If algorithm says yes, it's correct |
| `inferType_complete` | `WellTyped ctx t τ → inferType ctx t = some τ` | If well-typed, algorithm finds it |
| `inferType_correct` | `WellTyped ctx t τ ↔ inferType ctx t = some τ` | Algorithm is correct (biconditional) |

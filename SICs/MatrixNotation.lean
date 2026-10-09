/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import Mathlib.LinearAlgebra.Matrix.Defs

/-!
# Square matrix notation

The notation `Mat(n, R)` for square `n × n` matrices over `R`.

This complements Mathlib's `SL(n, R)` and `GL(n, R)` notation in the `MatrixGroups` scope while
remaining definitionally equal to `Matrix (Fin n) (Fin n) R`.
-/

/-- `Mat(n, R)` is the type of `n × n` matrices over `R`. -/
scoped[MatrixGroups] notation "Mat(" n ", " R ")" => Matrix (Fin n) (Fin n) R

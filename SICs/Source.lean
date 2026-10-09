/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import Lean

/-!
# Source Statements

The `@[source]` attribute naming the source statement a declaration is the primary formalization
of.

This module registers the attribute. Each source reference is one human-readable string,
`KEY, PRINTED_ITEM[, p. PRINTED_PAGE], TEX_LABEL[ (SCOPE)]` for a source whose LaTeX source is
pinned, and `KEY, PRINTED_ITEM, p. PRINTED_PAGE[ (SCOPE)]` for a source available only as a PDF.
A declaration tagged `@[source "AFK25, Theorem 2.20, p. 34, thm:field0"]` is the project's most
faithful formalization of Theorem 2.20 of [AFK25], printed on page 34 and carrying the LaTeX label
`thm:field0`; a statement of another arXiv reference is named by its bibliography number, as
`"72, Lemma 2.3, p. 13, lem:ell"` for [72, Kopp (2024), Lemma 2.3, `lem:ell`], and a statement of
a source outside that bibliography by its project-local key of capital letters and a two-digit
year, as `"RW26, equation (58), p. 28, eq:q-binomial-series"` for [RW26, Radchenko, Wheeler
(2026), equation (58), `eq:q-binomial-series`]. A source with no LaTeX label is cited by its
printed item and page alone, as `"95, Proposition 5, p. 181"`. When a statement is formalized
clause by clause, each clause has its own primary and the clause is appended in parentheses after
one space, as `"AFK25, Theorem 2.20, p. 34, thm:field0 (1)"` or
`"95, Proposition 5, p. 181 (product identity)"`; a declaration that formalizes several
statements lists several strings. The optional `(symbol := "…")` records the paper's notation for
a definition, mapping the paper's symbol to the Lean name. Exactly one public
declaration carries each source reference, and its docstring cites the same statement.

Derived declarations (unfolding lemmas, specializations, consequences) keep their prose citation
and carry no tag. The tag says only what a declaration formalizes.
-/

namespace SIC

open Lean

/-- The data of one `@[source]` tag: the source references, each
`KEY, PRINTED_ITEM[, p. PRINTED_PAGE], TEX_LABEL[ (SCOPE)]` or
`KEY, PRINTED_ITEM, p. PRINTED_PAGE[ (SCOPE)]`, of the statements the declaration is the primary
formalization of, and the paper's notation for it when it is a definition. -/
structure SourceTag where
  /-- The source references, each `KEY, PRINTED_ITEM[, p. PRINTED_PAGE], TEX_LABEL[ (SCOPE)]` or
  `KEY, PRINTED_ITEM, p. PRINTED_PAGE[ (SCOPE)]` with `KEY` the citation key `AFK25`, a
  bibliography number, or a project-local key such as `RW26`. -/
  labels : Array String
  /-- The paper's symbol for the object defined, when the declaration is a definition. -/
  symbol : Option String := none

/-- The empty tag, which `ParametricAttribute` requires as a default. -/
instance : Inhabited SourceTag := ⟨{ labels := #[] }⟩

/-- `@[source "AFK25, Theorem 2.20, p. 34, thm:field0" "72, Theorem 1.3, p. 8, thm:field (1)"
(symbol := "ש^r_A(β)")]`: one or more source references, then optionally the paper's symbol. -/
syntax (name := source) "source" (ppSpace str)+ (" (" &"symbol" " := " str ")")? : attr

/-- Read the source references and the optional symbol out of the attribute syntax. Each
reference must start with a citation key followed by `, ` and a printed item; the remaining
fields are kept as written. -/
def SourceTag.ofSyntax (stx : Syntax) : AttrM SourceTag := do
  let some labels := (stx[1].getArgs.mapM fun s => s.isStrLit?)
    | throwError "@[source] expects string literals \"KEY, PRINTED_ITEM, p. PAGE[, TEX_LABEL]\""
  if labels.isEmpty then throwError "@[source] expects at least one source reference"
  for label in labels do
    let fields := label.splitOn ", "
    let key := fields.headD ""
    if fields.length < 2 || key.isEmpty || !key.all Char.isAlphanum
        || (fields.getD 1 "").isEmpty then
      throwError "@[source] reference `{label}` is not of the form \
        \"KEY, PRINTED_ITEM[, p. PRINTED_PAGE], TEX_LABEL[ (SCOPE)]\" or \
        \"KEY, PRINTED_ITEM, p. PRINTED_PAGE[ (SCOPE)]\""
  let symbol := if stx[2].getNumArgs == 0 then none else stx[2][3].isStrLit?
  return { labels, symbol }

/-- The parametric attribute backing `@[source]`; read a declaration's tag with
`sourceAttr.getParam? env name`. -/
initialize sourceAttr : ParametricAttribute SourceTag ←
  registerParametricAttribute {
    name := `source
    descr := "Names the source statement of which the declaration is the primary formalization."
    getParam := fun _ stx => SourceTag.ofSyntax stx }

end SIC

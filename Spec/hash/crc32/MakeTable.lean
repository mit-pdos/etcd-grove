/-
`crc32.MakeTable(crc32.Castagnoli)` (`crc32.go:122-133`): the package's `castagnoliTable`, after
`castagnoliInitOnce()`, a table holding the Castagnoli table, read-only for good. Proved in
`Proof/hash/crc32/MakeTable.lean`. Lean-first. (crc32-hooks2, 2026-11-22: translated with its body,
etcd-grove#14, until then trusted; hence the premise `isPkgInit hash/crc32`, the package state its
code reads.)
-/
module

public import Proof.hash.crc32.PkgInit

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [hash.crc32.Assumptions]

/-- See the file header. -/
abbrev hash.crc32.MakeTable.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.hash.crc32 }}
    (App (Val (@! hash.crc32.MakeTable)) (Val #hash.crc32.castagnoliPoly))
  {{ (tab : Loc), RET #tab; tab ↦□ hash.crc32.castagnoliTableArr }}

end spec

end EtcdGrove
end Perennial

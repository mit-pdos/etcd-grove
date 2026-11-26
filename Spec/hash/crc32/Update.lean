/-
`crc32.Update(crc, tab, p)` with `tab` a Castagnoli table (`hash/crc32`, translated, its arch
hooks the Go model `models/hash/crc32/model.go`): `crc32c crc p`; `p` is only read, at any fraction, and the
table is read-only for good. Proved in `Proof/hash/crc32/Update.lean`, over `update`'s
(`Update` translated since 2026-11-21, `update(crc, tab, p, true)`; until then it was
the trusted function). Lean-first. (crc32-hooks2, 2026-11-22: `update` translated with its body,
etcd-grove#14; hence the premise `isPkgInit hash/crc32`, the package state it reads.)
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
abbrev hash.crc32.Update.spec : Prop :=
  ∀ (c : w32) (tab : Loc) (s : GoSlice) (bs : List w8) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.hash.crc32 ∗ tab ↦□ hash.crc32.castagnoliTableArr ∗
      s ↦*{dq} bs }}
    (App (App (App (Val (@! hash.crc32.Update)) (Val #c)) (Val #tab)) (Val #s))
  {{ RET #(hash.crc32.crc32c c bs); s ↦*{dq} bs }}

end spec

end EtcdGrove
end Perennial

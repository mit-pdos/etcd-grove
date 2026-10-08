/-
Port of `election_proof/spec_unstable__nextEntries.v` (857d09190).
-/
import EtcdGrove.Raft.InvReadylog

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `u.nextEntries()` (`log_unstable.go:96`, `unstable.nextEntries.impl`):

    inProgress := int(u.offsetInProgress - u.offset)
    if len(u.entries) == inProgress { return nil }
    return u.entries[inProgress:]

The entries not yet in progress, **read-only and uncapped**: the result shares
`u.entries`' slack (notes/todo.md, "nextUnstableEnts returns an uncapped slice"), so only
its elements are handed out. The premise is `ownRaftLog`'s `Hipb`: below `offset` the
`int` conversion would go negative, past the end the re-slice would panic. -/
abbrev unstable.nextEntries.spec : Prop :=
  ∀ (u : Loc) (us : UnstableSt),
  uint.Z us.offset ≤ uint.Z us.inprogress ∧
    uint.Z us.inprogress ≤ uint.Z us.offset + (us.ents.length : Int) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hun" ∷ ownUnstable u us }}
    (App (Val (u @!! go.GoType.PointerType unstable.ty @!! go!"nextEntries")) (Val #()))
  {{ (s : GoSlice), RET #s;
      ownUnstable u us ∗
      s ↦*□ us.ents.drop (uint.Z us.inprogress - uint.Z us.offset).toNat }}

end spec

end EtcdGrove
end Perennial

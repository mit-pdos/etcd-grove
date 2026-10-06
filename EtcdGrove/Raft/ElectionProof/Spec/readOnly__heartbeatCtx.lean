/- Port of election_proof/spec_readOnly__heartbeatCtx.v (feb5c73d4).

Lean notes: Rocq's `u64_le` is `u64Le`, `own_slice_cap w8 sl (DfracOwn 1)` is
`ownSliceCap w8 sl (DFrac.own 1)`.
-/
import EtcdGrove.Raft.ElectionProof.InvRaftPhys

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

/-- `ro.heartbeatCtx()` (`readOnly.heartbeatCtx.impl`,
`Perennial/Code/go_etcd_io/raft/v3.lean`; `read_only.go:93`):

    if len(ro.unconfirmedReads) == 0 { return nil }
    pos := ro.confirmedReads + uint64(len(ro.unconfirmedReads))
    enc := make([]byte, 8)
    binary.LittleEndian.PutUint64(enc, pos)
    return enc

No panic. With no pending request the result is `nil` -- under the phase-1 scope
(`ownRaftMisc`'s `pending = []`) always, which is what `bcastHeartbeat` relies on.
Otherwise a fresh eight-byte slice, fully owned, holding `readonlyPosition r`
little-endian (`u64Le`). The object is unchanged. The receiver is a pointer and the
body reads `ro.unconfirmedReads` through it, so the spec owns the object. -/
abbrev readOnly.heartbeatCtx.spec : Prop :=
  ∀ (ro : Loc) (r : ReadOnly),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ "Hown" ∷ ownReadOnly ro r }}
    (App (Val (ro @!! go.GoType.PointerType readOnly.ty @!! go!"heartbeatCtx")) (Val #()))
  {{ (sl : GoSlice), RET #sl;
      ownReadOnly ro r ∗
      (⌜r.pending = [] ∧ sl = slice.nil⌝ ∨
       ⌜r.pending ≠ []⌝ ∗
       sl ↦* u64Le (readonlyPosition r) ∗
       ownSliceCap w8 sl (DFrac.own 1)) }}

end spec

end EtcdGrove
end Perennial

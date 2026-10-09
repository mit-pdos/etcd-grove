/-
Port of election_proof/spec_readOnly__recvAck.v (feb5c73d4).

Lean notes:
* The Rocq binder `from` is `src` (`from` is a Lean keyword). `readonly.t`,
  `own_ReadOnly`, `readonly_recvAck`, `readonly_position` are `ReadOnly`,
  `ownReadOnly`, `readonlyRecvAck`, `readonlyPosition` (`InvMisc.lean`).
* The reference `readOnly__recvAckⁱᵐᵖˡ, new/code/go_etcd_io/raft/v3.v:6267` is to the
  Lean generated code `readOnly.recvAck.impl`.
-/
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `ro.recvAck(from, ctx)` (`readOnly.recvAck.impl`; `read_only.go:65`):

    if len(ctx) != 0 {
        ro.acks[from] = max(ro.acks[from], binary.LittleEndian.Uint64(ctx))
    }

The context is a heartbeat's: the first eight bytes, little-endian, are a *position*
(`readonlyPosition` of the leader when it sent the heartbeat), and the voter's ack
becomes the larger of that and its old one (`readonlyRecvAck`). A non-empty context
shorter than eight bytes makes `Uint64` panic (index out of range); a peer's `Context`
can be anything, and nothing in the state excludes it, so the spec takes
`cs = [] ∨ 8 ≤ length cs` as a premise (the smallest one). The context slice is only
read, at any fraction. -/
abbrev readOnly.recvAck.spec : Prop :=
  ∀ (ro : Loc) (r : ReadOnly) (src : w64) (ctx : GoSlice) (cs : List w8) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ "Hown" ∷ ownReadOnly ro r ∗
      "Hctx" ∷ ctx ↦*{dq} cs ∗ "%Hlen" ∷ ⌜cs = [] ∨ 8 ≤ cs.length⌝ }}
    (App (App (Val (ro @!! go.GoType.PointerType readOnly.ty @!! go!"recvAck"))
      (Val #src)) (Val #ctx))
  {{ RET #(); ownReadOnly ro (readonlyRecvAck r src cs) ∗ ctx ↦*{dq} cs }}

end spec

end EtcdGrove
end Perennial

/- Lean-first (no Rocq counterpart).

## `node.ReadIndex(ctx, rctx)` (node.go:608), a linearizable read's request (2026-10-13)

`step` of `pb.Message{Type: MsgReadIndex, Entries: []pb.Entry{{Data: rctx}}}`, from any
goroutine: the request goes onto `recvc` (`netP`), and `run` steps it as
`RawNode.ReadIndex` does. Specified for `context.Background()`. What the client supplies is
as for `RawNode.ReadIndex` (`Spec/RawNode__ReadIndex.lean`): its context's slice recorded
(`isPropData`, `node_read_register`), the context's fresh token (`rdFresh`), its persistent
atomic update (`readAu`, 2026-10-14, stage R), a committed log it knows (`L0`) and one read
credit; any number of voters. The update is deposited at the start, on the caller's goroutine
(`node_read_deposit`), before the request goes onto `recvc`: the client gets the request's
record `readReq γ c Lc` -- `Lc` the global committed log at the deposit, extending `L0` -- and
its handle `isRead γ c Qr`, whatever the error. The answer is a `ReadState` a later `Ready`
hands out (`readyData`), from which the client reads `readOk` of its read
(`node_readState_data`), the witness `readWit γ c Qr i` with its handle, and the update's
results (`node_read_collect`). The error says only whether the request reached `run`; a
dropped request leaves the update deposited, firing harmlessly, with no `ReadState` naming it.

raft v3.7 (2026-10-16, stage R5, D6): a read context is its bytes (`readStateOk` over
`ReadStateM`); the client supplies `rctx ↦*□ c` (the request's entry holds the slice read-only)
rather than the proposed slice.
-/
module

public import Raft37.Proof.go_etcd_io.raft.v3.InvNode
public import Perennial.Proof.context

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- See the file header. -/
abbrev node.ReadIndex.spec : Prop :=
  ∀ (γ : NodeNames) (id : w64) (n : Loc) (rctx : GoSlice) (c : List w8)
    (Qr : List EntryM → IProp GF) (L0 : List EntryM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode γ id n ∗
      -- (2026-10-16, stage R5, D6) the context's bytes, read-only (until then `isPropData γ.raft
      -- rctx c`)
      rctx ↦*□ c ∗ rdFresh γ.raft c ∗ readAu γ.raft Qr ∗
      isCommitted γ.raft L0 ∗ rdCred γ.raft 1 }}
    (App (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"ReadIndex"))
      (Val #(interface.ok context.backgroundCtxVal))) (Val #rctx))
  {{ (err : GoInterface), RET #err;
      ∃ Lc, ⌜L0 <+: Lc⌝ ∗ readReq γ.raft c Lc ∗ isRead γ.raft c Qr }}

end spec

end EtcdGrove
end Perennial

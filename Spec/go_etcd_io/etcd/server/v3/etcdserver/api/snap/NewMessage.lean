/-
`snap.NewMessage(rs, rc, rcSize)` (`server/etcdserver/api/snap/message.go`): the snapshot
message rafthttp's snapshot sender streams, `rs` (the raft message) followed by `rc` (the
database). Lean-first (no Rocq counterpart); branch `pr-verify/etcd-21569`.

At the base (`goose-lean` 09669450f) the message's `ReadCloser` is an exact reader over `rc`
(`ioutil.NewExactReadCloser(rc, rcSize)`): its reads fail (`ErrShortRead`) if `rc` ends before
`rcSize` bytes, or (`ErrExpectEOF`) if it goes past (`exactReadCloser.Read.spec`).
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.ioutil.Defs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseApply
public import Proof.go_etcd_io.raft.v3.InvPb

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.etcd.pkg.v3 go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

/-- **The base's `NewMessage(rs, rc, rcSize)`**: a new `*Message` holding `rs`, an exact reader
`e` over `rc` of `rcSize` bytes (nothing read yet), the total size `proto.Size(rs) + rcSize` and
a new channel of capacity 1. -/
abbrev snap.NewMessage.spec : Prop :=
  ∀ (rs : Loc) (dq : DFrac) (ms : MsgSt) (rc : GoInterface) (rcSize : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.snap ∗
      msgOwn rs dq ms }}
    (App (App (App (Val (@! snap.NewMessage)) (Val #rs)) (Val #rc)) (Val #rcSize))
  {{ (m : Loc), RET #m; ∃ (e : Loc) (sz : w64) (ch : Loc) (γ : ChanNames),
      m ↦ (snap.Message.mk rs (interface.mkOk (go.GoType.PointerType ioutil.exactReadCloser.ty) #e)
        (sz + rcSize) ch) ∗
      e ↦ (ioutil.exactReadCloser.mk rc 0 rcSize) ∗
      msgOwn rs dq ms ∗ ⌜0 ≤ sint.Z sz⌝ ∗
      isChan ch γ Bool ∗ ⌜γ.chanCap = W64 1⌝ ∗ ownChan γ Bool (ChanState.Buffered []) }}

end spec

end EtcdGrove
end Perennial

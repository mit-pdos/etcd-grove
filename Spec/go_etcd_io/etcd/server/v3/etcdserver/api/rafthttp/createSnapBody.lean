/-
`createSnapBody(lg, merged)` (`snapshot_sender.go`; rafthttp stage 7d, D42). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Snapshot
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Defs
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvSnapshot

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`createSnapBody(lg, merged)`** of a merged message of the frozen raft message `st` (which
marshals) and a reader of complete streams in `Φ`: the snapshot's body, a reader of the stream of
the envelope's frame (of an encoding `bs` of `st`) followed by a complete stream of the merged
message's reader (`snapPre`, `snapPhi`), whose `Close` returns (it closes the merged message's
reader). The encoding into a `bytes.Buffer` does not fail, so its `lg.Panic` is not reached. -/
abbrev rafthttp.createSnapBody.spec : Prop :=
  ∀ (lg m ml : Loc) (rc : GoInterface) (st : MsgSt) (Φ : List w8 → Prop),
  lg ≠ null → MsgMarshals st →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
      snap.msgIs m ml rc ∗ msgOwn ml DFrac.discard st ∗ backend.readerStreams rc Φ }}
    (App (App (Val (@! rafthttp.createSnapBody)) (Val #lg)) (Val #m))
  {{ (body : GoInterface), RET #body; ∃ (bs : List w8) (bi : GoInterfaceOk),
      ⌜body = GoInterface.ok bi ∧ MsgWireOk st bs ∧ bs.length < 2 ^ 63⌝ ∗
      http.streamHas body (snapPre bs) (snapPhi bs Φ) ∗ rdCloseOk bi }}

end spec

end EtcdGrove
end Perennial

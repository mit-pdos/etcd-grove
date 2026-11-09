/-
## `createSnapBody(lg, merged)`

**Users.** `snapshotSender.send`.

**Proof sketch.** `bytes.Buffer`, `messageEncoder.encode` into it (`writerAt` of a buffer: anything; an encoding cannot fail, else `lg.Panic`), then `Http.NewBuffer_reader`-like knowledge of the frame, `dbReader_readerAt.spec` of `rc`, `Http.MultiReader_reader.spec` (complete streams: the frame then a stream of `img`), `ReaderAndCloser` (pkg/v3/ioutil: the same reader).

**Changes.** Restated over the new vocabulary (was over `specs-ref`'s `TransportState`/`TransportInv` records, `NetNames`, `netBundle`); same behaviour.

**Margin.** None.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Rafthttp

open Iris Iris.BI Raft
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- (internal) **The snapshot request's body**: the envelope frame of the raft message, then the database reader. -/
def createSnapBody.spec : Prop :=
  ∀ (lg : Loc) (ν : Net GF) (mp ml : Loc) (rc : GoInterface) (dq : DFrac) (m : Msg) (s : Snapshot) (img : Snap.BeImage),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ (⌜lg = null⌝ ∨ Zap.isLogger lg) ∗ snapMsgOwn mp ml rc ∗ msgPts ml dq m ∗ ⌜m.type = MsgSnap ∧ m.snapshot = some s⌝ ∗ Snap.dbReader rc img ∗ snapImg ν s.index img }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.createSnapBody)) (Val #lg)) (Val #mp))
  {{ (bd : GoInterface), RET #bd; msgPts ml dq m ∗ snapBodyAt bd ν m }}

end spec
end Rafthttp
end EtcdGrove
end Perennial

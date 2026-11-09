/-
## `createSnapBody(lg, merged)`

**Users.** `snapshotSender.send`.

**Proof sketch.** `bytes.Buffer`, `messageEncoder.encode` into it (`writerAt` of a buffer: anything; an encoding cannot fail, else `lg.Panic`), `io.MultiReader`, `ReaderAndCloser` (pkg/v3/ioutil).

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
  ∀ (lg : Loc) (ν : Net) (mp ml : Loc) (rc : GoInterface) (dq : DFrac) (m : Msg) (s : Snapshot),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ (⌜lg = null⌝ ∨ Zap.isLogger lg) ∗ snapMsgOwn mp ml rc ∗ msgPts ml dq m ∗ ⌜m.type = MsgSnap ∧ m.snapshot = some s⌝ ∗ Http.readerAt rc (fun _ => iprop(True)) (fun bs => iprop(□ snapImg ν s.index bs)) [] }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.createSnapBody)) (Val #lg)) (Val #mp))
  {{ (bd : GoInterface), RET #bd; snapMsgOwn mp ml rc ∗ msgPts ml dq m ∗ snapBodyAt bd ν m }}

end spec
end Rafthttp
end EtcdGrove
end Perennial

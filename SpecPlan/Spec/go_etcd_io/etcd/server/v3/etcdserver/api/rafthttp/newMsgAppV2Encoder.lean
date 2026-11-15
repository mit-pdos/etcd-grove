/-
## `newMsgAppV2Encoder(w, fs)`

**Users.** `streamWriter.run`.

**Proof sketch.** The literal and its buffers.

**Changes.** Restated over the new vocabulary (was over `specs-ref`'s `TransportState`/`TransportInv` records, `NetNames`, `netBundle`); same behaviour.

**Margin.** `src`, `dst` are ghost (the frames' meaning).
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Api

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

/-- (internal) A msgappv2 encoder on `w` for the stream from `src` to `dst`, at the initial state. -/
def newMsgAppV2Encoder.spec : Prop :=
  ∀ (w : GoInterface) (fs : Loc) (src dst : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ followerStatsOk fs }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.newMsgAppV2Encoder)) (Val #w)) (Val #fs))
  {{ (enc : Loc), RET #enc; v2EncAt enc w src dst (W64 0, W64 0) }}

end spec
end Rafthttp
end EtcdGrove
end Perennial

/-
## `startRemote(tr, urls, id)`

**Users.** `Transport.AddRemote`.

**Proof sketch.** `newURLPicker`, `newPeerStatus`, the pipeline literal and `start`.

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

/-- (internal) **Starts a remote** (a pipeline only) for `pid`. -/
def startRemote.spec : Prop :=
  ∀ (t : Loc) (ν : Net GF) (lid pid : w64) (urls : GoSlice) (hs : List GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ isTransport t ν lid ∗ Types.urlsAt urls hs ∗ ⌜hs ≠ []⌝ ∗ ([∗list] a ∈ hs, peerAddr ν a) }}
    (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.startRemote)) (Val #t)) (Val #urls)) (Val #pid))
  {{ (g : Loc), RET #g; remoteAt g ν lid pid ∗ remoteStopRight g }}

end spec
end Rafthttp
end EtcdGrove
end Perennial

/-
## `checkStreamSupport(v, t)`

**Users.** `streamReader.dial`.

**Proof sketch.** `semver.New`, `String`, a map read (`supportedStream`'s initializer: a fact of the package's init).

**Changes.** Restated over the new vocabulary (was over `specs-ref`'s `TransportState`/`TransportInv` records, `NetNames`, `netBundle`); same behaviour.

**Margin.** None.
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

/-- (internal) Whether a version supports the stream type (`supportedStream`). -/
def checkStreamSupport.spec : Prop :=
  ∀ (v : Loc) (t : StreamTy),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ semverAt v }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.checkStreamSupport)) (Val #v)) (Val #(t.str)))
  {{ (b : Bool), RET #b; True }}

end spec
end Rafthttp
end EtcdGrove
end Perennial

/-
## `newPipelineHandler(t, r, cid)`

**Users.** `Transport.Handler`.

**Proof sketch.** The literal (`zap.NewNop()` for a `nil` logger).

**Changes.** Restated over the new vocabulary (was over `specs-ref`'s `TransportState`/`TransportInv` records, `NetNames`, `netBundle`); same behaviour.

**Margin.** The cluster id is not tracked (a mismatch only refuses requests).
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

/-- (internal) The pipeline handler of the transport (its `Raft` the transport's). -/
def newPipelineHandler.spec : Prop :=
  ∀ (t : Loc) (ν : Net GF) (lid : w64) (r : GoInterface) (cid : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ isTransport t ν lid ∗ raftOk ν lid r }}
    (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.newPipelineHandler)) (Val #t)) (Val #r)) (Val #cid))
  {{ (h : GoInterface), RET #h; ∃ hp : Loc, ⌜h = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.pipelineHandler.ty) #hp⌝ ∗ phAt hp ν lid }}

end spec
end Rafthttp
end EtcdGrove
end Perennial

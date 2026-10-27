/-
`(*Transport).Handler()` (`transport.go`; rafthttp stage 6c, its statement over the transport's
state in 6d, 2026-10-24). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.TransportState

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`t.Handler()`** on a frozen transport whose recorded peers cover every other member of the
network (a static cluster's, all added before the freeze), of the member owning the address `a`:
a handler of `a` for the raft protocol (`raftProto`), lending each invocation an `R` and one of
the lock's reader tokens. A mux of the pipeline handler (`/raft`), the stream handler
(`/raft/stream/`), the snapshot handler (`/raft/snapshot`, the snapshot stream's axiom) and the
prober's (`/raft/probing`). -/
abbrev rafthttp.Transport.Handler.spec : Prop :=
  ∀ (γn : NetNames GF) (t : Loc) (c : TrN GF) (rs : trIds) (a : GoString),
  (netRh γn).owner a = c.lid → (∀ f, (netRh γn).member f → f ≠ c.lid → f ∈ rs) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
      trFrozen γn t c rs }}
    (App (Val (t @!! go.GoType.PointerType rafthttp.Transport.ty @!! go!"Handler")) (Val #()))
  {{ (h : GoInterface), RET #h;
      http.handlerOk (raftHttpNet (netRh γn)) a iprop(c.R ∗ trTok γn t c) h }}

end spec

end EtcdGrove
end Perennial

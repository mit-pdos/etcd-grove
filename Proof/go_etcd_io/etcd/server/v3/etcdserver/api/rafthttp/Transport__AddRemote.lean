/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/Transport__AddRemote.lean`: `(*rafthttp.Transport).AddRemote(id, urls)`, over its
callees' specs (`rafthttp.Transport.AddRemote_ok`, `TransportSpecs.lean`; rafthttp stage 6f, 2026-10-24).
Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport__AddRemote
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.NewURLs
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.startRemote
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.ID__String_ptr
public import Spec.go_uber_org.zap.Logger__Info
public import Spec.go_uber_org.zap.String
public import Spec.go_uber_org.zap.Strings
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.TransportSpecs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Assumptions]

theorem rafthttp.Transport.AddRemote.wp_proof
    (hNewURLs : types.NewURLs.spec (GF := GF) (hG := hG))
    (hStartRemote : rafthttp.startRemote.spec (GF := GF) (hG := hG))
    (hIDStringPtr : types.ID.String_ptr.spec (GF := GF) (hG := hG))
    (hInfo : zap.Logger.Info.spec (GF := GF) (hG := hG))
    (hZString : zap.String.spec (GF := GF) (hG := hG))
    (hZStrings : zap.Strings.spec (GF := GF) (hG := hG)) :
    rafthttp.Transport.AddRemote.spec (GF := GF) (hG := hG) :=
  rafthttp.Transport.AddRemote_ok hNewURLs hStartRemote hIDStringPtr hInfo hZString hZStrings

end proof

end EtcdGrove
end Perennial

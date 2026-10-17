/-
Trust boundary: `etcdserver.NewServerVersionAdapter` (an axiom; see `Spec/go_etcd_io/etcd/server/v3/etcdserver/NewServerVersionAdapter.lean`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.NewServerVersionAdapter

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **Trust boundary** (item 4, the server start): its body is `return
&serverVersionAdapter{EtcdServer: s}`: an allocation, reading nothing (the function is not
translated with its body: `etcdserver.toml`, the server's). -/
axiom etcdserver.NewServerVersionAdapter.wp_proof : etcdserver.NewServerVersionAdapter.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial

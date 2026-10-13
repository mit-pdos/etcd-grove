/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__NextRequestID.lean`. Lean-first (no Rocq
counterpart); the request path's unit 4b (2026-10-13).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__NextRequestID
public import Spec.go_etcd_io.etcd.pkg.v3.idutil.Generator__Next

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem EtcdServer.NextRequestID.wp_proof
    (hNext : idutil.Generator.Next.spec (GF := GF) (hG := hG)) :
    EtcdServer.NextRequestID.spec (GF := GF) (hG := hG) := by
  intro s g γi
  wp_start as ⟨#Hf, #Hg, Hc⟩
  ihave #Pi : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.idutil $$ []
  · iPkgInit
  wp_auto
  wp_apply hNext γi g $$ [Hc] as %id ⟨Hfr, -⟩
  · iframe #; iframe Hc
  iapply HΦ
  iexact Hfr

end proof

end EtcdGrove
end Perennial

/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__RequestID.lean`. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__RequestID
public import Spec.go_etcd_io.etcd.pkg.v3.idutil.Generator__Next

@[expose] public section

set_option linter.unusedSectionVars false

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

theorem EtcdServer.RequestID.wp_proof
    (hNext : idutil.Generator.Next.spec (GF := GF) (hG := hG)) :
    EtcdServer.RequestID.spec (GF := GF) (hG := hG) := by
  intro s γi
  wp_start as ⟨#Hg, Hcred⟩
  iunfold srvIdGen at Hg
  icases Hg with ⟨%gen, %Q, #Hgen, #Hid⟩
  wp_auto
  ihave #Hpkg_id : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.idutil $$ []
  · iPkgInit
  wp_apply hNext γi gen Q $$ [Hcred] as %id ⟨Hfresh, -⟩
  · iframe #; iframe Hcred
  iapply HΦ
  iexact Hfresh

end proof

end EtcdGrove
end Perennial

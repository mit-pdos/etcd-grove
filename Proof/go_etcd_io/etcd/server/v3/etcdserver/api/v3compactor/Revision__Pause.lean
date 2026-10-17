/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3compactor/Revision__Pause.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Revision__Pause

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Assumptions]

theorem v3compactor.Revision.Pause.wp_proof :
    v3compactor.Revision.Pause.spec (GF := GF) (hG := hG) := by
  intro rc P
  wp_start as #Hrc
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold isRevision at Hrc
  icases Hrc with ⟨-, -, -, -, -, -, -, #Hmu⟩
  wp_auto
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HR⟩
  iunfold rvLockInv at HR
  icases HR with ⟨%b, Hp⟩
  wp_auto
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hp]
  · inext
    iunfold rvLockInv
    iexists _
    iframe
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial

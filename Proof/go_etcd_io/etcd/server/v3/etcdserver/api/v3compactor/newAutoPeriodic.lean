/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3compactor/newAutoPeriodic.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.newAutoPeriodic

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
variable [package_sem_ctx : context.Assumptions]

theorem v3compactor.newAutoPeriodic.wp_proof :
    v3compactor.newAutoPeriodic.spec (GF := GF) (hG := hG) := by
  intro P
  wp_start as Hcci
  iapply wp_fupd
  ihave #Hctxp : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  wp_auto
  iStructNamedPrefix «$r0» "A"
  imod sync.init_Mutex (apLockInv «$r0_ptr») ⊤ (apMuAddr «$r0_ptr») $$ Amu [Apaused] with #Hmu
  · inext
    iunfold apLockInv
    iexists _
    iframe
  wp_apply context.wp_Background
  wp_apply context.wp_WithCancel_Background iprop(True) $$ [$Hctxp $Hcci]
    as %ictx %γi %cancel ⟨#Hcancel, #Hictx, #Hcc⟩
  ihave #Hcancel' : context.cancelSpec (GF := GF) cancel γi iprop(True) $$ [Hcancel]
  · iunfold context.cancelSpec; iexact Hcancel
  ipersist Alg
  ipersist Aclock
  ipersist Aretention
  ipersist AmaxBytes
  ipersist Arg
  ipersist Ac
  ipersist Asg
  ipersist Actx
  ipersist Acancel
  imodintro
  iapply HΦ
  iunfold isAutoPeriodic
  iframe #

end proof

end EtcdGrove
end Perennial

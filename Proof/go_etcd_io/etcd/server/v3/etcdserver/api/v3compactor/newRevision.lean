/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3compactor/newRevision.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.newRevision

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
theorem v3compactor.newRevision.wp_proof :
    v3compactor.newRevision.spec (GF := GF) (hG := hG) := by
  intro lg clk retention interval rg c
  unfold rvInterval
  by_cases hi : interval = W64 0 <;> simp only [hi, ↓reduceIte]
  all_goals
    haveI : go.NotInterface go.int64 := ⟨by unfold go.int64; trivial⟩
    wp_start as Hcci
    iapply wp_fupd
    ihave #Hctxp : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
    · iPkgInit
    wp_auto
    try simp only [_root_.Perennial.time.Minute]
    try wp_auto
    try simp only [hi, decide_false]
    try wp_auto
    all_goals try (exfalso; simp_all; done)
    all_goals
      try rw [show (W64 60000000000 * W64 5 : w64) = W64 300000000000 from rfl]
      iStructNamedPrefix «$r0» "A"
      imod sync.init_Mutex (rvLockInv «$r0_ptr») ⊤ (rvMuAddr «$r0_ptr») $$ Amu [Apaused] with #Hmu
      · inext
        iunfold rvLockInv
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
      ipersist Ainterval
      ipersist Arg
      ipersist Ac
      ipersist Actx
      ipersist Acancel
      imodintro
      iapply HΦ
      iunfold isRevision
      iunfold cancellableCtxAt
      iframe #

end proof

end EtcdGrove
end Perennial

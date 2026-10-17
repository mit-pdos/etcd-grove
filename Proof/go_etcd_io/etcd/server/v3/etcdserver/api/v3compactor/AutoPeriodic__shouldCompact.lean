/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3compactor/AutoPeriodic__shouldCompact.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.AutoPeriodic__shouldCompact
public import Spec.time.Duration__Seconds_ptr

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

theorem v3compactor.AutoPeriodic.shouldCompact.wp_proof
    (wp_Seconds_ptr : time.Duration.Seconds_ptr.spec (GF := GF) (hG := hG)) :
    v3compactor.AutoPeriodic.shouldCompact.spec (GF := GF) (hG := hG) := by
  intro ac P tv size rate
  wp_start as ⟨#Hac, #Htv⟩
  ihave #Htime : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  iunfold isAutoPeriodic at Hac
  icases Hac with ⟨-, -, -, #Hmb, -, -, -, -, -⟩
  iunfold apTuning at Htv
  icases Htv with ⟨#Hhw, -, #Hlt, -, -⟩
  wp_auto
  wp_apply wp_Seconds_ptr $$ [$Hlt] as %secs -
  iapply HΦ
  ipureintro
  exact ⟨secs, rfl⟩

end proof

end EtcdGrove
end Perennial

/-
Proof of `Spec/.../schema/alarmBackend__ForceCommit.lean`: the backend's `ForceCommit`, with no commit
request. Lean-first (prove-ps2-v3alarm, 2026-11-24).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.schema.alarmBackend__ForceCommit
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__ForceCommit

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

theorem schema.alarmBackend.ForceCommit.wp_proof
    (hFC : backend.backend.ForceCommit.spec (GF := GF) (hG := hG)) :
    schema.alarmBackend.ForceCommit.spec (GF := GF) (hG := hG) := by
  intro ab γ P W Pk be qo hbe
  cases ab with
  | mk lg be0 =>
  simp only at hbe
  subst hbe
  wp_start as ⟨#HB, Ho, Hwb⟩
  ihave #Hbpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend $$ []
  · iPkgInit
  wp_auto
  ihave #Hcr := backend.commitReq_true (GF := GF) γ P Pk be
  wp_apply (hFC γ P W Pk be qo iprop(True) iprop(True)) $$ [$Hbpkg $HB $Ho $Hwb $Hcr] as ⟨Ho, -⟩
  iapply HΦ
  iframe Ho

end proof

end EtcdGrove
end Perennial

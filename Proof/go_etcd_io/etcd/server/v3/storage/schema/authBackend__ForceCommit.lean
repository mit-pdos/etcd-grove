/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/schema/authBackend__ForceCommit.lean`. Lean-first (no Rocq
counterpart); the authstore-noax stage (2026-11-18).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.schema.authBackend__ForceCommit

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage backend

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [backend_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

theorem schema.authBackend.ForceCommit.wp_proof
    (hFC : backend.backend.ForceCommit.spec (GF := GF) (hG := hG)) :
    schema.authBackend.ForceCommit.spec (GF := GF) (hG := hG) := by
  intro abe γ P W Pk b qo X Y
  wp_start as ⟨#Hbe, #HB, Ho, Hwb, HX, #Hcr⟩
  ihave #Hbpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend $$ []
  · iPkgInit
  wp_auto
  wp_apply (hFC γ P W Pk b qo X Y) $$ [$Hbpkg $HB $Ho $Hwb $HX $Hcr] as ⟨Ho, HY⟩
  (try wp_auto)
  iapply HΦ
  iframe

end proof

end EtcdGrove
end Perennial

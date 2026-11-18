/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/schema/authBackend__BatchTx.lean`. Lean-first (no Rocq
counterpart); the authstore-noax stage (2026-11-18).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.schema.authBackend__BatchTx

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

theorem schema.authBackend.BatchTx.wp_proof
    (hBT : backend.backend.BatchTx.spec (GF := GF) (hG := hG)) :
    schema.authBackend.BatchTx.spec (GF := GF) (hG := hG) := by
  intro abe γ P W Pk b lg
  wp_start as ⟨#Hbe, #Hlg, #HB⟩
  ihave #Hbpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend $$ []
  · iPkgInit
  wp_auto
  wp_apply (hBT γ P W Pk b) $$ [$Hbpkg $HB] as %t #Ht
  wp_alloc l as Hl
  iStructNamed Hl
  ipersist tx
  ipersist lg
  wp_auto
  iapply HΦ
  iexists l, t
  iframe #
  ipureintro; rfl

end proof

end EtcdGrove
end Perennial

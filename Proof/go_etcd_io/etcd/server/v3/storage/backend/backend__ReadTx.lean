/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/backend__ReadTx.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__ReadTx

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend backend

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

theorem backend.backend.ReadTx.wp_proof : backend.backend.ReadTx.spec (GF := GF) (hG := hG) := by
  intro γ P W Pk b
  wp_start as #Hb
  unfold isBackend
  icases Hb with ⟨%t, %rt, %tm, %db, %lg, %h, -, #Hrt, -⟩
  wp_auto
  iapply HΦ
  iframe #


end proof

end EtcdGrove
end Perennial

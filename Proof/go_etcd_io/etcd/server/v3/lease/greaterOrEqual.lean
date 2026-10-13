/-
Proof of `Spec/go_etcd_io/etcd/server/v3/lease/greaterOrEqual.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.greaterOrEqual
public import Spec.go_etcd_io.etcd.api.v3.version.LessThan

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.lease lease

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

theorem lease.greaterOrEqual.wp_proof
    (hLT : version.LessThan.spec (GF := GF) (hG := hG)) :
    lease.greaterOrEqual.spec (GF := GF) (hG := hG) := by
  intro a b
  wp_start as -
  ihave #Hver : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.version $$ []
  · iPkgInit
  wp_auto
  wp_apply hLT as %r -
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial

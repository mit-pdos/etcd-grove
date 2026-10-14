/-
Proof of `Spec/go_etcd_io/etcd/pkg/v3/adt/NewBytesAffineInterval.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.adt.NewBytesAffineInterval

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.pkg.v3.adt

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.adt.Assumptions]

theorem adt.NewBytesAffineInterval.wp_proof :
    adt.NewBytesAffineInterval.spec (GF := GF) (hG := hG) := by
  intro b e
  wp_start
  wp_auto
  unfold adt.bytesIvl
  wp_end

end proof

end EtcdGrove
end Perennial

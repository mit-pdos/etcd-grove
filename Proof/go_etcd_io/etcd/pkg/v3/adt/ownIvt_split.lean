module

public import Spec.go_etcd_io.etcd.pkg.v3.adt.ownIvt_split
public import Proof.go_etcd_io.etcd.pkg.v3.adt.NodeLemmas

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

theorem adt.ownIvt_split.wp_proof : adt.ownIvt_split.spec (GF := GF) (hG := hG) := by
  refine ⟨fun t L q1 q2 => ⟨adt.ownIvt_split' t L q1 q2, ?_⟩, fun t L1 L2 q1 q2 => ?_⟩
  · iintro H
    icases adt.ownIvt_combine t L L q1 q2 $$ H with ⟨-, H⟩
    iexact H
  · iintro H
    icases adt.ownIvt_combine t L1 L2 q1 q2 $$ H with ⟨%h, -⟩
    ipureintro; exact h

end proof

end EtcdGrove
end Perennial

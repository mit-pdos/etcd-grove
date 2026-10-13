module

public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalTree__Len
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

theorem adt.intervalTree.Len.wp_proof : adt.intervalTree.Len.spec (GF := GF) (hG := hG) := by
  intro t L q
  wp_start as Ht
  icases adt.ownIvt_read _ _ _ $$ Ht with ⟨%tv, %T, Hr, Hc, Hs, Hn, %Hp, Hback⟩
  wp_auto
  rw [Hp.2.2.2.1]
  iapply HΦ
  iapply Hback
  iframe

end proof

end EtcdGrove
end Perennial

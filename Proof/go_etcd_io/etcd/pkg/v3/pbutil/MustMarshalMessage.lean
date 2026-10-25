/-
Proof of `Spec/go_etcd_io/etcd/pkg/v3/pbutil/MustMarshalMessage.lean`. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.pbutil.MustMarshalMessage
public import Spec.google_golang_org.protobuf.proto.MarshalPb

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.pkg.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.pbutil.Assumptions]

theorem pbutil.MustMarshalMessage.wp_proof
    (wp_Marshal : proto.MarshalPb.spec (GF := GF) (hG := hG)) :
    pbutil.MustMarshalMessage.spec (GF := GF) (hG := hG) := by
  intro T l m hm
  wp_start as #Hro
  wp_auto
  wp_apply wp_Marshal T l m hm $$ [$Hro] as %d ⟨Hd, Hcap, %Hw⟩
  (try wp_auto)
  iapply HΦ
  iframe
  ipureintro
  exact Hw

end proof

end EtcdGrove
end Perennial

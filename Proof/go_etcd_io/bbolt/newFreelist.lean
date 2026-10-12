module
public import Spec.go_etcd_io.bbolt.newFreelist

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.freelist

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem newFreelist.wp_proof (hNA : NewArrayFreelist.spec (GF := GF) (hG := hG)) :
    newFreelist.spec (GF := GF) (hG := hG) := by
  intro t ht
  wp_start
  ihave #Hfp : (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist) $$ []
  · iPkgInit
  wp_auto
  rw [decide_eq_false ht]
  try wp_auto
  wp_apply hNA as %a %s Hfl
  try wp_auto
  iapply HΦ
  iexact Hfl

end proof

end bbolt
end EtcdGrove
end Perennial

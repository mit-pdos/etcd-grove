module
public import Spec.go_etcd_io.bbolt.Tx__Size
public import Spec.go_etcd_io.bbolt.internal.common.Meta__Pgid

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem Tx.Size.wp_proof (hPgid : _root_.Perennial.EtcdGrove.bbolt.Meta.Pgid.spec (GF := GF) (hG := hG)) :
    Tx.Size.spec (GF := GF) (hG := hG) := by
  intro tl t m d dq1 dq2 dq3
  wp_start as ⟨Ht, Hm, Hd⟩
  ihave #Hc : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  wp_auto
  wp_apply hPgid $$ [$Hm] as Hm
  try wp_auto
  iapply HΦ; iframe

end proof

end bbolt
end EtcdGrove
end Perennial

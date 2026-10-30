module
public import Spec.go_etcd_io.bbolt.internal.freelist.shared__AddReadonlyTXID

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.freelist

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

theorem shared.AddReadonlyTXID.wp_proof : shared.AddReadonlyTXID.spec (GF := GF) (hG := hG) := by
  intro s iface σ tid
  wp_start as Hs
  unfold ownShared ownSharedC
  icases Hs with ⟨%sv, %c, Hs, %Hok⟩
  iNamed Hs
  wp_auto
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  wp_apply wp_slice_append $$ [Hro Hro_cap Hsl] as %s' ⟨Hro, Hro_cap, -⟩
  · iframe
  try wp_auto
  iapply HΦ
  iexists _, c
  iframe
  ipureintro
  exact ⟨Hiface, Hok⟩

end proof

end bbolt
end EtcdGrove
end Perennial

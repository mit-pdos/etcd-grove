module
public import Spec.go_etcd_io.bbolt.internal.freelist.NewArrayFreelist
public import Spec.go_etcd_io.bbolt.internal.freelist.newShared

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

theorem NewArrayFreelist.wp_proof (hNS : newShared.spec (GF := GF) (hG := hG)) :
    NewArrayFreelist.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_apply hNS as %s Hsh
  unfold ownShared ownSharedC
  icases Hsh with ⟨%sv, %c, Hsh, %Hok⟩
  iNamed Hsh
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, Hslc⟩
  wp_pures
  wp_apply_core wp_alloc
  iintro %ap Hap
  iStructNamed Hap
  ipersist shared
  wp_auto
  try isimp at Hsl
  ispecialize HΦ $$ %ap %s
  rw [show interface.mkOk (go.GoType.PointerType array'.ty) #ap = (arrayImpl (GF := GF) ap).iface
    from rfl]
  iapply HΦ
  unfold ownFL; simp only [arrayImpl]; unfold arrayHdl ownArrayPart ownShared ownSharedC
  iframe shared
  isplitl [Hs Hro Hro_cap Hallocs Hcache Hpending Hpds]
  · iexists _, c
    isplitl
    · iexists pp
      simp only [named]
      iframe
      ipureintro; rfl
    · ipureintro; exact Hok
  · iexists _
    simp only [FLState.empty]
    iframe ids
    isplitr
    · ipureintro; simp [PgidsIncr]
    iExactEq Hsl; rfl

end proof

end bbolt
end EtcdGrove
end Perennial

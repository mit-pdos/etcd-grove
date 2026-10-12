module
public import Spec.go_etcd_io.bbolt.internal.freelist.array__Init
public import Spec.go_etcd_io.bbolt.internal.freelist.shared__reindex
public import Spec.go_etcd_io.bbolt.internal.freelist.array__freePageIds

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

theorem array.Init.wp_proof (hRI : shared.reindex.spec (GF := GF) (hG := hG))
    (hFPI : array.freePageIds.spec (GF := GF) (hG := hG)) :
    array.Init.spec (GF := GF) (hG := hG) := by
  intro a s σ ids xs Hwf
  wp_start as ⟨#Hhdl, Hs, Hown, Hnew, Hnewcap⟩
  unfold ownArrayPart
  iNamed Hown
  wp_auto
  wp_method_call
  wp_call
  unfold arrayHdl
  wp_auto
  unfold ownShared
  icases Hs with ⟨%sv, %c, Hs, %Hok⟩
  have hF : (arrayImpl (GF := GF) a).FreePageIdsSpec := fun s free => hFPI a s free
  wp_bind (App (Val #(methods (go.GoType.PointerType shared.ty) go!"reindex" #s)) (Val #()))
  iapply (hRI (arrayImpl a) s sv ({ σ with free := xs } : FLState) c hF) $$ [Hs Hidsf Hnew Hnewcap]
  · isplitl []; · iexact Hpkg
    isplitl []; · iExactEq Hhdl; rfl
    isplitl [Hs]; · iExactEq Hs; rfl
    unfold arrayImpl ownArrayPart
    iexists _
    iframe
    ipureintro; exact Hwf.2.2.1
  inext
  iintro %sv' %c' ⟨Hs, %Hc', Hown⟩
  wp_auto
  iapply HΦ
  isplitl [Hs]
  · iexists sv', c'
    iframe
    ipureintro; exact ⟨Hc', Hwf⟩
  · iExactEq Hown; rfl

end proof

end bbolt
end EtcdGrove
end Perennial

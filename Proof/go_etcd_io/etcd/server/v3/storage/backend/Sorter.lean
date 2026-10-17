/-
A bucket buffer as a `sort.Interface` (by its `Len`, `Less` and `Swap`), for the sorts of
`bucketBuffer.dedupe` (`sort.Stable`) and `txWriteBuffer.writeback` (`sort.Sort`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.bucketBuffer__Len
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.bucketBuffer__Less
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.bucketBuffer__Swap
public import Spec.sort.Sort

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend backend

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- A bucket buffer is a `sort.Interface` over its entries, ordered by key. -/
theorem backend.bb_sorter
    (hLen : backend.bucketBuffer.Len.spec (GF := GF) (hG := hG))
    (hLess : backend.bucketBuffer.Less.spec (GF := GF) (hG := hG))
    (hSwap : backend.bucketBuffer.Swap.spec (GF := GF) (hG := hG)) (bb : Loc) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ⊢
      sorterSpec (interface.mk (go.GoType.PointerType bucketBuffer.ty) #bb) (ownBB bb)
        (fun a b : Ent => decide (strLt a.1 b.1)) := by
  iintro #Hpkg
  unfold sorterSpec
  isplitr
  · imodintro
    iintro %l
    iintro !> %Φ Hl HΦ
    iapply (hLen bb l) $$ [$Hpkg $Hl] HΦ
  isplitr
  · imodintro
    iintro %l %i %j %a %b %Hij
    iintro !> %Φ Hl HΦ
    obtain ⟨hi, hj, ha, hb⟩ := Hij
    iapply (hLess bb l i j a b hi hj ha hb) $$ [$Hpkg $Hl] HΦ
  imodintro
  iintro %l %i %j %a %b %Hij
  iintro !> %Φ Hl HΦ
  obtain ⟨hi, hj, ha, hb⟩ := Hij
  iapply (hSwap bb l i j a b hi hj ha hb) $$ [$Hpkg $Hl] HΦ

end proof

end EtcdGrove
end Perennial

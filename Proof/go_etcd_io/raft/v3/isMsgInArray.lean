/- Lean-first (no Rocq counterpart). -/
module

public import Spec.go_etcd_io.raft.v3.isMsgInArray

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem isMsgInArray.wp_proof : isMsgInArray.spec (GF := GF) (hG := hG) := by
  intro t arr l Ht
  wp_start as #Harr
  wp_auto
  have Hi : sint.Z (W64 (sint.Z t)) = sint.Z t := by word
  rw [Hi]
  wp_if_destruct
  · ihave %Hlen := ownSlice_len $$ Harr
    obtain ⟨x, Hx⟩ : ∃ x, l[(sint.Z t).toNat]? = some x :=
      ⟨_, List.getElem?_eq_getElem (by word)⟩
    rw [Hi, ite_eq_left_of_eq_true _ _ (eq_true ⟨Ht, Hif⟩)]
    wp_apply wp_load_slice_index arr (sint.Z t) l DFrac.discard x Ht $$ [Harr] as -
    · iframe Harr; ipureintro; exact Hx
    iapply HΦ
    itrivial
  · iapply HΦ
    itrivial

end proof

end EtcdGrove
end Perennial

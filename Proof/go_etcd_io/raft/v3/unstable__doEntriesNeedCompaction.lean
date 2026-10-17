/-
Lean-first (etcd-io/raft#96).
-/
module

public import Spec.go_etcd_io.raft.v3.unstable__doEntriesNeedCompaction
public import Spec.google_golang_org.protobuf.proto.SizeEntry

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

theorem unstable.doEntriesNeedCompaction.wp_proof
    (wp_proto_SizeEntry : proto.SizeEntry.spec (GF := GF) (hG := hG)) :
    unstable.doEntriesNeedCompaction.spec (GF := GF) (hG := hG) := by
  intro u us k
  wp_start as H
  iNamed H
  open_unstable
  icases Hents with #Hents
  ihave Hents' := Hents
  iunfold entsRO at Hents'
  iunfold entsPts at Hents'
  icases Hents' with ⟨%ls, #Hls, #Hb⟩
  ihave %Hlsl := ownSlice_len $$ Hls
  ihave %Hbl := entsBig_length $$ Hb
  wp_auto
  wp_if_destruct
  · iapply HΦ
    close_unstable
  ihave IH : iprop(∃ (n s1 s2 x : w64) (ev : Loc),
      "i" ∷ i_ptr ↦ n ∗ "stableEntriesSize" ∷ stableEntriesSize_ptr ↦ s1 ∗
      "totalSize" ∷ totalSize_ptr ↦ s2 ∗ "ind" ∷ ind_ptr ↦ x ∗ "val" ∷ val_ptr ↦ ev ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (us.ents.length : Int)⌝) $$ [i stableEntriesSize totalSize ind val]
  · iexists _, _, _, _, _
    iframe
    ipureintro
    word
  wp_for IH
  wp_if_destruct
  · have Hlt : (sint.Z n).toNat < us.ents.length := by word
    obtain ⟨e, He⟩ : ∃ e, us.ents[(sint.Z n).toNat]? = some e :=
      ⟨_, List.getElem?_eq_getElem Hlt⟩
    icases entsBig_lookup ls us.ents _ e He $$ Hb with ⟨%l, %Hl, #Hl⟩
    simp only [show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z uv.entries'.len from ⟨Hn.1, by word⟩]
    wp_apply wp_load_slice_index uv.entries' (sint.Z n) ls DFrac.discard l Hn.1 $$ [Hls] as Hls'
    · isplitl
      · iexact Hls
      · ipureintro; exact Hl
    wp_if_destruct
    · wp_apply wp_proto_SizeEntry l DFrac.discard e $$ [$Hl] as %sz1 ⟨-, -⟩
      wp_apply wp_proto_SizeEntry l DFrac.discard e $$ [$Hl] as %sz2 ⟨-, -⟩
      wp_for_post
      iframe
      iexists _, _, _, _, _
      iframe
      ipureintro
      word
    · wp_apply wp_proto_SizeEntry l DFrac.discard e $$ [$Hl] as %sz2 ⟨-, -⟩
      wp_for_post
      iframe
      iexists _, _, _, _, _
      iframe
      ipureintro
      word
  · iapply HΦ
    close_unstable

end proof

end EtcdGrove
end Perennial

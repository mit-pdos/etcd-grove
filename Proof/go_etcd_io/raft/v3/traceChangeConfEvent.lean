/- `traceChangeConfEvent`, Lean-first (2026-10-13). -/
module

public import Spec.go_etcd_io.raft.v3.traceChangeConfEvent
public import Spec.go_etcd_io.raft.v3.traceEvent
public import Spec.go_etcd_io.raft.v3.raftpb.ConfChange__AsV2
public import Spec.go_etcd_io.raft.v3.raftpb.ConfChangeV2__AsV2
public import Spec.go_etcd_io.raft.v3.raftpb.ConfChangeSingle__GetType
public import Spec.go_etcd_io.raft.v3.raftpb.ConfChangeSingle__GetNodeId
public import Spec.strconv.FormatUint
public import Proof.go_etcd_io.raft.v3.FrameH

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

set_option hygiene false in
/-- A change the trace records (`AddNode`, `RemoveNode`, `AddLearnerNode`): its id formatted,
appended to `cc.Changes`, the next iteration. -/
local macro "cc_append" : tactic => `(tactic| (
    try wp_auto
    wp_apply wp_ConfChangeSingle_GetNodeId.1 q DFrac.discard ch $$ [$(frameH `Hq)] as -
    wp_apply wp_FormatUint
    · ipureintro; word
    iintro %str %Hstr
    wp_auto
    wp_apply wp_slice_literal (V := SingleConfChange) [_]
    isplitr
    · ipureintro; rfl
    iintro %sl2 ⟨Hs2, -⟩
    wp_apply wp_slice_append (V := SingleConfChange) $$ [$(frameH `Hxs) $(frameH `Hxc) $(frameH `Hs2)] as %s' ⟨Hxs, Hxc, -⟩
    wp_for_post
    iframe
    iexists _, _, _, _
    iframe Htc
    iframe
    ipureintro; exact ⟨by word, by word⟩))

theorem traceChangeConfEvent.wp_proof
    (wp_traceEvent : traceEvent.spec (GF := GF) (hG := hG))
    (wp_ConfChange_AsV2 : raftpb.ConfChange.AsV2.spec (GF := GF) (hG := hG))
    (wp_ConfChangeV2_AsV2 : raftpb.ConfChangeV2.AsV2.spec (GF := GF) (hG := hG))
    (wp_ConfChangeSingle_GetType : raftpb.ConfChangeSingle.GetType.spec (GF := GF) (hG := hG))
    (wp_ConfChangeSingle_GetNodeId : raftpb.ConfChangeSingle.GetNodeId.spec (GF := GF) (hG := hG))
    (wp_FormatUint : strconv.FormatUint.spec (GF := GF) (hG := hG)) :
    traceChangeConfEvent.spec (GF := GF) (hG := hG) := by
  intro c dq o r tl
  wp_start as ⟨Hc, #Htl, %Hok⟩
  cases o with
  | v1 m =>
    iunfold ownConfChangeI at Hc
    icases Hc with ⟨%p, %Hp, Hown⟩
    subst Hp
    wp_auto
    wp_apply wp_ConfChange_AsV2 _ _ _ $$ [$Hown] as %v2 ⟨Hown, Hv2⟩
    wp_apply wp_slice_literal (V := SingleConfChange) []
    isplitr
    · ipureintro; rfl
    iintro %sl0 Hsl0
    wp_auto
    wp_apply wp_slice_literal (V := GoString) []
    isplitr
    · ipureintro; rfl
    iintro %sl1 Hsl1
    wp_auto
    iunfold ownConfChangeV2 at Hv2
    iNamed Hv2
    ihave %Hlen := ownSlice_len $$ Hch
    ihave %Hbl := BigSepL2.bigSepL2_length $$ Hccs
    wp_auto
    icases Hsl0 with ⟨Hxs, Hxc⟩
    ihave IH : iprop(∃ (n : w64) (cv : Loc) (tc : go_etcd_io.raft.v3.TracingConfChange) (xs : List SingleConfChange),
        "i" ∷ i_ptr ↦ n ∗ "c" ∷ c_ptr ↦ cv ∗
        "Htc" ∷ «$r0_ptr» ↦ tc ∗ "Hxs" ∷ tc.Changes' ↦* xs ∗
        "Hxc" ∷ ownSliceCap SingleConfChange tc.Changes' (DFrac.own 1) ∗
        "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (m.asV2.changes.length : Int)⌝) $$ [i c «$r0» Hxs Hxc]
    · iexists _, _, _, _
      iframe «$r0»
      iframe
      ipureintro
      exact ⟨by word, by word⟩
    wp_for IH
    wp_if_destruct
    · have Hlt : (sint.Z n).toNat < m.asV2.changes.length := by word
      obtain ⟨ch, Hch⟩ : ∃ ch, m.asV2.changes[(sint.Z n).toNat]? = some ch :=
        ⟨_, List.getElem?_eq_getElem Hlt⟩
      obtain ⟨q, Hq⟩ : ∃ q, ls[(sint.Z n).toNat]? = some q :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      ihave #Hq := BigSepL2.bigSepL2_lookup Hq Hch $$ Hccs
      rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z chs.len from ⟨Hn.1, Hif⟩))]
      wp_apply wp_load_slice_index chs (sint.Z n) ls _ q Hn.1 $$ [Hch] as Hch
      · iframe; ipureintro; exact Hq
      try wp_auto
      wp_apply wp_ConfChangeSingle_GetType.1 q DFrac.discard ch $$ [$Hq] as -
      wp_if_destruct
      · cc_append
      wp_if_destruct
      · cc_append
      wp_if_destruct
      · cc_append
      wp_for_post
      iframe
      iexists _, _, _, _
      iframe Htc
      iframe
      ipureintro; exact ⟨by word, by word⟩
    · wp_if_destruct
      · iapply HΦ
        iunfold ownConfChangeI
        iexists p
        iframe Hown
        ipureintro; rfl
      wp_apply wp_map_make1 (K := GoString) (V := GoInterface) go.string go.any as %mp Hmp
      try wp_auto
      wp_apply wp_mapInsert $$ [$Hmp] as Hmp
      try wp_auto
      wp_apply wp_traceEvent _ r _ _ tl none (fun _ => True) iprop(True) iprop(emp) $$ [$Htl] as -
      · isplitr
        · iapply trOwn_none_intro
        iapply (traceFire_none tl _ _).2
        isplitr
        · ipureintro; exact Hok
        itrivial
      iapply HΦ
      iunfold ownConfChangeI
      iexists p
      iframe Hown
      ipureintro; rfl
  | v2 m =>
    iunfold ownConfChangeI at Hc
    icases Hc with ⟨%p, %Hp, Hown⟩
    subst Hp
    wp_auto
    wp_apply wp_ConfChangeV2_AsV2
    wp_apply wp_slice_literal (V := SingleConfChange) []
    isplitr
    · ipureintro; rfl
    iintro %sl0 Hsl0
    wp_auto
    wp_apply wp_slice_literal (V := GoString) []
    isplitr
    · ipureintro; rfl
    iintro %sl1 Hsl1
    wp_auto
    iunfold ownConfChangeV2 at Hown
    iNamed Hown
    ihave %Hlen := ownSlice_len $$ Hch
    ihave %Hbl := BigSepL2.bigSepL2_length $$ Hccs
    wp_auto
    icases Hsl0 with ⟨Hxs, Hxc⟩
    ihave IH : iprop(∃ (n : w64) (cv : Loc) (tc : go_etcd_io.raft.v3.TracingConfChange) (xs : List SingleConfChange),
        "i" ∷ i_ptr ↦ n ∗ "c" ∷ c_ptr ↦ cv ∗
        "Htc" ∷ «$r0_ptr» ↦ tc ∗ "Hxs" ∷ tc.Changes' ↦* xs ∗
        "Hxc" ∷ ownSliceCap SingleConfChange tc.Changes' (DFrac.own 1) ∗
        "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (m.changes.length : Int)⌝) $$ [i c «$r0» Hxs Hxc]
    · iexists _, _, _, _
      iframe «$r0»
      iframe
      ipureintro
      exact ⟨by word, by word⟩
    wp_for IH
    wp_if_destruct
    · have Hlt : (sint.Z n).toNat < m.changes.length := by word
      obtain ⟨ch, Hch⟩ : ∃ ch, m.changes[(sint.Z n).toNat]? = some ch :=
        ⟨_, List.getElem?_eq_getElem Hlt⟩
      obtain ⟨q, Hq⟩ : ∃ q, ls[(sint.Z n).toNat]? = some q :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      ihave #Hq := BigSepL2.bigSepL2_lookup Hq Hch $$ Hccs
      rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z chs.len from ⟨Hn.1, Hif⟩))]
      wp_apply wp_load_slice_index chs (sint.Z n) ls _ q Hn.1 $$ [Hch] as Hch
      · iframe; ipureintro; exact Hq
      try wp_auto
      wp_apply wp_ConfChangeSingle_GetType.1 q DFrac.discard ch $$ [$Hq] as -
      wp_if_destruct
      · cc_append
      wp_if_destruct
      · cc_append
      wp_if_destruct
      · cc_append
      wp_for_post
      iframe
      iexists _, _, _, _
      iframe Htc
      iframe
      ipureintro; exact ⟨by word, by word⟩
    · wp_if_destruct
      · iapply HΦ
        iunfold ownConfChangeI
        iexists p
        isplitr
        · ipureintro; rfl
        iunfold ownConfChangeV2
        iexists pt, chs, ls, cs, uf
        iframe
        isplitr
        · ipureintro; exact Hnn
        iframe cT Hccs Hcs Hpb
      wp_apply wp_map_make1 (K := GoString) (V := GoInterface) go.string go.any as %mp Hmp
      try wp_auto
      wp_apply wp_mapInsert $$ [$Hmp] as Hmp
      try wp_auto
      wp_apply wp_traceEvent _ r _ _ tl none (fun _ => True) iprop(True) iprop(emp) $$ [$Htl] as -
      · isplitr
        · iapply trOwn_none_intro
        iapply (traceFire_none tl _ _).2
        isplitr
        · ipureintro; exact Hok
        itrivial
      iapply HΦ
      iunfold ownConfChangeI
      iexists p
      isplitr
      · ipureintro; rfl
      iunfold ownConfChangeV2
      iexists pt, chs, ls, cs, uf
      iframe
      isplitr
      · ipureintro; exact Hnn
      iframe cT Hccs Hcs Hpb

end proof

end EtcdGrove
end Perennial

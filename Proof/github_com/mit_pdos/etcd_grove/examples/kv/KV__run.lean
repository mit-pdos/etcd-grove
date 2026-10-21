/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kv/KV__run.lean`. Lean-first (no
Rocq counterpart). raft v3.7 (2026-10-16, stage R6b): a `Ready`'s entries and committed entries
are read-only entry pointers (`entsRO`), its messages owned pointers (`sendSpec`), its read
states Go values whose contexts hold their bytes (`readStatesPts_rsOk`), its hard state `hsOpt`
(unused: the store persists no hard state); a conf-change entry is decoded with
`proto.Unmarshal` into a fresh `pb.ConfChange`, applied by pointer (`ownCCV1_persist`:
`node.ApplyConfChange` reads it on raft's goroutine).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.KV__run
public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.KV__apply
public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.KV__answer
public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.fits
public import Spec.go_etcd_io.raft.v3.node__Ready
public import Spec.go_etcd_io.raft.v3.node__Advance
public import Spec.go_etcd_io.raft.v3.MemoryStorage__Append
-- (2026-10-15, stage N) conf changes
public import Spec.go_etcd_io.raft.v3.node__ApplyConfChange
public import Spec.google_golang_org.protobuf.proto.UnmarshalConfChange
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetType
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetData
public import Proof.github_com.mit_pdos.etcd_grove.examples.kv.Lemmas
public import Proof.github_com.mit_pdos.etcd_grove.examples.kv.KVStorageInstance

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kv

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]
variable [KVStor GF]

theorem KV.run.wp_proof
    (wp_fits : kv.fits.spec (GF := GF) (hG := hG))
    (wp_apply : kv.KV.apply.spec (GF := GF) (hG := hG))
    (wp_answer : kv.KV.answer.spec (GF := GF) (hG := hG))
    (wp_node_Ready : node.Ready.spec (GF := GF) (hG := hG))
    (wp_node_Advance : node.Advance.spec (GF := GF) (hG := hG))
    (wp_MemoryStorage_Append : MemoryStorage.Append.spec (GF := GF) (hG := hG))
    (wp_proto_UnmarshalConfChange : proto.UnmarshalConfChange.spec (GF := GF) (hG := hG))
    (wp_node_ApplyConfChange : node.ApplyConfChange.spec (GF := GF) (hG := hG))
    (wp_Entry_GetType : raftpb.Entry.GetType.spec (GF := GF) (hG := hG))
    (wp_Entry_GetData : raftpb.Entry.GetData.spec (GF := GF) (hG := hG)) :
    KV.run.spec (GF := GF) (hG := hG) := by
  intro γr γp r id n st send c0
  wp_start as ⟨#Hrep, %Hst, Hncfg, Hdrv, Hrun, #Hsend⟩
  have Hsn : γp.node.snapIn = false := Hst.2.2.2
  ihave #Hrep' := Hrep
  iunfold isReplica at Hrep'
  iNamed Hrep'
  ihave #Hraftinit : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  ihave #Hpbinit : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  ihave #Hprotoinit : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_node_Ready γp.node id n $$ [$HisNode] as %ch #Hch
  ihave IH : iprop(∃ (ds : List EntryM) (rdv : Ready) (pv : GoSlice) (ps : List ReadState)
      (a : w64) (p : HardStateM),
      "Hrd" ∷ rd_ptr ↦ rdv ∗ "Hdrv" ∷ nodeDriver γp.node id n ds p ∗ "Hrun" ∷ runOwn γr r ds ∗
      "pending" ∷ pending_ptr ↦ pv ∗ "Hpv" ∷ pv ↦* ps ∗
      "Hpcap" ∷ ownSliceCap ReadState pv (DFrac.own 1) ∗
      "Hps" ∷ ([∗list] v ∈ ps, rsOk γr.raft v) ∗
      "applied" ∷ applied_ptr ↦ a ∗ "%Ha" ∷ ⌜uint.Z a ≤ (ds.length : Int)⌝ ∗
      "Hncfg" ∷ nodeCfg γp.node 0 c0)
    $$ [rd Hdrv Hrun pending applied Hncfg]
  · iexists [], _, _, [], _, hsZero
    iframe
    isplitl []
    · iapply ownSlice_nil
    isplitl []
    · iapply ownSliceCap_nil
    isplitl []
    · iapply (BigSepL.bigSepL_nil).2; iempintro
    ipureintro
    simp; rfl
  wp_for IH
  -- (D22 S-d4) no snapshot `Ready`: the node takes no `MsgSnap` (`snapIn` off)
  wp_apply node_ready_receive_ns γp.node id n ch ds p (.inr (.inr Hsn)) $$ [$Hch $Hdrv]
    as %rdv' ⟨%ce, %es, %msgs, %p', Hdata, Hbusy⟩
  ihave #Hdlb := nodeDriverBusy_lb γp.node id n (ds ++ ce) es p' $$ Hbusy
  unfold readyData
  icases Hdata with ⟨#Hce, #Hcomm, #Hes, Happ, Hms, Hmsok, Hcr, Htks, ⟨%sts, #Hsts, #Hstsok⟩, ⟨%hs, #Hhs, -⟩,
    -, #Hss, %Hsnap, -⟩
  wp_apply wp_fits rdv'.Entries' es DFrac.discard $$ [$Hes] as %b ⟨-, %Hfit⟩
  cases b
  · -- a log past `maxIndex`: the replica stops
    wp_auto
    ihave Hspin : iprop(True) $$ []
    · itrivial
    wp_for Hspin
    wp_for_post
    iframe
  -- `r.storage.Append(rd.Entries)`, the promoted `MemoryStorage.Append`
  icases Hsrec with ⟨%ms, %γs, #Hrec⟩
  ihave #Hrec' := Hrec
  iunfold kvStorRec at Hrec'
  icases Hrec' with ⟨#Hmsf, -⟩
  ihave Htok : iprop(∃ σ, ⌜es = []⌝ ∨ memAppendTok ms γs σ es) $$ [Happ]
  · unfold appendRight
    rw [Hstor]
    icases Happ with (%Hnil | ⟨%σ, Htok⟩)
    · iexists memStorEmpty; ileft; ipureintro; exact Hnil
    ihave Htok : kvAppendTok (kvStorIface st) σ es $$ Htok
    unfold kvAppendTok
    icases Htok with ⟨%s', %ms', %γs', %Hst, #Hrec2, Htok⟩
    have := kvStorIface_inj (GF := GF) _ _ Hst
    subst this
    icases kvStorRec_agree st ms ms' γs γs' $$ Hrec Hrec2 with ⟨%H1, %H2⟩
    subst H1 H2
    iexists σ; iright; iexact Htok
  icases Htok with ⟨%σ, Htok⟩
  wp_auto
  wp_method_call
  wp_auto
  wp_apply wp_MemoryStorage_Append ms γs σ es rdv'.Entries' DFrac.discard (Hfit rfl)
    $$ [$Hraftinit $Htok $Hes] as ⟨Hdone, -⟩
  ihave Hrcpt : appendReceipt γp.node.stor es $$ [Hdone]
  · unfold appendReceipt
    rw [Hstor]
    icases Hdone with (%Hnil | Hd)
    · ileft; ipureintro; exact Hnil
    iright; iexists σ
    ihave H : kvAppendedTok (kvStorIface st) σ es $$ [Hd]
    · unfold kvAppendedTok
      iexists st, ms, γs
      iframe Hrec Hd
      ipureintro; rfl
    iexact H
  -- `send(rd.Messages)`: the messages as `Ready` hands them out
  wp_bind (App (Val #send) _)
  iunfold sendSpec at Hsend
  iapply Hsend $$ [Hms Hmsok Hcr Htks]
  · iframe
  iintro !> -
  wp_auto
  -- the read states, noted (`rsOk` of each value)
  ihave Hvs := readStatesPts_rsOk γp.node.raft rdv'.ReadStates' sts $$ [Hsts Hstsok]
  · iframe Hsts Hstsok
  icases Hvs with ⟨%vs, #Hvs, #Hvsok⟩
  wp_apply wp_slice_append $$ [$Hpv $Hpcap $Hvs] as %pv' ⟨Hpv, Hpcap, -⟩
  ihave Hps : iprop([∗list] v ∈ ps ++ vs, rsOk γr.raft v) $$ [Hps]
  · iapply (BigSepL.bigSepL_append (Φ := fun _ v => rsOk (GF := GF) γr.raft v)).2
    iframe Hps
    rw [← Hraft]
    iexact Hvsok
  -- applying the committed entries, in order
  icases entsPts_elim _ _ _ $$ Hce with ⟨%cls, #Hce, #Hceb⟩
  ihave %Hcelen := ownSlice_len $$ Hce
  ihave %Hcebl := entsBig_length $$ Hceb
  ihave IHa : iprop(∃ (k : w64) (ev : Loc) (a' : w64),
      "i" ∷ i_ptr ↦ k ∗ "e" ∷ e_ptr ↦ ev ∗ "Hrun" ∷ runOwn γr r (ds ++ ce.take (sint.nat k)) ∗
      "applied" ∷ applied_ptr ↦ a' ∗
      "%Ha" ∷ ⌜uint.Z a' ≤ ((ds ++ ce.take (sint.nat k)).length : Int)⌝ ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ (ce.length : Int)⌝)
    $$ [i e Hrun applied]
  · iexists W64 0, _, a
    iframe i e applied
    simp only [show sint.nat (W64 0) = 0 by rfl, List.take_zero, List.append_nil]
    iframe Hrun
    ipureintro
    refine ⟨Ha, by constructor <;> word⟩
  wp_for IHa
  wp_if_destruct
  · have Hlt : sint.nat k < ce.length := by word
    obtain ⟨en, Hen⟩ : ∃ en, ce[sint.nat k]? = some en := ⟨_, List.getElem?_eq_getElem Hlt⟩
    ihave ⟨%ln, %Hln, #Hent⟩ := entsBig_lookup cls ce (sint.nat k) en Hen $$ Hceb
    have Hbnd' : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z rdv'.CommittedEntries'.len := ⟨Hk.1, by word⟩
    simp only [Hbnd', _root_.and_self]
    wp_apply wp_load_slice_index rdv'.CommittedEntries' (sint.Z k) _ DFrac.discard ln Hk.1 $$ [Hce] as -
    · iframe Hce; ipureintro; exact Hln
    have Htk : ce.take (sint.nat k + 1) = ce.take (sint.nat k) ++ [en] := by
      rw [List.take_add_one, Hen]; rfl
    ihave #Hc1 := isCommitted_mono γp.node.raft (ds ++ ce.take (sint.nat k) ++ [en]) (ds ++ ce)
      (by rw [List.append_assoc, ← Htk]; exact List.prefix_append_right_inj _ |>.mpr (List.take_prefix _ _))
      $$ Hcomm
    -- the entry's data: (D22 S-r) in the static mode a normal entry's, no conf change
    imod node_entry_data γp.node id n (ds ++ ce.take (sint.nat k)) en ⊤ CoPset.subseteq_top
      $$ HisNode Hc1 with ⟨%o, #Ho⟩
    ihave %Hty0 := kvStat_type0 γp.node Hst en o $$ Ho
    -- `if e.GetType() == pb.EntryConfChange { ... }`: not taken
    wp_apply wp_Entry_GetType.1 ln DFrac.discard en $$ [$Hpbinit $Hent] as -
    rw [decide_eq_false (show ¬ en.Type' = W32 1 by rw [Hty0]; intro h; revert h; word)]
    wp_auto
    rw [Hraft]
    wp_apply wp_apply γr γp r id n st (ds ++ ce.take (sint.nat k)) ln en
      $$ [$Hpkg $Hrep $Hrun $Hent $Hc1] as Hrun
    wp_for_post
    iframe
    iexists k + W64 1, ln, a' + W64 1
    rw [show sint.nat (k + W64 1) = sint.nat k + 1 by word, Htk, List.append_assoc]
    iframe
    ipureintro
    have Hl : ((ds ++ (ce.take (sint.nat k) ++ [en])).length : Int) =
        ((ds ++ ce.take (sint.nat k)).length : Int) + 1 := by simp; omega
    refine ⟨?_, ?_⟩
    · rw [Hl]; word
    · constructor <;> word
  · have Hfull : sint.nat k = ce.length := by word
    rw [Hfull, List.take_of_length_le (by omega)] at Ha ⊢
    -- the reads whose index is applied, answered
    wp_apply wp_answer γr γp r id n st (ds ++ ce) pv' (ps ++ vs) (DFrac.own 1) a' Ha
      $$ [$Hpkg $Hrep $Hrun $Hpv $Hps] as %rest ⟨Hrun, %ps', Hrest, Hcap, Hps'⟩
    -- (D22 S-d4) the receipt for a `Ready` without a snapshot
    ihave Hrcpt : advReceipt γp.node.stor es none $$ [Hrcpt]
    · simp only [advReceipt]; iexact Hrcpt
    have Hnd : γp.node.mode.isDyn = true → NoConfIn (ds ++ ce) 0 (ds ++ ce).length := by
      intro h; rw [Hst.1] at h; cases h
    wp_apply wp_node_Advance γp.node id n (ds ++ ce) es 0 c0 p' none Hnd
      $$ [$Hraftinit $Hbusy $Hrcpt $Hncfg] as ⟨Hdrv, Hncfg, -⟩
    wp_for_post
    iframe
    iexists ds ++ ce, rdv', rest, ps', a', p'
    iframe
    ipureintro; exact Ha

end proof

end kv
end EtcdGrove
end Perennial

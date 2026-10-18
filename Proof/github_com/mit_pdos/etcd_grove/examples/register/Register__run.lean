/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/register/Register__run.lean`. Lean-first (no
Rocq counterpart). raft v3.7 (2026-10-16, stage R6b): a `Ready`'s entries and committed entries
are read-only entry pointers (`entsRO`), its messages owned pointers (`sendSpec`), its read
states Go values whose contexts hold their bytes (`readStatesPts_rsOk`), its hard state `hsOpt`
(unused: the register persists no hard state); a conf-change entry is decoded with
`proto.Unmarshal` into a fresh `pb.ConfChange`, applied by pointer (`ownCCV1_persist`:
`node.ApplyConfChange` reads it on raft's goroutine).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.register.Register__run
public import Spec.github_com.mit_pdos.etcd_grove.examples.register.Register__apply
public import Spec.github_com.mit_pdos.etcd_grove.examples.register.Register__answer
public import Spec.github_com.mit_pdos.etcd_grove.examples.register.fits
public import Spec.go_etcd_io.raft.v3.node__Ready
public import Spec.go_etcd_io.raft.v3.node__Advance
public import Spec.go_etcd_io.raft.v3.MemoryStorage__Append
-- (2026-10-15, stage N) conf changes
public import Spec.go_etcd_io.raft.v3.node__ApplyConfChange
public import Spec.google_golang_org.protobuf.proto.UnmarshalConfChange
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetType
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetData
public import Proof.github_com.mit_pdos.etcd_grove.examples.register.Lemmas
public import Proof.github_com.mit_pdos.etcd_grove.examples.register.RegStorageInstance

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace register

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.register.Assumptions]
variable [RegStor GF]

theorem Register.run.wp_proof
    (wp_fits : register.fits.spec (GF := GF) (hG := hG))
    (wp_apply : register.Register.apply.spec (GF := GF) (hG := hG))
    (wp_answer : register.Register.answer.spec (GF := GF) (hG := hG))
    (wp_node_Ready : node.Ready.spec (GF := GF) (hG := hG))
    (wp_node_Advance : node.Advance.spec (GF := GF) (hG := hG))
    (wp_MemoryStorage_Append : MemoryStorage.Append.spec (GF := GF) (hG := hG))
    (wp_proto_UnmarshalConfChange : proto.UnmarshalConfChange.spec (GF := GF) (hG := hG))
    (wp_node_ApplyConfChange : node.ApplyConfChange.spec (GF := GF) (hG := hG))
    (wp_Entry_GetType : raftpb.Entry.GetType.spec (GF := GF) (hG := hG))
    (wp_Entry_GetData : raftpb.Entry.GetData.spec (GF := GF) (hG := hG)) :
    Register.run.spec (GF := GF) (hG := hG) := by
  intro γr γp r id n st send op c0 c1
  wp_start as ⟨#Hrep, %Hcc, Hncfg, Hdrv, Hrun, #Hsend⟩
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
      (a : w64) (ca : Nat) (cfg : CCState),
      "Hrd" ∷ rd_ptr ↦ rdv ∗ "Hdrv" ∷ nodeDriver γp.node id n ds ∗ "Hrun" ∷ runOwn γr r ds ∗
      "pending" ∷ pending_ptr ↦ pv ∗ "Hpv" ∷ pv ↦* ps ∗
      "Hpcap" ∷ ownSliceCap ReadState pv (DFrac.own 1) ∗
      "Hps" ∷ ([∗list] v ∈ ps, rsOk γr.raft v) ∗
      "applied" ∷ applied_ptr ↦ a ∗ "%Ha" ∷ ⌜uint.Z a ≤ (ds.length : Int)⌝ ∗
      "Hncfg" ∷ nodeCfg γp.node ca cfg ∗ "%Hrc" ∷ ⌜RunCfg ds ds.length ca cfg c0 c1⌝)
    $$ [rd Hdrv Hrun pending applied Hncfg]
  · iexists [], _, _, [], _, 0, c0
    iframe
    isplitl []
    · iapply ownSlice_nil
    isplitl []
    · iapply ownSliceCap_nil
    isplitl []
    · iapply (BigSepL.bigSepL_nil).2; iempintro
    ipureintro
    refine ⟨by simp; rfl, Nat.le_refl _, NoConfIn_empty _ _, .inl rfl⟩
  wp_for IH
  wp_apply node_ready_receive γp.node id n ch ds $$ [$Hch $Hdrv] as %rdv' ⟨%ce, %es, %msgs, Hdata, Hbusy⟩
  ihave #Hdlb := nodeDriverBusy_lb γp.node id n (ds ++ ce) es $$ Hbusy
  unfold readyData
  icases Hdata with ⟨#Hce, #Hcomm, #Hes, Happ, Hms, Hmsok, Hcr, ⟨%sts, #Hsts, #Hstsok⟩, ⟨%hs, #Hhs⟩,
    #Hss, %Hsnap, -⟩
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
  iunfold regStorRec at Hrec'
  icases Hrec' with ⟨#Hmsf, -⟩
  ihave Htok : iprop(∃ σ, ⌜es = []⌝ ∨ memAppendTok ms γs σ es) $$ [Happ]
  · unfold appendRight
    rw [Hstor]
    icases Happ with (%Hnil | ⟨%σ, Htok⟩)
    · iexists memStorEmpty; ileft; ipureintro; exact Hnil
    ihave Htok : regAppendTok (regStorIface st) σ es $$ Htok
    unfold regAppendTok
    icases Htok with ⟨%s', %ms', %γs', %Hst, #Hrec2, Htok⟩
    have := regStorIface_inj (GF := GF) _ _ Hst
    subst this
    icases regStorRec_agree st ms ms' γs γs' $$ Hrec Hrec2 with ⟨%H1, %H2⟩
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
    ihave H : regAppendedTok (regStorIface st) σ es $$ [Hd]
    · unfold regAppendedTok
      iexists st, ms, γs
      iframe Hrec Hd
      ipureintro; rfl
    iexact H
  -- `send(rd.Messages)`: the messages as `Ready` hands them out
  wp_bind (App (Val #send) _)
  iunfold sendSpec at Hsend
  iapply Hsend $$ [Hms Hmsok Hcr]
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
  ihave IHa : iprop(∃ (k : w64) (ev : Loc) (a' : w64) (ca' : Nat) (cfg' : CCState),
      "i" ∷ i_ptr ↦ k ∗ "e" ∷ e_ptr ↦ ev ∗ "Hrun" ∷ runOwn γr r (ds ++ ce.take (sint.nat k)) ∗
      "applied" ∷ applied_ptr ↦ a' ∗
      "%Ha" ∷ ⌜uint.Z a' ≤ ((ds ++ ce.take (sint.nat k)).length : Int)⌝ ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ (ce.length : Int)⌝ ∗
      -- (2026-10-15, stage N) the configuration, as the conf entries applied so far left it
      "Hncfg" ∷ nodeCfg γp.node ca' cfg' ∗
      "%Hrc" ∷ ⌜RunCfg (ds ++ ce) (ds ++ ce.take (sint.nat k)).length ca' cfg' c0 c1⌝)
    $$ [i e Hrun applied Hncfg]
  · iexists W64 0, _, a, ca, cfg
    iframe i e applied Hncfg
    simp only [show sint.nat (W64 0) = 0 by rfl, List.take_zero, List.append_nil]
    iframe Hrun
    ipureintro
    refine ⟨Ha, by constructor <;> word, Hrc.1,
      NoConfIn_prefix (List.prefix_append _ _) (Nat.le_refl _) Hrc.2.1, Hrc.2.2⟩
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
    -- (2026-10-15, stage N) the entry's data: a conf-change entry carries `op`
    imod node_entry_data γp.node id n (ds ++ ce.take (sint.nat k)) en ⊤ CoPset.subseteq_top
      $$ HisNode Hc1 with ⟨%o, #Ho⟩
    have Hpos : (ds ++ ce)[(ds ++ ce.take (sint.nat k)).length]? = some en := by
      rw [List.getElem?_append_right (by simp only [List.length_append, List.length_take]; omega)]
      simp only [List.length_append, List.length_take]
      rw [show ds.length + min (sint.nat k) ce.length - ds.length = sint.nat k by omega]
      exact Hen
    have Hlen : (ds ++ ce.take (sint.nat k)).length < (ds ++ ce).length := by
      simp only [List.length_append, List.length_take]; omega
    -- `if e.GetType() == pb.EntryConfChange { ... r.node.ApplyConfChange(&cc) }`
    wp_apply wp_Entry_GetType.1 ln DFrac.discard en $$ [$Hpbinit $Hent] as -
    wp_join iprop(∃ (ca'' : Nat) (cfg'' : CCState), nodeCfg γp.node ca'' cfg'' ∗
        ⌜RunCfg (ds ++ ce) ((ds ++ ce.take (sint.nat k)).length + 1) ca'' cfg'' c0 c1⌝ ∗
        e_ptr ↦ ln ∗ r_ptr ↦ r)
      at next with [Hncfg e r] as ⟨%ca'', %cfg'', Hncfg, %Hrc', e, r⟩
    · by_cases Hty1 : en.Type' = W32 1
      · rw [decide_eq_true Hty1]
        ihave %Hm := regCC_confData γp.node op c0 c1 Hcc en o Hty1 $$ Ho
        obtain ⟨m, Hm, Hop⟩ := Hm
        wp_auto
        -- `proto.Unmarshal(e.GetData(), &cc)`: the bytes decode (the error is nil)
        wp_apply wp_Entry_GetData.1 ln DFrac.discard en $$ [$Hpbinit $Hent] as %ds1 ⟨#Hds1, -⟩
        wp_apply wp_proto_UnmarshalConfChange ds1 en.Data' DFrac.discard cc_ptr _
          $$ [$Hprotoinit $Hds1 $cc] as %err ⟨-, Hres⟩
        rw [Hm]
        icases Hres with ⟨%Herr, Hown⟩
        imod ownCCV1_persist $$ Hown with #Hown
        try wp_auto
        -- `r.node.ApplyConfChange(&cc)`: the next conf entry's change, `op`
        have Hpre : ∀ dec c0' h0' h1', γp.node.mode = .dyn dec c0' h0' h1' →
            DynCCPreOp dec (ds ++ ce) ca' cfg' (ccV2Of (.v1 m))
              (ds ++ ce.take (sint.nat k)).length en c1 := by
          intro dec c0' h0' h1' hm'
          obtain ⟨⟨h0, h1, hm⟩, -, Hs0, Hs1, Hal⟩ := Hcc
          rw [hm] at hm'
          cases hm'
          refine ⟨Hrc.1, Hlen, Hpos, .inl Hty1, Hrc.2.1, ?_, ?_, Hal⟩
          · show some op = some (ccV2Of (.v1 m)); rw [Hop]
          · rw [Hop]; rcases Hrc.2.2 with rfl | rfl
            · exact Hs0
            · exact Hs1
        have Hnst : γp.node.mode ≠ .static := by
          obtain ⟨⟨h0, h1, hm⟩, -⟩ := Hcc; rw [hm]; intro h; cases h
        ihave Hcci : ownCCI (interface.mkOk (go.GoType.PointerType raftpb.ConfChange.ty) #cc_ptr)
            DFrac.discard (some (.v1 m)) $$ []
        · simp only [ownCCI]
          iexists cc_ptr
          iframe Hown
          ipureintro; rfl
        wp_apply wp_node_ApplyConfChange γp.node id n
            (interface.mkOk (go.GoType.PointerType raftpb.ConfChange.ty) #cc_ptr) (.v1 m)
            (ds ++ ce) ca' cfg' (ds ++ ce.take (sint.nat k)).length en c1
            (fun h => absurd h Hnst) Hpre
          $$ [$Hraftinit $HisNode $Hcci Hncfg] as %csp %cs ⟨-, Hpost⟩
        · iright
          iframe Hncfg
          iexact Hdlb
        icases Hpost with (⟨%Hs, -⟩ | ⟨-, Hncfg, -⟩)
        · exact absurd Hs Hnst
        try wp_auto
        wp_join_done
        iexists (ds ++ ce.take (sint.nat k)).length + 1, c1
        iframe Hncfg e r
        ipureintro
        exact ⟨Nat.le_refl _, NoConfIn_empty _ _, .inr rfl⟩
      · rw [decide_eq_false Hty1]
        ihave %Hnc := regCC_notConf γp.node op c0 c1 Hcc en o $$ Ho
        wp_auto
        wp_join_done
        iexists ca', cfg'
        iframe Hncfg e r
        ipureintro
        refine ⟨by have := Hrc.1; omega, ?_, Hrc.2.2⟩
        intro j x hj1 hj2 hx
        by_cases hj : j < (ds ++ ce.take (sint.nat k)).length
        · exact Hrc.2.1 j x hj1 hj hx
        · have hj' : j = (ds ++ ce.take (sint.nat k)).length := by omega
          subst hj'
          rw [Hpos] at hx
          cases hx
          exact Hnc Hty1
    rw [Hraft]
    wp_apply wp_apply γr γp r id n st (ds ++ ce.take (sint.nat k)) ln en
      $$ [$Hpkg $Hrep $Hrun $Hent $Hc1] as Hrun
    wp_for_post
    iframe
    iexists k + W64 1, ln, a' + W64 1, ca'', cfg''
    rw [show sint.nat (k + W64 1) = sint.nat k + 1 by word, Htk, List.append_assoc]
    iframe
    ipureintro
    have Hl : ((ds ++ (ce.take (sint.nat k) ++ [en])).length : Int) =
        ((ds ++ ce.take (sint.nat k)).length : Int) + 1 := by simp; omega
    refine ⟨?_, ?_, ?_⟩
    · rw [Hl]; word
    · constructor <;> word
    · rw [← List.append_assoc, List.length_append, List.length_singleton]; exact Hrc'
  · have Hfull : sint.nat k = ce.length := by word
    rw [Hfull, List.take_of_length_le (by omega)] at Ha Hrc ⊢
    -- the reads whose index is applied, answered
    wp_apply wp_answer γr γp r id n st (ds ++ ce) pv' (ps ++ vs) (DFrac.own 1) a' Ha
      $$ [$Hpkg $Hrep $Hrun $Hpv $Hps] as %rest ⟨Hrun, %ps', Hrest, Hcap, Hps'⟩
    wp_apply wp_node_Advance γp.node id n (ds ++ ce) es ca' cfg' (fun _ => Hrc.2.1)
      $$ [$Hraftinit $Hbusy $Hrcpt $Hncfg] as ⟨Hdrv, Hncfg⟩
    wp_for_post
    iframe
    iexists ds ++ ce, rdv', rest, ps', a', ca', cfg'
    iframe
    ipureintro; exact ⟨Ha, Hrc⟩

end proof

end register
end EtcdGrove
end Perennial

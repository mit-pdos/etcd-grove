/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvreconf/Replica__applyEntry.lean`. Lean-first
(no Rocq counterpart).

By the entry's type: normal, `applyOp` (`appNode_noConf` for the view); a conf change, decoded with
`proto.Unmarshal` (it decodes: every committed conf entry is shaped, `rkv_confShaped`, so the `panic`
is unreachable), frozen read-only and decided by `applyConf`; another type, nothing
(`repOwn_other`). Then `r.index` written with both halves under the lock, at the entry's index.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Replica__applyEntry
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Replica__applyOp
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Replica__applyConf
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetType
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetData
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetIndex
public import Spec.google_golang_org.protobuf.proto.UnmarshalConfChange
public import Spec.google_golang_org.protobuf.proto.UnmarshalConfChangeV2
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.EntryLemmas
public import Proof.go_etcd_io.raft.v3.FrameH

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvreconf.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [StorageModel GF] [AllG GF]

/-- `proto.Unmarshal` of bytes that decode (a `ConfChange`). -/
theorem unmarshal1_ok (bs : List w8) (cm : ConfChangeM) (p : Loc) (err : GoInterface)
    (h : ccDecodeV1 bs = some cm) :
    (match ccDecodeV1 bs with
      | some m => iprop(⌜err = interface.nil⌝ ∗ ownConfChange p (DFrac.own 1) m)
      | none => iprop(⌜err ≠ interface.nil⌝ ∗ ∃ x' : raftpb.ConfChange, p ↦ x') : IProp GF) ⊢
      ⌜err = interface.nil⌝ ∗ ownConfChange p (DFrac.own 1) cm := by
  rw [h]

/-- `proto.Unmarshal` of bytes that decode (a `ConfChangeV2`). -/
theorem unmarshal2_ok (bs : List w8) (cc : ConfChangeV2M) (p : Loc) (err : GoInterface)
    (h : ccDecodeV2 bs = some cc) :
    (match ccDecodeV2 bs with
      | some m => iprop(⌜err = interface.nil⌝ ∗ ownConfChangeV2 p (DFrac.own 1) m)
      | none => iprop(⌜err ≠ interface.nil⌝ ∗ ∃ x' : raftpb.ConfChangeV2, p ↦ x') : IProp GF) ⊢
      ⌜err = interface.nil⌝ ∗ ownConfChangeV2 p (DFrac.own 1) cc := by
  rw [h]

set_option hygiene false in
/-- `applyEntry`'s end: `r.index` moved to the entry's index, from `Hnext`. -/
local macro "applyentry_tail" : tactic => `(tactic| (
    icases Hnext with ⟨%csp', %m', %A', Hown, Hn⟩
    iunfold repOwn at Hown
    iNamed Hown
    try wp_auto
    wp_apply sync.Mutex.wp_Lock _ _ $$ [$(frameH `Hmu)] as ⟨Hlocked, HR⟩
    try wp_auto
    wp_apply wp_GetIndex.1 ep DFrac.discard _ $$ [$(frameH `Hpb) $(frameH `Hent)] as -
    iNamed HR
    iunfold repShared at Hrep
    icases Hrep with ⟨%mA0, %A0, %csp0, %c0, %idx0, %ap0, HmA', HA', Hcs', Hidx', #HcsO0, #Hap0, %HA0⟩
    icombine Hidx Hidx' gives %Hieq
    subst Hieq
    ihave Hif := (typedPointsto_half_split _ idx (1 : Qp)).2 $$ [$(frameH `Hidx) $(frameH `Hidx')]
    try wp_auto
    icases (typedPointsto_half_split _ (W64 (ap.length + 1)) (1 : Qp)).1 $$ Hif with ⟨Hidx, Hidx'⟩
    wp_apply sync.Mutex.wp_Unlock _ _ $$ [$(frameH `Hmu) $(frameH `Hlocked) HmA' HA' Hcs' Hidx'
        HmW HW Hwaiters Hns Hseq HmR HRd Hreads]
    · inext
      unfold lockInv repShared
      iexists ns, mW, W, mR, Rd
      iframe
      isplitl [HmA' HA' Hcs' Hidx']
      · iexists mA0, A0, csp0, c0, W64 (ap.length + 1), ap0
        iframe HmA' HA' Hcs' Hidx' HcsO0 Hap0
        ipureintro; exact HA0
      · ipureintro; exact HRdom
    try wp_auto
    iapply HΦ
    iexists csp', m', A'
    iframe Hn Hlive
    unfold repOwn
    iexists mK, K, c
    iframe
    iframe Hap HcsO Hcfg
    ipureintro; exact ⟨Hlen, Hval, HA, Hcsm⟩
  ))

theorem Replica.applyEntry.wp_proof
    (wp_applyOp : Replica.applyOp.spec (GF := GF) (hG := hG))
    (wp_applyConf : Replica.applyConf.spec (GF := GF) (hG := hG))
    (wp_GetType : raftpb.Entry.GetType.spec (GF := GF) (hG := hG))
    (wp_GetData : raftpb.Entry.GetData.spec (GF := GF) (hG := hG))
    (wp_GetIndex : raftpb.Entry.GetIndex.spec (GF := GF) (hG := hG))
    (wp_Unmarshal1 : proto.UnmarshalConfChange.spec (GF := GF) (hG := hG))
    (wp_Unmarshal2 : proto.UnmarshalConfChangeV2.spec (GF := GF) (hG := hG)) :
    Replica.applyEntry.spec (GF := GF) (hG := hG) := by
  intro γr vs id r n st sts q ap idx csp m mA A l e ep Hpre Hlen'
  wp_start as ⟨#Hrep, Hown, Hn, #Hent, #Hl, Hlive⟩
  ihave #Hrep' := Hrep
  iunfold isReplica at Hrep'
  iNamed Hrep'
  have Hk : l[ap.length]? = some e := by
    obtain ⟨t, rfl⟩ := Hpre
    rw [List.append_assoc, List.getElem?_append_right (Nat.le_refl _)]; simp
  ihave #Hce : isCommittedLogLb γr.cluster (ap ++ [e]) $$ []
  · iapply isCommittedLogLb_mono γr.cluster (ap ++ [e]) l Hpre $$ Hl
  ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  ihave #Hproto : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto $$ []
  · iPkgInit
  -- every committed conf entry decodes, with a defined transition
  ihave #Hcl' := Hcl
  iunfold kvrCluster at Hcl'
  icases Hcl' with ⟨-, -, -, -, #Hinv⟩
  imod rkv_confShaped γr l ⊤ (fun _ _ => CoPset.mem_full) $$ Hinv Hl with %Hsh
  have Hesh : e.isConfChange → ConfShaped e := Hsh e (Hpre.subset (by simp))
  try wp_auto
  wp_apply wp_GetType.1 ep DFrac.discard _ $$ [$Hpb $Hent] as -
  simp only [LogEntry.toEntryM]
  try wp_auto
  wp_if_destruct
  · -- a normal entry
    have Ht := Hif
    wp_apply wp_GetData.1 ep DFrac.discard _ $$ [$Hpb $Hent] as %ds ⟨#Hds, -⟩
    simp only [LogEntry.toEntryM]
    wp_apply wp_applyOp γr id r ap idx csp m mA A e ds Ht Hlen' $$ [$Hpkg $Hmu $Hown $Hds $Hce]
      as ⟨%A', Hown⟩
    ihave Hnext : iprop(∃ (csp' : Loc) (m' : Membership) (A' : GMap (List w8) (List w8)),
        repOwn γr r (ap ++ [e]) idx csp' m' mA A' ∗ appNode γr n l (ap.length + 1) m')
        $$ [Hown Hn]
    · iexists csp, m, A'
      iframe Hown
      iapply appNode_noConf γr n l ap.length e m Hk
        (by unfold LogEntry.isConfChange; rw [Ht]; intro h; rcases h with h | h <;> word)
      iexact Hn
    applyentry_tail
  · have Ht0 := Hif
    wp_if_destruct
    · -- a `ConfChange`
      have Ht1 := Hif
      obtain ⟨o, Ho, Htr⟩ := Hesh (.inl Ht1)
      obtain ⟨cm, Hcm, rfl⟩ : ∃ cm, ccDecodeV1 e.data = some cm ∧ o = .v1 cm := by
        unfold ccDecode at Ho; rw [if_pos Ht1] at Ho
        cases h : ccDecodeV1 e.data with
        | none => rw [h] at Ho; cases Ho
        | some cm => rw [h] at Ho; cases Ho; exact ⟨cm, rfl, rfl⟩
      try wp_auto
      wp_apply wp_GetData.1 ep DFrac.discard _ $$ [$Hpb $Hent] as %ds ⟨#Hds, -⟩
      simp only [LogEntry.toEntryM]
      wp_apply wp_Unmarshal1 ds _ DFrac.discard cc_ptr _ $$ [$Hproto $Hds $cc] as %er ⟨-, Hres⟩

      irevert Hres
      rw [Hcm]
      iintro Hres
      icases Hres with ⟨%Herr, Hcc⟩
      subst Herr
      imod ownConfChange_persist cc_ptr (DFrac.own 1) cm $$ Hcc with #Hcc
      ihave #Hci : ownConfChangeI (interface.mkOk (go.GoType.PointerType raftpb.ConfChange.ty) #cc_ptr)
          DFrac.discard (some (.v1 cm)) $$ []
      · simp only [ownConfChangeI]; iexists cc_ptr; iframe Hcc; ipureintro; rfl
      try wp_auto
      wp_apply wp_applyConf γr vs id r n st sts q ap idx csp m mA A l e _ (.v1 cm) Hpre Ho Htr Hlen'
        $$ [$Hrep $Hown $Hn $Hci $Hl $Hlive] as Hc0
      icases Hc0 with ⟨%csp1, %m1, Hro, Han, Hlive⟩
      ihave Hnext : iprop(∃ (csp' : Loc) (m' : Membership) (A' : GMap (List w8) (List w8)),
          repOwn γr r (ap ++ [e]) idx csp' m' mA A' ∗ appNode γr n l (ap.length + 1) m')
          $$ [Hro Han]
      · iexists csp1, m1, A; iframe Hro Han
      applyentry_tail
    · have Ht1 := Hif
      wp_if_destruct
      · -- a `ConfChangeV2`
        have Ht2 := Hif
        obtain ⟨o, Ho, Htr⟩ := Hesh (.inr Ht2)
        obtain ⟨cc, Hcc2, rfl⟩ : ∃ cc, ccDecodeV2 e.data = some cc ∧ o = .v2 cc := by
          unfold ccDecode at Ho; rw [if_neg Ht1, if_pos Ht2] at Ho
          cases h : ccDecodeV2 e.data with
          | none => rw [h] at Ho; cases Ho
          | some cc => rw [h] at Ho; cases Ho; exact ⟨cc, rfl, rfl⟩
        try wp_auto
        wp_apply wp_GetData.1 ep DFrac.discard _ $$ [$Hpb $Hent] as %ds ⟨#Hds, -⟩
        simp only [LogEntry.toEntryM]
        wp_apply wp_Unmarshal2 ds _ DFrac.discard cc_ptr _ $$ [$Hproto $Hds $cc] as %er ⟨-, Hres⟩
        irevert Hres
        rw [Hcc2]
        iintro Hres
        icases Hres with ⟨%Herr, Hcc⟩
        subst Herr
        imod kvr_ownConfChangeV2_persist cc_ptr (DFrac.own 1) cc $$ Hcc with #Hcc
        ihave #Hci : ownConfChangeI (interface.mkOk (go.GoType.PointerType raftpb.ConfChangeV2.ty)
            #cc_ptr) DFrac.discard (some (.v2 cc)) $$ []
        · simp only [ownConfChangeI]; iexists cc_ptr; iframe Hcc; ipureintro; rfl
        try wp_auto
        wp_apply wp_applyConf γr vs id r n st sts q ap idx csp m mA A l e _ (.v2 cc) Hpre Ho Htr
          Hlen' $$ [$Hrep $Hown $Hn $Hci $Hl $Hlive] as Hc0
        icases Hc0 with ⟨%csp1, %m1, Hro, Han, Hlive⟩
        ihave Hnext : iprop(∃ (csp' : Loc) (m' : Membership) (A' : GMap (List w8) (List w8)),
            repOwn γr r (ap ++ [e]) idx csp' m' mA A' ∗ appNode γr n l (ap.length + 1) m')
            $$ [Hro Han]
        · iexists csp1, m1, A; iframe Hro Han
        applyentry_tail
      · -- another type: nothing
        have Ht2 := Hif
        have Hc : ¬ e.isConfChange := fun h => h.elim Ht1 Ht2
        ihave Hnext : iprop(∃ (csp' : Loc) (m' : Membership) (A' : GMap (List w8) (List w8)),
            repOwn γr r (ap ++ [e]) idx csp' m' mA A' ∗
            appNode γr n l (ap.length + 1) m') $$ [Hown Hn]
        · iexists csp, m, A
          isplitl [Hown]
          · iapply repOwn_other γr r ap idx csp m mA A e Ht0 Hc Hlen'
            iframe Hce Hown
          · iapply appNode_noConf γr n l ap.length e m Hk Hc
            iexact Hn
        applyentry_tail

end proof

end kvreconf
end EtcdGrove
end Perennial

/-
#33 S4 (P-raft-3), `notes/antithesis-rawnode-design.md` §2.2, §2.6, §2.7. **`RawNode.Ready`, the
strengthened triple** (`RawNode.Ready.absSpec`, `RawNodeAbsSpecs.lean`); the old spec is its
corollary (`RawNode.Ready.spec_of_abs`, `RawNodeSpecOfAbs.lean`). The proof is `RawNode__Ready.lean`'s
composition (`readyWithoutAccept`, the hand-out, `acceptReady`) at the node's protocol state: the
first half leaves the node at a named state `s` reading as `ps` (`ownRawNodeReadyS`), the hand-out
keeps `s` (`ownRawNodeReady_handout_at`), and the second half closes `ownRawNodeAt` at `s`'s reading
with the outbox and the read states cleared (`pAccepted ps`). `ReadyOut` is the two halves' facts
put together: the messages' readings and the role from the first, the hard state, the durable
state, the entries and the boundary from the second.

A sibling of the function's proof file (the layout: a proof file exposes only its `wp_proof`), which
`RawNode__Ready.lean` applies.
-/
module

public import Proof.go_etcd_io.raft.v3.RawNodeAbsSpecs
public import Proof.go_etcd_io.raft.v3.RawNodeAtLemmas
public import Proof.go_etcd_io.raft.v3.RawNodeReadyAt
public import Proof.go_etcd_io.raft.v3.RawNodeAtScope
public import Spec.go_etcd_io.raft.v3.RawNode__readyWithoutAccept
public import Spec.go_etcd_io.raft.v3.RawNode__acceptReady
-- (2026-11-01, durability stage II (k)) *enter* (`raft_enter`)
import Proof.go_etcd_io.raft.v3.Protocol.Enter

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem RawNode.Ready.wp_absProof
    (wp_RawNode_readyWithoutAccept : RawNode.readyWithoutAccept.spec (GF := GF) (hG := hG))
    (wp_RawNode_acceptReady : RawNode.acceptReady.spec (GF := GF) (hG := hG)) :
    RawNode.Ready.absSpec (GF := GF) (hG := hG) := by
  intro sc γ rn id x rs r qs ip q g Hsteps0 Hunp0 HtrG
  wp_start as H
  iNamed H
  wp_auto
  -- (antithesis parity B1) in the scope the ghost prefix is empty, before and after
  icases ownRawNodeAt_fp_nil γ rn id rs r qs ip sc $$ Hrn with ⟨%Hfp1, Hrn⟩
  wp_apply wp_RawNode_readyWithoutAccept γ rn id rs r qs ip sc Hsteps0 Hunp0 $$ [$Hrn]
    as %rd %ce %es %ms %sts %h %L H
  iNamed H
  icases Hrn with ⟨%s, Hrn, Hsc, %Hrw, %ss1, #Hss1, %Hrole1⟩
  obtain ⟨Hps, Hip, Hmsperm, Hto, Hscf⟩ := Hrw
  ihave %Hssn1 := softStateIs_null rd.SoftState' ss1 $$ Hss1
  -- (2026-11-01, durability stage II (k)) the hand-out is the cut: the batch queued in `g`, at `s`
  ihave #HhardO := hsOptC_hsOpt _ _ $$ Hhard
  iapply (wp_ncfupd _ _ rfl)
  unfold ncfupd
  iintro Hnc
  imod ownRawNodeReady_handout_at ⊤ γ rn id rs rd ce es ms L x q g h s CoPset.subseteq_top
    CoPset.subseteq_top $$ HhardO Hnc Hlive Hfree Hrn
    with ⟨Hnc, %W, %ss0, Hrn, Happ, #Hfrz, #Hdk, Hcr, -, -, Hlive, Hpb, #Hss0, %Hssn0, #Hmw, #Hml,
      #Hmss, #Hsrcs, -⟩
  imodintro
  iframe Hnc
  ihave Hsc := rnScopeAt_keep sc rs { rs with bw := W } s s (fun h => h) rfl $$ Hsc
  wp_apply wp_RawNode_acceptReady γ rn id { rs with bw := W } rd ce es ms h L s sc
    (fun h => absurd HtrG h) $$ [$Hrn $Hsc $HhardO]
    as %steps %ss %qs' %ip' H
  iNamed H
  icases Hrn with ⟨%fp2, Hrn⟩
  icases ownRawNodeAt_fp_nil γ rn id _ _ qs' ip' sc $$ Hrn with ⟨%Hfp2, Hrn⟩
  -- the soft state the node records is the cut's, and the one `readyWithoutAccept` read
  ihave %Hsseq := softStateIs_agree rd.SoftState' ss0 ss Hssn0 Hssn $$ [Hss0 Hss]
  · iframe Hss0 Hss
  subst Hsseq
  ihave %Hsseq1 := softStateIs_agree rd.SoftState' ss1 ss0 Hssn1 Hssn0 $$ [Hss1 Hss0]
  · iframe Hss1 Hss0
  subst Hsseq1
  iapply HΦ $$ %rd %ce %es %ms %sts %h %steps %L %ss1 %W
    %({ toRState rs fp2 s with
        p := { toPState s with outbox := [], rd := { (toPState s).rd with states := [] } } }) %qs' %ip'
  iframe Hss Hce Hcommitted Hents Hmsgs Hmsgs_cap Hmsgs_own Hcr Happ Hrs Hrs_ok Hhard Hhsw
    Hsnapz Hfrz Hdk Hlive
  isplitl [Hrn]
  · iExactEq Hrn; rfl
  isplitl [Hpb]
  · iintro %E %q' %HE Hnc ⟨Hd, Hl⟩
    imod raft_enter E γ id rs.dur x q' g (readyDurable rs.dur (phsNext rs.phs h) L es) W HE
      (RaftState.next_wcommit _ _ _ _ _ _) $$ Hnc Hd Hl Hpb
      with ⟨Hnc, Hd, Hl, Hf, #Hfr⟩
    imodintro
    iframe Hnc Hd Hl Hf Hfr
    iapply bigSepL_wand_pers (durFrags (GF := GF) γ id W) (fun q : QMsg => isRaftMsg γ id q.st) ms
      $$ Hmw Hfr
  isplitr
  · iexact Hml
  isplitr
  · iexact Hmss
  isplitr
  · iexact Hsrcs
  ipureintro
  refine ⟨Hmsgs_term, Hpsn, fun md hmd => ?_⟩
  have hsc : sc = true := by cases sc <;> first | rfl | cases hmd
  obtain ⟨Hq, Hhs, Hdur, Hes, Hip', HL⟩ := Hout hsc
  obtain ⟨-, Hdpre, Hdlen, Htyped⟩ := Hscf hsc
  have Hr0 := Hps
  rw [(Hfp1 hsc).1] at Hr0
  subst Hr0
  have Hf2 : fp2 = [] := (Hfp2 hsc).1
  subst Hf2
  refine ⟨rfl, Hq, ⟨⟨by rw [Hrole1, roleProto_stateW64]; rfl,
    fun h => toPState_lead_of_stateW64 s (Hrole1 ▸ h)⟩, Hhs, Hdur, fun e0 he => (Hes e0 he).1,
    by show _ ≡ₚ List.filter _ s.outbox; simpa using Hmsperm, Hto,
    Hdpre, Hdlen, HL⟩, fun e0 he => (Hes e0 he).2.trans Hip, Hip', Hhnew,
    fun q hq => .inl (Htyped q hq),
    fun q hq x hx => by rw [xmsgOf_none_of_absMsgOf (Htyped q hq)] at hx; cases hx⟩

end proof

end EtcdGrove
end Perennial

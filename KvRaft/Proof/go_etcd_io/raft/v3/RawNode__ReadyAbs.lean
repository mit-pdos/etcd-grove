-- The copy for the part `KvRaft/` of `RaftNoAx/Proof/go_etcd_io/raft/v3/RawNode__ReadyAbs.lean` (etc/copy-part.py; rerun it, do not edit).
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

public import KvRaft.Proof.go_etcd_io.raft.v3.RawNodeAbsSpecs
public import KvRaft.Proof.go_etcd_io.raft.v3.RawNodeAtLemmas
public import KvRaft.Proof.go_etcd_io.raft.v3.RawNodeReadyAt
public import KvRaft.Proof.go_etcd_io.raft.v3.RawNodeAtScope
public import KvRaft.Spec.go_etcd_io.raft.v3.RawNode__readyWithoutAccept
public import KvRaft.Spec.go_etcd_io.raft.v3.RawNode__acceptReady
-- (2026-11-01, durability stage II (k)) *enter* (`raft_enter`)
import KvRaft.Proof.go_etcd_io.raft.v3.Protocol.Enter

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section pure
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

/-- (antithesis parity B1, step C4) A queued message of raft's shape with no protocol reading is a transfer
message (`sentShapeTypes`' last two). -/
theorem xmsgOf_isSome_of_shape {st : MsgSt} (H : SentMsgShape st) (h : mtypeOf st.msg.Type' = none) :
    (xmsgOf st).isSome := by
  have e : st.msg.Type' = MsgTimeoutNow ∨ st.msg.Type' = MsgTransferLeader := by
    have h0 : st.msg.Type' ∈ sentTypes ++ [MsgTimeoutNow, MsgTransferLeader] := H.1
    rcases List.mem_append.1 h0 with h1 | h1
    · exfalso
      simp only [sentTypes, List.mem_cons, List.mem_nil_iff, or_false] at h1
      rcases h1 with e | e | e | e | e | e | e | e | e | e | e | e <;> rw [e] at h <;> cases h
    · simpa only [List.mem_cons, List.mem_nil_iff, or_false] using h1
  unfold xmsgOf
  split
  · rfl
  · split
    · rfl
    · rename_i h1 h2
      rcases e with e | e
      · exact absurd e h1
      · exact absurd e h2

/-- (step C4) A message with a transfer reading has no protocol type. -/
theorem mtypeOf_none_of_xmsgOf {st : MsgSt} {x : XMsg} (hx : xmsgOf st = some x) :
    mtypeOf st.msg.Type' = none := by
  unfold xmsgOf at hx
  split at hx
  · rename_i e; rw [e]; rfl
  · split at hx
    · rename_i e; rw [e]; rfl
    · cases hx

/-- (antithesis parity B1) A transfer message of raft's shape has its other numbers zero and no
rejection (`SentMsgShape`'s transfer clause). -/
theorem xmsgOf_zero {st : MsgSt} {x : XMsg} (H : SentMsgShape st) (hx : xmsgOf st = some x) :
    st.msg.Index' = W64 0 ∧ st.msg.LogTerm' = W64 0 ∧ st.msg.Commit' = W64 0 ∧
      st.msg.Reject' = false := by
  have hty : st.msg.Type' = MsgTimeoutNow ∨ st.msg.Type' = MsgTransferLeader := by
    unfold xmsgOf at hx
    split at hx
    · rename_i e; exact .inl e
    · split at hx
      · rename_i e; exact .inr e
      · cases hx
  exact H.2.2.1.2 hty

/-- (step C4) **A handed-out transfer message against the node** (`XReadyOk`): the queued message's
facts (`XQOk`; a stamped transfer request's `NGhost.xw` record) and the scope's (`XScopeOk`: the records
past term `0`, and with non-voters off their destinations members of the names' voters). -/
theorem xReadyOk_of {γ : RaftNames} {md : RnMode} {id : w64} {s : NState} {st : MsgSt} {x : XMsg}
    (hq : XQOk id s st) (hw : st.msg.Type' = MsgTransferLeader →
      (s.gh.xw !! (st.msg.To', st.msg.Term')).isSome)
    (hxw : ∀ p : w64 × w64, (s.gh.xw !! p).isSome →
      (md.nonVoters = false → p.1 ∈ γ.reCfg) ∧ p.2 ≠ W64 0)
    (hxs : ∀ f : w64, (s.gh.xsrc !! f).isSome → (γ.reAcks !! f).isSome)
    (hx : xmsgOf st = some x) : XReadyOk γ md id (toPState s) x := by
  unfold xmsgOf at hx
  split at hx
  · rename_i e
    cases hx
    exact ⟨fun _ => hq.1 e, hq.2.1 (.inl e), (fun h => by cases h), (fun _ h => by cases h),
      (fun h => by cases h)⟩
  · split at hx
    · rename_i e
      cases hx
      have ht : st.msg.Term' ≠ W64 0 := (hxw _ (hw e)).2
      exact ⟨(fun h => by cases h), hq.2.1 (.inr ⟨e, ht⟩), (fun _ => ht), fun hnv _ => (hxw _ (hw e)).1 hnv,
        fun _ => (hq.2.2.2 e).imp (fun h => h) (hxs _)⟩
    · cases hx

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- (step C4) **The handed-out messages' facts at the named state** (`ownRaftPhysReady`'s `XfOk`, the
queues' relation `outboxRelP` and `MsSub`): each one's untyped facts (`XQOk`), its shape, a stamped
transfer request's record, typed until a transfer request is stepped, and a typed one read. -/
theorem ownRawNodeReadyS_xq (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (rd : Ready)
    (ce es : List EntryM) (ms : List QMsg) (h : Bool) (L : Option SnapLoan) (s : NState) :
    ownRawNodeReadyS (GF := GF) γ rn id rs rd ce es ms h L s ⊢
      ⌜∀ q ∈ ms, XQOk id s q.st ∧ SentMsgShape q.st ∧
        (q.st.msg.Type' = MsgTransferLeader →
          (s.gh.xw !! (q.st.msg.To', q.st.msg.Term')).isSome) ∧
        (s.gh.xs = false → mtypeOf q.st.msg.Type' ≠ none) ∧
        (mtypeOf q.st.msg.Type' ≠ none → (absMsgOf q.st).isSome)⌝ ∗
      ownRawNodeReadyS γ rn id rs rd ce es ms h L s := by
  apply persistent_entails_right
  iintro H
  icases H with ⟨%cf, %fp, %ds, %rnv, %sv, %hprev, H⟩
  iNamed H
  iunfold ownRaftPhysReady at Hphys
  icases Hphys with ⟨%rsl, %sl1, %sl2, %ms1, %ms2, Hv⟩
  iNamed Hv
  ipureintro
  intro q hq
  have hq' : q ∈ ms1 ++ ms2 := Hmslen.subset (List.mem_append_left _ hq)
  exact ⟨Hxf.xq q hq', Hxf.1 q hq', Hxf.2.2.1 q hq', fun hx => Hxf.typed_xs hx q hq',
    absMsgOf_isSome_of_rel Houtbox q hq'⟩

/-- (antithesis parity B1, step C4) **At each mode without snapshots the scope names, the `RState`'s ghost
prefix is empty** (and its log's boundary `base0`): `ownRawNodeAt_fp_nil` at an `Option RnMode`. -/
theorem ownRawNodeAt_fp_nilOpt (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (r : RState)
    (qs : List Msg) (ip : Nat) (sc : Option RnMode) (hs : ∀ md, sc = some md → md.snapshots = false) :
    ownRawNodeAt (GF := GF) γ rn id rs r qs ip sc ⊢
      ⌜∀ md, sc = some md → r.fp = [] ∧ r.p.base = base0⌝ ∗ ownRawNodeAt γ rn id rs r qs ip sc := by
  cases sc with
  | none => iintro H; iframe H; ipureintro; intro md h; cases h
  | some md0 =>
    iintro H
    iNamed H
    icases rnScopeAt_pureOpt (some md0) rs s $$ Hsc with ⟨%Hscope, Hsc⟩
    have Hsn := (Hscope md0 rfl).1.2.2.2.2.1 (hs md0 rfl)
    icases ownStepGhost_fp_nil γ rs fp ds cf id s (Hscope md0 rfl).2.1.2.2.2 Hsn.2.1
      $$ Hghost with ⟨%Hfp, Hghost⟩
    isplitr
    · ipureintro; intro _ _; subst Hps Hfp
      exact ⟨rfl, Hsn.2.1⟩
    unfold ownRawNodeAt
    iexists s, cf, fp, ds, rnv, sv, hprev, steps
    iframe Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hsteps_cap Hpend Hdeliv Hstrecs Hloanc Hsloc Hhist
      Hledger Hdur Hrntr Hsc
    ipureintro
    exact ⟨Hwf, Hin, Hasync, Hdlen, Hunp, Hsnap, Hstok, Htrm, Hstor, Hpvoff, Hrs_out,
      Hrs_unst, Hrs_clb, Hrnfl, Hloan, Hsdt, Hrole, Hphs, Hgtr, Hglq, Hps, Hip⟩

theorem RawNode.Ready.wp_absProof
    (wp_RawNode_readyWithoutAccept : RawNode.readyWithoutAccept.spec (GF := GF) (hG := hG))
    (wp_RawNode_acceptReady : RawNode.acceptReady.spec (GF := GF) (hG := hG)) :
    RawNode.Ready.absSpec (GF := GF) (hG := hG) := by
  intro sc hsc0 γ rn id x rs r qs ip q g Hsteps0 Hunp0 HtrG
  wp_start as H
  iNamed H
  wp_auto
  -- (antithesis parity B1) in the scope the ghost prefix is empty, before and after
  icases ownRawNodeAt_fp_nilOpt γ rn id rs r qs ip sc (fun md h => (hsc0 md h).1) $$ Hrn
    with ⟨%Hfp1, Hrn⟩
  wp_apply wp_RawNode_readyWithoutAccept γ rn id rs r qs ip sc hsc0 Hsteps0 Hunp0 $$ [$Hrn]
    as %rd %ce %es %ms %sts %h %L H
  iNamed H
  icases Hrn with ⟨%s, Hrn, Hsc, %Hrw, %ss1, #Hss1, %Hrole1⟩
  -- (antithesis parity B1, step C4) the handed-out messages' facts, and the scope's transfer facts
  icases ownRawNodeReadyS_xq γ rn id rs rd ce es ms false L s $$ Hrn with ⟨%Hxq, Hrn⟩
  icases rnScopeAt_pureOpt sc rs s $$ Hsc with ⟨%Hscope1, Hsc⟩
  have Hty1 : ∀ q ∈ ms, (absMsgOf q.st).isSome ∨ (xmsgOf q.st).isSome := fun q hq => by
    by_cases hm : mtypeOf q.st.msg.Type' = none
    · exact .inr (xmsgOf_isSome_of_shape (Hxq q hq).2.1 hm)
    · exact .inl ((Hxq q hq).2.2.2.2 hm)
  have Hxr : ∀ md, sc = some md → ∀ q ∈ ms, ∀ x, xmsgOf q.st = some x →
      XReadyOk γ md id (toPState s) x := fun md h q hq x hx => by
    obtain ⟨h1, -, h3, h4, -⟩ := Hxq q hq
    cases ht : md.transfer
    · exact absurd (mtypeOf_none_of_xmsgOf hx) (h4 ((Hscope1 md h).1.2.2.2.2.2.1 ht))
    · exact xReadyOk_of h1 h3 ((Hscope1 md h).2.2.2 ht).2.1 ((Hscope1 md h).2.2.2 ht).2.2.2 hx
  obtain ⟨Hps, Hip, Hmsperm, Hto, Hsts, Hpc, Hscf⟩ := Hrw
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
  ihave Hsc := rnScopeAt_keepOpt sc rs { rs with bw := W } s s (fun _ _ h => h) rfl
    (hx := fun _ _ _ h => h) $$ Hsc
  wp_apply wp_RawNode_acceptReady γ rn id { rs with bw := W } rd ce es ms h L s sc hsc0
    (fun h => absurd HtrG h) $$ [$Hrn $Hsc $HhardO]
    as %steps %ss %qs' %ip' H
  iNamed H
  icases Hrn with ⟨%fp2, Hrn⟩
  icases ownRawNodeAt_fp_nilOpt γ rn id _ _ qs' ip' sc (fun md h => (hsc0 md h).1) $$ Hrn
    with ⟨%Hfp2, Hrn⟩
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
  obtain ⟨Hq, Hhs, Hdur, Hes, Hip', HL⟩ := Hout md hmd
  obtain ⟨Hdpre, Hdlen, -⟩ := Hscf md hmd
  have Hxr' := Hxr md hmd
  have Hr0 := Hps
  rw [(Hfp1 md hmd).1] at Hr0
  subst Hr0
  have Hf2 : fp2 = [] := (Hfp2 md hmd).1
  subst Hf2
  refine ⟨rfl, Hq, ⟨⟨by rw [Hrole1, roleProto_stateW64]; rfl,
    fun h => toPState_lead_of_stateW64 s (Hrole1 ▸ h)⟩, Hhs, Hdur, fun e0 he => (Hes e0 he).1,
    by show _ ≡ₚ List.filter _ s.outbox; simpa using Hmsperm, Hto,
    Hdpre, Hdlen, HL⟩, fun e0 he => (Hes e0 he).2.trans Hip, Hip', Hhnew,
    Hty1, Hxr', (Hscf md hmd).2.2, fun q hq x hx => xmsgOf_zero (Hxq q hq).2.1 hx, fun h => ?_, by rw [Hsts, toRState_p, toPState_rd_states]⟩
  -- (antithesis parity B1, group E's S4) the node constant's pre-vote flag the raft state's (`KTie`)
  have hk : NodeK.mk s.prevote s.cq s.sdr = rs.k := (Hscope1 md hmd).2.2.1
  rw [← hk]
  exact Hpc (by
    rw [Hrole1] at h
    cases hr : s.role <;> simp_all [stateW64, StateFollower, StateCandidate, StateLeader,
      StatePreCandidate])

end proof

end EtcdGrove
end Perennial

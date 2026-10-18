/-
Port of election_proof/proof_raft__handleAppendEntries.v.

raft v3.7 (stage R4): the message (`msgIn`, taken) lends its `Entries` slice to
`logSliceFromMsgApp`; the elements are read-only, so the message is put back at once without its
capacity, which goes to `maybeAppend`. The scalars are read by the getters; each reply
`&pb.Message{To: m.From, Type: MsgAppResp.Enum(), Index: new(...), ...}` shares the request's
`From` cell and is built owned (`msgOwn_lit0`).
-/
module

public import Spec.go_etcd_io.raft.v3.raft__handleAppendEntries
public import Spec.go_etcd_io.raft.v3.logSliceFromMsgApp
public import Spec.go_etcd_io.raft.v3.raftLog__maybeAppend
public import Spec.go_etcd_io.raft.v3.raftLog__term
public import Spec.go_etcd_io.raft.v3.raftLog__zeroTermOnOutOfBounds
public import Spec.go_etcd_io.raft.v3.raftLog__lastIndex
public import Spec.go_etcd_io.raft.v3.raftLog__findConflictByTerm
public import Spec.go_etcd_io.raft.v3.raft__send
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetCommit
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetIndex
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetLogTerm
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetFrom
public import Spec.go_etcd_io.raft.v3.raftpb.MessageType__Enum
public import Proof.go_etcd_io.raft.v3.LemmasSendRB

@[expose] public section

set_option linter.unusedSectionVars false

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

/-- `r.send(&pb.Message{To: dst, Type: pb.MsgAppResp.Enum(), Index: ..., ...})`, the reply
built: `SendOk`'s `MsgAppResp` clause (d) with no entries. -/
private theorem wp_send_appResp (wp_raft_send : raft.send.spec (GF := GF) (hG := hG))
    (c : CfgM) (r : Loc) (id : w64) (s : NState) (ml : Loc) (dst idx hintterm hint : w64)
    (rej : Bool) (Hdst : dst ≠ id) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhysCV c c.voters r id s ∗
        msgOwn ml (DFrac.own 1) ⟨⟨W32 4, dst, 0, 0, hintterm, idx, 0, 0, rej, hint⟩, [], none, [], []⟩ }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"send")) (Val #ml))
    {{ RET #(); ownRaftPhysCV c c.voters r id (sendMsgs s [appResp id s dst rej idx hintterm hint]) }} := by
  iintro %Φ ⟨#Hpkg, Hphys, Hm⟩ HΦ
  wp_apply wp_raft_send c r id s ml _ [] none [] [] [appResp id s dst rej idx hintterm hint]
      (Or.inl rfl) (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, fun h => absurd h Hdst, rfl⟩))))
      (fun h => absurd h (by simp [MsgSnap])) $$ [$Hphys $Hm] as Hphys
  iapply HΦ
  iexact Hphys

set_option hygiene false in
/-- The reply's prefix: `To: m.From` (the request's cell, shared), `Type: MsgAppResp.Enum()`. -/
local macro "reply_head" : tactic => `(tactic| (
  icases msgPtsC_From_acc _ _ _ _ _ $$ Hm with ⟨%pfr, HFr, #cFr, HmB⟩
  wp_auto
  ihave Hm := HmB $$ HFr
  rw [show raftpb.MsgAppResp = #((W32 4 : raftpb.MessageType)) from rfl]
  haveI : go.NotInterface go.int32 := ⟨by unfold go.int32; trivial⟩
  wp_apply wp_MessageType_Enum (W32 4)
  iintro %pty Hpty
  imod cellRO_alloc $$ Hpty with #cTy
  try wp_auto))

/-- The three exits of `HandleAppResult`, in the body's order.

- `a.prev.index < committed`: `committed` is read twice through the log's struct
  (`ownRaftLog_struct`), once for the test and once for the reply.
- `maybeAppend`: the log is taken out at its state and put back at whatever
  `maybeAppend` leaves (`ownRaftPhysC_log_at`); on `ok` that is the new `ls'`, on `!ok`
  its spec says `ls' = ls`.
- the reject path: the `Debugf`'s arguments call `term(m.Index)` and hand its error to
  `zeroTermOnOutOfBounds`, whose premise is exactly `term`'s last conjunct; then
  `min(m.Index, lastIndex())`, `findConflictByTerm`, and the rejecting reply.

Every `send` is `SendOk`'s `MsgAppResp` clause (d) with no entries. -/
theorem raft.handleAppendEntries.wp_proof
    (wp_logSliceFromMsgApp : logSliceFromMsgApp.spec (GF := GF) (hG := hG))
    (wp_raftLog_maybeAppend : raftLog.maybeAppend.spec (GF := GF) (hG := hG))
    (wp_raftLog_term : raftLog.term.spec (GF := GF) (hG := hG))
    (wp_raftLog_zeroTermOnOutOfBounds : raftLog.zeroTermOnOutOfBounds.spec (GF := GF) (hG := hG))
    (wp_raftLog_lastIndex : raftLog.lastIndex.spec (GF := GF) (hG := hG))
    (wp_raftLog_findConflictByTerm : raftLog.findConflictByTerm.spec (GF := GF) (hG := hG))
    (wp_raft_send : raft.send.spec (GF := GF) (hG := hG))
    (wp_GetCommit : raftpb.Message.GetCommit.spec (GF := GF) (hG := hG))
    (wp_GetIndex : raftpb.Message.GetIndex.spec (GF := GF) (hG := hG))
    (wp_GetLogTerm : raftpb.Message.GetLogTerm.spec (GF := GF) (hG := hG))
    (wp_GetFrom : raftpb.Message.GetFrom.spec (GF := GF) (hG := hG))
    (wp_MessageType_Enum : raftpb.MessageType.Enum.spec (GF := GF) (hG := hG)) :
    raft.handleAppendEntries.spec (GF := GF) (hG := hG) := by
  intro c r id s ml m ents sn ctx rs Hwf Hnw Hconf Hfid Htyapp Hnl
  wp_start as Hpre
  iNamed Hpre
  simp only [msgIn, needsCap_of_eq Htyapp]
  wp_auto
  wp_apply wp_logSliceFromMsgApp $$ [$Hm] as %es %els ⟨#Hes, #Hents, Hcap, Hmback⟩
  ihave Hm := Hmback $$ %false %els %ents Hes Hents []
  · simp only [Bool.false_eq_true, ↓reduceIte]; iempintro
  try simp only
  -- the stale test reads `r.raftLog.committed`
  wp_apply raft.wp_load_raftLogC $$ Hphys as Hphys
  icases ownRaftPhysC_log_same c r id s $$ Hphys with ⟨Hlog, Hlogback⟩
  icases ownRaftLog_struct _ _ $$ Hlog with ⟨%lv, Hl, %Hlv, Hlb⟩
  wp_auto
  ihave Hlog := Hlb $$ Hl
  ihave Hphys := Hlogback $$ Hlog
  obtain ⟨Hcm, -⟩ := Hlv
  rw [Hcm]
  wp_if_destruct
  · -- stale: acknowledge `committed`
    reply_head
    wp_apply raft.wp_load_raftLogC $$ Hphys as Hphys
    icases ownRaftPhysC_log_same c r id s $$ Hphys with ⟨Hlog, Hlogback⟩
    icases ownRaftLog_struct _ _ $$ Hlog with ⟨%lv2, Hl, %Hlv2, Hlb⟩
    wp_auto
    ihave Hlog := Hlb $$ Hl
    ihave Hphys := Hlogback $$ Hlog
    imod cellRO_alloc $$ «$v2» with #cIx
    imod msgOwn_lit0 «$a0_ptr» _ ⟨W32 4, m.From', 0, 0, 0, lv2.committed', 0, 0, false, 0⟩ ⊤
      $$ [«$a0»] with Hr
    · iframe «$a0» cTy cFr cIx
      isplitr
      · ipureintro; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
      msg_nulls
    obtain ⟨Hcm2, -⟩ := Hlv2
    rw [Hcm2]
    wp_apply wp_send_appResp wp_raft_send (Hdst := Hfid) $$ [$Hphys $Hr] as Hphys
    iapply HΦ
    iframe
    ipureintro
    exact .inl ⟨Hif, rfl⟩
  · -- `maybeAppend`
    wp_apply wp_GetCommit.1 $$ [$Hm] as Hm
    wp_apply raft.wp_load_raftLogC $$ Hphys as Hphys
    icases ownRaftPhysC_log_at c r id s $$ Hphys with ⟨Hlog, %Hgh0, Hlogback⟩
    -- (D19i part 1) `m.Index` at or above `committed`, so above the floor
    icases ownRaftLog_fl _ _ $$ Hlog with ⟨%Hflb, Hlog⟩
    wp_apply wp_raftLog_maybeAppend _ s.logst
        (logSlice.mk m.Term' (entryID.mk m.LogTerm' m.Index') es) ents m.Commit'
        Hwf Hnw (fun Hm => Hconf (by omega) Hm) (by simp only; omega) $$ [$Hlog $Hcap]
      as %lastnewi %ok %ls' ⟨Hlog, %Hma, %Hmagh⟩
    · simp only [named, entsPts]; iexists els; iframe Hes Hents
    ihave Hphys := Hlogback $$ %ls' Hlog
      %(fun h => (Hgh0 h).elim (fun h1 => .inl (Hmagh.2 h1)) (fun h1 => .inr (Hmagh.1 ▸ h1)))
      %(fun h => absurd h Hnl)
    cases Hpm : plogMaybeAppend s.logst.prev (s.logst.sents ++ s.logst.uents)
        (entryID.mk m.LogTerm' m.Index') ents with
    | some res =>
      -- accepted
      obtain ⟨lni, es'⟩ := res
      rw [Hpm] at Hma
      obtain ⟨rfl, rfl, Hprev, Hes', Happ, Hcm', Ha', Hsn', Hu', Hst'⟩ := Hma
      wp_auto
      reply_head
      imod cellRO_alloc $$ «$v2» with #cIx
      imod msgOwn_lit0 «$a0_ptr» _ ⟨W32 4, m.From', 0, 0, 0, lastnewi, 0, 0, false, 0⟩ ⊤
        $$ [«$a0»] with Hr
      · iframe «$a0» cTy cFr cIx
        isplitr
        · ipureintro; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
        msg_nulls
      wp_apply wp_send_appResp wp_raft_send (Hdst := Hfid) $$ [$Hphys $Hr] as Hphys
      iapply HΦ
      iframe
      ipureintro
      exact .inr (.inl ⟨by omega, _, es', ls', Hpm, Hprev, Hes', Happ, Hcm',
        ⟨Ha', Hsn', Hu', Hprev, Hst'⟩, rfl⟩)
    | none =>
      -- rejected: `a.prev` does not match
      rw [Hpm] at Hma
      obtain ⟨rfl, rfl, rfl⟩ := Hma
      ihave Hphys : ownRaftPhysCV c c.voters r id s $$ [Hphys]
      · iapply ownRaftPhysC_eq c r id _ _ ?_ $$ Hphys
        cases s; rfl
      have Hnm : ¬ PlogMatches s.logst.prev (s.logst.sents ++ s.logst.uents)
          (entryID.mk m.LogTerm' m.Index') := by
        intro Hc
        unfold plogMaybeAppend at Hpm
        rw [ite_eq_left Hc] at Hpm
        cases Hpm
      wp_auto
      wp_apply raft.wp_load_idC $$ Hphys as Hphys
      wp_apply wp_GetIndex.1 $$ [$Hm] as Hm
      wp_apply raft.wp_load_raftLogC $$ Hphys as Hphys
      icases ownRaftPhysC_log_same c r id s $$ Hphys with ⟨Hlog, Hlogback⟩
      wp_apply wp_raftLog_term $$ [$Hlog] as %t %err ⟨Hlog, -, -, #Herr, -⟩
      ihave Hphys := Hlogback $$ Hlog
      wp_apply raft.wp_load_raftLogC $$ Hphys as Hphys
      wp_apply wp_raftLog_zeroTermOnOutOfBounds $$ [$Herr] as %t' -
      wp_apply wp_GetIndex.1 $$ [$Hm] as Hm
      wp_apply wp_GetLogTerm.1 $$ [$Hm] as Hm
      wp_apply wp_GetIndex.1 $$ [$Hm] as Hm
      wp_apply wp_GetFrom.1 $$ [$Hm] as Hm
      wp_raft_logC
      -- `hintIndex := min(m.Index, lastIndex())`
      wp_apply wp_GetIndex.1 $$ [$Hm] as Hm
      wp_apply raft.wp_load_raftLogC $$ Hphys as Hphys
      icases ownRaftPhysC_log_same c r id s $$ Hphys with ⟨Hlog, Hlogback⟩
      wp_apply wp_raftLog_lastIndex $$ [$Hlog] as %li ⟨Hlog, -⟩
      ihave Hphys := Hlogback $$ Hlog
      wp_apply wp_min2_uint64
      wp_apply wp_GetLogTerm.1 $$ [$Hm] as Hm
      wp_apply raft.wp_load_raftLogC $$ Hphys as Hphys
      icases ownRaftPhysC_log_same c r id s $$ Hphys with ⟨Hlog, Hlogback⟩
      wp_apply wp_raftLog_findConflictByTerm $$ [$Hlog] as %hint %hintterm ⟨Hlog, -⟩
      ihave Hphys := Hlogback $$ Hlog
      try wp_auto
      reply_head
      wp_apply wp_GetIndex.1 $$ [$Hm] as Hm
      imod cellRO_alloc $$ «$v2» with #cIx
      imod cellRO_alloc $$ «$v3» with #cRj
      imod cellRO_alloc $$ «$v4» with #cRh
      imod cellRO_alloc $$ «$v5» with #cLt
      imod msgOwn_lit0 «$a0_ptr» _ ⟨W32 4, m.From', 0, 0, hintterm, m.Index', 0, 0, true, hint⟩ ⊤
        $$ [«$a0»] with Hr
      · iframe «$a0» cTy cFr cIx cRj cRh cLt
        isplitr
        · ipureintro; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
        msg_nulls
      wp_apply wp_send_appResp wp_raft_send (Hdst := Hfid) $$ [$Hphys $Hr] as Hphys
      iapply HΦ
      iframe
      ipureintro
      exact .inr (.inr ⟨by omega, Hnm, hint, hintterm, rfl⟩)

end proof

end EtcdGrove
end Perennial

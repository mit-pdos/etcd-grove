/-
Proof of `Spec/go_etcd_io/raft/v3/newStorageAppendRespMsg.lean`. Lean-first (stage R5: the old
proof inlined it in `RawNode.acceptReady`'s, for a log with unstable entries only).
-/
module

public import Spec.go_etcd_io.raft.v3.newStorageAppendRespMsg
public import Spec.go_etcd_io.raft.v3.raftLog__hasNextOrInProgressUnstableEnts
public import Spec.go_etcd_io.raft.v3.raftLog__lastEntryID
public import Spec.go_etcd_io.raft.v3.IsEmptySnap
public import Spec.go_etcd_io.raft.v3.raftpb.MessageType__Enum
public import Proof.go_etcd_io.raft.v3.LemmasRawnodeR

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

/-- A fresh message (`msgOwn_lit0`); with unstable entries, its `Index`/`LogTerm` stored as
fresh cells holding the log's last entry id (`msgPtsC_store_Index`/`_LogTerm`); the `Ready`'s
snapshot is `nil`, so `Snapshot` stays unset. -/
theorem newStorageAppendRespMsg.wp_proof
    (wp_raftLog_hasNextOrInProgressUnstableEnts :
      raftLog.hasNextOrInProgressUnstableEnts.spec (GF := GF) (hG := hG))
    (wp_raftLog_lastEntryID : raftLog.lastEntryID.spec (GF := GF) (hG := hG))
    (wp_IsEmptySnap : IsEmptySnap.spec (GF := GF) (hG := hG))
    (wp_MessageType_Enum : raftpb.MessageType.Enum.spec (GF := GF) (hG := hG)) :
    newStorageAppendRespMsg.spec (GF := GF) (hG := hG) := by
  intro hw r id t l ls rd dq o Hne
  wp_start as ⟨#Hid, Ht, Hrl, Hlog, Hsn⟩
  wp_auto
  rw [show raftpb.MsgStorageAppendResp = #((W32 20 : raftpb.MessageType)) from rfl]
  haveI : go.NotInterface go.int32 := ⟨by unfold go.int32; trivial⟩
  wp_apply wp_MessageType_Enum (W32 20) as %pty Hpty
  rw [show go_etcd_io.raft.v3.LocalAppendThread = #(W64 18446744073709551615) from rfl]
  wp_auto
  imod cellRO_alloc $$ Hpty with #cTy
  imod cellRO_alloc $$ «$v1» with #cTo
  imod cellRO_alloc $$ «$v2» with #cFr
  imod cellRO_alloc $$ «$v3» with #cTe
  imod msgOwn_lit0 «$r0_ptr» _ (appendAckM id t (entryID.mk (W64 0) (W64 0))) ⊤ $$ [«$r0»] with Hm
  · iframe «$r0»
    simp only [appendAckM, show MsgStorageAppendResp = W32 20 from rfl,
      show EtcdGrove.LocalAppendThread = W64 18446744073709551615 from rfl]
    iframe cTy cTo cFr cTe
    isplitr
    · ipureintro; simp
    msg_nulls
  wp_apply wp_raftLog_hasNextOrInProgressUnstableEnts $$ [$Hlog] as %b ⟨Hlog, %Hb⟩
  cases b
  · wp_auto
    have Hne' : ¬ ls.uents ≠ [] := by simpa using Hb.symm
    simp only [Hne', ↓reduceIte]
    wp_apply wp_IsEmptySnap rd.Snapshot' dq o $$ [$Hsn] as %b' ⟨%Hb', Hsn⟩
    cases o with
    | none =>
      simp only [Option.elim] at Hb'
      subst Hb'
      wp_auto
      iapply HΦ
      iframe
      iintro -
      simp only [msgIn, show needsCap (appendAckM id t (entryID.mk (W64 0) (W64 0))) = false from rfl]
      iexact Hm
    | some sv =>
      simp only [Option.elim, decide_eq_false (Hne sv rfl)] at Hb'
      subst Hb'
      icases msgPtsC_store_Snapshot _ _ _ _ $$ Hm with ⟨%pSn, HSn, Hback⟩
      wp_auto
      iapply HΦ
      iframe
      iintro Hs
      simp only [msgIn, show needsCap (appendAckM id t (entryID.mk (W64 0) (W64 0))) = false from rfl]
      iapply Hback $$ HSn Hs
  · wp_auto
    wp_apply wp_raftLog_lastEntryID $$ [$Hlog] as %e ⟨Hlog, %He⟩
    icases msgPtsC_store_Index _ _ _ _ $$ Hm with ⟨%pIx, HIx, Hback⟩
    wp_auto
    imod cellRO_alloc $$ «$r0» with #cLt
    imod cellRO_alloc $$ «$r0» with #cIx
    ihave Hm := Hback $$ %_ %e.index' HIx cIx
    icases msgPtsC_store_LogTerm _ _ _ _ $$ Hm with ⟨%pLt, HLt, Hback⟩
    wp_auto
    ihave Hm := Hback $$ %_ %e.term' HLt cLt
    have Hne' : ls.uents ≠ [] := by simpa using Hb.symm
    simp only [Hne', ne_eq, not_false_eq_true, ↓reduceIte, ← He]
    wp_apply wp_IsEmptySnap rd.Snapshot' dq o $$ [$Hsn] as %b' ⟨%Hb', Hsn⟩
    cases o with
    | none =>
      simp only [Option.elim] at Hb'
      subst Hb'
      wp_auto
      iapply HΦ
      iframe
      iintro -
      simp only [msgIn, show needsCap (appendAckM id t e) = false from rfl]
      simp only [appendAckM]
      iexact Hm
    | some sv =>
      simp only [Option.elim, decide_eq_false (Hne sv rfl)] at Hb'
      subst Hb'
      icases msgPtsC_store_Snapshot _ _ _ _ $$ Hm with ⟨%pSn, HSn, Hback⟩
      wp_auto
      iapply HΦ
      iframe
      iintro Hs
      simp only [msgIn, show needsCap (appendAckM id t e) = false from rfl]
      simp only [appendAckM]
      iapply Hback $$ HSn Hs

end proof

end EtcdGrove
end Perennial

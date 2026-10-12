/-
Port of election_proof/proof_raft__handleAppendEntries.v.
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

/-- The builtin `min` on `uint64` (Rocq `wp_min2_uint64`). -/
private theorem wp_min_u64 (a b : w64) :
    {{ (True : IProp GF) }}
      (App (App (Val #(functions go.min [go.uint64, go.uint64])) (Val #a)) (Val #b))
    {{ RET #(w64Min a b); True }} := by
  wp_start
  wp_if_destruct
  · rw [show w64Min a b = a from ite_eq_left Hif]
    iapply HΦ; itrivial
  · rw [show w64Min a b = b from ite_eq_right Hif]
    iapply HΦ; itrivial

/-- `r.send(pb.Message{To: to, Type: pb.MsgAppResp, Index: idx, ...})`: `SendOk`'s
`MsgAppResp` clause (d) with no entries. -/
private theorem wp_send_appResp (wp_raft_send : raft.send.spec (GF := GF) (hG := hG))
    (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (dst idx hintterm hint : w64)
    (rej : Bool) (Hdst : dst ≠ id) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhys cfg r id s }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"send"))
        (Val #({ Type' := W32 4, To' := dst, From' := 0, Term' := 0,
                 LogTerm' := hintterm, Index' := idx, Entries' := slice.nil,
                 Commit' := 0, Vote' := 0, Snapshot' := null, Reject' := rej,
                 RejectHint' := hint, Context' := slice.nil, Responses' := slice.nil } :
                raftpb.Message)))
    {{ RET #(); ownRaftPhys cfg r id (sendMsgs s [appResp id s dst rej idx hintterm hint]) }} := by
  iintro %Φ ⟨#Hpkg, Hphys⟩ HΦ
  wp_apply wp_raft_send cfg r id s _ [] [appResp id s dst rej idx hintterm hint] (Or.inl rfl)
      (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, fun h => absurd h Hdst, rfl⟩)))) $$ [$Hphys]
      as Hphys
  · isplitr
    · iapply ownSlice_nil
    · iapply send_no_snap
      exact (by decide : W32 4 ≠ W32 7)
  iapply HΦ
  iexact Hphys

/-- The three exits of `HandleAppResult`, in the body's order.

- `a.prev.index < committed`: `committed` is read twice through the log's struct
  (`ownRaftLog_struct`), once for the test and once for the reply.
- `maybeAppend`: the log is taken out at its state and put back at whatever
  `maybeAppend` leaves (`ownRaftPhys_log_at`); on `ok` that is the new `ls'`, on `!ok`
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
    (wp_raft_send : raft.send.spec (GF := GF) (hG := hG)) :
    raft.handleAppendEntries.spec (GF := GF) (hG := hG) := by
  intro cfg r id s m ents Hwf Hnw Hnorm Hconf Hfid
  wp_start as Hpre
  iNamed Hpre
  wp_auto
  wp_apply wp_logSliceFromMsgApp $$ [$m] as m
  -- the stale test reads `r.raftLog.committed`
  wp_apply raft.wp_load_raftLog $$ Hphys as Hphys
  icases ownRaftPhys_log_same cfg r id s $$ Hphys with ⟨Hlog, Hlogback⟩
  icases ownRaftLog_struct _ _ $$ Hlog with ⟨%lv, Hl, %Hlv, Hlb⟩
  wp_auto
  ihave Hlog := Hlb $$ Hl
  ihave Hphys := Hlogback $$ Hlog
  obtain ⟨Hcm, -⟩ := Hlv
  rw [Hcm]
  wp_if_destruct
  · -- stale: acknowledge `committed`
    wp_apply raft.wp_load_raftLog $$ Hphys as Hphys
    icases ownRaftPhys_log_same cfg r id s $$ Hphys with ⟨Hlog, Hlogback⟩
    icases ownRaftLog_struct _ _ $$ Hlog with ⟨%lv2, Hl, %Hlv2, Hlb⟩
    wp_auto
    ihave Hlog := Hlb $$ Hl
    ihave Hphys := Hlogback $$ Hlog
    obtain ⟨Hcm2, -⟩ := Hlv2
    rw [Hcm2]
    wp_apply wp_send_appResp wp_raft_send (Hdst := Hfid) $$ [$Hphys] as Hphys
    iapply HΦ
    iframe
    ipureintro
    exact .inl ⟨Hif, rfl⟩
  · -- `maybeAppend`
    wp_apply raft.wp_load_raftLog $$ Hphys as Hphys
    icases ownRaftPhys_log_at cfg r id s $$ Hphys with ⟨Hlog, %Hgh0, Hlogback⟩
    wp_apply wp_raftLog_maybeAppend _ s.logst
        (logSlice.mk m.Term' (entryID.mk m.LogTerm' m.Index') m.Entries') ents m.Commit'
        Hwf Hnw Hnorm (fun Hm => Hconf (by omega) Hm) $$ [$Hlog $Hents $Hcap]
      as %lastnewi %ok %ls' ⟨Hlog, %Hma, %Hmagh⟩
    ihave Hphys := Hlogback $$ %ls' Hlog
      %(fun h => (Hgh0 h).elim (fun h1 => .inl (Hmagh.2 h1)) (fun h1 => .inr (Hmagh.1 ▸ h1)))
    cases Hpm : plogMaybeAppend s.logst.prev (s.logst.sents ++ s.logst.uents)
        (entryID.mk m.LogTerm' m.Index') ents with
    | some res =>
      -- accepted
      obtain ⟨lni, es'⟩ := res
      rw [Hpm] at Hma
      obtain ⟨rfl, rfl, Hprev, Hes, Happ, Hcm', Ha', Hsn', Hu', Hst'⟩ := Hma
      wp_auto
      wp_apply wp_send_appResp wp_raft_send (Hdst := Hfid) $$ [$Hphys] as Hphys
      iapply HΦ
      iframe
      ipureintro
      exact .inr (.inl ⟨by omega, _, es', ls', Hpm, Hprev, Hes, Happ, Hcm',
        ⟨Ha', Hsn', Hu', Hprev, Hst'⟩, rfl⟩)
    | none =>
      -- rejected: `a.prev` does not match
      rw [Hpm] at Hma
      obtain ⟨rfl, rfl, rfl⟩ := Hma
      ihave Hphys : ownRaftPhys cfg r id s $$ [Hphys]
      · iapply ownRaftPhys_eq cfg r id _ _ ?_ $$ Hphys
        cases s; rfl
      have Hnm : ¬ PlogMatches s.logst.prev (s.logst.sents ++ s.logst.uents)
          (entryID.mk m.LogTerm' m.Index') := by
        intro Hc
        unfold plogMaybeAppend at Hpm
        rw [ite_eq_left Hc] at Hpm
        cases Hpm
      wp_auto
      wp_apply raft.wp_load_id $$ Hphys as Hphys
      wp_apply raft.wp_load_raftLog $$ Hphys as Hphys
      icases ownRaftPhys_log_same cfg r id s $$ Hphys with ⟨Hlog, Hlogback⟩
      wp_apply wp_raftLog_term $$ [$Hlog] as %t %err ⟨Hlog, -, -, #Herr⟩
      ihave Hphys := Hlogback $$ Hlog
      wp_apply raft.wp_load_raftLog $$ Hphys as Hphys
      wp_apply wp_raftLog_zeroTermOnOutOfBounds $$ [$Herr] as %t' -
      wp_raft_log
      -- `hintIndex := min(m.Index, lastIndex())`
      wp_apply raft.wp_load_raftLog $$ Hphys as Hphys
      icases ownRaftPhys_log_same cfg r id s $$ Hphys with ⟨Hlog, Hlogback⟩
      wp_apply wp_raftLog_lastIndex $$ [$Hlog] as %li ⟨Hlog, -⟩
      ihave Hphys := Hlogback $$ Hlog
      wp_apply wp_min_u64
      wp_apply raft.wp_load_raftLog $$ Hphys as Hphys
      icases ownRaftPhys_log_same cfg r id s $$ Hphys with ⟨Hlog, Hlogback⟩
      wp_apply wp_raftLog_findConflictByTerm $$ [$Hlog] as %hint %hintterm ⟨Hlog, -⟩
      ihave Hphys := Hlogback $$ Hlog
      wp_apply wp_send_appResp wp_raft_send (Hdst := Hfid) $$ [$Hphys] as Hphys
      iapply HΦ
      iframe
      ipureintro
      exact .inr (.inr ⟨by omega, Hnm, hint, hintterm, rfl⟩)

end proof

end EtcdGrove
end Perennial

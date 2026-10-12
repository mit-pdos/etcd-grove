/-
Port of election_proof/proof_raft__appendEntry.v.
-/
module

public import Spec.go_etcd_io.raft.v3.raft__appendEntry
public import Spec.go_etcd_io.raft.v3.raftLog__lastIndex
public import Spec.go_etcd_io.raft.v3.raft__increaseUncommittedSize
public import Spec.go_etcd_io.raft.v3.traceReplicate
public import Spec.go_etcd_io.raft.v3.raftLog__append
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

/-- The two facts about the log that `appendEntry` needs but
`ownRaftLog` only holds inside: the index layout, and the bound that
makes one more entry fit.

The bound is the whole point of `isStorage`'s `Hbounded` clause: the
stable prefix is below `2^61` by that contract, the unstable suffix is a
Go slice and so below `2^63` by `ownSlice_len`, and their sum is what
`lastIndex` returns. -/
private theorem ownRaftLog_facts (l : Loc) (ls : LogState) :
    ⊢ ownRaftLog (GF := GF) l ls -∗
      ⌜LogIndicesOk ls.prev (ls.sents ++ ls.uents) ∧
        uint.Z ls.prev.index' + (ls.sents.length : Int) + (ls.uents.length : Int)
          < 2^61 + 2^63⌝ ∗
      ownRaftLog l ls := by
  iintro H0
  iNamed H0
  ihave #Hsto : isStorage (GF := GF) lv.storage' $$ []
  · iexact HisStorage
  iunfold isStorage at Hsto
  iunfold isStorageWith at Hsto
  icases Hsto with ⟨%isv, #Hs⟩
  iNamed Hs
  icases Hbounded $$ %σ HStorage with ⟨%Hstb, HStorage⟩
  ihave %Hul := ownSlice_len $$ Huents
  -- the stable part: below the storage's bound, or -- with a snapshot
  -- pending -- empty after a snapshot index below `2^61`
  have Hsb : uint.Z ls.prev.index' + (ls.sents.length : Int) < 2^61 := by
    unfold LogStoreOk at Hstore
    split at Hstore
    · obtain ⟨Hsp, Hstored, -⟩ := Hstore
      have := Hstored.length_le
      rw [Hsp] at Hstb
      omega
    · obtain ⟨rfl, Hs0, Hsid⟩ := Hstore
      rw [Hs0, List.length_nil]; omega
  isplitr
  · ipureintro
    refine ⟨Hidx, ?_⟩
    have : (ls.uents.length : Int) < 2^63 := by
      rw [Hul.1]; have := word.signed_range lv.unstable'.entries'.len; word
    omega
  · iapply ownRaftLog_intro l lv lv.storage' σ _ _ ls rfl Hcm Hap Hidx Hnowrap Hstore Hoffset
      HnoConfChange Happlied Hpapplied Hcommitted Hssnap Hapg Hip Hipb Hpersist Happlying
      Hpaused Hasz Hamx Hstor Hpend rfl rfl $$ Hl HisStorage HStorage Husnap Huents Huents_cap Hl_logger
      Hu_logger

/-! The batch, as `appendEntry` rewrites it: `stamp` (`Protocol/Model.lean`). -/

private theorem lookup_take_drop {A : Type _} (l1 l2 : List A) (k : Nat) (hk : k ≤ l1.length) :
    (l1.take k ++ l2.drop k)[k]? = l2[k]? := by
  rw [List.getElem?_append_right (by simp only [List.length_take]; omega)]
  simp only [List.length_take, Nat.min_eq_left hk, Nat.sub_self, List.getElem?_drop, Nat.add_zero]

/-- One iteration of the loop, on the list: the prefix already stamped grows
by one. -/
private theorem stamp_step (tm li : w64) (ents : List raftpb.Entry) (n : Nat) (e : raftpb.Entry)
    (He : ents[n]? = some e) :
    ((ents.mapIdx (stamp tm li)).take n ++ ents.drop n).set n
        { e with Term' := tm, Index' := li + W64 1 + W64 n }
      = (ents.mapIdx (stamp tm li)).take (n+1) ++ ents.drop (n+1) := by
  have Hlt : n < ents.length := by
    rcases (List.getElem?_eq_some_iff.1 He) with ⟨h, _⟩; exact h
  have Hl : ((ents.mapIdx (stamp tm li)).take n).length = n := by
    simp only [List.length_take, List.length_mapIdx]; omega
  rw [List.set_append_right _ _ (by omega), Hl, Nat.sub_self]
  rw [List.take_add_one, List.getElem?_mapIdx, He]
  rw [List.drop_eq_getElem_cons Hlt]
  simp only [Option.map_some, Option.toList_some, List.set_cons_zero, List.append_assoc,
    List.singleton_append]
  rfl

/-- Stamping touches only `Term` and `Index`: a property of the other fields carries
over to the stamped batch (Rocq `stamped_empty`, `stamped_normal`). -/
private theorem stamped_mem (tm li : w64) (ents : List raftpb.Entry) (P : raftpb.Entry → Prop)
    (HP : ∀ e ∈ ents, P e) (Hst : ∀ k e, P e → P (stamp tm li k e)) :
    ∀ e ∈ ents.mapIdx (stamp tm li), P e := by
  intro e He
  obtain ⟨i, hi, rfl⟩ := List.mem_mapIdx.1 He
  exact Hst _ _ (HP _ (List.getElem_mem hi))

/-- The stamped batch continues the log's index sequence. -/
private theorem stamped_indices (tm li : w64) (prev : entryID) (pre ents : List raftpb.Entry)
    (Hpre : LogIndicesOk prev pre)
    (Hli : uint.Z li = uint.Z prev.index' + (pre.length : Int))
    (Hnw : uint.Z li + (ents.length : Int) + 1 < 2^64) :
    LogIndicesOk prev (pre ++ ents.mapIdx (stamp tm li)) := by
  intro k e Hk
  by_cases hk : k < pre.length
  · rw [List.getElem?_append_left hk] at Hk; exact Hpre k e Hk
  · have Hge : pre.length ≤ k := by omega
    rw [List.getElem?_append_right Hge] at Hk
    have Hk2 := Hk
    rw [List.getElem?_mapIdx] at Hk2
    cases He' : ents[k - pre.length]? with
    | none => rw [He'] at Hk2; cases Hk2
    | some e' =>
      rw [He'] at Hk2
      simp only [Option.map_some, Option.some.injEq] at Hk2
      subst Hk2
      have Hlt : k - pre.length < ents.length := by
        rcases (List.getElem?_eq_some_iff.1 He') with ⟨h, _⟩; exact h
      unfold stamp
      simp only
      word

/-- `appendEntry` stamps the batch, charges it, appends it, and tells
itself about it with a self-addressed `MsgAppResp`.

The log's state is in `NState` (`NState.logst`), so the
`lastIndex()` read and the `append` are both stated at `s`'s log
state, and the calls in between (`r.Term` loads,
`increaseUncommittedSize`) leave it alone: nothing is lent. (Until
2026-09-28 the tracker and the log were lent out of `ownRaftPhys`
for that stretch, to keep the log split fixed.) -/
theorem raft.appendEntry.wp_proof
    (wp_raftLog_lastIndex : raftLog.lastIndex.spec (GF := GF) (hG := hG))
    (wp_raft_increaseUncommittedSize : raft.increaseUncommittedSize.spec (GF := GF) (hG := hG))
    (wp_traceReplicate : traceReplicate.spec (GF := GF) (hG := hG))
    (wp_raftLog_append : raftLog.append.spec (GF := GF) (hG := hG))
    (wp_raft_send : raft.send.spec (GF := GF) (hG := hG)) :
    raft.appendEntry.spec (GF := GF) (hG := hG) := by
  intro cfg r id s es ents Hnorm Hsmall Hnz
  wp_start as ⟨Hphys, Hes⟩
  wp_auto
  wp_apply raft.wp_load_raftLog $$ Hphys as Hphys
  ihave %Hlen := ownSlice_len $$ Hes
  -- `li := r.raftLog.lastIndex()`: the log is read at the state `s` records, and put
  -- back unchanged
  icases ownRaftPhys_log_same cfg r id s $$ Hphys with ⟨Hlog, Hlogback⟩
  icases ownRaftLog_facts _ _ $$ Hlog with ⟨%Hfacts, Hlog⟩
  obtain ⟨Hidx, Hbnd⟩ := Hfacts
  wp_apply wp_raftLog_lastIndex _ _ $$ [$Hlog] as %li ⟨Hlog, %Hli⟩
  ihave Hphys := Hlogback $$ Hlog
  -- The stamping loop. `slice.forRange` allocates its **own** counter (`i_ptr`
  -- here), distinct from the Go-level `i` (`iraft`) the body assigns `$key` to,
  -- hence two pointers in the invariant.
  rename_i iraft
  irename : (iraft ↦ zero_val w64 : IProp GF) => Hiraft
  ihave IH : iprop(∃ (n k : w64),
      "Hj" ∷ i_ptr ↦ n ∗
      "Hiraft" ∷ iraft ↦ k ∗
      "Hes" ∷ es ↦* ((ents.mapIdx (stamp s.term li)).take (sint.nat n) ++ ents.drop (sint.nat n)) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (ents.length : Int)⌝) $$ [i Hiraft Hes]
  · iexists W64 0, _
    iframe i Hiraft
    simp only [show sint.nat (W64 0) = 0 by rfl, List.take_zero, List.drop_zero, List.nil_append]
    iframe Hes
    ipureintro; constructor <;> word
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < ents.length := by word
    obtain ⟨e, He⟩ : ∃ e, ents[sint.nat n]? = some e := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hcur : ((ents.mapIdx (stamp s.term li)).take (sint.nat n) ++ ents.drop (sint.nat n))[
        (sint.Z n).toNat]? = some e := by
      show (_ ++ _)[sint.nat n]? = _
      rw [lookup_take_drop _ _ _ (by simp only [List.length_mapIdx]; omega), He]
    have Hbnd' : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z es.len := ⟨Hn.1, Hif⟩
    simp only [Hbnd', and_self]
    wp_apply wp_load_slice_index es (sint.Z n) _ (DFrac.own 1) e Hn.1 $$ [Hes] as Hes
    · iframe; ipureintro; exact Hcur
    wp_apply raft.wp_load_Term $$ Hphys as Hphys
    simp only [Hbnd', and_self]
    icases ownSlice_elem_acc (sint.Z n) e es (DFrac.own 1) _ Hn.1 Hcur $$ Hes with ⟨He1, Hesback⟩
    wp_auto
    -- the `Index` store has its own bounds `decide`
    simp only [Hbnd', and_self]
    wp_auto
    ihave Hes := Hesback $$ %_ He1
    have Hstep : ((ents.mapIdx (stamp s.term li)).take (sint.nat n) ++ ents.drop (sint.nat n)).set
        (sint.Z n).toNat
        { Term' := s.term, Index' := li + W64 1 + n, Type' := e.Type', Data' := e.Data' }
        = (ents.mapIdx (stamp s.term li)).take (sint.nat n + 1) ++ ents.drop (sint.nat n + 1) := by
      have H := stamp_step s.term li ents (sint.nat n) e He
      rw [show (W64 (sint.nat n : Int) : w64) = n by word] at H
      exact H
    dsimp only
    rw [Hstep]
    wp_for_post
    iframe
    iexists n + W64 1, n
    -- the counter moved on by one, so the stamped prefix does too
    rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word]
    iframe
    ipureintro; constructor <;> word
  · -- the loop is done: every entry is stamped
    have Hfull : sint.nat n = ents.length := by word
    rw [Hfull, List.take_of_length_le (by simp only [List.length_mapIdx]; omega),
      List.drop_of_length_le (by omega), List.append_nil]
    -- the budget check, on the *stamped* batch: the loop ran first
    wp_apply wp_raft_increaseUncommittedSize $$ [$Hphys $Hes] as %ok ⟨Hphys, Hes, %Hok⟩
    -- acceptance is pinned only for an all-empty batch; stamping does
    -- not touch `Data`, so the implication transfers to `ents`
    have Hacc : (∀ e ∈ ents, sint.Z e.Data'.len = 0) → ok = true := fun Hz =>
      Hok (stamped_mem _ _ _ _ Hz (fun _ _ h => h))
    -- `li` is `logLast` of the log it was read from: `lastIndex()`
    -- cannot wrap (`Hbnd`)
    have Hlast : logLast s.logst = li := by
      unfold logLast; word
    rw [Hlast]
    cases ok <;> wp_auto
    · -- dropped: `Warningf`, `return false`, the struct untouched
      wp_apply raft.wp_load_id $$ Hphys as Hphys
      wp_raft_log
      iapply HΦ
      simp only [Bool.false_eq_true, ↓reduceIte]
      iframe
      ipureintro; exact fun h => absurd (Hacc h) (by decide)
    wp_apply wp_traceReplicate
    wp_apply raft.wp_load_raftLog $$ Hphys as Hphys
    -- `append`'s premises
    have Hidx2 : LogIndicesOk s.logst.prev
        ((s.logst.sents ++ s.logst.uents) ++ ents.mapIdx (stamp s.term li)) :=
      stamped_indices _ _ _ _ _ Hidx (by rw [List.length_append]; push_cast; omega)
        (by omega)
    have Hnorm2 : ∀ e ∈ ents.mapIdx (stamp s.term li), e.Type' = EntryNormal :=
      stamped_mem _ _ _ _ Hnorm (fun _ _ h => h)
    have Hk2 : ∀ (k2 : Nat) e, (ents.mapIdx (stamp s.term li))[k2]? = some e →
        uint.Z e.Index' = uint.Z s.logst.prev.index' + (s.logst.sents.length : Int)
          + (s.logst.uents.length : Int) + 1 + (k2 : Int) := by
      intro k2 e Hk
      have H := Hidx2 (s.logst.sents.length + s.logst.uents.length + k2) e (by
        rw [List.getElem?_append_right (by simp only [List.length_append]; omega)]
        simp only [List.length_append, Nat.add_sub_cancel_left]; exact Hk)
      rw [H]; push_cast; omega
    icases ownRaftPhys_log_at cfg r id s $$ Hphys with ⟨Hlog, %Hgh0, Hlogback⟩
    -- `append`'s widened spec: the stamped batch continues the log, so
    -- it is a plain `logAppend` and nothing is adopted
    obtain ⟨Htac, Hado⟩ := logTruncateAppend_cont s.logst (ents.mapIdx (stamp s.term li))
      (fun e0 He0 => by have := Hk2 0 e0 He0; push_cast at this; omega)
    icases ownRaftLog_committed _ _ $$ Hlog with ⟨%Hcmb, Hlog⟩
    have Hpre : ∀ e0, (ents.mapIdx (stamp s.term li))[0]? = some e0 →
        (uint.Z s.logst.committed < uint.Z e0.Index' ∧
          uint.Z e0.Index' ≤ uint.Z s.logst.prev.index' + (s.logst.sents.length : Int)
            + (s.logst.uents.length : Int) + 1) ∧
        (∀ (k : Nat) e, (ents.mapIdx (stamp s.term li))[k]? = some e →
          uint.Z e.Index' = uint.Z e0.Index' + (k : Int)) ∧
        uint.Z e0.Index' + ((ents.mapIdx (stamp s.term li)).length : Int) < 2^64 := by
      intro e0 He0
      have H0 := Hk2 0 e0 He0
      push_cast at H0
      refine ⟨⟨by omega, by omega⟩, fun k e Hk => by rw [Hk2 k e Hk, H0]; omega, ?_⟩
      rw [List.length_mapIdx]; omega
    wp_apply wp_raftLog_append _ _ _ _ _ Hpre Hnorm2 $$ [$Hlog $Hes]
      as %li2 ⟨Hlog, Hes, %Hsplit2, %Hli2⟩
    · rw [Hado]; simp only [Bool.false_eq_true, ↓reduceIte, named]; itrivial
    rw [Hado, Htac] at *
    simp only [Bool.false_eq_true, ↓reduceIte]
    ihave Hphys := Hlogback $$ %_ Hlog %(LogGhOk.append _ Hgh0)
    wp_apply raft.wp_load_id $$ Hphys as Hphys
    have Hlast2 : logLast (logAppend s.logst (ents.mapIdx (stamp s.term li))) = li2 := by
      unfold logLast
      unfold logAppend at Hli2 ⊢
      simp only [List.length_append, List.length_mapIdx] at Hli2 ⊢
      push_cast at Hli2 ⊢
      word
    -- the self-acknowledgement: `SendOk`'s `MsgAppResp` clause, with no
    -- entries
    let s' : NState := { s with logst := logAppend s.logst (ents.mapIdx (stamp s.term li)) }
    let m : raftpb.Message :=
      { Type' := W32 4, To' := id, From' := 0, Term' := 0, LogTerm' := 0, Index' := li2,
        Entries' := slice.nil, Commit' := 0, Vote' := 0, Snapshot' := null,
        Reject' := false, RejectHint' := 0, Context' := slice.nil, Responses' := slice.nil }
    wp_apply wp_raft_send cfg r id s' m [] [] [selfAck id s'] ?_ ?_ $$ [$Hphys]
    · exact Or.inl rfl
    · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, fun _ => ⟨rfl, rfl, Hnz, rfl⟩, ?_⟩)))
      unfold selfAck absMsgFrom
      rw [Hlast2]
      rfl
    · isplitr
      · iapply ownSlice_nil
      isplitr
      · iapply ownSlice_nil
      iapply send_no_snap
      show W32 4 ≠ MsgSnap
      decide
    iintro Hphys
    wp_auto
    iapply HΦ
    simp only [↓reduceIte]
    iframe
    ipureintro; exact fun _ => trivial

end proof

end EtcdGrove
end Perennial

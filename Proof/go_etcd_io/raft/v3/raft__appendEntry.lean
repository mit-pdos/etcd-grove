/-
Port of election_proof/proof_raft__appendEntry.v.

raft v3.7 (stage R4): each entry of the batch (`entsPts es dq ents`, read-only elements) is cloned
(`proto.CloneEntry`: an owned copy holding the same record), stamped with fresh `Term`/`Index`
cells (`entOwn_store_Term`/`_Index`, `LemmasSendRB.lean`), frozen (`entOwn_freeze`) and stored
into the fresh slice `cloned`, which then holds the stamped batch read-only (`entsPts cloned 1`);
`increaseUncommittedSize` and `raftLog.append` take that slice. The caller's batch is given back
untouched. The self-acknowledgement is built owned (`msgOwn_lit0`).
-/
module

public import Spec.go_etcd_io.raft.v3.raft__appendEntry
public import Spec.go_etcd_io.raft.v3.raftLog__lastIndex
public import Spec.go_etcd_io.raft.v3.raft__increaseUncommittedSize
public import Spec.go_etcd_io.raft.v3.traceReplicate
public import Spec.go_etcd_io.raft.v3.raftLog__append
public import Spec.go_etcd_io.raft.v3.raft__send
public import Spec.go_etcd_io.raft.v3.raftpb.MessageType__Enum
public import Spec.google_golang_org.protobuf.proto.CloneEntry
public import Proof.go_etcd_io.raft.v3.LemmasSendRB
public import Proof.ReceiptTactics

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
  ihave %Hul := entsPts_len _ _ _ $$ Huents
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
      Happlied Hpapplied Hcommitted Hssnap Hapg Hip Hipb Hpersist Happlying
      Hpaused Hasz Hamx Hstor Hpend Hsksn rfl rfl rfl $$ Hl HisStorage HStorage Husnap Hpksn Huents
      Huents_cap Hl_logger Hu_logger

/-! The batch, as `appendEntry` rewrites it: `stamp` (`Protocol/Model.lean`). -/

private theorem lookup_take_drop {A : Type _} (l1 l2 : List A) (k : Nat) (hk : k ≤ l1.length) :
    (l1.take k ++ l2.drop k)[k]? = l2[k]? := by
  rw [List.getElem?_append_right (by simp only [List.length_take]; omega)]
  simp only [List.length_take, Nat.min_eq_left hk, Nat.sub_self, List.getElem?_drop, Nat.add_zero]

/-- One iteration of the loop, on the list: the prefix already stamped grows
by one. -/
private theorem stamp_step (tm li : w64) (ents : List EntryM) (n : Nat) (e : EntryM)
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
private theorem stamped_mem (tm li : w64) (ents : List EntryM) (P : EntryM → Prop)
    (HP : ∀ e ∈ ents, P e) (Hst : ∀ k e, P e → P (stamp tm li k e)) :
    ∀ e ∈ ents.mapIdx (stamp tm li), P e := by
  intro e He
  obtain ⟨i, hi, rfl⟩ := List.mem_mapIdx.1 He
  exact Hst _ _ (HP _ (List.getElem_mem hi))

/-- The stamped batch continues the log's index sequence. -/
private theorem stamped_indices (tm li : w64) (prev : entryID) (pre ents : List EntryM)
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

/-- `appendEntry` clones and stamps the batch, charges it, appends it, and tells itself about it
with a self-addressed `MsgAppResp`.

The log's state is in `NState` (`NState.logst`), so the `lastIndex()` read and the `append` are
both stated at `s`'s log state, and the calls in between (`r.Term` loads,
`increaseUncommittedSize`) leave it alone. The loop's invariant: the first `n` slots of `cloned`
hold the frozen stamped clones of the first `n` entries, the rest `nil`. -/
theorem raft.appendEntry.wp_proof
    (wp_raftLog_lastIndex : raftLog.lastIndex.spec (GF := GF) (hG := hG))
    (wp_raft_increaseUncommittedSize : raft.increaseUncommittedSize.spec (GF := GF) (hG := hG))
    (wp_traceReplicate : traceReplicate.spec (GF := GF) (hG := hG))
    (wp_raftLog_append : raftLog.append.spec (GF := GF) (hG := hG))
    (wp_raft_send : raft.send.spec (GF := GF) (hG := hG))
    (wp_CloneEntry : proto.CloneEntry.spec (GF := GF) (hG := hG))
    (wp_MessageType_Enum : raftpb.MessageType.Enum.spec (GF := GF) (hG := hG)) :
    raft.appendEntry.spec (GF := GF) (hG := hG) := by
  intro c r id s es ents dq m Hsmall Hnz
  wp_start as ⟨Hphys, Hes, #Hrc⟩
  wp_auto
  wp_apply raft.wp_load_raftLogC $$ Hphys as Hphys
  icases ownRaftPhysC_log_same c r id s $$ Hphys with ⟨Hlog, Hlogback⟩
  icases ownRaftLog_facts _ _ $$ Hlog with ⟨%Hfacts, Hlog⟩
  obtain ⟨Hidx, Hbnd⟩ := Hfacts
  wp_apply wp_raftLog_lastIndex _ _ $$ [$Hlog] as %li ⟨Hlog, %Hli⟩
  ihave Hphys := Hlogback $$ Hlog
  iunfold entsPts at Hes
  icases Hes with ⟨%lsE, Hes, #Hents⟩
  ihave %Hlen := ownSlice_len $$ Hes
  ihave %Hlen2 := BigSepL2.bigSepL2_length $$ Hents
  try wp_auto
  wp_apply wp_slice_make2 (V := Loc) es.len as %cl ⟨Hcl, Hcl_cap⟩
  · ipureintro; omega
  try wp_auto
  rename_i iraft
  irename : (iraft ↦ zero_val w64 : IProp GF) => Hiraft
  have HlenE : ents.length = sint.nat es.len := by omega
  ihave IH : iprop(∃ (n k : w64) (lc : List Loc),
      "Hj" ∷ i_ptr ↦ n ∗
      "Hiraft" ∷ iraft ↦ k ∗
      "Hcl" ∷ cl ↦* (lc ++ List.replicate (ents.length - sint.nat n) (zero_val Loc)) ∗
      "#Hcls" ∷ ([∗list] l;e ∈ lc;(ents.mapIdx (stamp s.term li)).take (sint.nat n), entRO l e) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (ents.length : Int) ∧ lc.length = sint.nat n⌝ ∗
      -- (2026-10-18, D19b stage 5) one receipt raised per entry cloned
      "#Hrc" ∷ ⧖ (m + sint.nat n))
    $$ [i Hiraft Hcl]
  · iexists W64 0, _, []
    iframe i Hiraft
    simp only [show sint.nat (W64 0) = 0 by rfl, List.take_zero, List.nil_append, Nat.sub_zero,
      HlenE]
    iframe Hcl
    isplitr
    · iapply BigSepL2.bigSepL2_nil.2; itrivial
    isplitr
    · ipureintro; refine ⟨by word, by word, rfl⟩
    iexact Hrc
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < ents.length := by word
    obtain ⟨e, He⟩ : ∃ e, ents[sint.nat n]? = some e := ⟨_, List.getElem?_eq_getElem Hlt⟩
    icases entsBig_lookup _ _ _ _ He $$ Hents with ⟨%le, %Hle, #Hle⟩
    have Hbnd' : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z es.len := ⟨Hn.1, Hif⟩
    ihave %Hcll := ownSlice_len $$ Hcl
    have Hnn : (sint.nat n : Int) = sint.Z n := Int.toNat_of_nonneg Hn.1
    have Hesn : (sint.nat es.len : Int) = sint.Z es.len := Int.toNat_of_nonneg Hlen.2
    have Hcln : (sint.nat cl.len : Int) = sint.Z cl.len := Int.toNat_of_nonneg Hcll.2
    have Hlc := Hn.2.2
    simp only [List.length_append, List.length_replicate] at Hcll
    have Hbndc : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z cl.len := ⟨Hn.1, by
      have h1 := Hcll.1; omega⟩
    try wp_auto
    simp only [Hbnd', _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index es (sint.Z n) _ dq le Hn.1 $$ [Hes] as Hes
    · iframe; ipureintro; exact Hle
    try wp_auto
    simp only [Hbnd', _root_.and_self, ↓reduceIte]
    wp_apply +noauto wp_load_slice_index es (sint.Z n) _ dq le Hn.1 $$ [Hes] as Hes
    · iframe; ipureintro; exact Hle
    -- (2026-10-18, D19b stage 5) the receipt of this entry: `proto.Clone`'s resolution
    wp_raise_receipt Hrc
    try wp_auto
    wp_apply wp_CloneEntry le DFrac.discard e $$ [$Hle] as %l' ⟨-, Hl'⟩
    try wp_auto
    simp only [Hbndc, _root_.and_self, ↓reduceIte]
    wp_apply wp_store_slice_index cl (sint.Z n) _ l' $$ [Hcl] as Hcl
    · iframe; ipureintro
      simp only [List.length_append, List.length_replicate]; omega
    have Hset : (lc ++ List.replicate (ents.length - sint.nat n) (zero_val Loc)).set (sint.Z n).toNat l'
        = (lc ++ [l']) ++ List.replicate (ents.length - (sint.nat n + 1)) (zero_val Loc) := by
      rw [show (sint.Z n).toNat = lc.length by omega]
      rw [List.set_append_right _ _ (by omega), Nat.sub_self]
      obtain ⟨k, hk⟩ : ∃ k, ents.length - sint.nat n = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos (by omega)).symm⟩
      rw [hk, List.replicate_succ, List.set_cons_zero, List.append_assoc, List.singleton_append]
      rw [show ents.length - (sint.nat n + 1) = k by omega]
    rw [Hset]
    wp_apply raft.wp_load_TermC $$ Hphys as Hphys
    imod cellRO_alloc $$ «$r0» with #cT
    try wp_auto
    simp only [Hbndc, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index cl (sint.Z n) _ _ l' Hn.1 $$ [Hcl] as Hcl
    · iframe; ipureintro
      rw [show (sint.Z n).toNat = lc.length by omega, List.append_assoc]
      simp
    icases entOwn_store_Term _ _ $$ Hl' with ⟨%pT, HT, HTback⟩
    try wp_auto
    ihave Hl' := HTback $$ %_ %s.term HT cT
    try wp_auto
    imod cellRO_alloc $$ «$r0» with #cI
    simp only [Hbndc, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index cl (sint.Z n) _ _ l' Hn.1 $$ [Hcl] as Hcl
    · iframe; ipureintro
      rw [show (sint.Z n).toNat = lc.length by omega, List.append_assoc]
      simp
    icases entOwn_store_Index _ _ $$ Hl' with ⟨%pI, HI, HIback⟩
    wp_pures
    wp_store
    ihave Hl' := HIback $$ %_ %_ HI cI
    imod entOwn_freeze $$ Hl' with #Hl'
    wp_auto
    wp_for_post
    iframe
    iexists n + W64 1, n, lc ++ [l']
    have Hn1 : sint.nat (n + W64 1) = sint.nat n + 1 := by word
    rw [Hn1]
    simp only [named]
    iframe
    have Htk : (ents.mapIdx (stamp s.term li)).take (sint.nat n + 1)
        = (ents.mapIdx (stamp s.term li)).take (sint.nat n) ++
          [{ Term' := s.term, Index' := li + W64 1 + n, Type' := e.Type', Data' := e.Data' }] := by
      rw [List.take_add_one, List.getElem?_mapIdx, He]
      simp only [Option.map_some, Option.toList_some, stamp]
      rw [show (W64 (sint.nat n : Int) : w64) = n by word]
    rw [Htk]
    isplitr
    · iapply BigSepL2.bigSepL2_snoc.2
      iframe Hcls Hl'
    isplitr
    · ipureintro
      refine ⟨by word, by word, by simp only [List.length_append, List.length_singleton]; omega⟩
    iexact Hrc
  · -- the loop is done: every entry is cloned and stamped
    have Hnn : (sint.nat n : Int) = sint.Z n := Int.toNat_of_nonneg Hn.1
    have Hesn : (sint.nat es.len : Int) = sint.Z es.len := Int.toNat_of_nonneg Hlen.2
    have Hfull : sint.nat n = ents.length := by omega
    rw [Hfull, Nat.sub_self, List.replicate_zero, List.append_nil,
      List.take_of_length_le (by simp only [List.length_mapIdx]; omega)] at *
    ihave Hcl : entsPts cl (DFrac.own 1) (ents.mapIdx (stamp s.term li)) $$ [Hcl]
    · iunfold entsPts; iexists lc; iframe Hcl Hcls
    ihave Hes : entsPts es dq ents $$ [Hes]
    · iunfold entsPts; iexists lsE; iframe Hes Hents
    -- the budget check, on the *stamped* batch: the loop ran first
    wp_apply wp_raft_increaseUncommittedSize $$ [$Hphys $Hcl] as %ok ⟨Hphys, Hcl, %Hok⟩
    -- acceptance is pinned only for an all-empty batch; stamping does
    -- not touch `Data`, so the implication transfers to `ents`
    have Hacc : (∀ e ∈ ents, e.Data' = []) → ok = true := fun Hz =>
      Hok (stamped_mem _ _ _ _ Hz (fun _ _ h => h))
    -- `li` is `logLast` of the log it was read from: `lastIndex()`
    -- cannot wrap (`Hbnd`)
    have Hlast : logLast s.logst = li := by
      unfold logLast; word
    rw [Hlast]
    cases ok <;> wp_auto
    · -- dropped: `Warningf`, `return false`, the struct untouched
      wp_apply raft.wp_load_idC $$ Hphys as Hphys
      wp_raft_logC
      iapply HΦ
      simp only [Bool.false_eq_true, ↓reduceIte]
      iframe
      isplitr
      · iexact Hrc
      ipureintro; exact fun h => absurd (Hacc h) (by decide)
    wp_apply wp_traceReplicate
    wp_apply raft.wp_load_raftLogC $$ Hphys as Hphys
    -- `append`'s premises
    have Hidx2 : LogIndicesOk s.logst.prev
        ((s.logst.sents ++ s.logst.uents) ++ ents.mapIdx (stamp s.term li)) :=
      stamped_indices _ _ _ _ _ Hidx (by rw [List.length_append]; push_cast; omega)
        (by omega)
    have Hk2 : ∀ (k2 : Nat) e, (ents.mapIdx (stamp s.term li))[k2]? = some e →
        uint.Z e.Index' = uint.Z s.logst.prev.index' + (s.logst.sents.length : Int)
          + (s.logst.uents.length : Int) + 1 + (k2 : Int) := by
      intro k2 e Hk
      have H := Hidx2 (s.logst.sents.length + s.logst.uents.length + k2) e (by
        rw [List.getElem?_append_right (by simp only [List.length_append]; omega)]
        simp only [List.length_append, Nat.add_sub_cancel_left]; exact Hk)
      rw [H]; push_cast; omega
    icases ownRaftPhysC_log_at c r id s $$ Hphys with ⟨Hlog, %Hgh0, Hlogback⟩
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
    wp_apply wp_raftLog_append _ _ _ _ _ Hpre $$ [$Hlog $Hcl]
      as %li2 ⟨Hlog, Hcl, %Hsplit2, %Hli2⟩
    · rw [Hado]; simp only [Bool.false_eq_true, ↓reduceIte, named]; itrivial
    rw [Hado, Htac] at *
    simp only [Bool.false_eq_true, ↓reduceIte]
    have Hlast2 : logLast (logAppend s.logst (ents.mapIdx (stamp s.term li))) = li2 := by
      unfold logLast
      unfold logAppend at Hli2 ⊢
      simp only [List.length_append, List.length_mapIdx] at Hli2 ⊢
      push_cast at Hli2 ⊢
      word
    -- (stage R8a) a leader's log only grows: the last index is not lower
    have Hle2 : s.role = .leader → uint.Z (logLast s.logst) ≤
        uint.Z (logLast (logAppend s.logst (ents.mapIdx (stamp s.term li)))) := by
      intro _
      rw [Hlast2, Hlast]
      unfold logAppend at Hli2
      simp only [List.length_append, List.length_mapIdx] at Hli2
      push_cast at Hli2
      word
    ihave Hphys := Hlogback $$ %_ Hlog %(LogGhOk.append _ Hgh0) %Hle2
    -- the self-acknowledgement: `SendOk`'s `MsgAppResp` clause, with no entries
    try wp_auto
    wp_apply raft.wp_load_idC $$ Hphys as Hphys
    imod cellRO_alloc $$ «$v0» with #cTo
    try wp_auto
    rw [show raftpb.MsgAppResp = #((W32 4 : raftpb.MessageType)) from rfl]
    haveI : go.NotInterface go.int32 := ⟨by unfold go.int32; trivial⟩
    wp_apply wp_MessageType_Enum (W32 4)
    iintro %pty Hpty
    imod cellRO_alloc $$ Hpty with #cTy
    try wp_auto
    imod cellRO_alloc $$ «$v2» with #cIx
    try wp_auto
    imod msgOwn_lit0 «$a0_ptr» _ ⟨W32 4, id, 0, 0, 0, li2, 0, 0, false, 0⟩ ⊤ $$ [«$a0»] with Hr
    · iframe «$a0» cTy cTo cIx
      isplitr
      · ipureintro; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
      msg_nulls
    let s' : NState := { s with logst := logAppend s.logst (ents.mapIdx (stamp s.term li)) }
    wp_apply wp_raft_send c r id s' «$a0_ptr» _ [] none [] [] [selfAck id s'] (Or.inl rfl) ?_
      (fun h => absurd h (by simp [MsgSnap])) $$ [$Hphys $Hr] as Hphys
    · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, fun _ => ⟨rfl, rfl, Hnz, rfl⟩, ?_⟩)))
      unfold selfAck absMsgFrom
      rw [Hlast2]
      rfl
    try wp_auto
    iapply HΦ
    simp only [↓reduceIte]
    iframe
    isplitr
    · iexact Hrc
    ipureintro; exact fun _ => trivial

end proof

end EtcdGrove
end Perennial

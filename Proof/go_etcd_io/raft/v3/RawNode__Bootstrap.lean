/- Lean-first (no Rocq counterpart). See `Spec/go_etcd_io/raft/v3/RawNode__Bootstrap.lean`. -/
module

public import Spec.go_etcd_io.raft.v3.RawNode__Bootstrap
public import Spec.go_etcd_io.raft.v3.raft__becomeFollower
public import Spec.go_etcd_io.raft.v3.raftpb.ConfChangeType__Enum
public import Spec.go_etcd_io.raft.v3.raftpb.EntryType__Enum
public import Spec.go_etcd_io.raft.v3.raftLog__append
public import Spec.go_etcd_io.raft.v3.raftpb.ConfChange__AsV2
public import Spec.go_etcd_io.raft.v3.raft__applyConfChange
public import Proof.go_etcd_io.raft.v3.LemmasMiscR

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3
open RawNodeOwnAccess

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

set_option maxHeartbeats 800000 in
theorem RawNode.Bootstrap.wp_proof
    (wp_raft_becomeFollower : raft.becomeFollower.spec (GF := GF) (hG := hG))
    (wp_ConfChangeType_Enum : raftpb.ConfChangeType.Enum.spec (GF := GF) (hG := hG))
    (wp_EntryType_Enum : raftpb.EntryType.Enum.spec (GF := GF) (hG := hG))
    (wp_raftLog_append : raftLog.append.spec (GF := GF) (hG := hG))
    (wp_ConfChange_AsV2 : raftpb.ConfChange.AsV2.spec (GF := GF) (hG := hG))
    (wp_raft_applyConfChange : raft.applyConfChange.spec (GF := GF) (hG := hG)) :
    RawNode.Bootstrap.spec (GF := GF) (hG := hG) := by
  intro γ rn id si sdr s peers dq pv ps ctxs bootLog R1 R2 R3 R4 R5 R6 R7 R8 R9
  wp_start as ⟨Hfresh, Hpeers, #Hctx, #Hmarshal, Hghost, #Hcommitted⟩
  iunfold rawNodeFresh at Hfresh
  icases Hfresh with ⟨%rnv, %sv, %hprev, Hfresh⟩
  iNamed Hfresh
  obtain ⟨Hp, Hse, Hue, Hsd, Hcm0, Hap0, Hapg0, Hun, Hsn, Hsg⟩ := Hlog
  obtain ⟨Ht0, Hv0, Hr, Ho, Hrst, Hrpd⟩ := Hterm0
  ihave %Hplen := ownSlice_len $$ Hpeers
  have Hpslen : ps.length = pv.length := by rw [R1, List.length_map]
  obtain ⟨HbLen, HbBnd, HbEnt⟩ := R9
  have Hpv62 : (pv.length : Int) ≤ 2 ^ 62 := by rw [← Hpslen]; exact R5
  wp_auto
  -- `len(peers) == 0`: dead
  wp_if_destruct
  · exfalso
    apply R2
    rw [R1]
    apply List.map_eq_nil_iff.2
    apply List.eq_nil_of_length_eq_zero
    have := Hplen.1; rw [this]; word
  -- `rn.raft.raftLog.storage.LastIndex()`: the storage is empty, so `0`
  wp_apply raft.wp_load_raftLog $$ Hphys as Hphys
  icases ownRaftPhys_log_same _ _ _ s $$ Hphys with ⟨Hlog, Hlogback⟩
  iNamed Hlog
  wp_auto
  ihave #Hsto : isStorageWith (ownStorage lv.storage') (appendTok lv.storage')
      (appendedTok lv.storage') lv.storage' $$ [HisStorage]
  · unfold isStorage; iexact HisStorage
  unfold isStorageWith
  icases Hsto with ⟨%isv, #Hsto⟩
  iNamed Hsto
  rw [Hstok]
  wp_auto
  have Hpnil : σ.pend = [] := by rw [Hpend.1]; exact Hun
  wp_apply HLastIndex $$ [$HStorage] as %li ⟨%Hli, HStorage⟩
  · ipureintro; exact Hpnil
  rw [← Hstok]
  try wp_auto
  ihave Hlog : ownRaftLog s.log s.logst $$ [Hl HStorage Huents Huents_cap]
  · reseal_raftLog
  ihave Hphys := Hlogback $$ Hlog
  have Hli0 : li = W64 0 := by
    obtain ⟨Hsp, -, Hsents⟩ : LogStoreOk none σ s.logst.prev s.logst.sents s.logst.uents :=
      Hsn ▸ Hstore
    have Hse' := Hsents Hue
    rw [Hsp, Hp, ← Hse', Hse] at Hli
    simp at Hli
    word
  subst Hli0
  wp_auto
  -- `rn.prevHardSt = emptyState`
  ihave Hinit := isInitialized_access $$ Hpkg
  ihave ⟨%es, #Hg, #Hes⟩ := emptyState_hsRO $$ Hinit
  wp_auto
  -- `rn.raft.becomeFollower(1, None)`
  wp_apply (raft.becomeFollower.spec_simple wp_raft_becomeFollower) ∅ rnv.raft' id s (W64 1)
    (W64 0) (by rw [Ht0]; word) $$ [$Hphys] as %pvs1 Hphys
  -- the state after `becomeFollower(1, None)`, as a variable (`s1`): term `1`, no vote, no leader
  generalize Hs1 : ({ becomeFollower s (W64 1) (W64 0) with prvals := pvs1 } : NState) = s1
  have Hs1f : s1.term = W64 1 ∧ s1.vote = W64 0 ∧ s1.lead = W64 0 ∧ s1.role = .follower ∧
      s1.votes = ∅ ∧ s1.outbox = s.outbox ∧ s1.logst = s.logst ∧ s1.log = s.log ∧ s1.gh = s.gh ∧
      s1.prevote = s.prevote ∧ s1.sdr = s.sdr ∧ s1.rd.states = s.rd.states ∧
      s1.rd.pend = s.rd.pend ∧ s1.stepfn = stepFuncOf .follower ∧ s1.ticking = true := by
    rw [← Hs1]
    refine ⟨rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    show (if W64 1 = s.term then s.vote else W64 0) = W64 0
    rw [Ht0]; exact ite_eq_right (by decide)
  obtain ⟨Hs1t, Hs1v, Hs1l, Hs1r, Hs1vs, Hs1o, Hs1ls, Hs1lg, Hs1gh, Hs1pv, Hs1sdr, Hs1rs, Hs1rp,
    Hs1sf, Hs1tk⟩ := Hs1f
  -- `ents := make([]*pb.Entry, len(peers))`
  wp_apply wp_slice_make2 (V := Loc) peers.len as %ents ⟨Hents, Hents_cap⟩
  · ipureintro; exact Hplen.2
  try wp_auto
  rename_i igo
  irename : (igo ↦ zero_val w64 : IProp GF) => Hi
  -- the first loop: entry `k` built from peer `k` (`ConfChange` marshalled, `Entry` at term `1`,
  -- index `k + 1`), stored at `ents[k]`; after `n` iterations the first `n` boot entries
  iunfold peersCtx at Hctx
  ihave %Hctxlen := BigSepL2.bigSepL2_length $$ Hctx
  ihave IH : iprop(∃ (n : w64) (lc : List Loc) (x : w64) (pr : Peer),
      "i" ∷ i_ptr ↦ n ∗
      "Hi" ∷ igo ↦ x ∗
      "peer" ∷ peer_ptr ↦ pr ∗
      "Hents" ∷ ents ↦* (lc ++ List.replicate (pv.length - sint.nat n) (zero_val Loc)) ∗
      "#Hlc" ∷ ([∗list] l;e ∈ lc;bootLog.take (sint.nat n), entRO l e) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (pv.length : Int) ∧ lc.length = sint.nat n⌝)
    $$ [i Hi peer Hents]
  · iexists W64 0, [], _, _
    simp only [named]
    iframe i Hi peer
    simp only [show sint.nat (W64 0) = 0 by rfl, List.take_zero, List.nil_append, Nat.sub_zero,
      Hplen.1]
    iframe Hents
    isplitr
    · iapply BigSepL2.bigSepL2_nil.2; itrivial
    ipureintro; refine ⟨by word, by word, rfl⟩
  wp_for IH
  wp_if_destruct
  · -- iteration `n`: `peer := peers[n]`
    have Hlt : sint.nat n < pv.length := by word
    obtain ⟨p, Hpn⟩ : ∃ p, pv[sint.nat n]? = some p := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hbnd' : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z peers.len := ⟨Hn.1, Hif⟩
    simp only [Hbnd', _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index peers (sint.Z n) _ dq p Hn.1 $$ [Hpeers] as Hpeers
    · iframe; ipureintro; exact Hpn
    try wp_auto
    -- the peer's conf change: `&pb.ConfChange{Type: AddNode.Enum(), NodeId: new(peer.ID),
    -- Context: peer.Context}`, owned (`ownCCV1`)
    obtain ⟨ctx, Hcn⟩ : ∃ ctx, ctxs[sint.nat n]? = some ctx :=
      ⟨_, List.getElem?_eq_getElem (by rw [← Hctxlen]; exact Hlt)⟩
    ihave #Hpctx := BigSepL2.bigSepL2_lookup (Φ := fun _ (p : Peer) ctx => (p.Context' ↦*□ ctx : IProp GF))
      Hpn Hcn $$ Hctx
    rw [show raftpb.ConfChangeAddNode = #((W32 0 : raftpb.ConfChangeType)) from rfl]
    haveI : go.NotInterface go.int32 := ⟨by unfold go.int32; trivial⟩
    wp_apply wp_ConfChangeType_Enum (W32 0) as %pty Hpty
    imod cellRO_alloc $$ Hpty with #cTy
    imod cellRO_alloc $$ «$v1» with #cN
    imod ownCCV1_of_struct «$r0_ptr» (⟨zero_val _, pty, «$v1_ptr», p.Context', null, slice.nil, 0⟩ : raftpb.ConfChange)
        ⟨W32 0, p.ID', ctx, W64 0⟩ ⊤ rfl $$ [«$r0»] with Hcc
    · iframe «$r0» cTy cN Hpctx
      iunfold cellRO; ileft; ipureintro; exact ⟨rfl, rfl⟩
    -- `proto.Marshal(cc)`: the boot entry's bytes (`bootMarshal`)
    obtain ⟨e, Hen⟩ : ∃ e, bootLog[sint.nat n]? = some e :=
      ⟨_, List.getElem?_eq_getElem (by rw [HbLen, Hpslen]; exact Hlt)⟩
    have Hpsn : ps[sint.nat n]? = some p.ID' := by
      rw [R1, List.getElem?_map, Hpn]; rfl
    obtain ⟨HeT, HeI, HeY, -, -⟩ := HbEnt _ _ Hen
    have Hpure : ps[sint.nat n]? = some (⟨W32 0, p.ID', ctx, W64 0⟩ : CCV1M).nodeId ∧
        ctxs[sint.nat n]? = some (⟨W32 0, p.ID', ctx, W64 0⟩ : CCV1M).context ∧
        bootLog[sint.nat n]? = some e ∧ (⟨W32 0, p.ID', ctx, W64 0⟩ : CCV1M).type = W32 0 ∧
        (⟨W32 0, p.ID', ctx, W64 0⟩ : CCV1M).id = W64 0 := ⟨Hpsn, Hcn, Hen, rfl, rfl⟩
    iunfold bootMarshal at Hmarshal
    ihave #Hmk := Hmarshal $$ %(sint.nat n) %«$r0_ptr» %(DFrac.own 1) %(⟨W32 0, p.ID', ctx, W64 0⟩ : CCV1M)
      %e %Hpure
    wp_apply Hmk $$ [$Hcc] as %d Hcc Hd
    try wp_auto
    -- the boot entry: `&pb.Entry{Type: EntryConfChange.Enum(), Term: new(1), Index: new(i + 1),
    -- Data: data}`, read-only (`entRO`)
    rw [show raftpb.EntryConfChange = #((W32 1 : raftpb.EntryType)) from rfl]
    wp_apply wp_EntryType_Enum (W32 1) as %pety Hpety
    imod cellRO_alloc $$ Hpety with #cY
    imod cellRO_alloc $$ «$v1» with #cT
    imod cellRO_alloc $$ «$v2» with #cI
    imod ownSlice_persist $$ Hd with #Hd
    imod entOwn_of_struct «$r0_ptr» (⟨zero_val _, «$v1_ptr», «$v2_ptr», pety, d, slice.nil, 0⟩ : raftpb.Entry)
        e ⊤ rfl $$ [«$r0»] with He
    · have HeI' : e.Index' = n + W64 1 := by word
      iframe «$r0» Hd
      rw [HeT, HeY, HeI']
      iframe cT cY cI
    imod entOwn_freeze $$ He with #He
    -- `ents[i] = &pb.Entry{...}`
    ihave %Hentsl := ownSlice_len $$ Hents
    simp only [List.length_append, List.length_replicate] at Hentsl
    have Hnn : (sint.nat n : Int) = sint.Z n := Int.toNat_of_nonneg Hn.1
    have Hesn : (sint.nat ents.len : Int) = sint.Z ents.len := Int.toNat_of_nonneg Hentsl.2
    have Hlc := Hn.2.2
    have Hbndc : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z ents.len := ⟨Hn.1, by
      have h1 := Hentsl.1; omega⟩
    try wp_auto
    simp only [Hbndc, _root_.and_self, ↓reduceIte]
    wp_apply wp_store_slice_index ents (sint.Z n) _ «$r0_ptr» $$ [Hents] as Hents
    · iframe; ipureintro
      simp only [List.length_append, List.length_replicate]; omega
    have Hset : (lc ++ List.replicate (pv.length - sint.nat n) (zero_val Loc)).set (sint.Z n).toNat «$r0_ptr»
        = (lc ++ [«$r0_ptr»]) ++ List.replicate (pv.length - (sint.nat n + 1)) (zero_val Loc) := by
      rw [show (sint.Z n).toNat = lc.length by omega]
      rw [List.set_append_right _ _ (by omega), Nat.sub_self]
      obtain ⟨k, hk⟩ : ∃ k, pv.length - sint.nat n = k + 1 :=
        ⟨_, (Nat.succ_pred_eq_of_pos (by omega)).symm⟩
      rw [hk, List.replicate_succ, List.set_cons_zero, List.append_assoc, List.singleton_append]
      rw [show pv.length - (sint.nat n + 1) = k by omega]
    rw [Hset]
    wp_for_post
    iframe
    iexists n + W64 1, lc ++ [«$r0_ptr»], _, _
    simp only [named]
    rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word]
    iframe i Hi peer Hents
    isplitr
    · rw [List.take_succ, Hen, show (some e).toList = [e] from rfl]
      iapply entsBig_app lc [«$r0_ptr»] (List.take (sint.nat n) bootLog) [e] $$ [$Hlc]
      iapply BigSepL2.bigSepL2_singleton.2
      iexact He
    ipureintro
    refine ⟨by word, by word, ?_⟩
    rw [List.length_append, List.length_singleton, Hn.2.2]
  -- the loop's exit: `ents` holds the boot entries
  have Hnlen : sint.nat n = pv.length := by word
  have Hrep : lc ++ List.replicate (pv.length - sint.nat n) (zero_val Loc) = lc := by
    rw [Hnlen, Nat.sub_self, List.replicate_zero, List.append_nil]
  have Htake : List.take (sint.nat n) bootLog = bootLog := by
    rw [Hnlen, ← Hpslen, ← HbLen]; exact List.take_length
  ihave Hes : entsPts ents (DFrac.own 1) bootLog $$ [Hents]
  · iunfold entsPts
    iexists lc
    isplitl [Hents]
    · iExactEq Hents; rw [Hrep]
    · iExactEq Hlc; rw [Htake]
  -- `rn.raft.raftLog.append(rn.raft.Term, ents...)`: the boot entries join the (empty) log,
  -- unstable, at the leader term `1` (raft#139)
  wp_apply raft.wp_load_Term $$ Hphys as Hphys
  wp_apply raft.wp_load_raftLog $$ Hphys as Hphys
  icases ownRaftPhys_log_at ∅ _ id _ $$ Hphys with ⟨Hlog, %Hgh0, Hlogback⟩
  have Hidx1 : ∀ e0, bootLog[0]? = some e0 →
      (uint.Z s.logst.committed < uint.Z e0.Index' ∧
        uint.Z e0.Index' ≤ uint.Z s.logst.prev.index' + (s.logst.sents.length : Int)
          + (s.logst.uents.length : Int) + 1) ∧
      (∀ (k : Nat) e, bootLog[k]? = some e → uint.Z e.Index' = uint.Z e0.Index' + (k : Int)) ∧
      uint.Z e0.Index' + (bootLog.length : Int) < 2 ^ 64 := by
    intro e0 He0
    obtain ⟨-, HI0, -, -, -⟩ := HbEnt _ _ He0
    rw [Hcm0, Hp, Hse, Hue]
    refine ⟨⟨by word, by word⟩, ?_, by word⟩
    intro k e He
    obtain ⟨-, HIk, -, -, -⟩ := HbEnt _ _ He
    omega
  have Hfirst : ∀ e0, bootLog[0]? = some e0 →
      uint.Z e0.Index' = uint.Z s.logst.prev.index' + (s.logst.sents.length : Int)
        + (s.logst.uents.length : Int) + 1 := by
    intro e0 He0
    obtain ⟨h1, h2⟩ := (Hidx1 e0 He0).1
    clear Hidx1
    have z0 : uint.Z (W64 0) = 0 := by first | rfl | decide | simp
    rw [Hcm0, z0] at h1
    rw [Hp, Hse, Hue] at h2
    rw [Hp, Hse, Hue]
    dsimp only at h2 ⊢
    rw [z0] at h2 ⊢
    simp only [List.length_nil] at h2 ⊢
    omega
  have Hcont := logTruncateAppend_cont s.logst bootLog Hfirst
  have Hlt0 : uint.Z s.logst.leaderTerm ≤ uint.Z s1.term := by
    have h := Hrel.2.2.2.1
    rw [Ht0] at h; rw [Hs1t]
    have h0 : uint.Z (W64 0) = 0 := rfl
    have h1 : uint.Z (W64 1) = 1 := rfl
    omega
  have Hlastt : ∀ e, bootLog.getLast? = some e → uint.Z s1.logst.leaderTerm ≤ uint.Z s1.term →
      uint.Z e.Term' ≤ uint.Z s1.term := by
    intro e He _
    obtain ⟨HeT, -⟩ := HbEnt _ _ (getLast?_some_getElem? _ _ He)
    rw [HeT, Hs1t]; exact Int.le_refl _
  wp_apply wp_raftLog_append s1.log s1.logst s1.term bootLog ents (DFrac.own 1)
      (by rw [Hs1ls]; exact Hidx1) Hlastt
    $$ [$Hlog $Hes] as %li ⟨Hlog, Hes, %Hpost⟩
  · rw [Hs1ls, Hcont.2]; simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
  ihave Hes : entsPts ents (DFrac.own 1) bootLog $$ [Hes]
  · iExactEq Hes; rw [Hs1ls, Hcont.2]; simp only [Bool.false_eq_true, ↓reduceIte]
  ihave Hlog : ownRaftLog s1.log (logAppendLT s.logst s1.term bootLog) $$ [Hlog]
  · iExactEq Hlog; rw [Hs1ls, logAppendAt_cont _ _ _ Hlt0 Hcont.1]
  ihave Hphys := Hlogback $$ %(logAppendLT s.logst s1.term bootLog) Hlog
    %(by intro h; rw [Hs1gh, Hgh] at h; cases h)
    %(by intro h; rw [Hs1r] at h; cases h)
  generalize Hs2 : ({ s1 with logst := logAppendLT s.logst s1.term bootLog } : NState) = s2
  have Hs2ls : s2.logst = logAppendLT s.logst s1.term bootLog := by rw [← Hs2]
  have Hs2lg : s2.log = s1.log := by rw [← Hs2]
  -- `rn.raft.raftLog.committed = uint64(len(ents))`: the raw store (D12), the entries committed
  -- although unstable
  wp_apply raft.wp_load_raftLog $$ Hphys as Hphys
  icases ownRaftPhys_log_at ∅ _ id _ $$ Hphys with ⟨Hlog, %Hgh1, Hlogback⟩
  ihave %Hesl := entsPts_len $$ Hes
  have Hlen' : uint.Z ents.len = (bootLog.length : Int) := by word
  have Hlenw : ents.len = W64 bootLog.length := by word
  wp_apply (ownRaftLog_setCommitted s2.log s2.logst ents.len
      (by rw [Hs2ls]; simp only [logAppendLT_prev, Hp]; word)
      (by rw [Hs2ls]; simp only [logAppendLT_prev, logAppendLT_sents, logAppendLT_uents, Hp, Hse,
            Hue, List.nil_append]; word)
      (by rw [Hs2ls]; simp only [logAppendLT_applying, Hapg0]; word)
      (by rw [Hs2ls]; simp only [logAppendLT_committed, Hcm0]; word))
    $$ [$Hlog] as Hlog
  ihave Hphys := Hlogback $$ %_ Hlog
    %(LogGhOk.of_fields Hgh1 rfl rfl rfl rfl rfl)
    %(by intro h; rw [← Hs2] at h; exact absurd h (by rw [Hs1r]; decide))
  generalize Hs3 : ({ s2 with logst := { s2.logst with committed := ents.len } } : NState) = s3
  have Hs3pr : s3.progress = s.progress := by rw [← Hs3, ← Hs2, ← Hs1]; rfl
  have Hs3r : s3.role = .follower := by rw [← Hs3, ← Hs2]; exact Hs1r
  try wp_auto
  -- the second loop: `applyConfChange(AddNode peer)` per peer, at a follower: the voters so far
  -- (`CfgM.simple (listToSet (ps.take k)) ∅`), the state but for the progress map, the `Progress`
  -- values and `isLearner` unchanged
  have Hd3 : domSet s3.progress \ (∅ : GSet w64) = ∅ := by
    rw [Hs3pr, Hdom]
    apply GMap.set_eq; intro k
    rw [GMap.elem_of_difference]
    exact ⟨fun h => h.1, fun h => absurd h (GMap.not_elem_of_empty _)⟩
  ihave Hphys := ownRaftPhys_toC' $$ Hphys
  ihave IH2 : iprop(∃ (k : w64) (pr : Peer) (sk : NState),
      "i" ∷ i_ptr ↦ k ∗
      "peer" ∷ peer_ptr ↦ pr ∗
      "Hphys" ∷ ownRaftPhysC (CfgM.simple (GMap.listToSet (ps.take (sint.nat k))) ∅) rnv.raft' id sk ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ (pv.length : Int) ∧
        ∃ (prs : GMap w64 Loc) (pvs : GMap w64 Progress) (b : Bool),
          sk = { s3 with progress := prs, prvals := pvs, isLearner := b }⌝)
    $$ [i peer Hphys]
  · iexists W64 0, _, s3
    simp only [named]
    iframe i peer
    isplitl [Hphys]
    · iExactEq Hphys
      rw [Hd3, show sint.nat (W64 0) = 0 by rfl, List.take_zero, GMap.listToSet_nil]
    · ipureintro
      refine ⟨by word, by word, s3.progress, s3.prvals, s3.isLearner, rfl⟩
  wp_for IH2
  wp_if_destruct
  · -- iteration `k`: `peer := peers[k]`
    have Hif' : sint.Z k < sint.Z peers.len := by
      first
        | exact Hif
        | (rcases Decidable.em (sint.Z k < sint.Z peers.len) with h | h
           · exact h
           · rw [decide_eq_false h] at Hif; exact absurd Hif false_neq_true)
    clear Hif
    obtain ⟨Hk1, Hk2, prs, pvs, b, Hsk⟩ := Hk
    have Hlt : sint.nat k < pv.length := by clear Hsk; word
    obtain ⟨p, Hpk⟩ : ∃ p, pv[sint.nat k]? = some p := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hpsk : ps[sint.nat k]? = some p.ID' := by
      rw [R1, List.getElem?_map, Hpk]; rfl
    have Hbnd' : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z peers.len := ⟨Hk1, Hif'⟩
    simp only [Hbnd', _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index peers (sint.Z k) _ dq p Hk1 $$ [Hpeers] as Hpeers
    · iframe; ipureintro; exact Hpk
    try wp_auto
    -- `(&pb.ConfChange{NodeId: new(peer.ID), Type: AddNode.Enum()}).AsV2()`
    rw [show raftpb.ConfChangeAddNode = #((W32 0 : raftpb.ConfChangeType)) from rfl]
    haveI : go.NotInterface go.int32 := ⟨by unfold go.int32; trivial⟩
    wp_apply wp_ConfChangeType_Enum (W32 0) as %pty Hpty
    imod cellRO_alloc $$ Hpty with #cTy
    imod cellRO_alloc $$ «$v0» with #cN
    wp_alloc cc as Hcc
    imod ownCCV1_of_struct cc (⟨zero_val _, pty, «$v0_ptr», slice.nil, null, slice.nil, 0⟩ : raftpb.ConfChange)
        ⟨W32 0, p.ID', [], W64 0⟩ ⊤ rfl $$ [Hcc] with Hcc
    · iframe Hcc cTy cN
      isplitl []
      · iunfold cellRO; ileft; ipureintro; exact ⟨rfl, rfl⟩
      iapply ownSlice_nil
    wp_apply wp_ConfChange_AsV2 cc (DFrac.own 1) _ $$ [$Hcc] as %v ⟨-, Hcc2⟩
    -- `rn.raft.applyConfChange(cc)`: the peer joins the voters (`bootCC_apply`)
    have Hskr : sk.role = .follower := by rw [Hsk]; exact Hs3r
    have Hp0 : p.ID' ≠ W64 0 := by
      intro h; apply R4; rw [← h]
      exact (List.getElem?_eq_some_iff.1 Hpsk).2 ▸ List.getElem_mem _
    have Hids : (cfgState (<[p.ID' := ()]> (GMap.listToSet (ps.take (sint.nat k)))) ∅).cfg.ids
        = GMap.listToSet (ps.take (sint.nat k + 1)) := by
      rw [cfgState_ids, listToSet_take_succ ps (sint.nat k) p.ID' Hpsk]
    have Hsz : (GMap.size (cfgState (<[p.ID' := ()]> (GMap.listToSet (ps.take (sint.nat k)))) ∅).cfg.ids : Int)
        ≤ 2 ^ 62 := by
      rw [Hids, GMap.size_list_to_set _ (R3.sublist (List.take_sublist _ _))]
      have := List.length_take_le (sint.nat k + 1) ps
      omega
    wp_apply wp_raft_applyConfChange (CfgM.simple (GMap.listToSet (ps.take (sint.nat k))) ∅) rnv.raft' id
        sk v _ (DFrac.own 1) (cfgState (<[p.ID' := ()]> (GMap.listToSet (ps.take (sint.nat k)))) ∅)
        (bootCC_apply _ _ Hp0) Hsz (by intro h; rw [Hskr] at h; cases h)
        (by intro h; rcases h with h | h <;> rw [Hskr] at h <;> cases h)
        (by intro h; rw [Hskr] at h; cases h)
      $$ [$Hphys $Hcc2] as %cs %xs %os %ls %lns %sk' ⟨Hphys, -, -, -, %Hok⟩
    obtain ⟨prs', pvs', Hsk'⟩ := applyCCOkC_nonleader _ _ _ _ Hok (by rw [Hskr]; decide)
    wp_for_post
    iframe
    iexists k + W64 1, _, sk'
    simp only [named]
    iframe i peer
    isplitl [Hphys]
    · iExactEq Hphys
      rw [show sint.nat (k + W64 1) = sint.nat k + 1 by clear Hsk Hsk'; word,
        listToSet_take_succ ps (sint.nat k) p.ID' Hpsk, cfgM_eq_simple]
    · ipureintro
      refine ⟨by clear Hsk Hsk'; word, by clear Hsk Hsk'; word, prs', pvs',
        learnerOfC (cfgState (<[p.ID' := ()]> (GMap.listToSet (ps.take (sint.nat k)))) ∅).cfg id, ?_⟩
      rw [Hsk', Hsk]
  -- the loop's exit: every peer a voter, `ownRaftPhys` at the cluster's configuration
  obtain ⟨Hk1, Hk2, prs, pvs, b, Hsk⟩ := Hk
  have Hklen : sint.nat k = pv.length := by clear Hsk; word
  have Htakek : ps.take (sint.nat k) = ps := by
    rw [Hklen, ← Hpslen]; exact List.take_length
  ihave Hphys : ownRaftPhysC (CfgM.simple (GMap.listToSet ps) ∅) rnv.raft' id sk $$ [Hphys]
  · iExactEq Hphys; rw [Htakek]
  icases ownRaftPhysC_sdr _ rnv.raft' id sk $$ Hphys with ⟨#Hsd0, Hphys⟩
  ihave #Hsdrf : sdrOk (GF := GF) rnv.raft' RNMode.static $$ []
  · iunfold sdrOk; iexists sk.sdr; iframe Hsd0; ipureintro; intro h; cases h
  ihave Hphys := ownRaftPhysC_toS $$ Hphys
  ihave Hphys : ownRaftPhys γ.reCfg rnv.raft' id sk $$ [Hphys]
  · rw [R7]; iexact Hphys
  -- the state: a follower at term `1`, the boot log committed -- `bootPState bootLog`
  have HN : sk.term = W64 1 ∧ sk.vote = W64 0 ∧ sk.lead = W64 0 ∧ sk.role = .follower ∧
      sk.votes = ∅ ∧ sk.outbox = [] ∧
      sk.logst = { logAppendLT s.logst s1.term bootLog with committed := ents.len } ∧ sk.gh = {} ∧
      sk.prevote = false ∧ sk.rd.states = [] ∧ sk.rd.pend = [] ∧
      sk.stepfn = stepFuncOf .follower ∧ sk.ticking = true := by
    rw [Hsk, ← Hs3, ← Hs2]
    refine ⟨Hs1t, Hs1v, Hs1l, Hs1r, Hs1vs, ?_, rfl, ?_, ?_, ?_, ?_, Hs1sf, Hs1tk⟩
    · show s1.outbox = []; rw [Hs1o, Ho]
    · show s1.gh = {}; rw [Hs1gh, Hgh]
    · show s1.prevote = false; rw [Hs1pv, Hpvoff]
    · show s1.rd.states = []; rw [Hs1rs, Hrst]
    · show s1.rd.pend = []; rw [Hs1rp, Hrpd]
  obtain ⟨HNt, HNv, HNl, HNr, HNvs, HNo, HNls, HNgh, HNpv, HNrs, HNrp, HNsf, HNtk⟩ := HN
  -- (raft#139) the log's leader term is the term `1` the boot entries were appended at
  have HLt : LtInv sk := by
    refine ⟨?_, fun h => by rw [HNr] at h; cases h⟩
    rw [HNls, HNt]
    show uint.Z (logAppendLT s.logst s1.term bootLog).leaderTerm ≤ _
    rw [logAppendLT_leaderTerm, Hs1t] at *
    split
    · exact Hlt0
    · exact Int.le_refl _
  have HNrel : NStateRel sk (bootPState bootLog) :=
    boot_post_rel bootLog sk ⟨by rw [HNsf, HNr], HNtk, HLt⟩ HNt HNv HNl HNr HNvs HNo
      (by rw [HNls]; simp only [logAppendLT_prev]; exact Hp)
      (by rw [HNls]; simp only [logAppendLT_sents]; exact Hse)
      (by rw [HNls]; simp only [logAppendLT_uents, Hue, List.nil_append])
      (by rw [HNls]; exact Hlenw) HNrs HNrp
  ihave #Hcomm0 := isCommitted_mono γ [] bootLog List.nil_prefix $$ Hcommitted
  try wp_auto
  iapply HΦ
  isplitl []
  · ipureintro; rfl
  isplitl [Hrn Hphys Hghost Hsteps Hsteps_cap]
  · iapply ownRawNode_intro_static γ rn id
        { delivered := [], unpersisted := [], steps := [], term := W64 1,
          storage := interface.ok si, mode := RNMode.static,
          cfg := cfgState (GMap.listToSet ps) ∅ }
        sk (bootPState bootLog) ({ rnv with prevHardSt' := es } : RawNode) sv
        (HardStateM.mk (W64 0) (W64 0) (W64 0)) [] rfl HNrel
        (by rw [R7]; exact (GMap.elem_of_list_to_set _ _).2 R6) Hasync
        (by rw [HNls]; simp only [logAppendLT_applying, Hapg0]; rfl)
        (by rw [HNls]; simp only [logAppendLT_unpersisted, Hun])
        (by rw [HNls]; simp only [logAppendLT_snap, Hsn]) trivial
        (by rw [HNt]) (by rw [HNls]; simp only [logAppendLT_storage, Hsg]) HNpv
        (by rw [HNgh]) (by rw [HNgh]) (uint_Z_nonneg _)
      $$ Hrn Hphys Hghost Hsdrf Hsoft Hes Hsteps Hsteps_cap [] Hcomm0 []
    · iapply pendList_nil
    · rw [HNls]; simp only [logAppendLT_stored, Hsd]; iapply storedRecs_nil
  · iexact Hpeers

end proof

end EtcdGrove
end Perennial

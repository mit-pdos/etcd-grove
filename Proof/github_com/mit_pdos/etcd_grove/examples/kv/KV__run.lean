/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kv/KV__run.lean`. Lean-first (no
Rocq counterpart). raft v3.7 (2026-10-16, stage R6b): a `Ready`'s entries and committed entries
are read-only entry pointers (`entsRO`), its messages owned pointers (`sendSpec`), its read
states Go values whose contexts hold their bytes (`readStatesPts_rsOk`), its hard state `hsOpt`
(unused: the store persists no hard state); a conf-change entry is decoded with
`proto.Unmarshal` into a fresh `pb.ConfChange`, applied by pointer (`ownConfChange_persist`:
`node.ApplyConfChange` reads it on raft's goroutine).

**Raft's node API (2026-10-27).** A `Ready` comes through `Draft.node.readyRecv`: its committed
entries (`Draft.committedEntriesAt`), its read states, the rest (`Draft.readyRest`): the entries to
persist, the messages, and the snapshot part (`Draft.readySnap`), in the storage contract's
vocabulary; and the loop's new state, by the snapshot's loan. A committed conf-change entry (type
`1`) is a requested one, so `RemoveMember`'s (`kv_committed_cc`, `RmReqs`): its bytes decode to
`rmCC id`, a change keeping the voters (`RmShrink id`), which `Draft.node.ApplyConfChange` applies in
the static cluster; `reconf` is set.

**Snapshots (D22 S-r, 2026-10-21).** The loop holds the storage's snapshot token at the
application's view `σt` (`runStor`, destructured once), whose snapshot is at `snapIndex`, at most
the applied index, which is exactly the length of the committed log applied (the `Ready`'s indices'
bound keeps it below `2^64`). A `Ready` comes with or without a snapshot (the loan `L`); the two meet
after `if rd.Snapshot != nil` (`wp_join`) at the committed log applied `D0`, the storage's token,
and the right to append the `Ready`'s entries with the receipt `Advance` takes (`advReceipt`):

* with a snapshot: its certificate (`Draft.snapshotCert_data`) says that the data encodes the
  replicated state of a committed log as long as the snapshot's index, which is the one the
  `Ready` hands out (`Draft.isCommittedLogLb_agree`); its decoded maps (`decodeState`) are
  `runOwn`'s at that log (`maps_of_stateEnc`), which `install` puts in place, answering this
  replica's waiters among the snapshot's operations; the storage installs it (`ApplySnapshot`, its
  registry's certificate from `readyOut`), then takes the entries after it (`memStorage_handout`,
  `memStorage_absorb`), the receipt `snapReceipt`;
* without one: as before (`appendRight`, `appendReceipt`).

After `Advance`, every `snapEvery` applied entries (never right after a snapshot `Ready`: it
applies nothing), the replica takes a snapshot of its state at the applied index: the floor's
witness (`Advance`'s, `kvStorFloor_at`) bounds the index, the data is `encodeState`'s
(`stateEnc_intro`), the configuration the cluster's voters (`Storage.voters`); it is certified
(`Draft.snapshotCert_static`) and registered at any term (`Draft.storageCert_registerAny`); then
`Compact`s to `snapMargin` below it -- unless `reconf` is set.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.KV__run
public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.KV__apply
public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.KV__answer
public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.KV__install
public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.fits
public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.encodeState
public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.decodeState
public import Spec.go_etcd_io.raft.v3.MemoryStorage__Append
public import Spec.go_etcd_io.raft.v3.MemoryStorage__ApplySnapshot
public import Spec.go_etcd_io.raft.v3.MemoryStorage__CreateSnapshot
public import Spec.go_etcd_io.raft.v3.MemoryStorage__Compact
public import Proof.go_etcd_io.raft.v3.MemstorageAU
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetType
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetData
public import Spec.google_golang_org.protobuf.proto.UnmarshalConfChange
public import Proof.github_com.mit_pdos.etcd_grove.examples.kv.Lemmas
public import Proof.github_com.mit_pdos.etcd_grove.examples.kv.KVStorageInstance
public import Proof.github_com.mit_pdos.etcd_grove.examples.kv.SnapData

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kv

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]
variable [KVStor GF]

/-- The configuration of the snapshots the replica takes, the cluster's voters, is well formed. -/
theorem snapListsOk_voters (vs : List w64) (t i : w64) (d : List w8) (hne : vs ≠ [])
    (hz : W64 0 ∉ vs) (hnd : vs.Nodup) (hl : (vs.length : Int) ≤ 2 ^ 62) (hi : uint.Z i < 2 ^ 61) :
    SnapListsOk ⟨⟨t, i⟩, (kvConfState vs).lists, false, d⟩ := by
  refine ⟨⟨hne, ?_, ?_, ?_, fun _ => rfl⟩, hnd, List.nodup_nil, List.nodup_nil, List.nodup_nil,
    by simp [kvConfState, ConfStateM.lists]; omega, fun _ => rfl, hi⟩
  · intro x hx
    simp only [kvConfState, ConfStateM.lists, List.not_mem_nil, false_or, or_false] at hx
    intro h; subst h; exact hz hx
  · intro x hx; simp [kvConfState, ConfStateM.lists] at hx
  · intro x hx; simp [kvConfState, ConfStateM.lists] at hx

theorem run_lt (k len : w64) (n m : Nat) (h : sint.Z k < sint.Z len) (h1 : m = sint.nat len)
    (h2 : m = n) (h0 : 0 ≤ sint.Z k) : sint.nat k < n := by
  subst h1 h2; word

theorem run_eq (k len : w64) (n m : Nat) (h : ¬ sint.Z k < sint.Z len) (h1 : m = sint.nat len)
    (h2 : m = n) (hk : sint.Z k ≤ (n : Int)) : sint.nat k = n := by
  subst h1 h2; word

theorem len_eq_unat (a : w64) (n : Nat) (h : uint.Z a = (n : Int)) : n = uint.nat a := by
  word

/-- The Go entry at position `k` of the log entries `ce` handed out after `base`. -/
theorem toEntries_get (ce : List Draft.LogEntry) (base k : Nat) (en : Draft.LogEntry)
    (h : ce[k]? = some en) :
    (Draft.LogEntry.toEntries ce base)[k]? = some (en.toEntryM (W64 (base + k + 1))) := by
  unfold Draft.LogEntry.toEntries; rw [List.getElem?_mapIdx, h]; rfl

theorem toEntries_length (ce : List Draft.LogEntry) (base : Nat) :
    (Draft.LogEntry.toEntries ce base).length = ce.length := by
  unfold Draft.LogEntry.toEntries; simp

set_option maxHeartbeats 8000000 in
theorem KV.run.wp_proof
    (wp_fits : kv.fits.spec (GF := GF) (hG := hG))
    (wp_apply : kv.KV.apply.spec (GF := GF) (hG := hG))
    (wp_answer : kv.KV.answer.spec (GF := GF) (hG := hG))
    (wp_install : kv.KV.install.spec (GF := GF) (hG := hG))
    (wp_encodeState : kv.encodeState.spec (GF := GF) (hG := hG))
    (wp_decodeState : kv.decodeState.spec (GF := GF) (hG := hG))
    (wp_node_Ready : Draft.node.Ready.spec (GF := GF) (hG := hG))
    (wp_readyRecv : Draft.node.readyRecv.spec (GF := GF) (hG := hG))
    (wp_node_Advance : Draft.node.Advance.spec (GF := GF) (hG := hG))
    (wp_MemoryStorage_Append : MemoryStorage.Append.spec (GF := GF) (hG := hG))
    (wp_MemoryStorage_ApplySnapshot : MemoryStorage.ApplySnapshot.spec (GF := GF) (hG := hG))
    (wp_MemoryStorage_CreateSnapshot : MemoryStorage.CreateSnapshot.spec (GF := GF) (hG := hG))
    (wp_MemoryStorage_Compact : MemoryStorage.Compact.spec (GF := GF) (hG := hG))
    (wp_proto_UnmarshalConfChange : proto.UnmarshalConfChange.spec (GF := GF) (hG := hG))
    (wp_node_ApplyConfChange : Draft.node.ApplyConfChange.spec (GF := GF) (hG := hG))
    (wp_Entry_GetType : raftpb.Entry.GetType.spec (GF := GF) (hG := hG))
    (wp_Entry_GetData : raftpb.Entry.GetData.spec (GF := GF) (hG := hG)) :
    KV.run.spec (GF := GF) (hG := hG) := by
  -- (D22 J3) the storage's snapshot methods with the whole token in hand: the AU specs' corollaries
  replace wp_MemoryStorage_ApplySnapshot :=
    MemoryStorage.ApplySnapshot.spec_tok_of wp_MemoryStorage_ApplySnapshot
  replace wp_MemoryStorage_CreateSnapshot :=
    MemoryStorage.CreateSnapshot.spec_tok_of wp_MemoryStorage_CreateSnapshot
  replace wp_MemoryStorage_Compact := MemoryStorage.Compact.spec_tok_of wp_MemoryStorage_Compact
  intro γr γp r id n st send
  wp_start as ⟨#Hrep, Hdrv, Hrun, Hstor, #Hsend⟩
  ihave #Hrep' := Hrep
  iunfold isReplica at Hrep'
  iNamed Hrep'
  ihave #Hraftinit : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  ihave #Hpbinit : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  ihave #Hprotoinit : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto $$ []
  · iPkgInit
  -- raft's error variables: `ErrSnapOutOfDate` and `ErrCompacted`
  ihave #Hinit := isInitialized_access $$ Hraftinit
  iunfold isInitialized at Hinit
  iNamed Hinit
  icases ErrSnapOOD with ⟨%eood, #Heood⟩
  -- (D22 S-r) the storage's snapshot token, its certificate registry and its voters
  unfold runStor
  icases Hstor with ⟨%ms, %γs, %vsl, #Hrec, Htok, #Hci, #Hvf, #Hvs, %Hsf⟩
  obtain ⟨Hcap, -⟩ := Hsf
  ihave #Hrec' := Hrec
  iunfold kvStorRec at Hrec'
  icases Hrec' with ⟨#Hmsf, -⟩
  wp_auto
  wp_apply wp_node_Ready γr.cluster kvRaftN id n $$ [$Hraftinit $HisNode] as %ch #Hch
  ihave IH : iprop(∃ (dv : Draft.NodeDriverState) (rdv : Ready) (pv : GoSlice)
      (ps : List ReadState) (a : w64) (sI : w64) (σt : StorState) (rc : Bool),
      "Hrd" ∷ rd_ptr ↦ rdv ∗ "Hdrv" ∷ Draft.nodeDriver n γr.cluster kvRaftN dv ∗
      "Hrun" ∷ runOwn γr r dv.delivered ∗
      "pending" ∷ pending_ptr ↦ pv ∗ "Hpv" ∷ pv ↦* ps ∗
      "Hpcap" ∷ ownSliceCap ReadState pv (DFrac.own 1) ∗
      "Hps" ∷ ([∗list] v ∈ ps, rsOk γr.cluster v) ∗
      "applied" ∷ applied_ptr ↦ a ∗ "snapIndex" ∷ snapIndex_ptr ↦ sI ∗
      "reconf" ∷ reconf_ptr ↦ rc ∗ "Htok" ∷ memSnapTok ms γs σt ∗
      "%Ha" ∷ ⌜uint.Z a = (dv.delivered.length : Int) ∧ σt.ss.index' = sI ∧ uint.Z sI ≤ uint.Z a ∧
        uint.Z σt.prev.index' ≤ uint.Z σt.ss.index' ∧ dv.handling = none ∧
        dv.storage = kvStorIface st⌝)
    $$ [rd Hdrv Hrun pending applied snapIndex reconf Htok]
  · iexists Draft.NodeDriverState.init (kvStorIface st), _, _, [], _, _, memStorEmpty, false
    iframe
    isplitl []
    · iapply ownSlice_nil
    isplitl []
    · iapply ownSliceCap_nil
    isplitl []
    · iapply (BigSepL.bigSepL_nil).2; iempintro
    ipureintro
    refine ⟨rfl, rfl, Int.le_refl _, Int.le_refl _, rfl, rfl⟩
  wp_for IH
  try wp_auto
  wp_apply wp_readyRecv n ch γr.cluster kvRaftN id dv Ha.2.2.2.2.1 $$ [$Hch $HisNode $Hdrv]
    as %rdv' ⟨%ce, %es, %hh, %L, #Hce, #Hcomm, ⟨%sts, #Hsts, #Hstsok⟩, Hrest, Hdrv⟩
  unfold Draft.readyRest
  icases Hrest with ⟨%msgs, #Hes, Hms, Hmsok, -, -, %Hidx, HS⟩
  -- the loop's new state, by the snapshot's loan
  ihave Hdrv : iprop(∃ dv' : Draft.NodeDriverState, Draft.nodeDriver n γr.cluster kvRaftN dv' ∗
      ⌜dv'.storage = dv.storage ∧ dv'.handling = some (es, L) ∧
        (L = none → dv'.delivered = dv.delivered ++ ce) ∧
        (∀ l, L = some l → dv'.delivered = Draft.strip l.dlv)⌝) $$ [Hdrv]
  · cases L with
    | none =>
      iexists _; iframe Hdrv; ipureintro
      refine ⟨rfl, rfl, fun _ => rfl, ?_⟩
      intro l h; cases h
    | some l0 =>
      iexists _; iframe Hdrv; ipureintro
      refine ⟨rfl, rfl, ?_, ?_⟩
      · intro h; cases h
      · intro l h; cases h; rfl
  icases Hdrv with ⟨%dv', Hdrv, %Hdv'⟩
  obtain ⟨Lr, HLr⟩ := Hidx
  have HstorEq : dv'.storage = kvStorIface st := Hdv'.1.trans Ha.2.2.2.2.2
  wp_apply wp_fits rdv'.Entries' es DFrac.discard $$ [$Hes] as %b ⟨-, %Hfit⟩
  cases b
  · -- a log past `maxIndex`: the replica stops
    wp_auto
    ihave Hspin : iprop(True) $$ []
    · itrivial
    wp_for Hspin
    wp_for_post
    iframe
  wp_auto
  -- (D22 S-r) `if rd.Snapshot != nil { ... }`: the two paths meet at the committed log applied
  -- `D0`, the storage's token, and the right to append the `Ready`'s entries
  wp_join iprop(∃ (D0 : List Draft.LogEntry) (a0 sI0 : w64) (σt0 σA : StorState),
      "Hrd" ∷ rd_ptr ↦ rdv' ∗ "r" ∷ r_ptr ↦ r ∗ "Hrun" ∷ runOwn γr r D0 ∗
      "applied" ∷ applied_ptr ↦ a0 ∗ "snapIndex" ∷ snapIndex_ptr ↦ sI0 ∗
      "Htok" ∷ memSnapTok ms γs σt0 ∗
      "%Ha0" ∷ ⌜uint.Z a0 = (D0.length : Int) ∧ σt0.ss.index' = sI0 ∧ uint.Z sI0 ≤ uint.Z a0 ∧
        uint.Z σt0.prev.index' ≤ uint.Z σt0.ss.index' ∧ D0 ++ ce = dv'.delivered ∧
        (L.isSome → ce = [] ∧ a0 = sI0) ∧ ((D0 ++ ce).length : Int) < 2 ^ 64⌝ ∗
      "#Hcomm0" ∷ Draft.isCommittedLogLb γr.cluster (D0 ++ ce) ∗
      "Happ" ∷ (⌜es = []⌝ ∨ memAppendTok ms γs σA es) ∗
      "Hrb" ∷ ((⌜es = []⌝ ∨ memAppendedTok ms γs σA es) -∗ |==> advReceipt (kvStorIface st) es L))
    at (If _ _ _) with [Hrd r Hrun applied snapIndex Htok HS]
    as ⟨%D0, %a0, %sI0, %σt0, %σA, Hrd, r, Hrun, applied, snapIndex, Htok, %Ha0, #Hcomm0, Happ, Hrb⟩
  · cases L with
    | none =>
      -- no snapshot: the right to append, as before
      simp only [Draft.readySnap]
      icases HS with ⟨%Hsn, Happ⟩
      have Hdl : dv'.delivered = dv.delivered ++ ce := Hdv'.2.2.1 rfl
      rw [Hsn]
      wp_auto
      wp_join_done
      ihave Happ : iprop(∃ σ, ⌜es = []⌝ ∨ memAppendTok ms γs σ es) $$ [Happ]
      · unfold appendRight
        rw [Ha.2.2.2.2.2]
        icases Happ with (%Hnil | ⟨%σ, Happ⟩)
        · iexists memStorEmpty; ileft; ipureintro; exact Hnil
        ihave Happ : kvAppendTok (kvStorIface st) σ es $$ Happ
        unfold kvAppendTok
        icases Happ with ⟨%s', %ms', %γs', %Hst', #Hrec2, Happ⟩
        have := kvStorIface_inj (GF := GF) _ _ Hst'
        subst this
        icases kvStorRec_agree st ms ms' γs γs' $$ Hrec Hrec2 with ⟨%H1, %H2⟩
        subst H1 H2
        iexists σ; iright; iexact Happ
      icases Happ with ⟨%σ, Happ⟩
      iexists dv.delivered, a, sI, σt, σ
      iframe Hrd r Hrun applied snapIndex Htok Happ
      isplitr
      · ipureintro
        refine ⟨Ha.1, Ha.2.1, Ha.2.2.1, Ha.2.2.2.1, Hdl.symm, (fun h => by cases h), ?_⟩
        omega
      isplitr
      · iexact Hcomm
      iintro Hdone
      imodintro
      simp only [advReceipt]
      unfold appendReceipt
      icases Hdone with (%Hnil | Hd)
      · ileft; ipureintro; exact Hnil
      iright; iexists σ
      ihave H : kvAppendedTok (kvStorIface st) σ es $$ [Hd]
      · unfold kvAppendedTok
        iexists st, ms, γs
        iframe Hrec Hd
        ipureintro; rfl
      iexact H
    | some l =>
      -- a snapshot: installed
      simp only [Draft.readySnap]
      icases HS with ⟨%Hl, Hsn, #Hdl, #Hscert, Hout⟩
      obtain ⟨-, Hptr, Hce0, Hpre, Hlen, Hdlv, Hi0, Hi61, Hfl, Hlio⟩ := Hl
      have Hdlv' : dv'.delivered = Draft.strip l.dlv := Hdv'.2.2.2 l rfl
      have Hsl : (Draft.strip l.dlv).length = l.dlv.length := by simp [Draft.strip]
      rw [← Hsl] at Hlen Hdlv
      generalize Draft.strip l.dlv = dl at Hlen Hdlv Hdlv' Hpre ⊢
      subst Hce0
      unfold readyOut
      icases Hout with ⟨⟨%σ, Hown, %Hσ⟩, #Hcert⟩
      ihave Hms : ownMemoryStorage ms γs σ $$ [Hown]
      · iapply kvOwnStorage_at st ms γs σ $$ Hrec
        rw [← Ha.2.2.2.2.2]; iexact Hown
      -- its data certificate: the data encodes the replicated state of the loan's committed log
      ihave #Hmc : memStorCert γs (snapTrip l.snap l.snap.Metadata'.ConfState'.lists) $$ []
      · iapply kvStorCert_at st ms γs _ $$ Hrec
        rw [← Ha.2.2.2.2.2]; iexact Hcert
      -- its data: the replicated state of the committed log up to it (`Draft.snapshotCert_data`)
      icases Draft.snapshotCert_data γr.cluster kvRaftN kvVoters kvSnapOk _ $$ [Hstatic Hscert]
        with ⟨%L', #HcL', %HL'⟩
      · iframe Hstatic Hscert
      ihave %Hag := Draft.isCommittedLogLb_agree γr.cluster L' dl $$ [HcL' Hdl]
      · iframe HcL' Hdl
      have HLeq : L' = dl := by
        have hl : L'.length = dl.length := by rw [HL'.1, Hdlv]; rfl
        rcases Hag with h | h
        · exact h.eq_of_length hl
        · exact (h.eq_of_length hl.symm).symm
      subst HLeq
      have HSE : StateEnc (histOf (L'.map odOf)) l.snap.Data' := HL'.2
      obtain ⟨kvs, ops, HdEq, HKw, HOw, Hk, Ho⟩ := HSE
      icases ownSnapS_not_null _ _ _ $$ Hsn with ⟨Hsn, %Hpn⟩
      rw [← Hptr, decide_eq_false Hpn]
      try wp_auto
      try rw [← Hptr]
      -- `decodeState(rd.Snapshot.GetData())`
      wp_apply wp_Snapshot_GetData_S l.ptr _ l.snap $$ [$Hpbinit $Hsn] as %dsl ⟨Hd, Hdback⟩
      wp_apply wp_decodeState dsl _ kvs ops HKw HOw $$ [$Hpkg Hd]
        as %mK' %mA' ⟨Hd, %K', %A', HK', HA', %HKA⟩
      · rw [← HdEq]; iexact Hd
      ihave Hsn := Hdback $$ [Hd]
      · rw [HdEq]; iexact Hd
      try wp_auto
      try rw [← Hptr]
      -- the store's state replaced (`install`, 2026-10-22: which answers this replica's waiters
      -- among the snapshot's operations): `runOwn` at the loan's committed log
      obtain ⟨HvalS, HAS⟩ := maps_of_stateEnc _ kvs ops K' A' Hk Ho HKA.1 HKA.2
      wp_apply wp_install γr γp r id n st dv.delivered L' (L'.map odOf) mK' mA' K' A' rfl HvalS
        HAS $$ [$Hpkg $Hrep $Hrun $HK' $HA' $HcL'] as Hrun
      try wp_auto
      try rw [← Hptr]
      -- `applied = rd.Snapshot.GetMetadata().GetIndex()`, `snapIndex = applied`
      wp_apply wp_Snapshot_GetMetadata_S l.ptr _ l.snap $$ [$Hpbinit $Hsn] as %pm ⟨Hmd, Hmback⟩
      wp_apply wp_SnapshotMetadata_GetIndex_S pm _ _ $$ [$Hpbinit $Hmd] as Hmd
      ihave Hsn := Hmback $$ Hmd
      try wp_auto
      try rw [← Hptr]
      -- `r.storage.ApplySnapshot(rd.Snapshot)`: newer than the application's snapshot
      wp_method_call
      try wp_auto
      try rw [← Hptr]
      have Hcap' : uint.Z l.snap.Metadata'.Index' ≤ γs.cap := by rw [Hcap]; word
      wp_apply +noauto wp_MemoryStorage_ApplySnapshot ms γs σ σt l.ptr l.snap _ eood Hσ.1 Hi61
          (by rw [Hσ.2]; exact Hfl) Hcap'
        $$ [$Hraftinit $Hms $Htok Hsn $Hmc $Heood] as %err ⟨Hsn, Hres⟩
      · unfold snapArg; iright; iexact Hsn
      icases Hres with (⟨%Hbad, -, -⟩ | ⟨-, Hms, Htok⟩)
      · exfalso
        have h1 : (dv.delivered.length : Int) < L'.length := by exact_mod_cast Hlen
        have h2 : (L'.length : Int) = uint.Z l.snap.Metadata'.Index' := by
          rw [Hdlv]
        have h3 := Hbad.2.1
        rw [Ha.2.1] at h3
        omega
      -- the entries after the snapshot: handed to the storage
      have Hσ' : ({ memStorApplied l.snap with fl := σ.fl } : StorState).prev = snapId l.snap := rfl
      have Hidx : (L'.length : Int) = uint.Z l.snap.Metadata'.Index' := by
        rw [Hdlv]
      by_cases Hes0 : es = []
      · try wp_auto
        wp_join_done
        iexists L', l.snap.Metadata'.Index', l.snap.Metadata'.Index', memStorApplied l.snap,
          { memStorApplied l.snap with fl := σ.fl }
        iframe Hrd r Hrun applied snapIndex Htok
        isplitr
        · ipureintro
          refine ⟨Hidx.symm, rfl, Int.le_refl _, Int.le_refl _, by simp [Hdlv'], fun _ => ⟨rfl, rfl⟩, ?_⟩
          simp only [List.append_nil]; omega
        isplitr
        · simp only [List.append_nil]; iexact HcL'
        isplitr
        · ileft; ipureintro; exact Hes0
        iintro -
        imodintro
        simp only [advReceipt, snapReceipt]
        iframe Hsn
        iexists { memStorApplied l.snap with fl := σ.fl }
        isplitl
        · iapply kvOwnStorage_intro st ms γs _ $$ Hrec Hms
        ipureintro
        exact ⟨rfl, rfl, Hes0.symm, rfl, Hσ.2, rfl, rfl, rfl⟩
      imod memStorage_handout ms γs { memStorApplied l.snap with fl := σ.fl } es
          ⟨rfl, pendOk_of_logIndices _ es Hes0 rfl Hlio,
            pendAbove_of_logIndices _ es (by rw [Hσ.2]; exact Hfl) Hlio⟩ $$ Hms
        with ⟨Hms, Happ⟩
      try wp_auto
      wp_join_done
      iexists L', l.snap.Metadata'.Index', l.snap.Metadata'.Index', memStorApplied l.snap,
        { memStorApplied l.snap with fl := σ.fl }
      iframe Hrd r Hrun applied snapIndex Htok
      isplitr
      · ipureintro
        refine ⟨Hidx.symm, rfl, Int.le_refl _, Int.le_refl _, by simp [Hdlv'], fun _ => ⟨rfl, rfl⟩, ?_⟩
        simp only [List.append_nil]; omega
      isplitr
      · simp only [List.append_nil]; iexact HcL'
      isplitl [Happ]
      · iright; iexact Happ
      iintro (%Hnil | Hdone)
      · exact absurd Hnil Hes0
      imod memStorage_absorb ms γs _ _ es $$ Hms Hdone with ⟨-, Hms⟩
      imodintro
      simp only [advReceipt, snapReceipt]
      iframe Hsn
      iexists storAbsorb { { memStorApplied l.snap with fl := σ.fl } with pend := es }
      isplitl
      · iapply kvOwnStorage_intro st ms γs _ $$ Hrec Hms
      ipureintro
      obtain ⟨e0, es', rfl⟩ := List.exists_cons_of_ne_nil Hes0
      exact ⟨rfl, rfl, by simp [storAbsorb, storApp, memStorApplied], rfl, Hσ.2, rfl, rfl, rfl⟩
  -- `r.storage.Append(rd.Entries)`, the promoted `MemoryStorage.Append`
  try wp_auto
  wp_method_call
  try wp_auto
  wp_apply wp_MemoryStorage_Append ms γs σA es rdv'.Entries' DFrac.discard (Hfit rfl)
    $$ [$Hraftinit $Happ $Hes] as ⟨Hdone, -⟩
  imod Hrb $$ Hdone with Hrcpt
  -- `send(rd.Messages)`: the messages as `Ready` hands them out
  wp_bind (App (Val #send) _)
  iunfold sendSpec at Hsend
  iapply Hsend $$ [Hms Hmsok]
  · iframe
  iintro !> -
  try wp_auto
  -- the read states, noted (`rsOk` of each value)
  ihave Hvs := readStatesPts_rsOk γr.cluster rdv'.ReadStates' sts $$ [Hsts Hstsok]
  · iframe Hsts Hstsok
  icases Hvs with ⟨%vls, #Hvls, #Hvlsok⟩
  wp_apply wp_slice_append $$ [$Hpv $Hpcap $Hvls] as %pv' ⟨Hpv, Hpcap, -⟩
  ihave Hps : iprop([∗list] v ∈ ps ++ vls, rsOk γr.cluster v) $$ [Hps]
  · iapply (BigSepL.bigSepL_append (Φ := fun _ v => rsOk (GF := GF) γr.cluster v)).2
    iframe Hps
    iexact Hvlsok
  -- applying the committed entries, in order
  iunfold Draft.committedEntriesAt at Hce
  icases entsPts_elim _ _ _ $$ Hce with ⟨%cls, #Hce, #Hceb⟩
  ihave %Hcelen := ownSlice_len $$ Hce
  ihave %Hcebl := entsBig_length $$ Hceb
  rw [toEntries_length] at Hcebl
  have Hbig := Ha0.2.2.2.2.2.2
  ihave IHa : iprop(∃ (k : w64) (ev : Loc) (a' : w64) (rc' : Bool),
      "i" ∷ i_ptr ↦ k ∗ "e" ∷ e_ptr ↦ ev ∗ "Hrun" ∷ runOwn γr r (D0 ++ ce.take (sint.nat k)) ∗
      "applied" ∷ applied_ptr ↦ a' ∗ "reconf" ∷ reconf_ptr ↦ rc' ∗
      "%Ha" ∷ ⌜uint.Z a' = ((D0 ++ ce.take (sint.nat k)).length : Int)⌝ ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ (ce.length : Int)⌝)
    $$ [i e Hrun applied reconf]
  · iexists W64 0, _, a0, rc
    iframe i e applied reconf
    simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.append_nil]
    iframe Hrun
    ipureintro
    refine ⟨Ha0.1, by constructor <;> word⟩
  wp_for IHa
  cleanup_bool_decide
  wp_if_destruct
  · have Hlt : sint.nat k < ce.length :=
      run_lt k _ _ _ (by first | exact Hif | exact of_decide_eq_true (go.intoVal_inj Hif)) Hcelen.1 Hcebl Hk.1
    obtain ⟨en, Hen⟩ : ∃ en, ce[sint.nat k]? = some en := ⟨_, List.getElem?_eq_getElem Hlt⟩
    ihave ⟨%ln, %Hln, #Hent⟩ := entsBig_lookup cls _ (sint.nat k) _
      (toEntries_get ce dv.delivered.length (sint.nat k) en Hen) $$ Hceb
    have Hbnd' : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z rdv'.CommittedEntries'.len := ⟨Hk.1, by word⟩
    simp only [Hbnd', _root_.and_self]
    wp_apply wp_load_slice_index rdv'.CommittedEntries' (sint.Z k) _ DFrac.discard ln Hk.1 $$ [Hce] as -
    · iframe Hce; ipureintro; exact Hln
    have Htk : ce.take (sint.nat k + 1) = ce.take (sint.nat k) ++ [en] := by
      rw [List.take_add_one, Hen]; rfl
    ihave #Hc1 := Draft.isCommittedLogLb_mono γr.cluster (D0 ++ ce.take (sint.nat k) ++ [en])
      (D0 ++ ce)
      (by rw [List.append_assoc, ← Htk]; exact List.prefix_append_right_inj _ |>.mpr (List.take_prefix _ _))
      $$ Hcomm0
    -- `if e.GetType() == pb.EntryConfChange { ... r.node.ApplyConfChange(&cc) }`
    wp_apply wp_Entry_GetType.1 ln DFrac.discard _ $$ [$Hpbinit $Hent] as -
    wp_join iprop(∃ rc2 : Bool, reconf_ptr ↦ rc2 ∗ e_ptr ↦ ln ∗ r_ptr ↦ r)
      at next with [reconf e r] as ⟨%rc2, reconf, e, r⟩
    · by_cases Hty1 : en.type = W32 1
      · rw [decide_eq_true Hty1]
        -- a committed conf change is a `RemoveMember`'s, which keeps the voters (`RmReqs`)
        imod kv_committed_cc γr (D0 ++ ce.take (sint.nat k) ++ [en]) en ⊤ CoPset.subseteq_top
            (List.mem_append_right _ (List.mem_singleton_self _)) Hty1 $$ Hinv Hc1
          with %Hcc
        obtain ⟨rid, Hm, Hsh⟩ := Hcc
        try wp_auto
        -- `proto.Unmarshal(e.GetData(), &cc)`: the bytes decode (the error is nil)
        wp_apply wp_Entry_GetData.1 ln DFrac.discard _ $$ [$Hpbinit $Hent] as %ds1 ⟨#Hds1, -⟩
        wp_apply wp_proto_UnmarshalConfChange ds1 _ DFrac.discard cc_ptr _
          $$ [$Hprotoinit $Hds1 $cc] as %err ⟨-, Hres⟩
        rw [Hm]
        icases Hres with ⟨%Herr, Hown⟩
        imod ownConfChange_persist $$ Hown with #Hown
        try wp_auto
        -- `r.node.ApplyConfChange(&cc)`: a change keeping the voters (`RmShrink`)
        ihave Hcci : ownConfChangeI (interface.mkOk (go.GoType.PointerType raftpb.ConfChange.ty) #cc_ptr)
            DFrac.discard (some (.v1 (rmCC rid))) $$ []
        · simp only [ownConfChangeI]
          iexists cc_ptr
          iframe Hown
          ipureintro; rfl
        wp_apply wp_node_ApplyConfChange n γr.cluster kvRaftN id kvVoters kvSnapOk _
            (.v1 (rmCC rid)) Hsh
          $$ [$Hraftinit $HisNode $Hstatic $Hcci] as %csp %cs -
        try wp_auto
        wp_join_done
      · rw [decide_eq_false Hty1]
        try wp_auto
        wp_join_done
    wp_apply wp_apply γr γp r id n st (D0 ++ ce.take (sint.nat k)) ln en _
      $$ [$Hpkg $Hrep $Hrun $Hent $Hc1] as Hrun
    wp_for_post
    iframe
    iexists k + W64 1, ln, a' + W64 1, rc2
    rw [show sint.nat (k + W64 1) = sint.nat k + 1 by word, Htk, List.append_assoc]
    iframe
    ipureintro
    have Hl : ((D0 ++ (ce.take (sint.nat k) ++ [en])).length : Int) =
        ((D0 ++ ce.take (sint.nat k)).length : Int) + 1 := by simp; omega
    have Hle : ((D0 ++ (ce.take (sint.nat k) ++ [en])).length : Int) ≤ ((D0 ++ ce).length : Int) := by
      simp; omega
    refine ⟨?_, ?_⟩
    · rw [Hl]; rw [Hl] at Hle; word
    · constructor <;> word
  · have HnP : ¬ sint.Z k < sint.Z rdv'.CommittedEntries'.len :=
      by first | exact Hif | exact fun h => Hif (by rw [decide_eq_true h])
    have Hfull : sint.nat k = ce.length := run_eq k _ _ _ HnP Hcelen.1 Hcebl Hk.2
    try simp only [decide_eq_false HnP, eq_self_iff_true, _root_.decide_true, ↓reduceIte]
    try wp_auto
    rw [Hfull, List.take_of_length_le (by omega)] at Ha ⊢
    -- the reads whose index is applied, answered
    wp_apply wp_answer γr γp r id n st (D0 ++ ce) pv' (ps ++ vls) (DFrac.own 1) a' (Int.le_of_eq Ha)
      $$ [$Hpkg $Hrep $Hrun $Hpv $Hps] as %rest ⟨Hrun, %ps', Hrest, Hcap2, Hps'⟩
    rw [show advReceipt (kvStorIface st) es L = advReceipt dv'.storage es L by rw [HstorEq]]
    wp_apply wp_node_Advance n γr.cluster kvRaftN kvVoters kvSnapOk dv' es L Hdv'.2.1
      $$ [$Hraftinit $Hstatic $Hdrv $Hrcpt] as ⟨Hdrv, Hreq⟩
    try wp_auto
    -- (D22 S-r) `if !reconf && applied-snapIndex >= snapEvery`: a snapshot
    have Hsa : uint.Z sI0 ≤ uint.Z a' := by
      have : ((D0 ++ ce).length : Int) ≥ D0.length := by simp; omega
      have := Ha0.1; have := Ha0.2.2.1; omega
    cases rc' with
    | true =>
      -- a conf change applied: no more snapshots (the voters are no longer the configuration)
      try wp_auto
      wp_for_post
      iframe
      iexists { dv' with handling := none }, rdv', rest, ps', a', sI0, σt0, true
      rw [show ({ dv' with handling := none } : Draft.NodeDriverState).delivered = D0 ++ ce
        from Ha0.2.2.2.2.1.symm]
      iframe
      ipureintro
      exact ⟨Ha, Ha0.2.1, Hsa, Ha0.2.2.2.1, rfl, HstorEq⟩
    | false =>
    try wp_auto
    wp_if_destruct
    · -- the snapshot: only after a `Ready` without one (a snapshot `Ready` applies nothing)
      have Hge : uint.Z (W64 100) ≤ uint.Z (a' - sI0) := by
        first | exact Hif | (revert Hif; simp)
      have Hsub : uint.Z (a' - sI0) = uint.Z a' - uint.Z sI0 := by word
      cases L with
      | some l =>
        exfalso
        obtain ⟨Hce0, Haeq⟩ := Ha0.2.2.2.2.2.1 rfl
        subst Hce0 Haeq
        have : uint.Z a' = uint.Z a0 := by rw [Ha, Ha0.1]; simp
        rw [Hsub] at Hge
        have : uint.Z (W64 100) = 100 := by decide
        omega
      | none =>
      simp only
      icases Hreq with ⟨%x, #Hfx, %Hx⟩
      ihave ⟨#Hmf, %Hx61⟩ := kvStorFloor_at st ms γs x $$ Hrec [Hfx]
      · rw [← HstorEq]; iexact Hfx
      have Ha'x : uint.Z a' ≤ uint.Z x := by rw [Ha, Ha0.2.2.2.2.1]; exact Hx
      -- `data := encodeState(r.kv, r.applied)`, under the lock
      iunfold runOwn at Hrun
      iNamed Hrun
      wp_apply sync.Mutex.wp_Lock _ _ $$ [$Hmu] as ⟨Hlocked, HR⟩
      try wp_auto
      wp_apply wp_encodeState mK mA K A (DFrac.own 1) (DFrac.own 1) $$ [$Hpkg $HK $HA]
        as %dsl ⟨HK, HA, %kvs, %ops, Hdsl, %Hko⟩
      try wp_auto
      wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hmu $Hlocked HR]
      · inext; iexact HR
      try wp_auto
      -- `&pb.ConfState{Voters: r.storage.voters}`: the voters read-only, frozen
      imod csPts_of_struct_ro «$a1_ptr»
          (⟨zero_val _, vsl, slice.nil, slice.nil, slice.nil, null, slice.nil, 0⟩ : raftpb.ConfState)
          (kvConfState kvVoters) ⊤ rfl $$ [«$a1»] with #Hcs
      · iframe «$a1»
        simp only [kvConfState]
        iframe Hvs
        repeat (isplitr; · iapply ownSlice_nil)
        iunfold cellRO; ileft; ipureintro; exact ⟨rfl, rfl⟩
      try wp_auto
      -- the snapshot's certificates: the cluster's voters, and the data of the applied log
      have HSE : kvSnapOk (D0 ++ ce) (encState kvs ops) := by
        unfold kvSnapOk logHist; rw [← Hods]
        exact stateEnc_intro _ K A kvs ops Hval HA Hko.1 Hko.2
      have Ha61 : uint.Z a' < 2 ^ 61 := by omega
      ihave #Hrc := Draft.snapshotCert_static γr.cluster kvRaftN kvVoters kvSnapOk (D0 ++ ce) a'
        (encState kvs ops)
        (fun t => snapListsOk_voters kvVoters t a' _ (by decide) (by decide) (by decide)
          (by decide) Ha61)
        (len_eq_unat a' _ Ha) HSE $$ [Hstatic Hap]
      · iframe Hstatic Hap
      imod Draft.storageCert_registerAny γr.cluster kvRaftN γs a' _ false _ ⊤ CoPset.subseteq_top
        $$ Hci Hrc with #Hmc
      -- `r.storage.CreateSnapshot(applied, cs, data)`: newer than the application's snapshot
      wp_method_call
      try wp_auto
      have Hlt : uint.Z sI0 < uint.Z a' := by
        rw [Hsub] at Hge
        have : uint.Z (W64 100) = 100 := by decide
        omega
      wp_apply wp_MemoryStorage_CreateSnapshot ms γs σt0 x a' «$a1_ptr» DFrac.discard
          (some (kvConfState kvVoters))
          dsl (encState kvs ops) eood
          (fun _ => ⟨by have := Ha0.2.2.2.1; rw [Ha0.2.1] at this; omega, Ha'x⟩)
        $$ [$Hraftinit $Htok $Hmf Hcs $Hdsl $Heood] as %snap' %err ⟨-, Hres⟩
      · isplitl
        · simp only
          iapply csPts_weaken; iexact Hcs
        imodintro
        iintro %t
        have Heq : snapTrip (memSnapCreated σt0 a' t (some (kvConfState kvVoters)) (encState kvs ops))
            (memSnapCreated σt0 a' t (some (kvConfState kvVoters))
              (encState kvs ops)).Metadata'.ConfState'.lists =
            ⟨⟨t, a'⟩, ⟨kvVoters, [], [], []⟩, false, encState kvs ops⟩ := rfl
        rw [Heq]
        iapply Hmc
      icases Hres with (⟨%Hbad, -, -⟩ | ⟨%t, ⟨%Hok, -⟩, -, Htok⟩)
      · exfalso; rw [Ha0.2.1] at Hbad; omega
      try wp_auto
      -- `if applied > snapMargin { r.storage.Compact(applied - snapMargin) }`
      wp_join iprop(∃ σt2 : StorState, memSnapTok ms γs σt2 ∗ r_ptr ↦ r ∗ applied_ptr ↦ a' ∗
          ⌜σt2.ss.index' = a' ∧ uint.Z σt2.prev.index' ≤ uint.Z σt2.ss.index'⌝)
        with [Htok r applied] as ⟨%σt2, Htok, r, applied, %Hσt2⟩
      · try wp_auto
        wp_method_call
        try wp_auto
        have Hci' : uint.Z (a' - W64 10) ≤ uint.Z a' := by word
        wp_apply wp_MemoryStorage_Compact ms γs _ x (a' - W64 10) errCompacted
            (fun _ => ⟨by omega, Hci', by rw [Hcap]; word⟩)
          $$ [$Hraftinit $Htok $Hmf $ErrCompacted] as %err2 Hres2
        icases Hres2 with (⟨-, Htok⟩ | ⟨%t2, -, Htok⟩)
        · try wp_join_done
          iexists _
          iframe Htok r applied
          ipureintro
          refine ⟨rfl, ?_⟩
          have := Ha0.2.2.2.1; rw [Ha0.2.1] at this; simp only; omega
        · try wp_join_done
          iexists _
          iframe Htok r applied
          ipureintro
          exact ⟨rfl, Hci'⟩
      · try wp_join_done
        iexists _
        iframe Htok r applied
        ipureintro
        refine ⟨rfl, ?_⟩
        have := Ha0.2.2.2.1; rw [Ha0.2.1] at this; simp only; omega
      wp_for_post
      iframe
      iexists { dv' with handling := none }, rdv', rest, ps', a', a', σt2, false
      iframe Hdrv
      ihave Hrun : runOwn γr r ({ dv' with handling := none } : Draft.NodeDriverState).delivered
        $$ [HmK HK HmA HA]
      · unfold runOwn
        iexists mK, K, mA, A, ods
        rw [show ({ dv' with handling := none } : Draft.NodeDriverState).delivered = D0 ++ ce
          from Ha0.2.2.2.2.1.symm]
        iframe HmK HK HmA HA Hap
        ipureintro; exact ⟨Hods, Hval, HA⟩
      iframe
      ipureintro
      refine ⟨?_, Hσt2.1, Int.le_refl _, Hσt2.2, rfl, HstorEq⟩
      show uint.Z a' = (dv'.delivered.length : Int); rw [← Ha0.2.2.2.2.1]; exact Ha
    · -- no snapshot taken
      wp_for_post
      iframe
      iexists { dv' with handling := none }, rdv', rest, ps', a', sI0, σt0, false
      rw [show ({ dv' with handling := none } : Draft.NodeDriverState).delivered = D0 ++ ce
        from Ha0.2.2.2.2.1.symm]
      iframe
      ipureintro
      exact ⟨Ha, Ha0.2.1, Hsa, Ha0.2.2.2.1, rfl, HstorEq⟩

end proof

end kv
end EtcdGrove
end Perennial

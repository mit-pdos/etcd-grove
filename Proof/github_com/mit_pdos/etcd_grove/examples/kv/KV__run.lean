/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kv/KV__run.lean`. Lean-first (no
Rocq counterpart). raft v3.7 (2026-10-16, stage R6b): a `Ready`'s entries and committed entries
are read-only entry pointers (`entsRO`), its messages owned pointers (`sendSpec`), its read
states Go values whose contexts hold their bytes (`readStatesPts_rsOk`), its hard state `hsOpt`
(unused: the store persists no hard state); a conf-change entry is decoded with
`proto.Unmarshal` into a fresh `pb.ConfChange`, applied by pointer (`ownConfChange_persist`:
`node.ApplyConfChange` reads it on raft's goroutine).

**Snapshots (D22 S-r, 2026-10-21).** The loop holds the storage's snapshot token at the
application's view `σt` (`runStor`, destructured once), whose snapshot is at `snapIndex`, at most
the applied index, which is now exactly the length of the committed log applied (`readyIdx`
bounds it below `2^64`). A `Ready` comes with or without a snapshot (`readyDataL_split`, the loan
`L`); the two meet after `if rd.Snapshot != nil` (`wp_join`) at the committed log applied `D0`
(the snapshot's prefix, or the log as before), the storage's token, and the right to append the
`Ready`'s entries with the receipt `Advance` takes (`advReceipt`):

* with a snapshot: its data certificate (`readyOut`'s certificate in the storage's registry, read
  through `memCertInv`) says that the data encodes the replicated state of a committed prefix as
  long as the snapshot's index, which is the loan's committed log (`isCommitted_agree`); its
  decoded maps (`decodeState`) are `runOwn`'s at that log (`maps_of_stateEnc`), which `install`
  puts in place, answering this replica's waiters among the snapshot's operations; the storage
  installs it (`ApplySnapshot`, newer than the application's snapshot: `snapIndex` is at most the
  applied index, below the snapshot's), then takes the entries after it (`memStorage_handout`,
  `memStorage_absorb`), the receipt `snapReceipt`;
* without one: as before (`appendRight`, `appendReceipt`).

After `Advance`, every `snapEvery` applied entries (never right after a snapshot `Ready`: it
applies nothing), the replica takes a snapshot of its state at the applied index: the floor's
witness (`reqWit`, `kvStorFloor_at`) bounds the index, the data is `encodeState`'s
(`stateEnc_intro`), the configuration the cluster's voters (`Storage.voters`, `raftSnapCert_static`),
both certificates registered at any term (`memCert_registerAny`); then `Compact`s to `snapMargin`
below it. `reconf` stays `false`: in the static mode no committed entry is a conf change.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.KV__run
public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.KV__apply
public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.KV__answer
public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.KV__install
public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.fits
public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.encodeState
public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.decodeState
public import Spec.go_etcd_io.raft.v3.node__Ready
public import Spec.go_etcd_io.raft.v3.node__Advance
public import Spec.go_etcd_io.raft.v3.MemoryStorage__Append
public import Spec.go_etcd_io.raft.v3.MemoryStorage__ApplySnapshot
public import Spec.go_etcd_io.raft.v3.MemoryStorage__CreateSnapshot
public import Spec.go_etcd_io.raft.v3.MemoryStorage__Compact
public import Proof.go_etcd_io.raft.v3.MemstorageAU
-- (2026-10-15, stage N) conf changes
public import Spec.go_etcd_io.raft.v3.node__ApplyConfChange
public import Spec.google_golang_org.protobuf.proto.UnmarshalConfChange
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetType
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetData
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

set_option maxHeartbeats 8000000 in
theorem KV.run.wp_proof
    (wp_fits : kv.fits.spec (GF := GF) (hG := hG))
    (wp_apply : kv.KV.apply.spec (GF := GF) (hG := hG))
    (wp_answer : kv.KV.answer.spec (GF := GF) (hG := hG))
    (wp_install : kv.KV.install.spec (GF := GF) (hG := hG))
    (wp_encodeState : kv.encodeState.spec (GF := GF) (hG := hG))
    (wp_decodeState : kv.decodeState.spec (GF := GF) (hG := hG))
    (wp_node_Ready : node.Ready.spec (GF := GF) (hG := hG))
    (wp_node_Advance : node.Advance.spec (GF := GF) (hG := hG))
    (wp_MemoryStorage_Append : MemoryStorage.Append.spec (GF := GF) (hG := hG))
    (wp_MemoryStorage_ApplySnapshot : MemoryStorage.ApplySnapshot.spec (GF := GF) (hG := hG))
    (wp_MemoryStorage_CreateSnapshot : MemoryStorage.CreateSnapshot.spec (GF := GF) (hG := hG))
    (wp_MemoryStorage_Compact : MemoryStorage.Compact.spec (GF := GF) (hG := hG))
    (wp_proto_UnmarshalConfChange : proto.UnmarshalConfChange.spec (GF := GF) (hG := hG))
    (wp_node_ApplyConfChange : node.ApplyConfChange.spec (GF := GF) (hG := hG))
    (wp_Entry_GetType : raftpb.Entry.GetType.spec (GF := GF) (hG := hG))
    (wp_Entry_GetData : raftpb.Entry.GetData.spec (GF := GF) (hG := hG)) :
    KV.run.spec (GF := GF) (hG := hG) := by
  -- (D22 J3) the storage's snapshot methods with the whole token in hand: the AU specs' corollaries
  replace wp_MemoryStorage_ApplySnapshot :=
    MemoryStorage.ApplySnapshot.spec_tok_of wp_MemoryStorage_ApplySnapshot
  replace wp_MemoryStorage_CreateSnapshot :=
    MemoryStorage.CreateSnapshot.spec_tok_of wp_MemoryStorage_CreateSnapshot
  replace wp_MemoryStorage_Compact := MemoryStorage.Compact.spec_tok_of wp_MemoryStorage_Compact
  intro γr γp r id n st send c0
  wp_start as ⟨#Hrep, %Hst, Hncfg, Hdrv, Hrun, Hstor, #Hsend⟩
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
  icases Hstor with ⟨%ms, %γs, %vsl, %vs, #Hrec, Htok, #Hci, #Hvf, #Hvs, %Hsf⟩
  obtain ⟨Hcap, Hvcfg, Hvnd, Hvne, Hvz, Hvlen, -⟩ := Hsf
  ihave #Hrec' := Hrec
  iunfold kvStorRec at Hrec'
  icases Hrec' with ⟨#Hmsf, -⟩
  have Hsok : γr.raft.reSnapOkRaw = kvSnapOk := by rw [← Hraft]; exact Hst.2.2.2.2.1
  have Hdyn : γr.raft.reDyn = none := by rw [← Hraft]; exact Hst.2.2.2.2.2.1
  have Htrk : γr.raft.reTracked = none := by rw [← Hraft]; exact Hst.2.2.2.2.2.2
  wp_auto
  wp_apply wp_node_Ready γp.node id n $$ [$HisNode] as %ch #Hch
  ihave IH : iprop(∃ (ds : List EntryM) (rdv : Ready) (pv : GoSlice) (ps : List ReadState)
      (a : w64) (p : HardStateM) (sI : w64) (σt : StorState),
      "Hrd" ∷ rd_ptr ↦ rdv ∗ "Hdrv" ∷ nodeDriver γp.node id n ds p ∗ "Hrun" ∷ runOwn γr r ds ∗
      "pending" ∷ pending_ptr ↦ pv ∗ "Hpv" ∷ pv ↦* ps ∗
      "Hpcap" ∷ ownSliceCap ReadState pv (DFrac.own 1) ∗
      "Hps" ∷ ([∗list] v ∈ ps, rsOk γr.raft v) ∗
      "applied" ∷ applied_ptr ↦ a ∗ "snapIndex" ∷ snapIndex_ptr ↦ sI ∗
      "reconf" ∷ reconf_ptr ↦ false ∗ "Htok" ∷ memSnapTok ms γs σt ∗
      "%Ha" ∷ ⌜uint.Z a = (ds.length : Int) ∧ σt.ss.index' = sI ∧ uint.Z sI ≤ uint.Z a ∧
        uint.Z σt.prev.index' ≤ uint.Z σt.ss.index'⌝ ∗
      "Hncfg" ∷ nodeCfg γp.node 0 c0)
    $$ [rd Hdrv Hrun pending applied snapIndex reconf Htok Hncfg]
  · iexists [], _, _, [], _, hsZero, _, memStorEmpty
    iframe
    isplitl []
    · iapply ownSlice_nil
    isplitl []
    · iapply ownSliceCap_nil
    isplitl []
    · iapply (BigSepL.bigSepL_nil).2; iempintro
    ipureintro
    refine ⟨rfl, rfl, Int.le_refl _, Int.le_refl _⟩
  wp_for IH
  try wp_auto
  wp_apply node_ready_receive γp.node id n ch ds p $$ [$Hch $Hdrv]
    as %rdv' ⟨%ce, %es, %msgs, %p', %L, Hdata, Hbusy⟩
  ihave ⟨Hcom, HS⟩ := readyDataL_split γp.node rdv' ds ce es msgs p p' L $$ Hdata
  unfold rdCommon
  icases Hcom with ⟨#Hce, #Hcomm, #Hes, Hms, Hmsok, Hcr, Htks, ⟨%sts, #Hsts, #Hstsok⟩, #Hidx⟩
  unfold readyIdx
  icases Hidx with ⟨%Lr, -, %HLr⟩
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
  wp_join iprop(∃ (D0 : List EntryM) (a0 sI0 : w64) (σt0 σA : StorState),
      "Hrd" ∷ rd_ptr ↦ rdv' ∗ "r" ∷ r_ptr ↦ r ∗ "Hrun" ∷ runOwn γr r D0 ∗
      "applied" ∷ applied_ptr ↦ a0 ∗ "snapIndex" ∷ snapIndex_ptr ↦ sI0 ∗
      "Htok" ∷ memSnapTok ms γs σt0 ∗
      "%Ha0" ∷ ⌜uint.Z a0 = (D0.length : Int) ∧ σt0.ss.index' = sI0 ∧ uint.Z sI0 ≤ uint.Z a0 ∧
        uint.Z σt0.prev.index' ≤ uint.Z σt0.ss.index' ∧ D0 ++ ce = dlvAfter ds ce L ∧
        (L.isSome → ce = [] ∧ a0 = sI0) ∧ ((D0 ++ ce).length : Int) < 2 ^ 64⌝ ∗
      "#Hcomm0" ∷ isCommitted γr.raft (D0 ++ ce) ∗
      "Happ" ∷ (⌜es = []⌝ ∨ memAppendTok ms γs σA es) ∗
      "Hrb" ∷ ((⌜es = []⌝ ∨ memAppendedTok ms γs σA es) -∗ |==> advReceipt γp.node.stor es L))
    at (If _ _ _) with [Hrd r Hrun applied snapIndex Htok HS]
    as ⟨%D0, %a0, %sI0, %σt0, %σA, Hrd, r, Hrun, applied, snapIndex, Htok, %Ha0, #Hcomm0, Happ, Hrb⟩
  · cases L with
    | none =>
      -- no snapshot: the right to append, as before
      simp only [rdSnap]
      icases HS with ⟨Happ, %Hsn⟩
      rw [Hsn]
      wp_auto
      wp_join_done
      ihave Happ : iprop(∃ σ, ⌜es = []⌝ ∨ memAppendTok ms γs σ es) $$ [Happ]
      · unfold appendRight
        rw [Hstor]
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
      iexists ds, a, sI, σt, σ
      iframe Hrd r Hrun applied snapIndex Htok Happ
      isplitr
      · ipureintro
        refine ⟨Ha.1, Ha.2.1, Ha.2.2.1, Ha.2.2.2, rfl, (fun h => by cases h), ?_⟩
        omega
      isplitr
      · rw [← Hraft]; iexact Hcomm
      iintro Hdone
      imodintro
      simp only [advReceipt]
      unfold appendReceipt
      rw [Hstor]
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
      simp only [rdSnap]
      icases HS with ⟨Hsn, #Hdl, %Hl, Hout⟩
      obtain ⟨Hptr, Hce0, Hpre, Hlen, Hdlv, Hi0, Hi61, Hfl, Hlio⟩ := Hl
      subst Hce0
      unfold readyOut
      icases Hout with ⟨⟨%σ, Hown, %Hσ⟩, #Hcert⟩
      ihave Hms : ownMemoryStorage ms γs σ $$ [Hown]
      · iapply kvOwnStorage_at st ms γs σ $$ Hrec
        rw [← Hstor]; iexact Hown
      -- its data certificate: the data encodes the replicated state of the loan's committed log
      ihave #Hmc : memStorCert γs (snapTrip l.snap l.snap.Metadata'.ConfState'.lists) $$ []
      · iapply kvStorCert_at st ms γs _ $$ Hrec
        rw [← Hstor]; iexact Hcert
      imod memCert_read γr.raft γs _ ⊤ CoPset.subseteq_top $$ Hci Hmc with #Hrc
      unfold raftSnapCertD snapDataOk
      icases Hrc with ⟨-, %L', #HcL', %HL'⟩
      ihave #Hdl' : isCommitted γr.raft l.dlv $$ []
      · rw [← Hraft]; iexact Hdl
      ihave %Hag := isCommitted_agree γr.raft L' l.dlv $$ HcL' Hdl'
      have HLeq : L' = l.dlv := by
        have hl : L'.length = l.dlv.length := by
          rw [HL'.1, Hdlv]; rfl
        rcases Hag with h | h
        · exact h.eq_of_length hl
        · exact (h.eq_of_length hl.symm).symm
      subst HLeq
      have HSE : StateEnc (firstOcc (l.dlv.map odOf)) l.snap.Data' := by
        have h := HL'.2
        unfold RaftNames.reSnapOk at h
        rw [Hsok] at h
        exact (kvSnapOk_entries l.dlv _).1 h
      obtain ⟨kvs, ops, HdEq, HKw, HOw, Hk, Ho⟩ := HSE
      -- the entries' data facts: the client history `firstOcc (l.dlv.map odOf)`
      imod node_committed_data γp.node id n l.dlv ⊤ CoPset.subseteq_top $$ HisNode Hdl
        with ⟨%odsn, #Hodsn⟩
      ihave %Hods_eq := entsDataIs_odOf γp.node.raft l.dlv odsn $$ Hodsn
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
      rw [← Hods_eq] at HvalS HAS
      ihave #Hodsn' : iprop([∗list] e;o ∈ l.dlv;odsn, entDataIs γr.raft e o) $$ []
      · rw [← Hraft]; iexact Hodsn
      wp_apply wp_install γr γp r id n st ds l.dlv odsn mK' mA' K' A' HvalS HAS
        $$ [$Hpkg $Hrep $Hrun $HK' $HA' $Hdl' $Hodsn'] as Hrun
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
        have h1 : (ds.length : Int) < l.dlv.length := by exact_mod_cast Hlen
        have h2 : (l.dlv.length : Int) = uint.Z l.snap.Metadata'.Index' := by
          rw [Hdlv]; exact Int.toNat_of_nonneg (by word)
        have h3 := Hbad.2.1
        rw [Ha.2.1] at h3
        omega
      -- the entries after the snapshot: handed to the storage
      have Hσ' : ({ memStorApplied l.snap with fl := σ.fl } : StorState).prev = snapId l.snap := rfl
      have Hidx : (l.dlv.length : Int) = uint.Z l.snap.Metadata'.Index' := by
        rw [Hdlv]; exact Int.toNat_of_nonneg (by word)
      by_cases Hes0 : es = []
      · try wp_auto
        wp_join_done
        iexists l.dlv, l.snap.Metadata'.Index', l.snap.Metadata'.Index', memStorApplied l.snap,
          { memStorApplied l.snap with fl := σ.fl }
        iframe Hrd r Hrun applied snapIndex Htok
        isplitr
        · ipureintro
          refine ⟨Hidx.symm, rfl, Int.le_refl _, Int.le_refl _, by simp [dlvAfter], fun _ => ⟨rfl, rfl⟩, ?_⟩
          simp only [List.append_nil]; omega
        isplitr
        · simp only [List.append_nil]; iexact Hdl'
        isplitr
        · ileft; ipureintro; exact Hes0
        iintro -
        imodintro
        simp only [advReceipt, snapReceipt]
        iframe Hsn
        iexists { memStorApplied l.snap with fl := σ.fl }
        isplitl
        · rw [Hstor]; iapply kvOwnStorage_intro st ms γs _ $$ Hrec Hms
        ipureintro
        exact ⟨rfl, rfl, Hes0.symm, rfl, Hσ.2, rfl, rfl, rfl⟩
      imod memStorage_handout ms γs { memStorApplied l.snap with fl := σ.fl } es
          ⟨rfl, pendOk_of_logIndices _ es Hes0 rfl Hlio,
            pendAbove_of_logIndices _ es (by rw [Hσ.2]; exact Hfl) Hlio⟩ $$ Hms
        with ⟨Hms, Happ⟩
      try wp_auto
      wp_join_done
      iexists l.dlv, l.snap.Metadata'.Index', l.snap.Metadata'.Index', memStorApplied l.snap,
        { memStorApplied l.snap with fl := σ.fl }
      iframe Hrd r Hrun applied snapIndex Htok
      isplitr
      · ipureintro
        refine ⟨Hidx.symm, rfl, Int.le_refl _, Int.le_refl _, by simp [dlvAfter], fun _ => ⟨rfl, rfl⟩, ?_⟩
        simp only [List.append_nil]; omega
      isplitr
      · simp only [List.append_nil]; iexact Hdl'
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
      · rw [Hstor]; iapply kvOwnStorage_intro st ms γs _ $$ Hrec Hms
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
  iapply Hsend $$ [Hms Hmsok Hcr Htks]
  · iframe
  iintro !> -
  try wp_auto
  -- the read states, noted (`rsOk` of each value)
  ihave Hvs := readStatesPts_rsOk γp.node.raft rdv'.ReadStates' sts $$ [Hsts Hstsok]
  · iframe Hsts Hstsok
  icases Hvs with ⟨%vls, #Hvls, #Hvlsok⟩
  wp_apply wp_slice_append $$ [$Hpv $Hpcap $Hvls] as %pv' ⟨Hpv, Hpcap, -⟩
  ihave Hps : iprop([∗list] v ∈ ps ++ vls, rsOk γr.raft v) $$ [Hps]
  · iapply (BigSepL.bigSepL_append (Φ := fun _ v => rsOk (GF := GF) γr.raft v)).2
    iframe Hps
    rw [← Hraft]
    iexact Hvlsok
  -- applying the committed entries, in order
  icases entsPts_elim _ _ _ $$ Hce with ⟨%cls, #Hce, #Hceb⟩
  ihave %Hcelen := ownSlice_len $$ Hce
  ihave %Hcebl := entsBig_length $$ Hceb
  have Hbig := Ha0.2.2.2.2.2.2
  ihave IHa : iprop(∃ (k : w64) (ev : Loc) (a' : w64),
      "i" ∷ i_ptr ↦ k ∗ "e" ∷ e_ptr ↦ ev ∗ "Hrun" ∷ runOwn γr r (D0 ++ ce.take (sint.nat k)) ∗
      "applied" ∷ applied_ptr ↦ a' ∗
      "%Ha" ∷ ⌜uint.Z a' = ((D0 ++ ce.take (sint.nat k)).length : Int)⌝ ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ (ce.length : Int)⌝)
    $$ [i e Hrun applied]
  · iexists W64 0, _, a0
    iframe i e applied
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
    ihave ⟨%ln, %Hln, #Hent⟩ := entsBig_lookup cls ce (sint.nat k) en Hen $$ Hceb
    have Hbnd' : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z rdv'.CommittedEntries'.len := ⟨Hk.1, by word⟩
    simp only [Hbnd', _root_.and_self]
    wp_apply wp_load_slice_index rdv'.CommittedEntries' (sint.Z k) _ DFrac.discard ln Hk.1 $$ [Hce] as -
    · iframe Hce; ipureintro; exact Hln
    have Htk : ce.take (sint.nat k + 1) = ce.take (sint.nat k) ++ [en] := by
      rw [List.take_add_one, Hen]; rfl
    ihave #Hc1 := isCommitted_mono γr.raft (D0 ++ ce.take (sint.nat k) ++ [en]) (D0 ++ ce)
      (by rw [List.append_assoc, ← Htk]; exact List.prefix_append_right_inj _ |>.mpr (List.take_prefix _ _))
      $$ Hcomm0
    -- the entry's data: in the static mode a normal entry's, no conf change
    imod node_entry_data γp.node id n (D0 ++ ce.take (sint.nat k)) en ⊤ CoPset.subseteq_top
      $$ HisNode [Hc1] with ⟨%o, #Ho⟩
    · rw [Hraft]; iexact Hc1
    ihave %Hty0 := kvStat_type0 γp.node Hst en o $$ Ho
    -- `if e.GetType() == pb.EntryConfChange { ... }`: not taken
    wp_apply wp_Entry_GetType.1 ln DFrac.discard en $$ [$Hpbinit $Hent] as -
    rw [decide_eq_false (show ¬ en.Type' = W32 1 by rw [Hty0]; intro h; revert h; word)]
    try wp_auto
    wp_apply wp_apply γr γp r id n st (D0 ++ ce.take (sint.nat k)) ln en
      $$ [$Hpkg $Hrep $Hrun $Hent $Hc1] as Hrun
    wp_for_post
    iframe
    iexists k + W64 1, ln, a' + W64 1
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
    have Hnd : γp.node.mode.isDyn = true → NoConfIn (dlvAfter ds ce L) 0 (dlvAfter ds ce L).length := by
      intro h; rw [Hst.1] at h; cases h
    wp_apply wp_node_Advance γp.node id n (dlvAfter ds ce L) es 0 c0 p' L Hnd
      $$ [$Hraftinit $Hbusy $Hrcpt $Hncfg] as ⟨Hdrv, Hncfg, #Hreq⟩
    rw [← Ha0.2.2.2.2.1]
    try wp_auto
    -- (D22 S-r) `if !reconf && applied-snapIndex >= snapEvery`: a snapshot
    have Hsa : uint.Z sI0 ≤ uint.Z a' := by
      have : ((D0 ++ ce).length : Int) ≥ D0.length := by simp; omega
      have := Ha0.1; have := Ha0.2.2.1; omega
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
      simp only [reqWit, reqOf]
      icases Hreq with ⟨%x, #Hfx, %Hx⟩
      ihave ⟨#Hmf, %Hx61⟩ := kvStorFloor_at st ms γs x $$ Hrec [Hfx]
      · rw [← Hstor]; iexact Hfx
      have Ha'x : uint.Z a' ≤ uint.Z x := by rw [Ha]; exact Hx
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
          (kvConfState vs) ⊤ rfl $$ [«$a1»] with #Hcs
      · iframe «$a1»
        simp only [kvConfState]
        iframe Hvs
        repeat (isplitr; · iapply ownSlice_nil)
        iunfold cellRO; ileft; ipureintro; exact ⟨rfl, rfl⟩
      try wp_auto
      -- the snapshot's certificates: the cluster's voters, and the data of the applied log
      ihave %Hods_eq := entsDataIs_odOf γr.raft (D0 ++ ce) ods $$ Hods
      have HSE : StateEnc (firstOcc ods) (encState kvs ops) :=
        stateEnc_intro _ K A kvs ops Hval HA Hko.1 Hko.2
      have Ha61 : uint.Z a' < 2 ^ 61 := by omega
      ihave #Hsd : snapDataOk γr.raft a' (encState kvs ops) $$ []
      · unfold snapDataOk
        iexists D0 ++ ce
        iframe Hap
        ipureintro
        refine ⟨len_eq_unat a' _ Ha, ?_⟩
        · unfold RaftNames.reSnapOk
          rw [Hsok, kvSnapOk_entries, ← Hods_eq]
          exact HSE
      ihave #Hrc : iprop(□ ∀ t : w64, raftSnapCertD γr.raft
          ⟨⟨t, a'⟩, (kvConfState vs).lists, false, encState kvs ops⟩) $$ []
      · imodintro
        iintro %t
        unfold raftSnapCertD
        isplitr
        · iapply raftSnapCert_static γr.raft _ (RaftNames.dyn_none Hdyn)
            (snapListsOk_voters vs t a' _ Hvne Hvz Hvnd Hvlen Ha61)
          intro _
          refine ⟨by simp [kvConfState, ConfStateM.lists]; exact Hvcfg, rfl, ?_⟩
          intro T hT; rw [Htrk] at hT; cases hT
        · iexact Hsd
      imod memCert_registerAny γr.raft γs a' _ false _ ⊤ CoPset.subseteq_top $$ Hci Hrc with #Hmc
      -- `r.storage.CreateSnapshot(applied, cs, data)`: newer than the application's snapshot
      wp_method_call
      try wp_auto
      have Hlt : uint.Z sI0 < uint.Z a' := by
        rw [Hsub] at Hge
        have : uint.Z (W64 100) = 100 := by decide
        omega
      wp_apply wp_MemoryStorage_CreateSnapshot ms γs σt0 x a' «$a1_ptr» DFrac.discard (some (kvConfState vs))
          dsl (encState kvs ops) eood
          (fun _ => ⟨by have := Ha0.2.2.2.1; rw [Ha0.2.1] at this; omega, Ha'x⟩)
        $$ [$Hraftinit $Htok $Hmf Hcs $Hdsl $Heood] as %snap' %err ⟨-, Hres⟩
      · isplitl
        · simp only
          iapply csPts_weaken; iexact Hcs
        imodintro
        iintro %t
        have Heq : snapTrip (memSnapCreated σt0 a' t (some (kvConfState vs)) (encState kvs ops))
            (memSnapCreated σt0 a' t (some (kvConfState vs)) (encState kvs ops)).Metadata'.ConfState'.lists =
            ⟨⟨t, a'⟩, (kvConfState vs).lists, false, encState kvs ops⟩ := rfl
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
      iexists D0 ++ ce, rdv', rest, ps', a', p', a', σt2
      iframe Hdrv
      ihave Hrun : runOwn γr r (D0 ++ ce) $$ [HmK HK HmA HA]
      · unfold runOwn
        iexists mK, K, mA, A, ods
        iframe HmK HK HmA HA Hap Hods
        ipureintro; exact ⟨Hval, HA⟩
      iframe
      ipureintro
      exact ⟨Ha, Hσt2.1, Int.le_refl _, Hσt2.2⟩
    · -- no snapshot taken
      wp_for_post
      iframe
      iexists D0 ++ ce, rdv', rest, ps', a', p', sI0, σt0
      iframe
      ipureintro
      exact ⟨Ha, Ha0.2.1, Hsa, Ha0.2.2.2.1⟩

end proof

end kv
end EtcdGrove
end Perennial

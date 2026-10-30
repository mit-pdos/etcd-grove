/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kv/KV__run.lean`. Lean-first (no
Rocq counterpart).

**2026-10-30 (stage P of the client repair, over raft's new API).** The loop keeps `kvRunInv`
(`KvRunInv.lean`): the node's driver at the delivered log `D`, `nodeRunning … 1` (refuting
`Advance`'s stopped answer), `runOwn` and the node's view `appNode` at `D` (at the voters'
membership), `applied` at `|D|`, a compaction point `c ≤ snapIndex ≤ applied` with `D` frozen above
it (`frozenTo`), `reconf` unset. The store's committed logs hold no conf entry (`kv_noConf`,
`KvRunSnap.lean`: a committed conf entry is raft's empty `ConfChangeV2`, which no position of the
voters' membership holds), so the `ApplyConfChange` branch is refuted and every position keeps
`kvMembership`. A `Ready` without a snapshot: its entries appended with its committed ones frozen
(`append_none_pre`/`append_none_post`, `KvRunFrozen.lean`), its committed entries applied, the
reads answered, `Advance` (the view's `skippedIn` by `skippedIn_noConf`); then, every `snapEvery`
entries, a snapshot at the applied index (`kv_snap_make`'s validity, the frozen entry there,
`storDL` from the delivered log, `memSnapLb γs 0`) and a compaction below it (the frozen entry or
the compaction point, `nodeAppliedLb` from `Advance`, `memSnapLb` from `CreateSnapshot`). A snapshot
`Ready`: its data the state of its committed log (`kv_snap_read`), installed (`decodeState`,
`install`), the storage takes it (`ApplySnapshot`, justified by `snapshotCert_valid`, `snapGiven`
and the delivered log), the entries after it appended (`snapAppend_pre`/`snapAppend_post`), and
`Advance` (`kv_snapReceipt`, the certificate) puts the view at the snapshot's index, at the voters'
membership (`confAt_agree` against `kv_noConf`'s); no snapshot is taken after it (it applied
nothing). The text below describes the proof before the repair. raft v3.7 (2026-10-16, stage R6b): a `Ready`'s entries and committed entries
are read-only entry pointers (`entsRO`), its messages owned pointers (`sendSpec`), its read
states Go values whose contexts hold their bytes (`readStatesPts_rsOk`), its hard state `hsOpt`
(unused: the store persists no hard state); a conf-change entry is decoded with
`proto.Unmarshal` into a fresh `pb.ConfChange`, applied by pointer (`ownConfChange_persist`:
`node.ApplyConfChange` reads it on raft's goroutine).

**Raft's node API (2026-10-27).** A `Ready` comes through `node.readyRecv`: its committed
entries (`committedEntriesAt`), its read states, the rest (`readyRest`): the entries to
persist, the messages, and the snapshot part (`readySnap`), in the storage contract's
vocabulary; and the loop's new state, by the snapshot's loan. A committed conf-change entry (type
`1`) is a requested one, so `RemoveMember`'s (`kv_committed_cc`, `RmReqs`): its bytes decode to
`rmCC id`, a change keeping the voters (`RmShrink id`); `reconf` is set. No committed entry is of
type `2` (`kv_committed_conf`).

**Raft's cluster with snapshots and reconfiguration (2026-10-28, stage U4a).** The loop holds the
node's view of its configuration (`nodeConfig`) at the voters' membership `kvMembership`, past the
conf entries applied (`confAt` beside it), none after it in the committed log delivered
(`NoConfChangeIn`), and none at all unless `reconf` is set. A conf entry is decided by the store's
rule (`confPolicy_decide`, `kvRule_decide`): its change applied, which keeps `kvMembership`
(`kvMembership_rm`), and `node.ApplyConfChange.unifiedSpec` moves the view past it. `Advance`
(`node.Advance.unifiedSpec`) takes the view (every conf entry delivered applied) and, after a
snapshot `Ready`, its certificate, and puts the view at the snapshot's index (its membership the
voters', `confAt_agree`).

**Snapshots (D22 S-r, 2026-10-21).** The loop holds the storage's snapshot token at the
application's view `σt` (`runStor`, destructured once), whose snapshot is at `snapIndex`, at most
the applied index, which is exactly the length of the committed log applied (the `Ready`'s indices'
bound keeps it below `2^64`). A `Ready` comes with or without a snapshot (the loan `L`); the two meet
after `if rd.Snapshot != nil` (`wp_join`) at the committed log applied `D0`, the storage's token,
and the right to append the `Ready`'s entries with the receipt `Advance` takes (`advReceipt`):

* with a snapshot: its certificate's snapshot is one the store made (`kv_snap_read`, the store's
  registry `kvSnapInv`): the data encodes the
  replicated state of a committed log as long as the snapshot's index, with no conf entry, which
  is the one the
  `Ready` hands out (`isCommittedLogLb_agree`); its decoded maps (`decodeState`) are
  `runOwn`'s at that log (`maps_of_stateEnc`), which `install` puts in place, answering this
  replica's waiters among the snapshot's operations; the storage installs it (`ApplySnapshot`, its
  registry's certificate from `readyOut`), then takes the entries after it (`memStorage_handout`,
  `memStorage_absorb`), the receipt `snapReceipt`;
* without one: as before (`appendRight`, `appendReceipt`).

After `Advance`, every `snapEvery` applied entries (never right after a snapshot `Ready`: it
applies nothing), the replica takes a snapshot of its state at the applied index: the floor's
witness (`Advance`'s, `kvStorFloor_at`) bounds the index, the data is `encodeState`'s
(`stateEnc_intro`), the configuration the cluster's voters (`Storage.voters`), the term the applied
log's last entry's, which the storage has there (`Advance`'s `storTermsAt`, `kvStorTerms_at`); it
is certified at the voters' membership (`kv_snap_make`: `snapshotCert_make`, recorded in the
store's registry) and registered at that term (`storageCert_register`), and
`MemoryStorage.CreateSnapshot.unifiedSpec` takes it (`CreateSnapshot.unifiedSpec_tok_of`); then
`Compact`s to `snapMargin` below it -- unless `reconf` is set (a conf entry applied: the snapshot's
prefix would hold one).
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
public import Spec.go_etcd_io.raft.v3.node__Ready
public import Spec.go_etcd_io.raft.v3.node__Advance
public import Spec.go_etcd_io.raft.v3.node__ApplyConfChange
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetType
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetData
public import Spec.google_golang_org.protobuf.proto.UnmarshalConfChange
public import Proof.github_com.mit_pdos.etcd_grove.examples.kv.Lemmas
public import Proof.github_com.mit_pdos.etcd_grove.examples.kv.KVStorageInstance
public import Proof.github_com.mit_pdos.etcd_grove.examples.kv.SnapData
public import Proof.github_com.mit_pdos.etcd_grove.examples.kv.Reconf
public import Proof.github_com.mit_pdos.etcd_grove.examples.kv.KvRunInv

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
theorem toEntries_get (ce : List LogEntry) (base k : Nat) (en : LogEntry)
    (h : ce[k]? = some en) :
    (LogEntry.toEntries ce base)[k]? = some (en.toEntryM (W64 (base + k + 1))) := by
  unfold LogEntry.toEntries; rw [List.getElem?_mapIdx, h]; rfl

theorem toEntries_length (ce : List LogEntry) (base : Nat) :
    (LogEntry.toEntries ce base).length = ce.length := by
  unfold LogEntry.toEntries; simp

set_option hygiene false in
/-- `run`'s loop invariant after a snapshot at the applied index. -/
local macro "kv_snap_post" : tactic => `(tactic| (
    try wp_auto
    wp_for_post
    iframe
    unfold kvRunInv
    iexists D ++ ce, phsNext hd hh, rdv', rest, ps', a', a', c
    iframe
    iframe Hps2 Hcp Hfz'
    isplitl [HmK HK HmA HA]
    · unfold runOwn
      iexists mK, K, mA, A, ods
      iframe HmK HK HmA HA Hap
      ipureintro; exact ⟨Hods, Hval, HA⟩
    ipureintro
    exact ⟨Ha', by omega, Nat.le_refl _⟩
  ))

set_option maxHeartbeats 8000000 in
set_option linter.unusedVariables false in
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
  intro γr γp r id n st send
  wp_start as ⟨#Hrep, Hdrv, Hcfg, Hrun, Hown, #Hstor, #Hsend⟩
  ihave #Hrep' := Hrep
  iunfold isReplica at Hrep'
  iNamed Hrep'
  ihave #Hcl' := Hcl
  iunfold kvCluster at Hcl'
  icases Hcl' with ⟨#Hiscl, -, #Hca0, -⟩
  ihave #Hraftinit : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  ihave #Hpbinit : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  ihave #Hinit := isInitialized_access $$ Hraftinit
  iunfold isInitialized at Hinit
  iNamed Hinit
  icases ErrSnapOOD with ⟨%eood, #Heood⟩
  unfold runStor
  icases Hstor with ⟨%ms, %γs, %vsl, #Hrec, #HmsInv, #HsnLb, #Hvf, #Hvs⟩
  ihave #HmsInv' := HmsInv
  iunfold memStorInvP at HmsInv'
  icases HmsInv' with ⟨#Hlock, -, -⟩
  wp_auto
  wp_apply wp_node_Ready γr.cluster kvRaftN id n $$ [$Hraftinit $HisNode] as %ch #Hch
  ihave IH : kvRunInv γr r n st γs rd_ptr pending_ptr applied_ptr snapIndex_ptr reconf_ptr
    $$ [rd Hdrv Hcfg Hrun Hown pending applied snapIndex reconf]
  · unfold kvRunInv
    ihave ⟨Hdrv, #Hdl⟩ := nodeDriver_deliveredLogLb _ _ _ _ $$ Hdrv
    iexists [], hsZero, zero_val Ready, zero_val GoSlice, [], zero_val w64, zero_val w64, 0
    unfold NodeDriverState.init
    iframe Hdrv Hrun Hown rd pending applied snapIndex reconf
    isplitl [Hcfg]
    · unfold appNode
      iexists ⟨0, kvMembership⟩
      iframe Hcfg Hdl
      isplitl []
      · iapply skippedIn_noConf γr.cluster [] 0 0 (fun _ _ _ h _ => absurd h (Nat.not_lt_zero _))
      ipureintro; exact ⟨rfl, Nat.le_refl _⟩
    isplitl []
    · iapply ownSlice_nil
    isplitl []
    · iapply ownSliceCap_nil
    isplitl []
    · iapply BigSepL.bigSepL_nil.2; itrivial
    isplitl []
    · iapply memCompacted_zero
    isplitl []
    · unfold frozenTo LogEntry.toEntries; simp only [List.mapIdx_nil, List.drop_nil]
      iapply memLog_nil
    ipureintro; exact ⟨rfl, Nat.zero_le _, Nat.le_refl _⟩
  wp_for IH
  try wp_auto
  wp_apply node.wp_readyRecv n ch γr.cluster kvRaftN id _ rfl $$ [$Hch $HisNode $Hdrv]
    as %rdv' ⟨%ce, %es, %hh, %L, #Hce, #Hcomm, ⟨%sts, #Hsts, #Hstsok⟩, Hrest, Hdrv⟩
  ihave ⟨%Hidx, Hrest⟩ := readyRest_indices _ _ _ _ _ _ _ _ _ $$ Hrest
  unfold readyRest
  icases Hrest with ⟨%msgs, #Hes, Hms, Hmsok, -, -, %Hbnd, HS⟩
  try wp_auto
  wp_apply wp_fits rdv'.Entries' es DFrac.discard $$ [$Hpkg $Hes] as %b ⟨-, %Hfit⟩
  cases b
  · -- a log past `maxIndex`: the replica stops
    wp_auto
    ihave Hspin : iprop(True) $$ []
    · itrivial
    wp_for Hspin
    wp_for_post
    iframe
  have Hfit' := Hfit rfl
  simp only at Hbnd
  obtain ⟨Lx, HLx, -, HLxd, -⟩ := Hbnd
  -- the store's committed log delivered holds no conf entry: the voters' membership throughout
  imod kv_noConf γr (D ++ ce) ⊤ CoPset.subseteq_top $$ Hinv Hcl Hcomm with ⟨%Hnc, #HcaF⟩
  cases L with
  | none =>
    ihave Hdrv : iprop(nodeDriver n γr.cluster kvRaftN ⟨kvStorIface st, D ++ ce, phsNext hd hh,
        some (es, none)⟩) $$ [Hdrv]
    · iexact Hdrv
    ihave ⟨Hdrv, #Hdl⟩ := nodeDriver_deliveredLogLb _ _ _ _ $$ Hdrv
    iunfold readySnap at HS
    icases HS with ⟨%Hnull, Happ, #Hcef, %Hin⟩
    try wp_auto
    wp_if_destruct
    rotate_left
    · exfalso; simp_all
    try wp_auto
    have HcD : c ≤ D.length := by have := Ha.2.1; have := Ha.2.2; omega
    -- `r.storage.Append(rd.Entries)`, with the `Ready`'s committed entries frozen
    icases append_none_pre st ms γs es $$ Hrec Happ with ⟨%k, %old, ⟨%Hk, %Hk0⟩, Hrange⟩
    have h1 : ∀ (j : Nat) (e : EntryM), es[j]? = some e → uint.nat e.Index' = k + j := by
      intro j e hj
      cases hes : es with
      | nil => rw [hes] at hj; cases hj
      | cons e0 rest =>
        rw [Hk e0 (by rw [hes]; rfl)]
        exact Hidx e0 (by rw [hes]; rfl) j e hj
    have h2 : k + es.length ≤ 2 ^ 61 := by
      cases hes : es with
      | nil => rw [Hk0 hes]; simp
      | cons e0 rest =>
        have := Hfit' e0 (by rw [hes]; rfl)
        rw [Hk e0 (by rw [hes]; rfl)]
        rw [hes] at this
        word
    wp_apply kvStorage.wp_Append wp_MemoryStorage_Append st ms γs k old es rdv'.Entries' DFrac.discard
        h1 h2 $$ [$Hrec $Hraftinit $Hlock $Hrange $Hes] as ⟨-, Hb⟩
    imod append_none_post st ms γs c D ce es k HcD (fun e0 h0 => (Hin e0 h0).2) Hidx Hk
      $$ Hrec Hfz Hcef Hb with ⟨#Hfz', Hrcpt⟩
    -- `send(rd.Messages)`
    try wp_auto
    wp_bind (App (Val #send) _)
    iunfold sendSpec at Hsend
    iapply Hsend $$ [Hms Hmsok]
    · iframe
    iintro !> -
    try wp_auto
    -- the read states, noted
    ihave Hvs := readStatesPts_rsOk γr.cluster rdv'.ReadStates' sts $$ [Hsts Hstsok]
    · iframe Hsts Hstsok
    icases Hvs with ⟨%vls, #Hvls, #Hvlsok⟩
    wp_apply wp_slice_append $$ [$Hpv $Hpcap $Hvls] as %pv' ⟨Hpv, Hpcap, -⟩
    ihave #Hps' : iprop([∗list] v ∈ ps ++ vls, rsOk γr.cluster v) $$ []
    · iapply (BigSepL.bigSepL_append (Φ := fun _ v => rsOk (GF := GF) γr.cluster v)).2
      iframe Hps Hvlsok
    iclear Hps
    -- applying the committed entries, in order
    iunfold committedEntriesAt at Hce
    icases entsPts_elim _ _ _ $$ Hce with ⟨%cls, #Hcel, #Hceb⟩
    ihave %Hcelen := ownSlice_len $$ Hcel
    ihave %Hcebl := entsBig_length $$ Hceb
    rw [toEntries_length] at Hcebl
    ihave IHa : iprop(∃ (k : w64) (ev : Loc) (a' : w64),
        "i" ∷ i_ptr ↦ k ∗ "e" ∷ e_ptr ↦ ev ∗ "Hown" ∷ runOwn γr r (D ++ ce.take (sint.nat k)) ∗
        "applied" ∷ applied_ptr ↦ a' ∗
        "%Ha'" ∷ ⌜uint.nat a' = (D ++ ce.take (sint.nat k)).length⌝ ∗
        "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ (ce.length : Int)⌝)
      $$ [i e Hown applied]
    · iexists W64 0, _, a
      simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.append_nil]
      iframe
      ipureintro
      exact ⟨Ha.1, by word, by word⟩
    wp_for IHa
    wp_if_destruct
    · have HifK := Hif
      have Hlt : sint.nat k < ce.length := run_lt k _ _ _ Hif Hcelen.1 Hcebl Hk.1
      obtain ⟨en, Hen⟩ : ∃ en, ce[sint.nat k]? = some en := ⟨_, List.getElem?_eq_getElem Hlt⟩
      ihave ⟨%ln, %Hln, #Hent⟩ := entsBig_lookup cls _ (sint.nat k) _
        (toEntries_get ce D.length (sint.nat k) en Hen) $$ Hceb
      simp only [show 0 ≤ sint.Z k ∧ sint.Z k < sint.Z rdv'.CommittedEntries'.len from ⟨Hk.1, Hif⟩,
        _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index rdv'.CommittedEntries' (sint.Z k) _ DFrac.discard ln Hk.1
        $$ [Hcel] as -
      · iframe Hcel; ipureintro; rw [show (sint.Z k).toNat = sint.nat k by word]; exact Hln
      have Htk : ce.take (sint.nat k + 1) = ce.take (sint.nat k) ++ [en] := by
        rw [List.take_add_one, Hen]; rfl
      have Hplen : (D ++ ce.take (sint.nat k)).length = D.length + sint.nat k := by
        rw [List.length_append, List.length_take_of_le (by omega)]
      have Hget : (D ++ ce)[D.length + sint.nat k]? = some en := by
        rw [List.getElem?_append_right (by omega)]
        simpa using Hen
      ihave #Hc1 := isCommittedLogLb_mono γr.cluster (D ++ ce.take (sint.nat k) ++ [en]) (D ++ ce)
        (by rw [List.append_assoc, ← Htk]
            exact List.prefix_append_right_inj _ |>.mpr (List.take_prefix _ _))
        $$ Hcomm
      -- `if e.GetType() == pb.EntryConfChange`: never (the store's log has no conf entry)
      try wp_auto
      wp_apply wp_Entry_GetType.1 ln DFrac.discard _ $$ [$Hpbinit $Hent] as -
      wp_if_destruct
      · exfalso
        refine Hnc (D.length + sint.nat k) en (Nat.zero_le _) ?_ Hget (Or.inl ?_)
        · rw [List.length_append]; omega
        · exact Hif
      try wp_auto
      wp_apply wp_apply γr γp r id n st (D ++ ce.take (sint.nat k)) ln en _
        $$ [$Hpkg $Hrep $Hown $Hent $Hc1] as Hown
      try wp_auto
      wp_for_post
      iframe
      iexists k + W64 1, ln, a' + W64 1
      have Hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by
        have := Hcelen.2
        have : sint.Z k < sint.Z rdv'.CommittedEntries'.len := HifK
        word
      rw [Hk1, Htk, ← List.append_assoc]
      iframe
      ipureintro
      refine ⟨?_, by word, by word⟩
      have : ((D ++ ce).length : Int) < 2 ^ 64 := by omega
      rw [List.length_append, List.length_singleton, ← Ha']
      have : uint.nat a' < (D ++ ce).length := by
        rw [Ha', Hplen, List.length_append]; omega
      word
    · have Hfull : sint.nat k = ce.length := run_eq k _ _ _ Hif Hcelen.1 Hcebl Hk.2
      rw [Hfull, List.take_of_length_le (Nat.le_refl _)] at Ha'
      rw [Hfull, List.take_of_length_le (Nat.le_refl _)]
      try wp_auto
      -- the reads whose index is applied, answered
      wp_apply wp_answer γr γp r id n st (D ++ ce) pv' (ps ++ vls) (DFrac.own 1) a' (by rw [← Ha']; word)
        $$ [$Hpkg $Hrep $Hown $Hpv $Hps'] as %rest ⟨Hown, %ps', Hrest, Hcap2, #Hps2⟩
      -- `r.node.Advance()`: every conf entry delivered skipped (there is none)
      iunfold appNode at Hview
      icases Hview with ⟨%v, Hcfg, -, -, %Hv⟩
      ihave #Hsk := skippedIn_noConf γr.cluster (D ++ ce) v.applied (D ++ ce).length
        (fun j e _ h2 h3 => Hnc j e (Nat.zero_le _) h2 h3)
      wp_apply wp_node_Advance n γr.cluster kvRaftN id _ es none v rfl (fun _ h => by cases h)
        $$ [$Hraftinit $Hiscl $HisNode $Hdrv $Hrcpt $Hcfg $Hsk] as Hadv
      icases Hadv with (⟨Hdrv, #Hal', Hcfg⟩ | ⟨#Hstop, -⟩)
      rotate_left
      · iexfalso
        iapply nodeRunning_stopped n γr.cluster kvRaftN 1
        iframe Hrun Hstop
      ihave Hview : appNode γr n (D ++ ce) (D ++ ce).length kvMembership $$ [Hcfg]
      · unfold appNode
        iexists v
        iframe Hcfg Hdl Hsk
        ipureintro
        exact ⟨Hv.1, by have := Hv.2; simp only [List.length_append]; omega⟩
      try wp_auto
      wp_if_destruct
      · -- a snapshot of the state at the applied index, then a compaction below it
        have Hge : uint.Z (W64 100) ≤ uint.Z (a' - sI) := Hif
        have Hsa : uint.nat sI ≤ uint.nat a' := by
          have := Ha.2.2; have := Ha.1; rw [Ha', List.length_append]; omega
        have Hsub : uint.Z (a' - sI) = uint.Z a' - uint.Z sI := by word
        have Hlt : uint.nat sI + 100 ≤ uint.nat a' := by
          have : uint.Z (W64 100) = 100 := by decide
          word
        have HcA : c < uint.nat a' := by have := Ha.2.1; omega
        have HaD : uint.nat a' ≤ (D ++ ce).length := by rw [Ha']; exact Nat.le_refl _
        -- `data := encodeState(r.kv, r.applied)`, under the lock
        iunfold runOwn at Hown
        iNamed Hown
        wp_apply sync.Mutex.wp_Lock _ _ $$ [$Hmu] as ⟨Hlocked, HR⟩
        try wp_auto
        wp_apply wp_encodeState mK mA K A (DFrac.own 1) (DFrac.own 1) $$ [$Hpkg $HK $HA]
          as %dsl ⟨HK, HA, %kvs, %ops, Hdsl, %Hko⟩
        try wp_auto
        wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hmu $Hlocked HR]
        · inext; iexact HR
        try wp_auto
        -- `&pb.ConfState{Voters: r.storage.voters}`: the voters read-only
        imod csPts_of_struct_ro «$a1_ptr»
            (⟨zero_val _, vsl, slice.nil, slice.nil, slice.nil, null, slice.nil, 0⟩ : raftpb.ConfState)
            (kvConfState kvVoters) ⊤ rfl $$ [«$a1»] with #Hcs
        · iframe «$a1»
          iframe Hvs
          repeat (isplitr; · iapply ownSlice_nil)
          iunfold cellRO; ileft; ipureintro; exact ⟨rfl, rfl⟩
        ihave #Hcs' := csPts_weaken _ _ _ _ $$ Hcs
        try wp_auto
        -- the frozen entry at the applied index, its term the applied log's last
        ihave %H61 := frozenTo_len γs c (D ++ ce) $$ Hfz'
        icases frozenTo_at γs c (D ++ ce) (uint.nat a') HcA HaD $$ Hfz' with ⟨%e, #He, %HeD⟩
        have Hne : D ++ ce ≠ [] := by
          intro h; rw [h] at HaD; simp only [List.length_nil] at HaD; omega
        obtain ⟨x, Hx⟩ : ∃ x, (D ++ ce)[uint.nat a' - 1]? = some x :=
          ⟨_, List.getElem?_eq_getElem (by omega)⟩
        have HeT : e.Term' = x.term := by rw [HeD x Hx]; rfl
        have Hlast : Option.map LogEntry.term (D ++ ce).getLast? = some e.Term' := by
          rw [List.getLast?_eq_getElem?, show (D ++ ce).length - 1 = uint.nat a' - 1 by omega, Hx, HeT]
          rfl
        have HSE : kvSnapOk (D ++ ce) (encState kvs ops) := by
          unfold kvSnapOk logHist; rw [← Hods]
          exact stateEnc_intro _ K A kvs ops Hval HA Hko.1 Hko.2
        have Ha61 : uint.Z a' < 2 ^ 61 := by have := H61 (by omega); word
        have Hlen' : (D ++ ce).length = uint.nat a' := Ha'.symm
        imod kv_snap_make γr (D ++ ce) a' e.Term' (encState kvs ops) Hlen' (by word) Ha61 Hlast
            (snapListsOk_voters kvVoters e.Term' a' _ (by decide) (by decide) (by decide) (by decide) Ha61)
            HSE $$ Hcl Hap HcaF with #Hsv
        ihave #HSV : (kvJ γr.cluster id).SV
            (memSnapMade a' e.Term' (kvConfState kvVoters) (encState kvs ops)) $$ []
        · unfold kvJ; iexact Hsv
        ihave #HDL : (kvJ γr.cluster id).DL (uint.nat a') $$ []
        · unfold kvJ storDL
          iexists n, kvRaftN, D ++ ce
          iframe HisNode Hdl
          ipureintro; omega
        -- `r.storage.CreateSnapshot(applied, cs, data)`
        wp_apply kvStorage.wp_CreateSnapshot wp_MemoryStorage_CreateSnapshot st ms γs (kvJ γr.cluster id)
            a' e «$a1_ptr» DFrac.discard (kvConfState kvVoters) dsl (encState kvs ops) eood
          $$ [$Hrec $Hraftinit $HmsInv $He $HSV $HDL $HsnLb $Hcs' $Hdsl $Heood] as %snap' %err ⟨-, #HsLb, -⟩
        try wp_auto
        -- `if applied > snapMargin { r.storage.Compact(applied - snapMargin) }`
        wp_if_destruct
        rotate_left
        · kv_snap_post
        · have Hx : uint.nat (a' - W64 10) = uint.nat a' - 10 := by
            have : uint.Z (W64 10) < uint.Z a' := Hif
            word
          ihave #Hfx : iprop((∃ e : EntryM, memLog γs (uint.nat (a' - W64 10)) DFrac.discard [e]) ∨
              memCompacted γs (uint.nat (a' - W64 10))) $$ []
          · by_cases hcx : c < uint.nat (a' - W64 10)
            · ileft
              icases frozenTo_at γs c (D ++ ce) (uint.nat (a' - W64 10)) hcx (by omega) $$ Hfz'
                with ⟨%e2, #He2, -⟩
              iexists e2; iexact He2
            · iright
              iapply memCompacted_mono γs c (uint.nat (a' - W64 10)) (by omega) $$ Hcp
          ihave #HBx : (kvJ γr.cluster id).B (uint.nat (a' - W64 10)) $$ []
          · unfold kvJ
            ileft
            iapply nodeAppliedLb_mono γr.cluster id (D ++ ce).length (uint.nat (a' - W64 10)) (by omega)
              $$ Hal'
          ihave #HsLbx := memSnapLb_mono γs (uint.nat a') (uint.nat (a' - W64 10)) (by omega) $$ HsLb
          wp_apply kvStorage.wp_Compact wp_MemoryStorage_Compact st ms γs (kvJ γr.cluster id)
              (a' - W64 10) errCompacted
            $$ [$Hrec $Hraftinit $HmsInv $Hfx $HBx $HsLbx $ErrCompacted] as %err2 -
          kv_snap_post
      · -- no snapshot taken
        wp_for_post
        iframe
        unfold kvRunInv
        iexists D ++ ce, phsNext hd hh, rdv', rest, ps', a', sI, c
        iframe
        iframe Hps2 Hcp Hfz'
        ipureintro
        refine ⟨Ha', Ha.2.1, ?_⟩
        have := Ha.2.2; have := Ha.1; rw [Ha', List.length_append]; omega
  | some l =>
    ihave Hdrv : iprop(nodeDriver n γr.cluster kvRaftN ⟨kvStorIface st, strip l.dlv, phsNext hd hh,
        some (es, some l)⟩) $$ [Hdrv]
    · iexact Hdrv
    ihave ⟨Hdrv, #Hdl⟩ := nodeDriver_deliveredLogLb _ _ _ _ $$ Hdrv
    iunfold readySnap at HS
    icases HS with ⟨%Hl, Hsn, #HcL, #Hcert, ⟨%k, %old, %Hk, Hlog, Hend⟩, #Hgiven⟩
    obtain ⟨Hdlv, Hptr, Hce0, Hpre, Hlt, Hdlen, Hpos, H61, -, Hli⟩ := Hl
    subst Hce0
    have Hslen : (strip l.dlv).length = uint.nat l.snap.Metadata'.Index' := by
      unfold strip; rw [List.length_map]; exact Hdlen
    icases ownSnapS_not_null _ _ _ $$ Hsn with ⟨Hsn, %Hpn⟩
    -- `if rd.Snapshot != nil`: taken
    try wp_auto
    wp_if_destruct
    · exfalso; exact Hpn (Hptr.trans Hif)
    try wp_auto
    try rw [← Hptr]
    -- `decodeState(rd.Snapshot.GetData())`: its data, the state of the snapshot's committed log
    wp_apply wp_Snapshot_GetData_S l.ptr _ l.snap $$ [$Hpbinit $Hsn] as %dsl ⟨Hd, Hdback⟩
    imod kv_snap_read γr _ ⊤ CoPset.subseteq_top $$ Hcl Hcert with ⟨%L', %mL, #HcL', #HcaL, %HL'⟩
    simp only [snapTrip, snapId] at HL'
    ihave %HLeq := committed_eq γr.cluster L' (strip l.dlv) (by rw [HL'.1, Hslen]) $$ [HcL' HcL]
    · iframe HcL' HcL
    subst HLeq
    obtain ⟨kvs, ops, HdEq, HKw, HOw, Hk', Ho⟩ := HL'.2.1
    wp_apply wp_decodeState dsl _ kvs ops HKw HOw $$ [$Hpkg Hd]
      as %mK' %mA' ⟨Hd, %K', %A', HK', HA', %HKA⟩
    · rw [← HdEq]; iexact Hd
    ihave Hsn := Hdback $$ [Hd]
    · rw [HdEq]; iexact Hd
    try wp_auto
    -- `r.install(kv, ops)`: the replicated state at the snapshot's committed log
    obtain ⟨HvalS, HAS⟩ := maps_of_stateEnc _ kvs ops K' A' Hk' Ho HKA.1 HKA.2
    wp_apply wp_install γr γp r id n st D (strip l.dlv) ((strip l.dlv).map odOf) mK' mA' K' A' rfl HvalS HAS
      $$ [$Hpkg $Hrep $Hown $HK' $HA' $HcL] as Hown
    try wp_auto
    try rw [← Hptr]
    -- `applied = rd.Snapshot.GetMetadata().GetIndex()`, `snapIndex = applied`
    wp_apply wp_Snapshot_GetMetadata_S l.ptr _ l.snap $$ [$Hpbinit $Hsn] as %pm ⟨Hmd, Hmback⟩
    wp_apply wp_SnapshotMetadata_GetIndex_S pm _ _ $$ [$Hpbinit $Hmd] as Hmd
    ihave Hsn := Hmback $$ Hmd
    try wp_auto
    try rw [← Hptr]
    -- `r.storage.ApplySnapshot(rd.Snapshot)`: its justifications at node `id`
    ihave Hlog := kvStorLog_to st ms γs _ _ _ $$ Hrec Hlog
    ihave Hend := kvStorEnd_to st ms γs _ $$ Hrec Hend
    ihave #HsvJ : (kvJ γr.cluster id).SV l.snap $$ []
    · unfold kvJ
      iapply snapshotCert_valid γr.cluster kvRaftN l.snap Hpos H61
      iframe Hiscl Hcert
    ihave #HBJ : (kvJ γr.cluster id).B (uint.nat l.snap.Metadata'.Index') $$ []
    · unfold kvJ; iright; iexact Hgiven
    ihave #HDLJ : (kvJ γr.cluster id).DL (uint.nat l.snap.Metadata'.Index') $$ []
    · unfold kvJ storDL
      iexists n, kvRaftN, strip l.dlv
      iframe HisNode Hdl
      ipureintro; omega
    wp_apply kvStorage.wp_ApplySnapshot wp_MemoryStorage_ApplySnapshot st ms γs (kvJ γr.cluster id) k old
        l.ptr (DFrac.own (Qp.half 1)) l.snap eood Hk (by word)
      $$ [$Hrec $Hraftinit $HmsInv $Hlog $Hend $HBJ $HsvJ $HDLJ Hsn $HsnLb $Heood]
      as ⟨Hsn, #HcpS, #Hdum, HendS, -⟩
    · unfold snapArg; iright; iexact Hsn
    -- `r.storage.Append(rd.Entries)`, after the snapshot's index
    ihave ⟨Hrange, Hkeep⟩ := snapAppend_pre γs (uint.nat l.snap.Metadata'.Index' + 1) es $$ HendS
    have h1 : ∀ (j : Nat) (e : EntryM), es[j]? = some e →
        uint.nat e.Index' = (uint.nat l.snap.Metadata'.Index' + 1) + j := by
      intro j e hj
      have := Hli j e hj
      simp only [snapId] at this
      word
    have h2 : uint.nat l.snap.Metadata'.Index' + 1 + es.length ≤ 2 ^ 61 := by
      cases hes : es with
      | nil => simp only [List.length_nil, Nat.add_zero]; word
      | cons e0 rest =>
        have Hf := Hfit' e0 (by rw [hes]; rfl)
        have He0 := h1 0 e0 (by rw [hes]; rfl)
        rw [hes] at Hf
        simp only [List.length_cons] at Hf ⊢
        word
    try wp_auto
    wp_apply kvStorage.wp_Append wp_MemoryStorage_Append st ms γs (uint.nat l.snap.Metadata'.Index' + 1) []
        es rdv'.Entries' DFrac.discard h1 h2
      $$ [$Hrec $Hraftinit $Hlock $Hrange $Hes] as ⟨-, Hb⟩
    ihave ⟨Hb, HendB⟩ := snapAppend_post γs _ es $$ [Hb Hkeep]
    · iframe Hb Hkeep
    ihave Hrcpt := kv_snapReceipt st ms γs l es $$ Hrec Hsn HcpS Hdum Hb HendB
    -- `send(rd.Messages)`
    try wp_auto
    wp_bind (App (Val #send) _)
    iunfold sendSpec at Hsend
    iapply Hsend $$ [Hms Hmsok]
    · iframe
    iintro !> -
    try wp_auto
    -- the read states, noted
    ihave Hvs := readStatesPts_rsOk γr.cluster rdv'.ReadStates' sts $$ [Hsts Hstsok]
    · iframe Hsts Hstsok
    icases Hvs with ⟨%vls, #Hvls, #Hvlsok⟩
    wp_apply wp_slice_append $$ [$Hpv $Hpcap $Hvls] as %pv' ⟨Hpv, Hpcap, -⟩
    ihave #Hps' : iprop([∗list] v ∈ ps ++ vls, rsOk γr.cluster v) $$ []
    · iapply (BigSepL.bigSepL_append (Φ := fun _ v => rsOk (GF := GF) γr.cluster v)).2
      iframe Hps Hvlsok
    iclear Hps
    -- no committed entries
    iunfold committedEntriesAt at Hce
    icases entsPts_elim _ _ _ $$ Hce with ⟨%cls, #Hcel, #Hceb⟩
    ihave %Hcelen := ownSlice_len $$ Hcel
    ihave %Hcebl := entsBig_length $$ Hceb
    rw [toEntries_length] at Hcebl
    ihave IHa : iprop(∃ ev : Loc, "i" ∷ i_ptr ↦ W64 0 ∗ "e" ∷ e_ptr ↦ ev) $$ [i e]
    · iexists _; iframe
    wp_for IHa
    wp_if_destruct
    · exfalso
      simp only [List.length_nil] at Hcebl
      have := Hcelen.1; word
    try wp_auto
    -- the reads whose index is applied, answered
    wp_apply wp_answer γr γp r id n st (strip l.dlv) pv' (ps ++ vls) (DFrac.own 1) l.snap.Metadata'.Index'
        (by rw [Hslen]; word)
      $$ [$Hpkg $Hrep $Hown $Hpv $Hps'] as %rest ⟨Hown, %ps', Hrest, Hcap2, #Hps2⟩
    -- `r.node.Advance()`: the node's configuration at the snapshot's, the voters'
    iunfold appNode at Hview
    icases Hview with ⟨%v, Hcfg, -, -, -⟩
    wp_apply wp_node_Advance n γr.cluster kvRaftN id _ es (some l) v rfl
        (fun l' h => by cases h; exact Hdlen)
      $$ [$Hraftinit $Hiscl $HisNode $Hdrv Hrcpt $Hcfg] as Hadv
    · simp only [advReceipt]
      iframe Hrcpt Hcert
    icases Hadv with (⟨Hdrv, #Hal', %m2, Hcfg, #Hca2, %Hcs2⟩ | ⟨#Hstop, -⟩)
    rotate_left
    · iexfalso
      iapply nodeRunning_stopped n γr.cluster kvRaftN 1
      iframe Hrun Hstop
    imod kv_noConf γr (strip l.dlv) ⊤ CoPset.subseteq_top $$ Hinv Hcl HcL with ⟨-, #HcaS⟩
    ihave #HcaS' : confAt γr.cluster (uint.nat l.snap.Metadata'.Index') kvMembership $$ []
    · rw [← Hslen]; iexact HcaS
    ihave %Hm := confAt_agree γr.cluster _ m2 kvMembership $$ [Hca2 HcaS']
    · iframe Hca2 HcaS'
    subst Hm
    ihave Hview := appNode_snap γr n (strip l.dlv) _ kvMembership Hslen $$ [Hcfg Hdl]
    · iframe Hcfg Hdl
    ihave #Hfz2 := frozenTo_snap (GF := GF) γs (strip l.dlv) _ Hslen
    -- `if !reconf && applied-snapIndex >= snapEvery`: no (the snapshot `Ready` applied nothing)
    try wp_auto
    wp_if_destruct
    · exfalso
      have h0 : uint.Z (W64 100) ≤ uint.Z (l.snap.Metadata'.Index' - l.snap.Metadata'.Index') := Hif
      rw [show l.snap.Metadata'.Index' - l.snap.Metadata'.Index' = W64 0 by word] at h0
      revert h0; decide
    wp_for_post
    iframe
    unfold kvRunInv
    iexists strip l.dlv, phsNext hd hh, rdv', rest, ps', l.snap.Metadata'.Index',
      l.snap.Metadata'.Index', uint.nat l.snap.Metadata'.Index'
    iframe
    iframe Hps2 HcpS Hfz2
    ipureintro
    exact ⟨Hslen.symm, Nat.le_refl _, Nat.le_refl _⟩

end proof

end kv
end EtcdGrove
end Perennial

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
  -- PORT(durability stage II): a definition or statement it uses changed (durability stage I-2..I-8)
  sorry

end proof

end kv
end EtcdGrove
end Perennial

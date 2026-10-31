/-
`s.snapshot(ep, toDisk)` (`server.go`): the trust boundary (names-only). Lean-first (no Rocq
counterpart); the request path's unit 4b (2026-10-13).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplyAll
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ApplyKVCore
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapTake
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvSnapSend
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AppliedOn

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`s.snapshot(ep, toDisk)`** (D22 J4b, 2026-10-27, as `specFull`, proved on lean; 2026-10-30,
the repair: the spec, in place of the trust-boundary axiom over the old storage token; 2026-10-31,
the snapshot track: proved again, the snapshot certified by `srv_snap_make`). It commits the
KV, creates a raft snapshot at the applied index in the `MemoryStorage`
(`CreateSnapshot(ep.appliedi, ep.confState, nil)`) and with `toDisk` saves it to the WAL, leaving
the apply thread's state as the old `spec` said; the storage's stored snapshot past `ai` afterwards
(`srvSnapState … ai ai`). What the body needs:
* the server's view (`isServer`: the logger, the member id, the consistent index's field) and
  `applyAll`'s (`isServerApplyAll`: `SnapshotCount`);
* with `toDisk`, `s.KV().Commit()`: the server's KV over the store (`txn.isKV`, `NewServer`'s) and
  the write budget (`srvWTPool`) for the commit's write-back, the writer's tokens lent by the
  applier row (`srvApplyKVCore_commit`; 2026-10-31, the snapshot track's S6: until then a contract
  `srvKVCommitOk kv RC RC'` with its `RC`, which no caller could give: the writer's tokens are the
  row's, which the spec also takes);
* `CreateSnapshot`'s premises (2026-10-30, the repair): the storage's invariant, the node's
  delivered log past `ai`, the cluster's registry and a committed log of length `ai` ending at
  `at'` (`srvSnapStor`), the frozen entry at `ai` (`srvSnapFrozen`, P8); (2026-10-31, the
  snapshot track, `notes/snapshot-sorries-plan.md`) and what certifying the snapshot takes
  (`snapshotCert_make`): `ep.confState` the voters' (`epCsCfg`), the frozen entry of term `at'`
  (`srvFrozenTerm`), `ai` positive, fewer than `2^61` voters;
* `verifyConsistentIndexIsLatest`'s check: the consistent index at least `ai`;
* with `toDisk`, the disk's storage (`srvSnapDisk`: `SaveSnap`, and `Release`'s directory at a
  removal fact the applied index past `j` gives) with the applied index at least `ai`, and
  `Release` not failing (`storage.releaseOk`, as `applySnapshot`'s `snapOpensOk`).
The applier row is `spec`'s, `srvApplyKVCore` (E3p; merged onto lean 2026-10-27). -/
abbrev EtcdServer.snapshot.spec : Prop :=
  ∀ (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (E : apply.AEnv GF)
    (ρ : ReqNames) (γr : ReadNames) (γw : GName) (b : GoInterface) (ep : Loc)
    (st : ApplyState) (ai at' : w64) (cs : Loc) (a t : w64) (x : apply.ApplyKV) (toDisk : Bool)
    (ms : Loc) (γs : MemStorNames) (nid : w64) (sl : w64) (γp : GName) (ua : GoInterface) (q : Qp),
  loopOk γ st ai → uint.Z ai ≤ uint.Z (ciEff γ st.k) → storage.releaseOk →
  -- (2026-10-31, the snapshot track: what `snapshotCert_make` takes) an entry applied, the voters
  -- fewer than `2^61` (`SnapListsOk`)
  0 < uint.Z ai → GMap.size γr.raft.raft.cfg < 2 ^ 61 →
  -- (2026-10-31, `notes/axiom-review/savesnap.md`) what the WAL's `SaveSnap` takes: the WAL's write
  -- not failing (I/O), the snapshot's term non-zero, a voter (the conf state not the empty one)
  storage.walSaveOk → at' ≠ W64 0 → 0 < GMap.size γr.raft.raft.cfg →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerM E.authOn s γ ci TM E ρ γr ∗ isServerApplyAll s γr ∗
      srvSnapState s ep ms γs ai sl ∗ srvSnapFrozen γs (uint.nat ai) ∗ (letI := srvStor (GF := GF) γr.raft.raft; nodeAppliedLb γr.raft.raft.cl nid (uint.nat ai)) ∗
      srvSnapStor ms γs γr nid ai at' ∗ srvSnapDisk s γr ∗ appliedAtLeast γr ai ∗
      -- (2026-10-31) `ep.confState` the voters', the entry at `ai` frozen at `at'`
      epCsCfg γr cs ∗ srvFrozenTerm γs ai at' ∗
      (∃ kv : GoInterface, srvKVAddr s ↦□ kv ∗ txn.isKV kv E.s E.γ) ∗ srvWTPool E γp ∗
      epAppliedIAddr ep ↦ ai ∗ epAppliedTAddr ep ↦ at' ∗ epConfState ep cs ∗
      applyThread γ st ∗ applyBackend γ ci b ∗ ciApplying ci a t ∗ srvLgReader s ∗
      srvApplyKVCore s E γw x ua ∗
      -- (2026-10-31) the WAL open (the apply thread's share of it)
      rnWalTok (srvRAddr s) q }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"snapshot")) (Val #ep))
      (Val #toDisk))
  {{ RET #(); ∃ st' : ApplyState, srvSnapState s ep ms γs ai ai ∗ srvSnapFrozen γs (uint.nat ai) ∗
      epAppliedIAddr ep ↦ ai ∗ epAppliedTAddr ep ↦ at' ∗ epConfState ep cs ∗
      applyThread γ st' ∗ applyBackend γ ci b ∗ ciApplying ci a t ∗ srvLgReader s ∗ srvApplyKVCore s E γw x ua ∗
      rnWalTok (srvRAddr s) q ∗
      ⌜loopOk γ st' ai ∧ ciEff γ st'.k = ciEff γ st.k⌝ }}

end spec

end EtcdGrove
end Perennial

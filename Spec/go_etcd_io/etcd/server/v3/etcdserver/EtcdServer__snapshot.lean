/-
`s.snapshot(ep, toDisk)` (`server.go`): the trust boundary (names-only). Lean-first (no Rocq
counterpart); the request path's unit 4b (2026-10-13).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplyAll
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ApplyKVCore
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapTake
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvSnapSend

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

/-- `s.snapshot(ep, toDisk)`, by the apply thread (the contract of a names-only callee: it
commits the KV (`KV().Commit()`, a commit of the backend's batch transaction, which saves the
consistent index), creates a raft snapshot at the applied index in the `MemoryStorage`, and if
`toDisk` saves it to the WAL): it leaves the applied index, term and conf state, the KV's state
(the applier row's part shared by both auth modes, `srvApplyKVCore`: since E3p, 2026-10-27,
without the auth store's apply-side resource, which `snapshot` does not touch; until then the whole
mode-off row `srvApplyKV`), the backend, the applying index unchanged, may load the consistent index (the
protocol's state keeps `loopOk` and `ciEff`), and may move the snapshot state (`ep`'s snapshot
indices, `forceDiskSnapshot`).

(D19i part 1, 2026-10-18; until then false: the contract owned nothing of the `MemoryStorage`)
The raft snapshot is `MemoryStorage.CreateSnapshot(ep.appliedi, ep.confState, nil)`, under the
application's snapshot token (`srvSnapState`'s `memSnapTok`) and the storage's floor at least the
applied index (`memFloorAtLeast`, the floor raft raised at the `Advance` that `raftAdvancedC`
reports), the conf state `nil` or read-only (`epConfState`'s `epCsOk`): `CreateSnapshot.spec`'s premises (its
boundary at most `ai`). Either it is created at `ai` or the storage's snapshot is already at or
past `ai` (`ErrSnapOutOfDate`, returned on): the token's snapshot index is at least `ai`
afterwards; the snapshot indices move only to `ai`.

(D22 J4, 2026-10-26) The token is shared (`srvSnapState`'s body: its ghost part in an invariant
raft's goroutine shares, the counter `γss` of the storage's snapshot index): the snapshot index is
at least `ai` afterwards in the counter (`CreateSnapshot.wp_shared`'s lower bound on both
branches). Still an axiom (names-only): its proof needs the created
snapshot's certificate in the storage's registry (`CreateSnapshot`'s premise; the server holds no
registry authority, `bootOk`) and the snapshot directory's invariant for `Release` (J1a's bundle,
which does not reach the apply thread yet): `notes/decisions.md`, "D22 J4". -/
abbrev EtcdServer.snapshot.spec : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (γw : GName) (γ : ApplyNames) (ci : Loc) (b : GoInterface) (ep : Loc)
    (st : ApplyState) (ai at' : w64) (cs : Loc) (a t : w64) (x : apply.ApplyKV) (toDisk : Bool)
    (ms : Loc) (γs : MemStorNames) (nid : w64) (sl : w64) (ua : GoInterface) (γr : ReadNames),
  loopOk γ st ai →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvSnapState s ep ms γs ai sl ∗ (letI := srvStor (GF := GF) γr.raft.raft; nodeAppliedLb γr.raft.raft.cl nid (uint.nat ai)) ∗
      epAppliedIAddr ep ↦ ai ∗ epAppliedTAddr ep ↦ at' ∗ epConfState ep cs ∗
      applyThread γ st ∗ applyBackend γ ci b ∗ ciApplying ci a t ∗ srvLgReader s ∗ srvApplyKVCore s E γw x ua }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"snapshot")) (Val #ep))
      (Val #toDisk))
  {{ RET #(); ∃ st' : ApplyState, srvSnapState s ep ms γs ai ai ∗
      epAppliedIAddr ep ↦ ai ∗ epAppliedTAddr ep ↦ at' ∗ epConfState ep cs ∗
      applyThread γ st' ∗ applyBackend γ ci b ∗ ciApplying ci a t ∗ srvLgReader s ∗ srvApplyKVCore s E γw x ua ∗
      ⌜loopOk γ st' ai ∧ ciEff γ st'.k = ciEff γ st.k⌝ }}

/-- **`s.snapshot(ep, toDisk)`, of the translated body** (D22 J4b, 2026-10-27; proved,
`EtcdServer.snapshot.wp_proof_full`, `SnapTakeProof.lean`; not linked yet: its premises beyond
`spec`'s do not reach `applyAll` before J1a's bundle, `notes/decisions.md`, "D22 J4b"). As `spec`,
with what the body needs beyond it:
* the server's view (`isServer`: the logger, the member id, the consistent index's field) and
  `applyAll`'s (`isServerApplyAll`: `SnapshotCount`);
* with `toDisk`, `s.KV().Commit()`'s contract (`srvKVCommitOk kv RC RC'`, as the merged snapshot's
  sender has it, `SnapSendBranch.lean`) and its `RC`, `RC'` after;
* `CreateSnapshot`'s certificate: the storage's registry (`memCertReg`, `SnapTake.lean`);
* `verifyConsistentIndexIsLatest`'s check: the consistent index at least `ai`;
* with `toDisk`, the disk's storage (`srvSnapDisk`: `SaveSnap`, and `Release`'s directory at a
  removal fact the applied index past `j` gives) with the applied index at least `ai`, and
  `Release` not failing (`storage.releaseOk`, as `applySnapshot`'s `snapOpensOk`).
The applier row is `spec`'s, `srvApplyKVCore` (E3p; merged onto lean 2026-10-27). -/
abbrev EtcdServer.snapshot.specFull : Prop :=
  ∀ (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (E : apply.AEnv GF)
    (ρ : ReqNames) (γr : ReadNames) (γw : GName) (b : GoInterface) (ep : Loc)
    (st : ApplyState) (ai at' : w64) (cs : Loc) (a t : w64) (x : apply.ApplyKV) (toDisk : Bool)
    (ms : Loc) (γs : MemStorNames) (nid : w64) (sl : w64) (kv : GoInterface) (RC RC' : IProp GF)
    (ua : GoInterface),
  loopOk γ st ai → uint.Z ai ≤ uint.Z (ciEff γ st.k) → storage.releaseOk →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServer s γ ci TM E ρ γr ∗ isServerApplyAll s γr ∗
      srvSnapState s ep ms γs ai sl ∗ (letI := srvStor (GF := GF) γr.raft.raft; nodeAppliedLb γr.raft.raft.cl nid (uint.nat ai)) ∗
      -- PENDING (Stage F, D2): what `CreateSnapshot`'s `J.SV` needs (until the repair the free
      -- certificate registry `memCertReg`)
      srvSnapDisk s γr ∗ appliedAtLeast γr ai ∗
      srvKVAddr s ↦□ kv ∗ srvKVCommitOk kv RC RC' ∗ (if toDisk then RC else iprop(True)) ∗
      epAppliedIAddr ep ↦ ai ∗ epAppliedTAddr ep ↦ at' ∗ epConfState ep cs ∗
      applyThread γ st ∗ applyBackend γ ci b ∗ ciApplying ci a t ∗ srvLgReader s ∗
      srvApplyKVCore s E γw x ua }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"snapshot")) (Val #ep))
      (Val #toDisk))
  {{ RET #(); ∃ st' : ApplyState, srvSnapState s ep ms γs ai ai ∗
      (if toDisk then RC' else iprop(True)) ∗
      epAppliedIAddr ep ↦ ai ∗ epAppliedTAddr ep ↦ at' ∗ epConfState ep cs ∗
      applyThread γ st' ∗ applyBackend γ ci b ∗ ciApplying ci a t ∗ srvLgReader s ∗ srvApplyKVCore s E γw x ua ∗
      ⌜loopOk γ st' ai ∧ ciEff γ st'.k = ciEff γ st.k⌝ }}

end spec

end EtcdGrove
end Perennial

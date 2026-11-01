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

/-- **`s.snapshot(ep, toDisk)`** (D22 J4b, 2026-10-27, as `specFull`, proved on lean,
`SnapTakeProof.lean`; 2026-10-30, the repair: the spec, in place of the trust-boundary axiom over
the old storage token; its proof SNAPSHOT-SORRY until `SnapTakeProof`'s is rewired). It commits the
KV, creates a raft snapshot at the applied index in the `MemoryStorage`
(`CreateSnapshot(ep.appliedi, ep.confState, nil)`) and with `toDisk` saves it to the WAL, leaving
the apply thread's state as the old `spec` said; the storage's stored snapshot past `ai` afterwards
(`srvSnapState … ai ai`). What the body needs:
* the server's view (`isServer`: the logger, the member id, the consistent index's field) and
  `applyAll`'s (`isServerApplyAll`: `SnapshotCount`);
* with `toDisk`, `s.KV().Commit()`'s contract (`srvKVCommitOk kv RC RC'`, as the merged snapshot's
  sender has it, `SnapSendBranch.lean`) and its `RC`, `RC'` after;
* `CreateSnapshot`'s premises (2026-10-30, the repair): the storage's invariant, the node's
  delivered log past `ai`, the cluster's registry and a committed log of length `ai` ending at
  `at'` (`srvSnapStor`), the frozen entry at `ai` (`srvSnapFrozen`, P8);
* `verifyConsistentIndexIsLatest`'s check: the consistent index at least `ai`;
* with `toDisk`, the disk's storage (`srvSnapDisk`: `SaveSnap`, and `Release`'s directory at a
  removal fact the applied index past `j` gives) with the applied index at least `ai`, and
  `Release` not failing (`storage.releaseOk`, as `applySnapshot`'s `snapOpensOk`).
The applier row is `spec`'s, `srvApplyKVCore` (E3p; merged onto lean 2026-10-27). -/
abbrev EtcdServer.snapshot.spec : Prop :=
  ∀ (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (E : apply.AEnv GF)
    (ρ : ReqNames) (γr : ReadNames) (γw : GName) (b : GoInterface) (ep : Loc)
    (st : ApplyState) (ai at' : w64) (cs : Loc) (a t : w64) (x : apply.ApplyKV) (toDisk : Bool)
    (ms : Loc) (γs : MemStorNames) (nid : w64) (sl : w64) (kv : GoInterface) (RC RC' : IProp GF)
    (ua : GoInterface),
  loopOk γ st ai → uint.Z ai ≤ uint.Z (ciEff γ st.k) → storage.releaseOk →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerM E.authOn s γ ci TM E ρ γr ∗ isServerApplyAll s γr ∗
      srvSnapState s ep ms γs ai sl ∗ srvSnapFrozen γs (uint.nat ai) ∗ (letI := srvStor (GF := GF) γr.raft.raft; nodeAppliedLb γr.raft.raft.cl nid (uint.nat ai)) ∗
      srvSnapStor ms γs γr nid ai at' ∗ srvSnapDisk s γr ∗ appliedAtLeast γr ai ∗
      srvKVAddr s ↦□ kv ∗ srvKVCommitOk kv RC RC' ∗ (if toDisk then RC else iprop(True)) ∗
      epAppliedIAddr ep ↦ ai ∗ epAppliedTAddr ep ↦ at' ∗ epConfState ep cs ∗
      applyThread γ st ∗ applyBackend γ ci b ∗ ciApplying ci a t ∗ srvLgReader s ∗
      srvApplyKVCore s E γw x ua }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"snapshot")) (Val #ep))
      (Val #toDisk))
  {{ RET #(); ∃ st' : ApplyState, srvSnapState s ep ms γs ai ai ∗ srvSnapFrozen γs (uint.nat ai) ∗
      (if toDisk then RC' else iprop(True)) ∗
      epAppliedIAddr ep ↦ ai ∗ epAppliedTAddr ep ↦ at' ∗ epConfState ep cs ∗
      applyThread γ st' ∗ applyBackend γ ci b ∗ ciApplying ci a t ∗ srvLgReader s ∗ srvApplyKVCore s E γw x ua ∗
      ⌜loopOk γ st' ai ∧ ciEff γ st'.k = ciEff γ st.k⌝ }}

end spec

end EtcdGrove
end Perennial

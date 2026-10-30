/-
`s.snapshotIfNeededAndCompactRaftLog(ep)` (`server.go`). Lean-first (no Rocq counterpart); the request path's unit 4b
(2026-10-13).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplyAll
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AppliedOn
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__snapshot

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

/-- `s.snapshotIfNeededAndCompactRaftLog(ep)`, by the apply thread: if a disk or in-memory
snapshot is due, `snapshot` and `compactRaftLog`; the applied index, term and conf state, the KV and
the backend are left as they are, the protocol's state keeps `loopOk` and `ciEff`. The applier row
in the environment's auth mode (`srvApplyKVM E.authOn`, the model's auth state `sa` on; `specOff`
and `specOn` its corollaries), kept.

(2026-10-30, stage P, the lead's decision B1) **The no-snapshot path's spec**: it takes only what the
guard (`shouldSnapshotToDisk`/`ToMemory`: `srvSnapState`'s indices and `SnapshotCount`,
`isServerApplyAll`) and the path where no snapshot is due need, what `applyAll` holds; its proof
closes the branch where a snapshot is due with SNAPSHOT-SORRY #11. `specFull` below is the spec
over `snapshot`'s and `compactRaftLog`'s premises, proved (`wp_proofFull`), for the snapshot
track. -/
abbrev EtcdServer.snapshotIfNeededAndCompactRaftLog.spec : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (γw : GName) (γ : ApplyNames) (ci : Loc) (b : GoInterface) (γr : ReadNames)
    (ep : Loc) (st : ApplyState) (ai at' : w64) (cs : Loc) (a t : w64) (x : apply.ApplyKV)
    (ms : Loc) (γs : MemStorNames) (sa : auth.AuthState),
  loopOk γ st ai →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerApplyAll s γr ∗ srvSnapState s ep ms γs ai (W64 0) ∗
      epAppliedIAddr ep ↦ ai ∗ epAppliedTAddr ep ↦ at' ∗ epConfState ep cs ∗
      applyThread γ st ∗ applyBackend γ ci b ∗ ciApplying ci a t ∗ srvLgReader s ∗ srvApplyKVM E.authOn s E γw x sa }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"snapshotIfNeededAndCompactRaftLog"))
      (Val #ep))
  {{ RET #(); ∃ st' : ApplyState, srvSnapState s ep ms γs ai (W64 0) ∗
      epAppliedIAddr ep ↦ ai ∗ epAppliedTAddr ep ↦ at' ∗ epConfState ep cs ∗
      applyThread γ st' ∗ applyBackend γ ci b ∗ ciApplying ci a t ∗ srvLgReader s ∗ srvApplyKVM E.authOn s E γw x sa ∗ ⌜loopOk γ st' ai ∧ ciEff γ st'.k = ciEff γ st.k⌝ }}

/-- **`spec` over `snapshot`'s and `compactRaftLog`'s premises** (2026-10-30, the repair: snapshots
allowed; renamed `specFull` by stage P's decision B1, for the snapshot track): what `snapshot` takes
(`isServerM`, `srvSnapDisk`, `appliedAtLeast`, the KV commit contract with `RC`, `srvSnapStor`, the
consistent index past `ai`, `releaseOk`) and the node's applied index past `ai` (`compactRaftLog`'s);
post `RC ∨ RC'`. -/
abbrev EtcdServer.snapshotIfNeededAndCompactRaftLog.specFull : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (γw : GName) (γ : ApplyNames) (ci : Loc) (b : GoInterface) (γr : ReadNames)
    (ep : Loc) (st : ApplyState) (ai at' : w64) (cs : Loc) (a t : w64) (x : apply.ApplyKV)
    (ms : Loc) (γs : MemStorNames) (nid : w64) (γp : GName) (w : Nat)
    (TM : MetaCI → IProp GF) (ρ : ReqNames) (kv : GoInterface) (RC RC' : IProp GF)
    (sa : auth.AuthState),
  loopOk γ st ai →
  -- (D22 J5) the applied index at most the write tokens taken (no snapshot installed)
  uint.Z ai ≤ w →
  -- (2026-10-30, the repair: snapshots allowed) what `snapshot` takes (its spec, lean's
  -- `specFull`): the consistent index past `ai`, `Release` not failing
  uint.Z ai ≤ uint.Z (ciEff γ st.k) → storage.releaseOk →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerM E.authOn s γ ci TM E ρ γr ∗ srvSnapDisk s γr ∗ appliedAtLeast γr ai ∗
      srvKVAddr s ↦□ kv ∗ srvKVCommitOk kv RC RC' ∗ RC ∗ srvSnapStor ms γs γr nid ai at' ∗
      isServerApplyAll s γr ∗ srvWTPool E γp ∗ srvWTTaken γp w ∗ srvSnapState s ep ms γs ai (W64 0) ∗
      -- (D19i part 1; 2026-10-30, the repair: in place of the storage's floor) the node `nid`'s
      -- applied index past the applied index (`raftAdvancedC`'s, `Compact`'s `J.B`)
      (letI := srvStor (GF := GF) γr.raft.raft; nodeAppliedLb γr.raft.raft.cl nid (uint.nat ai)) ∗
      epAppliedIAddr ep ↦ ai ∗ epAppliedTAddr ep ↦ at' ∗ epConfState ep cs ∗
      applyThread γ st ∗ applyBackend γ ci b ∗ ciApplying ci a t ∗ srvLgReader s ∗ srvApplyKVM E.authOn s E γw x sa }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"snapshotIfNeededAndCompactRaftLog"))
      (Val #ep))
  {{ RET #(); ∃ st' : ApplyState, (RC ∨ RC') ∗ srvSnapState s ep ms γs ai (W64 0) ∗
      epAppliedIAddr ep ↦ ai ∗ epAppliedTAddr ep ↦ at' ∗ epConfState ep cs ∗
      applyThread γ st' ∗ applyBackend γ ci b ∗ ciApplying ci a t ∗ srvLgReader s ∗ srvApplyKVM E.authOn s E γw x sa ∗ ⌜loopOk γ st' ai ∧ ciEff γ st'.k = ciEff γ st.k⌝ }}

end spec

end EtcdGrove
end Perennial

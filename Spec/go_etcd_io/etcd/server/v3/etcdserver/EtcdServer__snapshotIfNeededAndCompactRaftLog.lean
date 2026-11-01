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
and `specOn` its corollaries), kept. It takes what `snapshot` takes (`isServerM`, `srvSnapDisk`,
`appliedAtLeast`, the server's KV over the store, `srvSnapStor`, the consistent index past `ai`,
`releaseOk`, `walSaveOk`, the WAL's open token) and the node's applied index past `ai`
(`compactRaftLog`'s).

(2026-10-30, the repair: snapshots allowed; stage P's decision B1 split it into a no-snapshot
spec, whose proof closed the snapshot branch with SNAPSHOT-SORRY #11, and this one, then `specFull`;
2026-10-31, #11: `applyAll` uses this one, the other is gone. The snapshot track's S6: until then
the KV commit contract with `RC`, post `RC ∨ RC'`.) -/
abbrev EtcdServer.snapshotIfNeededAndCompactRaftLog.specBatch : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (γw : GName) (γ : ApplyNames) (ci : Loc) (b : GoInterface) (γr : ReadNames)
    (ep : Loc) (st : ApplyState) (ai at' : w64) (cs : Loc) (a t : w64) (x : apply.ApplyKV)
    (ms : Loc) (γs : MemStorNames) (nid : w64) (γp : GName) (w : Nat)
    (TM : MetaCI → IProp GF) (ρ : ReqNames)
    (sa : auth.AuthState) (q : Qp),
  loopOk γ st ai →
  -- (D22 J5) the applied index at most the write tokens taken (no snapshot installed)
  uint.Z ai ≤ w →
  -- (2026-10-30, the repair: snapshots allowed) what `snapshot` takes (its spec, lean's
  -- `specFull`): the consistent index past `ai`, `Release` not failing
  uint.Z ai ≤ uint.Z (ciEff γ st.k) → storage.releaseOk →
  -- (2026-10-31, the snapshot track: what certifying the snapshot takes) fewer than `2^61` voters
  GMap.size γr.raft.raft.cfg < 2 ^ 61 →
  -- (2026-10-31, `notes/axiom-review/savesnap.md`) what the WAL's `SaveSnap` takes (`snapshot`'s)
  storage.walSaveOk →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerM E.authOn s γ ci TM E ρ γr ∗ srvSnapDisk s γr ∗ appliedAtLeast γr ai ∗
      (∃ kv : GoInterface, srvKVAddr s ↦□ kv ∗ txn.isKV kv E.s E.γ) ∗ srvSnapStor ms γs γr nid ai at' ∗
      isServerApplyAll s γr ∗ srvWTPool E γp ∗ srvWTTaken γp w ∗ srvSnapState s ep ms γs ai (W64 0) ∗
      srvSnapFrozen γs (uint.nat ai) ∗
      -- (2026-10-31) `ep.confState` the voters' (or nothing applied: no snapshot is due at `0`), the
      -- entry at `ai` frozen at `at'` (`snapshot`'s)
      (⌜uint.Z ai = 0⌝ ∨ epCsCfg γr cs) ∗ srvFrozenTerm γs ai at' ∗
      -- (D19i part 1; 2026-10-30, the repair: in place of the storage's floor) the node `nid`'s
      -- applied index past the applied index (`raftAdvancedC`'s, `Compact`'s `J.B`)
      (letI := srvStor (GF := GF) γr.raft.raft; nodeAppliedLb γr.raft.raft.cl nid (uint.nat ai)) ∗
      epAppliedIAddr ep ↦ ai ∗ epAppliedTAddr ep ↦ at' ∗ epConfState ep cs ∗
      applyThread γ st ∗ applyBackend γ ci b ∗ ciApplying ci a t ∗ srvLgReader s ∗ srvApplyKVM E.authOn s E γw x sa ∗
      rnWalTok (srvRAddr s) q }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"snapshotIfNeededAndCompactRaftLog"))
      (Val #ep))
  {{ RET #(); ∃ st' : ApplyState, srvSnapState s ep ms γs ai (W64 0) ∗ srvSnapFrozen γs (uint.nat ai) ∗
      epAppliedIAddr ep ↦ ai ∗ epAppliedTAddr ep ↦ at' ∗ epConfState ep cs ∗
      applyThread γ st' ∗ applyBackend γ ci b ∗ ciApplying ci a t ∗ srvLgReader s ∗ srvApplyKVM E.authOn s E γw x sa ∗ rnWalTok (srvRAddr s) q ∗ ⌜loopOk γ st' ai ∧ ciEff γ st'.k = ciEff γ st.k⌝ }}

/-- (2026-11-01, J8a-5) **Nothing due** (after a snapshot's install, `applyAll.specSnap`): with the
disk and in-memory snapshot indices at the applied index `ai` (and `ai + memorySnapshotCount` not
wrapping), neither snapshot is due, and the function returns at once. -/
abbrev EtcdServer.snapshotIfNeededAndCompactRaftLog.specNoop : Prop :=
  ∀ (s : Loc) (γr : ReadNames) (ep : Loc) (ai : w64),
  uint.Z ai + 100 < 2 ^ 64 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerApplyAll s γr ∗ srvFS s ∗
      epAppliedIAddr ep ↦ ai ∗ epDiskSnapAddr ep ↦ ai ∗ epMemSnapAddr ep ↦ ai }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"snapshotIfNeededAndCompactRaftLog"))
      (Val #ep))
  {{ RET #(); srvFS s ∗ epAppliedIAddr ep ↦ ai ∗ epDiskSnapAddr ep ↦ ai ∗ epMemSnapAddr ep ↦ ai }}

/-- **`snapshotIfNeededAndCompactRaftLog`'s spec** (J8b, 2026-11-01): both cases, after a batch (`specBatch`) and at the snapshot indices (`specNoop`), for the link. -/
abbrev EtcdServer.snapshotIfNeededAndCompactRaftLog.spec : Prop :=
  EtcdServer.snapshotIfNeededAndCompactRaftLog.specBatch (GF := GF) (hG := hG) ∧
    EtcdServer.snapshotIfNeededAndCompactRaftLog.specNoop (GF := GF) (hG := hG)

end spec

end EtcdGrove
end Perennial

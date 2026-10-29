/-
`s.snapshotIfNeededAndCompactRaftLog(ep)` (`server.go`). Lean-first (no Rocq counterpart); the request path's unit 4b
(2026-10-13).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplyAll
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

/-- `s.snapshotIfNeededAndCompactRaftLog(ep)`, by the apply thread: if a disk or in-memory
snapshot is due, `snapshot` and `compactRaftLog` (contracts); the applied index, term and conf
state, the KV and the backend are left as they are, the protocol's state keeps `loopOk` and
`ciEff`. (2026-10-19, D21 M3) The compaction stays at index `1`, within the storage's cap: the
applied index is at most the write tokens taken (`srvWTAt`; D22 J5, 2026-10-26: the count
`srvWTTaken γp w`, with `uint.Z ai ≤ w`, which holds until a snapshot is installed), below the receipts' bound
(`srvWTPool_bound`), itself at most `SnapshotCatchUpEntries + 1` (`isServerApplyAll`).
The applier row in the environment's auth mode (`srvApplyKVM E.authOn`, the model's auth state `sa`
on; the auth-mode merge, 2026-10-29: one spec for both modes, `specOff` and `specOn` its
corollaries), kept (`snapshot` takes only the part both rows share, `srvApplyKVCore`). -/
abbrev EtcdServer.snapshotIfNeededAndCompactRaftLog.spec : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (γw : GName) (γ : ApplyNames) (ci : Loc) (b : GoInterface) (γr : ReadNames)
    (ep : Loc) (st : ApplyState) (ai at' : w64) (cs : Loc) (a t : w64) (x : apply.ApplyKV)
    (ms : Loc) (γs : MemStorNames) (γp : GName) (w : Nat)
    (sa : auth.AuthState),
  loopOk γ st ai →
  1 ≤ γs.cap →
  -- (D22 J5) the applied index at most the write tokens taken (no snapshot installed)
  uint.Z ai ≤ w →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerApplyAll s γr ∗ srvWTPool E γp ∗ srvWTTaken γp w ∗ srvSnapState s ep ms γs ai (W64 0) ∗
      -- (D19i part 1) the storage's floor past the applied index (`raftAdvancedC`'s)
      memFloorAtLeast ms γs (uint.Z ai) ∗
      epAppliedIAddr ep ↦ ai ∗ epAppliedTAddr ep ↦ at' ∗ epConfState ep cs ∗
      applyThread γ st ∗ applyBackend γ ci b ∗ ciApplying ci a t ∗ srvLgReader s ∗ srvApplyKVM E.authOn s E γw x sa }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"snapshotIfNeededAndCompactRaftLog"))
      (Val #ep))
  {{ RET #(); ∃ st' : ApplyState, srvSnapState s ep ms γs ai (W64 0) ∗
      epAppliedIAddr ep ↦ ai ∗ epAppliedTAddr ep ↦ at' ∗ epConfState ep cs ∗
      applyThread γ st' ∗ applyBackend γ ci b ∗ ciApplying ci a t ∗ srvLgReader s ∗ srvApplyKVM E.authOn s E γw x sa ∗ ⌜loopOk γ st' ai ∧ ciEff γ st'.k = ciEff γ st.k⌝ }}

end spec

end EtcdGrove
end Perennial

/-
`s.snapshot(ep, toDisk)` (`server.go`): the trust boundary (names-only). Lean-first (no Rocq
counterpart); the request path's unit 4b (2026-10-13).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplyAll
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ApplyKVCore

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
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
afterwards; the snapshot indices move only to `ai`. -/
abbrev EtcdServer.snapshot.spec : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (γw : GName) (γ : ApplyNames) (ci : Loc) (b : GoInterface) (ep : Loc)
    (st : ApplyState) (ai at' : w64) (cs : Loc) (a t : w64) (x : apply.ApplyKV) (toDisk : Bool)
    (ms : Loc) (γs : MemStorNames) (sl : w64) (ua : GoInterface),
  loopOk γ st ai →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvSnapState s ep ms γs ai sl ∗ memFloorAtLeast ms γs (uint.Z ai) ∗
      epAppliedIAddr ep ↦ ai ∗ epAppliedTAddr ep ↦ at' ∗ epConfState ep cs ∗
      applyThread γ st ∗ applyBackend γ ci b ∗ ciApplying ci a t ∗ srvLgReader s ∗ srvApplyKVCore s E γw x ua }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"snapshot")) (Val #ep))
      (Val #toDisk))
  {{ RET #(); ∃ st' : ApplyState, srvSnapState s ep ms γs ai ai ∗
      epAppliedIAddr ep ↦ ai ∗ epAppliedTAddr ep ↦ at' ∗ epConfState ep cs ∗
      applyThread γ st' ∗ applyBackend γ ci b ∗ ciApplying ci a t ∗ srvLgReader s ∗ srvApplyKVCore s E γw x ua ∗
      ⌜loopOk γ st' ai ∧ ciEff γ st'.k = ciEff γ st.k⌝ }}

end spec

end EtcdGrove
end Perennial

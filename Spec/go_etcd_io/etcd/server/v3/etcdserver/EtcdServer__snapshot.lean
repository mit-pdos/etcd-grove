/-
`s.snapshot(ep, toDisk)` (`server.go`): the trust boundary (names-only). Lean-first (no Rocq
counterpart); the request path's unit 4b (2026-10-13).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplyAll

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
(`srvApplyKV`), the backend, the applying index unchanged, may load the consistent index (the
protocol's state keeps `loopOk` and `ciEff`), and may move the snapshot state (`ep`'s snapshot
indices, `forceDiskSnapshot`). -/
abbrev EtcdServer.snapshot.spec : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (γw : GName) (γ : ApplyNames) (ci : Loc) (b : GoInterface) (ep : Loc)
    (st : ApplyState) (ai at' : w64) (cs : Loc) (a t : w64) (x : apply.ApplyKV) (toDisk : Bool),
  loopOk γ st ai →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ srvSnapState s ep ∗
      epAppliedIAddr ep ↦ ai ∗ epAppliedTAddr ep ↦ at' ∗ epConfStateAddr ep ↦ cs ∗
      applyThread γ st ∗ applyBackend γ ci b ∗ ciApplying ci a t ∗ srvLgReader s ∗ srvApplyKV s E γw x }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"snapshot")) (Val #ep))
      (Val #toDisk))
  {{ RET #(); ∃ st' : ApplyState, srvSnapState s ep ∗
      epAppliedIAddr ep ↦ ai ∗ epAppliedTAddr ep ↦ at' ∗ epConfStateAddr ep ↦ cs ∗
      applyThread γ st' ∗ applyBackend γ ci b ∗ ciApplying ci a t ∗ srvLgReader s ∗ srvApplyKV s E γw x ∗
      ⌜loopOk γ st' ai ∧ ciEff γ st'.k = ciEff γ st.k⌝ }}

end spec

end EtcdGrove
end Perennial

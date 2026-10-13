/-
`s.snapshotIfNeededAndCompactRaftLog(ep)` (`server.go`). Lean-first (no Rocq counterpart); the request path's unit 4b
(2026-10-13).
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

/-- `s.snapshotIfNeededAndCompactRaftLog(ep)`, by the apply thread: if a disk or in-memory
snapshot is due, `snapshot` and `compactRaftLog` (contracts); the applied index, term and conf
state, the KV and the backend are left as they are, the protocol's state keeps `loopOk` and
`ciEff`. -/
abbrev EtcdServer.snapshotIfNeededAndCompactRaftLog.spec : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (γ : ApplyNames) (ci : Loc) (b : GoInterface) (γr : ReadNames)
    (ep : Loc) (st : ApplyState) (ai at' : w64) (cs : Loc) (a t : w64) (x : apply.ApplyKV),
  loopOk γ st ai →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerApplyAll s γr ∗ srvSnapState s ep ∗
      epAppliedIAddr ep ↦ ai ∗ epAppliedTAddr ep ↦ at' ∗ epConfStateAddr ep ↦ cs ∗
      applyThread γ st ∗ applyBackend γ ci b ∗ ciApplying ci a t ∗ srvLgReader s ∗ srvApplyKV s E x }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"snapshotIfNeededAndCompactRaftLog"))
      (Val #ep))
  {{ RET #(); ∃ st' : ApplyState, srvSnapState s ep ∗
      epAppliedIAddr ep ↦ ai ∗ epAppliedTAddr ep ↦ at' ∗ epConfStateAddr ep ↦ cs ∗
      applyThread γ st' ∗ applyBackend γ ci b ∗ ciApplying ci a t ∗ srvLgReader s ∗ srvApplyKV s E x ∗ ⌜loopOk γ st' ai ∧ ciEff γ st'.k = ciEff γ st.k⌝ }}

end spec

end EtcdGrove
end Perennial

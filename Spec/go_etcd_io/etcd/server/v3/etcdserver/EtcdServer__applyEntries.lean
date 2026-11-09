/-
`(*EtcdServer).applyEntries(ep, apply)` (`server.go:1210-1234`): apply the batch's committed entries
past the applied index, record the new applied index and term, and schedule the stop if the member
was removed.

**Users**: `applyAll` (`server.go:981`). Snippet `apply.go` (`ReqWriteAnswered`).

**Proof sketch**. No entries: return. `firsti = B.base + 1` (R1's `BatchOk`: committed entries follow
the delivered ones; with a snapshot there are none), so neither the "unexpected committed entry
index" panic nor the skip of already-applied entries happens (`ep.appliedi + 1 - firsti = 0`);
`apply.spec` with the batch's entries (`Raft.entriesRO`, `committedLb`) and its `raftAdvancedC`
(`advancedChan`'s close: `nodeAdvanced r B.last`); store the returned index and term into `ep`
(`applyThread_at`); if removed, `go s.stopWithDelay(...)` (2e's stop path: an attached goroutine
that sends the stop request).

**Changes** from `specs-ref`'s `applyEntries.specBatch`: over `applyThread`/`applyBatch` (was the
window `kvBatchR`, the restart point, the auth component, the write-token pool `srvWTPool`).

**Margin**: none beyond the applied index.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiApply

set_option autoImplicit false
set_option linter.iris.dupNamespace false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdServer

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

/-- **Apply the batch's entries**: the applied index moves to the batch's end. -/
def EtcdServer.applyEntries.spec : Prop :=
  ∀ (s : Loc) (γ : Names) (id : w64) (ep ap : Loc)
    (apv : go_etcd_io.etcd.server.v3.etcdserver.toApply) (p : Progress) (B : ApplyBatch),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvNode s γ id ∗ applyThread s γ ep p ∗ ap ↦□ apv ∗
      applyBatch (structFieldRef go_etcd_io.etcd.server.v3.etcdserver.EtcdServer go!"r" s) γ apv B
        true ∗
      ⌜uint.nat p.appliedi = B.base⌝ }}
    (App (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!!
      go!"applyEntries")) (Val #ep)) (Val #ap))
  {{ RET #(); ∃ p', applyThread s γ ep p' ∗
      applyBatch (structFieldRef go_etcd_io.etcd.server.v3.etcdserver.EtcdServer go!"r" s) γ apv B
        true ∗
      ⌜uint.nat p'.appliedi = B.last⌝ }}

end spec
end EtcdServer
end EtcdGrove
end Perennial

/-
`concurrency.Election.Observe(ctx)` (`client/v3/concurrency/election.go`). Lean-first (no Rocq counterpart); see
`InvElection.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.concurrency.InvElection

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace concurrency

open Iris Iris.BI go_etcd_io.etcd.client.v3.concurrency go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

/-- **`e.Observe(ctx)`**, for a cancelable context, knowing etcd has reached `lo ≥ 0` (`0` is always
known: `etcdReached_zero`; `observe` watches from its gets' revisions, which `Watch` needs
non-negative): a channel of
`*GetResponse`s (an SPSC channel, `isObserveChan`; the caller receives) fed by a goroutine
(`observe`): the `i`-th response's key-value `v` was observed at a revision `R` (`observedAt`:
in etcd's state at `R`, and the leader there, or the two weaker facts of a watch that skipped
events), with the `R`s non-decreasing from `lo` (`γ.revs`). The channel may be closed at any time
(it is closed when `observe` returns: on any error, a closed watch, or the context's end). -/
abbrev Election.Observe.spec : Prop :=
  ∀ (e s : Loc) (γs : SessionNames) (client : Loc) (id : w64) (pfx : GoString)
    (ctx : GoInterfaceOk) (cs : context.ContextDesc (IProp GF)) (lo : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ isElection e s γs client id pfx ∗
      context.isContext ctx cs ∗ context.isCancelCtxCtx ctx cs ∗ etcdReached lo ∗
      ⌜0 ≤ sint.Z lo⌝ }}
    (App (Val (e @!! go.GoType.PointerType Election.ty @!! go!"Observe")) (Val #(GoInterface.ok ctx)))
  {{ (ch : Loc), RET #ch; ∃ γ : ObserveNames, isObserveChan ch γ pfx ∗
      spscConsumer γ.spsc ([] : List Loc) ∗ monoListIdxOwn γ.revs 0 lo }}

end spec

end concurrency
end EtcdGrove
end Perennial

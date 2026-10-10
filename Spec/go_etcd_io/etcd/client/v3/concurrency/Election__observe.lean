/-
`concurrency.Election.observe(ctx, ch)` (`client/v3/concurrency/election.go`). Lean-first (no Rocq counterpart); see
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

/-- **`e.observe(ctx, ch)`** (`Observe`'s goroutine), for a cancelable context, as the producer of
`Observe`'s channel `ch` having sent `sent`, with the revisions `L` (`L.length = sent.length + 1`,
the last, `Rl`, reached by etcd): every response it sends satisfies `observeElem` (its fact's
revision at least the previous one's), and it closes the channel when it returns. -/
abbrev Election.observe.spec : Prop :=
  ∀ (e s : Loc) (γs : SessionNames) (client : Loc) (id : w64) (pfx : GoString)
    (ctx : GoInterfaceOk) (cs : context.ContextDesc (IProp GF)) (ch : Loc) (γ : ObserveNames)
    (sent : List Loc) (L : List w64) (Rl : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ isElection e s γs client id pfx ∗
      context.isContext ctx cs ∗ context.isCancelCtxCtx ctx cs ∗ isObserveChan ch γ pfx ∗
      spscProducer γ.spsc sent ∗ monoListAuthOwn γ.revs 1 L ∗ etcdReached Rl ∗
      ⌜L.length = sent.length + 1 ∧ L.getLast? = some Rl⌝ }}
    (App (App (Val (e @!! go.GoType.PointerType Election.ty @!! go!"observe"))
      (Val #(GoInterface.ok ctx))) (Val #ch))
  {{ RET #(); True }}

end spec

end concurrency
end EtcdGrove
end Perennial

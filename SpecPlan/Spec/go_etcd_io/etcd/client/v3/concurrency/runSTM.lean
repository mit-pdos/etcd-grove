/-
`concurrency.runSTM(s, apply)` (`client/v3/concurrency/stm.go`), internal.

Users: `NewSTM`.

Proof sketch: a buffered channel (capacity 1: a one-shot future); `go` (`wp_fork`, no token from
the caller): under `with_defer_recover`, the loop carries `stmStale` and `∃ b, F b`: `reset`
(`STM.ResetTriple`), `apply` (`applyOk`): an error ends the loop with `nil` response; `nil` (an
attempt `a` with `Rel a`, `F a`): `commit` (`STM.CommitTriple` with the lent permission and its token, `stmEff ⊆ T`
and `Rel a` giving its premise): `nil` (a failed comparison), again; a response, the end with
`stmCommitted` and `F a`. An abort (`stmRet`'s panic `stmError{err}`) is recovered by the
deferred function into `(nil, err)`, `F` back (the closure's abort keeps it; the methods' aborts
inside the commit keep nothing else). The main thread receives the one result.

Changes: from `specs-ref`'s `runSTM.lean`: over `stmStale`, `stmResult`; the frame `F`.

Margin: a closure that panics with anything else crashes the program (`panic(r)` again): the
closure's contract (`applyOk`) excludes it.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.client.v3.concurrency.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Concurrency

open Iris Iris.BI EtcdModel EtcdWire ClientV3
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

/-- `runSTM(s, apply)`: attempts until one commits or fails; the result as `NewSTM`'s. -/
def runSTM.spec : Prop :=
  ∀ (iv : GoInterface) (γ : Cluster) (dflt who : Principal) (iso : w64) (apply : GoFunc)
    (F : Attempt → IProp GF) (Rel : Attempt → Prop) (T : State → State → Prop) (P : IProp GF) (σ0 : State),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ stmStale iv γ who iso ∗ applyOk apply γ who F Rel ∗ (∃ b, F b) ∗ etcdLent γ T P ∗ P ∗ etcdLb γ σ0 ∗ ⌜effIn (stmEff iso Rel) T⌝ }}
    (App (App (Val (@! go_etcd_io.etcd.client.v3.concurrency.runSTM)) (Val #iv)) (Val #apply))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); stmResult γ iso F Rel P σ0 resp err }}

end spec

end Concurrency
end EtcdGrove
end Perennial

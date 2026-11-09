/-
`concurrency.NewSTMReadCommitted(ctx, c, apply)` (`client/v3/concurrency/stm.go`), deprecated.

Users: etcd's tests (`tests/integration/clientv3/concurrency/example_stm_test.go`: a
transfer between accounts keeping their sum, `NewSTM` with the default level;
`tests/integration/clientv3/experimental/recipes/v3_stm_test.go`-style uses: every level,
`WithPrefetch`, `WithAbortContext`, an aborted closure), etcd's benchmark tool (`tools/benchmark`,
not in the pinned sources). No production caller in the pinned etcd, raft, Kubernetes or
`examples/`. Snippet: `concurrency/stm.go` (`ReqSTMLevels`).

Proof sketch: `WithAbortContext.spec`, `WithIsolation.spec`, a two-element slice, `NewSTM.spec`.

Changes: from `specs-ref`'s `NewSTMReadCommitted.lean`: as `NewSTM`.

Margin: as `NewSTM`.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.concurrency.Api

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

/-- `NewSTMReadCommitted(ctx, c, apply)`: `NewSTM` at `ReadCommitted` with the abort context `ctx`. -/
def NewSTMReadCommitted.spec : Prop :=
  ∀ (ctx : GoInterface) (c : Loc) (γ : Cluster) (who : Principal) (apply : GoFunc)
    (F : Attempt → IProp GF) (Rel : Attempt → Prop) (T : State → State → Prop) (P : IProp GF) (σ0 : State),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ isClient c γ who ∗ Context.ctxOk ctx ∗ ctxPrin ctx who ∗ applyOk apply γ who F Rel ∗ (∃ b, F b) ∗ etcdLent γ T P ∗ P ∗ etcdLb γ σ0 ∗
      ⌜effIn (stmEff isoRC Rel) T⌝ }}
    (App (App (App (Val (@! go_etcd_io.etcd.client.v3.concurrency.NewSTMReadCommitted)) (Val #ctx)) (Val #c)) (Val #apply))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); stmResult γ isoRC F Rel P σ0 resp err }}

end spec

end Concurrency
end EtcdGrove
end Perennial

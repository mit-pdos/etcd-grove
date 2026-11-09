/-
`concurrency.WithIsolation(lvl)` (`client/v3/concurrency/stm.go`).

Users: etcd's tests (`tests/integration/clientv3/concurrency/example_stm_test.go`: a
transfer between accounts keeping their sum, `NewSTM` with the default level;
`tests/integration/clientv3/experimental/recipes/v3_stm_test.go`-style uses: every level,
`WithPrefetch`, `WithAbortContext`, an aborted closure), etcd's benchmark tool (`tools/benchmark`,
not in the pinned sources). No production caller in the pinned etcd, raft, Kubernetes or
`examples/`. Snippet: `concurrency/stm.go` (`ReqSTMLevels`).

Proof sketch: a closure writing the field.

Changes: from `specs-ref`'s `WithIsolation.lean`: restated over `stmOptAt`.

Margin: none.
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

/-- `WithIsolation(lvl)`: an option setting the level. -/
def WithIsolation.spec : Prop :=
  ∀ (iso : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency }}
    (App (Val (@! go_etcd_io.etcd.client.v3.concurrency.WithIsolation)) (Val #iso))
  {{ (f : GoFunc), RET #f; stmOptAt f (withIsolationM iso) }}

end spec

end Concurrency
end EtcdGrove
end Perennial

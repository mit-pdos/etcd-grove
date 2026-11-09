/-
`gatherResponseOps` (`util.go`): each transaction among `ops` replaced by the operations of the
branch its response took. Stated one level deep (`gatherRespOk`: what `commitToCache` passes; a
non-transaction response at a transaction's index would be a nil dereference). Changes: over W0's
messages and `gatherRespM` (was `OpT.chosenL`).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.Internal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Leasing

open Iris Iris.BI EtcdModel EtcdWire ClientV3
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

/-- `gatherResponseOps(resps, ops)`. -/
def gatherResponseOps.spec : Prop :=
  ∀ (rsl : GoSlice) (dq : DFrac) (ms : List ResponseOpM) (ops : GoSlice) (os : List OpM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ msgsOwn responseOpOwn rsl dq ms ∗ opsAt ops os ∗ ⌜gatherRespOk ms os⌝ }}
    (App (App (Val (@! go_etcd_io.etcd.client.v3.leasing.gatherResponseOps)) (Val #rsl)) (Val #ops))
  {{ (ret : GoSlice), RET #ret; msgsOwn responseOpOwn rsl dq ms ∗ opsAt ops os ∗
      opsAt ret (gatherRespM ms os) }}

end spec

end Leasing
end EtcdGrove
end Perennial

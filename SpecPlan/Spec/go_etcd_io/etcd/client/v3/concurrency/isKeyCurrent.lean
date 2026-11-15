/-
`concurrency.isKeyCurrent(k, r)` (`client/v3/concurrency/stm.go`), internal.

Users: `readSet.cmps`.

Proof sketch: `ModRevision.spec`, `Compare.spec` with the first key-value's mod revision (an
`int64`) or `0` (an `int`): the same comparison.

Changes: from `specs-ref`'s `isKeyCurrent.lean`: restated.

Margin: none.
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

/-- `isKeyCurrent(k, r)`: the comparison `ModRevision(k) = ` the read's mod revision (`0` if absent). -/
def isKeyCurrent.spec : Prop :=
  ∀ (k : GoString) (p : Loc) (e : ReadM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ readRespAt p e }}
    (App (App (Val (@! go_etcd_io.etcd.client.v3.concurrency.isKeyCurrent)) (Val #k)) (Val #p))
  {{ (c : go_etcd_io.etcd.client.v3.Cmp), RET #c; cmpAt c (some (curCmp k e)) }}

end spec

end Concurrency
end EtcdGrove
end Perennial

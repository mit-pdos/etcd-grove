/-
`(concurrency.readSet).add` (`client/v3/concurrency/stm.go`), internal.

Users: the STM's methods and commits (`stm.go`).

Proof sketch: a loop over the responses: `ResponseOp.GetResponseRange` (3h), the map's store.

Changes: from `specs-ref`'s `readSet__add.lean`: restated over `readSetAt` and the `Attempt` model.

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

/-- `rs.add(keys, txnresp)`: the `i`-th response's range recorded as the `i`-th key's read. -/
def readSet.add.spec : Prop :=
  ∀ (rs : GoMap) (γ : Cluster) (reads : Key → Option ReadM) (sl : GoSlice) (ks : List GoString)
    (resp : Loc) (m : TxnRespM) (es : List ReadM) (σ : State),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ readSetAt rs γ reads ∗ sl ↦*□ ks ∗ txnRespOwn resp DFrac.discard m ∗ etcdLb γ σ ∗
      ⌜respReads m es ∧ es.length = ks.length ∧
        ∀ (i : Nat) k e, ks[i]? = some k → es[i]? = some e → readOf σ.kv k e⌝ }}
    (App (App (Val (rs @!! go_etcd_io.etcd.client.v3.concurrency.readSet.ty @!! go!"add")) (Val #sl)) (Val #resp))
  {{ RET #(); readSetAt rs γ (addReads reads (ks.zip es)) }}

end spec

end Concurrency
end EtcdGrove
end Perennial

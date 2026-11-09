/-
`(*concurrency.stm).Put` (`client/v3/concurrency/stm.go`), internal: the STM's method.

Users: the user's closure through `STM` (`stmAt_methods`), `runSTM`, `stmSerializable`'s methods.

Proof sketch: `OpPut.spec` (premise `¬ putPanics`), the map insert of `stmPut{val, op}`.

Changes: from `specs-ref`'s `stm__Put.lean`: restated over `stmCoreAt` and the `Attempt` model.

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

/-- `s.Put(key, val, opts...)`: the put in the write set. -/
def stm.Put.spec : Prop :=
  ∀ (p : Loc) (γ : Cluster) (dflt who : Principal) (iso : w64) (a : Attempt) (gs : List (OpM → OpM)) (k v : GoString) (opts : GoSlice) (ogs : List (OpM → OpM)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ stmCoreAt p γ who iso a gs ∗ optsAt opts ogs ∗ ⌜¬ (opPutM k v ogs).putPanics⌝ }}
    (App (App (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.concurrency.stm.ty @!! go!"Put")) (Val #k)) (Val #v)) (Val #opts))
  {{ RET #(); optsAt opts ogs ∗ stmCoreAt p γ who iso
      { a with writes := fun k' => if k' = k then some (.put (opPutM k v ogs).putReq) else a.writes k' } gs }}

end spec

end Concurrency
end EtcdGrove
end Perennial

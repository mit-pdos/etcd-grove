/-
`(*concurrency.stmSerializable).gets` (`client/v3/concurrency/stm.go`), internal: the STM's method.

Users: the user's closure through `STM` (`stmAt_methods`), `runSTM`, `stmSerializable`'s methods.

Proof sketch: a loop over the read set: `OpGet.spec` per key, two `append`s.

Changes: from `specs-ref`'s `stmSerializable__gets.lean`: restated over `stmSerAt` and the `Attempt` model.

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

/-- `s.gets()`: the read keys and a plain get of each, in the map's order. -/
def stmSerializable.gets.spec : Prop :=
  ∀ (p : Loc) (γ : Cluster) (dflt who : Principal) (iso : w64) (a : Attempt),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ stmSerAt p γ who iso a }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.concurrency.stmSerializable.ty @!! go!"gets")) (Val #()))
  {{ (ksl osl : GoSlice), RET (PairV #ksl #osl); stmSerAt p γ who iso a ∗ ∃ ks : List GoString,
      ⌜keysOf a.reads ks⌝ ∗ ksl ↦*□ ks ∗ opsAt osl (ks.map (fun k => opGetM k [])) }}

end spec

end Concurrency
end EtcdGrove
end Perennial

/-
`(*concurrency.stmSerializable).Get` (`client/v3/concurrency/stm.go`), internal: the STM's method.

Users: the user's closure through `STM` (`stmAt_methods`), `runSTM`, `stmSerializable`'s methods.

Proof sketch: `writeSet.get.spec`; the prefetched responses moved to the read set; `stm.fetch.spec` on the embedded `stm`; on the first read, the gets' options set to `WithRev(header), WithSerializable()` (`WithRev.spec`, `WithSerializable.spec`); `respToValue.spec`.

Changes: from `specs-ref`'s `stmSerializable__Get.lean`: restated over `stmSerAt` and the `Attempt` model.

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

/-- `s.Get(keys...)` (serializable levels): `GetPost`, or the abort; the first read fixes the revision of the attempt's later reads. -/
def stmSerializable.Get.spec : Prop :=
  ∀ (p : Loc) (γ : Cluster) (dflt who : Principal) (iso : w64) (a : Attempt) (sl : GoSlice) (ks : List GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ stmSerAt p γ who iso a ∗ sl ↦*□ ks }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.concurrency.stmSerializable.ty @!! go!"Get")) (Val #sl))
  {{ (r : val), RET r; stmRet r (fun v : GoString => iprop(∃ a',
      stmSerAt p γ who iso a' ∗ ⌜GetPost ks a v a'⌝)) iprop(True) }}

end spec

end Concurrency
end EtcdGrove
end Perennial

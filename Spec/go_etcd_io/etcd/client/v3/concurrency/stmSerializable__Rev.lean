/-
`(*concurrency.stmSerializable).Rev` (`client/v3/concurrency/stm.go`), internal: the STM's method.

Users: the user's closure through `STM` (`stmAt_methods`), `runSTM`, `stmSerializable`'s methods.

Proof sketch: `stmSerializable.Get.spec` on `[key]` (its value dropped), then `stm.Rev.spec` on the embedded `stm`.

Changes: from `specs-ref`'s `stmSerializable__Rev.lean`: restated over `stmSerAt` and the `Attempt` model.

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

/-- `s.Rev(key)` (serializable levels): `RevPost`, or the abort. -/
def stmSerializable.Rev.spec : Prop :=
  ∀ (p : Loc) (γ : Cluster) (who : Principal) (iso : w64) (a : Attempt) (k : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ stmSerAt p γ who iso a }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.concurrency.stmSerializable.ty @!! go!"Rev")) (Val #k))
  {{ (r : val), RET r; stmRet r (fun rev : w64 => iprop(∃ a',
      stmSerAt p γ who iso a' ∗ ⌜RevPost k a rev a'⌝)) iprop(True) }}

end spec

end Concurrency
end EtcdGrove
end Perennial

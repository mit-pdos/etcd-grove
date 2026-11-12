/-
`(*concurrency.stm).Rev` (`client/v3/concurrency/stm.go`), internal: the STM's method.

Users: the user's closure through `STM` (`stmAt_methods`), `runSTM`, `stmSerializable`'s methods.

Proof sketch: `stm.fetch.spec` on `[key]`; the first key-value's mod revision, or `0`.

Changes: from `specs-ref`'s `stm__Rev.lean`: restated over `stmCoreAt` and the `Attempt` model.

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

/-- `s.Rev(key)`: the key's mod revision as read (`RevPost`), or the abort. -/
def stm.Rev.spec : Prop :=
  ∀ (p : Loc) (γ : Cluster) (dflt who : Principal) (iso : w64) (a : Attempt) (gs : List (OpM → OpM)) (k : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ stmCoreAt p γ who iso a gs }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.concurrency.stm.ty @!! go!"Rev")) (Val #k))
  {{ (r : val), RET r; stmRet r (fun rev : w64 => iprop(∃ a',
      stmCoreAt p γ who iso a' gs ∗ ⌜RevPost k a rev a'⌝)) iprop(True) }}

end spec

end Concurrency
end EtcdGrove
end Perennial

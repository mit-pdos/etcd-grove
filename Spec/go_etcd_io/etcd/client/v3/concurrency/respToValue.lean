/-
`concurrency.respToValue(resp)` (`client/v3/concurrency/stm.go`), internal.

Users: `stm.Get`, `stmSerializable.Get`.

Proof sketch: the nil check, the first key-value's value converted.

Changes: from `specs-ref`'s `respToValue.lean`: restated.

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

/-- `respToValue(resp)`: the read's value, `""` for `nil` or an absent key. -/
def respToValue.spec : Prop :=
  ∀ (p : Loc) (e : Option ReadM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ (match e with | none => iprop(⌜p = null⌝) | some e => readRespAt p e) }}
    (App (Val (@! go_etcd_io.etcd.client.v3.concurrency.respToValue)) (Val #p))
  {{ RET #((e.map ReadM.value).getD []); True }}

end spec

end Concurrency
end EtcdGrove
end Perennial

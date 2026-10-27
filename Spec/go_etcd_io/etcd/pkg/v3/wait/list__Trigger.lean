/-
`(*list).Trigger(id, x)` (`wait.go`). Lean-first (no Rocq counterpart); see `wait/List.lean`.
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.wait.List

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.pkg.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `l.Trigger(id, x)`: with `Ψ x` for every expectation the registration condition allows under
`id` (`waitTrig`), or, for `x = nil`, the consumer token of the channel `id` was registered with:
if `id` is registered, its channel gets `x` (with the token, for `nil`) and is closed. Since
2026-10-20 (linkv-txn stage B1) also with `id`'s registration gone (`waitGone`): then `id` is not
registered, nothing is sent. -/
abbrev wait.list.Trigger.spec : Prop :=
  ∀ (l : Loc) (γi : IdNames) (γw : GName) (R : w64 → (GoInterface → IProp GF) → IProp GF)
    (id : w64) (x : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.wait ∗ waitList l γi γw R ∗
      ((∃ t : GName, waitGone γw id t) ∨
        (∃ γh : HandoffNames, ⌜x = GoInterface.nil⌝ ∗ handoffConsumer γh false ∗
          waitRegd γw id γh.takenName) ∨ waitTrig R id x) }}
    (App (App (Val (l @!! go.GoType.PointerType wait.list'.ty @!! go!"Trigger")) (Val #id))
      (Val #x))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial

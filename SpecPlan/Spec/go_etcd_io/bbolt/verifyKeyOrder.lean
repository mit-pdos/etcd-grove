/-
`verifyKeyOrder(...)` (`tx_check.go`): reports a key out of order on the channel.
(internal; mirrors the code. Round 1, review C8: a proved function of the old tree.)

**Proof sketch** (integration I7). `compareKeys` (`compareKeys.spec`) on the keys, read at their
shares; the premises are the "nothing to report" case (the key after the running minimum, strictly
after it past the first index, before the open maximum), so the channel, `keyToString` and the
stack are never touched.

**Changes** (integration I7): was any nine `val`s, post `True`: false of ill-typed arguments and of a
report. Now the keys typed and owned, and the order premises.
-/
module

public import SpecPlan.Spec.go_etcd_io.bbolt.Internal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Bbolt

open Iris Iris.BI go_etcd_io.bbolt

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- (internal) keys in order (the first not below the running minimum `prev`, a later one
strictly above it, all below the open maximum `mx` when it is not nil): nothing reported. -/
def verifyKeyOrder.spec : Prop :=
  ∀ (pgId : w64) (pageType : GoString) (index : w64) (key prev mx : GoSlice) (kb pb mb : GoString)
    (dk dp dm : DFrac) (ch kts stack : val),
  ((index = W64 0 → prev ≠ slice.nil → ¬ go.GoStringLt kb pb) ∧
    (0 < sint.Z index → go.GoStringLt pb kb) ∧
    (mx ≠ slice.nil → go.GoStringLt kb mb)) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ key ↦*{dk} kb ∗ prev ↦*{dp} pb ∗
      mx ↦*{dm} mb }}
    (App (App (App (App (App (App (App (App (App (Val (@! go_etcd_io.bbolt.verifyKeyOrder)) (Val #pgId)) (Val #pageType)) (Val #index)) (Val #key)) (Val #prev)) (Val #mx)) (Val ch)) (Val kts)) (Val stack))
  {{ RET #(); key ↦*{dk} kb ∗ prev ↦*{dp} pb ∗ mx ↦*{dm} mb }}

end spec

end Bbolt
end EtcdGrove
end Perennial

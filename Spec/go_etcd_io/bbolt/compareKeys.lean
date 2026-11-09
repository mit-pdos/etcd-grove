/-
`compareKeys(l, r)` (`node.go`): `bytes.Compare`.
(internal; mirrors the code. Round 1, review C8: a proved function of the old tree.)
-/
module

public import Spec.go_etcd_io.bbolt.Internal

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

/-- (internal) `-1`, `0` or `1` by `go.GoStringLt`. -/
def compareKeys.spec : Prop :=
  ∀ [HasExt osFsExt] (l r : GoSlice) (lb rb : GoString) (d1 d2 : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ l ↦*{d1} lb ∗ r ↦*{d2} rb }}
    (App (App (Val (@! go_etcd_io.bbolt.compareKeys)) (Val #l)) (Val #r))
  {{ (z : w64), RET #z; l ↦*{d1} lb ∗ r ↦*{d2} rb ∗ ⌜(go.GoStringLt lb rb → sint.Z z = -1) ∧ (lb = rb → z = W64 0) ∧ (go.GoStringLt rb lb → z = W64 1)⌝ }}

end spec

end Bbolt
end EtcdGrove
end Perennial

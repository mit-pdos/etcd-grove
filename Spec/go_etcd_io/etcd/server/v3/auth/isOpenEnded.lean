/-
## `isOpenEnded(rangeEnd)` (internal helper)

**Users.** `checkKeyInterval`, `isValidPermissionRange`.

**Proof sketch.** A length test and an index.

**Changes.** Unchanged.

**Margin.** None.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Auth

open Iris Iris.BI EtcdModel

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- **`isOpenEnded(re)`**: whether the range end is `"\x00"`. -/
def isOpenEnded.spec : Prop :=
  ∀ (re : GoSlice) (de : DFrac) (e : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ re ↦*{de} e }}
    (App (Val (@! go_etcd_io.etcd.server.v3.auth.isOpenEnded)) (Val #re))
  {{ (b : Bool), RET #b; re ↦*{de} e ∗ ⌜b = decide (e = [0#8])⌝ }}

end spec
end Auth
end EtcdGrove
end Perennial

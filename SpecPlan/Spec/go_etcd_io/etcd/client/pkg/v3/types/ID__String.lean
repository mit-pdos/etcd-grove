/-
`types.ID.String` (`client/pkg/v3/types/id.go`).

Users: the server and the client's logs (member ids).

Proof sketch: `strconv.FormatUint(uint64(i), 16)`.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/pkg/v3/types/ID__String.lean`.

Margin: none.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.client.pkg.v3.types.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Types

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.pkg.v3.types.Assumptions]

/-- `ID(x).String()`: `idStr x`. -/
def ID.String.spec : Prop :=
  ∀ (x : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.types }}
    (App (Val (x @!! go_etcd_io.etcd.client.pkg.v3.types.ID.ty @!! go!"String")) (Val #()))
  {{ (s : GoString), RET #s; ⌜s = idStr x⌝ }}

end spec

end Types
end EtcdGrove
end Perennial

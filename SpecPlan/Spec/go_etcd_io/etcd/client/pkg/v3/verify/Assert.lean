/-
`verify.Assert` (`client/pkg/v3/verify/verify.go`).

Users: the server (2d, 3e).

Proof sketch: a `true` condition: nothing.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/pkg/v3/verify/Assert.lean`.

Margin: none.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.client.pkg.v3.verify.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Verify

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `Assert(true, msg, v...)`: nothing. -/
def Assert.spec : Prop :=
  ∀ (msg : GoString) (v : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.verify }}
    (App (App (App (Val (@! go_etcd_io.etcd.client.pkg.v3.verify.Assert)) (Val #true)) (Val #msg))
      (Val #v))
  {{ RET #(); True }}

end spec

end Verify
end EtcdGrove
end Perennial

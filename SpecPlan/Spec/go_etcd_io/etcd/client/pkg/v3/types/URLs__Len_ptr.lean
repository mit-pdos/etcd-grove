/-
`(*types.URLs).Len` (`client/pkg/v3/types/urls.go`: a value method called through a pointer).

Users: rafthttp's `setPeerURLsHeader`.

Proof sketch: the wrapper loads `*p` (any fraction, kept); `len(us)`.

Changes: new (verify round, A2-completeness S4: only the value forms had specs).

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

/-- `p.Len()` of a `*URLs`: the slice's length. -/
def URLs.Len_ptr.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (us : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.types ∗ p ↦{dq} us }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.client.pkg.v3.types.URLs.ty @!! go!"Len"))
      (Val #()))
  {{ (n : w64), RET #n; p ↦{dq} us ∗ ⌜n = us.len⌝ }}

end spec

end Types
end EtcdGrove
end Perennial

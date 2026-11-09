/-
`(*types.URLs).StringSlice` (`client/pkg/v3/types/urls.go`: a value method called through a
pointer; Goose's wrapper loads the slice header and calls it).

Users: `NewServer` (`(*URLs).StringSlice` of the configuration's URLs).

Proof sketch: the wrapper loads `*p` (any fraction, kept), then `URLs.StringSlice.spec`.

Changes: new (verify round, A2-completeness S4: only the value forms had specs).

Margin: none.
-/
module

public import Spec.go_etcd_io.etcd.client.pkg.v3.types.Api

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

/-- `p.StringSlice()` of a `*URLs`: as the value method's, the slice at `p` kept. -/
def URLs.StringSlice_ptr.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (us : GoSlice) (ss : List GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.types ∗ p ↦{dq} us ∗
      urlsStrs us ss }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.client.pkg.v3.types.URLs.ty @!! go!"StringSlice"))
      (Val #()))
  {{ (sl : GoSlice), RET #sl; p ↦{dq} us ∗ sl ↦* ss }}

end spec

end Types
end EtcdGrove
end Perennial

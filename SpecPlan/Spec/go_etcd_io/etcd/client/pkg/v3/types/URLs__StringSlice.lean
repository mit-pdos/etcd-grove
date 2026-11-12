/-
`types.URLs.StringSlice` (`client/pkg/v3/types/urls.go`).

Users: the server (membership: a member's URL strings, 2e).

Proof sketch: a fresh slice, each URL's `String()` (`net/url`, trusted).

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/pkg/v3/types/URLs__StringSlice.lean`.

Changes (integration I1): over `urlsStrs` (2e's request: the member's URL strings), the strings
described.

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

/-- `us.StringSlice()`: a fresh slice of the URLs' `String()` forms. -/
def URLs.StringSlice.spec : Prop :=
  ∀ (us : GoSlice) (ss : List GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.types ∗ urlsStrs us ss }}
    (App (Val (us @!! go_etcd_io.etcd.client.pkg.v3.types.URLs.ty @!! go!"StringSlice")) (Val #()))
  {{ (sl : GoSlice), RET #sl; sl ↦* ss }}

end spec

end Types
end EtcdGrove
end Perennial

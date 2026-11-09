/-
`types.URLs.StringSlice` (`client/pkg/v3/types/urls.go`).

Users: the server (membership: a member's URL strings, 2e).

Proof sketch: a fresh slice, each URL's `String()` (`net/url`, trusted).

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/pkg/v3/types/URLs__StringSlice.lean`.

Margin: the strings are not described.
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

/-- `us.StringSlice()`: a fresh slice of strings, one per URL. -/
def URLs.StringSlice.spec : Prop :=
  ∀ (us : GoSlice) (dq : DFrac) (uvs : List net.url.URL),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.types ∗ us ↦*{dq} uvs }}
    (App (Val (us @!! go_etcd_io.etcd.client.pkg.v3.types.URLs.ty @!! go!"StringSlice")) (Val #()))
  {{ (sl : GoSlice), RET #sl; us ↦*{dq} uvs ∗
      ∃ ss : List GoString, sl ↦* ss ∗ ⌜ss.length = uvs.length⌝ }}

end spec

end Types
end EtcdGrove
end Perennial

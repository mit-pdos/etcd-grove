/-
`metadata.New(m)` (grpc-go, assumed: `metadata/metadata.go`).

Users: the auth store's `WithRoot` (`auth/store.go`: `metadata.New(map[string]string{rpctypes.
TokenFieldNameGRPC: tok})`, 3d), the gateway.

Why true: allocates a fresh `MD` and, for each pair of `m`, appends the value under the lowercased
key (`strings.ToLower`). Reads `m` only.

Changes: new (integration I3, 3d's request).

Margin: the order of a key's values when two keys of `m` lowercase alike is the map's iteration
order: the post says only which values a key has.
-/
module

public import Spec.google_golang_org.grpc.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Grpc

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : google_golang_org.grpc.metadata.Assumptions]

/-- `metadata.New(m)`: a fresh metadata map holding, under each lowercased key, exactly the values
of `m`'s keys that lowercase to it; `m` given back. -/
def New.spec : Prop :=
  ∀ (m : Loc) (dq : DFrac) (mm : GMap GoString GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.metadata ∗ ownMap m dq mm }}
    (App (Val (@! google_golang_org.grpc.metadata.New)) (Val #m))
  {{ (r : Loc), RET #r; ownMap m dq mm ∗ ∃ md : MD, mdAt r (DFrac.own 1) md ∗
      ⌜(∀ k v, mm.lookup k = some v → v ∈ md.get (lowerKey k)) ∧
       (∀ k' v, v ∈ md.get k' → ∃ k, lowerKey k = k' ∧ mm.lookup k = some v) ∧
       (∀ e ∈ md, e.2 ≠ [])⌝ }}

end spec

end Grpc
end EtcdGrove
end Perennial

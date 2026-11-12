/-
`proto.Merge(dst, src)` (protobuf-go, assumed: `proto/merge.go`).

Users: the client's `GetStreamToGetResponse` (`kv.go:105`, W0: each streamed chunk merged into one
`RangeResponse`).

Why true: `Merge` appends the source's repeated fields to the destination's, overwrites the set
scalars and merges the set submessages, copying (no aliasing of the source's bytes or
submessages, which are cloned); it writes the destination only.

Changes: new (no old spec: the client's streamed `Get` is new on this branch). Round 1 (3h's review
F1): the destination is a `mergeDst` (protobuf-go writes it in place: appends into its repeated
fields' capacity, merges into its set submessages), not any `msgAt (own 1)`.

Margin: what `merge` is for a given type is its owner's law (3h: a `RangeResponse`'s `Kvs`
appended, `Header`, `More`, `Count` taken when set).
-/
module

public import SpecPlan.Spec.google_golang_org.protobuf.proto.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Proto

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : google_golang_org.protobuf.proto.Assumptions]

/-- `proto.Merge(dst, src)` into a merge destination (`mergeDst`: owned with its slices'
capacity and its submessages writable): it holds `merge c c'` and stays a destination; `src` read
and given back. -/
def Merge.spec : Prop :=
  ∀ (t : go.GoType) (p q : Loc) (dq : DFrac) (c c' : Content),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto ∗ mergeDst t p c ∗ msgAt t q dq c' ∗ ⌜depth c < depthMax ∧ depth c' < depthMax⌝ }}
    (App (App (Val (@! google_golang_org.protobuf.proto.Merge)) (Val #(msgVal t p))) (Val #(msgVal t q)))
  {{ RET #(); mergeDst t p (merge c c') ∗ msgAt t q dq c' }}

end spec

end Proto
end EtcdGrove
end Perennial

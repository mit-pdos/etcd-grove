/-
`proto.Equal` of two non-nil `*spb.Status` (genproto's `google.rpc.Status`): the trust boundary
(protobuf's `proto` is names-only; `Equal` works by reflection), narrowed to what
`(*internal/status.Error).Is` (`internal/status/status.go:222-228`) needs: a `true` result means
equal codes and messages. Lean-first (no Rocq counterpart). Route: a Go model of `Equal` restricted
to `*spb.Status` in #37's protobuf models if those are wired for `proto` before reflection S0/S0.5,
else the translation of `proto/equal.go` over the reflect models (`notes/axiom-review/
proto-equal-status.md`).
-/
module

public import Proof.google_golang_org.grpc.status.StatusRO
public import Proof.google_golang_org.protobuf.PkgInit

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : google_golang_org.protobuf.proto.Assumptions]

/-- `proto.Equal(p, q)` of two non-nil `*spb.Status` (as `proto.Message`s), each read-only
(`status.pbStatusRO`: the fields `Equal` reads, `Code`, `Message`, `unknownFields`, `Details` and its
`Any`s', hold their values for good, so no writer races the reads; the spec needs that read
permission on both; and their unknown fields are what protobuf-go's decoder leaves, `ufWire`, on which
`equalUnknown`'s parse cannot fail) returns some `b` without panicking or blocking, and touches neither message but
to read it; `b = true` only if the codes and the messages are equal (protobuf-go v1.36.12
`proto/equal.go:39-64`: identical pointers, or `internal/impl/equal.go:22-133`'s field-by-field
comparison, which returns `false` at a populated field present in one only or of unequal values).
Nothing about `false` (it may come from `Details` or unknown fields), nothing about `Details`. -/
abbrev proto.EqualStatus.spec : Prop :=
  ∀ (p q : Loc) (c c' : w32) (m m' : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto ∗
      status.pbStatusRO p c m ∗ status.pbStatusRO q c' m' }}
    (App (App (Val (@! google_golang_org.protobuf.proto.Equal))
      (Val #(interface.mkOk
        (go.GoType.PointerType google_golang_org.genproto.googleapis.rpc.status.Status.ty) #p)))
      (Val #(interface.mkOk
        (go.GoType.PointerType google_golang_org.genproto.googleapis.rpc.status.Status.ty) #q)))
  {{ (b : Bool), RET #b; ⌜b = true → c = c' ∧ m = m'⌝ }}

end spec

end EtcdGrove
end Perennial

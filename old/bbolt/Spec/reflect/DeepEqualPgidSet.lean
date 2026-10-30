/-
`reflect.DeepEqual(a, b)` on two `map[common.Pgid]struct{}` values, as `hashMap.mergeSpans`'s
optional check calls it (bbolt's; `Spec/reflect/DeepEqual.lean` is the Raft proof's, on
`ConfState`s).
-/
module
public import Proof.go_etcd_io.bbolt.internal.freelist.Model

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt.internal.freelist

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

/-- **Trust boundary.** `reflect.DeepEqual` is Go reflection, which Goose does not model
(`reflect` is translated names-only), so this is an axiom (`Proof/reflect/DeepEqualPgidSet.lean`):
Go's `DeepEqual` on two maps of type `map[common.Pgid]struct{}`, read against
`reflect/deepequal.go`: two non-nil maps (owned maps are not nil) are deeply equal iff they have
the same length and each key of the first is a key of the second with a deeply equal value;
`struct{}` values always are. That is, iff they have the same keys: equal as `GMap`s. -/
abbrev reflect.DeepEqual.spec : Prop :=
  ∀ (m1 m2 : Loc) (M1 M2 : GMap w64 Unit) (dq1 dq2 : DFrac),
  {{ (m1 ↦${dq1} M1 : IProp GF) ∗ m2 ↦${dq2} M2 }}
    (App (App (Val #(functions _root_.Perennial.reflect.DeepEqual []))
      (Val #(interface.mkOk (go.GoType.MapType go_etcd_io.bbolt.internal.common.Pgid.ty
        (go.GoType.StructType [])) #m1)))
      (Val #(interface.mkOk (go.GoType.MapType go_etcd_io.bbolt.internal.common.Pgid.ty
        (go.GoType.StructType [])) #m2)))
  {{ (b : Bool), RET #b; ⌜b = true ↔ M1 = M2⌝ ∗ m1 ↦${dq1} M1 ∗ m2 ↦${dq2} M2 }}

end spec

end bbolt
end EtcdGrove
end Perennial

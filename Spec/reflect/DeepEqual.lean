/-
`reflect.DeepEqual(a, b)` on two `map[common.Pgid]struct{}` (bbolt's `pidSet`'s underlying type;
names-only in Perennial: reflection): deeply equal iff the maps have the same keys. Stated at this
one map type only (`spec_pgidSet`): the map points-to is not indexed by the Go type, so a statement
at any key type would claim results for maps Go never builds. The trust boundary: an axiom,
`Proof/reflect/DeepEqual.lean`. True of Go (`reflect/deepequal.go`): both arguments are non-nil
interfaces of the same dynamic type; for maps, `deepValueEqual` returns `false` if exactly one is
nil, or if their lengths differ, `true` if they are the same map, and otherwise whether every key
of the first is a key of the second with deeply equal values; `struct{}` values are always deeply
equal. Both maps are non-nil here (the map points-to holds a heap cell at the map's location, so
the location is not `map.nil`), so the result is whether the key sets are equal. Needed by bbolt's
`hashMap.mergeSpans` (its `Verify` check panics if the free maps disagree). Moved from bbolt's
`internal/freelist/Lemmas/Callees.lean` (2026-11-05), where it was a hypothesis of the linked
results; the user approved it as trust-boundary assumption. Lean-first.
-/
module

public import Proof.go_etcd_io.bbolt.PkgInit

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

/-- See the file header. -/
abbrev reflect.DeepEqual.spec_pgidSet : Prop :=
  ∀ (m1 m2 : Loc) (M1 M2 : GMap w64 Unit) (dq1 dq2 : DFrac),
  {{ (m1 ↦${dq1} M1 : IProp GF) ∗ m2 ↦${dq2} M2 }}
    (App (App (Val #(functions _root_.Perennial.reflect.DeepEqual []))
      (Val #(interface.mkOk (go.GoType.MapType go_etcd_io.bbolt.internal.common.Pgid.ty
        (go.GoType.StructType [])) #m1)))
      (Val #(interface.mkOk (go.GoType.MapType go_etcd_io.bbolt.internal.common.Pgid.ty
        (go.GoType.StructType [])) #m2)))
  {{ (b : Bool), RET #b; ⌜b = true ↔ M1 = M2⌝ ∗ m1 ↦${dq1} M1 ∗ m2 ↦${dq2} M2 }}

end spec

end EtcdGrove
end Perennial

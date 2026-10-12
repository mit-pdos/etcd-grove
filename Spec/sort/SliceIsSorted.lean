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

/-- `sort.SliceIsSorted(x, less)` on a slice `s` (any element type `t`), `less(i, j)` returning
`lt i j` for indices of `s` and keeping `P`: whether no element is `less` than the one before
it. It is Go's `sort/slice.go` (`for i := n - 1; i > 0; i-- { if less(i, i-1) { return false } }`,
`n` the slice's length, read by reflection): `less` is only called on indices of `s`. `sort` is
translated names-only (reflection); this spec is an axiom (`Proof/sort/SliceIsSorted.lean`). -/
abbrev sort.SliceIsSorted.spec : Prop :=
  ∀ (t : go.GoType) (s : GoSlice) (less : GoFunc) (P : IProp GF) (lt : Nat → Nat → Bool),
  {{ P ∗ □ (∀ (i j : w64) (Φ : val → IProp GF),
        ⌜0 ≤ sint.Z i ∧ sint.Z i < sint.Z s.len ∧ 0 ≤ sint.Z j ∧ sint.Z j < sint.Z s.len⌝ -∗
        P -∗ (P -∗ Φ #(lt (sint.nat i) (sint.nat j))) -∗
        WP (App (App (Val #less) (Val #i)) (Val #j)) {{ Φ }}) }}
    (App (App (Val #(functions _root_.Perennial.sort.SliceIsSorted []))
      (Val #(interface.mkOk (go.GoType.SliceType t) #s))) (Val #less))
  {{ (b : Bool), RET #b;
      ⌜b = true ↔ ∀ i, 0 < i → i < sint.nat s.len → lt i (i - 1) = false⌝ ∗ P }}

end spec

end bbolt
end EtcdGrove
end Perennial

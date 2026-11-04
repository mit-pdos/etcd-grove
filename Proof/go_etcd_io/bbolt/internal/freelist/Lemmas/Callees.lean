/-
Specs of callees that have none yet, which U2's proofs take as hypotheses (`notes/bbolt-proof-plan.md`,
design §5 item 4: "The `common.Verify` closures"):

- `common.Verify(f)` (internal/common, U1's package; the plan leaves it unstated): it runs `f`
  or not, depending on the environment (`getEnvVerify` reads `os.Getenv`).
- `sort.SliceIsSorted` (names-only: reflection), as `hashMap.Init` calls it.
- `reflect.DeepEqual` on two `map[Pgid]struct{}` (names-only: reflection), as `hashMap.mergeSpans`'
  check calls it.

They are stated here, not in `Spec/`, because U2 may not add shared modules; the owner of §5
item 4 moves them to `Spec/` (as trust-boundary specs, or proves `Verify`'s).
-/
module

public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas.Own

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt.internal.freelist

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `Verify(f)` runs the optional check `f` if the environment asks for it: so `Q` must follow
from `f` returning, and hold if it does not run. -/
abbrev common.Verify.spec [go_etcd_io.bbolt.internal.common.Assumptions] : Prop :=
  ∀ (f : GoFunc) (Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗
      (WP (App (Val #f) (Val #())) {{ fun _ => Q }} ∧ Q) }}
    (App (Val #(functions go_etcd_io.bbolt.internal.common.Verify [])) (Val #f))
  {{ RET #(); Q }}

/-- `sort.SliceIsSorted(x, less)` on a slice `s` (element type `t`), `less(i, j)` returning
`lt i j` for indices of `s` and keeping `P`: whether no element is `less` than the one before it
(Go's `sort/slice.go`: `for i := n - 1; i > 0; i-- { if less(i, i-1) { return false } }`). -/
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

/-- `reflect.DeepEqual(a, b)` on two `map[common.Pgid]struct{}`: deeply equal iff the maps have
the same keys (`reflect/deepequal.go`: same length, each key of the first a key of the second,
`struct{}` values always equal). -/
abbrev reflect.DeepEqual_pgidSet.spec : Prop :=
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

/-
`sort.Strings(x)` of a slice of any length: **a hypothesis** of `fileutil.ReadDir`'s proof, not
proved here and not an axiom. It is Perennial's `sort.Strings.spec` without the premise
`len(x) ≤ 2^62`, which Perennial's proof of the sort needs for its index arithmetic and no Go
program does (`notes/perennial-changes.md`, "`sort.Sort`'s size premise"). `ReadDir` sorts the
names `Readdirnames` read, whose number nothing bounds: the model is exact only on the names of a
claim, and may return any number of other names. The general fix is that Perennial change (the
sort proved for any `int` length); the statement below is what it would give.
Lean-first (W5 of `notes/wal-fsext-plan.md`).
-/
module

public import Perennial.Spec.sort.Strings

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
variable [package_sem : sort.Assumptions]

/-- See the file header. -/
abbrev sort.StringsAny.spec : Prop :=
  ∀ (x : GoSlice) (xs : List GoString),
    {{ isPkgInit (PROP := IProp GF) pkg_id.sort ∗ x ↦* xs }}
      (App (Val (@! _root_.Perennial.sort.Strings)) (Val #x))
    {{ (xs' : List GoString), RET #(); x ↦* xs' ∗
        ⌜xs ≡ₚ xs'⌝ ∗
        ⌜∀ (i j : Nat) (xi xj : GoString), xs'[i]? = some xi → xs'[j]? = some xj → i < j →
          go.GoStringLe xi xj⌝ }}

end spec

end EtcdGrove
end Perennial

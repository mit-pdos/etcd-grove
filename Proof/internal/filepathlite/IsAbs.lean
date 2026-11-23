/-
`filepathlite.IsAbs(p)` (`path_unix.go`: `stringslite.HasPrefix(path, "/")`), over its callee's spec,
Perennial's `internal.stringslite.HasPrefix.spec` (proved there, perennial#685; until the pin reached it a
hypothesis of this repository's own statement). Lean-first.
-/
module

public import Spec.internal.filepathlite.IsAbs
public import Perennial.Spec.internal.stringslite.HasPrefix

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

/-- Beginning with `"/"` is having `/` as the first byte. -/
private theorem slash_prefix_iff (p : GoString) : ([W8 47] <+: p) ↔ p.head? = some (W8 47) := by
  cases p with
  | nil => simp
  | cons c p =>
    show ([W8 47] <+: c :: p) ↔ some c = some (W8 47)
    constructor
    · rintro ⟨t, ht⟩; simp only [List.singleton_append, List.cons.injEq] at ht; rw [ht.1]
    · intro h; cases h; exact ⟨p, rfl⟩

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.internal.filepathlite.Assumptions]
variable [_root_.Perennial.internal.stringslite.Assumptions]

theorem filepathlite.IsAbs.wp_proof
    (hHP : _root_.Perennial.internal.stringslite.HasPrefix.spec (GF := GF) (hG := hG)) :
    filepathlite.IsAbs.spec (GF := GF) (hG := hG) := by
  intro p
  wp_start
  wp_auto
  wp_apply hHP
  erw [decide_eq_decide.mpr (slash_prefix_iff p)]
  iapply HΦ; itrivial

end proof

end EtcdGrove
end Perennial

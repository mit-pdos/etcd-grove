/-
`filepathlite.IsAbs(p)` (`path_unix.go`: `stringslite.HasPrefix(path, "/")`), over its callee's spec
`stringslite.HasPrefix.spec` (a hypothesis until the Perennial pin translates `HasPrefix`:
`Spec/internal/stringslite/HasPrefix.lean`). Lean-first.
-/
module

public import Spec.internal.filepathlite.IsAbs
public import Spec.internal.stringslite.HasPrefix

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

theorem filepathlite.IsAbs.wp_proof
    (hHP : stringslite.HasPrefix.spec (GF := GF) (hG := hG)) :
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

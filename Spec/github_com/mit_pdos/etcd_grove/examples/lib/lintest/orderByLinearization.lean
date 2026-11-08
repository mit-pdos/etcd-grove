/- Lean-first (no Rocq counterpart).

`orderByLinearization(ops, linearization)` (lintest.go; Kubernetes' `TestCorrectness`'s): a new
slice of the operations of `ops` at the indices `linearization`, in its order. The indices are
valid (non-negative, below `len(ops)`); the slices are only read.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.lintest.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace lintest

open Iris Iris.BI github_com.anishathalye.porcupine

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.lintest.Assumptions]

/-- See the file header. -/
abbrev orderByLinearization.spec : Prop :=
  ∀ (osl lsl : GoSlice) (os : List Operation) (xs : List w64) (dq1 dq2 : DFrac),
  (∀ x ∈ xs, 0 ≤ sint.Z x ∧ (sint.Z x).toNat < os.length) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.lintest ∗
      osl ↦*{dq1} os ∗ lsl ↦*{dq2} xs }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.lintest.orderByLinearization))
      (Val #osl)) (Val #lsl))
  {{ (r : GoSlice), RET #r;
      r ↦* xs.filterMap (fun x => os[(sint.Z x).toNat]?) ∗ osl ↦*{dq1} os ∗ lsl ↦*{dq2} xs }}

end spec

end lintest
end EtcdGrove
end Perennial

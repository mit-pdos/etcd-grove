/- Lean-first (no Rocq counterpart).

`orderByLinearization(ops, linearization)` (`realcheck.go`, TestCorrectness's, on the checker's
`correctness.Operation`s): a new slice of the operations of `ops` at the indices `linearization`, in its
order. The indices are valid (non-negative, below `len(ops)`); the slices are only read. (As
`lintest.orderByLinearization`, on another element type.)
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.MDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- See the file header. -/
abbrev orderByLinearization.spec : Prop :=
  ∀ (osl lsl : GoSlice) (os : List github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Operation)
    (xs : List w64) (dq1 dq2 : DFrac),
  (∀ x ∈ xs, 0 ≤ sint.Z x ∧ (sint.Z x).toNat < os.length) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗
      osl ↦*{dq1} os ∗ lsl ↦*{dq2} xs }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.orderByLinearization))
      (Val #osl)) (Val #lsl))
  {{ (r : GoSlice), RET #r;
      r ↦* xs.filterMap (fun x => os[(sint.Z x).toNat]?) ∗ osl ↦*{dq1} os ∗ lsl ↦*{dq2} xs }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial

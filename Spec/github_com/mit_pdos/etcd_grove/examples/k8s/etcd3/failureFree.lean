/- Lean-first (no Rocq counterpart).

`failureFree(ops)` (`realcheck.go`): whether no operation of `ops` failed with the client's error, on a history
whose inputs and outputs are boxed `Input`s and `Output`s (`RunLin2`'s, with the driver's model): true iff
every operation passes `okOut` (a watch that ran did not fail its `Watch` call, a unary output is not `EOther`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.RealMS

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI k8s_correctness
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- See the file header. -/
abbrev failureFree.spec : Prop :=
  ∀ (sl : GoSlice) (ops : List github_com.anishathalye.porcupine.Operation) (dq : DFrac),
  (∀ o ∈ ops, ∃ x y, o.Input' = boxIn x ∧ o.Output' = boxOut y) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗ sl ↦*{dq} ops }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.failureFree)) (Val #sl))
  {{ (b : Bool), RET #b; sl ↦*{dq} ops ∗
      ⌜b = true ↔ ∀ o ∈ ops, ∀ x y, o.Input' = boxIn x → o.Output' = boxOut y → okOut x y = true⌝ }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial

/- Lean-first (no Rocq counterpart).

`removeAt(pend, i)` (etcd_txnlin.go): a new slice, `pend` without its `i`-th input (`removeAtL`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_txnlin

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.etcd.txnlin


section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.Assumptions]

/-- See the file header. -/
abbrev removeAt.spec : Prop :=
  ∀ (sl : GoSlice) (es : List Input) (dq : DFrac) (i : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin ∗ sl ↦*{dq} es ∗ ⌜0 ≤ sint.Z i ∧ sint.Z i < sint.Z sl.len⌝ }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.removeAt)) (Val #sl)) (Val #i))
  {{ (out : GoSlice), RET #out;
      sl ↦*{dq} es ∗ out ↦* removeAtL es (sint.nat i) ∗ ownSliceCap Input out (DFrac.own 1) }}

end spec

end etcd_txnlin
end EtcdGrove
end Perennial

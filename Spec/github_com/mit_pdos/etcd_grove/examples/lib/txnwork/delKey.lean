/- Lean-first (no Rocq counterpart).

`delKey(kvs, k)` (etcd_txnlin.go): a new slice, `kvs` without `k`'s entries (`delKeyL`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.txnwork.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_txnlin

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.lib.txnwork


section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.txnwork.Assumptions]

/-- See the file header. -/
abbrev delKey.spec : Prop :=
  ∀ (sl : GoSlice) (es : List entry) (dq : DFrac) (k : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.txnwork ∗ sl ↦*{dq} es }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.txnwork.delKey)) (Val #sl)) (Val #k))
  {{ (out : GoSlice), RET #out;
      sl ↦*{dq} es ∗ out ↦* delKeyL es k ∗ ownSliceCap entry out (DFrac.own 1) }}

end spec

end etcd_txnlin
end EtcdGrove
end Perennial

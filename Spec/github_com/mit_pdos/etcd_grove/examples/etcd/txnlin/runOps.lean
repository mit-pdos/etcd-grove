/- Lean-first (no Rocq counterpart).

`runOps(kvs, r, ops)` (etcd_txnlin.go): a transaction's operations run at revision `r` on the store
`kvs` (`runOpsL`): the store after them (read-only: it may be `kvs` itself), their results (a new
slice), and whether they changed the store. Its premise bounds the lengths (`put`'s).
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
abbrev runOps.spec : Prop :=
  ∀ (sl : GoSlice) (es : List entry) (r : w64) (osl : GoSlice) (ops : List TOp) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin ∗ sl ↦*□ es ∗ osl ↦*{dq} ops ∗ ⌜es.length + ops.length + 1 < 2 ^ 63⌝ }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.runOps)) (Val #sl)) (Val #r)) (Val #osl))
  {{ (kvs res : GoSlice) (ch : Bool), RET (PairV (PairV #kvs #res) #ch);
      osl ↦*{dq} ops ∗ kvs ↦*□ (runOpsL es r ops).1 ∗ res ↦* (runOpsL es r ops).2.1 ∗
      ownSliceCap TRes res (DFrac.own 1) ∗ ⌜ch = (runOpsL es r ops).2.2⌝ }}

end spec

end etcd_txnlin
end EtcdGrove
end Perennial

/-
`sortRangeResults` (`range.go`): the sort.
Lean-first; see `InvRange.lean`, `RangeModel.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.InvRange

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.server.v3.etcdserver.txn
  go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

/-- `sortRangeResults(rr, r, lg)`: the key-values sorted as the request asks (`srvSorted`: a
permutation sorted by the target, ascending or descending, when `effSortOrder` is `1` or `2`;
unchanged otherwise). Premises: the sort target is one of the protobuf's (`validSortTarget`; else
`lg.Panic`), and a sort sorts at most `2 ^ 62` key-values with non-negative revisions and
versions (`sort.Sort`'s premise; the comparators' `(a - b) < 0` does not overflow). -/
abbrev txn.sortRangeResults.spec : Prop :=
  ∀ (rr r lg : Loc) (o : OpFull) (rev count : w64) (vs : List EtcdKv),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗
      txn.rangeResultIs rr rev count vs ∗ txn.rangeRequestIs r o ∗ ⌜txn.validSortTarget o⌝ ∗
      ⌜(o.effSortOrder = W64 1 ∨ o.effSortOrder = W64 2) →
        vs.length ≤ 2 ^ 62 ∧ ∀ v ∈ vs, txn.kvOk v⌝ }}
    (App (App (App (Val (@! txn.sortRangeResults)) (Val #rr)) (Val #r)) (Val #lg))
  {{ RET #(); ∃ vs' : List EtcdKv, txn.rangeResultIs rr rev count vs' ∗ ⌜txn.srvSorted o vs vs'⌝ }}

end spec

end EtcdGrove
end Perennial

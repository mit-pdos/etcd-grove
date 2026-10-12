/-
`pruneKVs` (`range.go`): compacts the result's key-values in place, keeping those `isPrunable`
rejects, in order.
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

/-- `pruneKVs(rr, isPrunable)`, with `isPrunable` deciding `P` of an owned key-value: the result
holds the key-values `P` rejects, in order (the slice re-sliced to them; the pruned key-values and
the slice's cells past the new length are no longer owned). -/
abbrev txn.pruneKVs.spec : Prop :=
  ∀ (rr : Loc) (rev count : w64) (vs : List EtcdKv) (f : GoFunc) (P : EtcdKv → Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗
      txn.rangeResultIs rr rev count vs ∗
      □ (∀ (p : Loc) (v : EtcdKv),
        {{ txn.kvAt p v }} (App (Val #f) (Val #p)) {{ RET #(P v); txn.kvAt p v }}) }}
    (App (App (Val (@! txn.pruneKVs)) (Val #rr)) (Val #f))
  {{ RET #(); txn.rangeResultIs rr rev count (vs.filter (fun v => !P v)) }}

end spec

end EtcdGrove
end Perennial

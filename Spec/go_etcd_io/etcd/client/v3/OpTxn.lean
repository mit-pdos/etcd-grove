/-
`clientv3.OpTxn(cmps, thenOps, elseOps)` (`client/v3/op.go`, translated for `client/v3/leasing`); see `InvEtcdTxnOwn.lean` (`OpT`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.InvEtcdTxnOwn

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `OpTxn(cmps, thenOps, elseOps)`: an `Op` of type `tTxn` (`OpFull.txnInit`) with clones of the
comparisons (`Cmp.Clone`) and the two slices themselves (shared, not copied). -/
abbrev OpTxn.spec : Prop :=
  ∀ (csl : GoSlice) (ms : List CmpModel) (tsl esl : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ cmpsAt csl ms }}
    (App (App (App (Val (@! go_etcd_io.etcd.client.v3.OpTxn)) (Val #csl)) (Val #tsl)) (Val #esl))
  {{ (op : go_etcd_io.etcd.client.v3.Op), RET #op; opFullAt op OpFull.txnInit ∗
      cmpsAt op.cmps' ms ∗ ⌜op.thenOps' = tsl ∧ op.elseOps' = esl⌝ }}

end spec

end EtcdGrove
end Perennial

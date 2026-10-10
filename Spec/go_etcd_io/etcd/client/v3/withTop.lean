/-
`clientv3.withTop(target, order)` (`client/v3/op.go`, translated for `client/v3/concurrency`). Lean-first (no Rocq
counterpart); see `InvOp.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvOp

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

/-- `withTop(target, order)`: the options `WithPrefix(), WithSort(target, order), WithLimit(1)`,
in a fresh slice (read-only, with its capacity owned: `waitDeletes` appends to it); not for a sort by key in ascending order (`WithSort`'s premise:
`WithFirstKey()`, which is not translated). -/
abbrev withTop.spec : Prop :=
  ∀ (target order : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      ⌜¬ (target = W64 0 ∧ order = W64 1)⌝ }}
    (App (App (Val (@! go_etcd_io.etcd.client.v3.withTop)) (Val #target)) (Val #order))
  {{ (sl : GoSlice), RET #sl; optsAt sl (withTopM target order)∗
      ownSliceCap GoFunc sl (DFrac.own 1) }}

end spec

end EtcdGrove
end Perennial

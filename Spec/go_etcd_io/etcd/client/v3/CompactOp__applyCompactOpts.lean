/-
`(*clientv3.CompactOp).applyCompactOpts(opts)` (`client/v3/compact_op.go`; the client's `kv.Compact`, 2026-11-01). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvKVConn

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `op.applyCompactOpts(opts)` with no options (`nil`, what a call with no variadic arguments
passes): `op` unchanged. -/
abbrev CompactOp.applyCompactOpts.spec : Prop :=
  ∀ (p : Loc) (op : go_etcd_io.etcd.client.v3.CompactOp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ p ↦ op }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.CompactOp.ty @!!
      go!"applyCompactOpts")) (Val #slice.nil))
  {{ RET #(); p ↦ op }}

end spec

end EtcdGrove
end Perennial

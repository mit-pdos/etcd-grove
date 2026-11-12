/-
`clientv3.CompactOp.toRequest()` (`client/v3/compact_op.go`; the client's `kv.Compact`, 2026-11-01). Lean-first (no Rocq counterpart).
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

/-- `op.toRequest()`: a new `*pb.CompactionRequest` holding `op`'s revision and `Physical` flag,
its other fields zero. -/
abbrev CompactOp.toRequest.spec : Prop :=
  ∀ (op : go_etcd_io.etcd.client.v3.CompactOp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 }}
    (App (Val (op @!! go_etcd_io.etcd.client.v3.CompactOp.ty @!! go!"toRequest")) (Val #()))
  {{ (p : Loc), RET #p; ∃ req : etcdserverpb.CompactionRequest, p ↦ req ∗
      ⌜req.Revision' = op.revision' ∧ req.Physical' = op.physical' ∧
        req.unknownFields' = slice.nil⌝ }}

end spec

end EtcdGrove
end Perennial

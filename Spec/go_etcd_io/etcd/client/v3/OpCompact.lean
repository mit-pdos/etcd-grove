/-
`clientv3.OpCompact(rev, opts...)` (`client/v3/compact_op.go`; the client's `kv.Compact`, 2026-11-01). Lean-first (no Rocq counterpart).
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

/-- `OpCompact(rev)` with no options (`nil`): the compaction at `rev`, not physical. -/
abbrev OpCompact.spec : Prop :=
  ∀ (rev : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 }}
    (App (App (Val (@! go_etcd_io.etcd.client.v3.OpCompact)) (Val #rev)) (Val #slice.nil))
  {{ RET #(go_etcd_io.etcd.client.v3.CompactOp.mk rev false); True }}

end spec

end EtcdGrove
end Perennial

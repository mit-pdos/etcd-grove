/- Lean-first (no Rocq counterpart).

## `node.Tick()` (node.go:458)

A tick, for one credit of the term budget (`tickCred`, `InvNode.lean`): the credit goes
into the buffered `tickc` with the tick, or is dropped with it when the channel is full
(the `default` branch, which warns through the raft struct's logger). Callable from any
goroutine.
-/
module

public import Proof.go_etcd_io.raft.v3.InvNode

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]
variable [AllG GF]

/-- See the file header. -/
abbrev node.Tick.spec : Prop :=
  ∀ (γ : NodeNames) (id : w64) (n : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode γ id n ∗
      tickCred γ.bud 1 }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"Tick")) (Val #()))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial

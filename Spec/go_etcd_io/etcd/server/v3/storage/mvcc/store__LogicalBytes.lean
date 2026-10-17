/-
`store.LogicalBytes` (`kvstore.go`, etcd-io/etcd#22096). Lean-first (no Rocq counterpart); see
`InvStore.lean` (the counter's invariant in `isStore`) and `LivePayload.lean` (the payload).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `s.LogicalBytes()`: an atomic read of the live payload counter. Any caller (the metrics
callback holds nothing) gets some value. A caller holding the writer's half of the counter's
ghost variable at `w` (`o = some w`: the writer's resource `writerRes`, where `w` is the committed
log's payload `payloadW ilog`, or a write transaction's `storeTxnWriteIs`, where it is the
pending changes' payload) gets exactly `w`: the counter is the sum of `len(key) + len(value)`
over the live keys of the writer's state (mod `2 ^ 64`). -/
abbrev mvcc.store.LogicalBytes.spec : Prop :=
  ∀ (s : Loc) (γ : mvcc.StoreNames) (o : Option w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isStore s γ ∗
      (match o with | none => iprop(True) | some w => ghostVar γ.lb (1 : Qp).half w) }}
    (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"LogicalBytes")) (Val #()))
  {{ (v : w64), RET #v;
      (match o with | none => iprop(True) | some w => ghostVar γ.lb (1 : Qp).half w) ∗
      ⌜∀ w, o = some w → v = w⌝ }}

end spec

end EtcdGrove
end Perennial

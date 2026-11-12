/-
`(*streamReader).start` (`stream.go`; rafthttp stage 5c). Lean-first; the reader's predicates:
`rafthttp/Reader.lean`, `rafthttp/ReaderRun.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.ReaderRun

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`cr.start()`** of a reader made as `startPeer` makes it (no `errorc`, no context): makes
`done`, takes the transport's `ErrorC`, a cancellable context, and runs `run` in a goroutine. -/
abbrev rafthttp.streamReader.start.spec : Prop :=
  ∀ (Rh : RaftHttp GF) (lid pid : w64) (γd : GName) (cr : Loc) (ty : StreamTy) (dc0 : GoChan)
    (cf0 : GoFunc),
  Rh.member lid → lid ≠ pid →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
      srFixed0 Rh lid pid γd cr ∗ srCfg Rh pid ty cr ∗
      cr.[rafthttp.streamReader, go!"done"] ↦ dc0 ∗
      cr.[rafthttp.streamReader, go!"errorc"] ↦ (chan.nil : GoChan) ∗
      cr.[rafthttp.streamReader, go!"ctx"] ↦ GoInterface.nil ∗
      cr.[rafthttp.streamReader, go!"cancel"] ↦ cf0 }}
    (App (Val (cr @!! go.GoType.PointerType rafthttp.streamReader.ty @!! go!"start")) (Val #()))
  {{ RET #(); srFixed Rh lid pid γd cr ∗ srStopRight cr }}

end spec

end EtcdGrove
end Perennial

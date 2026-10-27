/-
`(*streamWriter).writec` (`stream.go`; rafthttp stage 5b). Lean-first; the writer's predicates:
`rafthttp/Writer.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Writer

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

/-- **`cw.writec()`**: the current `msgc` (a bag of `swMsg`s) and whether the writer is working. -/
abbrev rafthttp.streamWriter.writec.spec : Prop :=
  ∀ (Rh : RaftHttp GF) (ty : StreamTy) (lid pid : w64) (Rr : IProp GF) (cw : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
      swFixed Rh ty lid pid Rr cw }}
    (App (Val (cw @!! go.GoType.PointerType rafthttp.streamWriter.ty @!! go!"writec")) (Val #()))
  {{ (mc : GoChan) (wk : Bool), RET (PairV #mc #wk);
      ∃ γm : ChanNames, isChanBag γm mc (swMsg Rh ty lid pid) }}

end spec

end EtcdGrove
end Perennial

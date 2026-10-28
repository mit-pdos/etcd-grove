/-
`(*streamWriter).close` (`stream.go`; rafthttp stage 5b). Lean-first; the writer's predicates:
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

/-- **`cw.close()`** (by `run`, with its halves): `closeUnlocked` under `mu`. -/
abbrev rafthttp.streamWriter.close.spec : Prop :=
  ∀ (Rh : RaftHttp GF) (ty : StreamTy) (lid pid : w64) (Rr : IProp GF) (cw : Loc) (mc : GoChan)
    (wk : Bool) (cl : GoInterface) (Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
      swFixed Rh ty lid pid Rr cw ∗ swRunOwn Rh ty lid pid cw mc wk cl ∗
      (if wk then iprop(closeRight cl Q ∗ Q) else iprop(True)) ∗ Rr }}
    (App (Val (cw @!! go.GoType.PointerType rafthttp.streamWriter.ty @!! go!"close")) (Val #()))
  {{ (b : Bool), RET #b; ⌜b = wk⌝ ∗ Rr ∗ ∃ mc' : GoChan, swRunOwn Rh ty lid pid cw mc' false cl }}

end spec

end EtcdGrove
end Perennial

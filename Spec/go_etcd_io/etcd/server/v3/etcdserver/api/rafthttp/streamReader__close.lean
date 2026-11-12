/-
`(*streamReader).close` (`stream.go`; rafthttp stage 5b). Lean-first; the reader's predicates:
`rafthttp/Reader.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Reader

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

/-- **`cr.close()`** with `mu` held (`closer` whole): closes the body it holds, if any (logging an
error); `closer` then `nil`. -/
abbrev rafthttp.streamReader.close.spec : Prop :=
  ∀ (Rh : RaftHttp GF) (lid pid : w64) (γd : GName) (cr : Loc) (c : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
      srFixed Rh lid pid γd cr ∗ cr.[rafthttp.streamReader, go!"closer"] ↦ c ∗
      (⌜c = GoInterface.nil⌝ ∨ http.respCloser c) }}
    (App (Val (cr @!! go.GoType.PointerType rafthttp.streamReader.ty @!! go!"close")) (Val #()))
  {{ RET #(); cr.[rafthttp.streamReader, go!"closer"] ↦ GoInterface.nil }}

end spec

end EtcdGrove
end Perennial

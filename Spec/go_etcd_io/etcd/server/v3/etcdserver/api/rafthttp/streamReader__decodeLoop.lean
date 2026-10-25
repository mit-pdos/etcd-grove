/-
`(*streamReader).decodeLoop` (`stream.go`; rafthttp stage 5b). Lean-first; the reader's predicates:
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`cr.decodeLoop(rc, t)`** of the response body `rc` of a `200` to the stream request of ticket `γk`,
registered as `(γw, ty, lid)` to the address of `pid` (`Rh.owner`), with the right to close it and the
reader's tokens: decodes the stream's frames and hands each message (but heartbeats, and messages
while paused or with a full channel, dropped) to `recvc` or `propc` (`netRecv`: its one-shot part
withdrawn with the token of its frame's index); returns once a decode fails (closing the body), or
at once if the reader is stopped, with an error (never `nil`: `io.EOF` once stopped, if the close
succeeds) whose `Error()` returns. -/
abbrev rafthttp.streamReader.decodeLoop.spec : Prop :=
  ∀ (Rh : RaftHttp GF) (lid pid : w64) (γd : GName) (cr : Loc) (ty : StreamTy) (rc : GoInterface)
    (R : http.HReq) (γk γw : GName),
  Rh.owner R.host = pid → R.path ≠ probingPath →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
      srFixed Rh lid pid γd cr ∗ http.respReader (raftHttpNet Rh) rc R γk (W64 200) [] ∗
      http.respCloser rc ∗ ⌜rc ≠ GoInterface.nil⌝ ∗ streamReg Rh γk (γw, ty, lid) ∗ streamRd γw 0 }}
    (App (App (Val (cr @!! go.GoType.PointerType rafthttp.streamReader.ty @!! go!"decodeLoop"))
      (Val #rc)) (Val #ty.str))
  {{ (err : GoInterface), RET #err; ⌜err ≠ GoInterface.nil⌝ ∗ http.errStrOk err }}

end spec

end EtcdGrove
end Perennial

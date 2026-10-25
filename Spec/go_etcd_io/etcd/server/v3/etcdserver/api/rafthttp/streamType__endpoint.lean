/-
`streamType.endpoint` (`stream.go`; rafthttp stage 5d). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Writer

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`t.endpoint(lg)`** of a stream type: `path.Join(RaftStreamPrefix, "msgapp")` or
`path.Join(RaftStreamPrefix, "message")`, the stream's endpoint (`StreamTy.endpoint`), given
`RaftStreamPrefix`'s value (`path.Join(RaftPrefix, "stream")`, `raftStreamPrefix_join`; its
initializer is untranslated: the fact is for stage 6 to provide). -/
abbrev rafthttp.streamType.endpoint.spec : Prop :=
  ∀ (ty : StreamTy) (lg : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
      globalAddr rafthttp.RaftStreamPrefix ↦□ go!"/raft/stream" }}
    (App (Val (ty.str @!! rafthttp.streamType.ty @!! go!"endpoint")) (Val #lg))
  {{ RET #ty.endpoint; True }}

end spec

end EtcdGrove
end Perennial

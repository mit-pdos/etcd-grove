/-
`(*streamReader).dial` (`stream.go`; rafthttp stage 5c). Lean-first; the reader's predicates:
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

/-- **`cr.dial(t)`** of the reader's stream type: a `GET` of the stream's path to one of the peer's
URLs, with a fresh ticket registered as the stream's (`(γw, ty, lid)`), whose response at a `200`
is the stream: its body (to read, with the right to close it) and the reader's tokens; or an error
whose `Error()` returns. No panic: `semver.MustParse` of the peer's `X-Server-Version` header
(`issues/etcd-rafthttp-stream-dial-bad-server-version-panic.md`) parses, the peer being a member of
the program, whose handlers set it to `version.Version` or not at all (the protocol's `rhdr`,
`verHdrOk`; proved in stage 5e-3). Nothing is reported on `errorc`: a member never answers `410`
(no member is removed; stage 6). -/
abbrev rafthttp.streamReader.dial.spec : Prop :=
  ∀ (Rh : RaftHttp GF) (lid pid : w64) (γd : GName) (cr : Loc) (ty : StreamTy),
  Rh.member lid → lid ≠ pid →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
      srFixed Rh lid pid γd cr ∗ srDial Rh pid ty cr }}
    (App (Val (cr @!! go.GoType.PointerType rafthttp.streamReader.ty @!! go!"dial")) (Val #ty.str))
  {{ (rc err : GoInterface), RET (PairV #rc #err); http.errStrOk err ∗
      (⌜err ≠ GoInterface.nil⌝ ∨ ⌜err = GoInterface.nil⌝ ∗
        ∃ (R : http.HReq) (γk γw : GName), ⌜Rh.owner R.host = pid ∧ R.path ≠ probingPath⌝ ∗
          http.respReader (raftHttpNet Rh) rc R γk (W64 200) [] ∗ http.respCloser rc ∗
          ⌜rc ≠ GoInterface.nil⌝ ∗ streamReg Rh γk (γw, ty, lid) ∗ streamRd γw 0) }}

end spec

end EtcdGrove
end Perennial

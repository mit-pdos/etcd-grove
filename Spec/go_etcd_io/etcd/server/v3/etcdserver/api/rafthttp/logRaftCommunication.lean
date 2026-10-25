/-
`rafthttp.logRaftCommunication(lg, localID, m, remote, direction)` (`transport.go:458`):
PR etcd#21401's debug logger for Raft messages sent and received over HTTP/stream/pipeline.
Lean-first.

### Preconditions exposed by verification (PR etcd#21401 bugs)

1. **`lg ≠ null` (Bug 2a)**: `logRaftCommunication` unconditionally calls
   `lg.Core().Enabled(zap.DebugLevel)` at line 459 without checking `if lg == nil`.
   In `pipeline.go:100`, `p.tr.Logger` is passed (which also panics if `p.tr == nil`, as in
   `TestPipelineSend`, or if `Logger == nil`, as in `TestSendMessage`).
2. **`rq.header.isSome` on `MsgProp` (Bug 2b)**: When `m.GetType() == raftpb.MsgProp` and
   `len(m.Entries) > 0`, `logRaftCommunication` unmarshals `m.Entries[0].Data` into
   `var r pb.InternalRaftRequest` and, when `err == nil`, dereferences `r.Header.ID`
   at line 480 without checking `if r.Header != nil`. Any `MsgProp` whose `Entries[0].Data`
   decodes to an `InternalRaftRequest` without a `Header` (such as a v2-style request with only
   top-level `ID` set, or an empty `Entry.Data`) causes a nil-pointer panic when debug logging
   is enabled.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseApply
public import Proof.go_etcd_io.raft.v3.InvPb
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.InvRequest
public import GeneratedProof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Assumptions]

abbrev rafthttp.logRaftCommunication.spec : Prop :=
  ∀ (lg m : Loc) (localID remote : go_etcd_io.etcd.client.pkg.v3.types.ID)
    (direction : GoString) (dq dqe : DFrac) (cap : Bool) (ms : MsgSt),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
      ⌜lg ≠ null⌝ ∗ msgPtsC m dq dqe cap ms ∗
      ⌜ms.msg.Type' = MsgProp →
        ∀ e0 rq, ms.ents[0]? = some e0 → apply.irrDecode e0.Data' = some rq →
          rq.header.isSome⌝ }}
    (App (App (App (App (App
      (Val (@! rafthttp.logRaftCommunication))
      (Val #lg)) (Val #localID)) (Val #m)) (Val #remote)) (Val #direction))
  {{ RET #(); msgPtsC m dq dqe cap ms }}

end spec

end EtcdGrove
end Perennial

/-
`v3rpc.serverWatchStream.newResponseHeader` (`watch.go`). Lean-first (no Rocq counterpart); the
vocabulary is `v3rpc/InvWatchStream.lean` and `v3rpc/InvWatch.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvWatch

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.etcd.server.v3.etcdserver
  go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`sws.newResponseHeader(rev)`**: a fresh header (read-only) with the server's cluster and
member ids, the revision `rev`, some term and leader. -/
abbrev v3rpc.serverWatchStream.newResponseHeader.spec : Prop :=
  ∀ (sws : Loc) (r : v3rpc.WRun GF) (rev : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ v3rpc.swsIs sws r }}
    (App (Val (sws @!! go.GoType.PointerType v3rpc.serverWatchStream.ty @!! go!"newResponseHeader"))
      (Val #rev))
  {{ (h : Loc), RET #h; ∃ t l : w64, hdrFull h ⟨r.srv.cid, r.srv.mid, rev, t, l⟩ }}

end spec

end EtcdGrove
end Perennial

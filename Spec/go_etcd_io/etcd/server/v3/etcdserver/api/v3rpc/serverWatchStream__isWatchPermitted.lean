/-
`v3rpc.serverWatchStream.isWatchPermitted` (`watch.go`). Lean-first (no Rocq counterpart); the
vocabulary is `v3rpc/InvWatchStream.lean` and `v3rpc/InvWatch.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvWatch
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.AuthClass

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

/-- **`sws.isWatchPermitted(wcr)`** with the auth store's reader resource: the auth info of the
stream's context, then the auth store's `IsRangePermitted` of the request's range: an error the
apply package's `applyErrIs` describes (`nil`: permitted). 2026-10-23 (auth plan A1): permitted
only with, for some auth info (the stream's context's, or the empty one), that info's read
permission class of the watch's range (`apply.classRes`, with auth on: `classOk`). -/
abbrev v3rpc.serverWatchStream.isWatchPermitted.spec : Prop :=
  ∀ (sws : Loc) (r : v3rpc.WRun GF) (wcr : Loc) (ks es : GoSlice) (k e : List w8) (dk de : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ v3rpc.swsIs sws r ∗ r.srv.E.RD ∗
      structFieldRef etcdserverpb.WatchCreateRequest go!"Key" wcr ↦{dk} ks ∗ ks ↦*□ k ∗
      structFieldRef etcdserverpb.WatchCreateRequest go!"RangeEnd" wcr ↦{de} es ∗ es ↦*□ e ∗
      ⌜k.length < 2 ^ 63 - 1⌝ }}
    (App (Val (sws @!! go.GoType.PointerType v3rpc.serverWatchStream.ty @!! go!"isWatchPermitted"))
      (Val #wcr))
  {{ (err : GoInterface), RET #err; r.srv.E.RD ∗
      structFieldRef etcdserverpb.WatchCreateRequest go!"Key" wcr ↦{dk} ks ∗
      structFieldRef etcdserverpb.WatchCreateRequest go!"RangeEnd" wcr ↦{de} es ∗
      applyErrIs err ∗
      (∀ _ : err = GoInterface.nil, ∃ info,
        apply.classRes r.srv.E.authMode info [(k, e, auth.PermType.read)]) }}

end spec

end EtcdGrove
end Perennial

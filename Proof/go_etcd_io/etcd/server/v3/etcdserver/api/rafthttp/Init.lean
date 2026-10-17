/-
Package initialization of `go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact is `True`. Its initializer initializes its imports and runs the untranslated
initializers of its variables (`X.init`, axioms of the translation), which the
trust-boundary axiom `opaqueInitsOk` says run without panicking.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseApply
public import Perennial.Proof.context.Link
public import Perennial.Proof.sync.Link
public import Perennial.Proof.time.Link
public import Proof.github_com.xiang90.probing.Init
public import Proof.go_etcd_io.etcd.client.pkg.v3.transport.Init
public import Proof.go_etcd_io.etcd.client.pkg.v3.types.Init
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Init
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.Init
public import Proof.go_etcd_io.raft.v3.Init
public import Proof.go_uber_org.zap.Init
public import Proof.golang_org.x.time.rate.Init
public import Proof.net.http.Init

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial

/-- `x ∈ [a, ..., x, ...]`, linear in the list (`simp` overflows on the long ones). -/
local macro "mem_tac" : tactic =>
  `(tactic| repeat (first | exact List.Mem.head _ | apply List.Mem.tail))

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section opaqueInits
namespace go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp`'s untranslated variable initializers run.**
Goose translates them names-only, so each `X.init` is an axiom of the translation; Go
runs them at program start, and etcd starts, so each returns without panicking.
Satisfiable whatever the semantics (the `X.init`s are uninterpreted constants). -/
axiom opaqueInitsOk :
    ∀ v ∈ ([RaftPrefix.init,
        ProbingPrefix.init,
        RaftStreamPrefix.init,
        RaftSnapshotPrefix.init,
        errIncompatibleVersion.init,
        ErrClusterIDMismatch.init,
        activePeers.init,
        disconnectedPeers.init,
        sentBytes.init,
        receivedBytes.init,
        sentFailures.init,
        recvFailures.init,
        snapshotSend.init,
        snapshotSendInflights.init,
        snapshotSendFailures.init,
        snapshotSendSeconds.init,
        snapshotReceive.init,
        snapshotReceiveInflights.init,
        snapshotReceiveFailures.init,
        snapshotReceiveSeconds.init,
        rttSec.init,
        readBytesLimit.init,
        ErrExceedSizeLimit.init,
        ConnReadTimeout.init,
        ConnWriteTimeout.init,
        errStopped.init,
        proberInterval.init,
        statusMonitoringInterval.init,
        statusErrorInterval.init,
        snapResponseReadTimeout.init,
        errUnsupportedStreamType.init,
        supportedStream.init,
        linkHeartbeatMessage.init,
        linkHeartbeatSize.init,
        errMemberRemoved.init,
        errMemberNotFound.init] : List val),
    {{ (True : IProp GF) }} (App (Val v) (Val #())) {{ RET #(); True }}

end go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp
end opaqueInits

section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Assumptions]
variable [_root_.Perennial.context.ErrorStringIsError]
  [_root_.Perennial.context.DeadlineExceededIsError]
variable [_root_.Perennial.log.NewModel]

namespace go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp

theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp }} := by
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply _root_.Perennial.go_etcd_io.etcd.client.pkg.v3.transport.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd13⟩
  wp_apply _root_.Perennial.github_com.xiang90.probing.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd12⟩
  wp_apply _root_.Perennial.go_etcd_io.raft.v3.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd11⟩
  wp_apply _root_.Perennial.golang_org.x.time.rate.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd10⟩
  wp_apply _root_.Perennial.sync.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd9⟩
  wp_apply _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd8⟩
  wp_apply _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.snap.wp_initialize' _ Hinit.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd7⟩
  wp_apply _root_.Perennial.go_etcd_io.etcd.client.pkg.v3.types.wp_initialize' _ Hinit.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd6⟩
  wp_apply _root_.Perennial.go_uber_org.zap.wp_initialize' _ Hinit.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd5⟩
  wp_apply _root_.Perennial.time.wp_initialize' _ Hinit.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd4⟩
  wp_apply _root_.Perennial.net.http.wp_initialize' _ Hinit.2.2.2.1 $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply _root_.Perennial.context.wp_initialize' _ Hinit.2.2.1 $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply _root_.Perennial.go_etcd_io.raft.v3.raftpb.wp_initialize' _ Hinit.2.1 $$ Hown as ⟨Hown, #Hd1⟩
  wp_apply (opaqueInitsOk RaftPrefix.init (by mem_tac))
  wp_apply (opaqueInitsOk ProbingPrefix.init (by mem_tac))
  wp_apply (opaqueInitsOk RaftStreamPrefix.init (by mem_tac))
  wp_apply (opaqueInitsOk RaftSnapshotPrefix.init (by mem_tac))
  wp_apply (opaqueInitsOk errIncompatibleVersion.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrClusterIDMismatch.init (by mem_tac))
  wp_apply (opaqueInitsOk activePeers.init (by mem_tac))
  wp_apply (opaqueInitsOk disconnectedPeers.init (by mem_tac))
  wp_apply (opaqueInitsOk sentBytes.init (by mem_tac))
  wp_apply (opaqueInitsOk receivedBytes.init (by mem_tac))
  wp_apply (opaqueInitsOk sentFailures.init (by mem_tac))
  wp_apply (opaqueInitsOk recvFailures.init (by mem_tac))
  wp_apply (opaqueInitsOk snapshotSend.init (by mem_tac))
  wp_apply (opaqueInitsOk snapshotSendInflights.init (by mem_tac))
  wp_apply (opaqueInitsOk snapshotSendFailures.init (by mem_tac))
  wp_apply (opaqueInitsOk snapshotSendSeconds.init (by mem_tac))
  wp_apply (opaqueInitsOk snapshotReceive.init (by mem_tac))
  wp_apply (opaqueInitsOk snapshotReceiveInflights.init (by mem_tac))
  wp_apply (opaqueInitsOk snapshotReceiveFailures.init (by mem_tac))
  wp_apply (opaqueInitsOk snapshotReceiveSeconds.init (by mem_tac))
  wp_apply (opaqueInitsOk rttSec.init (by mem_tac))
  wp_apply (opaqueInitsOk readBytesLimit.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrExceedSizeLimit.init (by mem_tac))
  wp_apply (opaqueInitsOk ConnReadTimeout.init (by mem_tac))
  wp_apply (opaqueInitsOk ConnWriteTimeout.init (by mem_tac))
  wp_apply (opaqueInitsOk errStopped.init (by mem_tac))
  wp_apply (opaqueInitsOk proberInterval.init (by mem_tac))
  wp_apply (opaqueInitsOk statusMonitoringInterval.init (by mem_tac))
  wp_apply (opaqueInitsOk statusErrorInterval.init (by mem_tac))
  wp_apply (opaqueInitsOk snapResponseReadTimeout.init (by mem_tac))
  wp_apply (opaqueInitsOk errUnsupportedStreamType.init (by mem_tac))
  wp_apply (opaqueInitsOk supportedStream.init (by mem_tac))
  wp_apply (opaqueInitsOk linkHeartbeatMessage.init (by mem_tac))
  wp_apply (opaqueInitsOk linkHeartbeatSize.init (by mem_tac))
  wp_apply (opaqueInitsOk errMemberRemoved.init (by mem_tac))
  wp_apply (opaqueInitsOk errMemberNotFound.init (by mem_tac))
  iframe Hown
  is_pkg_init_finish


end go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp

end init

end Perennial

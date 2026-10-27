/-
**The server is a receiver of the raft network** (D21 stage M2, 2026-10-19). Lean-first (no Rocq
counterpart). `srv_netRaftOk`: the server `s`, as the transport's `Raft` (`tv.Raft`, the
`*EtcdServer` interface value), meets `netRaftOk` from its `Process`, `IsIDRemoved`,
`ReportUnreachable`, `ReportSnapshot` (their specs), each call borrowing an `lgMu` reader slot
(`srvLgReader`, which `Process`'s `Logger()` reads with): what `rafthttp.Transport.Start` takes,
at any snapshot directory `γd` (D22 S-i).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Process
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__IsIDRemoved
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__ReportUnreachable
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__ReportSnapshot

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section bridge
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- The `*EtcdServer` `s` as an interface value (`rafthttp.Raft`, the transport's `Raft`). -/
abbrev srvIface (s : Loc) : GoInterface :=
  interface.mkOk (go.GoType.PointerType EtcdServer.ty) #s

/-- See the file header. -/
theorem srv_netRaftOk
    (wp_Process : EtcdServer.Process.spec (GF := GF) (hG := hG))
    (wp_IsIDRemoved : EtcdServer.IsIDRemoved.spec (GF := GF) (hG := hG))
    (wp_ReportUnreachable : EtcdServer.ReportUnreachable.spec (GF := GF) (hG := hG))
    (wp_ReportSnapshot : EtcdServer.ReportSnapshot.spec (GF := GF) (hG := hG))
    (γn : NetNames GF) (γd : GName) (s : Loc) (id : w64) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvProcOk γn s id ⊢ netRaftOk γn id γd (srvLgReader s) (srvIface s) := by
  iintro ⟨#Hpkg, #Hok⟩
  iunfold netRaftOk
  iexists ⟨go.GoType.PointerType EtcdServer.ty, #s⟩
  isplitr
  · ipureintro; rfl
  isplitr
  · iintro !> %ctx %cd %ml %Φ !> ⟨#Hctx, Hlr, Hrecv⟩ HΦ
    wp_apply wp_Process γn γd s id ctx cd ml $$ [Hlr Hrecv] as %err ⟨#Herr, Hlr⟩
    · iframe #; iframe Hlr Hrecv
    iapply HΦ
    iframe Hlr Herr
  isplitr
  · iintro !> %x %Φ !> - HΦ
    wp_apply wp_IsIDRemoved γn s id x
    · iframe #
    iapply HΦ; itrivial
  isplitr
  · iintro !> %x %Φ !> - HΦ
    wp_apply wp_ReportUnreachable γn s id x
    · iframe #
    iapply HΦ; itrivial
  · iintro !> %x %st %Φ !> - HΦ
    wp_apply wp_ReportSnapshot γn s id x st
    · iframe #
    iapply HΦ; itrivial

end bridge

end EtcdGrove
end Perennial

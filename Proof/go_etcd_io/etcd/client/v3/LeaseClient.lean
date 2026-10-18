/-
**The clients' lease contract, derived for etcd's lessor** (item 1, the client lease, branch
`lease-client`, 2026-10-18; `notes/STATUS.md`, "The client lease"). Lean-first, no Rocq counterpart.

`isEtcdLease_of_lessor`: a `*lessor` (`lessorAt l addr`, what `NewLease` returns over a connection
to `addr`) meets the clients' lease contract (`isEtcdLease`, `cache/v3/InvEtcdTxn.lean`) at any
etcd model `EM`, given that the server at `addr` registers etcd's specs of `LeaseGrant` and
`LeaseRevoke` at `EM` (`etcdLeaseGrantSpec`, `etcdLeaseRevokeSpec`: that etcd's server does is the
client lease's stage (c), not done) and serves the keep-alive stream (`leaseKAStreamOk`), and the
error facts the keep-alive loop's checks need (`eofOk`, `ctxErrClientAll`, `ctxErrTargets`).
`isEtcdLeaseClient_of_new`: `clientv3.New`'s client (`isNewClient`) has such a `Lease`.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.lessor__Grant
public import Spec.go_etcd_io.etcd.client.v3.lessor__Revoke
public import Spec.go_etcd_io.etcd.client.v3.lessor__KeepAlive
public import Proof.go_etcd_io.etcd.client.v3.InvClientNewResult
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.read.Init

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [EM : EtcdModel GF]

/-- **The clients' lease interface value of the `*lessor` `l`** (what `NewLease` returns). -/
abbrev lessorIfaceOf (l : Loc) : GoInterfaceOk :=
  interface.mk (go.GoType.PointerType go_etcd_io.etcd.client.v3.lessor.ty) #l

/-- **`context`'s facts give `ctxErrTargets`** (as the read package states them). -/
theorem ctxErrTargets_of [EtcdGrove.ContextReadErrs (GF := GF) (hG := hG)] :
    isPkgInit (PROP := IProp GF) pkg_id.context ⊢ ctxErrTargets := by
  iintro #Hp
  ihave ⟨#HC, #HD⟩ := EtcdGrove.ContextReadErrs.errs $$ Hp
  iunfold EtcdGrove.errVarLeaf at HC
  icases HC with ⟨%ec, #Hec, %Hlc, -⟩
  icases HD with ⟨%ed, #Hed, %Hld, -⟩
  unfold ctxErrTargets
  isplitl
  · iexists ec; iframe #; ipureintro; exact Hlc.1
  · iexists ed; iframe #; ipureintro; exact Hld.2.2.2

/-- **A `*lessor` meets the clients' lease contract** (see the file header). -/
theorem isEtcdLease_of_lessor
    (wp_Grant : lessor.Grant.spec (GF := GF) (hG := hG))
    (wp_Revoke : lessor.Revoke.spec (GF := GF) (hG := hG))
    (wp_KeepAlive : lessor.KeepAlive.spec (GF := GF) (hG := hG))
    (l : Loc) (addr : GoString) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ lessorAt l addr ∗
      isGrpcRpc addr go!"/etcdserverpb.Lease/LeaseGrant" etcdLeaseGrantSpec ∗
      isGrpcRpc addr go!"/etcdserverpb.Lease/LeaseRevoke" etcdLeaseRevokeSpec ∗
      leaseKAStreamOk addr ∗ client.eofOk ∗ client.ctxErrClientAll ∗ ctxErrTargets ⊢
    isEtcdLease (lessorIfaceOf l) := by
  iintro ⟨#Hp, #Hl, #HG, #HR, #Hstr, #Heof, #Hall, #Htg⟩
  ihave #Hl' := Hl
  iunfold lessorAt at Hl'
  icases Hl' with ⟨%dc, %γd, %sc, %scd, %lg, %d, -, -, -, -, -, -, -, #Hrem, -, -⟩
  unfold isEtcdLease
  isplitl
  · iintro !> %ctx %cs %ttl %Φ !> #Hctx HΦ
    ihave #Hok := ctxOk_of_isContext ctx cs $$ Hctx
    iunfold client.ctxErrClientAll at Hall
    ihave #Hce := Hall $$ %ctx %cs Hctx
    iapply (wp_Grant l addr etcdLeaseGrantSpec
      (fun m => iprop(⌜m.id ≠ W64 0⌝ ∗ etcdReached m.hdr.revision)) ctx cs ttl) $$ []
    · iframe #
      unfold etcdLeaseGrantSpec
      iintro !> !> %m %Hid #Hr
      simp only
      iframe #
      ipureintro; exact Hid
    inext
    iintro %resp %err Hres
    iapply HΦ
    icases Hres with (⟨%Herr, %m, %h, #Hhf, #Hhdr, #Hid, -, %Hidnn, #Hr⟩ | ⟨%Herr, -⟩)
    · iright
      isplitr
      · ipureintro; exact Herr
      iunfold hdrFull at Hhdr
      icases Hhdr with ⟨%Hhnn, -, -, #Hrev, -, -⟩
      iexists m.id, h, m.hdr.revision
      iframe #
      ipureintro; exact ⟨Hidnn, Hhnn⟩
    · ileft; ipureintro; exact Herr.1
  isplitl
  · iintro !> %ctx %cs %id %Φ !> #Hctx HΦ
    iapply (wp_KeepAlive l addr ctx cs id) $$ []
    · iframe #
    inext
    iintro %ch %err Hres
    iapply HΦ
    iexact Hres
  · iintro !> %ctx %cs %id %Φ !> #Hctx HΦ
    ihave #Hok := ctxOk_of_isContext ctx cs $$ Hctx
    iunfold client.ctxErrClientAll at Hall
    ihave #Hce := Hall $$ %ctx %cs Hctx
    iapply (wp_Revoke l addr etcdLeaseRevokeSpec
      (fun m => iprop(etcdReached m.hdr.revision)) ctx cs id) $$ []
    · iframe #
      unfold etcdLeaseRevokeSpec
      iintro !> !> %m #Hr
      iexact Hr
    inext
    iintro %resp %err Hres
    iapply HΦ
    icases Hres with (⟨%Herr, %m, #Hm, #Hr⟩ | ⟨%Herr, -⟩)
    · iright
      isplitr
      · ipureintro; exact Herr
      iunfold leaseRevokeRespMsg at Hm
      icases Hm with ⟨-, %h, #Hhf, #Hhdr⟩
      iunfold hdrFull at Hhdr
      icases Hhdr with ⟨%Hhnn, -, -, #Hrev, -, -⟩
      iexists h, m.hdr.revision
      iframe #
      ipureintro; exact Hhnn
    · ileft; ipureintro; exact Herr.1

/-- **`clientv3.New`'s client has the clients' lease contract** (`isEtcdLeaseClient`; see the file
header). -/
theorem isEtcdLeaseClient_of_new
    [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (wp_Grant : lessor.Grant.spec (GF := GF) (hG := hG))
    (wp_Revoke : lessor.Revoke.spec (GF := GF) (hG := hG))
    (wp_KeepAlive : lessor.KeepAlive.spec (GF := GF) (hG := hG))
    (cl : Loc) (ep : GoString) (V : client.WEnv GF) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ isNewClient cl ep V ∗
      isGrpcRpc ep go!"/etcdserverpb.Lease/LeaseGrant" etcdLeaseGrantSpec ∗
      isGrpcRpc ep go!"/etcdserverpb.Lease/LeaseRevoke" etcdLeaseRevokeSpec ∗
      leaseKAStreamOk ep ∗ client.eofOk ∗ client.ctxErrClientAll ∗ ctxErrTargets ⊢
    isEtcdLeaseClient cl := by
  iintro ⟨#Hp, #Hnc, #HG, #HR, #Hstr, #Heof, #Hall, #Htg⟩
  iunfold isNewClient at Hnc
  icases Hnc with ⟨-, -, -, -, %lp, #Hlf, #Hlp⟩
  unfold isEtcdLeaseClient
  iexists lessorIfaceOf lp
  iframe Hlf
  iapply isEtcdLease_of_lessor wp_Grant wp_Revoke wp_KeepAlive lp ep
  iframe #

end proof

end EtcdGrove
end Perennial

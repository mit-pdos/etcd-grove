/-
**The auth store's apply contract in the mode `on`, of the real store** (the auth plan's E2i,
2026-10-26; `notes/decisions.md`, "E2i of the auth plan"). Lean-first (no Rocq counterpart).

`authApplyOkM M` (`InvBoot.lean`) is the server's apply contract of its auth store on whichever
backend it is on, with the store's verdicts in the mode `M`; `NewAuthStore`'s axiom gives its mode
`off` (`authApplyOk`). In the mode `on γa` the real store meets it from its invariant: the
permission checks, `IsAdminPermitted`, `IsAuthEnabled` and `Revision` from the store's proofs
(`apply.isAuthStore_of_authInv`), the admin clauses vacuous (`apply.isAuthStoreAdmin_on`: the
server admits no auth request in the mode `on` yet, `apply.adminAdmitted`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvBoot
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthReqDerive

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- **The real store's apply contract in the mode `on γa`** (see the file header), with the
store's reader resource `auth.authRd stl R (.on γa)`. -/
theorem authApplyOkM_on
    (hPut : auth.authStore.IsPutPermitted.spec (GF := GF) (hG := hG))
    (hRange : auth.authStore.IsRangePermitted.spec (GF := GF) (hG := hG))
    (hDel : auth.authStore.IsDeleteRangePermitted.spec (GF := GF) (hG := hG))
    (hAdmin : auth.authStore.IsAdminPermitted.spec (GF := GF) (hG := hG))
    (hEn : auth.authStore.IsAuthEnabled.spec (GF := GF) (hG := hG))
    (hRev : auth.authStore.Revision.spec (GF := GF) (hG := hG))
    (stl : Loc) (R : IProp GF) (γa : auth.AuthNames) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗
      auth.authInv stl R (.on γa) ⊢
      authApplyOkM (.on γa) stl (auth.authRd stl R (.on γa)) := by
  iintro ⟨#Hpkg, #Hinv⟩
  iunfold authApplyOkM
  iintro !> %d %W %Pk %γ %f %RW %_ - - %_ -
  iapply (apply.isAuthStore_of_authInv hPut hRange hDel hAdmin hEn hRev stl R (.on γa) γ Pk #f RW)
  iframe Hpkg Hinv
  iapply (apply.isAuthStoreAdmin_on (interface.mk (go.GoType.PointerType auth.authStore.ty) #stl)
    γ Pk #f RW γa)

/-- **The real store's request side and apply contract in the mode `on γa`**, both with the
reader resource `auth.authRd stl R (.on γa)`: what `NewAuthStore`'s axiom gives in the mode `off`
(`isReqAuth`, `authApplyOk`). -/
theorem authSrvContracts_on
    (hCtx : auth.authStore.AuthInfoFromCtx.spec (GF := GF) (hG := hG))
    (hTLS : auth.authStore.AuthInfoFromTLS.spec (GF := GF) (hG := hG))
    (hPut : auth.authStore.IsPutPermitted.spec (GF := GF) (hG := hG))
    (hRange : auth.authStore.IsRangePermitted.spec (GF := GF) (hG := hG))
    (hDel : auth.authStore.IsDeleteRangePermitted.spec (GF := GF) (hG := hG))
    (hAdmin : auth.authStore.IsAdminPermitted.spec (GF := GF) (hG := hG))
    (hEn : auth.authStore.IsAuthEnabled.spec (GF := GF) (hG := hG))
    (hRev : auth.authStore.Revision.spec (GF := GF) (hG := hG))
    (stl : Loc) (R : IProp GF) (γa : auth.AuthNames) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗
      auth.authInv stl R (.on γa) ⊢
      isReqAuth (auth.authIface stl) (auth.authRd stl R (.on γa)) ∗
      authApplyOkM (.on γa) stl (auth.authRd stl R (.on γa)) := by
  iintro ⟨#Hpkg, #Hinv⟩
  isplitl []
  · iapply (isReqAuth_of_authInv hCtx hTLS stl R (.on γa)); iframe Hpkg Hinv
  iapply (authApplyOkM_on hPut hRange hDel hAdmin hEn hRev stl R γa); iframe Hpkg Hinv

end proof

end EtcdGrove
end Perennial

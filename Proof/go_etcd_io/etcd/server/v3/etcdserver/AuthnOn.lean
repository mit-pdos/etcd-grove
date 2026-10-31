/-
**The served `Authenticate`'s proposal with auth on** (C1's A4, 2026-10-31; `notes/c1-plan.md`).
`EtcdServer.Authenticate` proposes `&pb.InternalRaftRequest{Authenticate: {Name, SimpleToken}}`
(`irrAuthenticate ⟨name, [], pre⟩`: no password, checked before), which the mode `on` admits with pure facts only (`reqPropOkOn`'s third case:
`adminPropOk`'s `.authenticate` clause, the prefix's `auth.tokPrefixOk`; no admin permission, no
history update):
- `adminPropOk_authenticate`, `reqPropOkM_true_authn`: the admission.
- `appliedOkM_authn`: the law that reads an `Authenticate`'s answer out of `raftRequest`'s success
  (`appliedOkM true`'s `authnAnsM` at `.on γa`): an `*AuthenticateResponse` whose token was issued
  to the request's user.
- `authnRaft_on`: one round, `raftRequest.specM true` on the request: on `nil` that response.
Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AdminOn

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section pure
variable [GooseExts] [go_gctx : GoGlobalContext]

theorem dispatchKind_irrAuthenticate (name pre : GoString) (hm : apply.HeaderModel) :
    apply.dispatchKind (apply.withHeader (irrAuthenticate ⟨name, [], pre⟩) hm) = .authenticate := by
  simp [apply.dispatchKind, apply.withHeader, irrAuthenticate, apply.irrEmpty]

/-- **The request is admitted**, for a prefix the provider makes. -/
theorem adminPropOk_authenticate (name pre : GoString) (h : auth.tokPrefixOk pre) :
    adminPropOk srvAuthSt0 (irrAuthenticate ⟨name, [], pre⟩) :=
  ⟨by simp only [apply.adminKindOk]
      simp only [apply.dispatchKind, irrAuthenticate, apply.irrEmpty]
      simp only [Option.isSome_none, Option.isSome_some, Bool.false_eq_true, ↓reduceIte]
      refine ⟨by simp [apply.needAdminPermission], ?_⟩
      intro am h'; cases h'; exact h,
   by simp [apply.noSideEffect, irrAuthenticate, apply.irrEmpty],
   by simp [irrAuthenticate, apply.irrEmpty],
   rolesSorted_srvAuthSt0⟩

end pure

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The proposal's permission in the mode `on`**: admitted, at any header, with the result the
step's determinacy at the commit (`adminPropRes`). -/
theorem reqPropOkM_true_authn (γ : ServerRaftNames) (γk : KVNames)
    (Gb : apply.HeaderModel → IProp GF) (name pre : GoString) (h : auth.tokPrefixOk pre) :
    ⊢ reqPropOkM (GF := GF) true γ γk Gb (irrAuthenticate ⟨name, [], pre⟩)
        (fun hm => adminPropRes γk srvAuthSt0 (apply.withHeader (irrAuthenticate ⟨name, [], pre⟩) hm)) := by
  iunfold reqPropOkM
  iintro %hm
  iunfold reqPropOkOn
  iright
  iright
  ileft
  ipureintro
  exact ⟨adminPropOk_authenticate name pre h,
    irrNoZeroEnd_admin _ rfl rfl rfl, by simp [apply.needAdminPermission, apply.withHeader,
      irrAuthenticate, apply.irrEmpty], rfl⟩

/-- **An `Authenticate`'s answer, read out of `raftRequest`'s success** (with auth on at `γa`):
an `*AuthenticateResponse` `rp` whose token was issued to the request's user. -/
theorem appliedOkM_authn (E : apply.AEnv GF) (ρ : ReqNames) (γa : auth.AuthNames)
    (hγa : E.authMode = .on γa) (rq' : apply.IRRModel) (F : mvcc.Log) (resp : GoInterface)
    (L : List EntryModel) (hk : apply.dispatchKind rq' = .authenticate) :
    appliedOkM true E ρ rq' F resp L ⊢
      ∃ (am : apply.AuthenticateModel) (rp : Loc) (v : etcdserverpb.AuthenticateResponse),
        ⌜rq'.authenticate = some am ∧
          resp = interface.mkOk (go.GoType.PointerType etcdserverpb.AuthenticateResponse.ty) #rp⌝ ∗
        rp ↦ v ∗ auth.tokIssued γa v.Token' am.name := by
  unfold appliedOkM authnAnsM
  simp only [hγa]
  iintro H
  icases H with ⟨%x, %x', %o, %skip, -, -, -, -, -, -, Ha⟩
  icases Ha with (%Hn | ⟨%am, %rp, %v, %Hp, Hrp, #Ht⟩)
  · exact absurd hk Hn
  iexists am, rp, v
  iframe Hrp Ht
  ipureintro; exact Hp

/-- **One round of `Authenticate`'s proposal** (`raftRequest.specM true` on `irrAuthenticate`):
the run's slots back, the error one the gRPC layer can take, and on `nil` an
`*AuthenticateResponse` whose token was issued to `name`. -/
theorem authnRaft_on (hRR : EtcdServer.raftRequest.specM (GF := GF) (hG := hG) true)
    (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γa : auth.AuthNames) (hγa : E.authMode = .on γa)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (p : Loc) (name pre : GoString)
    (hpre : auth.tokPrefixOk pre) (F : mvcc.Log) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReqM true s E ρ ∗ srvLeadTimeReader s ∗ E.RD ∗ idCred ρ.ids 1 ∗
        context.isContext ctx cd ∗ irrNoHdrIs p (irrAuthenticate ⟨name, [], pre⟩) ∗
        (∃ h0 : Loc, structFieldRef etcdserverpb.InternalRaftRequest go!"Header" p ↦ h0) ∗
        mvcc.idxCert E.γ.idx F }}
      (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"raftRequest"))
        (Val #(GoInterface.ok ctx))) (Val #p))
    {{ (resp err : GoInterface), RET (PairV #resp #err); srvLeadTimeReader s ∗ E.RD ∗
        applyErrIs err ∗
        ((⌜err = GoInterface.nil⌝ ∗ ∃ (rp : Loc) (v : etcdserverpb.AuthenticateResponse),
            ⌜resp = interface.mkOk (go.GoType.PointerType etcdserverpb.AuthenticateResponse.ty) #rp⌝ ∗
            rp ↦ v ∗ auth.tokIssued γa v.Token' name) ∨
         ⌜resp = GoInterface.nil ∧ err ≠ GoInterface.nil⌝) }} := by
  iintro %Φ ⟨#Hpkg, #Hsrv, Hlt, Hrd, Hid, #Hctx, #Hirr, Hhdr, #HF⟩ HΦ
  ihave #Hperm := reqPropOkM_true_authn (GF := GF) ρ.raft ρ.kv
    (hdrBoundM true s E (GoInterface.ok ctx)) name pre hpre
  wp_apply hRR s E ρ ctx cd p (irrAuthenticate ⟨name, [], pre⟩) _ F rfl (apply.irrDepthOk_of_txnW_none rfl) $$ [Hlt Hrd Hid Hhdr]
    as %resp %err ⟨Hlt, Hrd, Hres⟩
  · iframe; iframe #
  icases Hres with (⟨%Herr, %hm, %rq', %L, %Hwire, -, Hok, -, -, -⟩ | ⟨%Hre, #HaE, -⟩)
  · subst Herr
    have hrq := irrWireOf_eq _ rq' hm Hwire (irrNoZeroEnd_admin _ rfl rfl rfl)
    have hk : apply.dispatchKind rq' = .authenticate := by
      rw [hrq]; exact dispatchKind_irrAuthenticate name pre hm
    ihave ⟨%am, %rp, %v, %Hp, Hrp, #Ht⟩ := appliedOkM_authn E ρ γa hγa rq' F resp L hk $$ Hok
    obtain ⟨Ham, Hresp⟩ := Hp
    have hname : am.name = name := by
      rw [hrq] at Ham
      simp only [apply.withHeader, irrAuthenticate, apply.irrEmpty, Option.some.injEq] at Ham
      rw [← Ham]
    iapply HΦ
    iframe Hlt Hrd
    isplitr
    · iapply applyErrIs_nil
    ileft
    isplitr
    · ipureintro; rfl
    iexists rp, v
    rw [← hname]
    iframe Hrp Ht
    ipureintro; exact Hresp
  · iapply HΦ
    iframe Hlt Hrd HaE
    iright
    ipureintro; exact Hre

end lemmas

end EtcdGrove
end Perennial

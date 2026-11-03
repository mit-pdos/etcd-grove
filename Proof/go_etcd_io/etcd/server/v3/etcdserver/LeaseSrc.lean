/-
**The lease checks' auth store, from the server's views** (the lease-src plan, 2026-11-02;
`notes/lease-src-plan.md`). Lean-first (no Rocq counterpart).

`srvAuthLeaseLb s E`, a premise of the lease discharges (`v3rpc.raftLeaseRead_of_server`,
`raftLeaseRenew_of_server`), from what `NewServer` and `Start` give, in the two modes a server runs in (`off`, `on γa`; the
generic mode `any` promises no verdict, so no lower bound): with auth off, the read side's store
(`isServerReadM`'s `isAuthStore … .off`, whose verdicts are the lower-bound ones: auth disabled,
every check passing; the request side, `isServerReqM`, has only `AuthInfoFromCtx`); with auth on,
`srvAuthLb`, whose `authStoreLbM` carries the lease checks' methods since this plan.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.LeaseCheck

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **With auth off, the store's exact triples are the lease checks' at any lower bound**: the
lower-bound verdicts' mode-off bodies are the exact ones' (auth disabled, every check passing), and
`IsAdminPermitted`'s pass gives `authApplyErrIs` (`authApplyErrIs_nil`). -/
theorem isAuthStoreLeaseLb_off (st : GoInterface) (γ : mvcc.StoreNames) (P : IProp GF) (f : val)
    (RD RW : IProp GF) (n : Nat) :
    apply.isAuthStore (GF := GF) st γ P f RD .off RW ⊢ isAuthStoreLeaseLb st RD .off n := by
  iintro #H
  iunfold apply.isAuthStore at H
  icases H with ⟨%ai, %Hai, #HPut, #HRng, -, #HAdm, -, #HEn, #HRev, -⟩
  iunfold isAuthStoreLeaseLb
  iexists ai
  isplitr
  · ipureintro; exact Hai
  isplitr
  · iintro !> %Φ !> Hrd HΦ
    iapply HEn $$ [Hrd]
    · iexact Hrd
    iintro !> %b ⟨Hrd, #Hv⟩
    iapply HΦ
    iframe Hrd
    iunfold auth.enabledVerdict at Hv
    iunfold auth.enabledVerdictFrom
    iexact Hv
  isplitr
  · iintro !> %Φ !> - HΦ
    iapply HRev $$ []
    · itrivial
    iintro !> %x -
    iapply HΦ
    iunfold auth.revisionVerdictFrom
    itrivial
  isplitr
  · iintro !> %a %info %dq %Φ !> ⟨Ha, Hrd⟩ HΦ
    iapply HAdm $$ [Ha Hrd]
    · iframe
    iintro !> %err ⟨Ha, Hrd, -, %Hoff, -⟩
    have he : err = GoInterface.nil := Hoff rfl
    subst he
    iapply HΦ
    iframe Ha Hrd
    isplitl []
    · iapply authApplyErrIs_nil
    unfold adminVerdictFrom auth.adminVerdictFrom
    ipureintro; rfl
  isplitr
  · iunfold apply.permCheck2 at HPut
    iunfold permCheck2Lb
    iintro !> %a %info %dq %key %k %dk %Φ !> ⟨Ha, Hk, Hrd, %Hlen⟩ HΦ
    iapply HPut $$ [Ha Hk Hrd]
    · iframe; ipureintro; exact Hlen
    iintro !> %err ⟨Ha, Hk, Hrd, #Herr, %Hoff, -⟩
    iapply HΦ
    iframe Ha Hk Hrd Herr
    iunfold auth.permVerdictFrom
    ipureintro; exact Hoff rfl
  · iunfold apply.permCheck3 at HRng
    iunfold apply.permCheck3Lb
    iintro !> %a %info %dq %key %re %k %e %dk %de %Φ !> ⟨Ha, Hk, He, Hrd, %Hlen⟩ HΦ
    iapply HRng $$ [Ha Hk He Hrd]
    · iframe; ipureintro; exact Hlen
    iintro !> %err ⟨Ha, Hk, He, Hrd, #Herr, %Hoff, -⟩
    iapply HΦ
    iframe Ha Hk He Hrd Herr
    iunfold auth.permVerdictFrom
    ipureintro; exact Hoff rfl

/-- **The lease checks' auth store, in the server's mode** (see the file header). -/
theorem srvAuthLeaseLb_of_server (s : Loc) (E : apply.AEnv GF) (γr : ReadNames)
    (hM : E.authMode = .off ∨ ∃ γa, E.authMode = .on γa) :
    isServerReadM (GF := GF) E.authOn s E γr ∗ srvAuthLb s E ⊢ srvAuthLeaseLb s E := by
  rcases hM with hoff | ⟨γa, hon⟩
  · unfold isServerReadM srvReadFieldsAtM srvAuthLeaseLb
    rw [hoff]
    iintro ⟨⟨%v, ⟨-, -, -, -, -, -, -, -, #Ha, #Has, -⟩⟩, -⟩
    iexists v.auth
    iframe Ha
    iintro !> %n -
    iapply isAuthStoreLeaseLb_off $$ Has
  · unfold srvAuthLb srvAuthLeaseLb
    rw [hon]
    unfold authStoreLbM
    iintro ⟨-, ⟨%au, #Ha, #Hlb⟩⟩
    iexists au
    iframe Ha
    iintro !> %n #Hn
    ihave ⟨-, #HL⟩ := Hlb $$ Hn
    iexact HL

end proof

end EtcdGrove
end Perennial

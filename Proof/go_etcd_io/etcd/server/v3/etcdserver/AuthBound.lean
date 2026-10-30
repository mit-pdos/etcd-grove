/-
**The token binding at the server's guards** (the auth plan's E1, 2026-10-24; `notes/decisions.md`,
"E1 of the auth plan"). Lean-first (no Rocq counterpart).

S5 stated the request side with the binding (`isReqAuthBound`, `AuthReqDerive.lean`: the auth info
`AuthInfoFromCtx` returns is `nil` or one bound to the request's token, `auth.ctxBound`) and derived
it of the real store (`isReqAuthBound_of_authInv`). The guards' specs state the binding gated by the
mode (the auth-mode merge, 2026-10-29; `notes/decisions.md`, "`AuthInfoFromCtx`: one spec, the
binding gated by the mode"): with auth off the server's store comes from `NewAuthStore`'s axiom,
which gives only the unbound `isReqAuth`. This file has the vocabulary of their posts:

* `srvAuthBound`: the server's store has the bound request side;
* `principalBound`: an auth info's user is bound to the request's token, or came from the client's
  TLS certificate (`AuthInfoFromTLS`, only with `ClientCertAuthEnabled`);
* `adminOutB`, `authedOutB`: the guards' outcomes, whose auth info is bound with auth on.

TLS client certificates as identity are out of the plan's scope (D-AU6): the TLS path is the
disjunct the statement names, not a binding.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthReqDerive
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthGuard
@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- **The server `s`'s store has the bound request side** (persistent): its `authStore` field's
store satisfies `isReqAuthBound` in the server's auth mode. Of the real store once `NewAuthStore`
is proved (`isReqAuthBound_of_authInv`). -/
def srvAuthBound (s : Loc) (E : apply.AEnv GF) : IProp GF :=
  iprop(∃ st : GoInterface, structFieldRef EtcdServer go!"authStore" s ↦□ st ∗
    isReqAuthBound st E.RD E.authMode)

instance srvAuthBound_persistent (s : Loc) (E : apply.AEnv GF) :
    Persistent (srvAuthBound s E) := by
  unfold srvAuthBound; infer_instance

/-- **A checked principal of the request context `ctx` is bound** in the mode `M` (persistent):
`nil`, or the user to whom the context's own token was issued (`auth.ctxTokenOf ctx`, the auth
plan's E2c; `auth.tokOk`: in `on γa`, `tokIssued`), or the server's TLS fallback is on. -/
def principalBound (s : Loc) (M : auth.AuthMode) (ctx : GoInterface)
    (ai : Option go_etcd_io.etcd.server.v3.auth.AuthInfo) : IProp GF :=
  match ai with
  | none => iprop(True)
  | some info => iprop((∃ token : GoString, ⌜auth.ctxTokenOf ctx = some token⌝ ∗
      auth.tokOk M token info.Username') ∨ srvTLSId s)

instance principalBound_persistent (s : Loc) (M : auth.AuthMode) (ctx : GoInterface)
    (ai : Option go_etcd_io.etcd.server.v3.auth.AuthInfo) :
    Persistent (principalBound (GF := GF) s M ctx ai) := by
  unfold principalBound; cases ai <;> infer_instance

/-- **An admin check's outcome with the binding**: `adminOut`, whose auth info is moreover
bound (`principalBound`) with auth on (the gate: the auth-mode merge, 2026-10-29; with auth off the
server's store has only the unbound request side, `NewAuthStore`'s axiom). -/
def adminOutB (s : Loc) (M : auth.AuthMode) (ctx err : GoInterface) : IProp GF :=
  iprop(applyErrIs err ∗
    (∀ _ : err = GoInterface.nil, ∃ ai : Option go_etcd_io.etcd.server.v3.auth.AuthInfo,
      adminRes M ai ∗ □ (⌜M.isOn = true⌝ → principalBound s M ctx ai)))

instance adminOutB_persistent (s : Loc) (M : auth.AuthMode) (ctx err : GoInterface) :
    Persistent (adminOutB (GF := GF) s M ctx err) := by
  unfold adminOutB; infer_instance

/-- `adminOutB` gives `adminOut` (the binding dropped). -/
theorem adminOut_of_adminOutB (s : Loc) (M : auth.AuthMode) (ctx err : GoInterface) :
    adminOutB (GF := GF) s M ctx err ⊢ adminOut M err := by
  iunfold adminOutB
  iunfold adminOut
  iintro ⟨#He, #Hn⟩
  iframe #
  iintro %h
  icases Hn $$ %h with ⟨%ai, #Hr, -⟩
  iexists ai
  iexact Hr

instance authInfoIs_persistent' (a : Loc) (user : GoString) (rev : w64) :
    Persistent (authInfoIs (GF := GF) a user rev) := by
  unfold authInfoIs; infer_instance

/-- **An authenticated-user check's outcome with the binding**: `authedOut`, whose auth info is
moreover bound (`principalBound`) with auth on (gated as `adminOutB`). -/
def authedOutB (s : Loc) (M : auth.AuthMode) (ctx err : GoInterface) : IProp GF :=
  iprop(applyErrIs err ∗ ⌜M.isOn = false → err = GoInterface.nil⌝ ∗
    (∀ _ : err = GoInterface.nil, ∃ ai : Option go_etcd_io.etcd.server.v3.auth.AuthInfo,
      authedRes M ai ∗ □ (⌜M.isOn = true⌝ → principalBound s M ctx ai)) ∗
    (∀ _ : err ≠ GoInterface.nil, auth.enabledVerdict M true))

instance authedOutB_persistent (s : Loc) (M : auth.AuthMode) (ctx err : GoInterface) :
    Persistent (authedOutB (GF := GF) s M ctx err) := by
  unfold authedOutB; infer_instance

/-- `authedOutB` gives `authedOut` (the binding dropped). -/
theorem authedOut_of_authedOutB (s : Loc) (M : auth.AuthMode) (ctx err : GoInterface) :
    authedOutB (GF := GF) s M ctx err ⊢ authedOut M err := by
  iunfold authedOutB
  iunfold authedOut
  iintro ⟨#He, #Hoff, #Hn, #Hne⟩
  iframe #
  iintro %h
  icases Hn $$ %h with ⟨%ai, #Hr, -⟩
  iexists ai
  iexact Hr

/-- **A bound auth info's user** is bound: from `ctxBoundOrTLS` and the auth info's fields
(`authInfoIs`), the user's token (or the TLS fallback). -/
theorem principalBound_of_ctxBoundOrTLS (s : Loc) (M : auth.AuthMode) (ctx : GoInterface) (a : Loc)
    (user : GoString) (rev : w64) :
    ctxBoundOrTLS (GF := GF) s M ctx a ∗ authInfoIs a user rev ⊢
      principalBound s M ctx (some ({ Username' := user, Revision' := rev } :
        go_etcd_io.etcd.server.v3.auth.AuthInfo)) := by
  iunfold ctxBoundOrTLS
  iunfold principalBound
  iintro ⟨#Hb, #Hai⟩
  icases Hb with (#Hb | #Ht)
  · iunfold auth.ctxBound at Hb
    icases Hb with (%Hn | ⟨%token, %Htk, #Hib⟩)
    · iunfold authInfoIs at Hai
      icases Hai with ⟨%Hnn, -, -⟩
      exact absurd Hn Hnn
    · iunfold auth.infoBound at Hib
      icases Hib with ⟨-, %user', #Hu', #Htok⟩
      iunfold authInfoIs at Hai
      icases Hai with ⟨-, #Hu, -⟩
      icombine Hu Hu' gives %Heq
      ileft
      iexists token
      isplitr
      · ipureintro; exact Htk
      rw [Heq]
      iexact Htok
  · iright; iexact Ht

/-- **The server's bound request side under the mode's gate**: a server whose store has the
bound request side with auth on (`srvAuthBound`), its store `st` (`authStore`'s field), has the bound
request side of `st` with auth on. -/
theorem srvAuthBound_gate (s : Loc) (E : apply.AEnv GF) (st : GoInterface) :
    structFieldRef EtcdServer go!"authStore" s ↦□ st ∗ □ (⌜E.authOn = true⌝ → srvAuthBound s E) ⊢
      □ (⌜E.authMode.isOn = true⌝ → isReqAuthBound st E.RD E.authMode) := by
  iintro ⟨#Has, #Hbd⟩
  iintro !> %h
  ihave #Hbd' : srvAuthBound s E $$ []
  · iapply Hbd; ipureintro; exact h
  iunfold srvAuthBound at Hbd'
  icases Hbd' with ⟨%st3, #Has3, #Hreqb⟩
  icombine Has Has3 gives %Heq3
  subst Heq3
  iexact Hreqb

/-- `principalBound_of_ctxBoundOrTLS` under the mode's gate. -/
theorem principalBound_of_ctxBoundOrTLS_gate (s : Loc) (M : auth.AuthMode) (ctx : GoInterface)
    (a : Loc) (user : GoString) (rev : w64) :
    □ (⌜M.isOn = true⌝ → ctxBoundOrTLS (GF := GF) s M ctx a) ∗ authInfoIs a user rev ⊢
      □ (⌜M.isOn = true⌝ → principalBound s M ctx (some ({ Username' := user, Revision' := rev } :
        go_etcd_io.etcd.server.v3.auth.AuthInfo))) := by
  iintro ⟨#Hb, #Hai⟩
  iintro !> %h
  iapply principalBound_of_ctxBoundOrTLS s M ctx a user rev
  isplitr
  · iapply Hb; ipureintro; exact h
  · iexact Hai

/-- **A checked principal, the anonymous one allowed** (persistent): the empty user (the check's
`&auth.AuthInfo{}` when the request carried none), or a bound one (`principalBound`). The empty user is the zero string (`zeroValDef`). -/
def principalBoundI (s : Loc) (M : auth.AuthMode) (ctx : GoInterface)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) : IProp GF :=
  iprop(⌜info.Username' = (zeroValDef : GoString)⌝ ∨ principalBound s M ctx (some info))

instance principalBoundI_persistent (s : Loc) (M : auth.AuthMode) (ctx : GoInterface)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) :
    Persistent (principalBoundI (GF := GF) s M ctx info) := by
  unfold principalBoundI; infer_instance

/-- A checked principal, bound to the context `ctx`, is bound to its token (`infoBoundT`; G2's
freeze, 2026-10-30). -/
theorem infoBoundT_of_principalBoundI (s : Loc) (M : auth.AuthMode) (ctx : GoInterface)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) :
    principalBoundI (GF := GF) s M ctx info ⊢ v3rpc.infoBoundT s M (auth.ctxTokenOf ctx) info := by
  unfold principalBoundI v3rpc.infoBoundT principalBound
  iintro H; iexact H

end defs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`srvAuthBound` of the real store** (the auth plan's E2e, 2026-10-25): a server whose
`authStore` field holds a store with the store's invariant in the server's mode, its reader
resource the store's (`auth.authRd`), has the bound request side. `auth.newAuthStore_boot`
(`auth/Boot.lean`) gives the invariant in the mode `on γa`; the server's own statement still
takes `NewAuthStore`'s axiom (mode `off`), so this is what the server derives `srvAuthBound` with
once its boot takes the store from `newAuthStore_boot`. -/
theorem srvAuthBound_of_authInv
    (hCtx : auth.authStore.AuthInfoFromCtx.spec (GF := GF) (hG := hG))
    (s stp : Loc) (R : IProp GF) (E : apply.AEnv GF)
    (hRD : E.RD = auth.authRd stp R E.authMode) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗
      structFieldRef EtcdServer go!"authStore" s ↦□ auth.authIface stp ∗
      auth.authInv stp R E.authMode ⊢ srvAuthBound s E := by
  iintro ⟨#Hpkg, #Hf, #Hinv⟩
  iunfold srvAuthBound
  iexists auth.authIface stp
  iframe Hf
  rw [hRD]
  iapply (isReqAuthBound_of_authInv hCtx stp R E.authMode) $$ [$Hpkg $Hinv]

end proof

end EtcdGrove
end Perennial

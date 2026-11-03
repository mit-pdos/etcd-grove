/-
Proof of `Spec/go_etcd_io/etcd/client/v3/Client__getToken.lean` (the auth plan's C1, 2026-10-28;
until then an axiom, the trust boundary of the client's auth part; `notes/c1-plan.md`). Lean-first
(no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.Client__getToken
public import Spec.go_etcd_io.etcd.client.v3.authClient__Authenticate
public import Spec.go_etcd_io.etcd.client.v3.credentials.perRPCCredentialBundle__UpdateAuthToken
public import Spec.errors.IsStatusErr
public import Proof.go_etcd_io.etcd.client.v3.InvLessor
public import Proof.go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Init

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3
open go_etcd_io.etcd.cache.v3 (statusErrOk)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem Client.getToken.wp_proof
    (wp_Authenticate : authClient.Authenticate.spec (GF := GF) (hG := hG))
    (wp_UpdateAuthToken : credentials.perRPCCredentialBundle.UpdateAuthToken.spec (GF := GF) (hG := hG))
    (wp_Is : errors.IsStatusErr.spec (GF := GF) (hG := hG)) :
    Client.getToken.spec (GF := GF) (hG := hG) := by
  intro c conn eps ctx cd
  wp_start as ⟨#Hrc, #Hready, Hconn, #Hctx⟩
  iunfold retryClientOk at Hrc
  icases Hrc with ⟨%Hcn, #Hlg, %tok, %atb, #Htok, #Hatb, %Htokatb⟩
  iunfold clientReady at Hready
  icases Hready with ⟨%api, %P, #Hauth, #HapiS, #Hca⟩
  iunfold clientAuthAt at Hca
  icases Hca with ⟨%u, %pw, %tok', %atb', #Hu, #Hpw, #Htok', #Hatb', #Hbun, #Htokp, #Hreg⟩
  ihave %Heq1 := typedPointsto_agree_wand _ _ _ _ _ $$ Htok Htok'
  ihave %Heq2 := typedPointsto_agree_wand _ _ _ _ _ $$ Hatb Hatb'
  subst Heq1 Heq2
  ihave #Hpe : isPkgInit (PROP := IProp GF) pkg_id.errors $$ []
  · iPkgInit
  ihave #Hpr : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.v3rpc.rpctypes $$ []
  · iPkgInit
  ihave ⟨%xan, #Han⟩ := errAuthNotEnabled_of_init $$ Hpr
  wp_auto_lc 1
  imod lc_fupd_elim_later $$ Hlc1 Hconn with #Hconn
  wp_if_destruct
  rotate_left
  · -- a token: set without a call
    icases Hbun with (%Hn | #Hb)
    · exact absurd Hn (Htokatb Hif)
    ihave #Hb' := Hb
    iunfold tokenBundleInv at Hb'
    icases Hb' with ⟨%b, %rc, %Hab, -, -⟩
    subst Hab
    wp_auto
    wp_apply wp_UpdateAuthToken b P tok $$ [Hb Htokp]
    · iframe Hb Htokp
    iapply HΦ
    isplitl
    · iapply clientErrOk_nil
    iintro !> -; ipureintro; rfl
  -- no token: a call with the user name and password, if there are both
  by_cases hu : u = []
  · rw [decide_eq_true hu]
    wp_auto
    iapply HΦ
    isplitl
    · iapply clientErrOk_nil
    iintro !> -; ipureintro; rfl
  rw [decide_eq_false hu]
  wp_auto
  by_cases hp : pw = []
  · rw [decide_eq_true hp]
    wp_auto
    iapply HΦ
    isplitl
    · iapply clientErrOk_nil
    iintro !> -; ipureintro; rfl
  rw [decide_eq_false hp]
  wp_auto
  icases Hreg with (%Hup | ⟨%Hatbn, #Hall, #Hreg, %Hsz⟩)
  · exfalso; rcases Hup with h | h
    · exact hu h
    · exact hp h
  icases Hbun with (%Hn | #Hb)
  · exact absurd Hn Hatbn
  ihave #Hapi := authObjAt_of api conn eps $$ [HapiS Hconn]
  · iframe #
  iunfold authTokReg at Hreg
  icases Hreg with ⟨%Spec, #Hrpc, #Hspec⟩
  -- the context's `Err()` gives client errors (`Authenticate`'s `ContextError`): every context's
  -- does, and a quiet one's at a descriptor of its own
  ihave Hcd : iprop(|==> ∃ cd' : context.ContextDesc (IProp GF),
      ctxOk ctx cd' ∗ ctxErrClient ctx cd') $$ []
  · iunfold ctxOk at Hctx
    icases Hctx with (#Hic | #Hq)
    · imodintro
      iexists cd
      isplitr
      · iapply ctxOk_of_isContext; iexact Hic
      iunfold client.ctxErrClientAll at Hall
      iapply Hall; iexact Hic
    · iapply quiet_ctx EtcdGrove.rpctypesEtcdError_asTarget ctx; iexact Hq
  imod Hcd with ⟨%cd', #Hok', #Hce⟩
  wp_apply wp_Authenticate api eps ctx cd' u pw Spec
      (fun (t : (pbAuthenticateResponse (GF := GF)).M) => iprop(□ P t)) $$ []
    as %resp %err Hres
  · iframe #
    ipureintro; exact Hsz
  ihave #Hb' := Hb
  iunfold tokenBundleInv at Hb'
  icases Hb' with ⟨%b, %rc, %Hab, -, -⟩
  subst Hab
  -- with a user name, `nil` never comes from here
  ihave #Hun : iprop(□ (structFieldRef go_etcd_io.etcd.client.v3.Client go!"Username" c ↦□
      ([] : GoString) -∗ ⌜False⌝)) $$ []
  · iintro !> Hu'
    ihave %Heq := typedPointsto_agree_wand _ _ _ _ _ $$ Hu Hu'
    exact absurd Heq hu
  iunfold authnCallOut at Hres
  icases Hres with (⟨%Herr, %t, Hrecv, #Hq⟩ | ⟨%Herr, #Hse, #Hcl⟩)
  · -- a token: stored
    subst Herr
    iunfold pbAuthenticateResponse at Hrecv
    icases Hrecv with ⟨%Hrn, Htk⟩
    ihave #Htk' : iprop(structFieldRef etcdserverpb.AuthenticateResponse go!"Token" resp ↦□
        (show GoString from t))
      $$ [Htk]
    · iexact Htk
    wp_auto
    wp_apply wp_UpdateAuthToken b P t $$ [Hb Hq]
    · iframe Hb
      iright; iexact Hq
    iapply HΦ
    isplitl
    · iapply clientErrOk_nil
    iintro !> -; ipureintro; rfl
  · obtain ⟨Hne, Hce', Hnull⟩ := Herr
    cases err with
    | nil => exact absurd rfl Hne
    | ok ei =>
      wp_auto
      wp_apply (wp_Is (GoInterface.ok ei) _ (Or.inl ⟨xan, rfl⟩)) $$ [$Hpe $Hse] as %bi %Hbi
      cases bi
      · -- another error: returned
        wp_auto
        iapply HΦ
        isplitl
        · unfold clientErrOk
          iframe #
          ipureintro; intro _; exact Hce'
        iintro !> Hu'
        ihave %Hf := Hun $$ Hu'
        exact Hf.elim
      · -- auth is off: no token
        wp_auto
        wp_apply wp_UpdateAuthToken b P [] $$ [Hb]
        · iframe Hb
          ileft; ipureintro; rfl
        iapply HΦ
        isplitl
        · iapply clientErrOk_nil
        iintro !> -; ipureintro; rfl

end proof

end EtcdGrove
end Perennial

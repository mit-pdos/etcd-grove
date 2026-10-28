/-
**The `UberApplier`'s admin triples at the latest state from its construction** (the auth plan's
E3n, 2026-10-27). Lean-first (no Rocq counterpart).

`uberAuthStepsL_of_base`: the uber-applier's base applier's auth layer as `NewUberApplier` leaves
it (`uberBaseAuth`, `uberIs`'s `baseAuth` and `baseShape`), its store's checks at the latest state
(`isAuthStoreL`) and admin steps carrying `X` (`isAuthStepsX`, the real store's from its
invariant: `isAuthStepsX_of_authInvTB`) give its admin triples and latest-state `Apply`
(`uberAuthStepsL`): the base chain's admin triples (`applierAdmin_uberX`) and the auth applier's
`Apply` at the latest state over an inner applier that does not reject (`applierAdmL_auth`,
`applyNR_base`), as `uberKVL_of_base` does for the KV side.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.BaseAuth
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.ApplyFnAdminL

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.apply go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- **The uber-applier's admin triples and latest-state `Apply`, from its construction** (see the
file header). -/
theorem apply.uberAuthStepsL_of_base
    (hUA : apply.applierV3backend.UserAdd.fuelSpecX (GF := GF) (hG := hG))
    (hRA : apply.applierV3backend.RoleAdd.fuelSpecX (GF := GF) (hG := hG))
    (hUGR : apply.applierV3backend.UserGrantRole.fuelSpecX (GF := GF) (hG := hG))
    (hRGP : apply.applierV3backend.RoleGrantPermission.fuelSpecX (GF := GF) (hG := hG))
    (hAE : apply.applierV3backend.AuthEnable.fuelSpecX (GF := GF) (hG := hG))
    (hAu : apply.applierV3backend.Authenticate.specX (GF := GF) (hG := hG))
    (hApplyL : apply.authApplierV3.Apply.specL (GF := GF) (hG := hG))
    (hApply : apply.applierV3backend.Apply.spec (GF := GF) (hG := hG))
    (ua : GoInterface) (E : apply.AEnv GF) (au le : GoInterface)
    (X : List auth.AuthState → IProp GF) (W : IProp GF) (L : List auth.AuthState → IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      apply.uberBaseAuth ua E au le ∗ apply.isAuthStoreL au E.RD E.authMode L ∗
      apply.isAuthStepsX au E.P E.f E.authMode X W E.RD ⊢
      apply.uberAuthStepsL ua E W (fun γa h => iprop(auth.authOwnFu γa h ∗ X h)) L := by
  iintro ⟨#Hpkg, #Hb, #HsL, #Hsteps⟩
  iunfold apply.uberBaseAuth at Hb
  icases Hb with ⟨%p, %opts, %Hpo, #Hu⟩
  obtain ⟨Hua, Hau, Hle⟩ := Hpo
  subst Hau Hle
  ihave ⟨%base, #Hbf, #Had⟩ := apply.applierAdmin_uberX hUA hRA hUGR hRGP hAE hAu E X W p opts $$
    [Hpkg Hu Hsteps]
  · iframe #
  ihave #Hu' := Hu
  iunfold apply.uberIs at Hu'
  icases Hu' with ⟨-, -, -, -, -, %base', #Hbf', -, #Hsh, #Hbase⟩
  icombine Hbf Hbf' gives %Hbb
  subst Hbb
  iunfold apply.baseAuth at Hbase
  icases Hbase with ⟨%pa, %inner, %Hpa, #Hai, -, #Has, -⟩
  iunfold apply.baseShape at Hsh
  icases Hsh with ⟨%pa', %pq, %pb, %Hpa', #Hpaq, #Hpq, -⟩
  rw [Hpa] at Hpa'
  have := apply.mkOk_ptr_inj _ _ _ Hpa'
  subst this
  ihave #Hai' := Hai
  iunfold apply.authIs at Hai'
  icases Hai' with ⟨#Hin, -⟩
  icombine Hin Hpaq gives %Hinner
  subst Hinner
  ihave #Hnr := apply.applyNR_base hApply pq pb $$ [Hpkg Hpq]
  · iframe #
  ihave #HaL : apply.authIsL E pa L $$ []
  · iunfold apply.authIsL
    iexists opts.AuthStore'
    iframe Has HsL
  ihave #HadmL := apply.applierAdmL_auth hApplyL E (.quota .backend) _ pa L $$ [Hpkg Hai HaL Hnr]
  · iframe #
  iunfold apply.uberAuthStepsL
  iexists p, opts
  isplitr
  · ipureintro; exact Hua
  iframe Hu
  iexists _
  iframe Hbf Had
  rw [Hpa]
  simp only [apply.baseChain]
  iexact HadmL

end proof

end EtcdGrove
end Perennial

#print axioms Perennial.EtcdGrove.apply.uberAuthStepsL_of_base

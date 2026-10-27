/-
**The server's applier's latest-state KV triples in the auth mode `on`** (the auth plan's E3k,
2026-10-27; E3i's "the construction handing over the server applier's latest-state facts").
Lean-first (no Rocq counterpart).

The construction leaves, with auth on, the uber-applier's base applier's auth layer at the
server's store and lessor (`srvUberBase`, `srvUberRowM true`, from `NewUberApplier`'s post).
`srv_uberKVL` gives from it the apply thread's latest-state KV triples (`apply.uberKVL`, what
`srvApplyKVOn` and `apply.Apply.kvSpecL` take), over two facts of the server's fields:

- `srvStoreLatest s E L`: its auth store's checks at the latest state for the family `L`
  (`isAuthStoreL`); the real store meets it from its invariant (`apply.isAuthStoreL_of_authInv`)
  when the environment's reader resource is the store's (`auth.authRd`), its family
  `auth.latestRes`; the server's rows do not yet carry the store's invariant, so it is a premise;
- `srvLessorNil s`: its lessor finds no lease (`apply.lookupNil`), a named premise: the server's
  lessor is the real one (`lease.NewLessor`), whose lookups find a lease once one is granted; a
  workload granting none (`examples/authkv`) is where it holds.

The admin side (`srv_uberAuthStepsL_on`, E3n): the built part's store fact and the apply thread's
auth row (`srvAuthApplyResB`, whose admin steps are at the environment's hook since E3n) give the
apply thread's latest-state admin triples (`apply.uberAuthStepsL`) at the admin steps' resource
`adminW` (the store's half of `be` borrowed from the rest, blocker 1's row).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ServerOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.UberKVLBase
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.UberAdmLBase
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.StoreLatest

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The server's auth store's checks at the latest state** for the family `L` (persistent). -/
def srvStoreLatest (s : Loc) (E : apply.AEnv GF) (L : List auth.AuthState → IProp GF) : IProp GF :=
  iprop(∃ au : GoInterface, srvAuthStoreAddr s ↦□ au ∗ apply.isAuthStoreL au E.RD E.authMode L)

instance srvStoreLatest_persistent (s : Loc) (E : apply.AEnv GF)
    (L : List auth.AuthState → IProp GF) : Persistent (srvStoreLatest s E L) := by
  unfold srvStoreLatest; infer_instance

/-- **The server's lessor finds no lease** (persistent; a named premise, see the file header). -/
def srvLessorNil (s : Loc) : IProp GF :=
  iprop(∃ le : GoInterface, srvLessorAddr s ↦□ le ∗ apply.lookupNil le)

instance srvLessorNil_persistent (s : Loc) : Persistent (srvLessorNil (GF := GF) s) := by
  unfold srvLessorNil; infer_instance

end defs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- **The server's uber-applier's KV triples at the latest state** (see the file header). -/
theorem srv_uberKVL
    (hRange : apply.authApplierV3.Range.specL (GF := GF) (hG := hG))
    (hDel : apply.authApplierV3.DeleteRange.specL (GF := GF) (hG := hG))
    (hPut : apply.authApplierV3.Put.specL (GF := GF) (hG := hG))
    (hTxn : apply.authApplierV3.Txn.specL (GF := GF) (hG := hG))
    (s : Loc) (ua : GoInterface) (E : apply.AEnv GF) (L : List auth.AuthState → IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      srvUberBase s ua E ∗ srvStoreLatest s E L ∗ srvLessorNil s ⊢
      apply.uberKVL ua E (.quota .backend) L := by
  iintro ⟨#Hpkg, #Hb, #Hst, #Hln⟩
  iunfold srvUberBase at Hb
  icases Hb with ⟨%au, %le, #Hauf, #Hlef, #Hub, -⟩
  iunfold srvStoreLatest at Hst
  icases Hst with ⟨%au', #Hauf', #HL⟩
  iunfold srvLessorNil at Hln
  icases Hln with ⟨%le', #Hlef', #Hnil⟩
  icombine Hauf Hauf' gives %Ha
  icombine Hlef Hlef' gives %Hl
  subst Ha Hl
  iapply apply.uberKVL_of_base hRange hDel hPut hTxn ua E au le L
  iframe Hpkg Hub HL Hnil

/-- **The server's uber-applier's KV triples at the latest state, with auth on** (the auth plan's
E3l): `srv_uberKVL` with `srvStoreLatest` discharged by the built part's store fact
(`srvUberBase`'s `authStoreLatestM`, of the store's invariant), at the family
`auth.latestRes stl` of the store `stl` the server's `authStore` field holds. -/
theorem srv_uberKVL_on
    (hRange : apply.authApplierV3.Range.specL (GF := GF) (hG := hG))
    (hDel : apply.authApplierV3.DeleteRange.specL (GF := GF) (hG := hG))
    (hPut : apply.authApplierV3.Put.specL (GF := GF) (hG := hG))
    (hTxn : apply.authApplierV3.Txn.specL (GF := GF) (hG := hG))
    (s : Loc) (ua : GoInterface) (E : apply.AEnv GF) (γa : auth.AuthNames)
    (hM : E.authMode = .on γa) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      srvUberBase s ua E ∗ srvLessorNil s ⊢
      ∃ stl : Loc, srvAuthStoreAddr s ↦□ auth.authIface stl ∗
        apply.uberKVL ua E (.quota .backend) (auth.latestRes stl (.on γa)) := by
  iintro ⟨#Hpkg, #Hb, #Hln⟩
  iunfold srvUberBase at Hb
  icases Hb with ⟨%au, %le, #Hauf, #Hlef, #Hub, %stl, %Hau, #HL⟩
  subst Hau
  have hL : authStoreLatestM (GF := GF) E.authMode (auth.authIface stl) E.RD stl =
      apply.isAuthStoreL (auth.authIface stl) E.RD E.authMode (auth.latestRes stl (.on γa)) := by
    rw [hM]; rfl
  rw [hL]
  iexists stl
  iframe Hauf
  iapply srv_uberKVL hRange hDel hPut hTxn s ua E (auth.latestRes stl (.on γa))
  iframe Hpkg Hln
  isplitr
  · iunfold srvUberBase
    iexists (auth.authIface stl), le
    iframe Hauf Hlef Hub
    iexists stl
    isplitr
    · ipureintro; rfl
    rw [hL]; iexact HL
  iunfold srvStoreLatest
  iexists (auth.authIface stl)
  iframe Hauf HL

/-- **The server's uber-applier's admin triples at the latest state, with auth on** (the auth
plan's E3n): the built part's store fact (`srvUberBase`) and the apply thread's auth row
(`srvAuthApplyResB`: the store's admin steps at the environment's hook, at `adminW`) give
`apply.uberAuthStepsL` at the admin steps' resource `adminW stl bel` (its write token `T`), for the
authority with its fuel and tie, the family `auth.latestRes stl`; the row is given back. -/
theorem srv_uberAuthStepsL_on
    (hUA : apply.applierV3backend.UserAdd.fuelSpecX (GF := GF) (hG := hG))
    (hRA : apply.applierV3backend.RoleAdd.fuelSpecX (GF := GF) (hG := hG))
    (hUGR : apply.applierV3backend.UserGrantRole.fuelSpecX (GF := GF) (hG := hG))
    (hRGP : apply.applierV3backend.RoleGrantPermission.fuelSpecX (GF := GF) (hG := hG))
    (hAE : apply.applierV3backend.AuthEnable.fuelSpecX (GF := GF) (hG := hG))
    (hApplyL : apply.authApplierV3.Apply.specL (GF := GF) (hG := hG))
    (hApply : apply.applierV3backend.Apply.spec (GF := GF) (hG := hG))
    (s : Loc) (ua : GoInterface) (E : apply.AEnv GF) (γa : auth.AuthNames) (st : auth.AuthState)
    (hM : E.authMode = .on γa) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      srvUberBase s ua E ∗ srvAuthApplyResB s E st ⊢
      srvAuthApplyResB s E st ∗ ∃ (stl bel : Loc) (T : IProp GF),
        srvAuthStoreAddr s ↦□ auth.authIface stl ∗
        apply.uberAuthStepsL ua E (adminW stl bel (.on γa) E.P E.f T)
          (fun γa' h => iprop(auth.authOwnFu γa' h ∗ auth.tieRes stl (.on γa) h))
          (auth.latestRes stl (.on γa)) := by
  iintro ⟨#Hpkg, #Hb, HR⟩
  iunfold srvUberBase at Hb
  icases Hb with ⟨%au, %le, #Hauf, #Hlef, #Hub, %stl, %Hau, #HL⟩
  subst Hau
  iunfold srvAuthApplyResB at HR
  icases HR with ⟨%stl', %bel, #Hf, HB, #Hlens, #Hro⟩
  icombine Hauf Hf gives %Hst
  have Hst' := apply.mkOk_ptr_inj _ _ _ Hst
  subst Hst'
  have hB : authApplyResB (GF := GF) E.authMode stl st bel E.P E.f =
      authApplyResB (GF := GF) (.on γa) stl st bel E.P E.f := by rw [hM]
  irevert HB
  rw [hB]
  unfold authApplyResB
  iintro ⟨%hs, %P0, %f0, %T, %be, Ho, HX, #Hw, HT, Htp, %Hl, #Hwa, #Hsteps⟩
  isplitl [Ho HX HT Htp]
  · iunfold srvAuthApplyResB
    iexists stl, bel
    iframe Hf Hlens Hro
    rw [hB]
    unfold authApplyResB
    iexists hs, P0, f0, T, be
    iframe Ho HX Hw HT Htp Hwa Hsteps
    ipureintro; exact Hl
  iexists stl, bel, T
  iframe Hauf
  have hL : authStoreLatestM (GF := GF) E.authMode (auth.authIface stl) E.RD stl =
      apply.isAuthStoreL (auth.authIface stl) E.RD E.authMode (auth.latestRes stl (.on γa)) := by
    rw [hM]; rfl
  iapply (apply.uberAuthStepsL_of_base hUA hRA hUGR hRGP hAE hApplyL hApply ua E (auth.authIface stl)
    le (auth.tieRes stl (.on γa)) (adminW stl bel (.on γa) E.P E.f T) (auth.latestRes stl (.on γa)))
  iframe Hpkg Hub
  isplitr
  · rw [← hL]; iexact HL
  rw [hM]
  iexact Hsteps

end proof

end EtcdGrove
end Perennial

#print axioms Perennial.EtcdGrove.srv_uberKVL
#print axioms Perennial.EtcdGrove.srv_uberKVL_on
#print axioms Perennial.EtcdGrove.srv_uberAuthStepsL_on

/-
Proof of the spec of the same name (the auth plan's E2j, 2026-10-26). Lean-first (no Rocq
counterpart). The backend's `GetUser` answers from the latest state; the reply copies the user's
roles (`append` onto the response's nil slice).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__UserGet
public import Proof.go_etcd_io.etcd.server.v3.auth.AdminLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.auth auth go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

theorem auth.authStore.UserGet.wp_proof :
    auth.authStore.UserGet.spec (GF := GF) (hG := hG) := by
  intro st R M P f T hs r name
  wp_start as ⟨#Hinv, Hreq, Hown, HWR⟩
  iunfold userGetReqIs at Hreq
  icases Hreq with ⟨%Hr, #Hname⟩
  icases authErrVar_of_init .userNotFound $$ Hpkg with ⟨%eNF, #HeNF⟩
  simp only [AuthErr.var]
  iunfold authWR at HWR
  icases HWR with ⟨⟨%be, Hbe, #Hbeok⟩, HT, Hen, Hca⟩
  ihave #Hbeok' := Hbeok
  iunfold authWBackendOk at Hbeok'
  icases Hbeok' with ⟨%bi, %Hbi, -, -, #HRds⟩
  iunfold authBackendReads at HRds
  icases HRds with ⟨#HGU, -, -, -⟩
  subst Hbi
  (try wp_auto)
  wp_bind (App (Val #(methods bi.ty go!"GetUser" bi.v)) (Val #name))
  iapply HGU $$ %hs %name [$HT $Hown]
  inext
  iintro %u ⟨HT, Hown, %sta, %Hl, Hu⟩
  (try wp_auto)
  wp_if_destruct
  · -- no such user
    ihave %Hnone := userOut_null sta name $$ Hu
    (try wp_auto)
    iapply HΦ
    iframe Hown
    isplitl [Hbe HT Hen Hca]
    · iunfold authWR; iframe HT Hen Hca; iexists (GoInterface.ok bi); iframe Hbe Hbeok
    iexists sta
    isplitr
    · ipureintro; exact Hl
    iunfold userGetOut
    simp only [show sta.users.lookup name = none from Hnone]
    isplitr
    · ipureintro; trivial
    iunfold authErrOf
    simp only [AuthErr.var]
    iexists eNF
    iframe HeNF
    ipureintro; rfl
  ihave Hu' := auth.userOut_some_named _ sta name Hif $$ Hu
  icases Hu' with ⟨%roles, %ur, %Hur, Hu⟩
  obtain ⟨Hlook, Hurn, Hurr, -⟩ := Hur
  iunfold ownUser at Hu
  icases Hu with ⟨%ums, %unm, %upw, %url, %uo, %uuf, %usc, Hup, #Hunm, #Hupw, #Hurl, #Huo⟩
  icases typedPointsto_split _ _ _ $$ Hup with Hup
  simp only [TypedPointsto.typedPointstoDef]
  iNamed Hup
  (try wp_auto)
  ihave Hnil := ownSlice_nil (V := GoString) (DFrac.own 1)
  ihave Hnilc := ownSliceCap_nil (V := GoString)
  wp_apply (wp_slice_append slice.nil ([] : List GoString) url ur.roles DFrac.discard)
    $$ [$Hnil $Hnilc $Hurl] as %sl' ⟨Hsl, -, -⟩
  (try wp_auto)
  iapply HΦ
  iframe Hown
  isplitl [Hbe HT Hen Hca]
  · iunfold authWR; iframe HT Hen Hca; iexists (GoInterface.ok bi); iframe Hbe Hbeok
  iexists sta
  isplitr
  · ipureintro; exact Hl
  iunfold userGetOut
  simp only [show sta.users.lookup name = some roles from Hlook]
  isplitr
  · ipureintro; trivial
  iexists _
  iframe
  simp only [List.nil_append, Hurr]
  iexact Hsl

end proof

end EtcdGrove
end Perennial

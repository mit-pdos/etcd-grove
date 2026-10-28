/-
Proof of the spec of the same name (the auth plan's E2j, 2026-10-26). Lean-first (no Rocq
counterpart). The backend's `GetRole` answers from the latest state; the reply is `root`'s fixed
permission for `root`, else a copy of the role's permissions (`append` onto the response's nil
slice).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__RoleGet
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

theorem auth.authStore.RoleGet.wp_proof :
    auth.authStore.RoleGet.spec (GF := GF) (hG := hG) := by
  intro st R M P f T hs r name
  wp_start as ⟨#Hinv, Hreq, Hown, HWR⟩
  iunfold roleGetReqIs at Hreq
  icases Hreq with ⟨%Hr, #Hname⟩
  icases authErrVar_of_init .roleNotFound $$ Hpkg with ⟨%eNF, #HeNF⟩
  simp only [AuthErr.var]
  iunfold authWR at HWR
  icases HWR with ⟨⟨%be, Hbe, #Hbeok⟩, HT, Hen, Hca⟩
  ihave #Hbeok' := Hbeok
  iunfold authWBackendOk at Hbeok'
  icases Hbeok' with ⟨%bi, %Hbi, -, -, #HRds⟩
  iunfold authBackendReads at HRds
  icases HRds with ⟨-, #HGR, -, -⟩
  subst Hbi
  (try wp_auto)
  wp_bind (App (Val #(methods bi.ty go!"GetRole" bi.v)) (Val #name))
  iapply HGR $$ %hs %name [$HT $Hown]
  inext
  iintro %ro ⟨HT, Hown, %sta, %Hl, Hro⟩
  (try wp_auto)
  wp_if_destruct
  · -- no such role
    ihave %Hnone := roleOut_null sta name $$ Hro
    (try wp_auto)
    iapply HΦ
    iframe Hown
    isplitl [Hbe HT Hen Hca]
    · iunfold authWR; iframe HT Hen Hca; iexists (GoInterface.ok bi); iframe Hbe Hbeok
    iexists sta
    isplitr
    · ipureintro; exact Hl
    iunfold roleGetOut
    simp only [show sta.roles.lookup name = none from Hnone]
    isplitr
    · ipureintro; trivial
    iunfold authErrOf
    simp only [AuthErr.var]
    iexists eNF
    iframe HeNF
    ipureintro; rfl
  ihave Hro' := roleOut_some _ sta name Hif $$ Hro
  icases Hro' with ⟨%ps, %rr, %Hrr, Hro⟩
  obtain ⟨Hlook, Hrrn, Hrrp⟩ := Hrr
  iunfold ownRole at Hro
  icases Hro with ⟨%rms, %rnm, %rkp, %pl, %ruf, %rsc, Hrp, #Hrnm, #Hrkp, %Hpl, Hperms⟩
  icases typedPointsto_split _ _ _ $$ Hrp with Hrp
  simp only [TypedPointsto.typedPointstoDef]
  iNamed Hrp
  (try wp_auto)
  wp_apply wp_bytes_to_string rnm rr.name DFrac.discard $$ [Hrnm] as -
  · iexact Hrnm
  (try wp_auto)
  obtain ⟨rt, hrt⟩ : ∃ x : GoString, x = go!"root" := ⟨_, rfl⟩
  rw [← hrt]
  wp_if_destruct
  · -- `root`: its fixed permission
    (try wp_auto)
    wp_apply wp_slice_literal (V := Loc) [_]
    isplitr
    · ipureintro; rfl
    iintro %lsl ⟨Hlsl, -⟩
    ihave Hnil := ownSlice_nil (V := Loc) (DFrac.own 1)
    ihave Hnilc := ownSliceCap_nil (V := Loc)
    wp_apply (wp_slice_append slice.nil ([] : List Loc) _ [globalAddr rootPerm] (DFrac.own 1))
      $$ [$Hnil $Hnilc $Hlsl] as %sl' ⟨Hsl, -, -⟩
    (try wp_auto)
    iapply HΦ
    iframe Hown
    isplitl [Hbe HT Hen Hca]
    · iunfold authWR; iframe HT Hen Hca; iexists (GoInterface.ok bi); iframe Hbe Hbeok
    iexists sta
    isplitr
    · ipureintro; exact Hl
    iunfold roleGetOut
    simp only [show sta.roles.lookup name = some ps from Hlook]
    isplitr
    · ipureintro; trivial
    iexists _
    iframe
    ileft
    ipureintro
    rw [← Hrrn]
    first | exact hrt | (unfold rootRole; exact hrt) | (subst Hif; exact hrt)
  -- another role: a copy of its permissions
  (try wp_auto)
  ihave Hnil := ownSlice_nil (V := Loc) (DFrac.own 1)
  ihave Hnilc := ownSliceCap_nil (V := Loc)
  wp_apply (wp_slice_append slice.nil ([] : List Loc) rkp pl DFrac.discard)
    $$ [$Hnil $Hnilc $Hrkp] as %sl' ⟨Hsl, -, -⟩
  (try wp_auto)
  iapply HΦ
  iframe Hown
  isplitl [Hbe HT Hen Hca]
  · iunfold authWR; iframe HT Hen Hca; iexists (GoInterface.ok bi); iframe Hbe Hbeok
  iexists sta
  isplitr
  · ipureintro; exact Hl
  iunfold roleGetOut
  simp only [show sta.roles.lookup name = some ps from Hlook]
  isplitr
  · ipureintro; trivial
  iexists _
  iframe
  iright
  iexists pl, rr.perms
  simp only [List.nil_append]
  iframe Hsl Hperms
  ipureintro
  exact ⟨Hpl, Hrrp⟩

end proof

end EtcdGrove
end Perennial

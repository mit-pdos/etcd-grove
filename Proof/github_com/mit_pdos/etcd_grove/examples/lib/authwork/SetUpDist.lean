/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/lib/authwork/SetUpDist.lean` (F7 stage S4, step 2).
Lean-first (no Rocq counterpart).

`SetUp.lean`'s proof at the cluster view. The puts: the two nested loops, each put in a timeout context
with no outgoing metadata (`client.wp_WithTimeout_bgMd`), through the `*Client`'s promoted `Put` (its `KV`
field, `userClientAt`) to `KV_PutOn_dist` with the caller's persistent update, the context cancelled
after the call. The admin calls: one such context, cancelled by the `defer` at every return, each call
through the client's `Auth` field (`authClientAt`) to its `Auth_*_dist` contract, with the anonymous
update and the reply of `SetupInvDist.lean` (the client's view of the auth history turned into `SetUp`'s
cell at the start, `setup_alloc`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.authwork.SetUpDist
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.authwork.Principals
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.authwork.keyOf
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.KVPutOnDist
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.AuthUserAddDist
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.AuthUserGrantRoleDist
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.AuthRoleAddDist
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.AuthRoleGrantPermissionDist
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.AuthAuthEnableDist
public import Spec.context.WithTimeoutBackgroundMd
public import Spec.context.ErrAny
public import Perennial.Spec.context.Background
public import Proof.go_etcd_io.etcd.client.v3.TimeoutCtx
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.authwork.SetupInvDist
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_auth

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.authwork.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [esrv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

set_option maxHeartbeats 1600000 in
theorem SetUp.wp_proof_dist
    (hWT : context.WithTimeoutBackgroundMd.spec (GF := GF) (hG := hG))
    (wp_ErrAny : context.ErrAny.spec (GF := GF) (hG := hG))
    (wp_Principals : Principals.spec (GF := GF) (hG := hG))
    (wp_keyOf : keyOf.spec (GF := GF) (hG := hG))
    (wp_PutOn : etcd_dist.authd.KV_PutOn_dist.spec (GF := GF) (hG := hG))
    (wp_UserAdd : etcd_dist.authd.Auth_UserAdd_dist.spec (GF := GF) (hG := hG))
    (wp_UserGrantRole : etcd_dist.authd.Auth_UserGrantRole_dist.spec (GF := GF) (hG := hG))
    (wp_RoleAdd : etcd_dist.authd.Auth_RoleAdd_dist.spec (GF := GF) (hG := hG))
    (wp_RoleGrantPermission : etcd_dist.authd.Auth_RoleGrantPermission_dist.spec (GF := GF) (hG := hG))
    (wp_AuthEnable : etcd_dist.authd.Auth_AuthEnable_dist.spec (GF := GF) (hG := hG)) :
    SetUp.spec_dist (GF := GF) (hG := hG) := by
  intro EA FA RA π cl api ap eps V Γ cfg γR L₀ hauth hlog hP hAs
  wp_start as ⟨Hlt, Huc0, Hac0, #HL0, #Hkv, Hview⟩
  iunfold etcd_dist.authd.userClientAt at Huc0
  icases Huc0 with ⟨#Hkc, #Hcfg, %Htok⟩
  ihave #Huc : (□ etcd_dist.authd.userClientAt cl api eps V Γ cfg : IProp GF) $$ []
  · imodintro; iunfold etcd_dist.authd.userClientAt; iframe #; ipureintro; exact Htok
  iunfold etcd_dist.authd.authClientAt at Hac0
  icases Hac0 with ⟨#Hnc, #Hnp, #Hcfg', %Htok', #Hauf, #Hms⟩
  ihave #Hac : (□ etcd_dist.authd.authClientAt cl ap eps V Γ cfg : IProp GF) $$ []
  · imodintro; iunfold etcd_dist.authd.authClientAt; iframe #; ipureintro; exact Htok'
  ihave Hkc' := Hkc
  iunfold etcd_dist.kvClientAt at Hkc'
  icases Hkc' with ⟨-, -, #Hkvf, -⟩
  ihave #Hkv' : (□ ∀ k : GoString, ⌜k ∈ setupKeys⌝ -∗
      etcd_dist.authd.writeAuD Γ.kv (etcd_dist.authd.principalOf cfg)
        (.put (putWireOf (opPutModel k go!"setup" []))) L₀ (fun _ => iprop(True)) : IProp GF) $$ []
  · rw [hP]; iexact Hkv
  have hom : etcd_dist.authd.outTokOk (etcd_dist.authd.principalOf cfg) none := etcd_dist.authd.outTokOk_none _
  imod (setup_alloc Γ.kv ⊤) $$ Hview with ⟨%γz, #Hc, #Hn⟩
  ihave #Pc : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply wp_Principals as %psl Hpsl
  ihave %Hpl := ownSlice_len $$ Hpsl
  (try wp_auto)
  ihave #Hnil : optsAt (GF := GF) slice.nil [] $$ []
  · iunfold optsAt
    iexists ([] : List GoFunc)
    isplitl
    · iapply ownSlice_nil
    isplitl
    · ipureintro; rfl
    imodintro
    iintro %i %f %g %Hf %Hg
    simp at Hf
  ihave HI : (∃ (j : w64) (w0 : GoString),
      "i" ∷ i_ptr ↦ j ∗ "who" ∷ who_ptr ↦ w0 ∗ "Hpsl" ∷ psl ↦* principals ∗ "Hlt" ∷ levelTok 0 ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z psl.len⌝ : IProp GF) $$ [i who Hpsl Hlt]
  · iexists W64 0, _
    iframe
    ipureintro
    constructor <;> word
  wp_for HI
  wp_if_destruct
  · have Hlt : sint.Z j < sint.Z psl.len :=
      Classical.byContradiction fun h => by simp [h] at Hif
    have Hb' : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z psl.len := ⟨Hj.1, Hlt⟩
    simp only [Hb', _root_.and_self, ↓reduceIte]
    list_elem principals (sint.nat j) as w
    have hwm : w ∈ principals := List.mem_of_getElem? Hw_lookup
    wp_apply wp_load_slice_index psl (sint.Z j) principals (DFrac.own 1) w Hj.1 $$ [Hpsl] as Hpsl
    · iframe; ipureintro; exact Hw_lookup
    (try wp_auto)
    wp_apply wp_slice_literal (V := GoString) keyParts
    isplitr
    · ipureintro; rfl
    iintro %xsl ⟨Hxsl, -⟩
    simp only [go.arrayLiteralSize, List.foldl, Int.reduceAdd,
      show max (max (2 : Int) 0) 0 = 2 from rfl]
    (try wp_auto)
    rename_i oi_ptr
    ihave HJ : (∃ (n : w64) (x0 : GoString),
        "i" ∷ i_ptr ↦ n ∗ "x" ∷ x_ptr ↦ x0 ∗ "Hxsl" ∷ _ ↦* keyParts ∗ "Hlt" ∷ levelTok 0 ∗
        "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ 2⌝ : IProp GF) $$ [i x Hxsl Hlt]
    · iexists W64 0, _
      iframe
      ipureintro
      constructor <;> word
    wp_for HJ
    wp_if_destruct
    · have Hlt2 : sint.Z n < sint.Z (W64 2) := by simpa using Hif
      have Hb2 : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z (W64 2) := ⟨Hn.1, Hlt2⟩
      simp only [Hb2, _root_.and_self, ↓reduceIte]
      have Hnk : sint.nat n < keyParts.length := by rw [show keyParts.length = 2 from rfl]; word
      list_elem keyParts (sint.nat n) as x
      have hxm : x ∈ keyParts := List.mem_of_getElem? Hx_lookup
      wp_apply wp_load_slice_index _ (sint.Z n) keyParts (DFrac.own 1) x Hn.1 $$ [Hxsl] as Hxsl
      · iframe; ipureintro; exact Hx_lookup
      (try wp_auto)
      wp_apply context.wp_Background
      (try wp_auto)
      wp_apply (client.wp_WithTimeout_bgMd hWT wp_ErrAny hAs _) $$ []
        as %cctx %cd %cancel ⟨#Hcancel, #Hctx, #Hce, -, #Hout, -⟩
      (try wp_auto)
      wp_apply wp_keyOf x w go!"d"
      (try wp_auto)
      have hk : keyOfK x w go!"d" ∈ setupKeys := by
        unfold setupKeys; exact List.mem_flatMap.2 ⟨w, hwm, List.mem_map.2 ⟨x, hxm, rfl⟩⟩
      rw [go_etcd_io.etcd.client.v3.Client.TypeAssumptions.ptr_Put_unfold.method_unfold]
      wp_pures
      wp_auto
      wp_apply (wp_PutOn cl api eps V Γ cfg γR L₀ cctx cd none (keyOfK x w go!"d") go!"setup"
          slice.nil [] (fun _ => iprop(True)) hauth hlog hom) $$ [$Hlt] as %resp %err ⟨Hlt, Hout'⟩
      · iframe #
        isplitr
        · ipureintro
          refine ⟨?_, ?_, Or.inl ?_⟩ <;>
            simp [OpFull.putPanics, opPutModel, opFold, OpFull.putInit, OpFull.newOp, OpModel.zero,
              putWireOf]
        isplitl
        · iapply Hkv'; ipureintro; exact hk
        ipureintro
        exact opSizeOk_opPutModel (K := 2 ^ 28) (E := 0) (V := 2 ^ 28) (optsKeep_nil _ _ _)
          ((show ∀ k ∈ setupKeys, k.length ≤ 2 ^ 28 by decide) _ hk) (by decide) (by decide)
      (try wp_auto)
      wp_apply Hcancel
      icases Hout' with (⟨%Herr, -⟩ | %Herr)
      · subst Herr
        (try wp_auto)
        wp_for_post
        iframe
        iexists n + W64 1, x
        iframe
        ipureintro; constructor <;> word
      · cases err with
        | nil => exact absurd rfl Herr.1
        | ok e =>
          (try wp_auto)
          wp_for_post
          wp_for_post
          (try wp_auto)
          iapply HΦ
          iframe Hlt
          simp only [Bool.false_eq_true, ↓reduceIte]
          itrivial
    · (try wp_auto)
      wp_for_post
      iframe
      iexists j + W64 1, w
      iframe
      ipureintro; constructor <;> word
  · (try wp_auto)
    wp_apply context.wp_Background
    (try wp_auto)
    wp_apply (client.wp_WithTimeout_bgMd hWT wp_ErrAny hAs _) $$ []
      as %cctx %cd %cancel ⟨#Hcancel, #Hctx, #Hce, -, #Hout, -⟩
    (try wp_auto)
    -- UserAdd(root)
    wp_apply (wp_UserAdd cl ap eps V Γ cfg γR cctx cd none go!"root" go!"root-pw"
        (fun _ => effLb Γ.kv 0) hauth hlog hom) $$ [$Hlt] as %resp0 %err0 ⟨Hlt, Hout0⟩
    · iframe #
      isplitr
      · ipureintro; decide
      iintro !> %um %hum
      iapply (setupD_histAu γR Γ.kv γz 0 _
        (setupReqAtD_userAdd 0 go!"root" um (fun um h1 h3 h2 => ⟨um, rfl, h2, h1, h3⟩) hum.1 hum.2) (by decide)
        _ hP) $$ Hc Hn
    icases Hout0 with (⟨%Herr0, Hq0⟩ | %Herr0)
    rotate_left
    · cases err0 with
      | nil => exact absurd rfl Herr0.1
      | ok e =>
        (try wp_auto)
        wp_apply Hcancel
        (try wp_auto)
        iapply HΦ
        iframe Hlt
        simp only [Bool.false_eq_true, ↓reduceIte]
        itrivial
    subst Herr0
    icases Hq0 with ⟨%um0, %hum0, Hq0⟩
    imod (setupD_reply eps Γ γR γz 0 _ ⟨um0, rfl, hum0.2.2, hum0.1, hum0.2.1⟩ ⊤ (fun _ _ => CoPset.mem_full)
      (fun _ _ => CoPset.mem_full) _ hP) $$ Hc Hn Hq0 with #F0
    (try wp_auto)
    -- UserGrantRole(root, root)
    wp_apply (wp_UserGrantRole cl ap eps V Γ cfg γR cctx cd none go!"root" go!"root"
        (fun _ => effLb Γ.kv 1) hauth hlog hom) $$ [$Hlt] as %resp1 %err1 ⟨Hlt, Hout1⟩
    · iframe #
      isplitr
      · ipureintro; decide
      iapply (setupD_histAu γR Γ.kv γz 1 _ (setupReqAtD_of 1 _ rfl) (by decide) _ hP) $$ Hc Hn
    icases Hout1 with (⟨%Herr1, Hq1⟩ | %Herr1)
    rotate_left
    · cases err1 with
      | nil => exact absurd rfl Herr1.1
      | ok e =>
        (try wp_auto)
        wp_apply Hcancel
        (try wp_auto)
        iapply HΦ
        iframe Hlt
        simp only [Bool.false_eq_true, ↓reduceIte]
        itrivial
    subst Herr1
    imod (setupD_reply eps Γ γR γz 1 _ rfl ⊤ (fun _ _ => CoPset.mem_full)
      (fun _ _ => CoPset.mem_full) _ hP) $$ Hc Hn Hq1 with #F1
    (try wp_auto)
    -- RoleAdd(r)
    wp_apply (wp_RoleAdd cl ap eps V Γ cfg γR cctx cd none go!"r"
        (fun _ => effLb Γ.kv 2) hauth hlog hom) $$ [$Hlt] as %resp2 %err2 ⟨Hlt, Hout2⟩
    · iframe #
      isplitr
      · ipureintro; decide
      iapply (setupD_histAu γR Γ.kv γz 2 _ (setupReqAtD_of 2 _ rfl) (by decide) _ hP) $$ Hc Hn
    icases Hout2 with (⟨%Herr2, Hq2⟩ | %Herr2)
    rotate_left
    · cases err2 with
      | nil => exact absurd rfl Herr2.1
      | ok e =>
        (try wp_auto)
        wp_apply Hcancel
        (try wp_auto)
        iapply HΦ
        iframe Hlt
        simp only [Bool.false_eq_true, ↓reduceIte]
        itrivial
    subst Herr2
    imod (setupD_reply eps Γ γR γz 2 _ rfl ⊤ (fun _ _ => CoPset.mem_full)
      (fun _ _ => CoPset.mem_full) _ hP) $$ Hc Hn Hq2 with #F2
    (try wp_auto)
    -- RoleGrantPermission(r, a, b, READWRITE)
    wp_apply (wp_RoleGrantPermission cl ap eps V Γ cfg γR cctx cd none go!"r" go!"a" go!"b" (W32 2)
        (fun _ => effLb Γ.kv 3) hauth hlog hom) $$ [$Hlt] as %resp3 %err3 ⟨Hlt, Hout3⟩
    · iframe #
      isplitr
      · ipureintro; decide
      iapply (setupD_histAu γR Γ.kv γz 3
        (irrRoleGrantPermission go!"r" (some (⟨W32 2, go!"a", go!"b"⟩ : auth.PermW)))
        (setupReqAtD_of 3 _ rfl) (by decide) _ hP) $$ Hc Hn
    icases Hout3 with (⟨%Herr3, Hq3⟩ | %Herr3)
    rotate_left
    · cases err3 with
      | nil => exact absurd rfl Herr3.1
      | ok e =>
        (try wp_auto)
        wp_apply Hcancel
        (try wp_auto)
        iapply HΦ
        iframe Hlt
        simp only [Bool.false_eq_true, ↓reduceIte]
        itrivial
    subst Herr3
    imod (setupD_reply eps Γ γR γz 3 (irrRoleGrantPermission go!"r" (some (⟨W32 2, go!"a", go!"b"⟩ : auth.PermW)))
      rfl ⊤ (fun _ _ => CoPset.mem_full) (fun _ _ => CoPset.mem_full) _ hP) $$ Hc Hn Hq3 with #F3
    (try wp_auto)
    -- UserAdd(u)
    wp_apply (wp_UserAdd cl ap eps V Γ cfg γR cctx cd none go!"u" go!"u-pw"
        (fun _ => effLb Γ.kv 4) hauth hlog hom) $$ [$Hlt] as %resp4 %err4 ⟨Hlt, Hout4⟩
    · iframe #
      isplitr
      · ipureintro; decide
      iintro !> %um %hum
      iapply (setupD_histAu γR Γ.kv γz 4 _
        (setupReqAtD_userAdd 4 go!"u" um (fun um h1 h3 h2 => ⟨um, rfl, h2, h1, h3⟩) hum.1 hum.2) (by decide)
        _ hP) $$ Hc Hn
    icases Hout4 with (⟨%Herr4, Hq4⟩ | %Herr4)
    rotate_left
    · cases err4 with
      | nil => exact absurd rfl Herr4.1
      | ok e =>
        (try wp_auto)
        wp_apply Hcancel
        (try wp_auto)
        iapply HΦ
        iframe Hlt
        simp only [Bool.false_eq_true, ↓reduceIte]
        itrivial
    subst Herr4
    icases Hq4 with ⟨%um4, %hum4, Hq4⟩
    imod (setupD_reply eps Γ γR γz 4 _ ⟨um4, rfl, hum4.2.2, hum4.1, hum4.2.1⟩ ⊤ (fun _ _ => CoPset.mem_full)
      (fun _ _ => CoPset.mem_full) _ hP) $$ Hc Hn Hq4 with #F4
    (try wp_auto)
    -- UserGrantRole(u, r)
    wp_apply (wp_UserGrantRole cl ap eps V Γ cfg γR cctx cd none go!"u" go!"r"
        (fun _ => effLb Γ.kv 5) hauth hlog hom) $$ [$Hlt] as %resp5 %err5 ⟨Hlt, Hout5⟩
    · iframe #
      isplitr
      · ipureintro; decide
      iapply (setupD_histAu γR Γ.kv γz 5 _ (setupReqAtD_of 5 _ rfl) (by decide) _ hP) $$ Hc Hn
    icases Hout5 with (⟨%Herr5, Hq5⟩ | %Herr5)
    rotate_left
    · cases err5 with
      | nil => exact absurd rfl Herr5.1
      | ok e =>
        (try wp_auto)
        wp_apply Hcancel
        (try wp_auto)
        iapply HΦ
        iframe Hlt
        simp only [Bool.false_eq_true, ↓reduceIte]
        itrivial
    subst Herr5
    imod (setupD_reply eps Γ γR γz 5 _ rfl ⊤ (fun _ _ => CoPset.mem_full)
      (fun _ _ => CoPset.mem_full) _ hP) $$ Hc Hn Hq5 with #F5
    (try wp_auto)
    -- UserAdd(v)
    wp_apply (wp_UserAdd cl ap eps V Γ cfg γR cctx cd none go!"v" go!"v-pw"
        (fun _ => effLb Γ.kv 6) hauth hlog hom) $$ [$Hlt] as %resp6 %err6 ⟨Hlt, Hout6⟩
    · iframe #
      isplitr
      · ipureintro; decide
      iintro !> %um %hum
      iapply (setupD_histAu γR Γ.kv γz 6 _
        (setupReqAtD_userAdd 6 go!"v" um (fun um h1 h3 h2 => ⟨um, rfl, h2, h1, h3⟩) hum.1 hum.2) (by decide)
        _ hP) $$ Hc Hn
    icases Hout6 with (⟨%Herr6, Hq6⟩ | %Herr6)
    rotate_left
    · cases err6 with
      | nil => exact absurd rfl Herr6.1
      | ok e =>
        (try wp_auto)
        wp_apply Hcancel
        (try wp_auto)
        iapply HΦ
        iframe Hlt
        simp only [Bool.false_eq_true, ↓reduceIte]
        itrivial
    subst Herr6
    icases Hq6 with ⟨%um6, %hum6, Hq6⟩
    imod (setupD_reply eps Γ γR γz 6 _ ⟨um6, rfl, hum6.2.2, hum6.1, hum6.2.1⟩ ⊤ (fun _ _ => CoPset.mem_full)
      (fun _ _ => CoPset.mem_full) _ hP) $$ Hc Hn Hq6 with #F6
    (try wp_auto)
    ihave #Hall : (□ ∀ i, ⌜i < 7⌝ -∗ effLb Γ.kv i : IProp GF) $$ []
    · imodintro
      iintro %i %hi
      have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
      rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · iexact F0
      · iexact F1
      · iexact F2
      · iexact F3
      · iexact F4
      · iexact F5
      · iexact F6
    -- AuthEnable()
    wp_apply (wp_AuthEnable cl ap eps V Γ cfg γR cctx cd none (setupDone γR Γ.kv γz) hauth hlog hom)
      $$ [$Hlt] as %resp7 %err7 ⟨Hlt, Hout7⟩
    · iframe #
      iapply (setupD_histAu_enable γR Γ.kv γz _ hP) $$ Hc Hn Hall
    icases Hout7 with (⟨%Herr7, Hq7⟩ | %Herr7)
    rotate_left
    · cases err7 with
      | nil => exact absurd rfl Herr7.1
      | ok e =>
        (try wp_auto)
        wp_apply Hcancel
        (try wp_auto)
        iapply HΦ
        iframe Hlt
        simp only [Bool.false_eq_true, ↓reduceIte]
        itrivial
    subst Herr7
    imod (setupD_reply_enable eps Γ γR γz ⊤ (fun _ _ => CoPset.mem_full)
      (fun _ _ => CoPset.mem_full) _ hP) $$ Hc Hn Hq7 with ⟨%hs, %Lset, %r, #Hf, #HLs, %Hd⟩
    (try wp_auto)
    wp_apply Hcancel
    (try wp_auto)
    iapply HΦ
    iframe Hlt
    simp only [↓reduceIte]
    iexists γz, hs, Lset, r
    iframe Hf HLs
    ipureintro; exact Hd

end proof

end etcd_auth
end EtcdGrove
end Perennial

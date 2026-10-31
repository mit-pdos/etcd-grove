/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/authkv/SetUp.lean` (the auth plan's
E2h). Lean-first (no Rocq counterpart).

The puts: two nested loops over `Principals()` and `{"a", "c"}`, each put in a timeout context
(`client.wp_WithTimeout_bg`), through `New`'s client with the caller's persistent update
(`client_Put_on`, S5: at the member's `Put` with auth on), the context cancelled after the call; the admin calls: one timeout
context with no outgoing metadata (`client.wp_WithTimeout_bgMd`), cancelled by the `defer` at every
return, each call through the client's `Auth` field (`clientTokAt`'s `authObjAtC`, over the
connection whose attempts carry no credential), with the update and the reply of `SetupInv.lean`
(the client's view of the auth history turned into `SetUp`'s cell at the start, `setup_alloc`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.authkv.SetUp
public import Spec.github_com.mit_pdos.etcd_grove.examples.authkv.Principals
public import Spec.github_com.mit_pdos.etcd_grove.examples.authkv.keyOf
public import Spec.go_etcd_io.etcd.client.v3.authClient__UserAdd
public import Spec.go_etcd_io.etcd.client.v3.authClient__UserGrantRole
public import Spec.go_etcd_io.etcd.client.v3.authClient__RoleAdd
public import Spec.go_etcd_io.etcd.client.v3.authClient__RoleGrantPermission
public import Spec.go_etcd_io.etcd.client.v3.authClient__AuthEnable
public import Proof.go_etcd_io.etcd.client.v3.ClientPutGet
public import Proof.github_com.mit_pdos.etcd_grove.examples.authkv.ClientOn
public import Perennial.Proof.context.Link
public import Proof.github_com.mit_pdos.etcd_grove.examples.authkv.SetupInv

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authkv

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.authkv.Assumptions]

theorem SetUp.wp_proof
    (hWT : context.WithTimeoutBackgroundMd.spec (GF := GF) (hG := hG))
    (wp_ErrAny : context.ErrAny.spec (GF := GF) (hG := hG))
    (wp_Principals : Principals.spec (GF := GF) (hG := hG))
    (wp_keyOf : keyOf.spec (GF := GF) (hG := hG))
    (wp_UserAdd : authClient.UserAdd.spec (GF := GF) (hG := hG))
    (wp_UserGrantRole : authClient.UserGrantRole.spec (GF := GF) (hG := hG))
    (wp_RoleAdd : authClient.RoleAdd.spec (GF := GF) (hG := hG))
    (wp_RoleGrantPermission : authClient.RoleGrantPermission.spec (GF := GF) (hG := hG))
    (wp_AuthEnable : authClient.AuthEnable.spec (GF := GF) (hG := hG)) :
    SetUp.spec (GF := GF) (hG := hG) := by
  intro CS EA FA RA CRE CEC cl ep V s E ρ cid mid γa hmode hc0 hAs
  wp_start as ⟨#Hnc, #Htok, #Hput, #Hkv, #Hauth, #Htls, Hview⟩
  iunfold clientTokAt at Htok
  icases Htok with ⟨%api, %conn, #Hkvf, #Hobj, #Hctok, ⟨%ap, #Hauf, #Hap⟩, -⟩
  imod (setup_alloc ρ.kv ⊤) $$ Hview with ⟨%γz, #Hc, #Hn⟩
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
  imod mvcc.idxCert_nil (GF := GF) E.γ.idx with #HF0
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
      "i" ∷ i_ptr ↦ j ∗ "who" ∷ who_ptr ↦ w0 ∗ "Hpsl" ∷ psl ↦* principals ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z psl.len⌝ : IProp GF) $$ [i who Hpsl]
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
        "i" ∷ i_ptr ↦ n ∗ "x" ∷ x_ptr ↦ x0 ∗ "Hxsl" ∷ _ ↦* keyParts ∗
        "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ 2⌝ : IProp GF) $$ [i x Hxsl]
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
        as %cctx %cd %cancel ⟨#Hcancel, #Hctx, #Hce, -, -⟩
      (try wp_auto)
      wp_apply wp_keyOf x w go!"d"
      (try wp_auto)
      have hk : keyOfK x w go!"d" ∈ setupKeys := by
        unfold setupKeys; exact List.mem_flatMap.2 ⟨w, hwm, List.mem_map.2 ⟨x, hxm, rfl⟩⟩
      wp_apply (client_Put_on cl api conn ep s E ρ cid mid cctx cd (keyOfK x w go!"d")
          go!"setup" slice.nil (fun _ => iprop(True)) []
          (opSizeOk_opPutModel (K := 2 ^ 28) (E := 0) (V := 2 ^ 28) (optsKeep_nil _ _ _)
            ((show ∀ k ∈ setupKeys, k.length ≤ 2 ^ 28 by decide) _ hk) (by decide) (by decide)))
        $$ [] as %resp %err Hout
      · iframe #
        iintro !>
        iapply Hkv
        ipureintro; exact hk
      (try wp_auto)
      wp_apply Hcancel
      icases Hout with (⟨%Herr, -⟩ | ⟨%Herr, -⟩)
      · subst Herr
        (try wp_auto)
        wp_for_post
        iframe
        iexists n + W64 1, x
        iframe
        ipureintro; constructor <;> word
      · cases err with
        | nil => exact absurd rfl Herr
        | ok e =>
          (try wp_auto)
          wp_for_post
          wp_for_post
          (try wp_auto)
          iapply HΦ
          simp only [Bool.false_eq_true, ↓reduceIte]
          itrivial
    · (try wp_auto)
      wp_for_post
      iframe
      iexists j + W64 1, w
      iframe
      ipureintro; constructor <;> word
  · (try wp_auto)
    iunfold setupAuthServed at Hauth
    icases Hauth with ⟨#Hu, #Hg, #Hr, #Hp, #He⟩
    wp_apply context.wp_Background
    (try wp_auto)
    wp_apply (client.wp_WithTimeout_bgMd hWT wp_ErrAny hAs _) $$ []
      as %cctx %cd %cancel ⟨#Hcancel, #Hctx, #Hce, -, %Hout⟩
    ihave #Hx : setupCtx s conn (GoInterface.ok cctx) $$ []
    · iunfold setupCtx; iframe Hctok Htls; ipureintro; exact Hout
    (try wp_auto)
    wp_apply (wp_UserAdd ap conn [ep] cctx cd go!"root" go!"root-pw" (v3rpc.etcdUserAddSpec s E ρ)
        (setupReplied s E ρ conn (GoInterface.ok cctx) (fun tok => v3rpc.userAddReplied s E ρ tok go!"root" (fun _ => effLb ρ.kv 0)))) $$ [] as %resp0 %err0 Hout0
    · iframe #
      isplitl
      rotate_left
      · ipureintro; decide
      iintro !>
      inext
      iapply (setup_pre_userAdd s E ρ conn _ γz 0 go!"root" go!"root-pw" (fun um h1 h2 => ⟨um, rfl, h2, h1⟩) (by decide) (by decide)) $$ Hc Hn Hx
    iunfold authCallOut at Hout0
    icases Hout0 with (⟨%Herr0, Hq0⟩ | ⟨%Herr0, -⟩)
    rotate_left
    · cases err0 with
      | nil => exact absurd rfl Herr0.1
      | ok e =>
        (try wp_auto)
        wp_apply Hcancel
        (try wp_auto)
        iapply HΦ
        simp only [Bool.false_eq_true, ↓reduceIte]
        itrivial
    subst Herr0
    imod (setup_post_userAdd s E ρ conn _ γz 0 go!"root" (fun um h1 h2 => ⟨um, rfl, h2, h1⟩) ⊤ (fun _ _ => CoPset.mem_full) (fun _ _ => CoPset.mem_full)) $$ Hc Hn Hx Hq0 with #F0
    (try wp_auto)
    wp_apply (wp_UserGrantRole ap conn [ep] cctx cd go!"root" go!"root" (v3rpc.etcdUserGrantRoleSpec s E ρ)
        (setupReplied s E ρ conn (GoInterface.ok cctx) (fun tok => v3rpc.adminReplied s E ρ tok (irrUserGrantRole go!"root" go!"root") (fun _ => effLb ρ.kv 1)))) $$ [] as %resp1 %err1 Hout1
    · iframe #
      isplitl
      rotate_left
      · ipureintro; decide
      iintro !>
      inext
      iapply (setup_pre_userGrantRole s E ρ conn _ γz 1 go!"root" go!"root" rfl (by decide) (by decide)) $$ Hc Hn Hx
    iunfold authCallOut at Hout1
    icases Hout1 with (⟨%Herr1, Hq1⟩ | ⟨%Herr1, -⟩)
    rotate_left
    · cases err1 with
      | nil => exact absurd rfl Herr1.1
      | ok e =>
        (try wp_auto)
        wp_apply Hcancel
        (try wp_auto)
        iapply HΦ
        simp only [Bool.false_eq_true, ↓reduceIte]
        itrivial
    subst Herr1
    imod (setup_post s E ρ conn _ γz 1 _ rfl ⊤ (fun _ _ => CoPset.mem_full) (fun _ _ => CoPset.mem_full)) $$ Hc Hn Hx Hq1 with #F1
    (try wp_auto)
    wp_apply (wp_RoleAdd ap conn [ep] cctx cd go!"r" (v3rpc.etcdRoleAddSpec s E ρ)
        (setupReplied s E ρ conn (GoInterface.ok cctx) (fun tok => v3rpc.adminReplied s E ρ tok (irrRoleAdd go!"r") (fun _ => effLb ρ.kv 2)))) $$ [] as %resp2 %err2 Hout2
    · iframe #
      isplitl
      rotate_left
      · ipureintro; decide
      iintro !>
      inext
      iapply (setup_pre_roleAdd s E ρ conn _ γz 2 go!"r" rfl (by decide) (by decide)) $$ Hc Hn Hx
    iunfold authCallOut at Hout2
    icases Hout2 with (⟨%Herr2, Hq2⟩ | ⟨%Herr2, -⟩)
    rotate_left
    · cases err2 with
      | nil => exact absurd rfl Herr2.1
      | ok e =>
        (try wp_auto)
        wp_apply Hcancel
        (try wp_auto)
        iapply HΦ
        simp only [Bool.false_eq_true, ↓reduceIte]
        itrivial
    subst Herr2
    imod (setup_post s E ρ conn _ γz 2 _ rfl ⊤ (fun _ _ => CoPset.mem_full) (fun _ _ => CoPset.mem_full)) $$ Hc Hn Hx Hq2 with #F2
    (try wp_auto)
    wp_apply (wp_RoleGrantPermission ap conn [ep] cctx cd go!"r" go!"a" go!"b" (W32 2) (v3rpc.etcdRoleGrantPermissionSpec s E ρ)
        (setupReplied s E ρ conn (GoInterface.ok cctx) (fun tok => v3rpc.adminReplied s E ρ tok (irrRoleGrantPermission go!"r" (some (⟨W32 2, go!"a", go!"b"⟩ : auth.PermW))) (fun _ => effLb ρ.kv 3)))) $$ [] as %resp3 %err3 Hout3
    · iframe #
      isplitr
      · ipureintro; decide
      isplitl
      rotate_left
      · ipureintro; decide
      iintro !>
      inext
      iapply (setup_pre_roleGrantPermission s E ρ conn _ γz 3 go!"r" ⟨W32 2, go!"a", go!"b"⟩ rfl (by decide) (by decide)) $$ Hc Hn Hx
    iunfold authCallOut at Hout3
    icases Hout3 with (⟨%Herr3, Hq3⟩ | ⟨%Herr3, -⟩)
    rotate_left
    · cases err3 with
      | nil => exact absurd rfl Herr3.1
      | ok e =>
        (try wp_auto)
        wp_apply Hcancel
        (try wp_auto)
        iapply HΦ
        simp only [Bool.false_eq_true, ↓reduceIte]
        itrivial
    subst Herr3
    imod (setup_post s E ρ conn _ γz 3 (irrRoleGrantPermission go!"r" (some (⟨W32 2, go!"a", go!"b"⟩ : auth.PermW))) rfl ⊤ (fun _ _ => CoPset.mem_full) (fun _ _ => CoPset.mem_full)) $$ Hc Hn Hx Hq3 with #F3
    (try wp_auto)
    wp_apply (wp_UserAdd ap conn [ep] cctx cd go!"u" go!"u-pw" (v3rpc.etcdUserAddSpec s E ρ)
        (setupReplied s E ρ conn (GoInterface.ok cctx) (fun tok => v3rpc.userAddReplied s E ρ tok go!"u" (fun _ => effLb ρ.kv 4)))) $$ [] as %resp4 %err4 Hout4
    · iframe #
      isplitl
      rotate_left
      · ipureintro; decide
      iintro !>
      inext
      iapply (setup_pre_userAdd s E ρ conn _ γz 4 go!"u" go!"u-pw" (fun um h1 h2 => ⟨um, rfl, h2, h1⟩) (by decide) (by decide)) $$ Hc Hn Hx
    iunfold authCallOut at Hout4
    icases Hout4 with (⟨%Herr4, Hq4⟩ | ⟨%Herr4, -⟩)
    rotate_left
    · cases err4 with
      | nil => exact absurd rfl Herr4.1
      | ok e =>
        (try wp_auto)
        wp_apply Hcancel
        (try wp_auto)
        iapply HΦ
        simp only [Bool.false_eq_true, ↓reduceIte]
        itrivial
    subst Herr4
    imod (setup_post_userAdd s E ρ conn _ γz 4 go!"u" (fun um h1 h2 => ⟨um, rfl, h2, h1⟩) ⊤ (fun _ _ => CoPset.mem_full) (fun _ _ => CoPset.mem_full)) $$ Hc Hn Hx Hq4 with #F4
    (try wp_auto)
    wp_apply (wp_UserGrantRole ap conn [ep] cctx cd go!"u" go!"r" (v3rpc.etcdUserGrantRoleSpec s E ρ)
        (setupReplied s E ρ conn (GoInterface.ok cctx) (fun tok => v3rpc.adminReplied s E ρ tok (irrUserGrantRole go!"u" go!"r") (fun _ => effLb ρ.kv 5)))) $$ [] as %resp5 %err5 Hout5
    · iframe #
      isplitl
      rotate_left
      · ipureintro; decide
      iintro !>
      inext
      iapply (setup_pre_userGrantRole s E ρ conn _ γz 5 go!"u" go!"r" rfl (by decide) (by decide)) $$ Hc Hn Hx
    iunfold authCallOut at Hout5
    icases Hout5 with (⟨%Herr5, Hq5⟩ | ⟨%Herr5, -⟩)
    rotate_left
    · cases err5 with
      | nil => exact absurd rfl Herr5.1
      | ok e =>
        (try wp_auto)
        wp_apply Hcancel
        (try wp_auto)
        iapply HΦ
        simp only [Bool.false_eq_true, ↓reduceIte]
        itrivial
    subst Herr5
    imod (setup_post s E ρ conn _ γz 5 _ rfl ⊤ (fun _ _ => CoPset.mem_full) (fun _ _ => CoPset.mem_full)) $$ Hc Hn Hx Hq5 with #F5
    (try wp_auto)
    wp_apply (wp_UserAdd ap conn [ep] cctx cd go!"v" go!"v-pw" (v3rpc.etcdUserAddSpec s E ρ)
        (setupReplied s E ρ conn (GoInterface.ok cctx) (fun tok => v3rpc.userAddReplied s E ρ tok go!"v" (fun _ => effLb ρ.kv 6)))) $$ [] as %resp6 %err6 Hout6
    · iframe #
      isplitl
      rotate_left
      · ipureintro; decide
      iintro !>
      inext
      iapply (setup_pre_userAdd s E ρ conn _ γz 6 go!"v" go!"v-pw" (fun um h1 h2 => ⟨um, rfl, h2, h1⟩) (by decide) (by decide)) $$ Hc Hn Hx
    iunfold authCallOut at Hout6
    icases Hout6 with (⟨%Herr6, Hq6⟩ | ⟨%Herr6, -⟩)
    rotate_left
    · cases err6 with
      | nil => exact absurd rfl Herr6.1
      | ok e =>
        (try wp_auto)
        wp_apply Hcancel
        (try wp_auto)
        iapply HΦ
        simp only [Bool.false_eq_true, ↓reduceIte]
        itrivial
    subst Herr6
    imod (setup_post_userAdd s E ρ conn _ γz 6 go!"v" (fun um h1 h2 => ⟨um, rfl, h2, h1⟩) ⊤ (fun _ _ => CoPset.mem_full) (fun _ _ => CoPset.mem_full)) $$ Hc Hn Hx Hq6 with #F6
    (try wp_auto)
    ihave #Hall : (□ ∀ i, ⌜i < 7⌝ -∗ effLb ρ.kv i : IProp GF) $$ []
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
    wp_apply (wp_AuthEnable ap conn [ep] cctx cd (v3rpc.etcdAuthEnableSpec s E ρ)
        (setupReplied s E ρ conn (GoInterface.ok cctx) (fun tok => v3rpc.adminReplied s E ρ tok irrAuthEnable (setupDone ρ.raft ρ.kv γz)))) $$ [] as %resp7 %err7 Hout7
    · iframe #
      iintro !>
      inext
      iapply (setup_pre_authEnable s E ρ conn _ γz) $$ Hc Hn Hx Hall
    iunfold authCallOut at Hout7
    icases Hout7 with (⟨%Herr7, Hq7⟩ | ⟨%Herr7, -⟩)
    rotate_left
    · cases err7 with
      | nil => exact absurd rfl Herr7.1
      | ok e =>
        (try wp_auto)
        wp_apply Hcancel
        (try wp_auto)
        iapply HΦ
        simp only [Bool.false_eq_true, ↓reduceIte]
        itrivial
    subst Herr7
    imod (setup_post_enable s E ρ conn _ γz γa hmode hc0 ⊤ (fun _ _ => CoPset.mem_full)
      (fun _ _ => CoPset.mem_full)) $$ Hc Hn Hx Hq7 with ⟨%hs, %Lset, %k, %r, #Hf, #HLs, %Hd, #Hk, #Hst⟩
    (try wp_auto)
    wp_apply Hcancel
    (try wp_auto)
    iapply HΦ
    simp only [↓reduceIte]
    iexists γz, hs, Lset, k, r
    iframe Hf HLs Hk Hst
    ipureintro; exact Hd

end proof

end authkv
end EtcdGrove
end Perennial

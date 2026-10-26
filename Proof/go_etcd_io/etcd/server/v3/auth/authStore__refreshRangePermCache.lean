/-
`(*authStore).refreshRangePermCache`'s proof (the auth plan's S2, 2026-10-23); see `InvAuth.lean`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__refreshRangePermCache
public import Spec.go_etcd_io.etcd.server.v3.auth.getMergedPerms
public import Spec.go_uber_org.zap.Logger__Debug
public import Spec.go_uber_org.zap.String
public import Spec.go_uber_org.zap.Logger__Error
public import Proof.go_etcd_io.etcd.server.v3.auth.PermTreeLemmas
public import Proof.go_etcd_io.etcd.server.v3.auth.CacheLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.auth auth

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

theorem auth.authStore.refreshRangePermCache.wp_proof
    (h_Debug : zap.Logger.Debug.spec (GF := GF) (hG := hG))
    (h_String : zap.String.spec (GF := GF) (hG := hG))
    (h_Error : zap.Logger.Error.spec (GF := GF) (hG := hG))
    (h_getMergedPerms : auth.getMergedPerms.spec (GF := GF) (hG := hG)) :
    auth.authStore.refreshRangePermCache.spec (GF := GF) (hG := hG) := by
  intro st R M ti Hs sta
  wp_start as ⟨#Hinv, Hca, #Hrd, Htok, #Hsnap, %Hfit⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  iunfold authInv at Hinv
  icases Hinv with ⟨%Hst, -, ⟨%lg, #Hlg, %Hlgnn⟩, -, -, -, #Hguard⟩
  ihave #Hrd2 : authReaderOk (GF := GF) ti Hs $$ []
  · iexact Hrd
  iunfold authReaderOk at Hrd2
  icases Hrd2 with ⟨-, -, -, -, #HAll⟩
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply sync.RWMutex.wp_Lock_guard $$ [$Hguard] as ⟨Hlk, HP⟩
  iunfold cacheP at HP
  icases HP with ⟨%mp, %Mp, Hmp, -, -⟩
  -- the admin side's half of the field joins the guard's
  iunfold cacheHalf at Hca
  icases Hca with ⟨%sta0, Hca, -⟩
  iunfold cacheAt at Hca
  icases Hca with ⟨%mp0, %Mp0, Hmp0, -, -⟩
  icombine Hmp Hmp0 gives %Heq0
  subst Heq0
  ihave Hmp := (typedPointsto_half_split _ _ (1 : Qp)).2 $$ [Hmp Hmp0]
  · iframe
  (try wp_auto)
  wp_apply h_Debug
  · ipureintro; exact Hlgnn
  (try wp_auto)
  wp_apply (wp_map_make1 (K := GoString) (V := Loc) go.string
    (go.GoType.PointerType unifiedRangePermissions.ty)) as %mp' HM'
  (try wp_auto)
  wp_bind (App (Val #(methods ti.ty go!"UnsafeGetAllUsers" ti.v)) (Val #()))
  iapply HAll $$ Htok
  inext
  iintro %usl %us %names ⟨Htok, Hus, %Hnames, Husers⟩
  obtain ⟨Hlens, Hnodup, Hmem⟩ := Hnames
  (try wp_auto)
  -- the users loop: the map holds the users seen so far
  ihave IH : iprop(∃ (k : w64) (ux : Loc) (Mp' : GMap GoString Loc),
      "i" ∷ i_ptr ↦ k ∗
      "user" ∷ user_ptr ↦ ux ∗
      "HM'" ∷ mp' ↦$ Mp' ∗
      "Hus" ∷ usl ↦* us ∗
      "Husers" ∷ ([∗list] x ∈ (us.zip names).drop (sint.nat k), userOut x.1 sta x.2) ∗
      "Hok" ∷ ([∗map] u ↦ p ∈ Mp', ∃ Lr Lw, permsAt p Lr Lw ∗ ⌜cacheEntryIs sta u Lr Lw⌝) ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.nat k ≤ us.length ∧
        ∀ u, (Mp' !! u).isSome ↔ u ∈ names.take (sint.nat k)⌝)
    $$ [i user HM' Hus Husers]
  · iexists W64 0, _, ∅
    rw [show sint.nat (W64 0) = 0 from rfl, List.drop_zero]
    iframe
    isplitl []
    · iapply BigSepM.bigSepM_empty.2; itrivial
    ipureintro
    refine ⟨by word, by word, ?_⟩
    intro u; simp
  -- the Go variable `as` (a Lean keyword) renamed for the loop's bookkeeping
  irename : (as_ptr ↦ st : IProp GF) => Has
  wp_for IH
  wp_if_destruct
  · -- a user
    have hlt : sint.Z k < sint.Z usl.len := by
      first | exact Hif | exact of_decide_eq_true (go.intoVal_inj Hif)
    ihave %Hul := ownSlice_len _ _ _ $$ Hus
    have hk : sint.nat k < us.length := by rw [Hul.1]; word
    obtain ⟨ux', hux⟩ : ∃ x, us[sint.nat k]? = some x := ⟨_, List.getElem?_eq_getElem hk⟩
    obtain ⟨nm, hnm⟩ : ∃ x, names[sint.nat k]? = some x :=
      ⟨_, List.getElem?_eq_getElem (by rw [← Hlens]; exact hk)⟩
    have hzip : (us.zip names)[sint.nat k]? = some (ux', nm) := by
      rw [List.getElem?_zip_eq_some]; exact ⟨hux, hnm⟩
    obtain ⟨hzk, hzeq⟩ := List.getElem?_eq_some_iff.1 hzip
    have hdrop : (us.zip names).drop (sint.nat k) =
        (ux', nm) :: (us.zip names).drop (sint.nat k + 1) := by
      rw [List.drop_eq_getElem_cons hzk, hzeq]
    rw [hdrop]
    icases BigSepL.bigSepL_cons.1 $$ Husers with ⟨Huser, Husers⟩
    have hnmem : nm ∈ names := List.mem_of_getElem? hnm
    -- the user exists in the state
    iunfold userOut at Huser
    cases hnm' : sta.users.lookup nm with
    | none =>
      exfalso
      have := (Hmem nm).1 hnmem
      rw [hnm'] at this; cases this
    | some roles =>
      dsimp only
      icases Huser with ⟨%ur, %Hur, Huser⟩
      iunfold ownUser at Huser
      icases Huser with ⟨%ms, %nmsl, %pw, %rs, %o, %uf, %sc, Hu, #Hnm, -, -, -⟩
      obtain ⟨Hurn, -, -⟩ := Hur
      have Hbnd : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z usl.len := ⟨Hk.1, hlt⟩
      (try wp_auto)
      simp only [Hbnd, _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index usl (sint.Z k) us (DFrac.own 1) ux' Hk.1 $$ [Hus] as Hus
      · iframe; ipureintro; exact hux
      (try wp_auto)
      wp_apply (wp_bytes_to_string nmsl ur.name DFrac.discard) $$ [$Hnm] as -
      (try wp_auto)
      wp_apply (h_getMergedPerms ti Hs sta ur.name) $$ [$Hrd $Htok] as %p ⟨Htok, Hp⟩
      · ipureintro; exact Hfit
      icases Hp with (⟨%Hpn, %Hnone⟩ | ⟨%Lr, %Lw, #Hperms, %Hent⟩)
      · exfalso; rw [Hurn, hnm'] at Hnone; cases Hnone
      (try wp_auto)
      wp_if_destruct
      · -- `getMergedPerms` returned nil: it does not (the user exists)
        iunfold permsAt at Hperms
        icases Hperms with ⟨%Hnn, -⟩
        exact absurd rfl Hnn
      · (try wp_auto)
        wp_apply wp_mapInsert go.string mp' Mp' ur.name p $$ [$HM'] as HM'
        have hfresh : Mp' !! ur.name = none := by rw [Hurn]; exact insert_fresh Hnodup hnm Hk.2.2
        have hsucc : sint.nat (k + W64 1) = sint.nat k + 1 := by
          have := Hul.1; have := Hul.2; word
        wp_for_post
        iframe Has tx Hlk defer Hmp Htok HΦ
        iexists k + W64 1, ux', <[ur.name := p]> Mp'
        rw [hsucc]
        iframe
        isplitl [Hok]
        · iapply (BigSepM.bigSepM_insert hfresh).2
          isplitr [Hok]
          · iexists Lr, Lw
            isplitl []
            · iexact Hperms
            ipureintro; exact Hent
          iexact Hok
        ipureintro
        refine ⟨by word, by omega, ?_⟩
        rw [Hurn]
        exact insert_keys_take hnm Hk.2.2 p
  · -- every user is in the map
    have hge : ¬ sint.Z k < sint.Z usl.len := by
      first | exact Hif | exact fun h => Hif (by rw [decide_eq_true h])
    ihave %Hul := ownSlice_len _ _ _ $$ Hus
    have hlen : sint.nat k = us.length := by
      have := Hk.2.1; rw [Hul.1] at this ⊢; have := Hul.2; word
    have hdom : ∀ u, (Mp' !! u).isSome ↔ (sta.users !! u).isSome := by
      intro u
      rw [Hk.2.2 u, hlen, Hlens, List.take_length]
      exact Hmem u
    (try wp_auto)
    ihave ⟨Hmp, Hmp2⟩ := (typedPointsto_half_split _ _ (1 : Qp)).1 $$ Hmp
    imod ownMap_persist mp' _ Mp' $$ HM' with #HM'
    ihave #Hof : (cacheOf (GF := GF) sta Mp') $$ [Hok]
    · iunfold cacheOf; iframe Hok; ipureintro; exact hdom
    ihave #Hok : (cacheOk (GF := GF) M Mp') $$ []
    · iunfold cacheOf at Hof
      icases Hof with ⟨-, #Hall⟩
      iapply cacheOk_intro M Mp' sta
      iframe Hall
      isplitl []
      · iexact Hsnap
      ipureintro; exact hdom
    wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hlk Hmp]
    · inext
      iunfold cacheP
      iexists mp', Mp'
      iframe Hmp HM' Hok
    (try wp_auto)
    iapply HΦ
    iframe Htok
    iunfold cacheAt
    iexists mp', Mp'
    iframe Hmp2 HM' Hof

end proof

end EtcdGrove
end Perennial

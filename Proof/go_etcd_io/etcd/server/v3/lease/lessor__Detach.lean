/-
Proof of `Spec/go_etcd_io/etcd/server/v3/lease/lessor__Detach.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__Detach
public import Proof.go_etcd_io.etcd.server.v3.lease.LessorLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.lease lease

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

theorem lease.lessor.Detach.wp_proof : lease.lessor.Detach.spec (GF := GF) (hG := hG) := by
  intro lp γl id items xs dq L0 I0
  wp_start as ⟨#Hinv, Hown, %Hne0, %Hxs0, Hxs⟩
  iunfold lessorInv at Hinv
  icases Hinv with ⟨%Hlp, #Hpin, #Hmu, #Hrdi⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_with_defer as %defer defer
  wp_apply sync.RWMutex.wp_Lock_guard $$ [$Hmu] as ⟨Hlk, HR⟩
  iunfold lessorMu at HR
  icases HR with ⟨%lm, %im, %M, %I, %rd0, %L, Hlm, HM, Him, HI, Hrdf, Ha, Hg, %HL, #Hsz, #Hls, Hx,
    %γrl, %hsl, #Hprl, Hhl, %Hlastl⟩
  wp_auto
  -- the owner's: the live set, the item map's half, the lease's element and item set's half
  iunfold leaseOwn at Hown
  icases Hown with ⟨Hown, Hcls⟩
  ihave %Hag := leaseFrag_agree γl _ _ _ _ $$ [$Hown $Hg]
  subst Hag
  iunfold leaseClosers at Hcls
  icases Hcls with ⟨%lp', %γga, %γcl, %C, %im', #Hp, %HC, Him', HI', %HIL, %HIS, Hcs,
    %γr, %hs, %Sm, #Hpr, Ho, %Hlast, HSo⟩
  icases lessorAuth_pin γl 1 lp lp' L0 M γga γcl $$ [$Ha $Hp] with ⟨%Hlp', Hcl, Hback⟩
  subst Hlp'
  ihave ⟨%Him_eq, Him⟩ := ptsto_halves_combine (lF go!"itemMap" lp) im im' $$ [$Him $Him']
  subst Him_eq
  ihave ⟨%HIeq, HI⟩ := ownMap_halves_combine im I I0 $$ [$HI $HI']
  subst HIeq
  have HidL : id ∈ L0 := by
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil xs Hne0
    exact HIL x id (Hxs0 x hx)
  obtain ⟨l, hCl⟩ : ∃ l, C.lookup id = some l := Option.isSome_iff_exists.1 ((HC id).1 HidL)
  icases closers_items γl γcl C id l I hCl $$ Hcs with ⟨He, Hio, Hcs⟩
  ihave %HMl := ghost_map_lookup $$ Hcl He
  wp_apply (wp_map_lookup1 LeaseID.ty (go.GoType.PointerType Lease.ty) lm M id) $$ HM as HM
  rw [HMl]
  simp only [Option.getD_some]
  ihave #Hl := BigSepM.bigSepM_lookup HMl $$ Hls
  iunfold isLeaseObj at Hl
  icases Hl with ⟨%Hnn, #Hlmu, -, -⟩
  simp only [Hnn, decide_false]
  wp_auto
  wp_apply sync.RWMutex.wp_Lock_guard $$ [$Hlmu] as ⟨Hllk, HS⟩
  iunfold leaseItems at HS
  icases HS with ⟨%sm, %S, %γr3, #Hpr3, Hsm, HSm, Hel⟩
  iunfold leaseItemsOwn at Hio
  icases Hio with ⟨%sm', %S0, Hsm', HSm', %HSI⟩
  ihave ⟨%Hsm_eq, Hsm⟩ := ptsto_halves_combine (lsF go!"itemSet" l) sm sm' $$ [$Hsm $Hsm']
  subst Hsm_eq
  ihave ⟨%HSeq, HSm⟩ := ownMap_halves_combine sm S S0 $$ [$HSm $HSm']
  subst HSeq
  ihave %Hlen := ownSlice_len items dq xs $$ Hxs
  ihave IH : iprop(∃ (n : w64) (itv : LeaseItem) (ys : List LeaseItem),
      "Hi" ∷ i_ptr ↦ n ∗ "Hit" ∷ it_ptr ↦ itv ∗
      "HSm" ∷ sm ↦$ deleteAll S ys ∗ "HI" ∷ im ↦$ deleteAll I ys ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z items.len⌝ ∗
      "%Hys" ∷ ⌜ys = xs.take (sint.nat n)⌝) $$ [i it HSm HI]
  · iexists W64 0, _, []
    rw [show deleteAll S [] = S from rfl, show deleteAll I [] = I from rfl]
    iframe i it HSm HI
    ipureintro; constructor
    · constructor <;> word
    · simp
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < xs.length := by word
    obtain ⟨x, Hx⟩ : ∃ x, xs[sint.nat n]? = some x := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hbnd' : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z items.len := ⟨Hn.1, Hif⟩
    simp only [Hbnd', and_self]
    wp_apply wp_load_slice_index items (sint.Z n) xs dq x Hn.1 $$ [Hxs] as Hxs
    · iframe; ipureintro; exact Hx
    wp_apply (wp_mapDelete sm (deleteAll S ys) x LeaseItem.ty (go.StructType [])) $$ HSm as HSm
    wp_apply (wp_mapDelete im (deleteAll I ys) x LeaseItem.ty LeaseID.ty) $$ HI as HI
    wp_for_post
    iframe
    iexists n + W64 1, x, ys ++ [x]
    rw [deleteAll_snoc, deleteAll_snoc]
    iframe
    ipureintro
    constructor
    · constructor <;> word
    · have h1 : sint.nat (n + W64 1) = sint.nat n + 1 := by word
      rw [h1, List.take_add_one, Hx, Hys]; rfl
  · have hys : ys = xs := by
      rw [Hys]; apply List.take_of_length_le; word
    subst hys
    -- the history: the snapshot without the lease's detached items appended, its set without them
    ihave %Hr := lessorPinR_agree γl γr γrl $$ [$Hpr $Hprl]
    subst Hr
    ihave %Hr := lessorPinR_agree γl γr γr3 $$ [$Hpr $Hpr3]
    subst Hr
    ihave %Hh := monoListAuthOwn_agree γr.1 _ _ hs hsl $$ Ho Hhl
    obtain ⟨-, rfl⟩ := Hh
    have hCM : C = M := by
      rw [Hlast] at Hlastl; injection Hlastl with h; injection h
    iapply fupd_wp
    imod hist_append_set γl γr hs Sm (M, deleteAll I ys) l S (deleteAll S ys) ⊤
      (fun _ _ => CoPset.mem_full)
      (fun hok hh hS => setsOk_items Hlastl hok hh HMl hS (itemsFor_detach I id S ys)
        (fun id' hne it => detach_other I id id' ys Hxs0 hne it)
        (fun h => itemKeysShort_deleteAll I ys h))
      $$ [$Hrdi $Hpr $Ho $Hhl $HSo $Hel] with ⟨Ho, Hhl, HSo, Hel⟩
    imodintro
    have hlast' : (hs ++ [(M, deleteAll I ys)]).getLast? = some (M, deleteAll I ys) := by
      simp
    icases ownMap_halves_split sm (deleteAll S ys) $$ HSm with ⟨HSm, HSm'⟩
    icases ptsto_halves_split (lsF go!"itemSet" l) sm $$ Hsm with ⟨Hsm, Hsm'⟩
    wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hllk Hsm HSm Hel]
    · inext
      iunfold leaseItems
      iexists sm, deleteAll S ys, γr
      iframe; iframe #
    icases ownMap_halves_split im (deleteAll I ys) $$ HI with ⟨HI, HI'⟩
    icases ptsto_halves_split (lF go!"itemMap" lp) im $$ Him with ⟨Him, Him'⟩
    ihave Ha := Hback $$ %M Hcl
    wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hlk Hlm HM Him HI Hrdf Ha Hg Hx Hhl]
    · inext
      iunfold lessorMu
      iexists lm, im, M, deleteAll I ys, rd0, L0
      iframe
      iframe Hsz Hls
      isplitr
      · ipureintro; exact HL
      iframe Hpr; ipureintro; exact hlast'
    iapply HΦ
    iframe Hxs
    iunfold leaseOwn
    iframe Hown
    iunfold leaseClosers
    iexists lp, γga, γcl, C, im
    iframe Hp Him' HI'
    isplitr
    · ipureintro; exact HC
    isplitr
    · ipureintro
      intro it id' h
      rw [deleteAll_lookup] at h
      by_cases hi : it ∈ ys
      · simp only [hi, ↓reduceIte, reduceCtorEq] at h
      · simp only [hi, ↓reduceIte] at h; exact HIL it id' h
    isplitr
    · ipureintro; exact itemKeysShort_deleteAll I ys HIS
    isplitl [Hcs He Hsm' HSm']
    · iapply Hcs $$ %(deleteAll I ys) [] He
      · ipureintro
        intro id' hne it
        exact detach_other I id id' ys Hxs0 hne it
      iunfold leaseItemsOwn
      iexists sm, deleteAll S ys
      iframe Hsm' HSm'
      ipureintro
      exact itemsFor_detach I id S ys HSI
    iexists γr, hs ++ [(M, deleteAll I ys)], Sm.insert l (deleteAll S ys)
    iframe Hpr Ho HSo
    ipureintro; rw [hCM]; exact hlast'

end proof

end EtcdGrove
end Perennial

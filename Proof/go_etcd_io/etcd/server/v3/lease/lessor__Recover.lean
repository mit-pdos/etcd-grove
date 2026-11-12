/-
Proof of `Spec/go_etcd_io/etcd/server/v3/lease/lessor__Recover.lean`. Lean-first (no Rocq
counterpart); until the lease-expiry plan's S1 (2026-11-04) an axiom at the trust boundary.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__Recover
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__initAndRecover
public import Proof.go_etcd_io.etcd.server.v3.lease.LessorRecoverLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.lease lease

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

theorem lease.lessor.Recover.wp_proof
    (hIR : lease.lessor.initAndRecover.spec (GF := GF) (hG := hG)) :
    lease.lessor.Recover.spec (GF := GF) (hG := hG) := by
  intro lp γl oldbe d W Pk qo S r rd rd0 L I mono recs U reqOf Lr hS hLp hrecs hmono hU hrq hLr
  wp_start as ⟨#Hinv, #Hcfg, #Hmode, HUo, #Hrq, Hbo, Hown, Hrvk, Hro, #Hgr, #HB, Ho, Htoks, Hrb⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hinv' := Hinv
  iunfold lessorInv at Hinv'
  icases Hinv' with ⟨%Hlp, #Hpin, #Hmu, #Hrd⟩
  ihave #Hcfg' := Hcfg
  iunfold lessorCfg at Hcfg'
  icases Hcfg' with ⟨%mt, %cpp, %cl, %ci, %lg, %rr, #Hmt, -, -, -, -, -, -, -⟩
  (try wp_auto)
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply sync.RWMutex.wp_Lock_guard $$ [$Hmu] as ⟨Hlk, HR⟩
  iunfold lessorMu at HR
  icases HR with ⟨%lm, %im, %M, %I', %rd1, %L', Hlm, HM, Him, HI, Hrdf, Ha, Hg, %HL, #Hsz, #Hls,
    Hx, Hhist⟩
  iunfold leaseOwn at Hown
  icases Hown with ⟨Hown, Hcls⟩
  ihave %Hag := leaseFrag_agree γl _ _ _ _ $$ [$Hown $Hg]
  subst Hag
  iunfold lessorExtra at Hx
  icases Hx with ⟨%dc, %np, %h, %hx, %cp, %bl, Hdc, Hnp, Hnot, Hh, Hhq, Hcp, -, Hbl⟩
  iunfold leaseClosers at Hcls
  icases Hcls with ⟨%lp', %γga, %γcl, %C, %im0, #Hp, %HC, Him0, HI0, -, -, Hcs, Hch⟩
  -- `le.b`, `le.rd`, `le.itemMap`: the two halves made whole
  iunfold lessorBeOn at Hbo
  icases ptsto_halves_combine _ _ _ $$ [Hbo Hbl] with ⟨-, Hb⟩
  · iframe
  iunfold rdOwn at Hro
  icases Hro with ⟨%lp2, #Hpin2, Hro⟩
  ihave %Hlp2 := lessorPin_agree γl lp lp2 $$ [$Hpin $Hpin2]
  subst Hlp2
  icases ptsto_halves_combine _ _ _ $$ [Hro Hrdf] with ⟨-, Hrdw⟩
  · iframe
  ihave #Hpin3 : lessorPin γl lp' $$ []
  · iunfold lessorPin; iexists γga, γcl; iexact Hp
  ihave %Hlp3 := lessorPin_agree γl lp lp' $$ [$Hpin $Hpin3]
  subst Hlp3
  icases ptsto_halves_combine _ _ _ $$ [Him0 Him] with ⟨-, Himw⟩
  · iframe
  (try wp_auto)
  -- fresh `leaseMap` and `itemMap`
  wp_apply (wp_map_make1 (V := Loc) LeaseID.ty (go.GoType.PointerType Lease.ty)) as %lm' HM'
  (try wp_auto)
  wp_apply (wp_map_make1 (V := w64) LeaseItem.ty LeaseID.ty) as %im' HI'
  (try wp_auto)
  -- `le.initAndRecover()`
  have hS' : S mvcc.leaseName := hS
  have hrecs' : backend.bktEnts ((r.lookup mvcc.leaseName).getD ∅) = recs.map leaseRecEnc := hrecs
  wp_apply (hIR lp lm' np h hx mt d.γB d.P W Pk d.be qo S r recs hS' hLp hrecs')
    $$ [$Hpkg $Hb $Hlm $HM' $Hmt $Hnp $Hnot $Hh $Hhq $HB $Ho $Htoks $Hrb]
    as ⟨%ls, %h', %hx', %Hlen, Hb, Hlm, HM', Hrl, #Hr, Hnp, Hnot, Hh, Hhq, Ho, Hrb⟩
  (try wp_auto)
  -- the ghost step: the recovered leases in place of the old ones
  have hfst : (recs.zip ls).map Prod.fst = recs := List.map_fst_zip (by omega)
  have hids : (recs.zip ls).map (·.1.1) = recs.map (·.1) := by
    calc (recs.zip ls).map (·.1.1) = ((recs.zip ls).map Prod.fst).map (·.1) := by
          rw [List.map_map]; rfl
      _ = recs.map (·.1) := by rw [hfst]
  have hnd : ((recs.zip ls).map (·.1.1)).Nodup := by
    rw [hids]; exact leaseRecs_nodup _ recs hrecs
  have hmono' : mono = true → ∀ id ∈ L, id ∈ (recs.zip ls).map (·.1.1) := by
    rw [hids]; exact hmono
  ihave #Hgr' : iprop([∗list] id ∈ (recs.zip ls).map (·.1.1), leaseGranted (GF := GF) γl id) $$ []
  · rw [hids]; iexact Hgr
  icases ptsto_halves_split _ _ $$ Himw with ⟨Himw, Himw'⟩
  icases ownMap_halves_split im' (∅ : GMap LeaseItem w64) $$ HI' with ⟨HI', HI''⟩
  iapply fupd_wp
  ihave HUo : iprop(⌜recs.zip ls = []⌝ ∨ leaseEver (GF := GF) γl U) $$ [HUo]
  · by_cases hr : recs = []
    · ileft; ipureintro; rw [hr]; rfl
    · irevert HUo; rw [if_neg hr]; iintro HUo
      iright; iexact HUo
  ihave #Hrq' : iprop([∗list] id ∈ (recs.zip ls).map (·.1.1),
      ⌜id ∉ U⌝ ∨ leaseReqIs (GF := GF) γl id (reqOf id)) $$ []
  · rw [hids, BigSepL.bigSepL_map (fun x : w64 × w64 × w64 => x.1)
      (Φ := fun _ id => iprop(⌜id ∉ U⌝ ∨ leaseReqIs (GF := GF) γl id (reqOf id)))]
    iexact Hrq
  imod closers_recover γl lp lp L M C I I' mono mt (recs.zip ls) im' γga γcl ⊤
      (fun _ _ => CoPset.mem_full) HL hnd hmono' U (by rw [hids]; exact hU) reqOf
      (fun p hp => hrq p.1 (List.of_mem_zip hp).1)
    $$ [$Hrd $Hmode $HUo $Hrq' $Ha $Hg $Hown $Hp $Hcs $Hch $Hhist $Hrvk $Himw' $HI'' $Hgr' $Hrl]
    with ⟨Ha, Hg, Hown, Hrvk, Hhist, #Hlos, Hmetas, HUo, #HrqOut, %i, #Hat⟩
  -- (S2–S4, Q-S7) the live set in the caller's order
  have hLr' : Lr.Perm ((recs.zip ls).map (·.1.1)) := by rw [hids]; exact hLr
  imod lessor_live_perm γl lp _ Lr _ ∅ hLr' $$ [$Ha $Hg $Hown $Hrvk] with ⟨Ha, Hg, Hown, Hrvk⟩
  ihave HUo : iprop(if recs = [] then iprop(True)
      else leaseEver (GF := GF) γl (U ++ (recs.zip ls).map (·.1.1))) $$ [HUo]
  · by_cases hr : recs = []
    · rw [if_pos hr]; itrivial
    · rw [if_neg hr]
      icases HUo with (%Hx | HUo)
      · have := congrArg List.length Hx
        rw [List.length_zip, Hlen, Nat.min_self] at this
        exact absurd (List.length_eq_zero_iff.1 this) hr
      · iexact HUo
  imodintro
  ihave #Hsz' : ⧖ (GMap.size (recMap (recs.zip ls))) $$ []
  · iapply (preceipt_mono (GF := GF) (m := GMap.size (recMap (recs.zip ls)))
      (n := recs.length) ?_) $$ Hr
    have := recMap_size (recs.zip ls)
    rw [List.length_zip] at this
    omega
  icases ptsto_halves_split _ _ $$ Hb with ⟨Hb, Hbl⟩
  icases ptsto_halves_split _ _ $$ Hrdw with ⟨Hrdw, Hrdf⟩
  ihave Hx : lessorExtra lp (recMap (recs.zip ls)) 1 $$ [Hdc Hnp Hnot Hh Hhq Hcp Hmetas Hbl]
  · iunfold lessorExtra; iexists dc, np, h', hx', cp, _; iframe
  wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hlk Hlm HM' Himw HI' Hrdf Ha Hg Hx Hhist]
  · iframe #
    inext
    iunfold lessorMu
    iexists lm', im', recMap (recs.zip ls), ∅, rd, Lr
    iframe
    iframe Hsz' Hlos
    ipureintro; intro x; rw [hLr'.mem_iff]; exact (recMap_isSome _ x).symm
  (try wp_auto)
  ihave #HrqR : iprop([∗list] x ∈ recs, leaseReqIs (GF := GF) γl x.1 (reqOf x.1)) $$ []
  · rw [← BigSepL.bigSepL_map (fun x : w64 × w64 × w64 => x.1)
      (Φ := fun _ id => leaseReqIs (GF := GF) γl id (reqOf id)), ← hids]
    iexact HrqOut
  iapply HΦ
  rw [← hids]
  iframe Hown Hrvk Ho HUo HrqR
  isplitl [Hb]
  · iunfold lessorBeOn; iexact Hb
  isplitl [Hrdw]
  · iunfold rdOwn; iexists lp; iframe Hpin Hrdw
  isplitl [Hrb]
  · rw [show (go!"lease" : GoString) = mvcc.leaseName from rfl]; iexact Hrb
  iexists i, ls, mt
  iframe Hmt
  isplitr
  · ipureintro; exact Hlen
  have hσ : recSnap mt (recs.zip ls) = (recMap (recs.zip ls), ∅, recTTLs mt recs) := by
    unfold recSnap; rw [hfst]
  rw [← hσ]
  iexact Hat

end proof

end EtcdGrove
end Perennial

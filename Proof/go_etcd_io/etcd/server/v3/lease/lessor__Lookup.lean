/-
Proof of `Spec/go_etcd_io/etcd/server/v3/lease/lessor__Lookup.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__Lookup
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

theorem lease.lessor.Lookup.wp_proof : lease.lessor.Lookup.spec (GF := GF) (hG := hG) := by
  intro lp γl id m U
  wp_start as ⟨#Hinv, Hrd, #Hlb, HU⟩
  iunfold lessorInv at Hinv
  icases Hinv with ⟨%Hlp, #Hpin, #Hmu, #Hrdi⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold lessorRd at Hrd
  wp_auto
  wp_apply wp_with_defer as %defer defer
  wp_apply sync.RWMutex.wp_RLock $$ [$Hrd] as ⟨Hlk, HR⟩
  iunfold lessorMu at HR
  icases HR with ⟨%lm, %im, %M, %I', %rd0, %L', Hlm, HM, Him, HI, Hrdf, Ha, Hg, %HL, #Hsz, #Hls, Hx,
    %γr, %hs, #Hpr, Hhl, %Hlast⟩
  -- the reader's view: the history's last snapshot, at an index no earlier than `m`
  icases lockHist_at γl γr _ hs (M, I') m Hlast $$ [$Hlb $Hpr $Hhl] with ⟨Hhl, %Hm, #Hat⟩
  wp_auto
  wp_apply (wp_map_lookup1 LeaseID.ty (go.GoType.PointerType Lease.ty) lm M id) $$ HM as HM
  have hL := HL id
  cases hM : M.lookup id with
  | none =>
    -- the owner's view: its live set is the lock's
    ihave HU' : lookupViewAfter (GF := GF) γl id null U ∗ lessorAuth γl _ lp L' M ∗
        leaseFrag γl _ L' $$ [HU Ha Hg]
    · cases U with
      | none => rw [lookupViewAfter_none]; iframe
      | some LI =>
        obtain ⟨L, I⟩ := LI
        rw [lookupView_some, lookupViewAfter_some]
        iunfold leaseOwn at HU
        icases HU with ⟨Hfr, Hcls⟩
        ihave %Hag := leaseFrag_agree γl _ _ _ _ $$ [$Hfr $Hg]
        subst Hag
        iframe Ha Hg
        isplitr
        · ipureintro
          simp only [hM, Option.isSome_none, Bool.false_eq_true, iff_false] at hL
          exact ⟨fun _ => hL, fun _ => rfl⟩
        ileft
        isplitr
        · ipureintro; rfl
        iunfold leaseOwn; iframe Hfr Hcls
    icases HU' with ⟨HU, Ha, Hg⟩
    wp_apply sync.RWMutex.wp_RUnlock $$ [$Hlk Hlm HM Him HI Hrdf Ha Hg Hx Hhl] as Hrd
    · inext
      iunfold lessorMu
      iexists lm, im, M, I', rd0, L'
      iframe
      iframe Hsz Hls
      isplitr
      · ipureintro; exact HL
      iframe Hpr; ipureintro; exact Hlast
    iapply HΦ
    iunfold lessorRd
    simp only [Option.getD_none]
    iframe Hrd HU
    ileft
    isplitr
    · ipureintro; rfl
    iunfold leaseAbsentFrom
    iexists hs.length - 1, (M, I')
    iframe Hat
    ipureintro; exact ⟨Hm, hM⟩
  | some l =>
    ihave #Hlo := BigSepM.bigSepM_lookup hM $$ Hls
    ihave #Hlo' := Hlo
    iunfold isLeaseObj at Hlo'
    icases Hlo' with ⟨%Hnn, #Hlmu, -⟩
    ihave HU' : lookupViewAfter (GF := GF) γl id l U ∗ lessorAuth γl _ lp L' M ∗
        leaseFrag γl _ L' $$ [HU Ha Hg]
    · cases U with
      | none => rw [lookupViewAfter_none]; iframe
      | some LI =>
        obtain ⟨L, I⟩ := LI
        rw [lookupView_some, lookupViewAfter_some]
        iunfold leaseOwn at HU
        icases HU with ⟨Hfr, Hcls⟩
        ihave %Hag := leaseFrag_agree γl _ _ _ _ $$ [$Hfr $Hg]
        subst Hag
        have hidL : id ∈ L := hL.2 (by rw [hM]; rfl)
        -- the owner's closer of `id` is the map's lease (the closers' map's authority agrees)
        iunfold leaseClosers at Hcls
        icases Hcls with ⟨%lp', %γga, %γcl, %C, %im', #Hp, %HC, Him', HI', %HIL, %HIS, Hcm,
          %γr2, %hs2, %Sm2, #Hpr2, Ho2, %Hlast2, HSm2⟩
        icases lessorAuth_pin γl _ lp lp' L M γga γcl $$ [$Ha $Hp] with ⟨%Hlp', Hcl, Hback⟩
        subst Hlp'
        obtain ⟨l', hCl⟩ : ∃ l', C.lookup id = some l' :=
          Option.isSome_iff_exists.1 ((HC id).1 hidL)
        icases (BigSepM.bigSepM_lookup_acc (Φ := fun i x => closerAt (GF := GF) γl γcl I i x)
          hCl).1 $$ Hcm with ⟨Hcid, Hcw⟩
        iunfold closerAt at Hcid
        icases Hcid with ⟨He, Hio, Hslot⟩
        ihave %HMl := ghost_map_lookup $$ Hcl He
        rw [hM] at HMl
        injection HMl with HMl
        subst HMl
        ihave Ha := Hback $$ %M Hcl
        iframe Ha Hg
        isplitr
        · ipureintro
          exact ⟨fun h => absurd h Hnn, fun h => absurd hidL h⟩
        iright
        iunfold leaseOwnOpen
        iframe Hlo Hio Hslot
        isplitr
        · ipureintro; exact HIS
        iintro ⟨Hio, Hslot⟩
        iunfold leaseOwn; iframe Hfr
        iunfold leaseClosers
        iexists lp, γga, γcl, C, im'
        iframe Hp Him' HI'
        isplitr
        · ipureintro; exact HC
        isplitr
        · ipureintro; exact HIL
        isplitr
        · ipureintro; exact HIS
        isplitl [Hcw He Hio Hslot]
        · iapply Hcw
          iunfold closerAt; iframe He Hio Hslot
        iexists γr2, hs2, Sm2; iframe Hpr2 Ho2 HSm2; ipureintro; exact Hlast2
    icases HU' with ⟨HU, Ha, Hg⟩
    wp_apply sync.RWMutex.wp_RUnlock $$ [$Hlk Hlm HM Him HI Hrdf Ha Hg Hx Hhl] as Hrd
    · inext
      iunfold lessorMu
      iexists lm, im, M, I', rd0, L'
      iframe
      iframe Hsz Hls
      isplitr
      · ipureintro; exact HL
      iframe Hpr; ipureintro; exact Hlast
    iapply HΦ
    iunfold lessorRd
    simp only [Option.getD_some]
    iframe Hrd HU
    iright
    iframe Hlo
    iunfold leaseLiveFrom
    iexists hs.length - 1, (M, I')
    iframe Hat
    ipureintro; exact ⟨Hm, hM⟩

end proof

end EtcdGrove
end Perennial

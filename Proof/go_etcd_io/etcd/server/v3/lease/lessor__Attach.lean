/-
Proof of `Spec/go_etcd_io/etcd/server/v3/lease/lessor__Attach.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__Attach
public import Proof.go_etcd_io.etcd.server.v3.lease.LessorLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.lease lease

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

theorem lease.lessor.Attach.wp_proof : lease.lessor.Attach.spec (GF := GF) (hG := hG) := by
  intro lp γl id items xs dq q L0
  wp_start as ⟨#Hinv, Hown, Hxs⟩
  iunfold lessorInv at Hinv
  icases Hinv with ⟨%Hlp, #Hpin, #Hmu⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave Hli : (leaseInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hli with ⟨Hl0, -⟩
  iunfold leaseErrVar at Hl0
  icases Hl0 with ⟨%e, #He, -⟩
  wp_apply wp_with_defer as %defer defer
  wp_apply sync.RWMutex.wp_Lock_guard $$ [$Hmu] as ⟨Hlk, HR⟩
  iunfold lessorMu at HR
  icases HR with ⟨%lm, %im, %M, %I, %rd0, %L, Hlm, HM, Him, HI, Hrdf, Ha, Hg, %HL, #Hls, Hx⟩
  wp_auto
  ihave %Hag := leaseFrag_agree γl _ _ _ _ $$ [$Hown $Hg]
  subst Hag
  wp_apply (wp_map_lookup1 LeaseID.ty (go.GoType.PointerType Lease.ty) lm M id) $$ HM as HM
  cases hM : M.lookup id with
  | none =>
    simp only [Option.getD_none]
    wp_auto
    wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hlk Hlm HM Him HI Hrdf Ha Hg Hx]
    · inext
      iunfold lessorMu
      iexists lm, im, M, I, rd0, L0
      iframe
      iframe Hls
      ipureintro; exact HL
    iapply HΦ
    iframe Hxs Hown
    ipureintro
    intro hin
    have := (HL id).1 hin
    rw [hM] at this
    cases this
  | some l =>
    simp only [Option.getD_some]
    ihave #Hl := BigSepM.bigSepM_lookup hM $$ Hls
    iunfold isLeaseObj at Hl
    icases Hl with ⟨%Hnn, #Hlmu⟩
    simp only [Hnn, decide_false]
    wp_auto
    wp_apply sync.RWMutex.wp_Lock_guard $$ [$Hlmu] as ⟨Hllk, HS⟩
    iunfold leaseItems at HS
    icases HS with ⟨%sm, %S, Hsm, HSm⟩
    ihave %Hlen := ownSlice_len items dq xs $$ Hxs
    ihave IH : iprop(∃ (n : w64) (itv : LeaseItem) (S' : GMap LeaseItem Unit)
        (I' : GMap LeaseItem w64),
        "Hi" ∷ i_ptr ↦ n ∗ "Hit" ∷ it_ptr ↦ itv ∗ "HSm" ∷ sm ↦$ S' ∗ "HI" ∷ im ↦$ I' ∗
        "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z items.len⌝) $$ [i it HSm HI]
    · iexists W64 0, _, S, I
      iframe i it HSm HI
      ipureintro; constructor <;> word
    wp_for IH
    wp_if_destruct
    · have Hlt : sint.nat n < xs.length := by word
      obtain ⟨x, Hx⟩ : ∃ x, xs[sint.nat n]? = some x := ⟨_, List.getElem?_eq_getElem Hlt⟩
      have Hbnd' : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z items.len := ⟨Hn.1, Hif⟩
      simp only [Hbnd', and_self]
      wp_apply wp_load_slice_index items (sint.Z n) xs dq x Hn.1 $$ [Hxs] as Hxs
      · iframe; ipureintro; exact Hx
      wp_apply (wp_mapInsert LeaseItem.ty sm S' x ()) $$ HSm as HSm
      wp_apply (wp_mapInsert LeaseItem.ty im I' x id) $$ HI as HI
      wp_for_post
      iframe
      iexists n + W64 1, x, _, _
      iframe
      ipureintro; constructor <;> word
    · wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hllk Hsm HSm]
      · inext
        iunfold leaseItems
        iexists sm, S'
        iframe
      wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hlk Hlm HM Him HI Hrdf Ha Hg Hx]
      · inext
        iunfold lessorMu
        iexists lm, im, M, I', rd0, L0
        iframe
        iframe Hls
        ipureintro; exact HL
      iapply HΦ
      iframe Hxs Hown
      ipureintro; intro _; rfl

end proof

end EtcdGrove
end Perennial

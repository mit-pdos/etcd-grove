/-
Proof of `Spec/go_etcd_io/etcd/server/v3/lease/lessor__findExpiredLeases.lean`. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__findExpiredLeases
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__expireExists
public import Spec.go_etcd_io.etcd.server.v3.lease.Lease__expired

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

theorem lease.lessor.findExpiredLeases.wp_proof
    (hEE : lease.lessor.expireExists.spec (GF := GF) (hG := hG))
    (hExp : lease.Lease.expired.spec (GF := GF) (hG := hG)) :
    lease.lessor.findExpiredLeases.spec (GF := GF) (hG := hG) := by
  intro lp lm np γl dm dn q M ri limit
  wp_start as ⟨Hlm, HM, Hnp, Hn, #Hri, #Hlos, Hmeta, Htt, %Htb⟩
  wp_auto
  wp_apply (wp_slice_make3 (V := Loc) (W64 0) (W64 16) (by word)) as %s0 ⟨Hs0, Hc0, -⟩
  (try wp_auto)
  ihave IH : iprop(∃ (s : GoSlice) (ps : List Loc),
      "Hls" ∷ leases_ptr ↦ s ∗ "Hs" ∷ s ↦* ps ∗ "Hc" ∷ ownSliceCap Loc s (DFrac.own 1) ∗
      "Hlm" ∷ lF go!"leaseMap" lp ↦{dm} lm ∗ "HM" ∷ lm ↦${dm} M ∗
      "Hnp" ∷ lF go!"leaseExpiredNotifier" lp ↦{dn} np ∗ "Hn" ∷ notifierAt np 1 ∗
      "Hmeta" ∷ ([∗map] id ↦ l ∈ M, leaseMeta id l q) ∗ "Htt" ∷ levelTok leaseLvl ∗
      "%Hps" ∷ ⌜(ps ≠ [] → ¬ leasesNoExpiry) ∧ ∀ p ∈ ps, ∃ id, M.lookup id = some p⌝)
    $$ [leases Hs0 Hc0 Hlm HM Hnp Hn Hmeta Htt]
  · iexists s0, (List.replicate (sint.nat (W64 0)) (zero_val Loc))
    iframe
    ipureintro; simp
  wp_for IH
  (try wp_auto)
  wp_apply (hEE lp lm np dm dn M ri) $$ [$Hpkg $Hlm $HM $Hnp $Hn $Hri] as %l %next ⟨Hlm, HM, Hnp, Hn, Hl⟩
  (try wp_auto)
  by_cases hln : l = null
  · subst hln
    simp only [decide_true]
    cases next
    · -- `l == nil && !next`: done
      (try wp_auto)
      wp_for_post
      (try wp_auto)
      iapply HΦ
      iframe
      (try iexists ps)
      (try iframe)
      ipureintro; exact Hps
    · -- `next`: again
      (try wp_auto)
      wp_for_post
      iframe
      (try iexists s, ps)
      (try iframe)
      ipureintro; exact Hps
  icases Hl with (%Hl | %Hl)
  · exact absurd Hl hln
  obtain ⟨id, hid⟩ := Hl
  simp only [decide_false, hln]
  cases next
  rotate_left
  · (try wp_auto)
    wp_for_post
    iframe
    (try iexists s, ps)
    (try iframe)
    ipureintro; exact Hps
  (try wp_auto)
  icases (BigSepM.bigSepM_lookup_acc (Φ := fun i x => leaseMeta (GF := GF) i x q) hid).1 $$ Hmeta
    with ⟨Hml, Hmeta⟩
  ihave #Hlo := BigSepM.bigSepM_lookup (Φ := fun _ x => isLeaseObj (GF := GF) γl x) hid $$ Hlos
  wp_apply (hExp γl l id q) $$ [$Hpkg $Hlo $Hml $Htt] as %b ⟨Hml, Htt, %Hb⟩
  · ipureintro; exact Htb
  ihave Hmeta := Hmeta $$ Hml
  cases b
  · (try wp_auto)
    wp_for_post
    iframe
    (try iexists s, ps)
    (try iframe)
    ipureintro; exact Hps
  have hNE : ¬ leasesNoExpiry := Hb rfl
  have Hps' : ((ps ++ [l]) ≠ [] → ¬ leasesNoExpiry) ∧ ∀ p ∈ ps ++ [l], ∃ id, M.lookup id = some p := by
    refine ⟨fun _ => hNE, fun p hp => ?_⟩
    rcases List.mem_append.1 hp with hp | hp
    · exact Hps.2 p hp
    · simp at hp; subst hp; exact ⟨id, hid⟩
  (try wp_auto)
  wp_apply wp_slice_literal (V := Loc) [l]
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  (try wp_auto)
  wp_apply wp_slice_append s ps _ [l] (DFrac.own 1) $$ [$Hs $Hc $Hsl] as %s' ⟨Hs', Hc', -⟩
  (try wp_auto)
  wp_if_destruct
  · wp_for_post
    (try wp_auto)
    iapply HΦ
    iframe
    (try iexists ps ++ [l])
    (try iframe)
    ipureintro; exact Hps'
  · wp_for_post
    iframe
    (try iexists s', ps ++ [l])
    (try iframe)
    ipureintro; exact Hps'

end proof

end EtcdGrove
end Perennial

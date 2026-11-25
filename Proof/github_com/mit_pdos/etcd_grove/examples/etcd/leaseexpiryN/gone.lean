/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/leaseexpiryN/gone.lean` (`notes/leaseN-plan.md`,
2026-11-16). Lean-first (no Rocq counterpart).

The poll loop (the one-member lease-expiry `Main`'s, with the listing in place of `TimeToLive`): each
poll sleeps, lists the member's leases at the caller's lower bound (`leases` at
`etcdLeaseLeasesSpecLive`: `Q`, the listing is the lessor's at an index at or after it), and, if `id`
is not listed (`listed`), returns `true` with the lease absent at that index; an error, or the polls
used up, returns `false`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.leaseexpiryN.gone
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.leaseexpiryN.leases
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.leaseexpiryN.listed
public import Perennial.Spec.time.Sleep

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_leaseexpiryN

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.leaseexpiryN.Assumptions]

set_option maxHeartbeats 1600000 in
/-- See the file header. -/
theorem gone.wp_proof
    (wp_leases : leases.spec (GF := GF) (hG := hG))
    (wp_listed : listed.spec (GF := GF) (hG := hG))
    (wp_Sleep : time.Sleep.spec (GF := GF) (hG := hG)) :
    gone.spec (GF := GF) (hG := hG) := by
  intro cl eps V γl m id
  wp_start as ⟨Hlt, #Hnc, #Hrpc, #Hlb, %hAs⟩
  ihave #Ptime : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  (try wp_auto)
  ihave IO : (∃ (n : w64), "i" ∷ i_ptr ↦ n ∗ "Hlt" ∷ levelTok 0 : IProp GF) $$ [i Hlt]
  · iexists _; iframe
  wp_for IO
  wp_if_destruct
  · (try wp_auto)
    wp_apply wp_Sleep
    (try wp_auto)
    -- the listing, at the lower bound `m`
    wp_apply (wp_leases cl eps V (etcdLeaseLeasesSpecLive γl)
        (fun r => iprop(∃ j : Nat, ⌜m ≤ j⌝ ∗ lease.leaseIdsAt γl j r.ids))) $$ [$Hlt] as %ls %lerr ⟨Hlt, Hls⟩
    · iframe #
      isplitl; rotate_left; · ipureintro; exact hAs
      imodintro; inext
      iunfold etcdLeaseLeasesSpecLive, etcdLeaseLeasesSpecLiveW
      iexists m
      iframe Hlb
      iintro %r Hr
      iexact Hr
    icases Hls with (⟨%Hlerr, %ml, %sl, #Hslf, #Hsl, ⟨%j, %Hmj, #Hids⟩⟩ | %Hlerr)
    · subst Hlerr
      (try wp_auto)
      wp_apply (wp_listed ls sl ml.ids id) $$ []
      · iframe #
      by_cases hin : id ∈ ml.ids
      · rw [decide_eq_true hin]
        (try wp_auto)
        wp_for_post
        iframe
        iexists _; iframe
      · rw [decide_eq_false hin]
        (try wp_auto)
        wp_for_post
        iapply HΦ
        iframe Hlt
        simp only [↓reduceIte]
        iunfold lease.leaseIdsAt at Hids
        icases Hids with ⟨%τ, %Hτ, #Hτat⟩
        iunfold lease.leaseAbsentFrom
        iexists j, τ
        iframe Hτat
        ipureintro
        refine ⟨Hmj, ?_⟩
        cases h : τ.1.lookup id with
        | none => rfl
        | some _ => exact absurd ((Hτ.2 id).2 (by rw [h]; rfl)) hin
    · cases lerr with
      | nil => exact absurd rfl Hlerr
      | ok ei => ?_
      (try wp_auto)
      wp_for_post
      iapply HΦ; iframe Hlt; simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
  · (try wp_auto)
    iapply HΦ; iframe Hlt; simp only [Bool.false_eq_true, ↓reduceIte]; itrivial

end proof

end etcd_leaseexpiryN
end EtcdGrove
end Perennial

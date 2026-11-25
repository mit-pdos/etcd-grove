/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/leaseN/check.lean` (`notes/leaseN-plan.md`,
2026-11-16). Lean-first (no Rocq counterpart). The one-member lease example's steps after `Serve`
(`lease/Main.lean`), at the member's address: `etcdstart.NewClient`; each read's context with the
request timeout (`client.wp_WithTimeout_bg`); `cli.Lease.Leases` (`Q`: the IDs have no duplicate) and
the double loop's check; `cli.Lease.TimeToLive(leaseID)` (`Q`: the reply's ID is `7`) and its check.
Every step's error returns `false`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.leaseN.check
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.NewClient
public import Spec.go_etcd_io.etcd.client.v3.lessor__TimeToLive
public import Spec.go_etcd_io.etcd.client.v3.lessor__Leases
public import Perennial.Spec.context.Background
public import Spec.context.WithTimeoutBackground
public import Spec.context.ErrAny
public import Proof.go_etcd_io.etcd.client.v3.LessorPlain
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_leaseN

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.leaseN.Assumptions]

set_option maxHeartbeats 1600000 in
/-- See the file header. -/
theorem check.wp_proof
    (wp_NewClient : etcdstart.NewClient.spec (GF := GF) (hG := hG))
    (wp_Background : context.Background.spec (GF := GF) (hG := hG))
    (hWT : context.WithTimeoutBackground.spec (GF := GF) (hG := hG))
    (wp_ErrAny : context.ErrAny.spec (GF := GF) (hG := hG))
    (wp_TimeToLive : lessor.TimeToLive.spec (GF := GF) (hG := hG))
    (wp_Leases : lessor.Leases.spec (GF := GF) (hG := hG)) :
    check.spec (GF := GF) (hG := hG) := by
  have wp_TimeToLive := lessor.TimeToLive.specP_of wp_TimeToLive
  have wp_Leases := lessor.Leases.specP_of wp_Leases
  intro CRE CEC addr lg V Hpe Htb hAs
  wp_start as ⟨Hlt, #Hlgz, #Hlr⟩
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave #Pes : isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart $$ []
  · iPkgInit
  ihave #Pcli : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  iunfold client.etcdLeaseReadAt at Hlr
  icases Hlr with ⟨#Hrttl, #Hrls⟩
  (try wp_auto)
  -- `NewClient(addr, lg)`
  wp_apply (wp_NewClient addr lg V Hpe Htb) $$ [$Hlt] as %cl %cerr ⟨Hlt, Hcl⟩
  · iframe #
  icases Hcl with (⟨%Hcerr, #Hnc, -⟩ | %Hcfail)
  rotate_left
  · obtain ⟨Hcerr, -⟩ := Hcfail
    cases cerr with
    | nil => exact absurd rfl Hcerr
    | ok ei => ?_
    wp_auto
    iapply HΦ; iframe Hlt; try itrivial
  subst Hcerr
  wp_auto
  iunfold isNewClient at Hnc
  icases Hnc with ⟨-, -, -, -, ⟨%lp, #Hlf, #Hla⟩, -⟩
  iunfold lessorAt at Hla
  icases Hla with ⟨%dc, %γd, %sc, %scd, %llg, %d, %γr, -, -, -, -, -, -, -, #Hrem, -, -⟩
  -- `lctx, lcancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)`
  wp_apply wp_Background
  (try wp_auto)
  wp_apply (client.wp_WithTimeout_bg hWT wp_ErrAny hAs _) $$ []
    as %lctx %lcd %lcancel ⟨#Hlcancel, #Hlctx, #Hlce, -⟩
  (try wp_auto)
  -- `cli.Lease.Leases(lctx)`, `Q`: the IDs have no duplicate
  wp_apply (wp_Leases lp [addr] etcdLeaseLeasesSpecAny
      (fun m => iprop(⌜m.ids.Nodup⌝)) lctx lcd) $$ [$Hlt] as %lsr %lerr ⟨Hlt, Hls⟩
  · iframe #
    imodintro; inext
    iunfold etcdLeaseLeasesSpecAny, etcdLeaseLeasesSpecAnyW
    iintro %m %Hm
    ipureintro; exact Hm
  -- `lcancel()`
  (try wp_auto)
  wp_apply Hlcancel
  icases Hls with (⟨%Hlerr, %m, %h, %sl, #Hhf, -, #Hslf, Hsl, %Hnd⟩ | ⟨%Hlfail, -⟩)
  rotate_left
  · obtain ⟨Hlerr, -, -⟩ := Hlfail
    cases lerr with
    | nil => exact absurd rfl Hlerr
    | ok ei => ?_
    wp_auto
    iapply HΦ; iframe Hlt; try itrivial
  subst Hlerr
  (try wp_auto)
  -- the double loop: no ID twice (`Nodup`)
  imod ownSlice_persist _ _ _ $$ Hsl with #Hsl
  ihave %Hlen := ownSlice_len $$ Hsl
  rename_i gi
  irename : (gi ↦ zero_val w64 : IProp GF) => gi
  ihave IO : (∃ (n gv : w64), "i" ∷ i_ptr ↦ n ∗ "gi" ∷ gi ↦ gv ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n⌝ : IProp GF) $$ [i gi]
  · iexists W64 0, _
    simp only [named]
    iframe
    ipureintro; decide
  wp_for IO
  wp_if_destruct
  · -- the `n`th lease: none of the ones before it has its ID
    have Hlt : sint.nat n < m.ids.length := by rw [List.length_map] at Hlen; word
    obtain ⟨x, hx⟩ : ∃ x, m.ids[sint.nat n]? = some x := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have hxs : (m.ids.map (fun id => (go_etcd_io.etcd.client.v3.LeaseStatus.mk id)))[sint.nat n]? =
        some (go_etcd_io.etcd.client.v3.LeaseStatus.mk x) := by simp [hx]
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len := ⟨Hn, Hif⟩
    simp only [Hbnd, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index _ (sint.Z n) _ DFrac.discard _ Hn $$ [Hsl] as -
    · iframe Hsl; ipureintro; exact hxs
    icases ownSlice_elem_acc (sint.Z n) _ sl DFrac.discard _ Hn hxs $$ Hsl with ⟨#Hxn, -⟩
    icases (go_etcd_io.etcd.client.v3.LeaseStatus.LeaseStatus_access_load_ID
        (sliceIndexRef go_etcd_io.etcd.client.v3.LeaseStatus (sint.Z n) sl)
        (go_etcd_io.etcd.client.v3.LeaseStatus.mk x) DFrac.discard).access_strict $$ Hxn with ⟨#Hxid, -⟩
    (try wp_auto)
    ihave IJ : (∃ (k : w64), "j" ∷ j_ptr ↦ k ∗
        "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z n⌝ : IProp GF) $$ [j]
    · iexists W64 0
      simp only [named]
      iframe
      ipureintro; constructor <;> word
    wp_for IJ
    wp_if_destruct
    · have Hlk : sint.nat k < m.ids.length := by word
      obtain ⟨y, hy⟩ : ∃ y, m.ids[sint.nat k]? = some y := ⟨_, List.getElem?_eq_getElem Hlk⟩
      have hys : (m.ids.map (fun id => (go_etcd_io.etcd.client.v3.LeaseStatus.mk id)))[sint.nat k]? =
          some (go_etcd_io.etcd.client.v3.LeaseStatus.mk y) := by simp [hy]
      icases ownSlice_elem_acc (sint.Z k) _ sl DFrac.discard _ Hk.1 hys $$ Hsl with ⟨#Hyk, -⟩
      icases (go_etcd_io.etcd.client.v3.LeaseStatus.LeaseStatus_access_load_ID
          (sliceIndexRef go_etcd_io.etcd.client.v3.LeaseStatus (sint.Z k) sl)
          (go_etcd_io.etcd.client.v3.LeaseStatus.mk y) DFrac.discard).access_strict $$ Hyk with ⟨#Hyid, -⟩
      have Hbk : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z sl.len := ⟨Hk.1, by word⟩
      simp only [Hbnd, _root_.and_self, ↓reduceIte]
      (try wp_auto)
      (try simp only [Hbk, _root_.and_self, ↓reduceIte])
      (try wp_auto)
      -- `k < n`: the IDs differ (`Nodup`)
      have Hne : x ≠ y := by
        intro hxy
        have := List.Nodup.eq_of_getElem?_eq (j := sint.nat k) Hnd Hlt (by rw [hx, hy, hxy])
        word
      rw [decide_eq_false Hne]
      (try wp_auto)
      wp_for_post
      iframe
      iexists k + W64 1
      simp only [named]
      iframe
      ipureintro; constructor <;> word
    · (try wp_auto)
      wp_for_post
      iframe
      iexists n + W64 1, n
      simp only [named]
      iframe
      ipureintro; word
  · (try wp_auto)
    -- `tctx, tcancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)`
    wp_apply wp_Background
    (try wp_auto)
    wp_apply (client.wp_WithTimeout_bg hWT wp_ErrAny hAs _) $$ []
      as %tctx %tcd %tcancel ⟨#Htcancel, #Htctx, #Htce, -⟩
    (try wp_auto)
    -- `cli.Lease.TimeToLive(tctx, leaseID)`, `Q`: the reply's ID is `7`
    wp_apply (wp_TimeToLive lp [addr] etcdLeaseTTLSpec
        (fun m => iprop(⌜m.id = W64 7⌝)) tctx tcd (W64 7) slice.nil []) $$ [$Hlt] as %tr %terr ⟨Hlt, Htl⟩
    · iframe #
      isplitl
      · imodintro; inext
        iunfold etcdLeaseTTLSpec, etcdLeaseTTLSpecW
        iintro %m %Hm
        ipureintro; exact Hm
      iunfold leaseOptsAt
      iexists ([] : List GoFunc)
      isplitl
      · iapply ownSlice_nil
      isplitl
      · ipureintro; rfl
      imodintro
      iintro %i %f %g %Hf %Hg
      simp at Hf
    -- `tcancel()`
    (try wp_auto)
    wp_apply Htcancel
    icases Htl with (⟨%Hterr, %mt, %ht, %ks, #Hth, -, #Htid, -, -, -, %Hmid⟩ | ⟨%Htfail, -⟩)
    rotate_left
    · obtain ⟨Hterr, -, -⟩ := Htfail
      cases terr with
      | nil => exact absurd rfl Hterr
      | ok ei => ?_
      wp_auto
      iapply HΦ; iframe Hlt; try itrivial
    subst Hterr
    (try wp_auto)
    -- the check: the reply is about lease `7`
    simp only [Hmid, _root_.decide_true, Bool.not_true]
    wp_auto
    iapply HΦ; iframe Hlt; try itrivial

end proof

end etcd_leaseN
end EtcdGrove
end Perennial

/-
Proof of `RunLeaseCatchup.spec` (leasecatchup's `run` argument, `Proof/.../examples/etcd/leasecatchup/run.lean`,
at members at other machines): the clients `c3` (of the last member, `mid3`) and `c1` (of the first), each
`Close`d at return (`defer`); `g1 := leaseGrant(c3, maxLeaseTTL)` is granted at `Γ.ls mid3`
(`leaseGrant.specMono`); `ready()`; the fillers' grants (their facts unused); each poll's listing of `c3` has
`g1` (`leaseList.specGranted` at `G = [g1]`), so `listed(ls, g1.ID)` is `true` and the panic is unreachable.
Every step's error returns `ended(...)`.
Lean-first (no Rocq counterpart); #50 N9b (`notes/etcd-dist-n9b.md`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.RunLeaseCatchup
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.newClient
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.leaseGrant
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.leaseList
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.listed
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.checked
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.ended
public import Perennial.Spec.time.Sleep
public import Spec.go_etcd_io.etcd.client.v3.Client__Close
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Iris.ProofMode Net client
open github_com.mit_pdos.etcd_grove.examples.etcd.dist
open etcd_dist.view

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [esrv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]

set_option maxHeartbeats 3200000 in
/-- See the file header. -/
theorem RunLeaseCatchup.wp_proof (svc : DistView → w64 → GrpcSvc GF)
    (wp_newClient : newClient.spec (GF := GF) (hG := hG))
    (wp_leaseGrant : leaseGrant.specMono (GF := GF) (hG := hG) svc)
    (wp_leaseList : leaseList.specGranted (GF := GF) (hG := hG) svc)
    (wp_listed : listed.spec (GF := GF) (hG := hG))
    (wp_checked : checked.spec (GF := GF) (hG := hG))
    (wp_ended : ended.spec (GF := GF) (hG := hG))
    (wp_Sleep : time.Sleep.spec (GF := GF) (hG := hG))
    (wp_Close : EtcdGrove.Client.Close.spec (GF := GF) (hG := hG)) :
    RunLeaseCatchup.spec (GF := GF) (hG := hG) svc := by
  intro π Γ eps addrs ready hV Htb hAs hlm hne
  wp_start as ⟨Hlt, #Heps, #Hms, Hready⟩
  ihave %Hlen := ownSlice_len $$ Heps
  have hpos : 0 < addrs.length := List.length_pos_iff.2 hne
  ihave #Ptime : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  -- the members: the last (`x3`) and the first (`x1`)
  obtain ⟨x3, hx3⟩ : ∃ x, addrs[addrs.length - 1]? = some x :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨x1, hx1⟩ : ∃ x, addrs[0]? = some x := ⟨_, List.getElem?_eq_getElem hpos⟩
  ihave #Hm3 := BigSepL.bigSepL_lookup hx3 $$ Hms
  ihave #Hm1 := BigSepL.bigSepL_lookup hx1 $$ Hms
  iunfold leaseMember at Hm3 Hm1
  icases Hm3 with ⟨%Hok3, %mid3, #Haddr3⟩
  icases Hm1 with ⟨%Hok1, %mid1, #Haddr1⟩
  have hpl3 : plainEndpoints [x3] := plainEndpoints_singleton _ (etcd_dist.addrOk_plainEndpoint Hok3)
  have hpl1 : plainEndpoints [x1] := plainEndpoints_singleton _ (etcd_dist.addrOk_plainEndpoint Hok1)
  (try wp_auto)
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  -- `c3, err := newClient([]string{eps[k-1]})`
  have Hb3 : 0 ≤ sint.Z (eps.len - W64 1) ∧ sint.Z (eps.len - W64 1) < sint.Z eps.len := by
    constructor <;> word
  (try simp only [Hb3, _root_.and_self, ↓reduceIte])
  wp_apply wp_load_slice_index eps (sint.Z (eps.len - W64 1)) _ _ x3 Hb3.1 $$ [Heps] as -
  · iframe #; ipureintro; rw [show (sint.Z (eps.len - W64 1)).toNat = addrs.length - 1 by word]; exact hx3
  (try wp_auto)
  wp_apply wp_slice_literal (V := GoString) (l := [x3])
  isplitr
  · ipureintro; rfl
  iintro %lit3 ⟨Hlit3, -⟩
  imod ownSlice_persist _ _ _ $$ Hlit3 with #Hlit3
  (try wp_auto)
  wp_apply (wp_newClient _ [x3] (Classical.choice hV) Htb hpl3) $$ [$Hlt] as %c3 %cerr ⟨Hlt, Hcl⟩
  · iframe #
  icases Hcl with (⟨%Hcerr, #Hnc3, #Hnp3⟩ | %Hcfail)
  rotate_left
  · obtain ⟨Hcerr, -⟩ := Hcfail
    cases cerr with
    | nil => exact absurd rfl Hcerr
    | ok ei => ?_
    (try wp_auto)
    wp_apply wp_ended as %r -
    (try wp_auto)
    iapply HΦ; iframe Hlt
  subst Hcerr
  ihave #Hcore3 := clientCoreAt_of_new c3 [x3] (Classical.choice hV) $$ [Hnc3 Hnp3]
  · iframe #
  ihave #Hmc3 : memberCli svc c3 x3 (Classical.choice hV) Γ mid3 $$ []
  · iunfold memberCli; iframe #
  (try wp_auto)
  -- `c1, err := newClient([]string{eps[0]})`
  have Hb1 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z eps.len := by constructor <;> word
  (try simp only [Hb1, _root_.and_self, ↓reduceIte])
  wp_apply wp_load_slice_index eps (sint.Z (W64 0)) _ _ x1 Hb1.1 $$ [Heps] as -
  · iframe #; ipureintro; exact hx1
  (try wp_auto)
  wp_apply wp_slice_literal (V := GoString) (l := [x1])
  isplitr
  · ipureintro; rfl
  iintro %lit1 ⟨Hlit1, -⟩
  imod ownSlice_persist _ _ _ $$ Hlit1 with #Hlit1
  (try wp_auto)
  wp_apply (wp_newClient _ [x1] (Classical.choice hV) Htb hpl1) $$ [$Hlt] as %c1 %cerr ⟨Hlt, Hcl⟩
  · iframe #
  icases Hcl with (⟨%Hcerr, #Hnc1, #Hnp1⟩ | %Hcfail)
  rotate_left
  · obtain ⟨Hcerr, -⟩ := Hcfail
    cases cerr with
    | nil => exact absurd rfl Hcerr
    | ok ei => ?_
    (try wp_auto)
    wp_apply wp_ended as %r -
    (try wp_auto)
    wp_apply wp_Close as %ce -
    · iframe #
    (try wp_auto)
    iapply HΦ; iframe Hlt
  subst Hcerr
  ihave #Hcore1 := clientCoreAt_of_new c1 [x1] (Classical.choice hV) $$ [Hnc1 Hnp1]
  · iframe #
  ihave #Hmc1 : memberCli svc c1 x1 (Classical.choice hV) Γ mid1 $$ []
  · iunfold memberCli; iframe #
  (try wp_auto)
  -- `g1, err := leaseGrant(c3, maxLeaseTTL)`: granted at the last member's lessor
  wp_apply (wp_leaseGrant c3 x3 (Classical.choice hV) Γ mid3 _ hAs hlm) $$ [$Hlt] as %g1 %gerr ⟨Hlt, Hg⟩
  · iframe #
  icases Hg with (⟨%Hgerr, %mg, #Hg1id, #Hg1ttl, %Hg1nz, %gi, #Hg1gr⟩ | %Hgfail)
  rotate_left
  · obtain ⟨Hgerr, -⟩ := Hgfail
    cases gerr with
    | nil => exact absurd rfl Hgerr
    | ok ei => ?_
    (try wp_auto)
    wp_apply wp_ended as %r -
    (try wp_auto)
    wp_apply wp_Close as %ce -
    · iframe #
    (try wp_auto)
    wp_apply wp_Close as %ce' -
    · iframe #
    (try wp_auto)
    iapply HΦ; iframe Hlt
  subst Hgerr
  ihave #HG : [∗list] id ∈ [mg.id], ∃ i : Nat, lease.leaseGrantedAt (Γ.ls mid3) i id $$ []
  · iapply BigSepL.bigSepL_singleton.2
    iexists gi; iexact Hg1gr
  (try wp_auto)
  -- `ready()`
  wp_apply Hready
  (try wp_auto)
  -- the fillers, through the first member (their facts unused)
  ihave IF : (∃ (n lv : w64) (gb : Bool), "i" ∷ i_ptr ↦ n ∗ "last" ∷ last_ptr ↦ lv ∗
      "granted" ∷ granted_ptr ↦ gb ∗ "Hlt" ∷ levelTok 0 : IProp GF) $$ [i last granted Hlt]
  · iexists _, _, _; iframe
  wp_for IF
  wp_if_destruct
  · (try wp_auto)
    wp_apply (wp_leaseGrant c1 x1 (Classical.choice hV) Γ mid1 _ hAs hlm) $$ [$Hlt]
      as %f %ferr ⟨Hlt, Hf⟩
    · iframe #
    icases Hf with (⟨%Hferr, %mf, #Hfid, -, -, -⟩ | %Hffail)
    · subst Hferr
      (try wp_auto)
      wp_for_post
      iframe
      iexists _, _, true; iframe
    · obtain ⟨Hferr, -⟩ := Hffail
      cases ferr with
      | nil => exact absurd rfl Hferr
      | ok ei => ?_
      (try wp_auto)
      wp_for_post
      iframe
      iexists _, _, gb; iframe
  (try wp_auto)
  cases gb
  · -- no filler granted
    (try wp_auto)
    wp_apply wp_ended as %r -
    (try wp_auto)
    wp_apply wp_Close as %ce -
    · iframe #
    (try wp_auto)
    wp_apply wp_Close as %ce' -
    · iframe #
    (try wp_auto)
    iapply HΦ; iframe Hlt
  (try wp_auto)
  -- the polls of the last member's listing: each has `g1`
  ihave IP : (∃ (n : w64), "p" ∷ p_ptr ↦ n ∗ "Hlt" ∷ levelTok 0 : IProp GF) $$ [p Hlt]
  · iexists _; iframe
  wp_for IP
  wp_if_destruct
  · (try wp_auto)
    wp_apply (wp_leaseList c3 x3 (Classical.choice hV) Γ mid3 [mg.id] hAs hlm) $$ [$Hlt]
      as %ls %lerr ⟨Hlt, Hls⟩
    · iframe #
    icases Hls with (⟨%Hlerr, %ids, %sl, #Hslf, Hsl, %Hids⟩ | %Hlfail)
    · subst Hlerr
      imod ownSlice_persist _ _ _ $$ Hsl with #Hsl
      have hg1 : mg.id ∈ ids := Hids.2 mg.id (List.mem_singleton_self _)
      (try wp_auto)
      wp_apply (wp_listed ls sl ids lv) $$ []
      · iframe #
      by_cases hin : lv ∈ ids
      · rw [decide_eq_true hin]
        (try wp_auto)
        wp_apply (wp_listed ls sl ids mg.id) $$ []
        · iframe #
        rw [decide_eq_true hg1]
        (try wp_auto)
        wp_apply wp_checked as %r -
        (try wp_auto)
        wp_for_post
        wp_apply wp_Close as %ce -
        · iframe #
        (try wp_auto)
        wp_apply wp_Close as %ce' -
        · iframe #
        (try wp_auto)
        iapply HΦ; iframe Hlt
      · rw [decide_eq_false hin]
        (try wp_auto)
        wp_apply wp_Sleep
        (try wp_auto)
        wp_for_post
        iframe
        iexists _; iframe
    · obtain ⟨Hlerr, -⟩ := Hlfail
      cases lerr with
      | nil => exact absurd rfl Hlerr
      | ok ei => ?_
      (try wp_auto)
      wp_apply wp_Sleep
      (try wp_auto)
      wp_for_post
      iframe
      iexists _; iframe
  -- polls exhausted
  (try wp_auto)
  wp_apply wp_ended as %r -
  (try wp_auto)
  wp_apply wp_Close as %ce -
  · iframe #
  (try wp_auto)
  wp_apply wp_Close as %ce' -
  · iframe #
  (try wp_auto)
  iapply HΦ; iframe Hlt

end proof

end etcd_dist_client
end EtcdGrove
end Perennial

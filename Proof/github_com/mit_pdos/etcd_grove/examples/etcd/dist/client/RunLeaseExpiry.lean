/-
Proof of `RunLeaseExpiry.spec` (leaseexpiryN's `run` argument, `Proof/.../examples/etcd/leaseexpiryN/run.lean`,
at members at other machines): the grant loop keeps, per member, its client (each `Close`d at return: the
`defer` chain, a triple `Hdv`) and, when its grant answered, the lease's snapshot (`expiryAt`); the check
loop: `gone` at the snapshot's index gives the lease absent at a later index, the listing at that index is a
snapshot at a still later one, where the lease is absent (`lessorAbsentStays_dist.law`), so `listed` is
`false` and the panic is unreachable.
Lean-first (no Rocq counterpart); #50 N9b (`notes/etcd-dist-n9b.md`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.RunLeaseExpiry
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.gone
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.MembersDefs
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
open etcd_dist etcd_dist.view etcdstart

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [esrv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- **The grant loop's fact of one member** (persistent): the client `c` of a member `mid` of the view at
`a` (closable), and, if its grant answered (`b`), a snapshot of the member's lessor history holding the
lease `id` (leaseexpiryN's `grantedAt`). -/
def expiryAt [π : NetProtoGS] (Γ : DistView) (c : Loc) (id : w64)
    (b : Bool) : IProp GF :=
  iprop(∃ (a : GoString) (V : WEnv GF) (mid : w64), memberCli c a V Γ mid ∗ clientCoreAt c ∗
    (if b then ∃ (i : Nat) (σ : lease.LSnap), ⌜(σ.1.lookup id).isSome⌝ ∗ lease.lessorAt (Γ.ls mid) i σ
     else True))

instance expiryAt_persistent [π : NetProtoGS] (Γ : DistView) (c : Loc)
    (id : w64) (b : Bool) : Persistent (expiryAt (GF := GF) Γ c id b) := by
  unfold expiryAt; cases b <;> infer_instance

/-- A slice's model where the grant loop does not store: the default value appended. -/
theorem app_replicate_snoc {α : Type _} (l : List α) (L : Nat) (z : α) (h : l.length < L) :
    l ++ List.replicate (L - l.length) z = (l ++ [z]) ++ List.replicate (L - (l ++ [z]).length) z := by
  obtain ⟨d, hd⟩ : ∃ d, L - l.length = d + 1 := ⟨L - l.length - 1, by omega⟩
  simp only [List.length_append, List.length_singleton]
  rw [hd, show L - (l.length + 1) = d by omega, List.replicate_succ, List.append_assoc]
  rfl

end defs

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
theorem RunLeaseExpiry.wp_proof
    (wp_newClient : newClient.spec (GF := GF) (hG := hG))
    (wp_leaseGrant : leaseGrant.spec (GF := GF) (hG := hG))
    (wp_leaseList : leaseList.specLive (GF := GF) (hG := hG))
    (wp_gone : gone.spec (GF := GF) (hG := hG))
    (wp_listed : listed.spec (GF := GF) (hG := hG))
    (wp_checked : checked.spec (GF := GF) (hG := hG))
    (wp_ended : ended.spec (GF := GF) (hG := hG))
    (wp_Close : EtcdGrove.Client.Close.spec (GF := GF) (hG := hG)) :
    RunLeaseExpiry.spec (GF := GF) (hG := hG) := by
  intro π Γ eps addrs hV Htb hAs hlm hinj
  wp_start as ⟨Hlt, #Heps, #Hms⟩
  ihave %Hlen := ownSlice_len $$ Heps
  (try wp_auto)
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  -- `clis`, `ids`, `ok := make(…, len(eps))`
  wp_apply (wp_slice_make2 (V := Loc) eps.len) as %clsl ⟨Hclsl, -⟩
  · ipureintro; word
  (try wp_auto)
  wp_apply (wp_slice_make2 (V := w64) eps.len) as %idsl ⟨Hidsl, -⟩
  · ipureintro; word
  (try wp_auto)
  wp_apply (wp_slice_make2 (V := Bool) eps.len) as %oksl ⟨Hoksl, -⟩
  · ipureintro; word
  (try wp_auto)
  have hkn : sint.nat eps.len = addrs.length := by word
  -- the grant loop
  ihave IG : (∃ (n jv : w64) (av : GoString) (cs : List Loc) (gids : List w64) (oks : List Bool)
      (dv : GoFunc),
      "i" ∷ i_ptr ↦ n ∗ "j" ∷ j_ptr ↦ jv ∗ "a" ∷ a_ptr ↦ av ∗ "Hlt" ∷ levelTok 0 ∗
      "defer" ∷ defer ↦ dv ∗
      "#Hdv" ∷ □ (∀ Ψ : val → IProp GF, ▷ Ψ #() -∗ WP (App (Val #dv) (Val #())) {{ Ψ }}) ∗
      "Hclsl" ∷ clsl ↦* (cs ++ List.replicate (addrs.length - cs.length) (zero_val Loc)) ∗
      "Hidsl" ∷ idsl ↦* (gids ++ List.replicate (addrs.length - gids.length) (zero_val w64)) ∗
      "Hoksl" ∷ oksl ↦* (oks ++ List.replicate (addrs.length - oks.length) (zero_val Bool)) ∗
      "#Hgr" ∷ ([∗list] p ∈ cs.zip (gids.zip oks), expiryAt Γ p.1 p.2.1 p.2.2) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.nat n ≤ addrs.length ∧ cs.length = sint.nat n ∧
        gids.length = sint.nat n ∧ oks.length = sint.nat n⌝ : IProp GF)
      $$ [i j a Hlt defer Hclsl Hidsl Hoksl]
  · iexists W64 0, _, _, [], [], [], _
    simp only [List.length_nil, Nat.sub_zero, List.nil_append, List.zip_nil_left]
    iframe
    isplitr
    · iintro !> %Ψ HΨ
      wp_auto
      (try iexact HΨ)
    isplitl [Hclsl]
    · iExactEq Hclsl; rw [hkn]
    isplitl [Hidsl]
    · iExactEq Hidsl; rw [hkn]
    isplitl [Hoksl]
    · iExactEq Hoksl; rw [hkn]
    isplitl
    · iapply BigSepL.bigSepL_nil.2; itrivial
    have h00 : sint.nat (W64 0) = 0 := rfl
    ipureintro; exact ⟨by decide, by omega, h00.symm, h00.symm, h00.symm⟩
  wp_for IG
  wp_if_destruct
  · have hlt : sint.nat n < addrs.length := by word
    list_elem addrs (sint.nat n) as x
    have hnz : (sint.Z n).toNat = sint.nat n := by word
    have Hbm : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z eps.len := ⟨Hn.1, Hif⟩
    (try wp_auto)
    (try simp only [Hbm, _root_.and_self, ↓reduceIte])
    wp_apply wp_load_slice_index eps (sint.Z n) _ _ x Hbm.1 $$ [Heps] as -
    · iframe #; ipureintro; rw [hnz]; exact Hx_lookup
    (try wp_auto)
    ihave #Hmx := BigSepL.bigSepL_lookup Hx_lookup $$ Hms
    iunfold leaseMember at Hmx
    icases Hmx with ⟨%Hok, %mid, #Haddr, #Hslot⟩
    have hpl : plainEndpoints [x] := plainEndpoints_singleton _ (etcd_dist.addrOk_plainEndpoint Hok)
    -- `cli, err := newClient([]string{a})`
    wp_apply wp_slice_literal (V := GoString) (l := [x])
    isplitr
    · ipureintro; rfl
    iintro %lit ⟨Hlit, -⟩
    imod ownSlice_persist _ _ _ $$ Hlit with #Hlit
    (try wp_auto)
    wp_apply (wp_newClient _ [x] (Classical.choice hV) Htb hpl) $$ [$Hlt] as %cl %cerr ⟨Hlt, Hcl⟩
    · iframe #
    icases Hcl with (⟨%Hcerr, #Hnc, #Hnp, -⟩ | %Hcfail)
    rotate_left
    · obtain ⟨Hcerr, -⟩ := Hcfail
      cases cerr with
      | nil => exact absurd rfl Hcerr
      | ok ei => ?_
      (try wp_auto)
      wp_apply wp_ended as %r -
      (try wp_auto)
      wp_for_post
      (try wp_auto)
      wp_apply Hdv
      (try wp_auto)
      iapply HΦ; iframe Hlt
    subst Hcerr
    ihave #Hcore := clientCoreAt_of_new cl [x] (Classical.choice hV) $$ [Hnc Hnp]
    · iframe #
    ihave #Hmc : memberCli cl x (Classical.choice hV) Γ mid $$ []
    · iunfold memberCli; iframe #
    (try wp_auto)
    -- `defer cli.Close()`: the chain's triple
    ihave ⟨%dv', defer, #Hdv'⟩ : iprop(∃ dv' : GoFunc, defer ↦ dv' ∗
        □ (∀ Ψ : val → IProp GF, ▷ Ψ #() -∗ WP (App (Val #dv') (Val #())) {{ Ψ }})) $$ [defer]
    · iexists _
      iframe defer
      iintro !> %Ψ HΨ
      wp_auto
      wp_apply wp_Close as %ce -
      · iframe #
      (try wp_auto)
      iapply Hdv
      iexact HΨ
    iclear Hdv
    -- `clis[j] = cli`
    ihave %Hcll := ownSlice_len $$ Hclsl
    ihave %Hidl := ownSlice_len $$ Hidsl
    ihave %Hokl := ownSlice_len $$ Hoksl
    have hcl : (cs ++ List.replicate (addrs.length - cs.length) (zero_val Loc)).length = addrs.length := by
      simp; omega
    have hil : (gids ++ List.replicate (addrs.length - gids.length) (zero_val w64)).length = addrs.length := by
      simp; omega
    have hol : (oks ++ List.replicate (addrs.length - oks.length) (zero_val Bool)).length = addrs.length := by
      simp; omega
    rw [hcl] at Hcll
    rw [hil] at Hidl
    rw [hol] at Hokl
    have Hb2 : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z clsl.len := by
      obtain ⟨h1, h2⟩ := Hcll; constructor <;> word
    have Hb3 : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z idsl.len := by
      obtain ⟨h1, h2⟩ := Hidl; constructor <;> word
    have Hb4 : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z oksl.len := by
      obtain ⟨h1, h2⟩ := Hokl; constructor <;> word
    (try simp only [Hb2, _root_.and_self, ↓reduceIte])
    wp_apply (wp_store_slice_index clsl (sint.Z n) _ cl) $$ [Hclsl] as Hclsl
    · iframe Hclsl; ipureintro; rw [hcl]; constructor <;> word
    (try wp_auto)
    have hcz : (sint.Z n).toNat = cs.length := by rw [hnz, Hn.2.2.1]
    have hgz : (sint.Z n).toNat = gids.length := by rw [hnz, Hn.2.2.2.1]
    have hoz : (sint.Z n).toNat = oks.length := by rw [hnz, Hn.2.2.2.2]
    have hn1 : sint.nat (n + W64 1) = sint.nat n + 1 := by word
    -- `g, err := leaseGrant(cli, expiryTTL)`: live in the member's lessor history from an index
    wp_apply (wp_leaseGrant cl x (Classical.choice hV) Γ mid _ hAs hlm hinj) $$ [$Hlt] as %g %gerr ⟨Hlt, Hg⟩
    · iframe #
    icases Hg with (⟨%Hgerr, %mg, #Hgid, -, -, %gi, %gl, #Hlive, -⟩ | %Hgfail)
    · subst Hgerr
      (try wp_auto)
      (try simp only [Hb3, _root_.and_self, ↓reduceIte])
      wp_apply (wp_store_slice_index idsl (sint.Z n) _ mg.id) $$ [Hidsl] as Hidsl
      · iframe Hidsl; ipureintro; rw [hil]; constructor <;> word
      (try wp_auto)
      (try simp only [Hb4, _root_.and_self, ↓reduceIte])
      wp_apply (wp_store_slice_index oksl (sint.Z n) _ true) $$ [Hoksl] as Hoksl
      · iframe Hoksl; ipureintro; rw [hol]; constructor <;> word
      (try wp_auto)
      iunfold lease.leaseLiveFrom at Hlive
      icases Hlive with ⟨%i', %σ, %Hσ, #Hσat⟩
      have hzz : (cs ++ [cl]).zip ((gids ++ [mg.id]).zip (oks ++ [true])) =
          cs.zip (gids.zip oks) ++ [(cl, (mg.id, true))] := by
        rw [List.zip_append (by omega), List.zip_append (by simp; omega)]; rfl
      ihave #Hgr' : [∗list] p ∈ (cs ++ [cl]).zip ((gids ++ [mg.id]).zip (oks ++ [true])),
          expiryAt Γ p.1 p.2.1 p.2.2 $$ []
      · rw [hzz]
        iapply BigSepL.bigSepL_snoc.2
        iframe #
        iunfold expiryAt
        iexists x, Classical.choice hV, mid
        iframe #
        simp only [↓reduceIte]
        iexists i', σ
        iframe #
        ipureintro; rw [Hσ.2]; rfl
      iclear Hgr
      wp_for_post
      iframe
      iexists n + W64 1, n, x, cs ++ [cl], gids ++ [mg.id], oks ++ [true], dv'
      rw [hn1]
      iframe; iframe #
      isplitl [Hclsl]
      · iExactEq Hclsl
        rw [hcz, set_replicate_snoc _ _ _ _ (by omega)]
        simp only [List.length_append, List.length_singleton]
      isplitl [Hidsl]
      · iExactEq Hidsl
        rw [hgz, set_replicate_snoc _ _ _ _ (by omega)]
        simp only [List.length_append, List.length_singleton]
      isplitl [Hoksl]
      · iExactEq Hoksl
        rw [hoz, set_replicate_snoc _ _ _ _ (by omega)]
        simp only [List.length_append, List.length_singleton]
      ipureintro; refine ⟨by word, by omega, by simp [Hn.2.2.1], by simp [Hn.2.2.2.1], by simp [Hn.2.2.2.2]⟩
    · obtain ⟨Hgerr, -⟩ := Hgfail
      cases gerr with
      | nil => exact absurd rfl Hgerr
      | ok ei => ?_
      (try wp_auto)
      have hzz : (cs ++ [cl]).zip ((gids ++ [zero_val w64]).zip (oks ++ [zero_val Bool])) =
          cs.zip (gids.zip oks) ++ [(cl, (zero_val w64, zero_val Bool))] := by
        rw [List.zip_append (by omega), List.zip_append (by simp; omega)]; rfl
      ihave #Hgr' : [∗list] p ∈ (cs ++ [cl]).zip ((gids ++ [zero_val w64]).zip (oks ++ [zero_val Bool])),
          expiryAt Γ p.1 p.2.1 p.2.2 $$ []
      · rw [hzz]
        iapply BigSepL.bigSepL_snoc.2
        iframe #
        iunfold expiryAt
        iexists x, Classical.choice hV, mid
        iframe #
        have hzb : (zero_val Bool) = false := rfl
        simp only [hzb, Bool.false_eq_true, ↓reduceIte]
        itrivial
      iclear Hgr
      wp_for_post
      iframe
      iexists n + W64 1, n, x, cs ++ [cl], gids ++ [zero_val w64], oks ++ [zero_val Bool], dv'
      rw [hn1]
      iframe; iframe #
      isplitl [Hclsl]
      · iExactEq Hclsl
        rw [hcz, set_replicate_snoc _ _ _ _ (by omega)]
        simp only [List.length_append, List.length_singleton]
      isplitl [Hidsl]
      · iExactEq Hidsl
        rw [app_replicate_snoc _ _ _ (by omega)]
      isplitl [Hoksl]
      · iExactEq Hoksl
        rw [app_replicate_snoc _ _ _ (by omega)]
      ipureintro; refine ⟨by word, by omega, by simp [Hn.2.2.1], by simp [Hn.2.2.2.1], by simp [Hn.2.2.2.2]⟩
  -- every member's grant tried: the slices hold the clients, the lease ids and the flags
  have hnk2 : sint.nat n = addrs.length := by word
  have hcsl : cs.length = addrs.length := by omega
  have hgsl : gids.length = addrs.length := by omega
  have hosl : oks.length = addrs.length := by omega
  simp only [hcsl, hgsl, hosl, Nat.sub_self, List.replicate_zero, List.append_nil]
  imod ownSlice_persist _ _ _ $$ Hclsl with #Hclsl
  imod ownSlice_persist _ _ _ $$ Hidsl with #Hidsl
  imod ownSlice_persist _ _ _ $$ Hoksl with #Hoksl
  ihave %Hcll := ownSlice_len $$ Hclsl
  ihave %Hidl := ownSlice_len $$ Hidsl
  ihave %Hokl := ownSlice_len $$ Hoksl
  (try wp_auto)
  -- the check loop
  ihave IB : (∃ (n jv k : w64), "i" ∷ i_ptr ↦ n ∗ "j" ∷ j_ptr ↦ jv ∗ "n" ∷ n_ptr ↦ k ∗ "Hlt" ∷ levelTok 0 ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.nat n ≤ addrs.length⌝ : IProp GF) $$ [i j n Hlt]
  · iexists W64 0, _, _
    iframe
    ipureintro; exact ⟨by decide, by simp⟩
  clear Hif
  wp_for IB
  wp_if_destruct
  · have hlt : sint.nat n < addrs.length := by word
    list_elem cs (sint.nat n) as cj
    list_elem gids (sint.nat n) as idj
    list_elem oks (sint.nat n) as bj
    list_elem addrs (sint.nat n) as x
    have hnz : (sint.Z n).toNat = sint.nat n := by word
    have Hb2 : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z clsl.len := ⟨Hn.1, by have := Hcll.1; word⟩
    have Hb3 : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z idsl.len := ⟨Hn.1, by have := Hidl.1; word⟩
    have Hb4 : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z oksl.len := ⟨Hn.1, by have := Hokl.1; word⟩
    have Hif' : sint.Z n < sint.Z eps.len := by simpa using Hif
    have Hbm : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z eps.len := ⟨Hn.1, Hif'⟩
    have hzj1 : (gids.zip oks)[sint.nat n]? = some (idj, bj) :=
      List.getElem?_zip_eq_some.2 ⟨Hidj_lookup, Hbj_lookup⟩
    have hzj : (cs.zip (gids.zip oks))[sint.nat n]? = some (cj, (idj, bj)) :=
      List.getElem?_zip_eq_some.2 ⟨Hcj_lookup, hzj1⟩
    ihave #Hgj := BigSepL.bigSepL_lookup hzj $$ Hgr
    iunfold expiryAt at Hgj
    icases Hgj with ⟨%aj, %Vj, %midj, #Hmcj, #Hcorej, Hσj⟩
    (try wp_auto)
    (try simp only [Hbm, _root_.and_self, ↓reduceIte])
    wp_apply wp_load_slice_index eps (sint.Z n) _ _ x Hbm.1 $$ [Heps] as -
    · iframe #; ipureintro; rw [hnz]; exact Hx_lookup
    (try wp_auto)
    (try simp only [Hb4, _root_.and_self, ↓reduceIte])
    wp_apply wp_load_slice_index oksl (sint.Z n) _ _ bj Hb4.1 $$ [Hoksl] as -
    · iframe #; ipureintro; rw [hnz]; exact Hbj_lookup
    (try wp_auto)
    cases bj
    · -- no grant answered at this member: `continue`
      (try wp_auto)
      wp_for_post
      iframe
      iexists n + W64 1, n, k
      iframe
      ipureintro; constructor <;> word
    simp only [↓reduceIte]
    (try wp_auto)
    icases Hσj with ⟨%i, %σ, %Hσ, #Hσat⟩
    ihave #Hlb := lease.lessorAt_lb (Γ.ls midj) i σ $$ Hσat
    (try simp only [Hb2, _root_.and_self, ↓reduceIte])
    wp_apply wp_load_slice_index clsl (sint.Z n) _ _ cj Hb2.1 $$ [Hclsl] as -
    · iframe #; ipureintro; rw [hnz]; exact Hcj_lookup
    (try wp_auto)
    (try simp only [Hb3, _root_.and_self, ↓reduceIte])
    wp_apply wp_load_slice_index idsl (sint.Z n) _ _ idj Hb3.1 $$ [Hidsl] as -
    · iframe #; ipureintro; rw [hnz]; exact Hidj_lookup
    (try wp_auto)
    -- `gone(clis[j], ids[j])`
    wp_apply (wp_gone cj aj Vj Γ midj i idj hAs hlm hinj) $$ [$Hlt] as %b ⟨Hlt, Hb⟩
    · iframe #
    cases b
    · (try wp_auto)
      wp_for_post
      iframe
      iexists n + W64 1, n, k
      iframe
      ipureintro; constructor <;> word
    isimp only [↓reduceIte] at Hb
    iunfold lease.leaseAbsentFrom at Hb
    icases Hb with ⟨%ka, %ρa, %Hρa, #Hρat⟩
    ihave #Hlbk := lease.lessorAt_lb (Γ.ls midj) ka ρa $$ Hρat
    (try wp_auto)
    -- `ls, err := leaseList(clis[j])`, at the absence's index
    (try simp only [Hb2, _root_.and_self, ↓reduceIte])
    wp_apply wp_load_slice_index clsl (sint.Z n) _ _ cj Hb2.1 $$ [Hclsl] as -
    · iframe #; ipureintro; rw [hnz]; exact Hcj_lookup
    (try wp_auto)
    wp_apply (wp_leaseList cj aj Vj Γ midj ka hAs hlm hinj) $$ [$Hlt] as %ls %lerr ⟨Hlt, Hls⟩
    · iframe #
    icases Hls with (⟨%Hlerr, %ids, %sl, %jj, #Hslf, Hsl, %Hkj, #Hids⟩ | %Hlfail)
    rotate_left
    · obtain ⟨Hlerr, -⟩ := Hlfail
      cases lerr with
      | nil => exact absurd rfl Hlerr
      | ok ei => ?_
      (try wp_auto)
      wp_for_post
      iframe
      iexists n + W64 1, n, k
      iframe
      ipureintro; constructor <;> word
    subst Hlerr
    -- a later credit for the slot's law (an invariant whose published law is not timeless)
    wp_pure_lc Hlc
    imod ownSlice_persist _ _ _ $$ Hsl with #Hsl
    (try wp_auto)
    -- the listing is a snapshot where the lease is still absent
    iunfold lease.leaseIdsAt at Hids
    icases Hids with ⟨%τ, %Hτ, #Hτat⟩
    iunfold memberCli at Hmcj
    icases Hmcj with ⟨-, -, -, #Hslotj⟩
    imod lessorAbsentStays_dist.law_holds (GF := GF) (hG := hG) Γ midj i ka jj σ ρa τ idj Hσ Hρa.1 Hρa.2 Hkj $$ [Hlc Hslotj Hσat Hρat Hτat] with %Hτn
    · iframe Hlc Hslotj Hσat Hρat Hτat
    have Hnot : idj ∉ ids := by
      intro h
      have := (Hτ.2 idj).1 h
      rw [Hτn] at this
      simp at this
    (try simp only [Hb3, _root_.and_self, ↓reduceIte])
    wp_apply wp_load_slice_index idsl (sint.Z n) _ _ idj Hb3.1 $$ [Hidsl] as -
    · iframe #; ipureintro; rw [hnz]; exact Hidj_lookup
    (try wp_auto)
    wp_apply (wp_listed ls sl ids idj) $$ []
    · iframe #
    rw [decide_eq_false Hnot]
    (try wp_auto)
    wp_for_post
    iframe
    iexists n + W64 1, n, k + W64 1
    iframe
    ipureintro; constructor <;> word
  -- after the checks
  (try wp_auto)
  by_cases hk : k = W64 0
  · subst hk
    (try simp only [_root_.decide_true, ↓reduceIte])
    (try wp_auto)
    wp_apply wp_ended as %r -
    (try wp_auto)
    wp_apply Hdv
    (try wp_auto)
    iapply HΦ; iframe Hlt
  (try simp only [hk, decide_false, ↓reduceIte])
  (try wp_auto)
  wp_apply wp_checked as %r -
  (try wp_auto)
  wp_apply Hdv
  (try wp_auto)
  iapply HΦ; iframe Hlt

end proof

end etcd_dist_client
end EtcdGrove
end Perennial

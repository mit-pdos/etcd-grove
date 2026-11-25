/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/leaseN/run.lean` (`notes/leaseN-plan.md`,
2026-11-16). Lean-first (no Rocq counterpart).

- The serve loop (authN's, at auth off): each member served (`etcdstart.Serve` with the ghost step
  `etcdstart.kv_lease_served_go` at the lease mode `none`: etcd's lease reads registered at its client
  address, the member's `GoAttach` resources and with them the thread token given back, passed on to
  the next member); the served members' registrations accumulate as a persistent big-sep.
- The check loop: at each member, `check` with the member's registrations (the client's watch
  environment `check`'s spec takes: any, one is built from a served member's watch server).
Every error returns `Failed` (`1`); the end `Checked` (`0`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.leaseN.run
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.leaseN.check
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Serve
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Served
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.ServedLease
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.ServedLeaseLinked

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_leaseN

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver etcdstart

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.leaseN.Assumptions]

set_option maxHeartbeats 3200000 in
/-- See the file header. -/
theorem run.wp_proof
    (wp_Serve : etcdstart.Serve.spec (GF := GF) (hG := hG))
    (wp_check : check.spec (GF := GF) (hG := hG)) :
    run.spec (GF := GF) (hG := hG) := by
  intro CS srvsl msl lg ss xs γn Hpe Hlm Htb HLv Hrb48 Hbuq Hrf Hlp Hms hAs
  wp_start as ⟨#Hlgz, Hss, #Hmsl, Htok, Hcfree, Hups⟩
  ihave #Psrv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver $$ []
  · iPkgInit
  ihave #Pv3 : isPkgInit (PROP := IProp GF)
      pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc $$ []
  · iPkgInit
  ihave #Pst : isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart $$ []
  · iPkgInit
  ihave %Hupl := BigSepL2.bigSepL2_length $$ Hups
  ihave %Hssl := ownSlice_len $$ Hss
  ihave %Hmsll := ownSlice_len $$ Hmsl
  imod ownSlice_persist _ _ _ $$ Hss with #Hss
  (try wp_auto)
  -- the serve loop: `for j, m := range ms { if err := Serve(srvs[j], m.Client); err != nil { return
  -- Failed } }`, the thread token from member to member
  ihave IH : (∃ (n jv : w64) (mv : GMember),
      "i" ∷ i_ptr ↦ n ∗ "j" ∷ j_ptr ↦ jv ∗ "m" ∷ m_ptr ↦ mv ∗ "Htok" ∷ threadTok ∗
      "Hups" ∷ ([∗list] s; x ∈ ss.drop (sint.nat n); xs.drop (sint.nat n),
        (threadTok -∗ memberUp s x.2.ρ x.2.E lg γn x.2.id .none)) ∗
      "Hcfree" ∷ ([∗list] x ∈ xs.drop (sint.nat n), netAddrFree (GF := GF) x.1.Client') ∗
      "#Hsv" ∷ ([∗list] x ∈ xs.take (sint.nat n), client.etcdLeaseReadAt (GF := GF) x.1.Client') ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.nat n ≤ xs.length ∧
        (sint.nat n = 0 ∨ Nonempty (client.WEnv GF))⌝ : IProp GF)
      $$ [i j m Htok Hups Hcfree]
  · iexists W64 0, _, _
    have h00 : sint.nat (W64 0) = 0 := rfl
    simp only [h00, List.drop_zero, List.take_zero]
    iframe
    isplitl
    · iapply BigSepL.bigSepL_nil.2; itrivial
    ipureintro; exact ⟨by decide, by omega, Or.inl trivial⟩
  wp_for IH
  wp_if_destruct
  · have hlt : sint.nat n < xs.length := by have := Hmsll.1; simp at this; word
    list_elem ss (sint.nat n) as sj
    list_elem xs (sint.nat n) as xj
    have hnz : (sint.Z n).toNat = sint.nat n := by word
    have Hbm : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z msl.len := ⟨Hn.1, Hif⟩
    have Hbs : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z srvsl.len := ⟨Hn.1, by have := Hssl.1; word⟩
    (try wp_auto)
    simp only [Hbm, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index msl (sint.Z n) _ _ xj.1 Hbm.1 $$ [Hmsl] as -
    · iframe #; ipureintro; rw [hnz, List.getElem?_map, Hxj_lookup]; rfl
    (try wp_auto)
    simp only [Hbs, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index srvsl (sint.Z n) _ _ sj Hbs.1 $$ [Hss] as -
    · iframe #; ipureintro; rw [hnz]; exact Hsj_lookup
    (try wp_auto)
    -- the member's `memberUp`, the token given to it
    isimp only [drop_cons_of_getElem? ss _ sj Hsj_lookup, drop_cons_of_getElem? xs _ xj Hxj_lookup] at Hups
    ihave Hups := BigSepL2.bigSepL2_cons.1 $$ Hups
    icases Hups with ⟨Hupj, Hups⟩
    ihave Hupj := Hupj $$ Htok
    isimp only [drop_cons_of_getElem? xs _ xj Hxj_lookup] at Hcfree
    ihave Hcfree := BigSepL.bigSepL_cons.1 $$ Hcfree
    icases Hcfree with ⟨Hcj, Hcfree⟩
    have hxj : xj ∈ xs := List.mem_of_getElem? Hxj_lookup
    icases etcdstart.memberUp_served _ _ _ _ _ _ _ $$ Hupj with ⟨%E, %cfg, %γw, %HEc, #Hreq, #Hrd,
      #Hsf, Hgo, Hlg3, Hbemu, #Hwb, Hstk, -, #HLR⟩
    obtain ⟨HEa, HEo, HElg, HEtr, HEw⟩ := HEc
    -- `Serve(srvs[j], m.Client)`, with etcd's lease reads registered at the address
    haveI := Hms
    ihave ⟨%HsvOff, #HreqM, #HrdM, #Hlb⟩ := etcdstart.serveViews_off sj E { xj.2.ρ with wait := γw }
      xj.2.ρ.rd $$ []
    · iframe #
    ihave #HzlgC : zapLoggerOk cfg.Logger' $$ []
    · rw [HElg]; iexact Hlgz
    wp_apply (wp_Serve sj xj.1.Client' E { xj.2.ρ with wait := γw } xj.2.ρ.rd cfg
        (fun _ _ _ => iprop(client.etcdLeaseReadAt (GF := GF) xj.1.Client' ∗ srvGoRes sj ∗
          ⌜Nonempty (client.WEnv GF)⌝)))
      $$ [Hcj Hlg3 Hbemu Hgo Hstk] as %serr Hs
    · iframe; iframe #
      isplitr
      · ipureintro; exact ⟨HEtr, HEw, Hms, Hbuq, HsvOff.2, Htb⟩
      iintro %gs' %lis %cid %mid %R Hg
      rw [HsvOff.1]
      ihave Hg := etcdstart.grpcUpM_false _ _ _ _ _ _ _ _ _ _ $$ Hg
      imod (etcdstart.kv_lease_served_go sj E { xj.2.ρ with wait := γw } xj.2.ρ.rd gs' lis
        xj.1.Client' cid mid R Hrb48 (by omega) Hrf Hlp rfl .none (Hlm xj hxj) HLv)
        $$ [Hg Hstk] with ⟨Htk, Hgo', #Hlr, -⟩
      · iframe; iframe #
      imodintro
      iframe Htk Hgo'
      iframe #
      ipureintro
      exact ⟨EtcdGrove.client.srvWEnv R (etcdstart.srvWOf R.E xj.2.ρ.rd false) xj.2.ρ.rd
        xj.1.Client' [] null null [] null default⟩
    icases Hs with (%Hserr | ⟨%Hserr, %cid, %mid, %R, #Hlr, Hgr, %HVne⟩)
    · cases serr with
      | nil => exact absurd rfl Hserr
      | ok ei => ?_
      (try wp_auto)
      wp_for_post
      iapply HΦ; ipureintro; right; rfl
    subst Hserr
    (try wp_auto)
    iunfold srvGoRes at Hgr
    icases Hgr with ⟨-, Htok⟩
    ihave #Hsv' : [∗list] x ∈ xs.take (sint.nat n + 1), client.etcdLeaseReadAt (GF := GF) x.1.Client'
      $$ []
    · rw [List.take_add_one, Hxj_lookup, Option.toList_some]
      iapply BigSepL.bigSepL_snoc.2
      iframe #
    iclear Hsv
    wp_for_post
    iframe
    have hn1 : sint.nat (n + W64 1) = sint.nat n + 1 := by word
    iexists n + W64 1, n, xj.1
    rw [hn1]
    iframe
    iframe #
    ipureintro; exact ⟨by word, by omega, Or.inr HVne⟩
  -- every member served
  have hnk : sint.nat n = xs.length := by have := Hmsll.1; simp at this; word
  ihave #Hsv : [∗list] x ∈ xs, client.etcdLeaseReadAt (GF := GF) x.1.Client' $$ []
  · iExactEq Hsv; rw [hnk, List.take_of_length_le (Nat.le_refl _)]
  have hVne : xs.length = 0 ∨ Nonempty (client.WEnv GF) := by rw [← hnk]; exact Hn.2.2
  iclear Hups Hcfree
  (try wp_auto)
  -- the check loop: `for _, m := range ms { if !check(m.Client, lg) { return Failed } }`
  icases (threadTok_level0 (GF := GF)).1 $$ Htok with ⟨Hlt, -⟩
  ihave IB : (∃ (n : w64) (mv : GMember),
      "i" ∷ i_ptr ↦ n ∗ "m" ∷ m_ptr ↦ mv ∗ "Hlt" ∷ levelTok 0 ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.nat n ≤ xs.length⌝ : IProp GF) $$ [i m Hlt]
  · iexists W64 0, _
    iframe
    ipureintro; exact ⟨by decide, by simp⟩
  wp_for IB
  wp_if_destruct
  · have hlt : sint.nat n < xs.length := by have := Hmsll.1; simp at this; word
    list_elem xs (sint.nat n) as xj
    have hxj : xj ∈ xs := List.mem_of_getElem? Hxj_lookup
    have hnz : (sint.Z n).toNat = sint.nat n := by word
    have Hbm : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z msl.len := ⟨Hn.1, Hif⟩
    (try wp_auto)
    simp only [Hbm, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index msl (sint.Z n) _ _ xj.1 Hbm.1 $$ [Hmsl] as -
    · iframe #; ipureintro; rw [hnz, List.getElem?_map, Hxj_lookup]; rfl
    (try wp_auto)
    ihave #Hlrj := BigSepL.bigSepL_lookup Hxj_lookup $$ Hsv
    have hne : Nonempty (client.WEnv GF) := hVne.resolve_left (by omega)
    wp_apply (wp_check xj.1.Client' lg (Classical.choice hne) (Hpe xj hxj) (by omega) hAs) $$ [$Hlt]
      as %b ⟨Hlt, -⟩
    · iframe #
    (try wp_auto)
    cases b
    · (try wp_auto)
      wp_for_post
      iapply HΦ; ipureintro; right; rfl
    (try wp_auto)
    wp_for_post
    iframe
    iexists n + W64 1, xj.1
    iframe
    ipureintro; constructor <;> word
  (try wp_auto)
  iapply HΦ; ipureintro; left; rfl

end proof

end etcd_leaseN
end EtcdGrove
end Perennial

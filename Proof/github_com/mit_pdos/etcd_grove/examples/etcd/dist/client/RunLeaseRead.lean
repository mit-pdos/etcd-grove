/-
Proof of `RunLeaseRead.spec` (the loop of leaseN's `run`, `Proof/.../examples/etcd/leaseN/run.lean`, without
its members' serving): `leaseReadCheck` at every endpoint in turn, counting those that answered; `ended` if
none did, `checked` otherwise.
Lean-first (no Rocq counterpart); #50 N9b (`notes/etcd-dist-n9b.md`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.RunLeaseRead
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.leaseReadCheck
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.checked
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.ended
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

set_option maxHeartbeats 800000 in
/-- See the file header. -/
theorem RunLeaseRead.wp_proof (svc : DistView → w64 → GrpcSvc GF)
    (wp_leaseReadCheck : leaseReadCheck.spec (GF := GF) (hG := hG) svc)
    (wp_checked : checked.spec (GF := GF) (hG := hG))
    (wp_ended : ended.spec (GF := GF) (hG := hG)) :
    RunLeaseRead.spec (GF := GF) (hG := hG) svc := by
  intro π Γ eps addrs hV Htb hAs
  wp_start as ⟨Hlt, #Heps, #Hms⟩
  ihave %Hlen := ownSlice_len $$ Heps
  (try wp_auto)
  -- `for _, a := range eps { if leaseReadCheck(a) { n++ } }`
  ihave IB : (∃ (j k : w64) (av : GoString),
      "i" ∷ i_ptr ↦ j ∗ "n" ∷ n_ptr ↦ k ∗ "a" ∷ a_ptr ↦ av ∗ "Hlt" ∷ levelTok 0 ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.nat j ≤ addrs.length ∧ 0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z j⌝ :
      IProp GF) $$ [i n a Hlt]
  · iexists W64 0, W64 0, _
    simp only [named]
    iframe
    ipureintro; refine ⟨by decide, by simp, by decide, by decide⟩
  wp_for IB
  wp_if_destruct
  · have hlt : sint.nat j < addrs.length := by word
    obtain ⟨x, hx⟩ : ∃ x, addrs[sint.nat j]? = some x := ⟨_, List.getElem?_eq_getElem hlt⟩
    have Hbm : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z eps.len := ⟨Hj.1, Hif⟩
    (try wp_auto)
    (try simp only [Hbm, _root_.and_self, ↓reduceIte])
    wp_apply wp_load_slice_index eps (sint.Z j) _ _ x Hbm.1 $$ [Heps] as -
    · iframe #; ipureintro; rw [show (sint.Z j).toNat = sint.nat j by word]; exact hx
    (try wp_auto)
    ihave #Hmx := BigSepL.bigSepL_lookup hx $$ Hms
    wp_apply (wp_leaseReadCheck Γ x hV Htb hAs) $$ [$Hlt] as %b Hlt
    · iframe #
    (try wp_auto)
    cases b
    · (try wp_auto)
      wp_for_post
      iframe
      iexists j + W64 1, k, x
      simp only [named]
      iframe
      ipureintro; refine ⟨by word, by word, Hj.2.2.1, by word⟩
    (try wp_auto)
    wp_for_post
    iframe
    iexists j + W64 1, k + W64 1, x
    simp only [named]
    iframe
    ipureintro; refine ⟨by word, by word, by word, by word⟩
  (try wp_auto)
  wp_if_destruct
  · wp_apply wp_ended as %r -
    (try wp_auto)
    iapply HΦ; iframe Hlt
  wp_apply wp_checked as %r -
  (try wp_auto)
  iapply HΦ; iframe Hlt

end proof

end etcd_dist_client
end EtcdGrove
end Perennial

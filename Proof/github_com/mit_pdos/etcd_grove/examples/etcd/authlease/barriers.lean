/-
Proof of `Spec/.../authlease/barriers.lean` (auth-lease S4, item 9). Lean-first (no Rocq counterpart).
The loop `for _, m := range ms { if !barrier(m.Client, lg) { return false } }; return true`, with the
successes of the members so far (`barrierPost` over `bs.take j`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.authlease.barriers
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.authlease.barrier
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_authlease

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver client etcd_auth

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.authlease.Assumptions]

theorem barriers.wp_proof (wp_barrier : barrier.spec (GF := GF) (hG := hG)) :
    barriers.spec (GF := GF) (hG := hG) := by
  intro CS ES FS RS CRE CEC msl lg ms bs hms htb hAs
  wp_start as ⟨Hlt, #Hlg, #Hmsl, #Hbs⟩
  ihave %Hmsll := ownSlice_len $$ Hmsl
  have hlen : ms.length = bs.length := by
    have := congrArg List.length hms; simpa using this
  (try wp_auto)
  ihave IB : (∃ (j : w64) (mv : etcdstart.GMember),
      "i" ∷ i_ptr ↦ j ∗ "m" ∷ m_ptr ↦ mv ∗ "Hlt" ∷ levelTok 0 ∗
      "#Hok" ∷ ([∗list] b ∈ bs.take (sint.nat j), barrierPost b) ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.nat j ≤ ms.length⌝ : IProp GF) $$ [i m Hlt]
  · iexists W64 0, _
    have h00 : sint.nat (W64 0) = 0 := rfl
    simp only [h00, List.take_zero]
    iframe
    isplitl
    · iapply BigSepL.bigSepL_nil.2; itrivial
    ipureintro; exact ⟨by decide, by omega⟩
  wp_for IB
  wp_if_destruct
  · have hlt : sint.nat j < ms.length := by have := Hmsll.1; word
    list_elem ms (sint.nat j) as mj
    have hbl : sint.nat j < bs.length := by omega
    list_elem bs (sint.nat j) as bj
    have haddr : mj.Client' = bj.addr := by
      have h := congrArg (fun l => l[sint.nat j]?) hms
      simp only [List.getElem?_map, Hmj_lookup, Hbj_lookup, Option.map_some, Option.some.injEq] at h
      exact h
    have hnz : (sint.Z j).toNat = sint.nat j := by word
    have Hbm : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z msl.len := ⟨Hj.1, Hif⟩
    (try wp_auto)
    simp only [Hbm, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index msl (sint.Z j) _ _ mj Hbm.1 $$ [Hmsl] as -
    · iframe #; ipureintro; rw [hnz]; exact Hmj_lookup
    (try wp_auto)
    ihave #Hpre := BigSepL.bigSepL_lookup Hbj_lookup $$ Hbs
    iunfold barrierPre at Hpre
    icases Hpre with ⟨%Hpe, #HAu, #HKV, #Hrd, #Hfz, #HLs, %Hh, #HLc, %HLcst, #HQ⟩
    rw [haddr]
    wp_apply (wp_barrier bj.addr lg bj.V bj.s bj.E bj.ρ bj.cid bj.mid bj.γa bj.γz bj.hs bj.Lset bj.Lc bj.r
        bj.Q Hpe.1 htb Hpe.2 hAs) $$ [$Hlt] as %okj ⟨Hlt, Hbj⟩
    · iframe #; ipureintro; exact ⟨Hh, HLcst⟩
    icases Hbj with (%Hb | ⟨%Hb, #Hfix, #Hfloor⟩) <;> subst Hb
    · (try wp_auto)
      wp_for_post
      iapply HΦ; iframe Hlt; ileft; ipureintro; rfl
    (try wp_auto)
    have htk : bs.take (sint.nat j + 1) = bs.take (sint.nat j) ++ [bj] := by
      rw [List.take_add_one, Hbj_lookup, Option.toList_some]
    ihave #Hok' : [∗list] b ∈ bs.take (sint.nat j + 1), barrierPost b $$ []
    · rw [htk]
      iapply BigSepL.bigSepL_snoc.2
      iframe #
      iunfold barrierPost
      iframe #
    iclear Hok
    wp_for_post
    iframe
    have hn1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
    iexists j + W64 1, mj
    rw [hn1]
    iframe
    iframe #
    ipureintro; exact ⟨by word, by omega⟩
  · have hnk' : sint.nat j = bs.length := by have := Hmsll.1; word
    (try wp_auto)
    iapply HΦ
    iframe Hlt
    iright
    isplitl []
    · ipureintro; rfl
    iExactEq Hok; rw [hnk', List.take_of_length_le (by omega)]

end proof

end etcd_authlease
end EtcdGrove
end Perennial

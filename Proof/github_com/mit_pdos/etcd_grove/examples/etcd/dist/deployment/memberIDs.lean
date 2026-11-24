/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/deployment/memberIDs.lean`. Lean-first.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.memberIDs
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.NewMember
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.AddrPlain

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.etcd.dist

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : deployment.Assumptions]

/-- A valid address's `url.URL{Scheme: "http", Host: a}` is plain (`url.URL.String` writes `http://a`). -/
theorem urlHttp_plain (a : GoString) (h : Net.addrOk a = true) :
    http.urlRootPlain (membership.urlHttp a) := by
  obtain ⟨hne, hb⟩ := types.plainHostPort_noEscape a (addrOk_plainHostPort h)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hne, hb⟩ <;>
    first | rfl | (refine Eq.trans (rfl : _ = ([] : GoString)) ?_; simp [stringToGoString])

theorem deployment.memberIDs.wp_proof [go_etcd_io.etcd.server.v3.etcdserver.api.membership.Assumptions]
    (hNew : EtcdGrove.membership.NewMember.spec (GF := GF) (hG := hG)) :
    etcd_dist.deployment.memberIDs.spec (GF := GF) (hG := hG) := by
  intro v d hfips
  wp_start as #Hd
  wp_auto
  iunfold deploymentRepr at Hd
  icases Hd with ⟨#Hm, %htok, %hcfg, #Hw, %ss, #Hn, #Hns⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hm
  rw [List.length_map] at Hlen
  ihave HI : (∃ (k : Nat) (mv : deployment.Member) (isl : GoSlice) (xs : List w64),
      "i" ∷ i_ptr ↦ W64 k ∗ "m" ∷ m_ptr ↦ mv ∗ "ids" ∷ ids_ptr ↦ isl ∗ "Hids" ∷ isl ↦* xs ∗
      "Hcap" ∷ ownSliceCap w64 isl (DFrac.own 1) ∗
      "%Hk" ∷ ⌜k ≤ d.members.length ∧ ((∀ m ∈ d.members, Net.addrOk m.peer = true) →
        xs = (d.members.take k).map (fun m => memberId (go!"http://" ++ m.peer) d.token))⌝ : IProp GF)
    $$ [i m ids]
  · iexists 0, _, slice.nil, []
    iframe
    isplitl []
    · iapply ownSlice_nil
    isplitl []
    · iapply ownSliceCap_nil
    ipureintro
    exact ⟨by omega, fun _ => by simp⟩
  wp_for HI
  obtain ⟨Hk1, Hk2⟩ := Hk
  wp_if_destruct
  · have hk : k < d.members.length := by word
    have hc : sint.Z (W64 (k : Int)) < sint.Z v.Members'.len := by word
    have h0 : 0 ≤ sint.Z (W64 (k : Int)) := by word
    simp only [h0, hc, and_self, ↓reduceIte]
    have hsk : (sint.Z (W64 (k : Int))).toNat = k := by word
    obtain ⟨mm, hmm⟩ : ∃ mm, d.members[k]? = some mm := ⟨_, List.getElem?_eq_getElem hk⟩
    wp_apply (wp_load_slice_index v.Members' (sint.Z (W64 (k : Int))) (d.members.map Member.val) DFrac.discard mm.val h0) $$ [] as -
    · iframe #; ipureintro; rw [hsk, List.getElem?_map, hmm]; rfl
    wp_apply wp_slice_literal (V := _root_.Perennial.net.url.URL) [membership.urlHttp mm.peer]
    isplitr
    · ipureintro; rfl
    iintro %usl ⟨Husl, -⟩
    imod ownSlice_persist _ _ _ $$ Husl with #Husl
    wp_auto
    rw [htok]
    wp_apply (hNew mm.name _ mm.peer d.token hfips) $$ [] as %mp %mvv ⟨Hmp, %Hid⟩
    · iframe #
    wp_apply wp_slice_literal (V := w64) [mvv.ID']
    isplitr
    · ipureintro; rfl
    iintro %isl1 ⟨Hisl1, -⟩
    wp_apply (wp_slice_append isl xs _ [mvv.ID'] (DFrac.own 1)) $$ [Hids Hcap Hisl1] as %isl2 ⟨Hids, Hcap, -⟩
    · iframe
    have hwk : W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) := by word
    wp_for_post
    iframe
    iexists (k + 1), _, isl2, xs ++ [mvv.ID']
    rw [hwk]
    iframe
    ipureintro
    refine ⟨by omega, fun hall => ?_⟩
    rw [Hk2 hall, List.take_add_one, hmm, Option.toList_some, List.map_append]
    congr 1
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
    have hp := hall mm (List.mem_of_getElem? hmm)
    exact Hid (urlHttp_plain _ hp)
  · have hkl : k = d.members.length := by word
    subst hkl
    rw [List.take_length] at Hk2
    iapply HΦ
    iframe
    ipureintro
    exact Hk2

end proof

end etcd_dist
end EtcdGrove
end Perennial

/-
The proof of `KvNet/Spec/.../kvnet/RunNode.lean`: `SplitAddrs`, `ValidCluster` (true by the
premise: no panic), the address map built by a loop (entry `i+1` the `i`-th address; the keys
distinct below `2^32` replicas), made read-only, then `Run`.
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.RunNode
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.SplitAddrs
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.ValidCluster
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Run

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI Iris.ProofMode Net go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NetProtoGS] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]
variable [package_sem' : net.Assumptions] [field_sem : net.FieldAssumptions]

theorem RunNode.wp_proof (F : KvFacts GF) (rep : Loc → w64 → IProp GF)
    (cf : GoInterface → List w8 → IProp GF) (S : IProp GF)
    (wp_SplitAddrs : SplitAddrs.spec (GF := GF) (hG := hG))
    (wp_ValidCluster : ValidCluster.spec (GF := GF) (hG := hG))
    (wp_Run : Run.spec (GF := GF) (hG := hG) F rep cf S) :
    RunNode.spec (GF := GF) (hG := hG) F rep cf S := by
  intro id addrs dir voters pv cq sd msz mcs mif eof ed Hvalid Hid1 Hid2
  wp_start as ⟨Hpr, HS, #Heof, #Hed, #Hcc⟩
  try wp_auto
  wp_apply wp_SplitAddrs addrs $$ [$Hpkg] as %sl ⟨Hsl, Hcap⟩
  try wp_auto
  have Hv := Hvalid
  simp only [validCluster, validAddrs, Bool.and_eq_true, decide_eq_true_eq] at Hv
  obtain ⟨⟨⟨⟨Hok, Hnd, Hlen32, Hv1, Hv2⟩, Hv3⟩, Hv4⟩, Hv5⟩ := Hv
  have Hl63 : ∀ a ∈ splitAddrs addrs, a.length + 1 < 2 ^ 63 := fun a ha => by
    have := addrOk_length (Hok a ha); omega
  ihave %Hsll := ownSlice_len $$ Hsl
  wp_apply wp_ValidCluster sl (DFrac.own 1) (splitAddrs addrs) voters msz mcs mif Hl63
    $$ [$Hpkg $Hsl] as Hsl
  rw [Hvalid]
  try wp_auto
  rw [decide_eq_false (show ¬ uint.Z id < uint.Z (W64 1) by word)]
  try wp_auto
  rw [decide_eq_false (show ¬ uint.Z sl.len < uint.Z id by have := Hsll.1; have := Hsll.2; word)]
  try wp_auto
  wp_apply (wp_map_make1 (K := w64) (V := GoString) go.uint64 go.string) as %mref Hm
  try wp_auto
  rename_i iu_ptr
  irename : iu_ptr ↦ (zero_val w64) => Hiu
  ihave IH : iprop(∃ (k iv : w64) (av : GoString) (M : GMap w64 GoString),
      "i" ∷ i_ptr ↦ k ∗ "Hiu" ∷ iu_ptr ↦ iv ∗ "a" ∷ a_ptr ↦ av ∗ "Hm" ∷ mref ↦$ M ∗
      "Hsl" ∷ sl ↦* splitAddrs addrs ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ ((splitAddrs addrs).length : Int) ∧
        ∀ j : Nat, j < sint.nat k → M !! W64 (j + 1) = (splitAddrs addrs)[j]?⌝) $$ [i Hiu a Hm Hsl]
  · iexists W64 0, W64 0, _, ∅
    iframe
    ipureintro
    refine ⟨by decide, by word, ?_⟩
    intro j hj; rw [show sint.nat (W64 0) = 0 from rfl] at hj; omega
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat k < (splitAddrs addrs).length := by word
    obtain ⟨x, Hx⟩ : ∃ x, (splitAddrs addrs)[sint.nat k]? = some x :=
      ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hbnd' : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z sl.len := ⟨Hk.1, by word⟩
    simp only [Hbnd', _root_.and_self]
    wp_apply wp_load_slice_index sl (sint.Z k) _ (DFrac.own 1) x Hk.1 $$ [Hsl] as Hsl
    · iframe Hsl; ipureintro; exact Hx
    try wp_auto
    wp_apply (wp_mapInsert (K := w64) (V := GoString) go.uint64 mref M (k + W64 1) x) $$ Hm as Hm
    try wp_auto
    wp_for_post
    iframe
    iexists k + W64 1, k, x, <[k + W64 1 := x]> M
    iframe
    ipureintro
    have Hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by word
    refine ⟨by word, by word, ?_⟩
    intro j hj
    rw [Hk1] at hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
    · rw [GMap.lookup_insert_ne _ _ (by intro h; have := congrArg uint.nat h; word)]
      exact Hk.2.2 j hj
    · subst hj
      rw [show W64 (↑(sint.nat k) + 1) = k + W64 1 by word, GMap.lookup_insert, Hx]
  · have Hkl : sint.nat k = (splitAddrs addrs).length := by
      have := Hk.2.1; have := Hsll.1; have := Hsll.2; word
    imod ownMap_persist mref _ _ $$ Hm with #Hm
    obtain ⟨a, Ha⟩ : ∃ a, (splitAddrs addrs)[uint.nat id - 1]? = some a :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have HMa : M !! id = some a := by
      have H := Hk.2.2 (uint.nat id - 1) (by omega)
      rw [show W64 (↑(uint.nat id - 1) + 1) = id by word] at H
      rw [H, Ha]
    ihave #Hap := Hpr $$ %a %Ha
    try wp_auto
    wp_apply wp_Run (⟨id, dir, mref, ⟨voters, pv, cq, sd, msz, mcs, mif⟩⟩ :
        github_com.mit_pdos.etcd_grove.examples.raft.kvnet.NodeConfig) M a eof ed HMa
      $$ [$Hpkg $Hm $Hap $HS $Heof $Hed $Hcc]
    try wp_auto
    iapply HΦ
    itrivial

end proof

end raft_kvnet
end EtcdGrove
end Perennial

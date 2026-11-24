/-
The proof of `KvNet/Spec/.../kvnet/RunNode.lean`: `SplitAddrs`, `ValidCluster` and the rest of the
check (a configuration it fails returns at once; one it passes gives the resources), the address map built by a loop (entry `i+1` the `i`-th address; the keys
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
    (cf : GoInterface → List w8 → IProp GF)
    (S : w64 → GoString → github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Options → GMap w64 GoString → IProp GF)
    (wp_SplitAddrs : SplitAddrs.spec (GF := GF) (hG := hG))
    (wp_ValidCluster : ValidCluster.spec (GF := GF) (hG := hG))
    (wp_Run : Run.spec (GF := GF) (hG := hG) F rep cf S) :
    RunNode.spec (GF := GF) (hG := hG) F rep cf S := by
  intro id addrs dir voters pv cq sd msz mcs mif eof ed
  wp_start as ⟨Hres, #Heof, #Hed, #Hcc⟩
  try wp_auto
  wp_apply wp_SplitAddrs addrs $$ [$Hpkg] as %sl ⟨Hsl, Hcap⟩
  try wp_auto
  ihave %Hsll := ownSlice_len $$ Hsl
  wp_apply wp_ValidCluster sl (DFrac.own 1) (splitAddrs addrs) voters msz mcs mif
    $$ [$Hpkg $Hsl] as Hsl
  -- the check: a configuration `RunNode` cannot run returns at once
  cases Hvalid : validCluster (splitAddrs addrs) (uint.nat voters) (uint.nat msz) (uint.nat mcs)
    (uint.nat mif)
  · try wp_auto
    iapply HΦ
    itrivial
  try wp_auto
  wp_if_destruct
  · try wp_auto
    iapply HΦ
    itrivial
  try wp_auto
  wp_if_destruct
  · try wp_auto
    iapply HΦ
    itrivial
  try wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hd63
  try wp_auto
  wp_if_destruct
  · try wp_auto
    iapply HΦ
    itrivial
  try wp_auto
  have Hid1 : 1 ≤ uint.nat id := by word
  have Hid2 : uint.nat id ≤ (splitAddrs addrs).length := by
    have := Hsll.1; have := Hsll.2; word
  have Hdir : dir.length < 2 ^ 39 := by word
  ihave ⟨Hpr, HS⟩ := Hres $$ %⟨Hvalid, Hid1, Hid2, Hdir⟩
  have Hv := Hvalid
  simp only [validCluster, validAddrs, Bool.and_eq_true, decide_eq_true_eq] at Hv
  obtain ⟨⟨⟨⟨Hok, Hnd, Hlen32, Hv1, Hv2⟩, Hv3⟩, Hv4⟩, Hv5⟩ := Hv
  wp_apply (wp_map_make1 (K := w64) (V := GoString) go.uint64 go.string) as %mref Hm
  try wp_auto
  rename_i iu_ptr
  irename : iu_ptr ↦ (zero_val w64) => Hiu
  ihave IH : iprop(∃ (k iv : w64) (av : GoString) (M : GMap w64 GoString),
      "i" ∷ i_ptr ↦ k ∗ "Hiu" ∷ iu_ptr ↦ iv ∗ "a" ∷ a_ptr ↦ av ∗ "Hm" ∷ mref ↦$ M ∗
      "Hsl" ∷ sl ↦* splitAddrs addrs ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ ((splitAddrs addrs).length : Int) ∧
        ∀ i : w64, M !! i = if 1 ≤ uint.nat i ∧ uint.nat i ≤ sint.nat k then
          (splitAddrs addrs)[uint.nat i - 1]? else none⌝) $$ [i Hiu a Hm Hsl]
  · iexists W64 0, W64 0, _, ∅
    iframe
    ipureintro
    refine ⟨by decide, by word, ?_⟩
    intro i
    rw [GMap.lookup_empty, show sint.nat (W64 0) = 0 from rfl, if_neg (by omega)]
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
    intro i
    rw [Hk1]
    by_cases hi : i = k + W64 1
    · subst hi
      have h1 : uint.nat (k + W64 1) = sint.nat k + 1 := by word
      rw [GMap.lookup_insert, if_pos (by omega), h1, show sint.nat k + 1 - 1 = sint.nat k by omega, Hx]
    · have hne : uint.nat i ≠ sint.nat k + 1 := by intro h; apply hi; word
      rw [GMap.lookup_insert_ne _ _ (fun h => hi h.symm), Hk.2.2 i]
      by_cases h : 1 ≤ uint.nat i ∧ uint.nat i ≤ sint.nat k
      · rw [if_pos h, if_pos ⟨h.1, by omega⟩]
      · rw [if_neg h, if_neg (by omega)]
  · have Hkl : sint.nat k = (splitAddrs addrs).length := by
      have := Hk.2.1; have := Hsll.1; have := Hsll.2; word
    imod ownMap_persist mref _ _ $$ Hm with #Hm
    obtain ⟨a, Ha⟩ : ∃ a, (splitAddrs addrs)[uint.nat id - 1]? = some a :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have HMa : M !! id = some a := by
      rw [Hk.2.2 id, if_pos (by omega), Ha]
    have HMok : addrMapOk (splitAddrs addrs) M := by
      intro i
      rw [Hk.2.2 i]
      by_cases h1 : 1 ≤ uint.nat i
      · by_cases h2 : uint.nat i ≤ sint.nat k
        · rw [if_pos ⟨h1, h2⟩, if_pos h1]
        · rw [if_neg (fun h => h2 h.2), if_pos h1, List.getElem?_eq_none (by omega)]
      · rw [if_neg (fun h => h1 h.1), if_neg h1]
    ihave HS := HS $$ %M %HMok
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

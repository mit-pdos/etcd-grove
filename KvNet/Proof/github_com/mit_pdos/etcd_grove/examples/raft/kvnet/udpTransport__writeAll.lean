/-
The proof of `KvNet/Spec/.../kvnet/udpTransport__writeAll.lean` (kvudp, phase 2: `notes/kvudp-proof-plan.md`).
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.udpTransport__writeAll
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Stats__add
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.udpNet__write

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI Iris.ProofMode Net Udp go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [HasExt udpExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NetProtoGS] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]
variable [net_sem : net.Assumptions] [net_udp_sem : net.UdpFieldAssumptions]

theorem udpTransport.writeAll.wp_proof
    (wp_write : udpNet.write.spec (GF := GF) (hG := hG))
    (wp_add : Stats.add.spec (GF := GF) (hG := hG)) :
    udpTransport.writeAll.spec (GF := GF) (hG := hG) := by
  intro F γu t id sc γsc to dsl q ds
  wp_start as ⟨#Ht, Hdsl, #Hds⟩
  iunfold isUdpBase at Ht
  icases Ht with ⟨%u, %boot, %sp, #Hu, #Hun, #Hstats, #Hs, #Hsc, -, -⟩
  try wp_auto
  ihave %Hdslen := ownSlice_len $$ Hdsl
  ihave IH : iprop(∃ (k : w64) (dv : GoSlice),
      "i" ∷ i_ptr ↦ k ∗ "d" ∷ d_ptr ↦ dv ∗ "Hdsl" ∷ dsl ↦*{q} ds ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ (ds.length : Int)⌝) $$ [i d Hdsl]
  · iexists W64 0, _
    iframe i d Hdsl
    ipureintro; constructor <;> word
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat k < ds.length := by word
    obtain ⟨dd, Hq⟩ : ∃ dd, ds[sint.nat k]? = some dd := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hbnd' : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z dsl.len := ⟨Hk.1, by word⟩
    simp only [Hbnd', and_self]
    wp_apply wp_load_slice_index dsl (sint.Z k) _ q dd Hk.1 $$ [Hdsl] as Hdsl
    · iframe Hdsl; ipureintro; exact Hq
    have Hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by word
    iunfold udpDgsOk at Hds
    icases BigSepL.bigSepL_lookup Hq $$ Hds with ⟨%bs, #Hdd, #Hok⟩
    try wp_auto
    wp_apply wp_write F γu u id boot to dd bs $$ [$Hpkg $Hun $Hdd $Hok] as %ok -
    try wp_auto
    cases ok
    · try wp_auto
      wp_apply wp_add sp (W64 32) (by decide) (by decide) $$ [$Hpkg $Hs]
      try wp_auto
      wp_for_post
      try wp_auto
      iapply HΦ
      iexact Hdsl
    · try wp_auto
      wp_apply wp_add sp (W64 24) (by decide) (by decide) $$ [$Hpkg $Hs]
      try wp_auto
      wp_for_post
      iframe
      iexists k + W64 1, dd
      iframe
      ipureintro; constructor <;> word
  · try wp_auto
    iapply HΦ
    iexact Hdsl

end proof

end raft_kvnet
end EtcdGrove
end Perennial

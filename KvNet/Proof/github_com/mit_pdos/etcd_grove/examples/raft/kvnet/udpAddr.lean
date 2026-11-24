/-
The proof of `KvNet/Spec/.../kvnet/udpAddr.lean` (kvudp, phase 2: `notes/kvudp-proof-plan.md`).
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.udpAddr
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.parseAddr

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

theorem udpAddr.wp_proof
    (wp_parseAddr : parseAddr.spec (GF := GF) (hG := hG)) :
    udpAddr.spec (GF := GF) (hG := hG) := by
  intro a ha
  wp_start
  try wp_auto
  wp_apply wp_parseAddr a ha $$ [$Hpkg] as %ip %port %ok %Hres
  obtain ⟨Hok, Hsome⟩ := Hres
  cases ok
  · -- refused
    try wp_auto
    iapply HΦ
    isplitr
    · ipureintro; exact Hok
    ileft; ipureintro; rfl
  · obtain ⟨Hvd, Hl4⟩ := (parseAddrM_ok a).2 _ _ (Hsome rfl)
    rcases ip with ⟨arr⟩
    obtain ⟨b0, b1, b2, b3, rfl⟩ : ∃ b0 b1 b2 b3, arr = [b0, b1, b2, b3] := by
      match arr, Hl4 with
      | [b0, b1, b2, b3], _ => exact ⟨_, _, _, _, rfl⟩
    try wp_auto
    ipersist ip
    icases array_acc (GF := GF) _ (sint.Z (W64 0)) _ _ (array.mk 4 [b0, b1, b2, b3] : GoArray w8 4) b0
      (by decide) rfl $$ ip with ⟨#Hi0, -⟩
    icases array_acc (GF := GF) _ (sint.Z (W64 1)) _ _ (array.mk 4 [b0, b1, b2, b3] : GoArray w8 4) b1
      (by decide) rfl $$ ip with ⟨#Hi1, -⟩
    icases array_acc (GF := GF) _ (sint.Z (W64 2)) _ _ (array.mk 4 [b0, b1, b2, b3] : GoArray w8 4) b2
      (by decide) rfl $$ ip with ⟨#Hi2, -⟩
    icases array_acc (GF := GF) _ (sint.Z (W64 3)) _ _ (array.mk 4 [b0, b1, b2, b3] : GoArray w8 4) b3
      (by decide) rfl $$ ip with ⟨#Hi3, -⟩
    try wp_auto
    wp_apply wp_slice_literal (V := w8) (t := go.byte) [b0, b1, b2, b3]
    isplitr
    · ipureintro; rfl
    iintro %slp ⟨Hsl, -⟩
    imod ownSlice_persist $$ Hsl with #Hsl
    try wp_auto
    ipersist «$r0»
    iapply HΦ
    isplitr
    · ipureintro; exact Hok
    iright
    iexists [b0, b1, b2, b3], port
    isplitl
    · unfold net.udpAddrAt
      iexists _, _
      iframe #
    · ipureintro; exact Hvd

end proof

end raft_kvnet
end EtcdGrove
end Perennial

/-
The proof of `KvNet/Spec/.../kvnet/putFragment.lean` (kvudp, phase 2: `notes/kvudp-proof-plan.md`).
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.putFragment
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.putHeader
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.putUint32
public import Perennial.Proof.bytes.BufferBasics

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI Iris.ProofMode Net Udp go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]

theorem putFragment.wp_proof
    (wp_putHeader : putHeader.spec (GF := GF) (hG := hG))
    (wp_putUint32 : putUint32.spec (GF := GF) (hG := hG)) :
    putFragment.spec (GF := GF) (hG := hG) := by
  intro src dst boot seq index total chunk q cs
  wp_start as Hc
  ihave %Hcl := ownSlice_len _ _ _ $$ Hc
  ihave %Hmax := bytes.ownSlice_bytes_len_le _ _ _ $$ Hc
  try wp_auto
  have hcl0 : 0 ≤ sint.Z chunk.len := Hcl.2
  have hcl1 : sint.Z chunk.len ≤ 2 ^ 47 := Hmax
  have h45 : sint.Z (W64 45 + chunk.len) = 45 + sint.Z chunk.len := by word
  have hcap : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (W64 45 + chunk.len) := by
    rw [h45, show sint.Z (W64 0) = 0 from rfl]; omega
  wp_apply wp_slice_make3 (V := w8) (W64 0) (W64 45 + chunk.len) hcap as %buf ⟨Hbuf, Hcap, -⟩
  rw [show List.replicate 0 (zero_val w8) = [] from rfl]
  try wp_auto
  wp_apply wp_putHeader buf [] _ src dst boot seq $$ [$Hbuf $Hcap] as %b1 ⟨Hb, Hbcap⟩
  try wp_auto
  wp_apply wp_putUint32 b1 _ index $$ [$Hb $Hbcap] as %b2 ⟨Hb, Hbcap⟩
  try wp_auto
  wp_apply wp_putUint32 b2 _ total $$ [$Hb $Hbcap] as %b3 ⟨Hb, Hbcap⟩
  try wp_auto
  wp_apply wp_slice_append b3 _ chunk cs q $$ [$Hb $Hbcap $Hc] as %b4 ⟨Hb, Hbcap, Hc⟩
  try wp_auto
  iapply HΦ
  iframe Hbcap Hc
  rw [show fragBytes src dst boot seq index total cs =
    [] ++ headerBytes (W8 1) src dst boot seq ++ u32Le index ++ u32Le total ++ cs from rfl]
  iexact Hb

end proof

end raft_kvnet
end EtcdGrove
end Perennial

/-
The proof of `KvNet/Spec/.../kvnet/putHeader.lean` (kvudp, phase 2: `notes/kvudp-proof-plan.md`).
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.putHeader
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.putUint32
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.putUint64

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

theorem putHeader.wp_proof
    (wp_putUint32 : putUint32.spec (GF := GF) (hG := hG))
    (wp_putUint64 : putUint64.spec (GF := GF) (hG := hG)) :
    putHeader.spec (GF := GF) (hG := hG) := by
  intro buf B kind src dst boot seq
  wp_start as ⟨HB, Hcap⟩
  try wp_auto
  wp_apply wp_putUint32 buf B _ $$ [$HB $Hcap] as %b1 ⟨Hb, Hbcap⟩
  try wp_auto
  wp_apply wp_slice_literal (V := w8) (t := go.byte) [kind]
  isplitr
  · ipureintro; rfl
  iintro %ksl ⟨Hk, -⟩
  try wp_auto
  wp_apply wp_slice_append b1 _ _ [kind] (DFrac.own 1) $$ [$Hb $Hbcap $Hk] as %b2 ⟨Hb, Hbcap, -⟩
  try wp_auto
  wp_apply wp_putUint64 b2 _ src $$ [$Hb $Hbcap] as %b3 ⟨Hb, Hbcap⟩
  try wp_auto
  wp_apply wp_putUint64 b3 _ dst $$ [$Hb $Hbcap] as %b4 ⟨Hb, Hbcap⟩
  try wp_auto
  wp_apply wp_putUint64 b4 _ boot $$ [$Hb $Hbcap] as %b5 ⟨Hb, Hbcap⟩
  try wp_auto
  wp_apply wp_putUint64 b5 _ seq $$ [$Hb $Hbcap] as %b6 ⟨Hb, Hbcap⟩
  try wp_auto
  iapply HΦ
  iframe Hbcap
  simp only [headerBytes, udpMagicW, List.append_assoc] at *
  iexact Hb

end proof

end raft_kvnet
end EtcdGrove
end Perennial

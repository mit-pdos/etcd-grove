/-
The proof of `KvRaft/Spec/.../kvraft/putHeader.lean` (kvraft-udp, phase 2: `notes/kvraft-udp-proof-plan.md`).
-/
module

public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.putHeader
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.putUint32
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.putUint64

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvraft

open Iris Iris.BI Iris.ProofMode Net Udp go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Assumptions]

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

end kvraft
end EtcdGrove
end Perennial

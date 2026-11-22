/-
Proof of `KvNet/Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvnet/getMsgEntry.lean`: `getEntry`'s
(`getEntry.lean`) without the type check: `getUint64` three times, `getBytes`, then the fresh entry
(`entOwn_of_struct`: its cells `new(x)`, frozen; the type, an `int32` written sign-extended, truncated back).
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.getMsgEntry
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.getUint64
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.getBytes
public import KvNet.Spec.go_etcd_io.raft.v3.raftpb.EntryType__Enum

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]

theorem getMsgEntry.wp_proof (wp_getUint64 : getUint64.spec (GF := GF) (hG := hG))
    (wp_getBytes : getBytes.spec (GF := GF) (hG := hG))
    (wp_Enum : raftpb.EntryType.Enum.spec (GF := GF) (hG := hG)) :
    getMsgEntry.spec (GF := GF) (hG := hG) := by
  intro b dq e r Hwf
  wp_start as Hb
  ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  try wp_auto
  simp only [encEntry, List.append_assoc] at *
  wp_apply wp_getUint64 b dq e.Term' _ $$ [$Hb] as %r1 ⟨Hr1, -⟩
  try wp_auto
  wp_apply wp_getUint64 r1 dq e.Index' _ $$ [$Hr1] as %r2 ⟨Hr2, -⟩
  try wp_auto
  wp_apply wp_getUint64 r2 dq _ _ $$ [$Hr2] as %r3 ⟨Hr3, -⟩
  try wp_auto
  wp_apply wp_getBytes r3 dq e.Data' r Hwf $$ [$Hpkg $Hr3] as %v %rest ⟨Hv, Hrest, -⟩
  imod ownSlice_persist v dq e.Data' $$ Hv with #Hv
  try wp_auto
  have Hty32 : W32 (uint.Z (W64 (sint.Z e.Type'))) = e.Type' := by word
  rw [Hty32]
  haveI : go.NotInterface go.int32 := ⟨by unfold go.int32; trivial⟩
  try wp_auto
  iapply wp_fupd
  wp_apply wp_Enum e.Type' $$ [$Hpb] as %pty Hpty
  try wp_auto
  imod cellRO_alloc _ _ $$ «$v0» with #cT
  imod cellRO_alloc _ _ $$ «$v1» with #cI
  imod cellRO_alloc _ _ $$ Hpty with #cY
  imod entOwn_of_struct «$r0_ptr» _ e ⊤ rfl $$ [$«$r0» $cT $cI $cY $Hv] with He
  imodintro
  iapply HΦ
  iframe He Hrest

end proof

end raft_kvnet
end EtcdGrove
end Perennial

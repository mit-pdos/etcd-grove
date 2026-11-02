/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvdurable/getEntry.lean`. Lean-first (no
Rocq counterpart): `getUint64` three times, the type check (false: `EntWf`), `getBytes`, then the
fresh entry (`entOwn_of_struct`: its cells `new(x)`, frozen).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.getEntry
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.getUint64
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.getBytes
public import Spec.go_etcd_io.raft.v3.raftpb.EntryType__Enum

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]

theorem getEntry.wp_proof (wp_getUint64 : getUint64.spec (GF := GF) (hG := hG))
    (wp_getBytes : getBytes.spec (GF := GF) (hG := hG))
    (wp_Enum : raftpb.EntryType.Enum.spec (GF := GF) (hG := hG)) :
    getEntry.spec (GF := GF) (hG := hG) := by
  intro b e r Hwf
  wp_start as #Hb
  ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  try wp_auto
  simp only [encEntry, List.append_assoc] at *
  wp_apply wp_getUint64 b DFrac.discard e.Term' _ $$ [$Hb] as %r1 ⟨#Hr1, -⟩
  try wp_auto
  wp_apply wp_getUint64 r1 DFrac.discard e.Index' _ $$ [$Hr1] as %r2 ⟨#Hr2, -⟩
  try wp_auto
  wp_apply wp_getUint64 r2 DFrac.discard _ _ $$ [$Hr2] as %r3 ⟨#Hr3, -⟩
  try wp_auto
  have Hty : uint.Z (W64 (sint.Z e.Type')) = uint.Z e.Type' := by have := Hwf.1; word
  rw [decide_eq_false (by rw [Hty]; have := Hwf.1; word)]
  try wp_auto
  wp_apply wp_getBytes r3 DFrac.discard e.Data' r Hwf.2 $$ [$Hpkg $Hr3] as %v %rest ⟨#Hv, #Hrest, -⟩
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

end kvdurable
end EtcdGrove
end Perennial

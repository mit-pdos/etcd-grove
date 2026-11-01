/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvdurable/putEntry.lean`. Lean-first (no
Rocq counterpart): the entry's getters, then `putUint64` three times and `putBytes`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.putEntry
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.putUint64
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.putBytes
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetTerm
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetIndex
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetType
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetData

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

theorem putEntry.wp_proof (wp_putUint64 : putUint64.spec (GF := GF) (hG := hG))
    (wp_putBytes : putBytes.spec (GF := GF) (hG := hG))
    (wp_GetTerm : raftpb.Entry.GetTerm.spec (GF := GF) (hG := hG))
    (wp_GetIndex : raftpb.Entry.GetIndex.spec (GF := GF) (hG := hG))
    (wp_GetType : raftpb.Entry.GetType.spec (GF := GF) (hG := hG))
    (wp_GetData : raftpb.Entry.GetData.spec (GF := GF) (hG := hG)) :
    putEntry.spec (GF := GF) (hG := hG) := by
  intro buf B l dq e
  wp_start as ⟨Hbuf, Hcap, He⟩
  ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  try wp_auto
  wp_apply wp_GetTerm.1 l dq e $$ [$Hpb $He] as He
  wp_apply wp_putUint64 buf B e.Term' $$ [$Hbuf $Hcap] as %b1 ⟨Hb, Hbcap⟩
  try wp_auto
  wp_apply wp_GetIndex.1 l dq e $$ [$Hpb $He] as He
  wp_apply wp_putUint64 b1 _ e.Index' $$ [$Hb $Hbcap] as %b2 ⟨Hb, Hbcap⟩
  try wp_auto
  wp_apply wp_GetType.1 l dq e $$ [$Hpb $He] as He
  try wp_auto
  wp_apply wp_putUint64 b2 _ _ $$ [$Hb $Hbcap] as %b3 ⟨Hb, Hbcap⟩
  try wp_auto
  wp_apply wp_GetData.1 l dq e $$ [$Hpb $He] as %ds ⟨#Hds, He⟩
  wp_apply wp_putBytes b3 ds _ e.Data' DFrac.discard $$ [$Hb $Hbcap $Hds] as %b4 ⟨Hb, Hbcap, -⟩
  try wp_auto
  iapply HΦ
  iframe Hbcap He
  simp only [encEntry, List.append_assoc]
  iexact Hb

end proof

end kvdurable
end EtcdGrove
end Perennial

module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Storage__Snapshot
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.oneIn
public import Spec.go_etcd_io.raft.v3.MemoryStorage__Snapshot

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvreconf.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]
variable [KvrStor GF]

theorem Storage.Snapshot.wp_proof
    (wp_oneIn : oneIn.spec (GF := GF) (hG := hG))
    (wp_Snapshot : MemoryStorage.Snapshot.spec (GF := GF) (hG := hG)) :
    Storage.Snapshot.spec (GF := GF) (hG := hG) := by
  intro s ms γs J c esu
  wp_start as ⟨#Hrec, #Hinv, #Hc, #Hesu⟩
  ihave #Hrec' := Hrec
  iunfold kvrStorRec at Hrec'
  icases Hrec' with ⟨#Hf, -⟩
  ihave #Hraft : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  try wp_auto
  wp_apply wp_oneIn (W64 4) (by decide) $$ [$Hpkg] as %b -
  wp_if_destruct
  · try wp_auto
    wp_apply wp_Snapshot ms γs J c esu $$ [$Hraft $Hinv $Hc $Hesu] as %snap %err Hres
    try wp_auto
    iapply HΦ
    iexact Hres
  · try wp_auto
    iapply HΦ
    ileft; ipureintro; rfl

end proof

end kvreconf
end EtcdGrove
end Perennial

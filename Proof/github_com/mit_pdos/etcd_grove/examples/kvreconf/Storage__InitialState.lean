module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Storage__InitialState
public import Spec.go_etcd_io.raft.v3.MemoryStorage__InitialState

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

theorem Storage.InitialState.wp_proof
    (wp_InitialState : MemoryStorage.InitialState.spec (GF := GF) (hG := hG))
    (wp_Clone : proto.CloneConfState.spec (GF := GF) (hG := hG)) :
    Storage.InitialState.spec (GF := GF) (hG := hG) := by
  intro s ms bp γs hs csm
  wp_start as ⟨#Hrec, #Hboot, Hmeta, Hfresh⟩
  ihave #Hrec' := Hrec
  iunfold kvrStorRec at Hrec'
  icases Hrec' with ⟨#Hf, -⟩
  iunfold kvrStorBoot at Hboot
  icases Hboot with ⟨#Hb, #Hcs⟩
  ihave #Hraft : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  ihave #Hproto : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_InitialState ms γs hs $$ [$Hraft $Hmeta $Hfresh] as %hp %cs0 ⟨#Hhs, Hmeta, Hfresh, -⟩
  try wp_auto
  wp_apply wp_Clone.1 bp DFrac.discard csm $$ [$Hproto $Hcs] as %cs ⟨-, Hcl⟩
  try wp_auto
  iapply HΦ
  iframe Hhs Hmeta Hfresh Hcl

end proof

end kvreconf
end EtcdGrove
end Perennial

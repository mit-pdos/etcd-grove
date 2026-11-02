/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvdurable/Storage__InitialState.lean`. Lean-first
(no Rocq counterpart).

`MemoryStorage.InitialState` (detached: the hard state, the stored snapshot's conf state read-only,
`AutoLeave` frozen), then `snapIndex` (detached: the stored snapshot's index): at index `0` the
bootstrap conf state is cloned, otherwise the snapshot's (weakened to an unfrozen one, which is
what `proto.Clone`'s spec takes); the clone made read-only.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Storage__InitialState
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Storage__snapIndex
public import Spec.go_etcd_io.raft.v3.MemoryStorage__InitialState
public import Spec.google_golang_org.protobuf.proto.CloneConfState
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.DefsLaws
public import Proof.go_etcd_io.raft.v3.InvPbLog

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt durableExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KdStor GF]

attribute [local instance] kdStorageModel

/-- Justifications nothing reads (the detached call of `snapIndex` names none). -/
private def trivJ : MemJust GF where
  SV _ := iprop(True)
  B _ := iprop(True)
  DL _ := iprop(True)
  SV_pers _ := inferInstance
  B_pers _ := inferInstance
  B_timeless _ := inferInstance
  DL_pers _ := inferInstance

theorem Storage.InitialState.wp_proof
    (wp_InitialState : MemoryStorage.InitialState.spec (GF := GF) (hG := hG))
    (wp_snapIndex : Storage.snapIndex.spec (GF := GF) (hG := hG))
    (wp_Clone : proto.CloneConfState.spec (GF := GF) (hG := hG)) :
    Storage.InitialState.spec (GF := GF) (hG := hG) := by
  intro s ms bp γs hs c sv boot
  wp_start as ⟨#Hrec, #Hboot, Hlock, Hmeta, Hfresh⟩
  ihave #Hrec' := Hrec
  iunfold kdStorRec at Hrec'
  icases Hrec' with ⟨#Hf, -⟩
  iunfold kdStorBoot at Hboot
  icases Hboot with ⟨#Hb, #Hcs⟩
  ihave #Hraft : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  ihave #Hproto : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_InitialState ms γs hs c sv $$ [$Hraft $Hmeta $Hfresh] as %hp %cs0 ⟨#Hhs, Hmeta, Hfresh, #Hcs0⟩
  try wp_auto
  wp_apply wp_snapIndex s ms γs trivJ (some (c, sv)) 0
    $$ [$Hpkg $Hrec Hlock Hfresh] as %i ⟨-, Hrest⟩
  · isplitl
    · simp only [memStorAt]; iframe
    iapply memCompacted_zero
  icases Hrest with ⟨%Hi, Hlock, Hfresh⟩
  subst Hi
  try wp_auto
  wp_if_destruct
  · rw [if_pos Hif]
    try wp_auto
    iapply wp_fupd
    wp_apply wp_Clone.1 bp DFrac.discard boot $$ [$Hproto $Hcs] as %cs ⟨-, Hcl⟩
    imod csPts_persist _ _ _ _ $$ Hcl with #Hcl
    imodintro
    try wp_auto
    iapply HΦ
    iframe Hhs Hlock Hmeta Hfresh Hcl
  · rw [if_neg Hif]
    ihave #Hcs1 := csPts_weaken cs0 DFrac.discard _ true $$ Hcs0
    try wp_auto
    iapply wp_fupd
    wp_apply wp_Clone.1 cs0 DFrac.discard _ $$ [$Hproto $Hcs1] as %cs ⟨-, Hcl⟩
    imod csPts_persist _ _ _ _ $$ Hcl with #Hcl
    imodintro
    try wp_auto
    iapply HΦ
    iframe Hhs Hlock Hmeta Hfresh Hcl

end proof

end kvdurable
end EtcdGrove
end Perennial

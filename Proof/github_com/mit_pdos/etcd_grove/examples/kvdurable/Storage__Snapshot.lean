/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvdurable/Storage__Snapshot.lean`. Lean-first
(no Rocq counterpart). kvreconf's proof (`kvreconf/Storage__Snapshot.lean`), at kvdurable's wrapper.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Storage__Snapshot
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.oneIn
public import Spec.go_etcd_io.raft.v3.MemoryStorage__Snapshot

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

theorem Storage.Snapshot.wp_proof
    (wp_oneIn : oneIn.spec (GF := GF) (hG := hG))
    (wp_Snapshot : MemoryStorage.Snapshot.spec (GF := GF) (hG := hG)) :
    Storage.Snapshot.spec (GF := GF) (hG := hG) := by
  intro s ms γs J c esu
  wp_start as ⟨#Hrec, #Hinv, #Hc, #Hesu⟩
  ihave #Hrec' := Hrec
  iunfold kdStorRec at Hrec'
  icases Hrec' with ⟨#Hf, -⟩
  ihave #Hraft : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  try wp_auto
  wp_apply wp_oneIn (W64 4) (by decide) $$ [$Hpkg] as %b -
  wp_if_destruct
  · try wp_auto
    wp_apply wp_Snapshot ms γs J none c false esu $$ [$Hraft $Hc $Hesu] as %snap %err ⟨-, Hres⟩
    · isplitr
      · iapply memStorAt_none_intro $$ Hinv
        iempintro
      iempintro
    try wp_auto
    iapply HΦ
    icases Hres with ⟨%H, %sv, Hs, %Hsv, Hv⟩
    ihave Hs := ownSnapW_E $$ Hs
    ihave Hs := ownSnapE_weaken $$ Hs
    iright
    iframe
    ipureintro; exact ⟨H, Hsv.1⟩
  · try wp_auto
    iapply HΦ
    ileft; ipureintro; rfl

end proof

end kvdurable
end EtcdGrove
end Perennial

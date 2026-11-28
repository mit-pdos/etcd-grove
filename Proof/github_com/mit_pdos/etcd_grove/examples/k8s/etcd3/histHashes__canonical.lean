/-
Lean-first (no Rocq counterpart).

The proof of `(*histHashes).canonical`: `canonLocked` under `hh.mu` (`hhOwn`'s mutex).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.histHashes__canonical
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.histHashes__canonLocked
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock
public import Perennial.Proof.sync.Link

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem histHashes.canonical.wp_proof
    (wp_canonLocked : histHashes.canonLocked.spec (GF := GF) (hG := hG)) :
    histHashes.canonical.spec (GF := GF) (hG := hG) := by
  intro hh h hs
  wp_start as ⟨#Hhh, #Hh, %Hlen⟩
  iunfold hhOwn at Hhh
  icases Hhh with ⟨#Hsync, #Hmu⟩
  (try wp_auto)
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply sync.Mutex.wp_Lock _ (hhInv hh) $$ [$Hsync $Hmu] as ⟨Hlk, Hinv⟩
  iunfold hhInv at Hinv
  icases Hinv with ⟨Hinv, Hgaps⟩
  try wp_auto
  wp_apply wp_canonLocked hh h hs $$ [$Hinv $Hh] as %c ⟨Hinv, #Hc⟩
  · ipureintro; exact Hlen
  try wp_auto
  wp_apply sync.Mutex.wp_Unlock _ (hhInv hh) $$ [$Hsync $Hmu $Hlk Hinv Hgaps]
  · iunfold hhInv
    iframe
  try wp_auto
  iapply HΦ
  iexact Hc

end proof

end k8s_etcd3
end EtcdGrove
end Perennial

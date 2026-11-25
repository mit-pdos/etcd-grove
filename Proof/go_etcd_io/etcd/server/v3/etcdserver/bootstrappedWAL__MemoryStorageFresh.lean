/-
The proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/bootstrappedWAL__MemoryStorageFresh.lean` (claim
#34 stage 4, 2026-11-25): `NewMemoryStorage`, and the three branches skipped. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.bootstrappedWAL__MemoryStorageFresh

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem bootstrappedWAL.MemoryStorage.wp_proofFresh
    (wp_NewMemoryStorage : NewMemoryStorage.spec (GF := GF) (hG := hG)) :
    bootstrappedWAL.MemoryStorage.specFresh (GF := GF) (hG := hG) := by
  intro sz w dq bw Hsn Hst Hen
  wp_start as Hw
  icases typedPointsto_not_null_dup _ _ _ $$ Hw with ⟨Hw, %Hwnn⟩
  iStructNamed Hw
  ihave #Hraft : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  try wp_auto
  wp_apply wp_NewMemoryStorage sz as %ms %γs ⟨%Hsz, #Hlock, #Hd0, Hend, Hnone, Hmeta, Hfresh⟩
  try wp_auto
  try simp only [Hsn, Hst, Hen]
  try wp_auto
  iapply HΦ
  iframe Hlock Hd0 Hend Hnone Hmeta Hfresh
  isplitl
  · iapply typedPointsto_combine _ _ _ Hwnn
    simp only [TypedPointsto.typedPointstoDef, Hsn, Hst, Hen]
    iframe
  ipureintro; exact Hsz

end proof

end EtcdGrove
end Perennial

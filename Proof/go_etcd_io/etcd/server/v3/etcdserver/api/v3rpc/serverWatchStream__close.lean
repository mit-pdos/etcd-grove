/-
Proof of the spec of the same name (the watch slice's unit W-S). Lean-first (no Rocq counterpart).
Over mvcc's API (2026-11-05): `Close`'s contract, through `shapes.law`, with the update
`WatchApi.close_au`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.serverWatchStream__close

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api
  go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem v3rpc.serverWatchStream.close.wp_proof
    (hShapes : mvcc.api.shapes.law (GF := GF) (hG := hG))
    (hP : mvcc.api.persistent.law (GF := GF) (hG := hG)) :
    v3rpc.serverWatchStream.close.spec (GF := GF) (hG := hG) := by
  intro sws r Up Dn st ci cd n P
  have := v3rpc.swsIs_persistent (GF := GF) hP
  wp_start as ⟨#Hsws, Htok, Hcc, Hadd⟩
  have : ∀ ws γ ι, Persistent (mvcc.api.isMvccWatchStream (GF := GF) ws γ ι) := hP.2.1
  ihave #Hsws' := Hsws
  iunfold v3rpc.swsIs at Hsws'
  icases Hsws' with ⟨%Hnn, -, -, -, -, -, -, -, -, -, #Fws, -, -, -, -, #Fcc, -, -, -, -, -, #Hwstream,
    #Hinv, -⟩
  ihave %Hsh := hShapes.2.2.2 r.ws r.W.γm r.ι $$ Hwstream
  obtain ⟨ty, v, hws, -, -, -, -, -, hClose, -⟩ := Hsh
  ihave Hau := v3rpc.close_au (v3rpc.cancelQ r.γs) hP r.ι r.γreg r.γtok r.γcl $$ [Htok]
  · iunfold v3rpc.wsInv at Hinv; iframe Hinv Htok
  rw [hws]
  ihave #Pmvcc : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc $$ []
  · iPkgInit
  ihave #Psync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_auto
  wp_apply (hClose r.W.γm r.ι (fun _ => iprop(True))) $$ [$Hau] as -
  · iframe #
  wp_apply wp_broadcast_chan_close r.cc r.γcc iprop(True) $$ [$Hcc] as -
  · iintro !>; itrivial
  wp_apply sync.join.WaitGroup.wp_Wait P n (v3rpc.swsF sws go!"wg") $$ [$Hadd] as -
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial

/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/BackendHooks__SetConfState.lean`. Lean-first
(no Rocq counterpart); D43 M5b′ (2026-10-26): under `confStateLock`, `proto.Clone`'s fresh copy
(a nil one for nil) stored, the dirty flag set.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.BackendHooks__SetConfState

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage backend storage go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.Assumptions]

theorem storage.BackendHooks.SetConfState.wp_proof
    (hClone : proto.CloneConfState.spec (GF := GF) (hG := hG)) :
    storage.BackendHooks.SetConfState.spec (GF := GF) (hG := hG) := by
  intro bh ix lg cs
  wp_start as ⟨#Hbh, Hcs⟩
  iunfold storage.isBackendHooks at Hbh
  icases Hbh with ⟨#Hix, #Hlg, #Hmu⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hproto : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto $$ []
  · iPkgInit
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hinv⟩
  iunfold storage.csInv at Hinv
  icases Hinv with ⟨%cs0, %d, Hcsf, Hd⟩
  (try wp_auto)
  icases Hcs with (%Hnil | ⟨%c, #Hc⟩)
  · subst Hnil
    wp_apply hClone.2
    (try wp_auto)
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hcsf Hd]
    · inext
      iunfold storage.csInv
      iexists _, _
      iframe
    (try wp_auto)
    iapply HΦ
    itrivial
  · wp_apply hClone.1 cs DFrac.discard c $$ [] as %p' ⟨-, -⟩
    · iframe #
    (try wp_auto)
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hcsf Hd]
    · inext
      iunfold storage.csInv
      iexists _, _
      iframe
    (try wp_auto)
    iapply HΦ
    itrivial

end proof

end EtcdGrove
end Perennial

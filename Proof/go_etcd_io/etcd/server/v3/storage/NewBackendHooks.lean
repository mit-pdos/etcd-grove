/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/NewBackendHooks.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.NewBackendHooks

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage storage

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.Assumptions]

theorem storage.NewBackendHooks.wp_proof : storage.NewBackendHooks.spec (GF := GF) (hG := hG) := by
  intro lg ix
  wp_start
  iapply wp_fupd
  wp_auto
  irename «$r0» => Hbh
  generalize «$r0_ptr» = bh at *
  iStructNamed Hbh
  ipersist indexer
  ipersist lg
  imod sync.init_Mutex (csInv bh) ⊤ (hF go!"confStateLock" bh) $$ confStateLock
    [confState confStateDirty] with #Hmu
  · inext
    iunfold csInv
    iexists null, false
    iframe confState confStateDirty
  imodintro
  iapply HΦ
  iunfold isBackendHooks
  iframe indexer lg Hmu

end proof

end EtcdGrove
end Perennial

/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/NewStorage.lean` (wal-link L2, 2026-11-17). Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.NewStorage

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode storage

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.Assumptions]

theorem storage.NewStorage.wp_proof : storage.NewStorage.spec (GF := GF) (hG := hG) := by
  intro lg w ss
  wp_start as -
  wp_auto
  iapply wp_fupd
  wp_alloc p as Hp
  iStructNamed Hp
  ipersist s
  imod sync.init_RWMutex (storagePw (GF := GF) p w) (E := ⊤) _ $$ [w] mux with Hslots
  · inext; iunfold storagePw; iexact w
  ihave ⟨Hslots, #Hguard⟩ := sync.ownRWMutex_slots_guard _ _ $$ Hslots
  ihave ⟨H1, H2⟩ := slots_two _ $$ Hslots
  wp_pures
  wp_store
  wp_pures
  wp_load
  wp_pures
  imodintro
  iapply HΦ
  iunfold storageOver
  iunfold storageRd
  iframe H1 H2
  iframe #

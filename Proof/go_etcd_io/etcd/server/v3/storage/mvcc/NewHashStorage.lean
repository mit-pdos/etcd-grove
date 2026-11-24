/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/mvcc/NewHashStorage.lean`. Lean-first (no
Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.NewHashStorage

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.NewHashStorage.wp_proof : mvcc.NewHashStorage.spec (GF := GF) (hG := hG) := by
  intro lg s
  wp_start as #Hlg
  (try wp_auto)
  wp_alloc h as Hh
  iStructNamed Hh
  ipersist lg
  -- `hashMu`, over the empty `hashes` (its reader slots are dropped: nothing verified reads
  -- `hashes` under the read lock yet)
  imod (sync.init_RWMutex (mvcc.hashesR (GF := GF) h) (E := ⊤)
      (structFieldRef hashStorage go!"hashMu" h)) $$ [hashes] hashMu with Hslots
  · inext
    iunfold mvcc.hashesR
    iexists slice.nil, []
    iframe hashes
    isplitr
    · iapply ownSlice_nil
    isplitl
    · iapply ownSliceCap_nil
    · ipureintro; simp
  icases sync.ownRWMutex_slots_guard _ _ $$ Hslots with ⟨-, #Hg⟩
  (try wp_auto)
  iapply HΦ
  unfold mvcc.hashStorageOk
  iexists lg
  iframe lg Hg
  iexact Hlg

end proof

end EtcdGrove
end Perennial

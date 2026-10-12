/-
Proof of `Spec/.../mvcc/watcherSet__add.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watcherSet__add

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.watcherSet.add.wp_proof : mvcc.watcherSet.add.spec (GF := GF) (hG := hG) := by
  intro m S wa
  wp_start as ⟨Hm, %Hwa⟩
  iunfold mvcc.ownWatcherSet at Hm
  wp_auto
  wp_apply wp_map_lookup2 $$ Hm as Hm
  rw [Hwa]
  wp_auto
  wp_apply wp_mapInsert $$ Hm as Hm
  iapply HΦ
  iunfold mvcc.ownWatcherSet
  iexact Hm

end proof

end EtcdGrove
end Perennial

/-
Proof of `Spec/.../mvcc/treeIndex__KeyIndex.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.treeIndex__KeyIndex
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.treeIndex__keyIndex
@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [go_etcd_io.etcd.cache.v3.Assumptions]

theorem mvcc.treeIndex.KeyIndex.wp_proof
    (hKI : mvcc.treeIndex.keyIndex.spec (GF := GF) (hG := hG)) :
    mvcc.treeIndex.KeyIndex.spec (GF := GF) (hG := hG) := by
  intro ti L keyi k
  wp_start as ⟨Hix, #Hkey⟩
  iunfold mvcc.ownIdxPriv at Hix
  icases Hix with ⟨%t, %lg, #Htree, #Hlg, %Hlgnn, Hmu, Htr⟩
  wp_apply wp_with_defer
  iintro %defer Hdefer
  (try wp_auto)
  -- `ti.RLock()`: the promoted method, on private memory
  rw [method_unfold (t := go.GoType.PointerType treeIndex.ty) (m := go!"RLock")]
  wp_call
  (try wp_auto)
  wp_apply (plain.wp_RLock sync.atomic.Int32.wp_Add (mvcc.idxMuAddr ti)) $$ [$Hmu] as Hmu
  (try wp_auto)
  -- `ti.keyIndex(keyi)`
  ihave #Hitem : mvcc.kiItemIs (GF := GF) keyi (keyi, k) $$ []
  · iunfold mvcc.kiItemIs
    isplitl []
    · ipureintro; rfl
    iexact Hkey
  wp_apply (hKI ti t L 1 keyi k) $$ [$Htr] as %p ⟨Htr, %Hp⟩
  · iframe #
  -- the deferred `ti.RUnlock()`
  rw [method_unfold (t := go.GoType.PointerType treeIndex.ty) (m := go!"RUnlock")]
  wp_call
  (try wp_auto)
  wp_apply (plain.wp_RUnlock sync.atomic.Int32.wp_Add (mvcc.idxMuAddr ti)) $$ [$Hmu] as Hmu
  (try wp_auto)
  iapply HΦ
  isplitl [Hmu Htr]
  · iunfold mvcc.ownIdxPriv
    iexists t, lg
    iframe Hmu Htr
    iframe #
    ipureintro; exact Hlgnn
  ipureintro; exact Hp

end proof

end EtcdGrove
end Perennial

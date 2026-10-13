/-
Proof of `Spec/.../mvcc/storeTxnRead__End.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.storeTxnRead__End


@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.storeTxnRead.End.wp_proof : mvcc.storeTxnRead.End.spec (GF := GF) (hG := hG) := by
  intro tr s trace ti rt γ log rev
  wp_start as ⟨-, #Htr, Hrd, #Hidx0, Hmu0, HrevMu0, Hti0⟩
  iunfold mvcc.storeTxnReadIs at Htr
  iNamedSuffix Htr "T"
  iunfold mvcc.txReader at Hrd
  icases Hrd with ⟨%m, %Rd, %L, %Tok, Hrd⟩
  iNamed Hrd
  iunfold mvcc.keyReadSnap at Hsnap
  icases Hsnap with ⟨-, #HRU, -, -, -⟩
  (try wp_auto)
  -- `tr.tx.RUnlock()`
  wp_apply HRU $$ [$Htok]
  (try wp_auto)
  -- `tr.s.mu.RUnlock()`
  wp_apply +noauto sync.RWMutex.wp_RUnlock $$ [$Hmu0] as Hmu0
  · inext; iunfold mvcc.muInv; itrivial
  (try wp_auto)
  iapply HΦ
  iunfold mvcc.storeReader
  iexists ti
  simp only [named]
  iframe Hmu0 HrevMu0 Hti0
  iframe #

end proof

end EtcdGrove
end Perennial

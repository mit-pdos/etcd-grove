/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/InmemStore__GetLog.lean (241f27e).
-/
/-
`raft.(*InmemStore).GetLog`'s spec: logically atomic read. The caller's atomic update sees the
log contents `L` (unchanged); `*log` receives a copy of the entry at `index` and the result is
`nil`, or (no entry) `*log` is unchanged and the result is a non-nil error (`getLogPost`). The
read lock is paid for by the calling thread's `rtok`, given back. As `isLogStore`'s
`GetLog`.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.InmemStoreBase

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

open github_com.hashicorp.raft proto in
/-- `i.GetLog(index, log)` copies the entry at `index` into `*log`, atomically. -/
abbrev github_com.hashicorp.raft.InmemStore.GetLog.spec : Prop :=
  ∀ (γs : InmemNames) (i : Loc) (idx : w64) (ptr : Loc) (lv0 : Log) (tid : Nat),
  ⊢ ∀ Φ : val → IProp GF,
    iprop(isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isInmemStore γs i ∗
      ptr ↦ lv0 ∗ rtok tid) -∗
    (|NC={⊤ \ ↑storeN,∅}=> ▷ ∃ A, inmemLogs γs A ∗
      (inmemLogs γs A ={∅,⊤ \ ↑storeN}=∗ ∀ err : GoInterface, getLogPost ptr (uint.nat idx) A.m err -∗
        rtok tid -∗ Φ #err)) -∗
    WP (App (App (Val (i @!! go.GoType.PointerType InmemStore.ty @!! go!"GetLog")) (Val #idx))
      (Val #ptr)) {{ Φ }}

end spec

end Perennial

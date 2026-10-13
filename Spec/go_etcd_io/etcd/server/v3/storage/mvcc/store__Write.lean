/-
`store.Write` (kvstore_txn.go). Lean-first (no Rocq counterpart); see `InvStore.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `s.Write(trace)` opens a write transaction at the committed log, for one revision token:
`s.mu` held shared and the batch transaction locked (the writer's resources) until `End`.
`LockInsideApply` runs the store's post-lock hook `f` under the lock (invariant `P`, `hookIs`)
on the caller's `Pre`, by the caller's triple: its `Q` is the caller's. A write token of the
backend (`storeWT`: the real backend's write-back budget, which the transaction's `Unlock` spends;
nothing for mvcc's assumed backend; 2026-10-13, unit 5) is spent too.

**The compaction revision** (2026-10-13, unit 6a): the transaction holds `s.mu` at the
compaction revision `crev` (fixed until `End`), at or above the caller's lower bound `c`, a
revision of the committed log (or `-1`); its reads answer `rangeOutcomeC` at it. The reader's tag
`Z` is carried to `End`. The frozen statement (`storeReader`, `crev = -1`) is `specFrozen`
(`spec_frozen`). -/
abbrev mvcc.store.Write.spec : Prop :=
  ∀ (s : Loc) (γ : mvcc.StoreNames) (trace : Loc) (P Pre Q : IProp GF) (f : val) (c : Int)
    (Z : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isStore s γ ∗ mvcc.storeReaderC s γ ∗ □ Z ∗ mvcc.crevLb γ.idx c ∗ mvcc.revToken γ ∗
      mvcc.storeWT γ ∗ ⌜trace ≠ null⌝ ∗
      mvcc.hookIs γ P f ∗ Pre ∗ □ ({{ P ∗ Pre }} (App (Val f) (Val #())) {{ RET #(); Q }}) }}
    (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"Write")) (Val #trace))
  {{ (mw : Loc), RET #(interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw);
      (∃ (ilog : mvcc.Log) (crev : Int),
        mvcc.isTxnWrite mw s γ ilog [] (W64 0) (W64 0) (W64 0) crev Z ∗ mvcc.crevLb γ.idx crev ∗
        ⌜c ≤ crev⌝) ∗ Q }}

/-- The frozen statement (before unit 6a). -/
abbrev mvcc.store.Write.specFrozen : Prop :=
  ∀ (s : Loc) (γ : mvcc.StoreNames) (trace : Loc) (P Pre Q : IProp GF) (f : val),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isStore s γ ∗ mvcc.storeReader s γ ∗ mvcc.revToken γ ∗ mvcc.storeWT γ ∗ ⌜trace ≠ null⌝ ∗
      mvcc.hookIs γ P f ∗ Pre ∗ □ ({{ P ∗ Pre }} (App (Val f) (Val #())) {{ RET #(); Q }}) }}
    (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"Write")) (Val #trace))
  {{ (mw : Loc), RET #(interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw);
      (∃ ilog : mvcc.Log, mvcc.isTxnWrite mw s γ ilog [] (W64 0) (W64 0) (W64 0)) ∗ Q }}

open Iris.ProofMode in
/-- **The frozen statement is a corollary** (`isTxnWrite_frozen`). -/
theorem mvcc.store.Write.spec_frozen (h : mvcc.store.Write.spec (GF := GF) (hG := hG)) :
    mvcc.store.Write.specFrozen (GF := GF) (hG := hG) := by
  intro s γ trace P Pre Q f
  iintro %Φ ⟨#Hpkg, #Hs, Hrd, Htok, Hwt, %Ht, #Hh, Hpre, #Htr⟩ HΦ
  icases mvcc.storeReader_toC s γ $$ Hrd with ⟨Hrd, #Hf⟩
  imod mvcc.crevLb_neg γ.idx with #Hlb
  iapply wp_fupd
  iapply (h s γ trace P Pre Q f (-1) (mvcc.crevFrozen γ)) $$ %(fun v => iprop(|={⊤}=> Φ v))
    [Hrd Htok Hwt Hpre]
  · iframe Hrd Htok Hwt Hpre; iframe #; ipureintro; exact Ht
  inext
  iintro %mw ⟨⟨%ilog, %crev, Htx, #Hlb', %Hc⟩, HQ⟩
  imod mvcc.isTxnWrite_frozen mw s γ ilog [] (W64 0) (W64 0) (W64 0) crev $$ Htx with ⟨Htx, %Hcr⟩
  subst Hcr
  imodintro
  iapply HΦ
  iframe HQ
  iexists ilog
  iexact Htx

end spec

end EtcdGrove
end Perennial

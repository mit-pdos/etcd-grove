/-
`readView__Range` (metrics_txn.go / kv_view.go). Lean-first (no Rocq counterpart); see `InvStore.lean`.
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

/-- `rv.Range(ctx, key, end, ro)`: a read transaction opened at the last revision of a
committed log, its range, and closed: at the compaction revision `crev` it observed, at or above
the caller's lower bound `c` (`rangeOutcomeC`; 2026-10-13, unit 6a). The frozen statement
(`storeReader`, `rangeOutcome`) is `specFrozen` (`spec_frozen`). -/
abbrev mvcc.readView.Range.spec : Prop :=
  ∀ (rv s : Loc) (γ : mvcc.StoreNames)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (key endk : GoSlice) (k e : GoString)
    (ro : RangeOptions) (c : Int),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isReadView rv s γ ∗ mvcc.storeReaderC s γ ∗ mvcc.crevLb γ.idx c ∗
      context.isContext ctx cd ∗ key ↦*□ k ∗ endk ↦*□ e }}
    (App (App (App (App (Val (rv @!! go.GoType.PointerType readView.ty @!! go!"Range"))
      (Val #(GoInterface.ok ctx))) (Val #key)) (Val #endk)) (Val #ro))
  {{ (r : Loc) (err : GoInterface), RET (PairV #r #err);
      mvcc.storeReaderC s γ ∗
      ∃ (log : mvcc.Log) (rev : w64) (crev : Int), mvcc.idxCert γ.idx log ∗ mvcc.crevLb γ.idx crev ∗
        ⌜log ≠ [] ∧ rev = W64 ((log.length : Int) - 1) ∧ c ≤ crev ∧ -1 ≤ crev⌝ ∗
        mvcc.rangeOutcomeC r err log rev crev (decide (endk = slice.nil)) k e ro }}

/-- The frozen statement (before unit 6a). -/
abbrev mvcc.readView.Range.specFrozen : Prop :=
  ∀ (rv s : Loc) (γ : mvcc.StoreNames)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (key endk : GoSlice) (k e : GoString)
    (ro : RangeOptions),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isReadView rv s γ ∗ mvcc.storeReader s γ ∗
      context.isContext ctx cd ∗ key ↦*□ k ∗ endk ↦*□ e }}
    (App (App (App (App (Val (rv @!! go.GoType.PointerType readView.ty @!! go!"Range"))
      (Val #(GoInterface.ok ctx))) (Val #key)) (Val #endk)) (Val #ro))
  {{ (r : Loc) (err : GoInterface), RET (PairV #r #err);
      mvcc.storeReader s γ ∗
      ∃ (log : mvcc.Log) (rev : w64), mvcc.idxCert γ.idx log ∗
        ⌜log ≠ [] ∧ rev = W64 ((log.length : Int) - 1)⌝ ∗
        mvcc.rangeOutcome r err log rev (decide (endk = slice.nil)) k e ro }}

open Iris.ProofMode in
/-- **The frozen statement is a corollary**: the frozen fact bounds the observed compaction
revision by `-1` (`crevFrozen_lb`), and the read's revision is not negative (`rangeOutcomeC_neg`). -/
theorem mvcc.readView.Range.spec_frozen (h : mvcc.readView.Range.spec (GF := GF) (hG := hG)) :
    mvcc.readView.Range.specFrozen (GF := GF) (hG := hG) := by
  intro rv s γ ctx cd key endk k e ro
  iintro %Φ ⟨#Hpkg, #Hrv, Hrd, #Hctx, #Hkey, #Hend⟩ HΦ
  icases mvcc.storeReader_toC s γ $$ Hrd with ⟨Hrd, #Hf⟩
  imod mvcc.crevLb_neg γ.idx with #Hlb
  iapply wp_fupd
  iapply (h rv s γ ctx cd key endk k e ro (-1)) $$ %(fun v => iprop(|={⊤}=> Φ v)) [Hrd]
  · iframe Hrd; iframe #
  inext
  iintro %r %err ⟨Hrd, %log, %rev, %crev, #Hc, #Hlb', %Hp, Hout⟩
  imod mvcc.crevFrozen_lb γ crev Hp.2.2.2 $$ Hf Hlb' with %Hcr
  subst Hcr
  ihave %Hrv := mvcc.idxCert_lastRev γ log Hp.1 $$ Hc
  imodintro
  iapply HΦ
  isplitl [Hrd]
  · iapply mvcc.storeReader_of $$ [$Hrd $Hf]
  iexists log, rev
  iframe Hc
  isplitl []
  · ipureintro; exact ⟨Hp.1, Hp.2.1⟩
  iapply mvcc.rangeOutcomeC_neg _ _ _ _ _ _ _ _ (by rw [Hp.2.1]; exact Hrv) $$ Hout

end spec

end EtcdGrove
end Perennial

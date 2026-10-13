/-
`store__Rev` (kvstore.go: `store.Rev` is the method `Rev` of its embedded `ReadView`, the
`readView{s}` `NewStore` installs; kv_view.go). Lean-first (no Rocq counterpart); see
`InvStore.lean`. For the server's apply package (`newHeader` reads `KV.Rev()`).
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

/-- `s.Rev()`: the store's `readView` opens a read transaction and closes it; the last revision
of the committed log it read. As `store.Read`'s, the log read is pinned between the caller's
certificate `log₀` and its `m` revision tokens (with every token left, at the sole writer, it is
the writer's log); `m = 0`, `log₀ = []` is the plain spec. The store's `ReadView` field holds the
`readView` `NewStore` returns (`isReadView`). Of a store that may be compacted (`storeReaderC`;
2026-10-13, unit 6a); the frozen statement (`storeReader`) is `specFrozen` (`spec_frozen`). -/
abbrev mvcc.store.Rev.spec : Prop :=
  ∀ (s rv : Loc) (γ : mvcc.StoreNames) (m : Nat) (log₀ : mvcc.Log),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      s.[store, go!"ReadView"] ↦□
        (interface.mkOk (go.GoType.PointerType readView.ty) #rv : GoInterface) ∗
      mvcc.isReadView rv s γ ∗ mvcc.storeReaderC s γ ∗ ownToks γ.revs m ∗
      mvcc.idxCert γ.idx log₀ }}
    (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"Rev")) (Val #()))
  {{ (v : w64), RET #v; mvcc.storeReaderC s γ ∗ ownToks γ.revs m ∗
      ∃ log : mvcc.Log, mvcc.idxCert γ.idx log ∗
        ⌜log₀ <+: log ∧ log.length + m + 3 ≤ 2 ^ 63 ∧ log ≠ [] ∧
          v = W64 ((log.length : Int) - 1)⌝ }}

/-- The frozen statement (before unit 6a). -/
abbrev mvcc.store.Rev.specFrozen : Prop :=
  ∀ (s rv : Loc) (γ : mvcc.StoreNames) (m : Nat) (log₀ : mvcc.Log),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      s.[store, go!"ReadView"] ↦□
        (interface.mkOk (go.GoType.PointerType readView.ty) #rv : GoInterface) ∗
      mvcc.isReadView rv s γ ∗ mvcc.storeReader s γ ∗ ownToks γ.revs m ∗
      mvcc.idxCert γ.idx log₀ }}
    (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"Rev")) (Val #()))
  {{ (v : w64), RET #v; mvcc.storeReader s γ ∗ ownToks γ.revs m ∗
      ∃ log : mvcc.Log, mvcc.idxCert γ.idx log ∗
        ⌜log₀ <+: log ∧ log.length + m + 3 ≤ 2 ^ 63 ∧ log ≠ [] ∧
          v = W64 ((log.length : Int) - 1)⌝ }}

open Iris.ProofMode in
/-- **The frozen statement is a corollary** (the frozen fact framed). -/
theorem mvcc.store.Rev.spec_frozen (h : mvcc.store.Rev.spec (GF := GF) (hG := hG)) :
    mvcc.store.Rev.specFrozen (GF := GF) (hG := hG) := by
  intro s rv γ m log₀
  iintro %Φ ⟨#Hpkg, #HRV, #Hrv, Hrd, Htoks, #Hc0⟩ HΦ
  icases mvcc.storeReader_toC s γ $$ Hrd with ⟨Hrd, #Hf⟩
  iapply (h s rv γ m log₀) $$ %Φ [Hrd Htoks]
  · iframe Hrd Htoks; iframe #
  inext
  iintro %v ⟨Hrd, Hpost⟩
  iapply HΦ
  iframe Hpost
  iapply mvcc.storeReader_of $$ [$Hrd $Hf]

end spec

end EtcdGrove
end Perennial

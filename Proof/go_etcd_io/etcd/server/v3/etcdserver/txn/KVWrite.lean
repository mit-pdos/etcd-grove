/-
**The txn package's KV over either store** (unit N4, D14a, `notes/decisions.md`). Lean-first (no
Rocq counterpart).

The functions of the txn package call `kv.Read`, `kv.Write` and, on the write transaction,
`End`; `txn.isKV kv s γ` (`Defs.lean`) is the plain store or a watchable store over it. Here:

* **`kv.Read`** at either (`kv_Read`, the frozen `store.Read` at a KV over the store).
* **`kv.Write`** (`kv_Write`): the store's `store.Write`, or the watchable store's, whose write
  transaction needs the sole writer of its notified log (`watchWriter`: the caller's tokens with
  the transaction's, its certificate and half of the notified log, `wlogOwn`). Either way the
  result is a write transaction `interface.mkOk tyX vX` over the `*metricsTxnWrite` `mw`
  (`mvcc.twWrap`, `KVView.lean`: the functions in between run on `mw`'s methods), the caller's
  tokens back, and what `End` needs beside the transaction (`twEnd`).
* **`End`** (`tw_End`): `metricsTxnWrite.End`, or the watchable store's (the watchers notified
  under its lock): the store's reader slots back, the committed log certified, the transaction's
  token back if nothing changed, the writer's part of the notified log at the committed log.
* **The writer** (`kvWriter s γ log`): the sole writer (`soleWriter`) with the writer's part of
  the notified log (`wlogOwn`); what the apply thread holds.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.Defs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.Writer
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.KVView
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore__Write
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchableStoreTxnWrite__End

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace txn

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section kv
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

/-- The writer's part of a watchable store's notified log, unfolded. -/
theorem wlogOwn_watch (s : Loc) (γ : mvcc.StoreNames) (L : mvcc.Log) (h : γ.watchQ = true) :
    wlogOwn (GF := GF) s γ L ⊣⊢ ∃ (ws : Loc) (γw : mvcc.WsNames), ⌜γw.st = γ⌝ ∗
      mvcc.isWatchableStore ws s γw ∗ monoListAuthOwn γw.wlog (1 : Qp).half L ∗ mvcc.idxCert γ.idx L := by
  unfold wlogOwn; rw [h]; simp only [↓reduceIte]; exact .rfl

/-! ## The KV -/

/-- A KV is an interface value that is not `nil`. -/
theorem isKV_ok (kv : GoInterface) (s : Loc) (γ : mvcc.StoreNames) :
    isKV (GF := GF) kv s γ ⊢ ⌜∃ (ty : go.GoType) (v : val), kv = interface.mkOk ty v⌝ := by
  iintro H
  iunfold isKV at H
  icases H with (⟨%H, -⟩ | ⟨%ws, %γw, %H, -⟩)
  · ipureintro; exact ⟨_, _, H⟩
  · ipureintro; exact ⟨_, _, H.1⟩

/-- The KV is over the store (`mvcc.kvOver`), the store's facts. -/
theorem isKV_kvOver (kv : GoInterface) (s : Loc) (γ : mvcc.StoreNames) :
    isKV (GF := GF) kv s γ ⊢ mvcc.kvOver kv s ∗ mvcc.isStore s γ := by
  iintro #H
  iunfold isKV at H
  icases H with (⟨%H, #Hs, -⟩ | ⟨%ws, %γw, %H, #Hws⟩)
  · iframe Hs
    iunfold mvcc.kvOver; ileft; ipureintro; exact H
  · obtain ⟨H, hγ⟩ := H
    subst hγ
    iunfold mvcc.isWatchableStore at Hws
    iNamed Hws
    iframe Hs
    iunfold mvcc.kvOver; iright; iexists ws; iframe Hst; ipureintro; exact H

/-- **`kv.Read(mode, trace)` at either store**: the frozen `store.Read` (a reader of a store
never compacted). -/
theorem kv_Read (hRead : mvcc.store.Read.spec (GF := GF) (hG := hG))
    (ty : go.GoType) (v : val) (s : Loc) (γ : mvcc.StoreNames) (mode : w32) (trace : Loc) (m : Nat)
    (log₀ : mvcc.Log) (te : Bool) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
        isKV (interface.mkOk ty v) s γ ∗ mvcc.storeReader s γ ∗ ownToks γ.revs m ∗
        mvcc.idxCert γ.idx log₀ ∗ ⌜trace ≠ null⌝ ∗ traceutil.ownTrace trace te }}
      (App (App (Val #(methods ty go!"Read" v)) (Val #mode)) (Val #trace))
    {{ (mw : Loc), RET #(interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw);
        ∃ (log : mvcc.Log) (rev : w64), mvcc.isTxnRead mw s γ trace log rev ∗ ownToks γ.revs m ∗
          mvcc.certOk γ log ∗ ⌜log₀ <+: log ∧ log.length + m + 3 ≤ 2 ^ 63⌝ }} := by
  have hRF := mvcc.store.Read.spec_frozen hRead
  iintro %Φ ⟨#Hpkg, #Hkv, Hrd, Hm, #Hc0, %Ht, Htrc⟩ HΦ
  ihave ⟨#Hko, #Hs⟩ := isKV_kvOver _ s γ $$ Hkv
  iapply mvcc.kvOver_read_wp ty v s mode trace
  iframe Hko
  iapply (hRF s γ mode trace m log₀ te) $$ [Hrd Hm Htrc] HΦ
  iframe Hrd Hm Htrc; iframe #; ipureintro; exact Ht

/-! ## The write transaction -/

/-- **What `End` needs beside the write transaction** `interface.mkOk tyX vX` over `mw` at the
committed log `ilog`: nothing for the plain store's (`γ.watchQ = false`); for the watchable
store's, its read-only struct, the watchable store over `s`, the writer's half of its notified
log and the certificate of `ilog`. -/
def twEnd (s : Loc) (γ : mvcc.StoreNames) (tyX : go.GoType) (vX : val) (mw : Loc)
    (ilog : mvcc.Log) : IProp GF :=
  iprop(⌜tyX = go.GoType.PointerType metricsTxnWrite.ty ∧ vX = #mw ∧ γ.watchQ = false⌝ ∨
    ∃ (twl ws : Loc) (γw : mvcc.WsNames),
      ⌜tyX = go.GoType.PointerType watchableStoreTxnWrite.ty ∧ vX = #twl ∧ γw.st = γ⌝ ∗
      twl ↦□ ({ TxnWrite' := interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw,
                s' := ws } : watchableStoreTxnWrite) ∗
      mvcc.isWatchableStore ws s γw ∗ monoListAuthOwn γw.wlog (1 : Qp).half ilog ∗
      mvcc.idxCert γ.idx ilog)

/-- The write transaction is over `mw` (`twWrap`, persistent). -/
theorem twEnd_wrap (s : Loc) (γ : mvcc.StoreNames) (tyX : go.GoType) (vX : val) (mw : Loc)
    (ilog : mvcc.Log) :
    twEnd (GF := GF) s γ tyX vX mw ilog ⊢ twEnd s γ tyX vX mw ilog ∗ mvcc.twWrap tyX vX mw := by
  iintro H
  iunfold twEnd at H
  icases H with (%H | ⟨%twl, %ws, %γw, %H, #Htw, Hrest⟩)
  · obtain ⟨h1, h2, h3⟩ := H
    isplitl []
    · iunfold twEnd; ileft; ipureintro; exact ⟨h1, h2, h3⟩
    · iunfold mvcc.twWrap; ileft; ipureintro; exact ⟨h1, h2⟩
  · obtain ⟨h1, h2, h3⟩ := H
    isplitl [Hrest]
    · iunfold twEnd; iright; iexists twl, ws, γw; iframe Htw Hrest; ipureintro; exact ⟨h1, h2, h3⟩
    · iunfold mvcc.twWrap; iright; iexists twl, ws; iframe Htw; ipureintro; exact ⟨h1, h2⟩

/-- Two watchable stores over the same store are the same (its `ReadView` points at it). -/
theorem watchableStore_unique (ws1 ws2 s : Loc) (γ1 γ2 : mvcc.WsNames) :
    mvcc.isWatchableStore (GF := GF) ws1 s γ1 ∗ mvcc.isWatchableStore ws2 s γ2 ⊢ ⌜ws1 = ws2⌝ := by
  iintro ⟨#H1, #H2⟩
  iunfold mvcc.isWatchableStore at H1 H2
  icases H1 with ⟨%vc1, %stc1, %rv1, %γv1, H1⟩
  icases H2 with ⟨%vc2, %stc2, %rv2, %γv2, H2⟩
  iNamedSuffix H1 "1"
  iNamedSuffix H2 "2"
  icombine Hrv1 Hrv2 gives %Hrv
  have hrv : rv1 = rv2 := by
    simp only [interface.mkOk, GoInterface.ok.injEq] at Hrv
    injection Hrv with _ h
    exact go.intoVal_inj (V := Loc) h
  subst hrv
  icombine Hrvkv1 Hrvkv2 gives %Hkv
  ipureintro
  simp only [interface.mkOk, GoInterface.ok.injEq] at Hkv
  injection Hkv with _ h
  exact go.intoVal_inj (V := Loc) h

/-- **`kv.Write(trace)` at either store**: a write transaction `interface.mkOk tyX vX` over the
`*metricsTxnWrite` `mw` at the committed log `ilog`, the caller's `m` tokens back and what `End`
needs beside it (`twEnd`). For a watchable store the caller is the sole writer of the notified
log `Lw` (`wlogOwn`, its `m` tokens all but the transaction's: the transaction is at `Lw`).
`LockInsideApply` runs the store's hook on the caller's `Pre` (`store.Write`). -/
theorem kv_Write (hW : mvcc.store.Write.spec (GF := GF) (hG := hG))
    (hWW : mvcc.watchableStore.Write.spec (GF := GF) (hG := hG))
    (ty : go.GoType) (v : val) (s : Loc) (γ : mvcc.StoreNames) (trace : Loc)
    (P Pre Q : IProp GF) (f : val) (te : Bool) (m : Nat) (Lw : mvcc.Log) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
        isKV (interface.mkOk ty v) s γ ∗ mvcc.storeReader s γ ∗ mvcc.revToken γ ∗
        mvcc.storeWT γ ∗ ownToks γ.revs m ∗ wlogOwn s γ Lw ∗
        ⌜γ.watchQ = true → m + 1 = soleBudget Lw ∧ Lw.length + 4 ≤ 2 ^ 63⌝ ∗ ⌜trace ≠ null⌝ ∗
        mvcc.hookIs γ P f ∗ Pre ∗ □ ({{ P ∗ Pre }} (App (Val f) (Val #())) {{ RET #(); Q }}) ∗
        traceutil.ownTrace trace te }}
      (App (Val #(methods ty go!"Write" v)) (Val #trace))
    {{ (tyX : go.GoType) (vX : val), RET #(interface.mkOk tyX vX);
        ∃ (ilog : mvcc.Log) (mw : Loc),
          mvcc.isTxnWrite mw s γ trace ilog [] (W64 0) (W64 0) (W64 0) ∗
          twEnd s γ tyX vX mw ilog ∗ ownToks γ.revs m ∗ ⌜γ.watchQ = true → ilog = Lw⌝ ∗ Q ∗
          mvcc.hookIs γ P f }} := by
  have hWF := mvcc.store.Write.spec_frozen hW
  iintro %Φ ⟨#Hpkg, #Hkv, Hrd, Htok, Hwt, Hm, Hwl, %Hsole, %Ht, Hhook, Hpre, #Htr, Htrc⟩ HΦ
  iunfold isKV at Hkv
  icases Hkv with (⟨%Hkv, #Hs, %Hwq⟩ | ⟨%ws, %γw, %Hkv, #Hws⟩)
  · -- the plain store
    simp only [interface.mkOk, GoInterface.ok.injEq] at Hkv
    injection Hkv with h1 h2
    subst h1 h2
    iapply (hWF s γ trace P Pre Q f te) $$ [Hrd Htok Hwt Hpre Htrc Hhook]
    · iframe Hrd Htok Hwt Hpre Htrc Hhook; iframe #; ipureintro; exact Ht
    inext
    iintro %mw ⟨⟨%ilog, Htx⟩, HQ, Hhook⟩
    iapply HΦ
    iexists ilog, mw
    iframe Htx Hm HQ Hhook
    isplitl []
    · iunfold twEnd; ileft; ipureintro; exact ⟨rfl, rfl, Hwq⟩
    · ipureintro; intro h; rw [Hwq] at h; cases h
  · -- the watchable store: its writer's half of the notified log
    obtain ⟨Hkv, hγ⟩ := Hkv
    simp only [interface.mkOk, GoInterface.ok.injEq] at Hkv
    injection Hkv with h1 h2
    subst h1 h2 hγ
    ihave #Hws' := Hws
    iunfold mvcc.isWatchableStore at Hws'
    icases Hws' with ⟨%vc, %stc, %rv, %γv, Hws'⟩
    iNamed Hws'
    obtain ⟨hb, hlen⟩ := Hsole Hwq
    icases (wlogOwn_watch s γw.st Lw Hwq).1 $$ Hwl with ⟨%ws2, %γw2, %hγ2, #Hws2, Hhalf, #HcL⟩
    ihave %Hws := watchableStore_unique ws ws2 s γw γw2 $$ [$Hws $Hws2]
    subst Hws
    -- the sole writer of the notified log, at `γw2`'s names
    ihave Hww : mvcc.watchWriter γw2 Lw $$ [Htok Hm Hhalf]
    · iunfold mvcc.watchWriter
      rw [hγ2]
      iframe HcL Hhalf
      have hb' : mvcc.wBudget Lw = m + 1 := by unfold mvcc.wBudget; unfold soleBudget at hb; omega
      rw [hb']
      unfold mvcc.revToken
      iapply (ownToks_add 1 m γw.st.revs).2
      iframe Hm Htok
    iapply (hWW ws s γw2 trace Lw P Pre Q f te) $$ [Hrd Hwt Hww Hpre Htrc Hhook]
    · rw [hγ2]; iframe Hrd Hwt Hww Hpre Htrc Hhook; iframe #; ipureintro; exact ⟨hlen, Ht⟩
    inext
    iintro %tw ⟨Htw, HQ, Hhook⟩
    iunfold mvcc.isWatchTxnWrite at Htw
    iNamed Htw
    iapply HΦ
    iexists Lw, mw
    rw [hγ2]
    iframe Htx HQ Hhook
    isplitr [Htoks]
    · iunfold twEnd; iright; iexists tw, ws, γw2
      rw [hγ2]
      iframe Htw Hws Hwlog Hcert
      ipureintro; exact ⟨rfl, rfl, rfl⟩
    isplitl [Htoks]
    · have hb' : mvcc.wBudget Lw - 1 = m := by unfold mvcc.wBudget; unfold soleBudget at hb; omega
      rw [hb']; iexact Htoks
    · ipureintro; intro _; rfl

/-- **The write transaction's `End` at either store**: the store's reader slots back, the trace
owned, the committed log `commitLog ilog pend` certified, the transaction's token back if nothing
changed, the caller's `m` tokens back and the writer's part of the notified log at the committed
log. The caller's `m` tokens are, for a watchable store, all but the transaction's (its
`watchWriter`). `Unlock` takes the batch lock's invariant `P` back (the store's, `hookIs`). -/
theorem tw_End (hEnd : mvcc.metricsTxnWrite.End.spec (GF := GF) (hG := hG))
    (hWEnd : mvcc.watchableStoreTxnWrite.End.spec (GF := GF) (hG := hG))
    (tyX : go.GoType) (vX : val) (s : Loc) (γ : mvcc.StoreNames) (trace mw : Loc)
    (ilog : mvcc.Log) (pend : List mvcc.Change) (puts deletes putSize : w64) (m : Nat)
    (P : IProp GF) (f : val) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
        mvcc.isTxnWrite mw s γ trace ilog pend puts deletes putSize ∗ twEnd s γ tyX vX mw ilog ∗
        ownToks γ.revs m ∗ ⌜γ.watchQ = true → m + 1 = soleBudget ilog⌝ ∗
        mvcc.hookIs γ P f ∗ P ∗ mvcc.certOkNext γ ilog pend }}
      (App (Val #(methods tyX go!"End" vX)) (Val #()))
    {{ RET #(); mvcc.storeReader s γ ∗ (∃ te : Bool, traceutil.ownTrace trace te) ∗
        mvcc.idxCert γ.idx (mvcc.commitLog ilog pend) ∗
        (if pend = [] then mvcc.revToken γ else iprop(True)) ∗ ownToks γ.revs m ∗
        wlogOwn s γ (mvcc.commitLog ilog pend) ∗ mvcc.hookIs γ P f }} := by
  have hEF := mvcc.metricsTxnWrite.End.spec_frozen hEnd
  iintro %Φ ⟨#Hpkg, Htx, Hte, Hm, %Hsole, Hhook, HP, #Hok⟩ HΦ
  -- the hook's facts kept, its fragment given back by `End` (D22 receiver epochs, S5b)
  icases (mvcc.hookIs_split γ P f).1 $$ Hhook with ⟨#HhookOk, Hfrag⟩
  ihave Hhook : mvcc.hookIs γ P f $$ [Hfrag]
  · iapply (mvcc.hookIs_split γ P f).2; iframe HhookOk Hfrag
  iunfold twEnd at Hte
  icases Hte with (%H | ⟨%twl, %ws, %γw, %H, #Htw, #Hws, Hhalf, #Hcert⟩)
  · -- the plain store's `metricsTxnWrite.End`
    obtain ⟨h1, h2, hwq⟩ := H
    subst h1 h2
    ihave Htx : mvcc.isTxn mw s γ trace (.write ilog pend puts deletes putSize) $$ [Htx]
    · simp only [mvcc.isTxn]; iexact Htx
    ihave Htx := mvcc.isTxn_toEnd _ _ _ _ $$ Htx
    iapply (hEF trace mw s γ _) $$ [Htx HP Hhook]
    · iframe Htx; iframe #
      iapply (mvcc.txnEndPre_write_plain _ _ _ _ _ _ _ _ hwq); iframe Hhook HP Hok
    inext
    iintro ⟨Hrd, Hpost, %te', Htrc⟩
    ihave ⟨#Hc, Htok, Hfrag⟩ := mvcc.txnEndPost_plain _ _ _ _ _ _ hwq $$ Hpost
    iapply HΦ
    iframe Hrd Hc Htok Hm
    isplitl [Htrc]
    · iexists te'; iexact Htrc
    isplitl []
    · iapply wlogOwn_plain s γ _ hwq
    iapply (mvcc.hookIs_split γ P f).2; iframe HhookOk Hfrag
  · -- the watchable store's `End`: the watchers notified under its lock
    obtain ⟨h1, h2, hγ⟩ := H
    subst h1 h2 hγ
    ihave #Hws' := Hws
    iunfold mvcc.isWatchableStore at Hws'
    icases Hws' with ⟨%vc, %stc, %rv, %γv, Hws'⟩
    iNamed Hws'
    have hb := Hsole Hwq
    have hb' : mvcc.wBudget ilog - 1 = m := by unfold mvcc.wBudget; unfold soleBudget at hb; omega
    ihave Hw : mvcc.isWatchTxnWrite twl ws s γw trace ilog pend puts deletes putSize $$ [Htx Hm Hhalf]
    · iunfold mvcc.isWatchTxnWrite
      iexists mw
      simp only [named]
      rw [hb']
      iframe Htw Hws Htx Hcert Hm Hhalf
    iapply (hWEnd trace twl ws s γw ilog pend puts deletes putSize P f) $$ [Hw HP Hhook]
    · iframe Hw HP Hhook; iframe #
    inext
    iintro ⟨Hrd, #Hc, Hww, Htrc, Hfrag⟩
    iunfold mvcc.watchWriter at Hww
    icases Hww with ⟨-, Htoks, Hhalf⟩
    iapply HΦ
    iframe Hrd Hc Htrc
    have e : mvcc.wBudget (mvcc.commitLog ilog pend) = m + (if pend = [] then 1 else 0) := by
      unfold mvcc.wBudget mvcc.commitLog; unfold soleBudget at hb
      by_cases hp : pend = [] <;> simp [hp] <;> omega
    irevert Htoks
    rw [e]
    iintro Htoks
    icases (ownToks_add (if pend = [] then 1 else 0) m γw.st.revs).1 $$ Htoks with ⟨Hm, H1⟩
    iframe Hm
    isplitl [H1]
    · by_cases hp : pend = []
      · simp only [hp, ↓reduceIte]; unfold mvcc.revToken; iexact H1
      · simp only [hp, ↓reduceIte]; itrivial
    isplitr [Hfrag]
    · iapply (wlogOwn_watch s γw.st _ Hwq).2
      iexists ws, γw
      iframe Hws Hhalf Hc
      ipureintro; rfl
    iapply (mvcc.hookIs_split γw.st P f).2; iframe HhookOk Hfrag

end kv

end txn
end EtcdGrove
end Perennial

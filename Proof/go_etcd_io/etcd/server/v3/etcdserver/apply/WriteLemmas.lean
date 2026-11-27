/-
**The writing methods' resources, split** (strict M1, 2026-11-05): `mPreW` (the chain's
precondition of a method whose component writes the backend) split into the writer's half (for
`newHeader`), the critical-section contract at the backend `B`'s lock, the backend's write and read
tokens and its tie (what a component's write takes, `Contracts.lean`), the chain's resources and the
rest of the thread's KV resources (`kvRest`); and `mPostW` rebuilt from them. Lean-first (no Rocq
counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Chain
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.WinLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apply

open Iris Iris.BI Iris.ProofMode
open mvcc.api (mvccBackend hookIs mvccLeases)

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- **The thread's KV resources but the writer's half and the tie**, at the backend `B`: the
backend's whole share and its hook, the live leases, the auth store's reader resource. -/
def kvRest (E : AEnv GF) (log : mvcc.Log) (B : mvcc.KBReal) : IProp GF :=
  iprop(mvccBackend E.γ 1 B (E.Pk B) ∗ hookIs B E.f ∗ leasesLive E (mvcc.stateAfter log) ∗ E.RD)

/-- `mPreW`, split (see the file header). -/
theorem mPreW_split (E : AEnv GF) (c : Chain) (a : GoInterface)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (log : mvcc.Log) (Pre Q Post : IProp GF) :
    mPreW E c a info log Pre Q Post ⊢ ∃ (cr : Int) (B : mvcc.KBReal), srvApi.wStQ E.γs E.stq log cr ∗
      srvApi.csContractA (E.Pk B) E.f Pre Q Post ∗ bkWT B ∗ bkRT B ∗ E.BkTie B ∗
      chainRes c a info ∗ kvRest E log B := by
  iintro H
  iunfold mPreW at H
  icases H with ⟨⟨%cr, Hw⟩, Hll, Hrd, Hres, %B, Hbk, Hhk, Htie, Hwt, Hrt, Hcs⟩
  iexists cr, B
  iframe Hw Hcs Hwt Hrt Htie Hres
  iunfold kvRest
  iframe Hbk Hhk Hll Hrd

/-- The thread's KV resources from the split. -/
theorem kvOwn_of_split (E : AEnv GF) (log : mvcc.Log) (B : mvcc.KBReal) (cr : Int) :
    srvApi.wStQ E.γs E.stq log cr ∗ E.BkTie B ∗ kvRest E log B ⊢ kvOwn E log := by
  iintro ⟨Hw, Htie, Hr⟩
  iunfold kvRest at Hr
  icases Hr with ⟨Hbk, Hhk, Hll, Hrd⟩
  iunfold kvOwn
  isplitl [Hw]
  · iexists cr; iexact Hw
  isplitl [Hbk Hhk Htie]
  · iunfold kvBk; iexists B; iframe Hbk Hhk Htie
  iframe Hll Hrd

/-- A put's pending changes at the writer's state: none (the key missing for an ignore flag), else
its one change. -/
theorem putPend_cases (o : OpFull) (log : mvcc.Log) (c : Int) :
    (txn.needsPrev o = true ∧ mvcc.findKey o.key (mvcc.stateAfter log) = none ∧
        txn.putPend o (srvApi.stAt log c) = []) ∨
      ((txn.needsPrev o = true → (mvcc.findKey o.key (mvcc.stateAfter log)).isSome) ∧
        txn.putPend o (srvApi.stAt log c) =
          [txn.putChangeOf o (mvcc.findKey o.key (mvcc.stateAfter log))]) := by
  unfold txn.putPend
  simp only [srvApi.stAt]
  by_cases h : txn.needsPrev o = true ∧ mvcc.findKey o.key (mvcc.stateAfter log) = none
  · left; exact ⟨h.1, h.2, by simp [h]⟩
  · right
    refine ⟨fun hn => ?_, by simp [h]⟩
    cases hf : mvcc.findKey o.key (mvcc.stateAfter log) with
    | none => exact absurd ⟨hn, hf⟩ h
    | some _ => rfl

/-- **A put's lessor-window target** (auth-lease S4 item 7b, the applier at a window): with the request's lease live
(or none) at the live set `T`, the window's target is the item map after the put's outcome at the writer's state. -/
theorem putWinTgt (w : Option lease.LWin) (rq : IRRModel) (o : OpFull) (log : mvcc.Log) (c : Int) (T : List w64)
    (h : winTgt w rq log T) (hrq : rq.put = some o) (hk : dispatchKind rq = .put)
    (hl : o.leaseID = W64 0 ∨ o.leaseID ∈ T) :
    ∀ (s : Nat) (T' : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64), w = some (s, T') →
      T' = mvcc.leaseItemsOf (mvcc.stateAfter (mvcc.commitLog log (txn.putPend o (srvApi.stAt log c)))) := by
  intro s T' hw
  rcases putPend_cases o log c with ⟨hn, hf, hp⟩ | ⟨hn, hp⟩
  · rw [hp]
    have := h s T' hw (.rejected .backend)
      (by unfold backendStep; rw [hk]; exact ⟨o, hrq, Or.inr (Or.inl ⟨hn, hf, rfl⟩)⟩)
      (by simp only [leaseExactL, hk]; intro op hop; rw [hrq] at hop; cases hop
          exact ⟨fun _ => rfl, fun _ => Or.inr ⟨hn, hf⟩⟩)
    simpa [Outcome.logAfter, mvcc.commitLog] using this
  · rw [hp]
    have := h s T' hw (.applied (log ++ [[txn.putChangeOf o (mvcc.findKey o.key (mvcc.stateAfter log))]]) false)
      (by unfold backendStep; rw [hk]; exact ⟨o, hrq, Or.inr (Or.inr ⟨hn, rfl⟩)⟩)
      (by simp only [leaseExactL, hk]; intro op hop; rw [hrq] at hop; cases hop
          exact ⟨fun h => (hl.elim h.1 h.2).elim, fun h => by cases h⟩)
    simpa [Outcome.logAfter, mvcc.commitLog] using this

/-- **A put that writes moves the items toward the window's target** (item 7b): `putAUW`'s begin premise. -/
theorem putWinMove (w : Option lease.LWin) (rq : IRRModel) (o : OpFull) (log : mvcc.Log) (T : List w64)
    (h : winTgt w rq log T) (hrq : rq.put = some o) (hk : dispatchKind rq = .put)
    (hl : o.leaseID = W64 0 ∨ o.leaseID ∈ T)
    (hn : txn.needsPrev o = true → (mvcc.findKey o.key (mvcc.stateAfter log)).isSome) :
    Perennial.EtcdGrove.lease.winMove w (mvcc.leaseItemsOf (mvcc.stateAfter log))
      (txn.putItemsOf (mvcc.leaseItemsOf (mvcc.stateAfter log)) o) := by
  cases w with
  | none => exact Perennial.EtcdGrove.lease.winMove_none _ _
  | some v =>
    obtain ⟨s, T'⟩ := v
    have ht := h s T' rfl (.applied (log ++ [[txn.putChangeOf o (mvcc.findKey o.key (mvcc.stateAfter log))]]) false)
      (by unfold backendStep; rw [hk]; exact ⟨o, hrq, Or.inr (Or.inr ⟨hn, rfl⟩)⟩)
      (by simp only [leaseExactL, hk]; intro op hop; rw [hrq] at hop; cases hop
          exact ⟨fun h => (hl.elim h.1 h.2).elim, fun h => by cases h⟩)
    simp only [Outcome.logAfter] at ht
    have e1 : mvcc.commitLog log [txn.putChangeOf o (mvcc.findKey o.key (mvcc.stateAfter log))] =
        log ++ [[txn.putChangeOf o (mvcc.findKey o.key (mvcc.stateAfter log))]] := by
      unfold mvcc.commitLog; simp
    have e0 : mvcc.commitLog log [] = log := by unfold mvcc.commitLog; simp
    rw [ht, ← e1, ← txn.pendItems_commitLog, txn.pendItems_putChangeOf, txn.pendItems_commitLog, e0]
    exact txn.winMove_to_target s _ _

/-- **A range delete's lessor-window target** (item 7b): the window's target is the item map after the delete. -/
theorem delWinTgt (w : Option lease.LWin) (rq : IRRModel) (o : OpFull) (log : mvcc.Log) (T : List w64)
    (h : winTgt w rq log T) (hrq : rq.deleteRange = some o) (hk : dispatchKind rq = .deleteRange) :
    ∀ (s : Nat) (T' : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64), w = some (s, T') →
      T' = mvcc.leaseItemsOf (mvcc.stateAfter (mvcc.commitLog log (txn.delChanges (mvcc.stateAfter log) o))) := by
  intro s T' hw
  have := h s T' hw (.applied (mvcc.commitLog log (txn.delChanges (mvcc.stateAfter log) o)) false)
    (by unfold backendStep; rw [hk]; exact ⟨o, hrq, rfl⟩)
    (leaseExactL_other T rq log _ (by rw [hk]; decide) (by rw [hk]; decide))
  simpa [Outcome.logAfter] using this

/-- **A range delete's window drops its range's items** (item 7b): `txn.DeleteRange.spec`'s `winDrops`. -/
theorem delWinDrops (w : Option lease.LWin) (rq : IRRModel) (o : OpFull) (log : mvcc.Log) (T : List w64)
    (h : winTgt w rq log T) (hrq : rq.deleteRange = some o) (hk : dispatchKind rq = .deleteRange) :
    Perennial.EtcdGrove.lease.winDrops w (mvcc.leaseItemsOf (mvcc.stateAfter log)) (txn.delSelOf o) := by
  intro v hv it hsel hpres
  obtain ⟨s, T'⟩ := v
  have ht := delWinTgt w rq o log T h hrq hk s T' hv
  simp only at ht ⊢
  subst ht
  rw [txn.stateAfter_commitLog]
  simp only [mvcc.leaseItemsOf_lookup] at hpres ⊢
  obtain ⟨kv, hkv⟩ : ∃ kv, mvcc.findKey it.Key' (mvcc.stateAfter log) = some kv := by
    cases h' : mvcc.findKey it.Key' (mvcc.stateAfter log) with
    | none => rw [h'] at hpres; exact absurd rfl hpres
    | some kv => exact ⟨kv, rfl⟩
  have hmem : kv ∈ mvcc.stateAfter log := List.mem_of_find?_eq_some hkv
  have hkk : kv.key = it.Key' := by simpa using List.find?_some hkv
  have hin : kv ∈ rangeIn (mvcc.stateAfter log) o := by
    unfold rangeIn
    rw [List.mem_filter]
    exact ⟨hmem, by rw [hkk]; exact (txn.delSelOf_iff o it).1 hsel⟩
  have hks : it.Key' ∈ (rangeIn (mvcc.stateAfter log) o).map EtcdKv.key := by
    rw [← hkk]; exact List.mem_map_of_mem hin
  have hdel : txn.delChanges (mvcc.stateAfter log) o =
      ((rangeIn (mvcc.stateAfter log) o).map EtcdKv.key).map .del := by
    unfold txn.delChanges; rw [List.map_map]; rfl
  rw [hdel, txn.findKey_applyChanges_dels_mem _ _ _ _ hks]
  rfl

/-- **A writing transaction's lessor-window target** (item 7b): with its checks passed at the live set `L`, the
window's target is the item map after its run. -/
theorem txnWinTgt (w : Option lease.LWin) (rq : IRRModel) (t : TxnModel) (log : mvcc.Log) (L : List w64)
    (h : winTgt w rq log L) (hrq : rq.txn = some t) (hk : dispatchKind rq = .txn)
    (hro : txn.txnReadonly t = false)
    (hig : txn.PathsIgnOk (mvcc.stateAfter log) (t.branch (txn.txnOk (mvcc.stateAfter log) t)) ∧
      txn.PathsLeaseOk (mvcc.stateAfter log) L (t.branch (txn.txnOk (mvcc.stateAfter log) t))) :
    ∀ (s : Nat) (T' : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64), w = some (s, T') →
      T' = mvcc.leaseItemsOf (mvcc.stateAfter (mvcc.commitLog log (txn.txnChs log t))) := by
  intro s T' hw
  have := h s T' hw (.applied (mvcc.commitLog log
      (txn.srvRunTxn (W64 (log.length : Int)) (mvcc.stateAfter log) t).2.1) false)
    (by unfold backendStep; rw [hk]
        exact ⟨t, hrq, Or.inr ⟨rfl, fun h => (by rw [hro] at h; cases h), hig.1⟩⟩)
    (by simp only [leaseExactL, hk]
        intro t' ht'; rw [hrq] at ht'; cases ht'
        exact ⟨fun _ => hig.2, fun _ h => by cases h⟩)
  simp only [Outcome.logAfter] at this
  exact this

/-- **A writing transaction's run is within the window** (item 7b): `txnBeginAUW`'s begin premise, from its keys'
distinctness (`txnKeysNodup`, etcd's `checkIntervals`). -/
theorem txnWinOps (w : Option lease.LWin) (rq : IRRModel) (t : TxnModel) (log : mvcc.Log) (L : List w64)
    (h : winTgt w rq log L) (hrq : rq.txn = some t) (hk : dispatchKind rq = .txn)
    (hro : txn.txnReadonly t = false) (hnd : txn.txnKeysNodup t)
    (hig : txn.PathsIgnOk (mvcc.stateAfter log) (t.branch (txn.txnOk (mvcc.stateAfter log) t)) ∧
      txn.PathsLeaseOk (mvcc.stateAfter log) L (t.branch (txn.txnOk (mvcc.stateAfter log) t))) :
    txn.WinOps w (mvcc.stateAfter log) (W64 (log.length : Int)) (mvcc.stateAfter log)
      (t.branch (txn.txnOk (mvcc.stateAfter log) t)) := by
  cases w with
  | none => exact txn.winOps_none _ _ _ _
  | some v =>
    obtain ⟨s, T'⟩ := v
    rw [txnWinTgt _ rq t log L h hrq hk hro hig s T' rfl, txn.stateAfter_commitLog]
    exact txn.winOps_txn_of_nodup s log t
      (by simpa [txn.txnChs, txn.srvRunTxn] using hnd (mvcc.stateAfter log) _ (mvcc.stateAfter_sorted log))

/-- The thread's KV resources at the live set `L`, from the split's pieces (auth-lease S3a). -/
theorem kvOwnAt_of_split (E : AEnv GF) (log : mvcc.Log) (B : mvcc.KBReal) (cr : Int) (L : List w64) :
    (srvApi.wStQ E.γs E.stq log cr ∗ E.Wt E.win) ∗ E.BkTie B ∗ mvccBackend E.γ 1 B (E.Pk B) ∗ hookIs B E.f ∗
      txn.leasesKnown L (mvcc.stateAfter log) ∗
      lease.lessorUserW (mvccLeases E.γ) L (mvcc.leaseItemsOf (mvcc.stateAfter log)) E.win ∗ ltHalf E L ∗
      E.RD ⊢ kvOwnAt E log L := by
  iintro ⟨⟨Hw, HWt⟩, Htie, Hbk, Hhk, Hk, Hu, Hlt, Hrd⟩
  iunfold kvOwnAt
  isplitl [Hw]
  · iexists cr; iexact Hw
  isplitl [Hbk Hhk Htie]
  · iunfold kvBk; iexists B; iframe Hbk Hhk Htie
  iframe Hk Hu Hlt HWt Hrd

/-- **Two writer halves at different logs are impossible** (each holds a half of `γs.st`). -/
theorem wSt_ne_false (γs : srvApi.KVSNames) {q q' : Qp} (l l' : mvcc.Log) (c c' : Int) (h : l ≠ l') :
    srvApi.wStQ (GF := GF) γs q l c ∗ srvApi.wStQ γs q' l' c' ⊢ False := by
  unfold srvApi.wStQ
  iintro ⟨⟨Hs, -⟩, ⟨Hs', -⟩⟩
  icombine Hs Hs' gives %H
  exfalso
  have := H.2
  simp only [Prod.mk.injEq] at this
  exact h this.1

/-- **`mPostW` at the backend**, from the split's pieces, the caller's outcome and the reader
token back. -/
theorem mPostW_backend (E : AEnv GF) (a : GoInterface) (log : mvcc.Log) (Pre Post : IProp GF)
    (B : mvcc.KBReal) (cr : Int) :
    srvApi.wStQ E.γs E.stq log cr ∗ E.BkTie B ∗ kvRest E log B ∗ (Post ∨ Pre) ∗ bkRT B ⊢
      mPostW E .backend a log Pre Post := by
  iintro ⟨Hw, Htie, Hr, HPP, Hrt⟩
  icases bkRTOf_intro E B $$ [$Htie $Hrt] with ⟨Htie, Hrt⟩
  iunfold mPostW
  isplitr [Hrt]
  · iapply mPost_backend
    iframe HPP
    iapply kvOwn_of_split E log B cr
    iframe Hw Htie Hr
  · iexact Hrt

/-- `mPreV` (the cluster methods', with `v3`), split as `mPreW`. -/
theorem mPreV_split (v3 : Bool) (E : AEnv GF) (c : Chain) (a : GoInterface)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (log : mvcc.Log) (Pre Q Post : IProp GF) :
    mPreV v3 E c a info log Pre Q Post ⊢ ∃ (cr : Int) (B : mvcc.KBReal), srvApi.wStQ E.γs E.stq log cr ∗
      cPre v3 (E.Pk B) E.f Pre Q Post ∗ bkWT B ∗ bkRT B ∗ E.BkTie B ∗
      chainRes c a info ∗ kvRest E log B := by
  iintro H
  iunfold mPreV at H
  icases H with ⟨⟨%cr, Hw⟩, Hll, Hrd, Hres, %B, Hbk, Hhk, Htie, Hwt, Hrt, Hcs⟩
  iexists cr, B
  iframe Hw Hcs Hwt Hrt Htie Hres
  iunfold kvRest
  iframe Hbk Hhk Hll Hrd

/-- **`mPostV`** from the split's pieces, the writer's outcome and the reader token back. -/
theorem mPostV_of (v3 : Bool) (E : AEnv GF) (c : Chain) (a : GoInterface)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (log : mvcc.Log) (Pre Post : IProp GF)
    (B : mvcc.KBReal) (cr : Int) (φ : Prop) :
    srvApi.wStQ E.γs E.stq log cr ∗ E.BkTie B ∗ kvRest E log B ∗ chainRes c a info ∗
      cPost v3 Pre Post φ ∗ bkRT B ⊢ mPostV v3 E c a info log Pre Post φ := by
  iintro ⟨Hw, Htie, Hr, Hres, HPP, Hrt⟩
  icases bkRTOf_intro E B $$ [$Htie $Hrt] with ⟨Htie, Hrt⟩
  iunfold mPostV
  iframe Hres HPP
  isplitl [Hw Htie Hr]
  · iapply kvOwn_of_split E log B cr
    iframe Hw Htie Hr
  · iexact Hrt

/-- **`mPre` without the chain's resources** (strict M1, 2026-11-05): what a wrapper passes on
unchanged, or gives back with `Pre` when it rejects (`mPreRest_reject`). -/
def mPreRest (E : AEnv GF) (log : mvcc.Log) (Pre Q Post : IProp GF) : IProp GF :=
  iprop((∃ cr : Int, srvApi.wStQ E.γs E.stq log cr) ∗ leasesLive E (mvcc.stateAfter log) ∗ E.RD ∗
    ∃ B : mvcc.KBReal, mvccBackend E.γ 1 B (E.Pk B) ∗ hookIs B E.f ∗ E.BkTie B ∗
      srvApi.csContractA (E.Pk B) E.f Pre Q Post)

/-- `mPre` is `mPreRest` and the chain's resources. -/
theorem mPre_split_chain (E : AEnv GF) (c : Chain) (a : GoInterface)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (log : mvcc.Log) (Pre Q Post : IProp GF) :
    mPre E c a info log Pre Q Post ⊢ mPreRest E log Pre Q Post ∗ chainRes c a info := by
  iintro H
  iunfold mPre at H
  icases H with ⟨Hw, Hll, Hrd, Hres, Hb⟩
  iunfold mPreRest
  iframe

/-- `mPre` from `mPreRest` and the chain's resources. -/
theorem mPre_of_rest (E : AEnv GF) (c : Chain) (a : GoInterface)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (log : mvcc.Log) (Pre Q Post : IProp GF) :
    mPreRest E log Pre Q Post ∗ chainRes c a info ⊢ mPre E c a info log Pre Q Post := by
  iintro ⟨H, Hres⟩
  iunfold mPreRest at H
  icases H with ⟨Hw, Hll, Hrd, Hb⟩
  iunfold mPre
  iframe

/-- **`mPreRest` at the live set `T`** (auth-lease S3a2): `mPreAt` without the chain's resources. -/
def mPreRestAt (E : AEnv GF) (log : mvcc.Log) (T : List w64) (Pre Q Post : IProp GF) : IProp GF :=
  iprop((∃ cr : Int, srvApi.wStQ E.γs E.stq log cr) ∗ leasesLiveAt E (mvcc.stateAfter log) T ∗ E.RD ∗
    ∃ B : mvcc.KBReal, mvccBackend E.γ 1 B (E.Pk B) ∗ hookIs B E.f ∗ E.BkTie B ∗
      srvApi.csContractA (E.Pk B) E.f Pre Q Post)

/-- `mPreAt` is `mPreRestAt` and the chain's resources. -/
theorem mPreAt_split_chain (E : AEnv GF) (c : Chain) (a : GoInterface)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (log : mvcc.Log) (T : List w64)
    (Pre Q Post : IProp GF) :
    mPreAt E c a info log T Pre Q Post ⊢ mPreRestAt E log T Pre Q Post ∗ chainRes c a info := by
  iintro H
  iunfold mPreAt at H
  icases H with ⟨Hw, Hll, Hrd, Hres, Hb⟩
  iunfold mPreRestAt
  iframe

/-- `mPreAt` from `mPreRestAt` and the chain's resources. -/
theorem mPreAt_of_rest (E : AEnv GF) (c : Chain) (a : GoInterface)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (log : mvcc.Log) (T : List w64)
    (Pre Q Post : IProp GF) :
    mPreRestAt E log T Pre Q Post ∗ chainRes c a info ⊢ mPreAt E c a info log T Pre Q Post := by
  iintro ⟨H, Hres⟩
  iunfold mPreRestAt at H
  icases H with ⟨Hw, Hll, Hrd, Hb⟩
  iunfold mPreAt
  iframe

/-- `mPreRestAt` forgets its live set. -/
theorem mPreRest_of_at (E : AEnv GF) (log : mvcc.Log) (T : List w64) (Pre Q Post : IProp GF) :
    mPreRestAt E log T Pre Q Post ⊢ mPreRest E log Pre Q Post := by
  iintro H
  iunfold mPreRestAt at H
  icases H with ⟨Hw, Hll, Hrd, Hb⟩
  iunfold leasesLiveAt at Hll
  icases Hll with ⟨Hk, Hu, Hlt⟩
  iunfold mPreRest
  iframe Hw Hrd Hb
  iunfold leasesLive
  iexists T
  iframe

/-- The auth store's reader resource and the lease owner's resource at `T` of `mPreRestAt`, lent out
(`mPreRest_lend` at the live set: the lender gives back the same `T`). -/
theorem mPreRestAt_lend (E : AEnv GF) (log : mvcc.Log) (T : List w64) (Pre Q Post : IProp GF) :
    mPreRestAt E log T Pre Q Post ⊢ E.RD ∗
      lease.lessorUserW (mvccLeases E.γ) T (mvcc.leaseItemsOf (mvcc.stateAfter log)) E.win ∗
      (E.RD -∗ lease.lessorUserW (mvccLeases E.γ) T (mvcc.leaseItemsOf (mvcc.stateAfter log)) E.win -∗
        mPreRestAt E log T Pre Q Post) := by
  iintro H
  iunfold mPreRestAt at H
  icases H with ⟨Hw, Hll, Hrd, Hb⟩
  iunfold leasesLiveAt at Hll
  icases Hll with ⟨#Hk, Hu, Hlt⟩
  iframe Hrd Hu
  iintro Hrd Hu
  iunfold mPreRestAt
  iframe Hw Hrd Hb
  iunfold leasesLiveAt
  iframe Hk Hu Hlt

/-- **The `ltHalf` agreement at `mPreAt`'s live set** (`kvOwnAt_ltHalf`'s): in a cluster that grants leases,
`mPreAt`'s live set is the other half's. -/
theorem mPreAt_ltHalf (E : AEnv GF) (c : Chain) (a : GoInterface)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (log : mvcc.Log) (L T : List w64)
    (Pre Q Post : IProp GF) :
    mPreAt E c a info log L Pre Q Post ∗ ltHalf E T ⊢
      ⌜E.lg = true → L = T⌝ ∗ mPreAt E c a info log L Pre Q Post ∗ ltHalf E T := by
  unfold mPreAt leasesLiveAt ltHalf
  cases h : E.lg
  · simp only [Bool.false_eq_true, ↓reduceIte]
    iintro ⟨H, -⟩
    isplitl []
    · ipureintro; intro h'; cases h'
    iframe H
    try itrivial
  · simp only [↓reduceIte]
    iintro ⟨⟨Hw, ⟨Hk, Hu, Hlt, HWt⟩, Hrd, Hres, Hb⟩, HT⟩
    icombine Hlt HT gives %H
    iframe Hw Hk Hu Hlt HWt Hrd Hres Hb HT
    ipureintro; intro _; exact H.2

/-- **`putPre` from the class track's certificate** (auth-lease S3a2, Draft §1's `putPre_of_old`): `certPre`
at every outcome, the request, and `mPre` split at its live set. -/
theorem putPre_of_mPre (E : AEnv GF) (c : Chain) (a : GoInterface)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (r : Loc) (rq : IRRModel) (o : OpFull)
    (log : mvcc.Log) (Pre Q Post : IProp GF) (T0 : List w64)
    (hw : E.lg = true → winTgt E.win rq log T0) (hn : E.lg = false → E.win = none)
    (h : rq.put = some o ∧ dispatchKind rq = .put ∧ putOk log ∧
      o.key.length ≤ etcdKeyMax ∧ o.val.length ≤ etcdKeyMax) :
    certPre E c rq log ∗ txn.putRequestIs r o ∗ mPre E c a info log Pre Q Post ∗ ltHalf E T0 ⊢
      putPre E c a info r rq o log Pre Q Post ∗ ltHalf E T0 := by
  iintro ⟨#Hcp, #Hr, Hm, HT⟩
  ihave ⟨%T, Hm⟩ := (mPre_iff_at E c a info log Pre Q Post).1 $$ Hm
  ihave ⟨%HL, Hm, HT⟩ := mPreAt_ltHalf E c a info log T T0 Pre Q Post $$ [$Hm $HT]
  iframe HT
  iunfold putPre
  isplitr; · ipureintro; exact h
  iframe Hr
  iexists T
  isplitr
  · ipureintro
    cases hlg : E.lg
    · rw [hn hlg]; exact winTgt_none _ _ _
    · rw [HL hlg]; exact hw hlg
  iframe Hm
  iapply certPreT_of_certPre; iexact Hcp

/-- **`txnPre` from the class track's certificate** (as `putPre_of_mPre`). -/
theorem txnPre_of_mPre (E : AEnv GF) (c : Chain) (a : GoInterface)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (r : Loc) (rq : IRRModel) (t : TxnModel)
    (log : mvcc.Log) (Pre Q Post : IProp GF) (T0 : List w64)
    (hw : E.lg = true → winTgt E.win rq log T0) (hn : E.lg = false → E.win = none) (hnd : txn.txnKeysNodup t)
    (h : rq.txn = some t ∧ dispatchKind rq = .txn ∧ txn.TxnPreA log t ∧ putOk log ∧
      t.putsLe etcdKeyMax) :
    certPre E c rq log ∗ txn.txnRequestIs r t ∗ mPre E c a info log Pre Q Post ∗ ltHalf E T0 ⊢
      txnPre E c a info r rq t log Pre Q Post ∗ ltHalf E T0 := by
  iintro ⟨#Hcp, #Hr, Hm, HT⟩
  ihave ⟨%T, Hm⟩ := (mPre_iff_at E c a info log Pre Q Post).1 $$ Hm
  ihave ⟨%HL, Hm, HT⟩ := mPreAt_ltHalf E c a info log T T0 Pre Q Post $$ [$Hm $HT]
  iframe HT
  iunfold txnPre
  isplitr; · ipureintro; exact h
  iframe Hr
  iexists T
  isplitr
  · ipureintro
    refine ⟨?_, hnd⟩
    cases hlg : E.lg
    · rw [hn hlg]; exact winTgt_none _ _ _
    · rw [HL hlg]; exact hw hlg
  iframe Hm
  iapply certPreT_of_certPre; iexact Hcp

/-- **A rejection**: the thread's KV resources and `Pre` back. -/
theorem mPreRest_reject (E : AEnv GF) (log : mvcc.Log) (Pre Q Post : IProp GF) :
    mPreRest E log Pre Q Post ⊢ kvOwn E log ∗ Pre := by
  iintro H
  iunfold mPreRest at H
  icases H with ⟨Hw, Hll, Hrd, %B, Hbk, Hhk, Htie, Hcs⟩
  iunfold srvApi.csContractA at Hcs
  icases Hcs with ⟨HPre, -, -⟩
  iframe HPre
  iunfold kvOwn
  iframe Hw Hll Hrd
  iunfold kvBk
  iexists B
  iframe

/-- **A rejection of a writing method**: the thread's KV resources, the chain's, `Pre` and the
reader token back. -/
theorem mPreW_reject (E : AEnv GF) (c : Chain) (a : GoInterface)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (log : mvcc.Log) (Pre Q Post : IProp GF) :
    mPreW E c a info log Pre Q Post ⊢ kvOwn E log ∗ chainRes c a info ∗ Pre ∗ bkRTOf E := by
  iintro H
  icases mPreW_split E c a info log Pre Q Post $$ H with
    ⟨%cr, %B, Hw, Hcs, -, Hrt, Htie, Hres, Hkv⟩
  icases bkRTOf_intro E B $$ [$Htie $Hrt] with ⟨Htie, Hrt⟩
  iunfold srvApi.csContractA at Hcs
  icases Hcs with ⟨HPre, -, -⟩
  iframe HPre Hres
  isplitr [Hrt]
  · iapply kvOwn_of_split E log B cr
    iframe
  · iexact Hrt

/-- **`mPreW` without the chain's resources** (as `mPreRest`). -/
def mPreWRest (E : AEnv GF) (log : mvcc.Log) (Pre Q Post : IProp GF) : IProp GF :=
  iprop((∃ cr : Int, srvApi.wStQ E.γs E.stq log cr) ∗ leasesLive E (mvcc.stateAfter log) ∗ E.RD ∗
    ∃ B : mvcc.KBReal, mvccBackend E.γ 1 B (E.Pk B) ∗ hookIs B E.f ∗ E.BkTie B ∗ bkWT B ∗ bkRT B ∗
      srvApi.csContractA (E.Pk B) E.f Pre Q Post)

theorem mPreW_split_chain (E : AEnv GF) (c : Chain) (a : GoInterface)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (log : mvcc.Log) (Pre Q Post : IProp GF) :
    mPreW E c a info log Pre Q Post ⊢ mPreWRest E log Pre Q Post ∗ chainRes c a info := by
  iintro H
  iunfold mPreW at H
  icases H with ⟨Hw, Hll, Hrd, Hres, Hb⟩
  iunfold mPreWRest
  iframe

theorem mPreW_of_rest (E : AEnv GF) (c : Chain) (a : GoInterface)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (log : mvcc.Log) (Pre Q Post : IProp GF) :
    mPreWRest E log Pre Q Post ∗ chainRes c a info ⊢ mPreW E c a info log Pre Q Post := by
  iintro ⟨H, Hres⟩
  iunfold mPreWRest at H
  icases H with ⟨Hw, Hll, Hrd, Hb⟩
  iunfold mPreW
  iframe

/-- **A rejection, the contract kept** (the auth layer's rejection lemmas take it). -/
theorem mPreRest_reject_cs (E : AEnv GF) (log : mvcc.Log) (Pre Q Post : IProp GF) :
    mPreRest E log Pre Q Post ⊢
      kvOwn E log ∗ ∃ B : mvcc.KBReal, srvApi.csContractA (E.Pk B) E.f Pre Q Post := by
  iintro H
  iunfold mPreRest at H
  icases H with ⟨Hw, Hll, Hrd, %B, Hbk, Hhk, Htie, Hcs⟩
  isplitr [Hcs]
  · iunfold kvOwn
    iframe Hw Hll Hrd
    iunfold kvBk
    iexists B
    iframe
  · iexists B; iexact Hcs

/-- The auth store's reader resource and the lease owner's resource of `mPreRest`, lent out (as
`kvOwn_lend`). -/
theorem mPreRest_lend (E : AEnv GF) (log : mvcc.Log) (Pre Q Post : IProp GF) :
    mPreRest E log Pre Q Post ⊢ E.RD ∗ ∃ L : List w64,
      lease.lessorUserW (mvccLeases E.γ) L (mvcc.leaseItemsOf (mvcc.stateAfter log)) E.win ∗
      (E.RD -∗ lease.lessorUserW (mvccLeases E.γ) L (mvcc.leaseItemsOf (mvcc.stateAfter log)) E.win -∗
        mPreRest E log Pre Q Post) := by
  iintro H
  iunfold mPreRest at H
  icases H with ⟨Hw, Hll, Hrd, Hb⟩
  iunfold leasesLive at Hll
  icases Hll with ⟨%L, #Hk, Hu, Hlt⟩
  iframe Hrd
  iexists L
  iframe Hu
  iintro Hrd Hu
  iunfold mPreRest
  iframe Hw Hrd Hb
  iunfold leasesLive
  iexists L
  iframe Hk Hu Hlt

/-- The auth store's reader resource of `mPreRest`, lent out (as `kvOwn_rd`). -/
theorem mPreRest_rd (E : AEnv GF) (log : mvcc.Log) (Pre Q Post : IProp GF) :
    mPreRest E log Pre Q Post ⊢ E.RD ∗ (E.RD -∗ mPreRest E log Pre Q Post) := by
  iintro H
  iunfold mPreRest at H
  icases H with ⟨Hw, Hll, Hrd, Hb⟩
  iframe Hrd
  iintro Hrd
  iunfold mPreRest
  iframe

/-- The auth store's reader resource of `mPreWRest`, lent out. -/
theorem mPreWRest_rd (E : AEnv GF) (log : mvcc.Log) (Pre Q Post : IProp GF) :
    mPreWRest E log Pre Q Post ⊢ E.RD ∗ (E.RD -∗ mPreWRest E log Pre Q Post) := by
  iintro H
  iunfold mPreWRest at H
  icases H with ⟨Hw, Hll, Hrd, Hb⟩
  iframe Hrd
  iintro Hrd
  iunfold mPreWRest
  iframe

/-- **A rejection of a writing method** from `mPreWRest`. -/
theorem mPreWRest_reject (E : AEnv GF) (log : mvcc.Log) (Pre Q Post : IProp GF) :
    mPreWRest E log Pre Q Post ⊢ kvOwn E log ∗ Pre ∗ bkRTOf E := by
  iintro H
  iunfold mPreWRest at H
  icases H with ⟨Hw, Hll, Hrd, %B, Hbk, Hhk, Htie, -, Hrt, Hcs⟩
  icases bkRTOf_intro E B $$ [$Htie $Hrt] with ⟨Htie, Hrt⟩
  iunfold srvApi.csContractA at Hcs
  icases Hcs with ⟨HPre, -, -⟩
  iframe HPre
  isplitr [Hrt]
  · iunfold kvOwn
    iframe Hw Hll Hrd
    iunfold kvBk
    iexists B
    iframe
  · iexact Hrt

/-- **`mPreV` without the chain's resources** (as `mPreRest`). -/
def mPreVRest (v3 : Bool) (E : AEnv GF) (log : mvcc.Log) (Pre Q Post : IProp GF) : IProp GF :=
  iprop((∃ cr : Int, srvApi.wStQ E.γs E.stq log cr) ∗ leasesLive E (mvcc.stateAfter log) ∗ E.RD ∗
    ∃ B : mvcc.KBReal, mvccBackend E.γ 1 B (E.Pk B) ∗ hookIs B E.f ∗ E.BkTie B ∗ bkWT B ∗ bkRT B ∗
      cPre v3 (E.Pk B) E.f Pre Q Post)

theorem mPreV_split_chain (v3 : Bool) (E : AEnv GF) (c : Chain) (a : GoInterface)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (log : mvcc.Log) (Pre Q Post : IProp GF) :
    mPreV v3 E c a info log Pre Q Post ⊢ mPreVRest v3 E log Pre Q Post ∗ chainRes c a info := by
  iintro H
  iunfold mPreV at H
  icases H with ⟨Hw, Hll, Hrd, Hres, Hb⟩
  iunfold mPreVRest
  iframe

theorem mPreV_of_rest (v3 : Bool) (E : AEnv GF) (c : Chain) (a : GoInterface)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (log : mvcc.Log) (Pre Q Post : IProp GF) :
    mPreVRest v3 E log Pre Q Post ∗ chainRes c a info ⊢ mPreV v3 E c a info log Pre Q Post := by
  iintro ⟨H, Hres⟩
  iunfold mPreVRest at H
  icases H with ⟨Hw, Hll, Hrd, Hb⟩
  iunfold mPreV
  iframe

/-! ### `kvOwnPre` (`uberApplier.dispatch`'s and `Apply`'s resources), split per method -/

/-- `kvOwnPre` is `mPreV`'s rest (the same resources). -/
theorem kvOwnPre_eq_rest (v3 : Bool) (E : AEnv GF) (log : mvcc.Log) (Pre Q Post : IProp GF) :
    kvOwnPre v3 E log Pre Q Post = mPreVRest v3 E log Pre Q Post := rfl

/-- **For a cluster method**: `mPreV` from `kvOwnPre` and the chain's resources. -/
theorem kvOwnPre_mPreV (v3 : Bool) (E : AEnv GF) (c : Chain) (a : GoInterface)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (log : mvcc.Log) (Pre Q Post : IProp GF) :
    kvOwnPre v3 E log Pre Q Post ∗ chainRes c a info ⊢ mPreV v3 E c a info log Pre Q Post := by
  rw [kvOwnPre_eq_rest]; exact mPreV_of_rest v3 E c a info log Pre Q Post

/-- **For a method that does not write** (a read, `AuthStatus`, a request with nothing to do):
the thread's KV resources, the reader token, and `Pre` (the contract unused; the write-back token
dropped). -/
theorem kvOwnPre_kvOwn (v3 : Bool) (E : AEnv GF) (log : mvcc.Log) (Pre Q Post : IProp GF) :
    kvOwnPre v3 E log Pre Q Post ⊢ kvOwn E log ∗ bkRTOf E ∗ Pre := by
  iintro H
  iunfold kvOwnPre at H
  icases H with ⟨Hw, Hll, Hrd, %B, Hbk, Hhk, Htie, -, Hrt, Hc⟩
  icases bkRTOf_intro E B $$ [$Htie $Hrt] with ⟨Htie, Hrt⟩
  isplitl [Hw Hll Hrd Hbk Hhk Htie]
  · iunfold kvOwn
    iframe Hw Hll Hrd
    iunfold kvBk
    iexists B
    iframe Hbk Hhk Htie
  isplitl [Hrt]
  · iexact Hrt
  iapply cPre_pre; iexact Hc

/-- **For a KV method that writes through the store** (`Put`, `DeleteRange`, `Txn`,
`Compaction`): `mPre` from `kvOwnPre true` and the chain's resources, the reader token aside (the
write-back token dropped: the store's own write takes none). -/
theorem kvOwnPre_mPre (E : AEnv GF) (c : Chain) (a : GoInterface)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (log : mvcc.Log) (Pre Q Post : IProp GF) :
    kvOwnPre true E log Pre Q Post ∗ chainRes c a info ⊢
      mPre E c a info log Pre Q Post ∗ bkRTOf E := by
  iintro ⟨H, Hres⟩
  iunfold kvOwnPre at H
  icases H with ⟨Hw, Hll, Hrd, %B, Hbk, Hhk, Htie, -, Hrt, Hc⟩
  icases bkRTOf_intro E B $$ [$Htie $Hrt] with ⟨Htie, Hrt⟩
  isplitr [Hrt]
  · iunfold mPre
    iframe Hw Hll Hrd Hres
    iexists B
    iframe Hbk Hhk Htie
    simp only [cPre, ↓reduceIte]
    iexact Hc
  iexact Hrt

/-- **For a method whose component writes the backend** (the merge of `lean`, 2026-11-06: the
lessor's grant, `grantPre`): `mPreW` from `kvOwnPre true` and the chain's resources. -/
theorem kvOwnPre_mPreW (E : AEnv GF) (c : Chain) (a : GoInterface)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (log : mvcc.Log) (Pre Q Post : IProp GF) :
    kvOwnPre true E log Pre Q Post ∗ chainRes c a info ⊢ mPreW E c a info log Pre Q Post := by
  iintro ⟨H, Hres⟩
  iunfold kvOwnPre at H
  icases H with ⟨Hw, Hll, Hrd, %B, Hbk, Hhk, Htie, Hwt, Hrt, Hc⟩
  iunfold mPreW
  iframe Hw Hll Hrd Hres
  iexists B
  iframe Hbk Hhk Htie Hwt Hrt
  simp only [cPre, ↓reduceIte]
  iexact Hc

/-- **`kvOwnPre` lends the auth store's reader resource** (`uberApplier.Apply`'s `rdLend`, as
`rdLend_kvOwn`). -/
theorem rdLend_kvOwnPre (v3 : Bool) (E : AEnv GF) (X : IProp GF) (log : mvcc.Log)
    (Pre Q Post Y : IProp GF) :
    ⊢ rdLend E iprop(X ∗ kvOwnPre v3 E log Pre Q Post ∗ Y) := by
  unfold rdLend
  iintro !> ⟨HX, Hkv, HY⟩
  iunfold kvOwnPre at Hkv
  icases Hkv with ⟨Hw, Hll, Hrd, Hb⟩
  iframe Hrd
  iintro Hrd
  iframe HX HY
  iunfold kvOwnPre
  iframe

end lemmas

end apply
end EtcdGrove
end Perennial

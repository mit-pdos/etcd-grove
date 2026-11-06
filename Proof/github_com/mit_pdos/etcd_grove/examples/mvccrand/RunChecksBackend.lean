/-
`runChecks`' backend (`examples/mvccrand/mvccrand.go`): its parameters, its write-back tokens and
the store's part of it. Lean-first (no Rocq counterpart).

- **The parameters** (`rcP`, the instance `rcKB`): schema's `Key`, `Meta` and `Lease` buckets (the
  store's and the lessor's), mvcc's layout (`bridgeParams`), the lessor's (`leaseParams`), no hook
  of its own (`hookMax = 0`: the tester's backend has no `BackendHooks`), compaction mode on (the
  store's `New`), the batch limit `DefaultBackendConfig`'s.
- **The write-back tokens** (`bFresh`'s `2 ^ 40 - 1`): two for the store's open, one for `NewLessor`,
  one for `SetTxPostLockInsideApplyHook`, one per writer operation (its lease grants'), and the rest
  a stock (`rcStock`) backing the store's receipt-paid supply (`□ (⧗ 1 ={⊤}=∗ wbTok)`): every
  receipt taken one token out, so it never runs out before the receipts (`receiptBound`) do.
- **The open** (`rc_open`): `backend.New`'s post, its reader slots pooled (the pool one slot short:
  the lessor's write right holds a reader's token, `apply.bkRT`), opened at the store's write
  invariant over the empty data (`mvccImage_fresh.law`, `etcdStorage_open.law`), the client's rest
  opened (`backendRest_open.law`).
- **`DefaultBackendConfig`** (`wp_DefaultBackendConfig`): its configuration has no hooks and a batch
  limit in range; it loads three package variables of which the backend's package fact states
  nothing (a placeholder, below).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccrand.WriterRun
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.New
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.RdPool
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBatch
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.EtcdBackend
public import Perennial.ProgramLogic.Bounds

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccrand

open Iris Iris.BI Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.mvccrand mvcc mvcc.api

section params
variable [GooseExts]

/-- The tester's bucket table: schema's `Key`, `Meta` and `Lease`. -/
def rcBT : GMap GoString w64 :=
  (((∅ : GMap GoString w64).insert keyName (W64 1)).insert
    go_etcd_io.etcd.server.v3.storage.schema.metaName (W64 2)).insert leaseName (W64 3)

/-- **The tester's backend instance** (`backend.New`'s `γB`, its `*backend`, the store's
registration name `gx`), with the batch limit `lim`. -/
abbrev rcKB (γB : backend.BNames) (be : Loc) (gx : GName) (lim : w64) : KBReal :=
  ⟨γB, rcBT, 0, lim, be, gx, true⟩

/-- **The tester's backend parameters** (`rcKB`'s, whatever its names). -/
def rcP (lim : w64) : backend.BParams :=
  { BT := rcBT, HB := fun n => decide (n ≠ keyName), SB := fun n => decide (n = keyName),
    HK := fun n k => decide (n = go_etcd_io.etcd.server.v3.storage.schema.metaName ∧
      (k = go_etcd_io.etcd.server.v3.storage.schema.ciKeyBytes ∨
        k = go_etcd_io.etcd.server.v3.storage.schema.termKeyBytes)),
    RB := fun n => decide (n ∈ restBuckets), hookMax := 0, limit := lim, FV := metaRevVal }

theorem rcKB_P (γB : backend.BNames) (be : Loc) (gx : GName) (lim : w64) :
    (rcKB γB be gx lim).P = rcP lim := rfl

theorem rcKB_γB (γB : backend.BNames) (be : Loc) (gx : GName) (lim : w64) :
    (rcKB γB be gx lim).γB = γB := rfl

theorem rcKB_be (γB : backend.BNames) (be : Loc) (gx : GName) (lim : w64) :
    (rcKB γB be gx lim).be = be := rfl

theorem rcKB_gx (γB : backend.BNames) (be : Loc) (gx : GName) (lim : w64) :
    (rcKB γB be gx lim).gx = gx := rfl

theorem rcBT_key : rcBT.lookup keyName = some (W64 1) := by
  unfold rcBT
  rw [GMap.lookup_insert_ne _ _ (by decide), GMap.lookup_insert_ne _ _ (by decide),
    GMap.lookup_insert]

theorem rcBT_meta :
    rcBT.lookup go_etcd_io.etcd.server.v3.storage.schema.metaName = some (W64 2) := by
  unfold rcBT
  rw [GMap.lookup_insert_ne _ _ (by decide), GMap.lookup_insert]

theorem rcBT_lease : rcBT.lookup leaseName = some (W64 3) := by
  unfold rcBT
  rw [GMap.lookup_insert]

theorem rcBT_lookup (n : GoString) (i : w64) (h : rcBT.lookup n = some i) :
    (n = keyName ∧ i = W64 1) ∨ (n = go_etcd_io.etcd.server.v3.storage.schema.metaName ∧ i = W64 2) ∨
      (n = leaseName ∧ i = W64 3) := by
  unfold rcBT at h
  by_cases h3 : n = leaseName
  · subst h3; rw [GMap.lookup_insert] at h; cases h; exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  rw [GMap.lookup_insert_ne _ _ (Ne.symm h3)] at h
  by_cases h2 : n = go_etcd_io.etcd.server.v3.storage.schema.metaName
  · subst h2; rw [GMap.lookup_insert] at h; cases h; exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  rw [GMap.lookup_insert_ne _ _ (Ne.symm h2)] at h
  by_cases h1 : n = keyName
  · subst h1; rw [GMap.lookup_insert] at h; cases h; exact Or.inl ⟨rfl, rfl⟩
  rw [GMap.lookup_insert_ne _ _ (Ne.symm h1)] at h
  simp at h

/-- The parameters are sane (`backend.New`'s premise), at a limit in range. -/
theorem rcP_wf (lim : w64) (h0 : 0 < sint.Z lim) (h1 : sint.Z lim ≤ 2 ^ 57) : (rcP lim).Wf := by
  refine ⟨?_, h0, h1, by simp [rcP], ?_⟩
  · intro n1 n2 i e1 e2
    rcases rcBT_lookup n1 i e1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases rcBT_lookup n2 _ e2 with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ <;>
    first | rfl | (exfalso; revert h; decide)
  · intro n h
    simp only [rcP, decide_eq_true_eq] at h ⊢
    simp [h]

/-- mvcc's layout. -/
theorem rcP_bridge (lim : w64) : bridgeParams (rcP lim) := by
  refine ⟨rcBT_key, rcBT_meta, fun _ => rfl, fun _ => rfl, ?_, ?_⟩ <;> simp only [rcP] <;> decide

/-- The lessor's layout. -/
theorem rcP_lease (lim : w64) : leaseParams (rcP lim) := by
  refine ⟨rcBT_lease, by simp only [rcP]; decide, fun k => ?_⟩
  have h : leaseName ≠ go_etcd_io.etcd.server.v3.storage.schema.metaName := by decide
  simp only [backend.BParams.hk, rcP, h, false_and, decide_false, Bool.and_false]

end params

section stock
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccrand.Assumptions]

/-- The stock's namespace. -/
def rcStockN : Namespace := (nroot .@ "mvccrand") .@ "wbstock"

/-- **The store's stock of write-back tokens** (persistent): `n` tokens of the backend and the `a`
receipts taken so far, with `receiptBound ≤ a + n + 1`. -/
def rcStock (γB : backend.BNames) : IProp GF :=
  inv rcStockN iprop(∃ (a n : Nat), ⧗ a ∗ ownToks γB.wb n ∗ ⌜receiptBound GF ≤ a + n + 1⌝)

instance rcStock_persistent (γB : backend.BNames) : Persistent (rcStock (GF := GF) γB) := by
  unfold rcStock; infer_instance

/-- The stock from `n` tokens, `receiptBound ≤ n + 1`. -/
theorem rcStock_alloc (γB : backend.BNames) (n : Nat) (h : receiptBound GF ≤ n + 1) (E : CoPset) :
    ownToks (GF := GF) γB.wb n ⊢ |={E}=> rcStock γB := by
  iintro Hn
  imod receipt_zero (GF := GF) with H0
  unfold rcStock
  iapply inv_alloc rcStockN E
  inext
  iexists 0, n
  iframe H0 Hn
  ipureintro; omega

/-- **The receipt-paid supply** of the stock's backend. -/
theorem rcStock_supply (γB : backend.BNames) :
    rcStock (GF := GF) γB ⊢ □ (⧗ 1 ={⊤}=∗ backend.wbTok γB) := by
  iintro #Hs
  iintro !> Hr
  unfold rcStock
  iinv Hs with ⟨%a, %n, >Ha, >Hn, >%Hb⟩ Hclose
  icases receipt_add_one_lt a $$ [Hr Ha] with ⟨%Hlt, Ha⟩
  · iframe
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  icases ownToks_add_1 1 n' γB.wb $$ Hn with ⟨Hn, Ht⟩
  imod Hclose $$ [Ha Hn] with -
  · inext
    iexists a + 1, n'
    iframe Ha Hn
    ipureintro; omega
  imodintro
  unfold backend.wbTok
  iexact Ht

/-- `k` tokens as `k` write-back tokens. -/
theorem wbToks_list (γB : backend.BNames) : ∀ k : Nat,
    ownToks (GF := GF) γB.wb k ⊢ [∗list] _x ∈ List.replicate k (), backend.wbTok γB
  | 0 => by
    iintro -
    simp only [List.replicate]
    iapply BigSepL.bigSepL_nil.2; itrivial
  | k + 1 => by
    iintro H
    icases ownToks_add_1 1 k γB.wb $$ H with ⟨H, Ht⟩
    rw [List.replicate_succ]
    iapply BigSepL.bigSepL_cons.2
    ihave Ht : backend.wbTok (GF := GF) γB $$ [Ht]
    · unfold backend.wbTok; iexact Ht
    iframe Ht
    iapply wbToks_list γB k $$ H

end stock

section opening
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccrand.Assumptions]

/-- **What the tester keeps of its opened backend**: the store's part opened, the backend's
contract, the hook's half (unset), the tracked buckets' half, half of the open token, one reader's
token (a slot and its open share: the lessor's write right, `apply.bkRT`) and `m` write-back
tokens. -/
def rcBk (γB : backend.BNames) (b : Loc) (gx : GName) (lim : w64) (m : Nat) : IProp GF :=
  iprop(mvccStorageFor (etcdStorage (rcKB γB b gx lim)) iprop(True) mvccStart.log mvccStart.crev false ∗
    □ backend.isBackend γB (rcP lim) (mvccW gx) iprop(True) b ∗
    backend.plHook γB func.nil ∗ backend.rbOwn γB (backend.rbData (rcP lim) ∅) ∗
    backend.bOpen γB (1 : Qp).half ∗ backend.bOpen γB backend.rdOpen ∗
    backend.rdTok γB (rcP lim) b ∗ ownToks γB.wb m)

/-- **The tester's backend opened for the store** (see the file header): from `backend.New`'s post
at the store's write invariant over the empty data, keeping the fresh backend's payment rights
(`K := bFresh`), and the registration, the store's part opened, the client's rest, `m` tokens. -/
theorem rc_open (hfresh : mvccImage_fresh.law (GF := GF)) (hopen : etcdStorage_open.law (GF := GF))
    (hrest : backendRest_open.law (GF := GF)) [ThreadBoundLe GF (2 ^ 28)]
    (γB : backend.BNames) (b : Loc) (gx : GName) (lim : w64) (m : Nat)
    (hm : receiptBound GF + m + 2 ≤ backend.wbInit) :
    □ (∀ (γ : backend.BNames) (P : backend.BParams) (b' : Loc), keySized (GF := GF) γ P b') ∗ mvccWReg gx ∗
      backend.newPostK γB (rcP lim) (fun _ => mvccW gx) (fun _ => iprop(True)) (backend.bFresh (GF := GF)) b ∅ ⊢
    |={⊤}=> rcBk γB b gx lim m := by
  have hT : threadBound GF ≤ backend.rdPoolN :=
    ThreadBoundLe.le_of (2 ^ 28) (Nat.le_of_eq (by unfold backend.rdPoolN; rfl))
  iintro ⟨#Hks, Hreg, Hnew⟩
  iunfold backend.newPostK at Hnew
  icases Hnew with ⟨#Hb, #Hsc, Hk, Hv, Hh, Hrb, Hrd, Hdl, Hfk, Hsr⟩
  iunfold backend.bFresh at Hk
  icases Hk with ⟨Hwb, Ho⟩
  icases (backend.bOpen_one_pool γB).1 $$ Ho with ⟨Hoh, -, Hos⟩
  -- the reader slots pooled; the stock's open shares: the store's, two of the client's
  imod backend.rdToks_pool hT ⊤ γB (rcP lim) b $$ Hrd with ⟨#Hpool, Hrs⟩
  obtain ⟨n2, hn2⟩ : ∃ n2, backend.rdStockN = n2 + 2 :=
    ⟨backend.rdStockN - 2, by have := backend.rdStockN_val; omega⟩
  have hn2' : backend.rdStockN - 2 = n2 := by omega
  rw [hn2]
  icases (backend.bigSepL_replicate_add _ n2 2).1 $$ Hos with ⟨Hos, Ho2⟩
  rw [List.replicate_succ]
  icases BigSepL.bigSepL_cons.1 $$ Ho2 with ⟨Hor, -⟩
  -- the write-back tokens: two for the open, `m` kept, the stock
  obtain ⟨N, hN⟩ : ∃ N, backend.wbInit = N + (2 + m) := ⟨backend.wbInit - (2 + m), by omega⟩
  rw [hN]
  icases ownToks_add_1 (2 + m) N γB.wb $$ Hwb with ⟨HwN, Hw⟩
  icases ownToks_add_1 m 2 γB.wb $$ Hw with ⟨Hw2, Hwm⟩
  icases ownToks_add_1 1 1 γB.wb $$ Hw2 with ⟨Hw1, Hw1'⟩
  imod rcStock_alloc γB N (by omega) ⊤ $$ HwN with #Hstock
  ihave #Hsup := rcStock_supply γB $$ Hstock
  imod hfresh ∅ (fun _ => rfl) rfl rfl with #Himg
  ihave Hnp : backend.newPostKP (GF := GF) γB (rcP lim) (fun _ => mvccW gx) (fun _ => iprop(True))
      (fun _ => iprop(True)) b ∅ $$ [Hv Hh Hrb Hrs Hdl Hfk Hsr]
  · iunfold backend.newPostKP
    isplitr; iexact Hb
    isplitr; iexact Hsc
    isplitr; itrivial
    isplitl [Hv]; iexact Hv
    isplitl [Hh]; iexact Hh
    isplitl [Hrb]; iexact Hrb
    isplitr; iexact Hpool
    isplitl [Hrs]; iexact Hrs
    isplitl [Hdl]; iexact Hdl
    isplitl [Hfk]; iexact Hfk
    iexact Hsr
  ihave Hw1 : backend.wbTok (GF := GF) γB $$ [Hw1]
  · unfold backend.wbTok; iexact Hw1
  ihave Hw1' : backend.wbTok (GF := GF) γB $$ [Hw1']
  · unfold backend.wbTok; iexact Hw1'
  ihave Hks' : (□ (∀ (γ : backend.BNames) (b' : Loc), keySized (GF := GF) γ (rcP lim) b')) $$ []
  · iintro !> %γ %b'; iapply Hks
  rw [← hn2']
  imod hopen (rcKB γB b gx lim) (fun _ => iprop(True)) (fun _ => iprop(True)) ∅ mvccStart.log
      mvccStart.crev false (rcP_bridge lim) (rcP_lease lim) rfl
      $$ [Hks' Himg Hnp Hreg Hw1 Hw1' Hsup Hos] with ⟨Hsf, Hrest, Hrt, -⟩
  · rw [rcKB_P, rcKB_γB, rcKB_be, rcKB_gx]
    isplitl [Hks']; iexact Hks'
    isplitl [Himg]; iexact Himg
    isplitl [Hnp]; iexact Hnp
    isplitl [Hreg]; iexact Hreg
    isplitl [Hw1]; iexact Hw1
    isplitl [Hw1']; iexact Hw1'
    isplitl [Hsup]; iexact Hsup
    iexact Hos
  rw [rcKB_P, rcKB_γB, rcKB_be]
  ihave ⟨-, -, Hhk, Hrbo, -⟩ := hrest _ _ _ _ _ $$ Hrest
  imodintro
  iunfold rcBk
  iframe Hsf Hb Hhk Hrbo Hoh Hor Hrt Hwm

end opening

section config
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccrand.Assumptions]

open go_etcd_io.etcd.server.v3.storage.backend in
/-- **Placeholder: the backend's defaults.** `DefaultBackendConfig` (`backend.go`) reads the package
variables `defaultBatchInterval` (`100 * time.Millisecond`), `defaultBatchLimit` (`10000`) and
`InitialMmapSize` (`10 * 1024 * 1024 * 1024`), which nothing writes after the package's
initializer; the backend's package fact (`backendInit`, `Base.lean`) states none of them, so a
client cannot load them. The missing fact, as the package fact would state it. -/
theorem backend_defaults_M1 :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ⊢
      ∃ (bi ms : w64), globalAddr defaultBatchInterval ↦□ bi ∗
        globalAddr defaultBatchLimit ↦□ (W64 10000) ∗ globalAddr InitialMmapSize ↦□ ms := by
  sorry -- M1-REPLACE: backend's package fact (backendInit) states nothing of defaultBatchInterval, defaultBatchLimit, InitialMmapSize, which DefaultBackendConfig loads

open go_etcd_io.etcd.server.v3.storage.backend in
/-- **`DefaultBackendConfig(lg)`**: its configuration has the default batch limit and no hooks. -/
theorem wp_DefaultBackendConfig (lg : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend }}
      (App (Val (@! go_etcd_io.etcd.server.v3.storage.backend.DefaultBackendConfig)) (Val #lg))
    {{ (c : BackendConfig), RET #c; ⌜c.BatchLimit' = W64 10000 ∧ c.Hooks' = GoInterface.nil⌝ }} := by
  wp_start as #Hpkg
  ihave ⟨%bi, %ms, #Hbi, #Hbl, #Hms⟩ := backend_defaults_M1 $$ Hpkg
  wp_auto
  iapply HΦ
  ipureintro
  exact ⟨rfl, rfl⟩

end config

end mvccrand
end EtcdGrove
end Perennial

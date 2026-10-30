/-
**M2, the storage side, step 2: the server's side of restore in compaction mode (Draft)**
(`notes/m2-storage-plan.md`, "Step 2: restore in compaction mode"). Imported by nothing; no `axiom`,
no `sorry`; nothing switched. D22's statements are the collaborator's: each `…D`/`…R`/`…M` here is a
draft of one, for them to read.

- **The write-back supply follows the backend** (task 2; `kbWTSupplyM`, Q1 (a): `store.Compact`'s
  premise). The write budget's tokens move out of `srvWTPool`'s invariant into **one stock invariant
  per backend** (`srvWTStockInv γp d`, persistent, named by the backend `d`, which never changes),
  sharing the pool's receipt counter `γp` (a lower bound in each stock): the pool keeps the receipts,
  the counter's authority, its quarter of `E.γbe` at the current backend and that backend's stock
  fact (`srvWTPoolR`). A taker at any backend with a stock takes a receipt into the pool and a token
  from the stock (`srvWTStock_take`); so the supply of `d` is persistent
  (`kbWTSupplyM_of_stock`), and survives `applySnapshot`'s swap, which still gathers the whole of
  `E.γbe` (`srv_be_swapR`: it takes the new backend's stock fact in place of its tokens, and no
  longer hands out the old backend's tokens, which `Close` does not need). The new backend's stock is
  made from its fresh tokens (`srvWTStock_alloc`) *before* `Restore`, which needs the supply for the
  compaction `restore()` resumes. No more tokens than today: one stock of `receiptBound - 1` per
  backend, as the pool's today (the shared counter bounds all takes together). Alternatives in the
  plan (questions for the user).
- **The apply environment's facts by the mode** (`srvEnvOkD`: `d.cm = E.cmp` in place of
  `d.cm = false`, over N1's `apply.AEnvD`), with the step the install makes (`srvEnvOkD_mode_step`).
- **The KV's closer by the mode** (`srvKVCloserM`: today's `srvKVCloser` off; on, the watchable
  store's own parts and the inner store's restorable right, `mvcc.wsCloserR`), and **`RestorePre`
  drafted** (`restorePre_of_applyM`: today's `restorePre_of_apply` in either mode, without its
  `sorry`: off, the frozen fact is the watchable store's `Hfrz`; on, the right is the closer's).
- **The restore step composes** (`snap_closer_after`): `watchableStore.Restore.specM`'s post's right
  and the watchable store's kept parts make the new environment's closer, in either mode.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapApply
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvWatchBuilt
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.M2StorageDraft
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.M2StorageDraftRestore

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section draft
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-! ## The write budget, one stock per backend -/

/-- The stocks' invariants' name (disjoint from the pool's, `srvWTN`). -/
def srvWTStockN : Namespace := nroot .@ "srvWTStock"

/-- **The write-back tokens of the backend `d`** (persistent; draft): an invariant holding `n` tokens
of `d` and a lower bound `m` of the write budget's count of tokens taken (`γp`, the pool's counter),
with `receiptBound ≤ m + n + 1`: every take raises the count by one (a receipt into the pool), so
the stock never runs out before the receipts do. Named by `d`, which a backend swap does not change,
so a persistent supply of `d` (`kbWTSupplyM (some d)`, a compaction job's) stays good after
`applySnapshot` moves `E.γbe` to the next backend. -/
def srvWTStockInv (γp : GName) (d : mvcc.KBReal) : IProp GF :=
  inv srvWTStockN iprop(∃ (m n : Nat), monoNatLbOwn γp m ∗ ownToks d.γB.wb n ∗
    ⌜receiptBound GF ≤ m + n + 1⌝)

instance srvWTStockInv_persistent (γp : GName) (d : mvcc.KBReal) :
    Persistent (srvWTStockInv (GF := GF) γp d) := by
  unfold srvWTStockInv; infer_instance

/-- **Draft of `srvWTPool`** (D22's, `InvApplier.lean:819`): today's invariant with the current
backend's tokens and their bound replaced by its stock (`srvWTStockInv γp d`). The receipts, the
counter's authority, the quarter of `E.γbe` and the storage-version monitor's read token as today. -/
def srvWTPoolR (E : apply.AEnv GF) (γp : GName) : IProp GF :=
  inv srvWTN iprop(∃ (a : Nat) (d : mvcc.KBReal), ⧗ a ∗
    dghostVar E.γbe (DFrac.own (1 : Qp).half.half) d ∗ srvWTStockInv γp d ∗
    monoNatAuthOwn γp 1 a ∗
    (mvcc.bkRTx d.γB d.P d.be ∨ ∃ q : Qp, dghostVar E.γbe (DFrac.own q) d))

instance srvWTPoolR_persistent (E : apply.AEnv GF) (γp : GName) :
    Persistent (srvWTPoolR (GF := GF) E γp) := by
  unfold srvWTPoolR; infer_instance

theorem srvWTStockN_mask : (↑srvWTStockN : CoPset) ⊆ ⊤ \ ↑srvWTN :=
  sync.wg_mask_ndot_ne nroot "srvWTStock" "srvWT" (by decide)

/-- **A token of any backend with a stock, for a receipt** (draft): the receipt goes into the pool
(the count up by one), the token out of the stock. -/
theorem srvWTStock_take (E : apply.AEnv GF) (γp : GName) (d : mvcc.KBReal) :
    ⊢ srvWTPoolR (GF := GF) E γp -∗ srvWTStockInv γp d -∗ ⧗ 1 ={⊤}=∗ backend.wbTok d.γB := by
  have hm := srvWTStockN_mask
  iintro #Hp #Hs Hr
  unfold srvWTPoolR
  iinv Hp with ⟨%a, %d0, >Ha, >Hg, #Hs0, >Hc, Hrt⟩ Hclose
  unfold srvWTStockInv
  iinv Hs with ⟨%m, %n, >#Hm, >Hn, >%Hb⟩ Hclose2
  ihave %Hma := monoNatLbOwn_valid γp 1 a m $$ Hc Hm
  icases receipt_add_one_lt a $$ [Hr Ha] with ⟨%Hlt, Ha⟩
  · iframe
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  icases wbToks_split d n' $$ Hn with ⟨Ht, Hn⟩
  imod mono_nat_own_update (a + 1) (by omega) $$ Hc with ⟨Hc, #Hlb⟩
  imod Hclose2 $$ [Hn] with -
  · inext
    iexists a + 1, n'
    iframe Hlb Hn
    ipureintro; omega
  imod Hclose $$ [Ha Hg Hc Hrt] with -
  · inext
    iexists a + 1, d0
    iframe Ha Hg Hs0 Hc Hrt
  imodintro
  iexact Ht

/-- **The compaction's write-back supply of any backend with a stock** (draft; in place of
`kbWTSupplyM_of_srvWTPool`, whose discarded part of `E.γbe` P4's withdrawal took away): persistent,
good after any number of swaps. -/
theorem kbWTSupplyM_of_stock (E : apply.AEnv GF) (γp : GName) (d : mvcc.KBReal) :
    srvWTPoolR (GF := GF) E γp ∗ srvWTStockInv γp d ⊢ mvcc.kbWTSupplyM (some d) := by
  iintro ⟨#Hp, #Hs⟩
  unfold mvcc.kbWTSupplyM
  split
  · unfold mvcc.kbWTSupply
    iintro !> Hr
    iapply srvWTStock_take E γp d $$ Hp Hs Hr
  · itrivial

/-- **A backend's stock from its fresh tokens** (draft; the walk's step after `OpenSnapshotBackend`,
before `Restore`, and `start`'s at the boot backend): as many as the pool's today. -/
theorem srvWTStock_alloc (γp : GName) (d : mvcc.KBReal) (n : Nat) (h : receiptBound GF ≤ n + 1)
    (Ms : CoPset) :
    ⊢ ownToks (GF := GF) d.γB.wb n ={Ms}=∗ srvWTStockInv γp d := by
  iintro Hn
  imod monoNatLbOwn_0 (GF := GF) γp with #H0
  unfold srvWTStockInv
  iapply inv_alloc srvWTStockN Ms
  inext
  iexists 0, n
  iframe H0 Hn
  ipureintro; omega

/-- **A token of the current backend** (draft of `srvWTPool_take_extra_d`, D22's): the pool's
current stock, then a take. One cost against today's: a later credit (the stock's fact is an
invariant, under the pool's `▷`), which every caller has from its step (`wp_auto_lc`). -/
theorem srvWTPoolR_take_extra_d (E : apply.AEnv GF) (γp : GName) (d : mvcc.KBReal) (dq : DFrac) :
    ⊢ srvWTPoolR (GF := GF) E γp -∗ ⧗ 1 -∗ £ 1 -∗ dghostVar E.γbe dq d ={⊤}=∗
      backend.wbTok d.γB ∗ dghostVar E.γbe dq d := by
  iintro #Hp Hr Hlc Hg
  ihave #Hp' := Hp
  iunfold srvWTPoolR at Hp'
  iinv Hp' with ⟨%a, %d0, >Ha, >Hg0, #Hs0, >Hc, Hrt⟩ Hclose
  ihave %Hdd := dghostVar_agree E.γbe d dq d0 _ $$ Hg Hg0
  subst Hdd
  imod lc_fupd_elim_later (E := ⊤ \ ↑srvWTN) $$ Hlc Hs0 with #Hs1
  imod Hclose $$ [Ha Hg0 Hc Hrt] with -
  · inext
    iexists a, d
    iframe Ha Hg0 Hs0 Hc Hrt
  imod srvWTStock_take E γp d $$ Hp Hs1 Hr with Ht
  imodintro
  iframe Ht Hg

/-- **Draft of `srv_be_swap`** (D22's, `SnapApply.lean:119`): the new backend's stock fact in place
of its `n'` tokens (made before `Restore`, `srvWTStock_alloc`); the old backend's tokens stay in its
stock (its `Close` needs its `bOpen` shares, not its write tokens). The rest as today. -/
theorem srv_be_swapR (s : Loc) (E : apply.AEnv GF) (γp : GName) (d' : mvcc.KBReal) :
    srvWTPoolR E γp ⊢ bemuP s E.γbe 1 -∗ srvBeOwn s E -∗ srvBeRO d' -∗ srvWTStockInv γp d' -∗
      mvcc.bkRTx d'.γB d'.P d'.be -∗ £ 1 -∗
      |={⊤}=> ∃ d : mvcc.KBReal, ⌜E.γ.kb = some d⌝ ∗ srvBeAddr s ↦ srvBeIface d.be ∗
        mvcc.bkRTx d.γB d.P d.be ∗ srvBeRO d ∗
        (srvBeAddr s ↦ srvBeIface d'.be -∗ bemuP s E.γbe 1 ∗
          srvBeAddr s ↦{DFrac.own (1 : Qp).half} srvBeIface d'.be ∗
          dghostVar E.γbe (DFrac.own (1 : Qp).half.half) d') := by
  iintro #Hp Hbm Hbo #Hro' #Hs' Hrt' Hlc
  iunfold bemuP at Hbm
  icases Hbm with ⟨%d1, Hbe1, Hg1, #Hro1⟩
  iunfold srvBeOwn at Hbo
  icases Hbo with ⟨%d, %Hd, Hbe2, Hg2⟩
  icombine Hg1 Hg2 gives %Hag
  obtain ⟨-, rfl⟩ := Hag
  icombine Hbe1 Hbe2 as Hbe
  unfold srvWTPoolR
  iinv Hp with ⟨%a, %d2, >Ha, >Hg3, #Hs2, >Hc, Hrt⟩ Hclose
  icombine Hg1 Hg3 gives %Hag2
  obtain ⟨-, rfl⟩ := Hag2
  icombine Hg2 Hg3 as Hg23
  icombine Hg1 Hg23 as Hg
  imod lc_fupd_elim_later (E := ⊤ \ ↑srvWTN) $$ Hlc Hrt with Hrt
  icases Hrt with (Hrt | ⟨%q, Hq⟩)
  rotate_left
  · iexfalso
    icombine Hg Hq gives %Hv
    obtain ⟨Hv, -⟩ := Hv
    exact absurd (DFrac.valid_own.1 Hv) (Qp_one_add_not_le q)
  icases (typedPointsto_half_combine (srvBeAddr s) (srvBeIface d1.be) (srvBeIface d1.be) 1)
    $$ Hbe with ⟨-, Hbe⟩
  imod dghostVar_update d' E.γbe d1 $$ Hg with Hg
  icases (dghostVar_split (GF := GF) E.γbe d' (DFrac.own (1 : Qp).half) (DFrac.own (1 : Qp).half))
    $$ [Hg] with ⟨Hgm, Hg⟩
  · rw [DFrac.op_own, Qp.half_add_half]; iexact Hg
  icases (dghostVar_split (GF := GF) E.γbe d' (DFrac.own (1 : Qp).half.half)
      (DFrac.own (1 : Qp).half.half)) $$ [Hg] with ⟨HgA, HgW⟩
  · rw [DFrac.op_own, Qp.half_add_half]; iexact Hg
  imod Hclose $$ [Ha HgW Hc Hrt'] with -
  · inext
    iexists a, d'
    iframe Ha HgW Hs' Hc
    ileft; iexact Hrt'
  imodintro
  iexists d1
  iframe Hbe Hrt Hro1
  isplitr
  · ipureintro; exact Hd
  iintro Hbe
  icases (typedPointsto_half_split (srvBeAddr s) (srvBeIface d'.be) 1).1 $$ Hbe with ⟨Hb1, Hb2⟩
  iframe Hb2 HgA
  iunfold bemuP
  iexists d'
  iframe Hb1 Hgm Hro'

/-! ## The apply environment by the mode -/

/-- **Draft of `srvEnvOk`** (D22's, `InvApplier.lean:478`), over N1's `apply.AEnvD`: the store's
backend at the server's mode (`d.cm = E.cmp`) in place of `d.cm = false` (Q5-4's restriction,
withdrawn: restore works in compaction mode). -/
def srvEnvOkD (s : Loc) (γ : ApplyNames) (ci : Loc) (E : apply.AEnvD GF) (cl : Loc) : Prop :=
  E.FS = srvFS s ∧ E.ciC = srvCiC γ ci ∧
    ∃ (γB : backend.BNames) (H : IProp GF), E.RO = srvRestOwnH γB cl H ∧ E.RW = srvRestRWH γB H ∧
      ∃ (d : mvcc.KBReal) (al st lp : Loc), E.γ.kb = some d ∧ d.γB = γB ∧
        H = srvObjsOn al st lp cl d.be ∧ d.cm = E.cmp

/-- **At the off mode it is today's.** -/
theorem srvEnvOkD_off (s : Loc) (γ : ApplyNames) (ci : Loc) (E : apply.AEnvD GF) (cl : Loc)
    (h : E.cmp = false) : srvEnvOkD s γ ci E cl ↔ srvEnvOk s γ ci E.toAEnv cl := by
  unfold srvEnvOkD srvEnvOk
  rw [h]

/-- **The install keeps the mode** (the step `SnapApplyDefs`/`SnapApplyIsServer` make, at
`hcm' : d'.cm = d.cm` in place of `d'.cm = false`): the new backend at the old one's mode, so the
store's mode is the server's after it too (`envAgreeD`'s mode clause, S5'). -/
theorem srvEnvOkD_mode_step (E E' : apply.AEnvD GF) (d d' : mvcc.KBReal)
    (hkb' : E'.γ.kb = some d') (hcm : d.cm = E.cmp) (hcm' : d'.cm = d.cm)
    (hE : E'.cmp = E.cmp) :
    d'.cm = E'.cmp ∧ (mvcc.kbCmpM E'.γ.kb ↔ E'.cmp = true) := by
  refine ⟨by rw [hcm', hcm, hE], ?_⟩
  rw [hkb', mvcc.kbCmpM_some_iff, hcm', hcm, hE]

/-! ## The KV's closer by the mode -/

/-- **Draft of `srvKVCloser`** (D22's, `InvWatchBuilt.lean:70`), by the mode, at the store's
compaction revision `c`: off, today's (the watchable store's closer) at `c = -1`; on, the watchable
store's own parts and the inner store's restorable compaction right at `c` (`mvcc.wsCloserR`: a
compacting store keeps its closer, so `Cleanup`'s close, Q3, would have it too). -/
def srvKVCloserM (s : Loc) (E : apply.AEnv GF) (c : Int) : IProp GF :=
  if mvcc.kbCmpM E.γ.kb then
    iprop(∃ wsl : Loc,
      srvKVAddr s ↦□ (interface.mkOk (go.GoType.PointerType
        go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty) #wsl : GoInterface) ∗
      mvcc.wsCloserR wsl E.s E.γ c)
  else iprop(srvKVCloser s E ∗ ⌜c = -1⌝)

theorem srvKVCloserM_on (s : Loc) (E : apply.AEnv GF) (c : Int) (h : mvcc.kbCmpM E.γ.kb) :
    srvKVCloserM (GF := GF) s E c ⊣⊢ ∃ wsl : Loc,
      srvKVAddr s ↦□ (interface.mkOk (go.GoType.PointerType
        go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty) #wsl : GoInterface) ∗
      mvcc.wsCloserR wsl E.s E.γ c := by
  unfold srvKVCloserM; simp only [h, ↓reduceIte]; exact .rfl

theorem srvKVCloserM_off (s : Loc) (E : apply.AEnv GF) (c : Int) (h : ¬ mvcc.kbCmpM E.γ.kb) :
    srvKVCloserM (GF := GF) s E c ⊣⊢ srvKVCloser s E ∗ ⌜c = -1⌝ := by
  unfold srvKVCloserM; simp only [h, ↓reduceIte]; exact .rfl

/-- **`NewServer`'s step, on** (draft; after its last error return, in place of
`compactRight_of_wsCloser`): the kept closer and the authority's half make the closer by the mode
at `-1`. -/
theorem srvKVCloserM_of_new (s : Loc) (E : apply.AEnv GF) (h : mvcc.kbCmpM E.γ.kb) :
    ⊢ srvKVCloser (GF := GF) s E -∗ mvcc.crevRightM E.γ ={⊤}=∗ srvKVCloserM s E (-1) := by
  iintro Hcl Hcr
  iunfold srvKVCloser at Hcl
  icases Hcl with ⟨%wsl, #Hkv, Hcl⟩
  imod mvcc.wsCloserR_of_wsCloser wsl E.s E.γ h ⊤ $$ Hcl Hcr with Hr
  unfold srvKVCloserM
  simp only [h, ↓reduceIte]
  imodintro
  iexists wsl
  iframe Hkv Hr

/-! ## `RestorePre`, drafted -/

/-- **Draft of `restorePre_of_apply`** (D22's, `RestorePre.lean:54`, whose `crevFrozen` is a `sorry`
today), in either mode: from the apply thread's KV resources and the closer by the mode, the store's
restore right by the mode (`restoreRightM`, `watchableStore.Restore.specM`'s), the rest as today.
Off, the frozen fact is the watchable store's own (`isWatchableStore`'s `Hfrz`: at the switch, its
mode-gated `wsFrozenM`, `isWatchableStoreD_frozen`); on, there is none: the compaction right is
taken instead. No `sorry`. -/
theorem restorePre_of_applyM (s : Loc) (E : apply.AEnv GF) (log : mvcc.Log) (c : Int)
    (hwq : E.γ.watchQ = true) :
    apply.kvOwn E log ∗ srvKVCloserM s E c ⊢
      ∃ (ws : Loc) (γw : mvcc.WsNames), ⌜γw.st = E.γ⌝ ∗ mvcc.isWatchableStore ws E.s γw ∗
        mvcc.restoreRightM E.s γw.st c ∗ mvcc.writerFrag γw.st ∗ mvcc.writerOwn γw.st ∗
        mvcc.watchWriter γw log ∗
        (mvcc.storeReader E.s E.γ ∗ apply.leasesLive E.γ (mvcc.stateAfter log) ∗ E.RD) ∗
        (∃ (wsl stc : Loc), srvKVAddr s ↦□ (interface.mkOk (go.GoType.PointerType
            go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty) #wsl : GoInterface) ∗
          structFieldRef go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore go!"stopc" wsl ↦□ stc ∗
          mvcc.stopCloser stc ∗ mvcc.wsWaiter wsl) := by
  iintro ⟨Hown, Hcl⟩
  iunfold apply.kvOwn at Hown
  icases Hown with ⟨Hrd, Hkw, Hll, HRD, Hwo⟩
  iunfold txn.kvWriter at Hkw
  icases Hkw with ⟨Hsw, Hwl, Hfrag⟩
  iunfold txn.wlogOwn at Hwl
  rw [hwq]
  simp only [↓reduceIte]
  icases Hwl with ⟨%ws, %γw, %hγw, #Hws, Hwl, -⟩
  -- the closer by the mode: the store's restore right and the watchable store's own parts
  ihave ⟨Hr, Hcp⟩ : iprop(mvcc.restoreRightM E.s γw.st c ∗
      ∃ (wsl stc : Loc), srvKVAddr s ↦□ (interface.mkOk (go.GoType.PointerType
          go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty) #wsl : GoInterface) ∗
        structFieldRef go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore go!"stopc" wsl ↦□ stc ∗
        mvcc.stopCloser stc ∗ mvcc.wsWaiter wsl) $$ [Hcl]
  · rw [hγw]
    by_cases h : mvcc.kbCmpM E.γ.kb
    · icases (srvKVCloserM_on s E c h).1 $$ Hcl with ⟨%wsl, #Hkvf, Hcl⟩
      icases mvcc.wsCloserR_split wsl E.s E.γ c h $$ Hcl with ⟨Hr, ⟨%stc, #Hstc, Hstcl, Hwsw⟩⟩
      iframe Hr
      iexists wsl, stc
      iframe Hkvf Hstc Hstcl Hwsw
    · icases (srvKVCloserM_off s E c h).1 $$ Hcl with ⟨Hcl, %Hc⟩
      iunfold srvKVCloser at Hcl
      icases Hcl with ⟨%wsl, #Hkvf, Hcl⟩
      iunfold mvcc.wsCloser at Hcl
      icases Hcl with ⟨%stc, #Hstc, Hstcl, Hwsw, Hcl⟩
      ihave #Hfrz : mvcc.crevFrozen E.γ $$ []
      · iunfold mvcc.isWatchableStore at Hws
        iNamed Hws
        rw [← hγw]
        iexact Hfrz
      isplitl [Hcl]
      · iapply (mvcc.restoreRightM_off E.s E.γ c h).2
        iframe Hcl Hfrz
        ipureintro; exact Hc
      iexists wsl, stc
      iframe Hkvf Hstc Hstcl Hwsw
  iexists ws, γw
  iunfold mvcc.watchWriter
  rw [hγw]
  iframe Hws Hr Hfrag Hwo Hrd Hll HRD Hcp
  isplitr
  · ipureintro; rfl
  iunfold txn.soleWriter at Hsw
  icases Hsw with ⟨#Hc, Htoks, -⟩
  simp only [txn.soleBudget, mvcc.wBudget]
  iframe Hc Htoks Hwl

/-! ## The restore step composes -/

/-- **After `Restore`, the new closer** (the walk's step after `watchableStore.Restore.specM`, in
place of `srvKVCloser`'s re-make, `SnapApplyPost`): the right `Restore` hands back at the new names
and the restored revision `c'`, with the watchable store's own parts kept from `restorePre_of_applyM`,
make the new environment's closer by the mode, the mode being the old one's (`d'.cm = d.cm`; off,
the image's revision is `-1`, `restoreImageM_off`). -/
theorem snap_closer_after (s : Loc) (E E' : apply.AEnv GF) (p' : mvcc.PhysNames) (d d' : mvcc.KBReal)
    (c' : Int) (hs : E'.s = E.s) (hγ : E'.γ = E.γ.withPhys p') (hkb : E.γ.kb = some d)
    (hkb' : p'.kb = some d') (hcm' : d'.cm = d.cm) (hc' : d.cm = false → c' = -1) :
    mvcc.restoreRightPostM (GF := GF) E.s (E.γ.withPhys p') c' ∗
        (∃ (wsl stc : Loc), srvKVAddr s ↦□ (interface.mkOk (go.GoType.PointerType
            go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty) #wsl : GoInterface) ∗
          structFieldRef go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore go!"stopc" wsl ↦□ stc ∗
          mvcc.stopCloser stc ∗ mvcc.wsWaiter wsl) ⊢
      srvKVCloserM s E' c' ∗ ⌜mvcc.kbCmpM E'.γ.kb ↔ mvcc.kbCmpM E.γ.kb⌝ := by
  have hmode : mvcc.kbCmpM E'.γ.kb ↔ mvcc.kbCmpM E.γ.kb := by
    rw [hγ, mvcc.StoreNames.withPhys_kb, hkb', hkb, mvcc.kbCmpM_some_iff, mvcc.kbCmpM_some_iff, hcm']
  iintro ⟨Hr, ⟨%wsl, %stc, #Hkvf, #Hstc, Hstcl, Hwsw⟩⟩
  isplitl
  · by_cases h : mvcc.kbCmpM E'.γ.kb
    · have h' : mvcc.kbCmpM (E.γ.withPhys p').kb := by rw [← hγ]; exact h
      unfold srvKVCloserM
      simp only [h, ↓reduceIte]
      iexists wsl
      iframe Hkvf
      rw [hs, hγ]
      iapply mvcc.wsCloserR_join wsl E.s (E.γ.withPhys p') c' h' $$ [Hr Hstcl Hwsw]
      iframe Hr
      iexists stc
      iframe Hstc Hstcl Hwsw
    · have h' : ¬ mvcc.kbCmpM (E.γ.withPhys p').kb := by rw [← hγ]; exact h
      ihave Hr := (mvcc.restoreRightPostM_off E.s (E.γ.withPhys p') c' h').1 $$ Hr
      -- off: `Restore`'s image premise made `c' = -1` (`restoreImageM_off`): the closer at `-1`
      have hoff : d.cm = false := by
        have : ¬ mvcc.kbCmpM E.γ.kb := fun h2 => h (hmode.2 h2)
        rw [hkb, mvcc.kbCmpM_some_iff] at this; simpa using this
      unfold srvKVCloserM
      simp only [h, ↓reduceIte]
      isplitl
      · iunfold srvKVCloser
        iexists wsl
        iframe Hkvf
        rw [hs, hγ]
        iunfold mvcc.wsCloser
        iexists stc
        iframe Hstc Hstcl Hwsw Hr
      ipureintro; exact hc' hoff
  ipureintro; exact hmode

/-- **Before `Restore`, the new backend's supply** (the walk's step after `OpenSnapshotBackend`, in
place of handing `srv_be_swap` the new tokens after it): the new backend's stock from its fresh
tokens, and with it the supply `watchableStore.Restore.specM` takes for the compaction `restore()`
resumes; the stock fact is kept for `srv_be_swapR`. -/
theorem snap_supply_before (E : apply.AEnv GF) (γp : GName) (d' : mvcc.KBReal) (n : Nat)
    (h : receiptBound GF ≤ n + 1) :
    ⊢ srvWTPoolR (GF := GF) E γp -∗ ownToks d'.γB.wb n ={⊤}=∗
      srvWTStockInv γp d' ∗ mvcc.kbWTSupplyM (some d') := by
  iintro #Hp Hn
  imod srvWTStock_alloc γp d' n h ⊤ $$ Hn with #Hs
  imodintro
  iframe Hs
  iapply kbWTSupplyM_of_stock E γp d' $$ [$Hp $Hs]

end draft

end EtcdGrove
end Perennial

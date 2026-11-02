/-
**M2, the storage side, step 2: the server's side of restore in compaction mode (Draft)**
(`notes/m2-storage-plan.md`, "Step 2: restore in compaction mode"). Imported by nothing; no `axiom`,
no `sorry`; nothing switched. D22's statements are the collaborator's: each `…D`/`…R`/`…M` here is a
draft of one, for them to read.

- **The write-back supply follows the backend** (task 2; `kbWTSupplyM`, Q1 (a): `store.Compact`'s
  premise; made real in stage B1, 2026-11-02, `InvApplier.lean`). The write budget's tokens move out of `srvWTPool`'s invariant into **one stock invariant
  per backend** (`srvWTStockInv γp d`, persistent, named by the backend `d`, which never changes),
  sharing the pool's receipt counter `γp` (a lower bound in each stock): the pool keeps the receipts,
  the counter's authority, its quarter of `E.γbe` at the current backend and that backend's stock
  fact (`srvWTPool`). A taker at any backend with a stock takes a receipt into the pool and a token
  from the stock (`srvWTStock_take`); so the supply of `d` is persistent
  (`kbWTSupplyM_of_stock`), and survives `applySnapshot`'s swap, which still gathers the whole of
  `E.γbe` (`srv_be_swap`: it takes the new backend's stock fact in place of its tokens, and no
  longer hands out the old backend's tokens, which `Close` does not need). The new backend's stock is
  made from its fresh tokens (`srvWTStock_alloc`) *before* `Restore`, which needs the supply for the
  compaction `restore()` resumes. No more tokens than today: one stock of `receiptBound - 1` per
  backend, as the pool's today (the shared counter bounds all takes together). Alternatives in the
  plan (questions for the user).
- **The apply environment's facts by the mode** (`srvEnvOkD`: `d.cm = E.cmp` in place of
  `d.cm = false`, over N1's `apply.AEnv` with `cmp`), with the step the install makes (`srvEnvOkD_mode_step`).
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

/-! ## The write budget's supply, one stock per backend

The stocks themselves (`srvWTStockInv`, `srvWTStock_alloc`, `srvWTStock_take`, `srvWTPool_stockOf`)
and the pool over them (`srvWTPool`) are in `InvApplier.lean` (stage B1, 2026-11-02); the swap is
`srv_be_swap`. What is left here is the supply the compaction mode takes. -/

/-- **The compaction's write-back supply of any backend with a stock** (draft; in place of
`kbWTSupplyM_of_srvWTPool`, whose discarded part of `E.γbe` P4's withdrawal took away): persistent,
good after any number of swaps. -/
theorem kbWTSupplyM_of_stock (E : apply.AEnv GF) (γp : GName) (d : mvcc.KBReal) :
    srvWTPool (GF := GF) E γp ∗ srvWTStockInv γp d ⊢ mvcc.kbWTSupplyM (some d) := by
  iintro ⟨#Hp, #Hs⟩
  unfold mvcc.kbWTSupplyM
  split
  · unfold mvcc.kbWTSupply
    iintro !> Hr
    imod monoNatLbOwn_0 (GF := GF) γp with #H0
    imod srvWTStock_take E γp d 0 $$ Hp Hs Hr H0 with ⟨Ht, -⟩
    imodintro
    iexact Ht
  · itrivial

/-- **The compaction arm's supply** (review round 3's S5: the law the apply loop's compaction arm
uses, `store.Compact.specD`'s `kbWTSupplyM γ.kb`): the apply thread's part of the backend's name
(`srvBeOwn`, which it holds) agrees with the pool's, whose stock fact (under the pool's `▷`: a
later credit) gives the current backend's supply. -/
theorem kbWTSupplyM_of_poolR (s : Loc) (E : apply.AEnv GF) (γp : GName) :
    ⊢ srvWTPool (GF := GF) E γp -∗ srvBeOwn s E -∗ £ 1 ={⊤}=∗
      srvBeOwn s E ∗ mvcc.kbWTSupplyM E.γ.kb := by
  iintro #Hp Hbo Hlc
  icases srvBeOwn_frag s E $$ Hbo with ⟨%d, %Hd, Hg, Hbo⟩
  imod srvWTPool_stockOf E γp d _ $$ Hp Hlc Hg with ⟨#Hs, Hg⟩
  ihave Hbo := Hbo $$ Hg
  imodintro
  iframe Hbo
  rw [Hd]
  iapply kbWTSupplyM_of_stock E γp d $$ [$Hp $Hs]

/-! ## The apply environment by the mode -/

/-- **Draft of `srvEnvOk`** (D22's, `InvApplier.lean:478`), over N1's `apply.AEnv` with `cmp`: the store's
backend at the server's mode (`d.cm = E.cmp`) in place of `d.cm = false` (Q5-4's restriction,
withdrawn: restore works in compaction mode). -/
def srvEnvOkD (s : Loc) (γ : ApplyNames) (ci : Loc) (E : apply.AEnv GF) (cl : Loc) : Prop :=
  E.γ.cm = E.cmp ∧ E.FS = srvFS s ∧ E.ciC = srvCiC γ ci ∧
    ∃ (γB : backend.BNames) (H : IProp GF), E.RO = srvRestOwnH γB cl H ∧ E.RW = srvRestRWH γB H ∧
      ∃ (d : mvcc.KBReal) (al st lp : Loc), E.γ.kb = some d ∧ d.γB = γB ∧
        H = srvObjsOn al st lp cl d.be ∧ d.cm = E.cmp

/-- **At the off mode it is today's.** -/
theorem srvEnvOkD_off (s : Loc) (γ : ApplyNames) (ci : Loc) (E : apply.AEnv GF) (cl : Loc)
    (h : E.cmp = false) : srvEnvOkD s γ ci E cl ↔ srvEnvOk s γ ci E cl := by
  unfold srvEnvOkD srvEnvOk
  rw [h]

/-- **The install keeps the mode** (the step `SnapApplyDefs`/`SnapApplyIsServer` make, at
`hcm' : d'.cm = d.cm` in place of `d'.cm = false`): the new backend at the old one's mode, so the
store's mode is the server's after it too (`envAgreeD`'s mode clause, S5'). -/
theorem srvEnvOkD_mode_step (E E' : apply.AEnv GF) (d d' : mvcc.KBReal)
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
step 1's discarding `compactRight_of_wsCloser`, dropped): the kept closer and the authority's half make the closer by the mode
at `-1`. -/
theorem srvKVCloserM_of_new (s : Loc) (E : apply.AEnv GF) (h : mvcc.kbCmpM E.γ.kb)
    (hc : E.γ.cm = true) :
    ⊢ srvKVCloser (GF := GF) s E -∗ mvcc.crevRightM E.γ ={⊤}=∗ srvKVCloserM s E (-1) := by
  iintro Hcl Hcr
  iunfold srvKVCloser at Hcl
  icases Hcl with ⟨%wsl, #Hkv, Hcl⟩
  imod mvcc.wsCloserR_of_wsCloser wsl E.s E.γ hc ⊤ $$ Hcl Hcr with Hr
  unfold srvKVCloserM
  simp only [h, ↓reduceIte]
  imodintro
  iexists wsl
  iframe Hkv Hr

/-! ## `RestorePre`, drafted -/

/-- **Draft of `restorePre_of_apply`** (D22's, `RestorePre.lean:54`, whose `crevFrozen` is a `sorry`
today), in either mode: from the apply thread's KV resources and the closer by the mode, the store's
restore right by the mode (`restoreRightM`, `watchableStore.Restore.specM`'s), the rest as today.
Off, the frozen fact is the watchable store's own, by a law (`isWatchableStore_frozen`: at the
switch `isWatchableStoreD_frozen`, its `wsFrozenM` mode-gated; review round 3's S7, no unfold); on, there is none: the compaction right is
taken instead. No `sorry`. -/
theorem restorePre_of_applyM (s : Loc) (E : apply.AEnv GF) (log : mvcc.Log) (c : Int)
    (hwq : E.γ.watchQ = true) (htie : mvcc.kbCmpM E.γ.kb ↔ E.γ.cm = true) :
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
  icases Hwl with ⟨Hwl, Hpin⟩
  iunfold txn.wlogOwnW at Hwl
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
      · rw [← hγw]
        iapply mvcc.isWatchableStore_frozen ws E.s γw
          (by rw [hγw]; exact Bool.eq_false_iff.mpr (fun hc => h (htie.2 hc))) $$ Hws
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
  iframe Hc Htoks Hwl Hpin

/-! ## The restore step composes -/

/-- **After `Restore`, the new closer** (the walk's step after `watchableStore.Restore.specM`, in
place of `srvKVCloser`'s re-make, `SnapApplyPost`): the right `Restore` hands back at the new names
and the restored revision `c'`, with the watchable store's own parts kept from `restorePre_of_applyM`,
make the new environment's closer by the mode, the mode being the old one's (`d'.cm = d.cm`; off,
the image's revision is `-1`, `restoreImageM_off`). -/
theorem snap_closer_after (s : Loc) (E E' : apply.AEnv GF) (p' : mvcc.PhysNames) (d d' : mvcc.KBReal)
    (c' : Int) (hs : E'.s = E.s) (hγ : E'.γ = E.γ.withPhys p') (hkb : E.γ.kb = some d)
    (hkb' : p'.kb = some d') (hcm' : d'.cm = d.cm) (hc' : d.cm = false → c' = -1) :
    mvcc.storeCloserM (GF := GF) E.s (E.γ.withPhys p') c' ∗
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
      ihave Hr := (mvcc.storeCloserM_off E.s (E.γ.withPhys p') c' h').1 $$ Hr
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
resumes; the stock fact is kept for `srv_be_swap`. -/
theorem snap_supply_before (E : apply.AEnv GF) (γp : GName) (d' : mvcc.KBReal) (n : Nat)
    (h : receiptBound GF ≤ n + 1) :
    ⊢ srvWTPool (GF := GF) E γp -∗ ownToks d'.γB.wb n ={⊤}=∗
      srvWTStockInv γp d' ∗ mvcc.kbWTSupplyM (some d') := by
  iintro #Hp Hn
  imod srvWTStock_alloc γp d' n h ⊤ $$ Hn with #Hs
  imodintro
  iframe Hs
  iapply kbWTSupplyM_of_stock E γp d' $$ [$Hp $Hs]

end draft

end EtcdGrove
end Perennial

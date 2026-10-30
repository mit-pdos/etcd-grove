/-
**M2, the storage side: the server's glue over the Draft** (`notes/m2-storage-plan.md`; revised
after review round 1, `notes/spec-first-study/m2-storage-review-1.md`). Imported by nothing. What
`NewServer` and the apply thread do with the drafted mvcc statements (`mvcc/M2StorageDraft.lean`),
proved against them before any proof is switched:

- `server_kv_watchable_ofD` (review round 1's S1: one lemma over the backend record `d`, the mode
  `d.cm`, in place of `server_kv_watchable_of` and the round's `server_kv_watchable_ofC`): the
  server's KV from `New.specD` over the backend `d` in either mode: the deletable keys fixed by the
  mode (nothing deletable off, the store's keys on: `storeDlReg`), the compaction keys' values
  tracked when compacting (`□ (⌜d.cm = true⌝ -∗ fkV)`, as `mvcc_NewStore_backend` takes it), the
  safe-range slot in either mode (`mvcc.kbSRM_some`). Its post: the store at `kb = some d`,
  `actualMaxReaders - nJobRd (some d) - 2` watch readers, `retiredAt γ (nJobRd (some d))`, the
  closer and `crevRightM γw.st` (the right made after `NewServer`'s last error return,
  `mvcc.compactRight_of_wsCloser` with `mvcc.kbCmpM_some`; the round's wrapper
  `newServer_compactRight` dropped, S2). It gives `watchWriter`/`writerFrag` in place of today's
  `txn.isKV`/`txn.kvWriter`, which are defined over today's `isWatchableStore` (a Draft artifact:
  at the switch the predicate is redefined in place and they follow as today).
- `kbWTSupplyM_of_srvWTPool`: R2-7's conversion (unchanged; its discarded part of `E.γbe` had F2
  as its source, which the user withdrew with P4 on 2026-10-30, "restore must work in compaction
  mode": the supply's server source is pending step 2, `notes/m2-storage-plan.md`).
- **F2 withdrawn** (2026-10-30, the user's decisions after `lean`'s Stage P): `srvBeFrac`,
  `srvBeOwnD`, `srvBeOwnD_off`, `srvBeOwnD_frozen`, `kbWTSupplyM_of_srvBeOwnD` and `srvBe_allocD`
  are gone (step 2 replaces them; review round 2's S1' and S2' with them).
- **N1, the server's mode in its apply environment** (review round 2's N1; the route decided after
  the round, `notes/m2-storage-plan.md`): `apply.AEnvD` (`apply.AEnv` with the field `cmp`),
  `envAgreeD` (today's `envAgree` with `E.cmp = E'.cmp` and the mode clause `kbCmpM E.γ.kb ↔
  E.cmp = true`: S5', the one reading of the mode), its laws (`envAgreeD_agree`, `envAgreeD_off`,
  `envAgreeD_on`, `envAgreeD_mode`) and `NewServer`'s step (`envAgreeD_of_new`, at
  `NewServer.lean:1039`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BuildLemmas
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplier
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.M2StorageDraft

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

/-- **R2-7's conversion** (`notes/backend-cmp-plan.md`, "R2-7, D22's side"): the server's write
budget (`srvWTPool`) at the boot backend `d`, with a discarded part of the current backend's ghost
variable at `d` (persistent: `d` stays the backend for good, as in a server that installs no
snapshot), is the compaction's write-back supply (`kbWTSupplyM`), from the same stock: each
conversion takes a receipt into the pool (`srvWTPool_take_extra_d`). -/
theorem kbWTSupplyM_of_srvWTPool (E : apply.AEnv GF) (γp : GName) (d : mvcc.KBReal) :
    srvWTPool (GF := GF) E γp ∗ dghostVar E.γbe DFrac.discard d ⊢ mvcc.kbWTSupplyM (some d) := by
  iintro ⟨#Hp, #Hg⟩
  unfold mvcc.kbWTSupplyM
  split
  · unfold mvcc.kbWTSupply
    iintro !> Hr
    imod srvWTPool_take_extra_d E γp d _ $$ Hp Hr Hg with ⟨Ht, -⟩
    imodintro
    iexact Ht
  · itrivial

/-- **A real backend's write-back tokens are the store's write supply** (review round 2's S6': a
law of txn's, so the server's glue does not unfold `txn.storeWTs`; goes to `txn/Defs.lean` at the
switch). -/
theorem txn.storeWTs_someD (γ : mvcc.StoreNames) (d : mvcc.KBReal) (hd : γ.kb = some d) (n : Nat) :
    ownToks (GF := GF) d.γB.wb n ⊢ txn.storeWTs γ n := by
  unfold txn.storeWTs
  rw [hd]

/-- **`server_kv_watchable_of` over the backend record `d`, in either mode** (S1; see the file
header). -/
theorem server_kv_watchable_ofD
    (hNew : mvcc.New.specD (GF := GF) (hG := hG))
    (hCRT : backend.backend.ConcurrentReadTx.spec (GF := GF) (hG := hG))
    (hRT : backend.backend.ReadTx.spec (GF := GF) (hG := hG))
    (hBT : backend.backend.BatchTx.spec (GF := GF) (hG := hG))
    (hFC : backend.backend.ForceCommit.spec (GF := GF) (hG := hG))
    (hSz : backend.backend.Size.spec (GF := GF) (hG := hG))
    (hSzU : backend.backend.SizeInUse.spec (GF := GF) (hG := hG))
    (hcRL : backend.concurrentReadTx.RLock.spec (GF := GF) (hG := hG))
    (hcRU : backend.concurrentReadTx.RUnlock.spec (GF := GF) (hG := hG))
    (hcUR : backend.concurrentReadTx.UnsafeRange.spec (GF := GF) (hG := hG))
    (hrRL : backend.readTx.RLock.spec (GF := GF) (hG := hG))
    (hrRU : backend.readTx.RUnlock.spec (GF := GF) (hG := hG))
    (hrUR : backend.readTx.UnsafeRange.spec (GF := GF) (hG := hG))
    (hLI : backend.batchTxBuffered.LockInsideApply.spec (GF := GF) (hG := hG))
    (hLO : backend.batchTxBuffered.LockOutsideApply.spec (GF := GF) (hG := hG))
    (hSP : backend.batchTxBuffered.UnsafeSeqPut.spec (GF := GF) (hG := hG))
    (hUL : backend.batchTxBuffered.Unlock.spec (GF := GF) (hG := hG))
    (hbUR : backend.batchTxBuffered.UnsafeRange.spec (GF := GF) (hG := hG))
    (hCB : backend.batchTxBuffered.UnsafeCreateBucket.spec (GF := GF) (hG := hG))
    (hDel : backend.batchTxBuffered.UnsafeDelete.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    (hLSR : backend.backend.LockForSafeRangeDelete.spec (GF := GF) (hG := hG))
    (hUSR : backend.backend.UnlockForSafeRangeDelete.spec (GF := GF) (hG := hG))
    (hUP : backend.batchTxBuffered.UnsafePut.spec (GF := GF) (hG := hG))
    (lg : Loc) (le : GoInterface)
    (cfg : go_etcd_io.etcd.server.v3.storage.mvcc.StoreConfig)
    (d : mvcc.KBReal) (hP : mvcc.bridgeParams d.P) (γb γl : GName)
    (Pk : IProp GF) (f : val) (rd0 : GoFunc) (N : Nat) (γi : mvcc.IdxNames) (γok : GName)
    (M : auth.AuthMode)
    (hcfg : mvcc.batchLimitOk cfg.CompactionBatchLimit')
    (hrb : receiptBound GF ≤ 2 ^ 48) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
        backend.isBackend d.γB d.P (mvcc.lateW d.gx) Pk d.be ∗ mvcc.keySized d.γB d.P d.be ∗
        backend.dlInit d.γB ∗ □ (⌜d.cm = true⌝ -∗ backend.fkV d.γB true) ∗
        mvcc.bkView d.γB 1 (∅ : mvcc.Bucket) ∗ mvcc.bkNoCmp d.γB ∗ mvcc.lateReg d.gx ∗
        ownToks d.γB.wb (N + 2) ∗ backend.srSlot d.be ∗
        ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (),
          mvcc.bkRTx d.γB d.P d.be) ∗
        lease.lessorRdOf γl ∗ mvcc.isLessor le γl ∗ lease.rdOwn γl rd0 ∗
        mvcc.idxFresh γi ∗ ghostMapAuth γok 1 (∅ : GMap w64 mvcc.Log) }}
      (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.New)) (Val #lg))
        (Val #(interface.mkOk
          (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #d.be)))
        (Val #le)) (Val #cfg))
    {{ (ws : Loc), RET #(interface.mkOk
          (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty) #ws);
        ∃ (st : Loc) (γw : mvcc.WsNames),
        ⌜γw.st.bucket = γb ∧ γw.st.leases = γl ∧ γw.st.kb = some d ∧ γw.st.idx = γi ∧
          γw.st.cok = γok⌝ ∗
        (∃ rv : Loc, st.[go_etcd_io.etcd.server.v3.storage.mvcc.store, go!"ReadView"] ↦□
            (interface.mkOk (go.GoType.PointerType
              go_etcd_io.etcd.server.v3.storage.mvcc.readView.ty) #rv : GoInterface) ∗
          mvcc.isReadView rv st γw.st) ∗
        mvcc.hookInit γw.st Pk f ∗ mvcc.watchWriter γw [[], []] ∗ mvcc.writerFrag γw.st ∗
        txn.storeWTs γw.st N ∗ ghostMapAuth γw.st.cok 1 (∅ : GMap w64 mvcc.Log) ∗
        mvcc.isWatchableStoreD ws st γw ∗ mvcc.watchToks γw (2 ^ 63 - 3) ∗
        ([∗list] _x ∈ List.replicate
            (Int.toNat sync.rwmutex.actualMaxReaders - mvcc.nJobRd (some d) - 2) (),
          mvcc.watchReader ws st γw) ∗
        mvcc.wsCloser ws st γw.st ∗ mvcc.crevRightM γw.st ∗
        mvcc.retiredAt γw.st (mvcc.nJobRd (some d)) ∗
        (∃ rd : GoFunc, lease.rdOwn γl rd ∗ mvcc.rdIs rd ws st γw) ∗ auth.modeTag γw.tag M }} := by
  iintro %Φ ⟨#Hpkg, #Hbpkg, #Hsch, #Hb, #Hsz, Hdl, #Hfv, Hv, Hncmp, Hrg, Hw, Hsr, Hrts, Hlrd,
    #Hle, Hro, Hif, Hok⟩ HΦ
  -- the backend's deletable keys fixed by the mode, and the store's contract the bridge's of it
  ihave Hsb : iprop(|==> □ ∀ (s : Loc) (γ : mvcc.StoreNames),
      ⌜γ.bucket = γb ∧ γ.kb = some d ∧ γ.idx = γi⌝ →
        mvcc.storeBackend (interface.mkOk (go.GoType.PointerType
          go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #d.be) s γ Pk) $$ [Hdl]
  · by_cases hcm : d.cm = true
    · imod mvcc.storeDlReg_fix d.γB γi $$ Hdl with #Hreg
      ihave #Hfk := Hfv $$ %hcm
      ihave #Hsb := mvcc.storeBackend_of_backendC hCRT hRT hBT hFC hSz hSzU hcRL hcRU hcUR hrRL
        hrRU hrUR hLI hLO hSP hUL hbUR hCB hDel hID hName hSafe hLSR hUSR hUP d hP Pk γb γi $$ []
      · iframe #
      imodintro; imodintro
      iexact Hsb
    · have hcm' : d.cm = false := by simpa using hcm
      imod backend.dlNoDel_fix d.γB $$ Hdl with #Hnd
      ihave #Hsb := mvcc.storeBackend_of_backend hCRT hRT hBT hFC hSz hSzU hcRL hcRU hcUR hrRL
        hrRU hrUR hLI hLO hSP hUL hbUR hCB hDel hID hName hSafe d hP hcm' Pk γb $$ []
      · iframe #
      imodintro; imodintro
      iintro %s %γ %hγ
      iapply Hsb
      ipureintro; exact ⟨hγ.1, hγ.2.1⟩
  imod Hsb with #Hsb
  imod auth.modeTag_alloc (GF := GF) M with ⟨%γtag, #Htag⟩
  rw [show N + 2 = (N + 1) + 1 by omega]
  icases ownToks_add_1 1 (N + 1) d.γB.wb $$ Hw with ⟨Hw, Hw1⟩
  icases ownToks_add_1 1 N d.γB.wb $$ Hw with ⟨Hw, Hw2⟩
  ihave Hsrm := mvcc.kbSRM_some d $$ Hsr
  iapply (hNew lg _ le cfg (some d) γb γl Pk f rd0 γi γok γtag hcfg hrb)
    $$ [Hv Hncmp Hrg Hw1 Hw2 Hsrm Hrts Hlrd Hro Hif Hok]
  · iframe Hpkg Hle Hro Hif Hok Hsrm Hsb
    simp only [mvcc.kbView_some, mvcc.kbNoCmp_some, mvcc.kbRegRight_some, mvcc.kbWT_some,
      mvcc.kbRT_some]
    unfold backend.wbTok
    iframe Hv Hncmp Hrg Hw1 Hw2 Hrts Hlrd
  inext
  iintro %ws ⟨%st, %γw, %Hγ, #Hws, Hro, #Hhk, Hww, Hwt, Hcok, Hrds, Hcl, Hcr, Hfrag, Hret⟩
  obtain ⟨hb, hl, hk, hi, hc, ht⟩ := Hγ
  ihave #Hrv := mvcc.isWatchableStoreD_readView ws st γw $$ Hws
  iapply HΦ
  iexists st, γw
  rw [ht]
  iframe Hws Hhk Hww Hfrag Hwt Hcok Hrds Hcl Hcr Hro Hret Htag Hrv
  isplitr
  · ipureintro; exact ⟨hb, hl, hk, hi, hc⟩
  iapply (txn.storeWTs_someD γw.st d hk N) $$ Hw

/-! ## N1: the server's compaction mode in its apply environment (review round 2's N1)

The watching examples hold `memberBuilt`/`memberUp`, whose apply environment `E` is existential and
whose parameters carry no mode; both `NewServer.spec` and `NewServer.specCompact` give them. The
mode reaches them through the stand-in `E₀` they already pass: `apply.AEnv` gains a field `cmp`
(drafted as `apply.AEnvD`, a structure extending today's), `envAgree E E₀` (a pure conjunct of
`NewServer.spec`'s post, `memberBuilt`, `memberUp`) agrees on it and ties it to the store's mode
(`envAgreeD`), and `NewServer.spec` takes `E₀.cmp = false` (`specCompact`: `E₀.cmp = true`). An
example then reads `¬ kbCmpM E.γ.kb` off `envAgree` (`envAgreeD_off`), the premise of the watch
server's "no compactor" law (`v3rpc.isWatchServerD_noCompactor_env`). -/

/-- **Draft of `apply.AEnv`** (N1; `apply/Chain.lean`): one more field, after `γbe`,
```
  /-- (M2, the storage side, N1) the server's compaction mode: whether its store compacts (the
  auto-compactor on), which `envAgree` ties to the store's backend (`kbCmpM E.γ.kb`) and the
  stand-in `E₀` carries to the examples; the apply package does not use it (as `γrev`) -/
  cmp : Bool := false
```
(drafted as an extension, so the Draft reads today's predicates at `E.toAEnv`). -/
structure apply.AEnvD (GF : BundledGFunctors) extends apply.AEnv GF where
  cmp : Bool := false

instance apply.AEnvD.coe : CoeOut (apply.AEnvD GF) (apply.AEnv GF) := ⟨apply.AEnvD.toAEnv⟩

/-- **Draft of `envAgree`** (N1; `InvBuild.lean`): two environments agree on the names (today's),
on the compaction mode, and the first one's mode is its store's (S5': one reading of the mode,
`E.cmp` the server's own, not a second copy that could drift; D22's snapshot install, which
replaces `E.γ.kb`, keeps the clause in step 2). -/
def envAgreeD (E E' : apply.AEnvD GF) : Prop :=
  E.γ.idx = E'.γ.idx ∧ E.γ.cok = E'.γ.cok ∧ E.γrev = E'.γrev ∧ E.cmp = E'.cmp ∧
    (mvcc.kbCmpM E.γ.kb ↔ E.cmp = true)

/-- Today's agreement (what `srvC_agree`/`srvCM_agree` read: at the switch their patterns
`⟨hi, hc, hr⟩` become `⟨hi, hc, hr, -, -⟩`). -/
theorem envAgreeD_agree (E E' : apply.AEnvD GF) (h : envAgreeD E E') :
    envAgree (GF := GF) E.toAEnv E'.toAEnv :=
  ⟨h.1, h.2.1, h.2.2.1⟩

/-- **The mode, read at the stand-in** (N1, S5'): the server's store compacts exactly when the
stand-in says so. -/
theorem envAgreeD_mode (E E₀ : apply.AEnvD GF) (h : envAgreeD E E₀) :
    mvcc.kbCmpM E.γ.kb ↔ E₀.cmp = true := by
  rw [h.2.2.2.2, h.2.2.2.1]

/-- **An off stand-in, an off server** (N1: what the watching examples read off `memberUp`'s
`envAgree E E₀`, with `E₀.cmp = false` from the member's boot bundle). -/
theorem envAgreeD_off (E E₀ : apply.AEnvD GF) (h : envAgreeD E E₀) (h0 : E₀.cmp = false) :
    ¬ mvcc.kbCmpM E.γ.kb := by
  rw [envAgreeD_mode E E₀ h, h0]; simp

/-- A compacting stand-in, a compacting server (`specCompact`'s, for the compaction arm). -/
theorem envAgreeD_on (E E₀ : apply.AEnvD GF) (h : envAgreeD E E₀) (h0 : E₀.cmp = true) :
    mvcc.kbCmpM E.γ.kb :=
  (envAgreeD_mode E E₀ h).2 h0

/-- **`NewServer`'s step** (N1; `NewServer.lean:1039`, `hγs`): today's agreement, the store built
over the boot backend `d` at the environment's mode (`{ d with cm := E.cmp }`; today
`{ d with cm := false }`), and the environment built at the stand-in's mode (`cmp := E₀.cmp`, the
anonymous constructor's one more component) give the drafted agreement. -/
theorem envAgreeD_of_new (E E₀ : apply.AEnvD GF) (d : mvcc.KBReal)
    (h : envAgree (GF := GF) E.toAEnv E₀.toAEnv) (hkb : E.γ.kb = some d) (hd : d.cm = E.cmp)
    (hc : E.cmp = E₀.cmp) : envAgreeD E E₀ :=
  ⟨h.1, h.2.1, h.2.2, hc, by rw [hkb, mvcc.kbCmpM_some, hd]⟩

/-- `NewServer.spec`'s instance (`E₀.cmp = false`, the store at `{ d with cm := false }`). -/
theorem envAgreeD_of_new_off (E E₀ : apply.AEnvD GF) (d : mvcc.KBReal)
    (h : envAgree (GF := GF) E.toAEnv E₀.toAEnv)
    (hkb : E.γ.kb = some ({ d with cm := false } : mvcc.KBReal)) (hc : E.cmp = false)
    (h0 : E₀.cmp = false) : envAgreeD E E₀ :=
  envAgreeD_of_new E E₀ _ h hkb (by rw [hc]) (by rw [hc, h0])


end draft

end EtcdGrove
end Perennial

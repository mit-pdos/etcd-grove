/-
Package `proxy`: `NewProxy`'s main-loop state (`proxyOwn`) from the fields of the new proxy:
the log of the genesis slot, nothing executed, nothing proposed (`np_own`).
-/
module

public import Dsverify.Proof.raxos.Proxy.NewHelpers

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.raxos


open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open Perennial.raxos.pure Perennial.raxos.msg
open raxos.replica.src

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [qv : hyp.QpVocab GF]

/-- The genesis slot's log: one slot, decided `["nil"]`. -/
theorem np_logP (γ : QNames) (γs : GName) (c : QConf) (s0 : Slot) (db : GoSlice)
    (h1 : s0.decided' = true) (h2 : s0.decidedBatch' = db) :
    db ↦*□ [go!"nil"] ⊢ logP (GF := GF) γ γs c [s0] [some [go!"nil"]] := by
  iintro #Hdb
  unfold logP
  isplitr
  · ipureintro; rfl
  iapply (BigSepL.bigSepL_cons (Φ := fun i (s : Slot) =>
    iprop(∃ o, ⌜([some [go!"nil"]] : List (Option (List GoString)))[i]? = some o⌝ ∗
      slotP γ γs c i s o))).2
  isplitl
  · iexists (some [go!"nil"])
    isplitr
    · ipureintro; rfl
    unfold slotP
    isplitr
    · ipureintro; rw [h1]; rfl
    rw [h2]
    isplitr
    · iexact Hdb
    isplitr
    · ipureintro; exact ⟨by simp, by intro x hx; simp at hx; subst hx; exact np_strOk_nil⟩
    · rw [if_pos rfl]; ipureintro; rfl
  · iapply BigSepL.bigSepL_nil.2; iempintro

/-- Nothing executed: the executed prefix of the genesis log. -/
theorem np_smrP (γ : QNames) (pr bm ebm kvm : Loc) (t1 : time.Time) :
    ⊢ pr.[Proxy, go!"committedIndex"] ↦ W64 0 -∗ pr.[Proxy, go!"lastTimeCommitted"] ↦ t1 -∗
      bm.[Benchmark, go!"mode"] ↦□ W64 0 -∗ bm.[Benchmark, go!"keyLen"] ↦□ W64 8 -∗
      bm.[Benchmark, go!"KVStore"] ↦□ kvm -∗ kvm ↦$ (∅ : GMap GoString GoString) -∗
      ebm ↦$ (∅ : GMap GoString Bool) -∗ batchReg γ go!"nil" nilBatch -∗
      |==> smrP (GF := GF) γ pr bm ebm [some [go!"nil"]] (W64 0) [] (<[go!"nil" := nilBatch]> ∅) := by
  iintro Hc Ht #Hmode #Hkl #Hkv Hkvm Hebm #Hnil
  imod monoListLbOwn_nil (GF := GF) (A := List GoString) γ.exec with #Hlb
  imodintro
  unfold smrP
  iexists ∅, t1
  iframe Hc Ht Hebm
  isplitr
  · ipureintro; refine ⟨by simp, by simp, by simp, ?_⟩
    intro i h; simp at h
  isplitr
  · unfold execLb; iexact Hlb
  isplitl [Hkvm]
  · unfold kvOwn
    iexists kvm, ∅
    iframe Hkvm
    iframe #
    ipureintro; intro x; rfl
  isplitr
  · ipureintro; intro x; simp [execLog, ExecSt.init]
  isplitr
  · unfold knownP
    iapply (BigSepM.bigSepM_insert (Iris.Std.LawfulPartialMap.get?_empty _)).2
    isplitr
    · iframe #; ipureintro; exact np_nilBatch_ok
    · iapply BigSepM.bigSepM_empty.2; iempintro
  ipureintro
  refine ⟨?_, ?_, ?_⟩
  · intro x b h c hc
    rw [GMap.lookup_insert_eq_iff] at h
    split at h
    · cases h; simp [nilBatch] at hc
    · simp at h
  · intro x b h
    rw [GMap.lookup_insert_eq_iff] at h
    split at h
    · cases h; rename_i hx; rw [← hx]; rfl
    · simp at h
  · intro x hx; simp at hx

/-- No decided slot to piggyback. -/
theorem np_decState (γ : QNames) (pr : Loc) (ls ps ds : GoSlice) :
    ⊢ pr.[Proxy, go!"lastDecidedIndexes"] ↦ ls -∗ pr.[Proxy, go!"lastDecidedProposers"] ↦ ps -∗
      pr.[Proxy, go!"lastDecidedDecisions"] ↦ ds -∗
      ls ↦*□ ([] : List w64) -∗ ps ↦*□ ([] : List w32) -∗ ds ↦*□ ([] : List GoSlice) -∗
      ownSliceCap w64 ls (DFrac.own 1) -∗ ownSliceCap w32 ps (DFrac.own 1) -∗
      ownSliceCap GoSlice ds (DFrac.own 1) -∗ decState (GF := GF) γ pr := by
  iintro Hl Hp Hd #Hls #Hps #Hds Hlc Hpc Hdc
  unfold decState
  iexists ls, ps, ds
  iframe Hl Hp Hd Hlc Hpc Hdc
  unfold decidedSlotsP
  iexists [], [], [], []
  iframe #
  isplitr
  · ipureintro; exact ⟨rfl, rfl, rfl⟩
  iapply BigSepL.bigSepL_nil.2; iempintro

/-- No pending slot; no timer. -/
theorem np_ownProp [hs : raxos.replica.src.Assumptions] (γ : QNames) (k : Nat) (pr : Loc)
    (γq : GName) (pri : Loc) (γpri : ChanNames) (its : GoSlice) (t2 : time.Time) (bt : w64) :
    ⊢ pr.[Proxy, go!"proposeRequestIndex"] ↦□ pri -∗ isChanBag γpri pri (reqIdxP (GF := GF) γq) -∗
      ghostMapAuth γq 1 (∅ : GMap Int Unit) -∗
      pr.[Proxy, go!"instanceTimeouts"] ↦ its -∗ its ↦* List.replicate 1000000 (zero_val Loc) -∗
      pr.[Proxy, go!"lastTimeProposed"] ↦ t2 -∗ pr.[Proxy, go!"batchTime"] ↦□ bt -∗
      ownProp (GF := GF) γ k pr γq 0 1 := by
  iintro #Hpri #Hbag Hauth Hit Hits Htlp #Hbt
  unfold ownProp
  iexists ∅, its, _, t2, bt
  iframe Hauth Hit Hits Htlp
  iframe #
  isplitr
  · iexists hs; unfold chanField; iexists pri, γpri; iframe #
  isplitr
  · iapply BigSepM.bigSepM_empty.2; iempintro
  isplitr
  · ipureintro; constructor
    · intro i h; simp at h
    · intro i h1 h2; omega
  ipureintro; constructor
  · exact List.length_replicate
  · intro i t h hne
    exfalso; apply hne
    rw [List.getElem?_replicate] at h
    split at h
    · cases h; rfl
    · cases h

/-- The new proxy's main-loop state. -/
theorem np_own (γ : QNames) (c : QConf) (k : Nat) (pr : Loc) (γq γs : GName) (cb bm ebm kvm : Loc)
    (rl : GoSlice) (s0 : Slot) (db tb : GoSlice) (t1 : time.Time)
    (h1 : s0.decided' = true) (h2 : s0.decidedBatch' = db) :
    ⊢ isStoreDef (GF := GF) γ γs cb -∗ storeHasDef (GF := GF) γs go!"nil" -∗
      pr.[Proxy, go!"clientBatchStore"] ↦□ cb -∗ pr.[Proxy, go!"benchmark"] ↦□ bm -∗
      pr.[Proxy, go!"executedBatches"] ↦□ ebm -∗
      pr.[Proxy, go!"replicatedLog"] ↦ rl -∗ rl ↦* [s0] -∗ ownSliceCap Slot rl (DFrac.own 1) -∗
      db ↦*□ [go!"nil"] -∗
      pr.[Proxy, go!"committedIndex"] ↦ W64 0 -∗ pr.[Proxy, go!"lastTimeCommitted"] ↦ t1 -∗
      bm.[Benchmark, go!"mode"] ↦□ W64 0 -∗ bm.[Benchmark, go!"keyLen"] ↦□ W64 8 -∗
      bm.[Benchmark, go!"KVStore"] ↦□ kvm -∗ kvm ↦$ (∅ : GMap GoString GoString) -∗
      ebm ↦$ (∅ : GMap GoString Bool) -∗ batchReg γ go!"nil" nilBatch -∗
      pr.[Proxy, go!"lastProposedIndex"] ↦ W64 0 -∗ initFront γ k 1 -∗
      pr.[Proxy, go!"toBeProposed"] ↦ tb -∗ tb ↦* ([] : List GoString) -∗
      ownSliceCap GoString tb (DFrac.own 1) -∗
      decState γ pr -∗ epochOwn pr -∗ ownProp γ k pr γq 0 1 -∗ |==> proxyOwn γ c k pr := by
  iintro #Hst #Hhas #Hcb #Hbm #Hebm Hrl Hsl Hrlc #Hdb Hc Ht #Hmode #Hkl #Hkv Hkvm HE #Hnil
    Hlp Hfront Htb Htbs Htbc Hdec Hep Hprop
  imod np_smrP γ pr bm ebm kvm t1 $$ Hc Ht Hmode Hkl Hkv Hkvm HE Hnil with Hsmr
  ihave #Hlog := np_logP (GF := GF) γ γs c s0 db h1 h2 $$ Hdb
  imodintro
  unfold proxyOwn proxyOwnDef
  iexists γq
  unfold ownQ
  iexists γs, cb, bm, ebm, rl, [s0], [some [go!"nil"]], W64 0, W64 0, [], _, tb, []
  iframe Hrl Hsl Hrlc Hsmr Hlp Htb Htbs Htbc Hdec Hep
  iframe #
  rw [show sint.Z (W64 0) = 0 from rfl]
  rw [show (0 : Int) + 1 = 1 from rfl, show [s0].length = 1 from rfl]
  iframe Hfront Hprop
  isplitr
  · ipureintro; constructor <;> decide
  iapply BigSepL.bigSepL_nil.2; iempintro

end proofs

end Perennial.raxos

/-
**The server's store invariant, generic in its witness and permit, with its builders proved**
(strict M1, 2026-11-05). `KVStoreApi.lean`'s `kvStoreInv` (the frozen draft's, holding the client's
`mvccState γ σ`) is `kvStoreInvG` at the raft witness `kvNx γr on` and the compaction permit
`crevOk γr` (`kvStoreInv_eq`, by `rfl`); every builder and law of the draft over the invariant is
proved here for any persistent, timeless `Nx` and `Cp` (no server module needed: the server's
foundations are red under strict M1 until the apply chain moves onto the API), over mvcc's API laws
as hypotheses (`persistent.law`: `mvccState`'s timelessness, `isMvcc`'s persistence;
`mvccState_reachable.law`): the begin, the writer's read, the snapshot's update, the end (two nested
updates), a compaction, a restore, anyone's read, the writer's facts (`kvAus.law`'s conjuncts), the
peek (`kvPeek.law`), the boot's notified-log bound (`histLb_boot.law`) and the boot's invariant
(`bootStore.law`). Also the server's ghost names of the store's state (`KVSNames`), the floors
(`kvLogLb`), the apply thread's halves (`wSt`, `crOwn`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.lease.MvccShapes
public import Perennial.Ghost.MonoList
public import Perennial.Ghost.GhostVar

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section
namespace Perennial
namespace EtcdGrove
namespace srvApi
open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc mvcc.api

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **The server's ghost names of the store's state** (allocated by `NewServer`'s caller, with
the read names: the floors are indexed by `slog`): `st` the `(log, pending)` part (½ the
invariant, ½ the apply thread's `kvOwn`), `cr` the compaction revision (½ the invariant, ¼
`kvOwn`, ¼ `cmpOwn`), `slog` the monotone list of the committed log (authority the invariant's,
fragments the floors), `nlog` the monotone list of the notified log (the pending revision
included: the watch path's `histLb`). -/
structure KVSNames where
  st : GName
  cr : GName
  slog : GName
  nlog : GName

/-- The store invariant's namespace (outside `mvccN`, as every `server_*` one). -/
def kvsN : Namespace := nroot .@ "server_kv_store"

/-- A floor: the committed log extends `L` (today's `idxCert γ.idx L`; persistent). -/
def kvLogLb (γs : KVSNames) (L : mvcc.Log) : IProp GF := monoListLbOwn γs.slog L

instance kvLogLb_persistent (γs : KVSNames) (L : mvcc.Log) :
    Persistent (kvLogLb (GF := GF) γs L) := by
  unfold kvLogLb; infer_instance

instance kvLogLb_timeless (γs : KVSNames) (L : mvcc.Log) :
    Timeless (kvLogLb (GF := GF) γs L) := by
  unfold kvLogLb; infer_instance

/-- The apply thread's half of the state (`kvOwn`'s): the log `log`, nothing pending, and a
quarter of the compaction revision `c`. -/
def wSt (γs : KVSNames) (log : mvcc.Log) (c : Int) : IProp GF :=
  iprop(ghostVar γs.st (1 : Qp).half (log, (none : Option (List mvcc.Change))) ∗
    ghostVar γs.cr (1 : Qp).half.half c)

/-- The compaction right's quarter of the compaction revision (`cmpOwn`'s). -/
def crOwn (γs : KVSNames) (c : Int) : IProp GF := ghostVar γs.cr (1 : Qp).half.half c


/-- **The store invariant, generic**: `KVStoreApi.lean`'s `kvStoreInv` at a witness `Nx` of the
logs and a permit `Cp` of the compaction revision. -/
def kvStoreInvG (kv : GoInterface) (γ : MvccName) (Nx : mvcc.Log → IProp GF) (Cp : Int → IProp GF)
    (γs : KVSNames) : IProp GF :=
  iprop(isMvcc kv γ ∗ inv kvsN iprop(∃ σ : MvccState, mvccState γ σ ∗
    ghostVar γs.st (1 : Qp).half (σ.log, σ.pending) ∗ ghostVar γs.cr (1 : Qp).half σ.crev ∗
    monoListAuthOwn γs.slog 1 σ.log ∗ monoListAuthOwn γs.nlog 1 σ.notifiedLog ∗
    Nx σ.log ∗ Nx σ.notifiedLog ∗ ⧖ (mvcc.logCh σ.notifiedLog) ∗ Cp σ.crev))

/-- The store invariant is persistent (`isMvcc`'s persistence is the API's `persistent.law`). -/
theorem kvStoreInvG_persistent (Hp : persistent.law (GF := GF)) (kv : GoInterface) (γ : MvccName)
    (Nx : mvcc.Log → IProp GF) (Cp : Int → IProp GF) (γs : KVSNames) :
    Persistent (kvStoreInvG (GF := GF) kv γ Nx Cp γs) := by
  haveI := Hp.1 kv γ
  unfold kvStoreInvG; infer_instance

/-- `kvReadAt`, generic. -/
def kvReadAtG (Nx : mvcc.Log → IProp GF) (γs : KVSNames) (L₀ : mvcc.Log) (σ : MvccState) :
    IProp GF :=
  iprop(⌜L₀ <+: σ.log⌝ ∗ kvLogLb γs σ.log ∗ Nx σ.log ∗ ⧖ (mvcc.logCh σ.log) ∗
    ⌜MvccReachable σ ∧ σ.log.length + 3 ≤ 2 ^ 63⌝)

/-- `histLb`, generic. -/
def histLbG (Nx : mvcc.Log → IProp GF) (γs : KVSNames) (L : mvcc.Log) : IProp GF :=
  iprop(monoListLbOwn γs.nlog L ∗ ∃ L' : mvcc.Log, ⌜L <+: L' ∧ mvcc.LogWf' L'⌝ ∗ Nx L' ∗
    ⧖ (mvcc.logCh L'))

end defs

/-! ## The pure part -/

/-- A state to strip the invariant's later from its existential. -/
instance : Inhabited MvccState := ⟨mvccStart⟩


/-- The store invariant's namespace is outside mvcc's. -/
theorem kvsN_mvccN : (↑kvsN : CoPset) ⊆ ⊤ \ ↑mvccN :=
  mask_ndot_ne' nroot "server_kv_store" "mvcc" (by decide)

/-- A reachable state's log begins with a new store's, and its notified log extends it. -/
theorem reach_prefix (σ : MvccState) (h : MvccReachable σ) :
    mvccStart.log <+: σ.log ∧ σ.log <+: σ.notifiedLog := by
  induction h with
  | start => exact ⟨List.prefix_refl _, by simp [MvccState.notifiedLog, mvccStart]⟩
  | notify σ pend _ _ _ ih =>
    refine ⟨by simpa [MvccState.notify] using ih.1, ?_⟩
    rw [MvccState.notify_notifiedLog]
    simp only [MvccState.notify]
    unfold mvcc.commitLog
    split
    · exact List.prefix_refl _
    · exact List.prefix_append _ _
  | commit σ _ ih =>
    refine ⟨?_, by simp [MvccState.commitPending, MvccState.notifiedLog]⟩
    simp only [MvccState.commitPending]
    unfold mvcc.commitLog
    split
    · exact ih.1
    · exact ih.1.trans (List.prefix_append _ _)
  | compact σ r _ _ _ _ _ ih =>
    simpa [MvccState.compactTo, MvccState.notifiedLog] using ih

/-- **A reachable state's log has a revision per change past its first two**, and its pending
revision (if any) changes something (strict M1, 2026-11-05: the apply thread's small log,
`srvApplyKV_small`, until then the sole writer's `txn.soleWriter_small'`). -/
theorem reach_len_logCh (σ : MvccState) (h : MvccReachable σ) :
    σ.log.length ≤ mvcc.logCh σ.log + 2 ∧ ∀ p, σ.pending = some p → p ≠ [] := by
  induction h with
  | start => exact ⟨by simp [mvccStart], fun p hp => by simp [mvccStart] at hp⟩
  | notify σ pend _ _ _ ih =>
    refine ⟨by simpa [MvccState.notify] using ih.1, fun p hp => ?_⟩
    simp only [MvccState.notify] at hp
    split at hp
    · cases hp
    · cases hp; assumption
  | commit σ _ ih =>
    refine ⟨?_, fun p hp => by simp [MvccState.commitPending] at hp⟩
    simp only [MvccState.commitPending]
    unfold mvcc.commitLog
    split
    · exact ih.1
    · rename_i hne
      have : 0 < (σ.pending.getD []).length := List.length_pos_iff.mpr hne
      have := ih.1
      simp only [List.length_append, List.length_singleton, mvcc.logCh, List.map_append,
        List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil] at this ⊢
      omega
  | compact σ r _ _ _ _ _ ih =>
    exact ⟨by simpa [MvccState.compactTo] using ih.1, by simpa [MvccState.compactTo] using ih.2⟩

/-- The writer's view's notified log is its log. -/
@[simp] theorem stAt_log (log : mvcc.Log) (c : Int) : (stAt log c).log = log := rfl
@[simp] theorem stAt_crev (log : mvcc.Log) (c : Int) : (stAt log c).crev = c := rfl
@[simp] theorem stAt_pending (log : mvcc.Log) (c : Int) :
    (stAt log c).pending = (none : Option (List mvcc.Change)) := rfl

/-- The writer's view after a commit's first step: its notified log the commit's history. -/
theorem stAt_notify_notifiedLog (log : mvcc.Log) (c : Int) (pend : List mvcc.Change) :
    ((stAt log c).notify pend).notifiedLog = mvcc.commitLog log pend :=
  MvccState.notify_notifiedLog _ _

@[simp] theorem stAt_notifiedLog (log : mvcc.Log) (c : Int) : (stAt log c).notifiedLog = log := rfl

/-- The states the halves agree on are the writer's view. -/
theorem stAt_of (σ : MvccState) (log : mvcc.Log) (c : Int)
    (h1 : (σ.log, σ.pending) = (log, (none : Option (List mvcc.Change)))) (h2 : σ.crev = c) :
    σ = stAt log c := by
  obtain ⟨l, cr, p⟩ := σ
  simp only [Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl⟩ := h1
  subst h2
  rfl

/-- A prefix's changes are at most the log's. -/
theorem logCh_prefix {l l' : mvcc.Log} (h : l <+: l') : mvcc.logCh l ≤ mvcc.logCh l' := by
  obtain ⟨t, rfl⟩ := h
  simp [mvcc.logCh]

/-- The writer's view after a commit's two steps. -/
theorem stAt_notify_commit (log : mvcc.Log) (c : Int) (pend : List mvcc.Change) :
    ((stAt log c).notify pend).commitPending = stAt (mvcc.commitLog log pend) c := by
  unfold MvccState.commitPending MvccState.notify stAt mvcc.commitLog
  by_cases h : pend = [] <;> simp [h]

/-- The writer's view after a commit's first step: the log unchanged. -/
@[simp] theorem stAt_notify_log (log : mvcc.Log) (c : Int) (pend : List mvcc.Change) :
    ((stAt log c).notify pend).log = log := rfl

@[simp] theorem stAt_notify_crev (log : mvcc.Log) (c : Int) (pend : List mvcc.Change) :
    ((stAt log c).notify pend).crev = c := rfl

/-- A commit's first step's history extends the log. -/
theorem commitLog_prefix (log : mvcc.Log) (pend : List mvcc.Change) : log <+: mvcc.commitLog log pend := by
  unfold mvcc.commitLog; split
  · exact List.prefix_refl _
  · exact List.prefix_append _ _

/-- **The compaction revision after `Compact(rev)`** at `c` (`apply.cmpRevAfter`, by `rfl`). -/
def crevAfter (c : Int) (rev : w64) : Int := if c < sint.Z rev then sint.Z rev else c

/-- A compaction at a revision of the log, on the writer's view: the compaction revision
`crevAfter`. -/
theorem stAt_compact (log : mvcc.Log) (c : Int) (rev : w64) (h : sint.Z rev < log.length) :
    (if (stAt log c).crev < sint.Z rev ∧ sint.Z rev ≤ ((stAt log c).rev : Int)
      then (stAt log c).compactTo (sint.Z rev) else stAt log c) =
      stAt log (crevAfter c rev) := by
  unfold crevAfter
  simp only [stAt, MvccState.rev, MvccState.compactTo]
  by_cases hc : c < sint.Z rev
  · have : sint.Z rev ≤ ((log.length - 1 : Nat) : Int) := by omega
    simp [hc, this]
  · simp [hc]

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable (Nx : mvcc.Log → IProp GF) (Cp : Int → IProp GF)
variable [hNxP : ∀ l, Persistent (Nx l)] [hNxT : ∀ l, Timeless (Nx l)]
variable [hCpP : ∀ c, Persistent (Cp c)] [hCpT : ∀ c, Timeless (Cp c)]

/-- Keep a resource while learning a pure fact from it. -/
private theorem keep_pure {P : IProp GF} {φ : Prop} (h : P ⊢ ⌜φ⌝) : P ⊢ P ∗ ⌜φ⌝ :=
  (BI.and_intro .rfl h).trans BI.persistent_and_sep_mp

/-- The state's facts, keeping it: reachable (`mvccState_reachable.law`), well formed
(`reach_logWf`). -/
theorem mvccState_facts (Hr : mvccState_reachable.law (GF := GF))
    (kv : GoInterface) (γ : MvccName) (σ : MvccState) :
    isMvcc (GF := GF) kv γ ∗ mvccState γ σ ⊢ mvccState γ σ ∗
      ⌜MvccReachable σ ∧ σ.log.length + 3 ≤ 2 ^ 63 ∧ mvcc.LogWf' σ.log ∧ mvcc.LogWf' σ.notifiedLog ∧
        mvccStart.log <+: σ.log ∧ σ.log <+: σ.notifiedLog⌝ := by
  refine (keep_pure (Hr kv γ σ)).trans ?_
  iintro ⟨⟨-, Hs⟩, %H⟩
  iframe Hs
  ipureintro
  exact ⟨H.1, H.2, (reach_logWf σ H.1).1, (reach_logWf σ H.1).2, (reach_prefix σ H.1).1,
    (reach_prefix σ H.1).2⟩

/-- **The watch path's peek** (`kvPeek.law`, generic). -/
theorem kvPeekG (Hp : persistent.law (GF := GF)) (Hr : mvccState_reachable.law (GF := GF))
    (kv : GoInterface) (γ : MvccName) (γs : KVSNames) (E : CoPset) (hE : ↑kvsN ⊆ E) :
    kvStoreInvG (GF := GF) kv γ Nx Cp γs ⊢ |={E, E \ ↑kvsN}=> ∃ σ : MvccState, mvccState γ σ ∗
      histLbG Nx γs σ.notifiedLog ∗ Cp σ.crev ∗ kvLogLb γs σ.log ∗
      (mvccState γ σ ={E \ ↑kvsN, E}=∗ True) := by
  haveI := Hp.1 kv γ
  haveI := fun σ => Hp.2.2.2.2.2.1 γ σ
  haveI := kvStoreInvG_persistent Hp kv γ Nx Cp γs
  iintro #Hk
  iunfold kvStoreInvG at Hk
  icases Hk with ⟨#Hm, #Hinv⟩
  iinv Hinv with ⟨%σ, >Hs, >Hst, >Hcr, >Hsl, >Hnl, >#Hnx1, >#Hnx2, >#Hrc, >#Hco⟩ Hclose
  ihave ⟨Hs, %Hf⟩ := mvccState_facts Hr kv γ σ $$ [Hm Hs]
  · isplitl []
    · iexact Hm
    iexact Hs
  ihave #Hnlb := monoListLbOwn_get γs.nlog 1 σ.notifiedLog $$ Hnl
  ihave #Hslb := monoListLbOwn_get γs.slog 1 σ.log $$ Hsl
  imodintro
  iexists σ
  iframe Hs Hco
  isplitr [Hclose Hst Hcr Hsl Hnl]
  · iunfold histLbG
    iframe Hnlb
    iexists σ.notifiedLog
    iframe Hnx2 Hrc
    ipureintro; exact ⟨List.prefix_refl _, Hf.2.2.2.1⟩
  isplitr [Hclose Hst Hcr Hsl Hnl]
  · iunfold kvLogLb; iexact Hslb
  iintro Hs
  imod Hclose $$ [Hs Hst Hcr Hsl Hnl] with -
  · inext
    iexists σ
    iframe Hs Hst Hcr Hsl Hnl Hnx1 Hnx2 Hrc Hco
  imodintro
  itrivial

/-- **The boot's bound** (`histLb_boot.law`, generic). -/
theorem histLb_bootG (Hp : persistent.law (GF := GF)) (Hr : mvccState_reachable.law (GF := GF))
    (kv : GoInterface) (γ : MvccName) (γs : KVSNames) :
    kvStoreInvG (GF := GF) kv γ Nx Cp γs ={⊤}=∗ histLbG Nx γs [[], []] := by
  haveI := Hp.1 kv γ
  haveI := fun σ => Hp.2.2.2.2.2.1 γ σ
  haveI := kvStoreInvG_persistent Hp kv γ Nx Cp γs
  iintro #Hk
  iunfold kvStoreInvG at Hk
  icases Hk with ⟨#Hm, #Hinv⟩
  iinv Hinv with ⟨%σ, >Hs, >Hst, >Hcr, >Hsl, >Hnl, >#Hnx1, >#Hnx2, >#Hrc, >#Hco⟩ Hclose
  ihave ⟨Hs, %Hf⟩ := mvccState_facts Hr kv γ σ $$ [Hm Hs]
  · isplitl []
    · iexact Hm
    iexact Hs
  ihave #Hnlb := monoListLbOwn_get γs.nlog 1 σ.notifiedLog $$ Hnl
  imod Hclose $$ [Hs Hst Hcr Hsl Hnl] with -
  · inext
    iexists σ
    iframe Hs Hst Hcr Hsl Hnl Hnx1 Hnx2 Hrc Hco
  imodintro
  iunfold histLbG
  isplitl
  · iapply monoListLbOwn_le [[], []] (Hf.2.2.2.2.1.trans Hf.2.2.2.2.2) $$ Hnlb
  iexists σ.notifiedLog
  iframe Hnx2 Hrc
  ipureintro; exact ⟨Hf.2.2.2.2.1.trans Hf.2.2.2.2.2, Hf.2.2.2.1⟩

/-! ## The builders (`kvAus.law`), one per update shape -/

/-- **A write's begin** (`auBegin`, continuation form), from the writer's half. -/
theorem au_begin (Hp : persistent.law (GF := GF)) (kv : GoInterface) (γ : MvccName)
    (γs : KVSNames) (log : mvcc.Log) (c : Int) (X : IProp GF) :
    kvStoreInvG (GF := GF) kv γ Nx Cp γs ⊢
      wSt γs log c -∗ (wSt γs log c -∗ X) -∗ auBegin γ (stAt log c) X := by
  haveI := fun σ => Hp.2.2.2.2.2.1 γ σ
  haveI := kvStoreInvG_persistent Hp kv γ Nx Cp γs
  iintro #Hk Hw HX
  iunfold kvStoreInvG at Hk
  icases Hk with ⟨#Hm, #Hinv⟩
  iunfold auBegin
  iauintro
  unfold atomic_acc
  have Hdisj := kvsN_mvccN
  iinv Hinv with ⟨%σ, >Hs, >Hst, >Hcr, >Hsl, >Hnl, >#Hnx1, >#Hnx2, >#Hrc, >#Hco⟩ Hclose
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ (⊤ \ ↑mvccN) \ ↑kvsN from
    Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists σ
  iframe Hs
  isplit
  · iintro Hs
    imod Hclose2 with -
    imod Hclose $$ [Hs Hst Hcr Hsl Hnl] with -
    · inext
      iexists σ
      iframe Hs Hst Hcr Hsl Hnl Hnx1 Hnx2 Hrc Hco
    imodintro
    iframe Hw HX
  · iintro ⟨%Hpn, Hs⟩
    imod Hclose2 with -
    iunfold wSt at Hw
    icases Hw with ⟨Hw1, Hw2⟩
    icombine Hst Hw1 gives %H1
    icombine Hcr Hw2 gives %H2
    imod Hclose $$ [Hs Hst Hcr Hsl Hnl] with -
    · inext
      iexists σ
      iframe Hs Hst Hcr Hsl Hnl Hnx1 Hnx2 Hrc Hco
    imodintro
    isplitr
    · ipureintro; exact stAt_of σ log c H1.2 H2.2
    iapply HX
    iunfold wSt
    iframe Hw1 Hw2

/-- **The writer's own read** (`auRead` at the writer's view, continuation form). -/
theorem au_wread (Hp : persistent.law (GF := GF)) (kv : GoInterface) (γ : MvccName)
    (γs : KVSNames) (log : mvcc.Log) (c : Int) (X : IProp GF) :
    kvStoreInvG (GF := GF) kv γ Nx Cp γs ⊢
      wSt γs log c -∗ (wSt γs log c -∗ X) -∗
        auRead γ (fun σ => iprop(⌜σ = stAt log c⌝ ∗ X)) := by
  haveI := fun σ => Hp.2.2.2.2.2.1 γ σ
  haveI := kvStoreInvG_persistent Hp kv γ Nx Cp γs
  iintro #Hk Hw HX
  iunfold kvStoreInvG at Hk
  icases Hk with ⟨#Hm, #Hinv⟩
  iunfold auRead
  iauintro
  unfold atomic_acc
  have Hdisj := kvsN_mvccN
  iinv Hinv with ⟨%σ, >Hs, >Hst, >Hcr, >Hsl, >Hnl, >#Hnx1, >#Hnx2, >#Hrc, >#Hco⟩ Hclose
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ (⊤ \ ↑mvccN) \ ↑kvsN from
    Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists σ
  iframe Hs
  isplit
  · iintro Hs
    imod Hclose2 with -
    imod Hclose $$ [Hs Hst Hcr Hsl Hnl] with -
    · inext
      iexists σ
      iframe Hs Hst Hcr Hsl Hnl Hnx1 Hnx2 Hrc Hco
    imodintro
    iframe Hw HX
  · iintro Hs
    imod Hclose2 with -
    iunfold wSt at Hw
    icases Hw with ⟨Hw1, Hw2⟩
    icombine Hst Hw1 gives %H1
    icombine Hcr Hw2 gives %H2
    imod Hclose $$ [Hs Hst Hcr Hsl Hnl] with -
    · inext
      iexists σ
      iframe Hs Hst Hcr Hsl Hnl Hnx1 Hnx2 Hrc Hco
    imodintro
    isplitr
    · ipureintro; exact stAt_of σ log c H1.2 H2.2
    iapply HX
    iunfold wSt
    iframe Hw1 Hw2

/-- **The snapshot's update** (`auSnap` at the writer's view): `pending = none` from the halves at
every access. -/
theorem au_snap (Hp : persistent.law (GF := GF)) (kv : GoInterface) (γ : MvccName)
    (γs : KVSNames) (log : mvcc.Log) (c : Int) (X : IProp GF) :
    kvStoreInvG (GF := GF) kv γ Nx Cp γs ⊢
      wSt γs log c -∗ (wSt γs log c -∗ X) -∗
        auSnap γ (fun σ => iprop(⌜σ = stAt log c⌝ ∗ X)) := by
  haveI := fun σ => Hp.2.2.2.2.2.1 γ σ
  haveI := kvStoreInvG_persistent Hp kv γ Nx Cp γs
  iintro #Hk Hw HX
  iunfold kvStoreInvG at Hk
  icases Hk with ⟨#Hm, #Hinv⟩
  iunfold wSt at Hw
  icases Hw with ⟨Hw1, Hw2⟩
  iunfold auSnap
  iauintro
  unfold atomic_acc
  have Hdisj := kvsN_mvccN
  iinv Hinv with ⟨%σ, >Hs, >Hst, >Hcr, >Hsl, >Hnl, >#Hnx1, >#Hnx2, >#Hrc, >#Hco⟩ Hclose
  icombine Hst Hw1 gives %H1
  icombine Hcr Hw2 gives %H2
  have Hσ := stAt_of σ log c H1.2 H2.2
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ (⊤ \ ↑mvccN) \ ↑kvsN from
    Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists σ
  isplitl [Hs]
  · iframe Hs; ipureintro; rw [Hσ]; rfl
  isplit
  · iintro ⟨Hs, -⟩
    imod Hclose2 with -
    imod Hclose $$ [Hs Hst Hcr Hsl Hnl] with -
    · inext
      iexists σ
      iframe Hs Hst Hcr Hsl Hnl Hnx1 Hnx2 Hrc Hco
    imodintro
    iframe Hw1 Hw2 HX
  · iintro Hs
    imod Hclose2 with -
    imod Hclose $$ [Hs Hst Hcr Hsl Hnl] with -
    · inext
      iexists σ
      iframe Hs Hst Hcr Hsl Hnl Hnx1 Hnx2 Hrc Hco
    imodintro
    isplitr
    · ipureintro; exact Hσ
    iapply HX
    iunfold wSt
    iframe Hw1 Hw2

/-- **Anyone's read** (`auRead` at `kvReadAt`, from a floor). -/
theorem au_read (Hp : persistent.law (GF := GF)) (Hr : mvccState_reachable.law (GF := GF))
    (kv : GoInterface) (γ : MvccName) (γs : KVSNames)
    (L₀ : mvcc.Log) :
    kvStoreInvG (GF := GF) kv γ Nx Cp γs ⊢ kvLogLb γs L₀ -∗ auRead γ (kvReadAtG Nx γs L₀) := by
  haveI := fun σ => Hp.2.2.2.2.2.1 γ σ
  haveI := kvStoreInvG_persistent Hp kv γ Nx Cp γs
  haveI := Hp.1 kv γ
  iintro #Hk #HL
  iunfold kvStoreInvG at Hk
  icases Hk with ⟨#Hm, #Hinv⟩
  iunfold auRead
  iauintro
  unfold atomic_acc
  have Hdisj := kvsN_mvccN
  iinv Hinv with ⟨%σ, >Hs, >Hst, >Hcr, >Hsl, >Hnl, >#Hnx1, >#Hnx2, >#Hrc, >#Hco⟩ Hclose
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ (⊤ \ ↑mvccN) \ ↑kvsN from
    Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists σ
  iframe Hs
  isplit
  · iintro Hs
    imod Hclose2 with -
    imod Hclose $$ [Hs Hst Hcr Hsl Hnl] with -
    · inext
      iexists σ
      iframe Hs Hst Hcr Hsl Hnl Hnx1 Hnx2 Hrc Hco
    imodintro
    iempintro
  · iintro Hs
    imod Hclose2 with -
    ihave ⟨Hs, %Hf⟩ := mvccState_facts Hr kv γ σ $$ [Hm Hs]
    · isplitl []
      · iexact Hm
      iexact Hs
    iunfold kvLogLb at HL
    ihave %HL0 := mono_list_auth_lb_valid γs.slog 1 σ.log L₀ $$ Hsl HL
    ihave #Hslb := monoListLbOwn_get γs.slog 1 σ.log $$ Hsl
    ihave #Hrc' := preceipt_mono (logCh_prefix Hf.2.2.2.2.2) $$ Hrc
    imod Hclose $$ [Hs Hst Hcr Hsl Hnl] with -
    · inext
      iexists σ
      iframe Hs Hst Hcr Hsl Hnl Hnx1 Hnx2 Hrc Hco
    imodintro
    iunfold kvReadAtG
    iunfold kvLogLb
    iframe Hslb Hnx1 Hrc'
    ipureintro; exact ⟨HL0.2, Hf.1, Hf.2.1⟩

/-- **The writer's facts** at its state, outside any update. -/
theorem writer_facts (Hp : persistent.law (GF := GF)) (Hr : mvccState_reachable.law (GF := GF))
    (kv : GoInterface) (γ : MvccName) (γs : KVSNames)
    (log : mvcc.Log) (c : Int) :
    kvStoreInvG (GF := GF) kv γ Nx Cp γs ⊢
      wSt γs log c ={⊤}=∗ wSt γs log c ∗ kvLogLb γs log ∗ Nx log ∗
        ⧖ (mvcc.logCh log) ∗ ⌜MvccReachable (stAt log c) ∧ log.length + 3 ≤ 2 ^ 63⌝ := by
  haveI := fun σ => Hp.2.2.2.2.2.1 γ σ
  haveI := kvStoreInvG_persistent Hp kv γ Nx Cp γs
  haveI := Hp.1 kv γ
  iintro #Hk Hw
  iunfold kvStoreInvG at Hk
  icases Hk with ⟨#Hm, #Hinv⟩
  iunfold wSt at Hw
  icases Hw with ⟨Hw1, Hw2⟩
  iinv Hinv with ⟨%σ, >Hs, >Hst, >Hcr, >Hsl, >Hnl, >#Hnx1, >#Hnx2, >#Hrc, >#Hco⟩ Hclose
  icombine Hst Hw1 gives %H1
  icombine Hcr Hw2 gives %H2
  have Hσ : σ = ⟨log, c, none⟩ := stAt_of σ log c H1.2 H2.2
  subst Hσ
  ihave ⟨Hs, %Hf⟩ := mvccState_facts Hr kv γ ⟨log, c, none⟩ $$ [Hm Hs]
  · isplitl []
    · iexact Hm
    iexact Hs
  ihave #Hslb := monoListLbOwn_get γs.slog 1 log $$ Hsl
  imod Hclose $$ [Hs Hst Hcr Hsl Hnl] with -
  · inext
    iexists ⟨log, c, none⟩
    iframe Hs Hst Hcr Hsl Hnl Hnx1 Hnx2 Hrc Hco
  imodintro
  iunfold wSt
  iunfold kvLogLb
  iframe Hw1 Hw2 Hslb Hnx1
  rw [show ({ log := log, crev := c, pending := none } : MvccState).notifiedLog = log from rfl]
  iframe Hrc
  ipureintro; exact ⟨Hf.1, Hf.2.1⟩

/-- **The writer's log extends every floor** (strict M1, 2026-11-05: the chain's KV methods' floor
`floorOkO`, `envAus`'s last conjunct): the writer's half is the invariant's state, whose committed
log is the authority of every floor `kvLogLb γs F`. -/
theorem writer_floor (Hp : persistent.law (GF := GF)) (kv : GoInterface) (γ : MvccName)
    (γs : KVSNames) (log : mvcc.Log) (c : Int) (F : mvcc.Log) :
    kvStoreInvG (GF := GF) kv γ Nx Cp γs ⊢
      wSt γs log c -∗ kvLogLb γs F ={⊤}=∗ wSt γs log c ∗ ⌜F <+: log⌝ := by
  haveI := fun σ => Hp.2.2.2.2.2.1 γ σ
  haveI := kvStoreInvG_persistent Hp kv γ Nx Cp γs
  iintro #Hk Hw #HF
  iunfold kvStoreInvG at Hk
  icases Hk with ⟨#Hm, #Hinv⟩
  iunfold wSt at Hw
  icases Hw with ⟨Hw1, Hw2⟩
  iinv Hinv with ⟨%σ, >Hs, >Hst, >Hcr, >Hsl, >Hnl, >#Hnx1, >#Hnx2, >#Hrc, >#Hco⟩ Hclose
  icombine Hst Hw1 gives %H1
  iunfold kvLogLb at HF
  ihave %HL0 := mono_list_auth_lb_valid γs.slog 1 σ.log F $$ Hsl HF
  imod Hclose $$ [Hs Hst Hcr Hsl Hnl] with -
  · inext
    iexists σ
    iframe Hs Hst Hcr Hsl Hnl Hnx1 Hnx2 Hrc Hco
  imodintro
  iunfold wSt
  iframe Hw1 Hw2
  ipureintro
  have hl : σ.log = log := (Prod.mk.inj H1.2).1
  rw [← hl]; exact HL0.2

/-- **A write's end** (`auEnd`'s two nested updates), from the writer's half and the committed
log's witness: the notify step moves the pending revision's halves and the notified log (its
receipt mvcc's), the commit step the committed log's. -/
theorem au_end (Hp : persistent.law (GF := GF)) (kv : GoInterface) (γ : MvccName)
    (γs : KVSNames) (log : mvcc.Log) (c : Int) (pend : List mvcc.Change) :
    kvStoreInvG (GF := GF) kv γ Nx Cp γs ⊢
      wSt γs log c -∗ Nx (mvcc.commitLog log pend) -∗
        auEnd γ (stAt log c) pend (wSt γs (mvcc.commitLog log pend) c) := by
  haveI := fun σ => Hp.2.2.2.2.2.1 γ σ
  haveI := kvStoreInvG_persistent Hp kv γ Nx Cp γs
  iintro #Hk Hw #Hnx
  iunfold kvStoreInvG at Hk
  icases Hk with ⟨#Hm, #Hinv⟩
  iunfold wSt at Hw
  icases Hw with ⟨Hw1, Hw2⟩
  iunfold auEnd
  iauintro
  unfold atomic_acc
  have Hdisj := kvsN_mvccN
  iinv Hinv with ⟨%σ, >Hs, >Hst, >Hcr, >Hsl, >Hnl, >#Hnx1, >#Hnx2, >#Hrc, >#Hco⟩ Hclose
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ (⊤ \ ↑mvccN) \ ↑kvsN from
    Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists σ
  iframe Hs
  isplit
  · iintro Hs
    imod Hclose2 with -
    imod Hclose $$ [Hs Hst Hcr Hsl Hnl] with -
    · inext
      iexists σ
      iframe Hs Hst Hcr Hsl Hnl Hnx1 Hnx2 Hrc Hco
    imodintro
    iframe Hw1 Hw2
  · iintro ⟨%Hσ, Hs, #Hrc'⟩
    imod Hclose2 with -
    subst Hσ
    simp only [stAt_log, stAt_crev, stAt_pending, stAt_notifiedLog]
    imod ghostVar_update_halves (log, ((stAt log c).notify pend).pending) γs.st _ _ $$ Hst Hw1
      with ⟨Hst, Hw1⟩
    imod monoListAuthOwn_update (mvcc.commitLog log pend) (commitLog_prefix log pend) $$ Hnl
      with ⟨Hnl, -⟩
    imod Hclose $$ [Hs Hst Hcr Hsl Hnl] with -
    · inext
      iexists (stAt log c).notify pend
      simp only [stAt_notify_log, stAt_notify_crev, stAt_notify_notifiedLog]
      iframe Hs Hst Hcr Hsl Hnl Hnx1 Hnx Hco
      rw [logCh_commitLog]
      iexact Hrc'
    imodintro
    -- the commit step
    iauintro
    unfold atomic_acc
    iinv Hinv with ⟨%σ2, >Hs, >Hst, >Hcr, >Hsl, >Hnl, >#Hnx1', >#Hnx2', >#Hrc2, >#Hco'⟩ Hclose
    iapply fupd_mask_intro (show (∅ : CoPset) ⊆ (⊤ \ ↑mvccN) \ ↑kvsN from
      Std.LawfulSet.empty_subset)
    iintro Hclose2
    isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
    iexists σ2
    iframe Hs
    isplit
    · iintro Hs
      imod Hclose2 with -
      imod Hclose $$ [Hs Hst Hcr Hsl Hnl] with -
      · inext
        iexists σ2
        iframe Hs Hst Hcr Hsl Hnl Hnx1' Hnx2' Hrc2 Hco'
      imodintro
      iframe Hw1 Hw2
    · iintro ⟨%Hσ2, Hs⟩
      imod Hclose2 with -
      subst Hσ2
      simp only [stAt_notify_log, stAt_notify_crev, stAt_notify_notifiedLog, stAt_notify_commit]
      imod ghostVar_update_halves (mvcc.commitLog log pend, (none : Option (List mvcc.Change)))
        γs.st _ _ $$ Hst Hw1 with ⟨Hst, Hw1⟩
      imod monoListAuthOwn_update (mvcc.commitLog log pend) (commitLog_prefix log pend) $$ Hsl
        with ⟨Hsl, -⟩
      imod Hclose $$ [Hs Hst Hcr Hsl Hnl] with -
      · inext
        iexists stAt (mvcc.commitLog log pend) c
        simp only [stAt_log, stAt_crev, stAt_pending, stAt_notifiedLog]
        iframe Hs Hst Hcr Hsl Hnl Hnx Hrc2 Hco'
      imodintro
      iunfold wSt
      iframe Hw1 Hw2

/-- **A compaction at `rev`**, one of the log's, permitted: the compaction revision's three parts
move to `crevAfter c rev`. -/
theorem au_compact (Hp : persistent.law (GF := GF)) (kv : GoInterface) (γ : MvccName)
    (γs : KVSNames) (log : mvcc.Log) (c : Int) (rev : w64) (hrev : sint.Z rev < log.length) :
    kvStoreInvG (GF := GF) kv γ Nx Cp γs ⊢
      wSt γs log c -∗ crOwn γs c -∗ Cp (sint.Z rev) -∗
        auCompact γ rev (fun σ => iprop(⌜σ = stAt log c⌝ ∗
          wSt γs log (crevAfter c rev) ∗ crOwn γs (crevAfter c rev))) := by
  haveI := fun σ => Hp.2.2.2.2.2.1 γ σ
  haveI := kvStoreInvG_persistent Hp kv γ Nx Cp γs
  iintro #Hk Hw Hc #Hcp
  iunfold kvStoreInvG at Hk
  icases Hk with ⟨#Hm, #Hinv⟩
  iunfold wSt at Hw
  icases Hw with ⟨Hw1, Hw2⟩
  iunfold crOwn at Hc
  iunfold auCompact
  iauintro
  unfold atomic_acc
  have Hdisj := kvsN_mvccN
  iinv Hinv with ⟨%σ, >Hs, >Hst, >Hcr, >Hsl, >Hnl, >#Hnx1, >#Hnx2, >#Hrc, >#Hco⟩ Hclose
  icombine Hst Hw1 gives %H1
  icombine Hcr Hw2 gives %H2
  have Hσ := stAt_of σ log c H1.2 H2.2
  subst Hσ
  simp only [stAt_log, stAt_crev, stAt_pending, stAt_notifiedLog]
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ (⊤ \ ↑mvccN) \ ↑kvsN from
    Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists stAt log c
  iframe Hs
  isplit
  · iintro Hs
    imod Hclose2 with -
    imod Hclose $$ [Hs Hst Hcr Hsl Hnl] with -
    · inext
      iexists stAt log c
      simp only [stAt_log, stAt_crev, stAt_pending, stAt_notifiedLog]
      iframe Hs Hst Hcr Hsl Hnl Hnx1 Hrc Hco
    imodintro
    iframe Hw1 Hw2 Hc
  · iintro Hs
    imod Hclose2 with -
    rw [stAt_compact log c rev hrev]
    icombine Hw2 Hc as Hq

    imod ghostVar_update_halves (crevAfter c rev) γs.cr _ _ $$ Hcr Hq with ⟨Hcr, Hq⟩
    ihave ⟨Hw2, Hc⟩ := (ghostVar_split_half γs.cr (1 : Qp).half (crevAfter c rev)).1 $$ Hq
    imod Hclose $$ [Hs Hst Hcr Hsl Hnl] with -
    · inext
      iexists stAt log (crevAfter c rev)
      simp only [stAt_log, stAt_crev, stAt_pending, stAt_notifiedLog]
      iframe Hs Hst Hcr Hsl Hnl Hnx1 Hrc
      unfold crevAfter
      split
      · iexact Hcp
      · iexact Hco
    imodintro
    isplitr
    · ipureintro; rfl
    iunfold wSt
    iunfold crOwn
    iframe Hw1 Hw2 Hc

/-- **A restore to an extension**: every part moves to the restored state, its receipt
`Restore`'s. -/
theorem au_restore (Hp : persistent.law (GF := GF)) (kv : GoInterface) (γ : MvccName)
    (γs : KVSNames) (log log' : mvcc.Log) (c c' : Int) (hl : log <+: log') (hc : c ≤ c') :
    kvStoreInvG (GF := GF) kv γ Nx Cp γs ⊢
      wSt γs log c -∗ crOwn γs c -∗ Nx log' -∗ Cp c' -∗
        auRestore γ (stAt log' c') (fun σ => iprop(⌜σ = stAt log c⌝ ∗ wSt γs log' c' ∗
          crOwn γs c')) := by
  haveI := fun σ => Hp.2.2.2.2.2.1 γ σ
  haveI := kvStoreInvG_persistent Hp kv γ Nx Cp γs
  iintro #Hk Hw Hc #Hnx #Hcp
  iunfold kvStoreInvG at Hk
  icases Hk with ⟨#Hm, #Hinv⟩
  iunfold wSt at Hw
  icases Hw with ⟨Hw1, Hw2⟩
  iunfold crOwn at Hc
  iunfold auRestore
  iauintro
  unfold atomic_acc
  have Hdisj := kvsN_mvccN
  iinv Hinv with ⟨%σ, >Hs, >Hst, >Hcr, >Hsl, >Hnl, >#Hnx1, >#Hnx2, >#Hrc, >#Hco⟩ Hclose
  icombine Hst Hw1 gives %H1
  icombine Hcr Hw2 gives %H2
  have Hσ := stAt_of σ log c H1.2 H2.2
  subst Hσ
  simp only [stAt_log, stAt_crev, stAt_pending, stAt_notifiedLog]
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ (⊤ \ ↑mvccN) \ ↑kvsN from
    Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists stAt log c
  isplitl [Hs]
  · iframe Hs; ipureintro; exact ⟨hl, hc⟩
  isplit
  · iintro ⟨Hs, -⟩
    imod Hclose2 with -
    imod Hclose $$ [Hs Hst Hcr Hsl Hnl] with -
    · inext
      iexists stAt log c
      simp only [stAt_log, stAt_crev, stAt_pending, stAt_notifiedLog]
      iframe Hs Hst Hcr Hsl Hnl Hnx1 Hrc Hco
    imodintro
    iframe Hw1 Hw2 Hc
  · iintro ⟨Hs, #Hrc'⟩
    imod Hclose2 with -
    imod ghostVar_update_halves (log', (none : Option (List mvcc.Change))) γs.st _ _ $$ Hst Hw1
      with ⟨Hst, Hw1⟩
    icombine Hw2 Hc as Hq

    imod ghostVar_update_halves c' γs.cr _ _ $$ Hcr Hq with ⟨Hcr, Hq⟩
    ihave ⟨Hw2, Hc⟩ := (ghostVar_split_half γs.cr (1 : Qp).half c').1 $$ Hq
    imod monoListAuthOwn_update log' hl $$ Hsl with ⟨Hsl, -⟩
    imod monoListAuthOwn_update log' hl $$ Hnl with ⟨Hnl, -⟩
    imod Hclose $$ [Hs Hst Hcr Hsl Hnl] with -
    · inext
      iexists stAt log' c'
      simp only [stAt_log, stAt_crev, stAt_pending, stAt_notifiedLog]
      iframe Hs Hst Hcr Hsl Hnl Hnx Hrc' Hcp
    imodintro
    isplitr
    · ipureintro; rfl
    iunfold wSt
    iunfold crOwn
    iframe Hw1 Hw2 Hc

/-- **The boot's invariant** (`bootStore.law`, generic): from the new store's state, the fresh
names and the witness of the empty history, the invariant and the apply thread's halves; the
receipt `⧖ 0` (`preceipt_zero`). -/
theorem bootStoreG (Hp : persistent.law (GF := GF)) (kv : GoInterface) (γ : MvccName)
    (γs : KVSNames) :
    isMvcc (GF := GF) kv γ ∗ mvccState γ mvccStart ∗
      ghostVar γs.st 1 (([[], []] : mvcc.Log), (none : Option (List mvcc.Change))) ∗
      ghostVar γs.cr 1 (-1 : Int) ∗ monoListAuthOwn γs.slog 1 ([[], []] : mvcc.Log) ∗
      monoListAuthOwn γs.nlog 1 ([[], []] : mvcc.Log) ∗ Nx [[], []] ∗ Cp (-1) ={⊤}=∗
    kvStoreInvG kv γ Nx Cp γs ∗ wSt γs [[], []] (-1) ∗ crOwn γs (-1) := by
  haveI := Hp.1 kv γ
  iintro ⟨#Hm, Hs, Hst, Hcr, Hsl, Hnl, #Hnx, #Hcp⟩
  imod (preceipt_zero (GF := GF)) with #Hr0
  ihave ⟨Hst, Hw1⟩ := (ghostVar_split_half γs.st 1 _).1 $$ Hst
  ihave ⟨Hcr, Hq⟩ := (ghostVar_split_half γs.cr 1 _).1 $$ Hcr
  ihave ⟨Hw2, Hc⟩ := (ghostVar_split_half γs.cr (1 : Qp).half _).1 $$ Hq
  imod inv_alloc kvsN ⊤ iprop(∃ σ : MvccState, mvccState γ σ ∗
    ghostVar γs.st (1 : Qp).half (σ.log, σ.pending) ∗ ghostVar γs.cr (1 : Qp).half σ.crev ∗
    monoListAuthOwn γs.slog 1 σ.log ∗ monoListAuthOwn γs.nlog 1 σ.notifiedLog ∗
    Nx σ.log ∗ Nx σ.notifiedLog ∗ ⧖ (mvcc.logCh σ.notifiedLog) ∗ Cp σ.crev)
    $$ [Hs Hst Hcr Hsl Hnl] with #Hinv
  · inext
    iexists mvccStart
    simp only [show mvccStart.log = [[], []] from rfl, show mvccStart.crev = -1 from rfl,
      show mvccStart.pending = none from rfl, show mvccStart.notifiedLog = [[], []] from rfl]
    iframe Hs Hst Hcr Hsl Hnl Hnx Hcp
    rw [show mvcc.logCh [[], []] = 0 from rfl]
    iexact Hr0
  imodintro
  iunfold kvStoreInvG
  iunfold wSt
  iunfold crOwn
  iframe Hm Hinv Hw1 Hw2 Hc

/-- **The builders, together** (`kvAus.law`'s shape, generic): the begin, the writer's read, the
snapshot's update, the end, a compaction, a restore, anyone's read, the writer's facts. -/
theorem kvAusG (Hp : persistent.law (GF := GF)) (Hr : mvccState_reachable.law (GF := GF))
    (kv : GoInterface) (γ : MvccName) (γs : KVSNames) :
    kvStoreInvG (GF := GF) kv γ Nx Cp γs ⊢
    □ (∀ log c (X : IProp GF), wSt γs log c -∗ (wSt γs log c -∗ X) -∗
        auBegin γ (stAt log c) X) ∗
    □ (∀ log c (X : IProp GF), wSt γs log c -∗ (wSt γs log c -∗ X) -∗
        auRead γ (fun σ => iprop(⌜σ = stAt log c⌝ ∗ X))) ∗
    □ (∀ log c (X : IProp GF), wSt γs log c -∗ (wSt γs log c -∗ X) -∗
        auSnap γ (fun σ => iprop(⌜σ = stAt log c⌝ ∗ X))) ∗
    □ (∀ log c pend, wSt γs log c -∗ Nx (mvcc.commitLog log pend) -∗
        auEnd γ (stAt log c) pend (wSt γs (mvcc.commitLog log pend) c)) ∗
    □ (∀ log c (rev : w64), ⌜sint.Z rev < log.length⌝ → wSt γs log c -∗ crOwn γs c -∗
        Cp (sint.Z rev) -∗
        auCompact γ rev (fun σ => iprop(⌜σ = stAt log c⌝ ∗
          wSt γs log (crevAfter c rev) ∗ crOwn γs (crevAfter c rev)))) ∗
    □ (∀ log c log' c', ⌜log <+: log' ∧ c ≤ c'⌝ → wSt γs log c -∗ crOwn γs c -∗
        Nx log' -∗ Cp c' -∗
        auRestore γ (stAt log' c') (fun σ => iprop(⌜σ = stAt log c⌝ ∗ wSt γs log' c' ∗
          crOwn γs c'))) ∗
    □ (∀ L₀, kvLogLb γs L₀ -∗ auRead γ (kvReadAtG Nx γs L₀)) ∗
    □ (∀ log c, wSt γs log c ={⊤}=∗ wSt γs log c ∗ kvLogLb γs log ∗ Nx log ∗
        ⧖ (mvcc.logCh log) ∗ ⌜MvccReachable (stAt log c) ∧ log.length + 3 ≤ 2 ^ 63⌝) := by
  haveI := kvStoreInvG_persistent Hp kv γ Nx Cp γs
  iintro #Hk
  isplitr
  · iintro !> %log %c %X Hw HX
    iapply au_begin Nx Cp Hp kv γ γs log c X $$ Hk Hw HX
  isplitr
  · iintro !> %log %c %X Hw HX
    iapply au_wread Nx Cp Hp kv γ γs log c X $$ Hk Hw HX
  isplitr
  · iintro !> %log %c %X Hw HX
    iapply au_snap Nx Cp Hp kv γ γs log c X $$ Hk Hw HX
  isplitr
  · iintro !> %log %c %pend Hw #Hnx
    iapply au_end Nx Cp Hp kv γ γs log c pend $$ Hk Hw Hnx
  isplitr
  · iintro !> %log %c %rev %hrev Hw Hc #Hcp
    iapply au_compact Nx Cp Hp kv γ γs log c rev hrev $$ Hk Hw Hc Hcp
  isplitr
  · iintro !> %log %c %log' %c' %h Hw Hc #Hnx #Hcp
    iapply au_restore Nx Cp Hp kv γ γs log log' c c' h.1 h.2 $$ Hk Hw Hc Hnx Hcp
  isplitr
  · iintro !> %L₀ #HL
    iapply au_read Nx Cp Hp Hr kv γ γs L₀ $$ Hk HL
  iintro !> %log %c Hw
  iapply writer_facts Nx Cp Hp Hr kv γ γs log c $$ Hk Hw

end laws

end srvApi
end EtcdGrove
end Perennial

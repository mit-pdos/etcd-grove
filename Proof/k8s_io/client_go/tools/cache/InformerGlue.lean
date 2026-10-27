/-
**The informer invariant's accessors** (phase 4 of `notes/k8s-daemonset-plan.md`, fourth round): the
linearization points the informer's components and its clients take through `infInv`. Lean-first.

* `infInv_readAU`: a reader of the store (the listers' `List`, `GetByKey`, `ByIndex`, `Index`, the
  consistency store's `LastStoreSyncResourceVersion`): at its linearization point it learns
  `readFacts` (the store is the server's table at its version, a lower bound of that version).
-/
module

public import Proof.k8s_io.client_go.tools.cache.InformerInv
public import Spec.k8s_io.client_go.tools.cache.RealFIFO__PopBatch
public import Proof.k8s_io.client_go.tools.cache.InformerDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace informer

open Iris Iris.BI Iris.ProofMode apimodel cache

section glue
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **A store reader's linearization point**, through the invariant: the store's state `σs`, its
facts `readFacts`. -/
theorem infInv_readAU (γa : ApiNames) (r : Res) (γf : FifoNames) (γt : TsNames) (γi : InfNames)
    (K : cache.St → IProp GF) :
    ⊢ infInv γa r γf γt γi -∗ (∀ σs, readFacts γa r γi σs -∗ K σs) -∗
      |={⊤ \ ∅, ∅}=> ∃ σs, storeSt γt σs ∗ (storeSt γt σs ={∅, ⊤ \ ∅}=∗ K σs) := by
  iintro #Hinv HK
  rw [Iris.Std.LawfulSet.diff_empty]
  iunfold infInv at Hinv
  iinv Hinv with >Hi Hclose
  iunfold infRes at Hi
  icases Hi with ⟨%σp, %s, %q, %σs, %R, %pd, %ap, #Hp, Hreg, #Hsnap, #Hobjs, Hq, Hst, Hsw, Hlast, Hpop, Hlb,
    %Hok⟩
  ihave #Hlb' := monoNatLbOwn_get γi.rvlb 1 (rvNat s.store.rv) $$ Hlb
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ \ ↑infN from Std.LawfulSet.empty_subset)
  iintro Hclose2
  iexists σs
  iframe Hst
  iintro Hst
  imod Hclose2 with -
  imod Hclose $$ [Hreg Hq Hst Hsw Hlast Hpop Hlb] with -
  · inext
    unfold infRes
    iexists σp, s, q, σs, R, pd, ap
    iframe
    iframe #
    ipureintro; exact Hok
  imodintro
  iapply HK
  unfold readFacts
  iexists σp, s.store, R
  iframe #
  ipureintro
  exact ⟨Hok.2.2.2.2.1, Hok.1.1⟩

/-- **The processing goroutine, idle**: nothing popped. -/
def procIdle (γi : InfNames) : IProp GF := ghostVar γi.pop (1 : Qp).half (([] : List cache.FD), false)

/-- **The processing goroutine with a popped batch** `ds`, not yet applied (the batch processing's
precondition). -/
def procPopped (γi : InfNames) (ds : List cache.FD) (_b : Bool) : IProp GF :=
  ghostVar γi.pop (1 : Qp).half (ds, false)

/-- **A batch's removal from the FIFO**, through the invariant: the popped deltas move from the
queue to the popped ones (`InfP.ok_pop`). -/
theorem infInv_popBatchAU (γa : ApiNames) (r : Res) (γf : FifoNames) (γt : TsNames) (γi : InfNames)
    (Ω : val → IProp GF) (hΩ : ∀ e : GoInterface, procIdle γi ⊢ Ω #e) :
    ⊢ infInv γa r γf γt γi -∗ procIdle γi -∗ popBatchAU γf (procPopped γi) Ω := by
  iintro #Hinv Hidle
  unfold popBatchAU
  inext
  iunfold infInv at Hinv
  iinv Hinv with >Hi Hclose
  iunfold infRes at Hi
  icases Hi with ⟨%σp, %s, %q, %σs, %R, %pd, %ap, #Hp, Hreg, #Hsnap, #Hobjs, Hq, Hst, Hsw, Hlast, Hpop, Hlb,
    %Hok⟩
  iunfold procIdle at Hidle
  icombine Hpop Hidle gives % ⟨_, hpd⟩
  simp only [Prod.mk.injEq] at hpd
  obtain ⟨rfl, rfl⟩ := hpd
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ \ ↑infN from Std.LawfulSet.empty_subset)
  iintro Hclose2
  iexists q
  iframe Hq
  isplit
  · iintro %hcl Hq
    imod Hclose2 with -
    imod Hclose $$ [Hreg Hq Hst Hsw Hlast Hpop Hlb] with -
    · inext
      unfold infRes
      iexists σp, s, q, σs, R, [], false
      iframe
      iframe #
      ipureintro; exact Hok
    imodintro
    iintro %e
    iapply (hΩ e)
    iunfold procIdle
    iexact Hidle
  · iintro %hne Hq
    obtain ⟨hok, hlast, hfifo, hpop, hst, hres, hgood, hfq, hpr⟩ := Hok
    have hpop0 : s.popped = [] := by
      unfold poppedRel at hpop; simp only [Bool.false_eq_true, ↓reduceIte] at hpop
      exact forall₂_nil_left hpop
    obtain ⟨rest, hrest⟩ := FQ.batch_prefix q
    rw [← hrest] at hfifo
    obtain ⟨m1, m2, hm, h1, h2⟩ := forall₂_append_split _ _ _ hfifo
    imod ghostVar_update_halves (q.batch, false) $$ Hpop Hidle with ⟨Hpop, Hidle⟩
    imod Hclose2 with -
    imod Hclose $$ [Hreg Hq Hst Hsw Hlast Hpop Hlb] with -
    · inext
      unfold infRes
      iexists σp, ⟨s.store, m1, m2, s.last⟩, { q with items := q.items.drop q.batch.length }, σs, R,
        q.batch, false
      iframe
      iframe #
      ipureintro
      refine ⟨?_, hlast, ?_, ?_, hst, hres, hgood, fqOk_pop q hfq hne, ?_⟩
      · have := InfP.ok_pop _ s m1 m2 hm hok
        rw [hpop0, List.nil_append] at this
        exact this
      · show List.Forall₂ (fdRel R) (q.items.drop q.batch.length) m2
        rw [← hrest, List.drop_left]; exact h2
      · unfold poppedRel; simp only [Bool.false_eq_true, ↓reduceIte]; exact h1
      · exact pdReg_batch R q m1 h1
    imodintro
    iunfold procPopped
    iexact Hidle

/-- **The processing goroutine's store writer** for a popped batch `ds`: the store's state as the
writer knows it (the `blockDeltas` lock's), and the popped batch, applied or not. -/
def procWriter (γi : InfNames) (ds : List cache.FD) (σ : cache.St) : IProp GF :=
  iprop(ghostVar γi.sw (1 : Qp).half σ ∗ ∃ ap : Bool, ghostVar γi.pop (1 : Qp).half (ds, ap))

/-- **The batch writer's allowed steps**: a read, or the batch's store step. -/
def batchRw (R0 : Reg) (ds : List cache.FD) (σ σ' : cache.St) : Prop :=
  σ' = σ ∨ σ' = cache.batchStore (regKF R0) (regRv R0) σ ds

/-- The registry snapshot `R0` is part of the registry `R`. -/
theorem reg_sub (γ : GName) (R R0 : Reg) :
    ghostMapAuth (GF := GF) γ 1 R ∗ ([∗map] x ↦ o ∈ R0, x ↪[γ]□ o) ⊢
      ⌜∀ x o, R0 !! x = some o → R !! x = some o⌝ ∗
        (ghostMapAuth γ 1 R ∗ ([∗map] x ↦ o ∈ R0, x ↪[γ]□ o)) := by
  apply persistent_entails_right
  iintro ⟨Ha, Hs⟩
  ihave %h := (ghost_map_lookup_big (γ := γ) (q := 1) (m := R) (dq := DFrac.discard) R0) $$ Ha Hs
  ipureintro
  exact (GMap.map_subseteq_spec R0 R).1 h

/-- **The store writer of a popped batch**, through the invariant: a read changes nothing, the
batch's store step applies the popped deltas (`InfP.ok_apply`), once (`batchStore_idem`). -/
theorem infInv_batchWriter (γa : ApiNames) (r : Res) (γf : FifoNames) (γt : TsNames)
    (γi : InfNames) (R0 : Reg) (ds : List cache.FD) (hlen : 2 ≤ ds.length)
    (hobj : ∀ d ∈ ds, ∃ t x, d = .obj t x) (hreg : ∀ x ∈ fdObjs ds, ∃ o, R0 !! x = some o) :
    ⊢ infInv γa r γf γt γi -∗ ([∗map] x ↦ o ∈ R0, x ↪[γi.reg]□ o) -∗
      storeWriter γt (procWriter γi ds) (batchRw R0 ds) := by
  iintro #Hinv #Hsnap
  iunfold storeWriter
  imodintro
  iintro %σ Hw
  iunfold procWriter at Hw
  icases Hw with ⟨Hsw', %ap', Hpop'⟩
  iunfold infInv at Hinv
  iinv Hinv with >Hi Hclose
  iunfold infRes at Hi
  icases Hi with ⟨%σp, %s, %q, %σs, %R, %pd, %ap, #Hp, Hreg, #Hsnap', #Hobjs, Hq, Hst, Hsw, Hlast, Hpop,
    Hlb, %Hok⟩
  icombine Hsw Hsw' gives % ⟨_, hσ⟩
  subst hσ
  icombine Hpop Hpop' gives % ⟨_, hpd⟩
  simp only [Prod.mk.injEq] at hpd
  obtain ⟨rfl, rfl⟩ := hpd
  ihave ⟨%hsub, Hreg, -⟩ := reg_sub γi.reg R R0 $$ [$Hreg $Hsnap]
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ \ ↑infN from Std.LawfulSet.empty_subset)
  iintro Hclose2
  iframe Hst
  iintro %σ' %hRw Hst
  obtain ⟨hok, hlast, hfifo, hpop, hst, hres, hgood, hfq, hpr⟩ := Hok
  have hkf : ∀ x ∈ fdObjs pd, regKF R0 x = regKF R x := by
    intro x hx; obtain ⟨o, ho⟩ := hreg x hx; simp [regKF, ho, hsub x o ho]
  have hrvf : ∀ x ∈ fdObjs pd, regRv R0 x = regRv R x := by
    intro x hx; obtain ⟨o, ho⟩ := hreg x hx; simp [regRv, ho, hsub x o ho]
  rcases hRw with h | h
  · -- a read
    rw [h]
    imod Hclose2 with -
    imod Hclose $$ [Hreg Hq Hst Hsw Hlast Hpop Hlb] with -
    · inext
      unfold infRes
      iexists σp, s, q, σs, R, pd, ap
      iframe
      iframe #
      ipureintro; exact ⟨hok, hlast, hfifo, hpop, hst, hres, hgood, hfq, hpr⟩
    imodintro
    unfold procWriter
    iframe
  · rw [h]
    cases ap with
    | true =>
      -- already applied: the step changes nothing
      unfold poppedRel at hpop
      simp only [↓reduceIte] at hpop
      obtain ⟨hpz, σ0, hσ0⟩ := hpop
      have hfix : cache.batchStore (regKF R0) (regRv R0) σs pd = σs := by
        rw [batchStore_congr _ (regKF R) _ (regRv R) σs pd hkf hrvf, hσ0,
          popStep_batch _ _ _ _ hlen, cache.batchStore_idem]
      rw [hfix]
      imod Hclose2 with -
      imod Hclose $$ [Hreg Hq Hst Hsw Hlast Hpop Hlb] with -
      · inext
        unfold infRes
        iexists σp, s, q, σs, R, pd, true
        iframe
        iframe #
        ipureintro
        refine ⟨hok, hlast, hfifo, ?_, hst, hres, hgood, hfq, hpr⟩
        unfold poppedRel; simp only [↓reduceIte]; exact ⟨hpz, σ0, hσ0⟩
      imodintro
      unfold procWriter
      iframe
    | false =>
      unfold poppedRel at hpop
      simp only [Bool.false_eq_true, ↓reduceIte] at hpop
      ihave #Hp2 := Hp
      iunfold pastSt at Hp2
      icases Hp2 with ⟨%Hh, -, %hH⟩
      have hwf := hH.2.1
      have hchg : ∀ a ∈ s.popped, ∃ c, a = .change c ∧ keyGood c.obj.key ∧
          c.obj.meta.ResourceVersion' = rvStr c.rv := by
        intro a ha
        obtain ⟨c, rfl⟩ := fdRel_obj_changes R pd s.popped hpop hobj a ha
        have hc := InfP.popped_mem _ s hok c ha
        exact ⟨c, rfl, hgood c hc, (hwf.log_obj r c hc).2⟩
      have hobjok := objOk_of_fdRel R R0 hsub pd s.popped hpop hreg hchg
      have hst' := storeRel_batch R (regKF R0) (regRv R0) σs s.store pd s.popped hst hobjok
      have hsorted := hwf.log_sorted r
      have hok' := InfP.ok_apply _ hsorted s hok
      have hrvle := rvNat_mono (InfP.apply_rv_le _ hsorted s hok)
      imod ghostVar_update_halves (cache.batchStore (regKF R0) (regRv R0) σs pd) $$ Hsw Hsw'
        with ⟨Hsw, Hsw'⟩
      imod ghostVar_update_halves (pd, true) $$ Hpop Hpop' with ⟨Hpop, Hpop'⟩
      imod mono_nat_own_update _ hrvle $$ Hlb with ⟨Hlb, -⟩
      imod Hclose2 with -
      imod Hclose $$ [Hreg Hq Hst Hsw Hlast Hpop Hlb] with -
      · inext
        unfold infRes
        iexists σp, ⟨s.store.applyAll s.popped, [], s.fifo, s.last⟩, q,
          cache.batchStore (regKF R0) (regRv R0) σs pd, R, pd, true
        iframe
        iframe #
        ipureintro
        refine ⟨hok', hlast, hfifo, ?_, hst', hres, hgood, hfq, hpr⟩
        unfold poppedRel
        simp only [↓reduceIte]
        refine ⟨trivial, σs, ?_⟩
        rw [popStep_batch _ _ _ _ hlen, batchStore_congr _ (regKF R) _ (regRv R) σs pd hkf hrvf]
      imodintro
      unfold procWriter
      iframe

/-- **The processing goroutine after processing a popped batch `ds`** (applied). -/
def procDone (γi : InfNames) (ds : List cache.FD) : IProp GF :=
  ghostVar γi.pop (1 : Qp).half (ds, true)

/-- **A batch's processing finished** (the handler's view shift `Hstep`, with the writer's state
`σ'` the batch's store step of the state `σ` it locked): the popped deltas are applied, if the
writer's write left the store as it was (then it is the step's fixed point). -/
theorem infInv_batchFinish (γa : ApiNames) (r : Res) (γf : FifoNames) (γt : TsNames)
    (γi : InfNames) (R0 : Reg) (ds : List cache.FD) (hlen : 2 ≤ ds.length)
    (hobj : ∀ d ∈ ds, ∃ t x, d = .obj t x) (hreg : ∀ x ∈ fdObjs ds, ∃ o, R0 !! x = some o)
    (σ σ' : cache.St) (hstep : σ' = cache.batchStore (regKF R0) (regRv R0) σ ds) :
    ⊢ infInv γa r γf γt γi -∗ ([∗map] x ↦ o ∈ R0, x ↪[γi.reg]□ o) -∗
      ghostVar γi.sw (1 : Qp).half σ' -∗ (∃ ap : Bool, ghostVar γi.pop (1 : Qp).half (ds, ap)) ={⊤}=∗
      ghostVar γi.sw (1 : Qp).half σ' ∗ procDone γi ds := by
  iintro #Hinv #Hsnap Hsw' ⟨%ap', Hpop'⟩
  iunfold infInv at Hinv
  iinv Hinv with >Hi Hclose
  iunfold infRes at Hi
  icases Hi with ⟨%σp, %s, %q, %σs, %R, %pd, %ap, #Hp, Hreg, #Hsnap', #Hobjs, Hq, Hst, Hsw, Hlast, Hpop,
    Hlb, %Hok⟩
  icombine Hsw Hsw' gives % ⟨_, hσ⟩
  subst hσ
  icombine Hpop Hpop' gives % ⟨_, hpd⟩
  simp only [Prod.mk.injEq] at hpd
  obtain ⟨rfl, rfl⟩ := hpd
  ihave ⟨%hsub, Hreg, -⟩ := reg_sub γi.reg R R0 $$ [$Hreg $Hsnap]
  obtain ⟨hok, hlast, hfifo, hpop, hst, hres, hgood, hfq, hpr⟩ := Hok
  have hkf : ∀ x ∈ fdObjs pd, regKF R0 x = regKF R x := by
    intro x hx; obtain ⟨o, ho⟩ := hreg x hx; simp [regKF, ho, hsub x o ho]
  have hrvf : ∀ x ∈ fdObjs pd, regRv R0 x = regRv R x := by
    intro x hx; obtain ⟨o, ho⟩ := hreg x hx; simp [regRv, ho, hsub x o ho]
  cases ap with
  | true =>
    imod Hclose $$ [Hreg Hq Hst Hsw Hlast Hpop Hlb] with -
    · inext
      unfold infRes
      iexists σp, s, q, σs, R, pd, true
      iframe
      iframe #
      ipureintro; exact ⟨hok, hlast, hfifo, hpop, hst, hres, hgood, hfq, hpr⟩
    imodintro
    unfold procDone
    iframe
  | false =>
    unfold poppedRel at hpop
    simp only [Bool.false_eq_true, ↓reduceIte] at hpop
    ihave #Hp2 := Hp
    iunfold pastSt at Hp2
    icases Hp2 with ⟨%Hh, -, %hH⟩
    have hwf := hH.2.1
    have hchg : ∀ a ∈ s.popped, ∃ c, a = .change c ∧ keyGood c.obj.key ∧
        c.obj.meta.ResourceVersion' = rvStr c.rv := by
      intro a ha
      obtain ⟨c, rfl⟩ := fdRel_obj_changes R pd s.popped hpop hobj a ha
      have hc := InfP.popped_mem _ s hok c ha
      exact ⟨c, rfl, hgood c hc, (hwf.log_obj r c hc).2⟩
    have hobjok := objOk_of_fdRel R R0 hsub pd s.popped hpop hreg hchg
    have hfix : cache.batchStore (regKF R0) (regRv R0) σs pd = σs := by
      rw [hstep, cache.batchStore_idem]
    have hst' := storeRel_batch R (regKF R0) (regRv R0) σs s.store pd s.popped hst hobjok
    rw [hfix] at hst'
    have hsorted := hwf.log_sorted r
    have hok' := InfP.ok_apply _ hsorted s hok
    have hrvle := rvNat_mono (InfP.apply_rv_le _ hsorted s hok)
    imod ghostVar_update_halves (pd, true) $$ Hpop Hpop' with ⟨Hpop, Hpop'⟩
    imod mono_nat_own_update _ hrvle $$ Hlb with ⟨Hlb, -⟩
    imod Hclose $$ [Hreg Hq Hst Hsw Hlast Hpop Hlb] with -
    · inext
      unfold infRes
      iexists σp, ⟨s.store.applyAll s.popped, [], s.fifo, s.last⟩, q, σs, R, pd, true
      iframe
      iframe #
      ipureintro
      refine ⟨hok', hlast, hfifo, ?_, hst', hres, hgood, hfq, hpr⟩
      unfold poppedRel
      simp only [↓reduceIte]
      refine ⟨trivial, σ, ?_⟩
      rw [popStep_batch _ _ _ _ hlen, ← batchStore_congr _ (regKF R) _ (regRv R) σ pd hkf hrvf,
        hstep]
    imodintro
    unfold procDone
    iframe

/-- **`PopBatch`'s deferred step**, through the invariant: the applied batch is done (nothing popped
any more), and the initial items' count goes down by its length, which it does not exceed
(`fqOk`). -/
theorem infInv_doneBatchAU (γa : ApiNames) (r : Res) (γf : FifoNames) (γt : TsNames)
    (γi : InfNames) (Ω : val → IProp GF) (hΩ : ∀ e : GoInterface, procIdle γi ⊢ Ω #e) :
    ⊢ infInv γa r γf γt γi -∗ doneBatchAU γf (fun ds _ => procDone γi ds) Ω := by
  iintro #Hinv
  unfold doneBatchAU
  iintro %ds %err Hdone
  inext
  iunfold infInv at Hinv
  iinv Hinv with >Hi Hclose
  iunfold infRes at Hi
  icases Hi with ⟨%σp, %s, %q, %σs, %R, %pd, %ap, #Hp, Hreg, #Hsnap', #Hobjs, Hq, Hst, Hsw, Hlast, Hpop,
    Hlb, %Hok⟩
  iunfold procDone at Hdone
  icombine Hpop Hdone gives % ⟨_, hpd⟩
  simp only [Prod.mk.injEq] at hpd
  obtain ⟨rfl, rfl⟩ := hpd
  obtain ⟨hok, hlast, hfifo, hpop, hst, hres, hgood, hfq, hpr⟩ := Hok
  unfold poppedRel at hpop
  simp only [↓reduceIte] at hpop
  obtain ⟨hpz, -⟩ := hpop
  have hcond : pd.length = 1 ∨ q.initCount = 0 ∨ pd.length ≤ q.initCount := by
    by_cases h2 : 2 ≤ pd.length
    · exact Or.inr (hfq.2 h2).2
    · rcases Nat.lt_or_ge pd.length 1 with h | h
      · right; right; omega
      · left; omega
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ \ ↑infN from Std.LawfulSet.empty_subset)
  iintro Hclose2
  iexists q
  iframe Hq
  isplitr
  · ipureintro; exact hcond
  iintro Hq
  imod ghostVar_update_halves (([] : List cache.FD), false) $$ Hpop Hdone with ⟨Hpop, Hdone⟩
  imod Hclose2 with -
  imod Hclose $$ [Hreg Hq Hst Hsw Hlast Hpop Hlb] with -
  · inext
    unfold infRes
    iexists σp, s, q.popDoneN pd.length, σs, R, [], false
    iframe
    iframe #
    ipureintro
    refine ⟨hok, hlast, ?_, ?_, hst, hres, hgood, ?_⟩
    · unfold cache.FQ.popDoneN; split <;> exact hfifo
    · unfold poppedRel; simp only [Bool.false_eq_true, ↓reduceIte, hpz]; exact .nil
    · refine ⟨⟨?_, fun h => absurd h (by simp)⟩, by simp [pdReg]⟩
      unfold cache.FQ.popDoneN; split <;> exact hfq.1
  imodintro
  iapply (hΩ err)
  iunfold procIdle
  iexact Hdone

/-- **The single writer's allowed steps**: a read, or the lone delta's store step. -/
def singleRw (R0 : Reg) (d : cache.FD) (σ σ' : cache.St) : Prop :=
  σ' = σ ∨ σ' = cache.storeStepFD (regKF R0) (regRv R0) σ d

/-- The facts of a lone popped delta `a` the store step needs: a change's key good and its object's
version its own; a relist's table well keyed. -/
theorem single_facts (l : List Change) (s : InfP) (hok : s.ok l) (hwf : ∀ c ∈ l,
    keyGood c.obj.key ∧ c.obj.meta.ResourceVersion' = rvStr c.rv) (a : Delta)
    (ha : a ∈ s.popped) :
    (∀ c, a = .change c → keyGood c.obj.key ∧ c.obj.meta.ResourceVersion' = rvStr c.rv) ∧
    (∀ M n, a = .replaced M n →
      (∀ key, key ∈ M → keyGood key) ∧ (∀ key o, M !! key = some o → o.key = key)) := by
  refine ⟨fun c hc => ?_, fun M n hM => ?_⟩
  · subst hc; exact hwf c (InfP.popped_mem l s hok c ha)
  · subst hM
    have := InfP.popped_replaced l s hok M n ha
    subst this
    exact ⟨tableAt_good l n (fun c hc => (hwf c hc).1), tableAt_keyed l n⟩

/-- **The store writer of a lone popped delta**, through the invariant (as `infInv_batchWriter`). -/
theorem infInv_singleWriter (γa : ApiNames) (r : Res) (γf : FifoNames) (γt : TsNames)
    (γi : InfNames) (R0 : Reg) (d : cache.FD) (hreg : ∀ x ∈ d.objs, ∃ o, R0 !! x = some o) :
    ⊢ infInv γa r γf γt γi -∗ ([∗map] x ↦ o ∈ R0, x ↪[γi.reg]□ o) -∗
      storeWriter γt (procWriter γi [d]) (singleRw R0 d) := by
  iintro #Hinv #Hsnap
  iunfold storeWriter
  imodintro
  iintro %σ Hw
  iunfold procWriter at Hw
  icases Hw with ⟨Hsw', %ap', Hpop'⟩
  iunfold infInv at Hinv
  iinv Hinv with >Hi Hclose
  iunfold infRes at Hi
  icases Hi with ⟨%σp, %s, %q, %σs, %R, %pd, %ap, #Hp, Hreg, #Hsnap', #Hobjs, Hq, Hst, Hsw, Hlast, Hpop,
    Hlb, %Hok⟩
  icombine Hsw Hsw' gives % ⟨_, hσ⟩
  subst hσ
  icombine Hpop Hpop' gives % ⟨_, hpd⟩
  simp only [Prod.mk.injEq] at hpd
  obtain ⟨rfl, rfl⟩ := hpd
  ihave ⟨%hsub, Hreg, -⟩ := reg_sub γi.reg R R0 $$ [$Hreg $Hsnap]
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ \ ↑infN from Std.LawfulSet.empty_subset)
  iintro Hclose2
  iframe Hst
  iintro %σ' %hRw Hst
  obtain ⟨hok, hlast, hfifo, hpop, hst, hres, hgood, hfq, hpr⟩ := Hok
  have hkf : ∀ x ∈ d.objs, regKF R0 x = regKF R x := by
    intro x hx; obtain ⟨o, ho⟩ := hreg x hx; simp [regKF, ho, hsub x o ho]
  have hrvf : ∀ x ∈ d.objs, regRv R0 x = regRv R x := by
    intro x hx; obtain ⟨o, ho⟩ := hreg x hx; simp [regRv, ho, hsub x o ho]
  rcases hRw with h | h
  · rw [h]
    imod Hclose2 with -
    imod Hclose $$ [Hreg Hq Hst Hsw Hlast Hpop Hlb] with -
    · inext
      unfold infRes
      iexists σp, s, q, σs, R, [d], ap
      iframe
      iframe #
      ipureintro; exact ⟨hok, hlast, hfifo, hpop, hst, hres, hgood, hfq, hpr⟩
    imodintro
    unfold procWriter
    iframe
  · rw [h]
    cases ap with
    | true =>
      unfold poppedRel at hpop
      simp only [↓reduceIte] at hpop
      obtain ⟨hpz, σ0, hσ0⟩ := hpop
      have hfix : cache.storeStepFD (regKF R0) (regRv R0) σs d = σs := by
        rw [storeStepFD_congr _ (regKF R) _ (regRv R) σs d hkf hrvf, hσ0]
        exact cache.storeStepFD_idem _ _ _ _
      rw [hfix]
      imod Hclose2 with -
      imod Hclose $$ [Hreg Hq Hst Hsw Hlast Hpop Hlb] with -
      · inext
        unfold infRes
        iexists σp, s, q, σs, R, [d], true
        iframe
        iframe #
        ipureintro
        refine ⟨hok, hlast, hfifo, ?_, hst, hres, hgood, hfq, hpr⟩
        unfold poppedRel; simp only [↓reduceIte]; exact ⟨hpz, σ0, hσ0⟩
      imodintro
      unfold procWriter
      iframe
    | false =>
      unfold poppedRel at hpop
      simp only [Bool.false_eq_true, ↓reduceIte] at hpop
      ihave #Hp2 := Hp
      iunfold pastSt at Hp2
      icases Hp2 with ⟨%Hh, -, %hH⟩
      have hwf := hH.2.1
      obtain ⟨a, hpa, hda⟩ := forall₂_singleton hpop
      · obtain ⟨hchg, hrep⟩ := single_facts _ s hok
          (fun c hc => ⟨hgood c hc, (hwf.log_obj r c hc).2⟩) a (by rw [hpa]; simp)
        have hst' := storeRel_single R R0 hsub σs s.store d a hst hda hreg hchg hrep
        have hsorted := hwf.log_sorted r
        have hok' := InfP.ok_apply _ hsorted s hok
        have hrvle := rvNat_mono (InfP.apply_rv_le _ hsorted s hok)
        have happ : s.store.applyAll s.popped = s.store.apply a := by
          rw [hpa]; rfl
        imod ghostVar_update_halves (cache.storeStepFD (regKF R0) (regRv R0) σs d) $$ Hsw Hsw'
          with ⟨Hsw, Hsw'⟩
        imod ghostVar_update_halves ([d], true) $$ Hpop Hpop' with ⟨Hpop, Hpop'⟩
        imod mono_nat_own_update _ hrvle $$ Hlb with ⟨Hlb, -⟩
        imod Hclose2 with -
        imod Hclose $$ [Hreg Hq Hst Hsw Hlast Hpop Hlb] with -
        · inext
          unfold infRes
          iexists σp, ⟨s.store.applyAll s.popped, [], s.fifo, s.last⟩, q,
            cache.storeStepFD (regKF R0) (regRv R0) σs d, R, [d], true
          iframe
          iframe #
          ipureintro
          refine ⟨hok', hlast, hfifo, ?_, by rw [happ]; exact hst', hres, hgood, hfq, hpr⟩
          unfold poppedRel
          simp only [↓reduceIte]
          refine ⟨trivial, σs, ?_⟩
          show _ = cache.storeStepFD _ _ _ _
          rw [storeStepFD_congr _ (regKF R) _ (regRv R) σs d hkf hrvf]
        imodintro
        unfold procWriter
        iframe

/-- **A lone delta's processing finished** (as `infInv_batchFinish`). -/
theorem infInv_singleFinish (γa : ApiNames) (r : Res) (γf : FifoNames) (γt : TsNames)
    (γi : InfNames) (R0 : Reg) (d : cache.FD) (hreg : ∀ x ∈ d.objs, ∃ o, R0 !! x = some o)
    (σ σ' : cache.St) (hstep : σ' = cache.storeStepFD (regKF R0) (regRv R0) σ d) :
    ⊢ infInv γa r γf γt γi -∗ ([∗map] x ↦ o ∈ R0, x ↪[γi.reg]□ o) -∗
      ghostVar γi.sw (1 : Qp).half σ' -∗ (∃ ap : Bool, ghostVar γi.pop (1 : Qp).half ([d], ap))
      ={⊤}=∗ ghostVar γi.sw (1 : Qp).half σ' ∗ procDone γi [d] := by
  iintro #Hinv #Hsnap Hsw' ⟨%ap', Hpop'⟩
  iunfold infInv at Hinv
  iinv Hinv with >Hi Hclose
  iunfold infRes at Hi
  icases Hi with ⟨%σp, %s, %q, %σs, %R, %pd, %ap, #Hp, Hreg, #Hsnap', #Hobjs, Hq, Hst, Hsw, Hlast, Hpop,
    Hlb, %Hok⟩
  icombine Hsw Hsw' gives % ⟨_, hσ⟩
  subst hσ
  icombine Hpop Hpop' gives % ⟨_, hpd⟩
  simp only [Prod.mk.injEq] at hpd
  obtain ⟨rfl, rfl⟩ := hpd
  ihave ⟨%hsub, Hreg, -⟩ := reg_sub γi.reg R R0 $$ [$Hreg $Hsnap]
  obtain ⟨hok, hlast, hfifo, hpop, hst, hres, hgood, hfq, hpr⟩ := Hok
  have hkf : ∀ x ∈ d.objs, regKF R0 x = regKF R x := by
    intro x hx; obtain ⟨o, ho⟩ := hreg x hx; simp [regKF, ho, hsub x o ho]
  have hrvf : ∀ x ∈ d.objs, regRv R0 x = regRv R x := by
    intro x hx; obtain ⟨o, ho⟩ := hreg x hx; simp [regRv, ho, hsub x o ho]
  cases ap with
  | true =>
    imod Hclose $$ [Hreg Hq Hst Hsw Hlast Hpop Hlb] with -
    · inext
      unfold infRes
      iexists σp, s, q, σs, R, [d], true
      iframe
      iframe #
      ipureintro; exact ⟨hok, hlast, hfifo, hpop, hst, hres, hgood, hfq, hpr⟩
    imodintro
    unfold procDone
    iframe
  | false =>
    unfold poppedRel at hpop
    simp only [Bool.false_eq_true, ↓reduceIte] at hpop
    ihave #Hp2 := Hp
    iunfold pastSt at Hp2
    icases Hp2 with ⟨%Hh, -, %hH⟩
    have hwf := hH.2.1
    obtain ⟨a, hpa, hda⟩ := forall₂_singleton hpop
    obtain ⟨hchg, hrep⟩ := single_facts _ s hok
      (fun c hc => ⟨hgood c hc, (hwf.log_obj r c hc).2⟩) a (by rw [hpa]; simp)
    have hfix : cache.storeStepFD (regKF R0) (regRv R0) σs d = σs := by
      rw [hstep]; exact cache.storeStepFD_idem _ _ _ _
    have hst' := storeRel_single R R0 hsub σs s.store d a hst hda hreg hchg hrep
    rw [hfix] at hst'
    have hsorted := hwf.log_sorted r
    have hok' := InfP.ok_apply _ hsorted s hok
    have hrvle := rvNat_mono (InfP.apply_rv_le _ hsorted s hok)
    have happ : s.store.applyAll s.popped = s.store.apply a := by rw [hpa]; rfl
    imod ghostVar_update_halves ([d], true) $$ Hpop Hpop' with ⟨Hpop, Hpop'⟩
    imod mono_nat_own_update _ hrvle $$ Hlb with ⟨Hlb, -⟩
    imod Hclose $$ [Hreg Hq Hst Hsw Hlast Hpop Hlb] with -
    · inext
      unfold infRes
      iexists σp, ⟨s.store.applyAll s.popped, [], s.fifo, s.last⟩, q, σs, R, [d], true
      iframe
      iframe #
      ipureintro
      refine ⟨hok', hlast, hfifo, ?_, by rw [happ]; exact hst', hres, hgood, hfq, hpr⟩
      unfold poppedRel
      simp only [↓reduceIte]
      refine ⟨trivial, σ, ?_⟩
      show _ = cache.storeStepFD _ _ _ _
      rw [← storeStepFD_congr _ (regKF R) _ (regRv R) σ d hkf hrvf, hstep]
    imodintro
    unfold procDone
    iframe

/-- **Registering a fresh object** with the informer (the reflector, for each object a list or a
watch event gives it): it becomes read-only and registered with its model object (`infObj`, the
FIFO's and the store's contract). An object owned exclusively is not registered yet
(`objAt_excl`). -/
theorem infInv_register (γa : ApiNames) (r : Res) (γf : FifoNames) (γt : TsNames)
    (γi : InfNames) (x : GoInterface) (o : Obj) (hres : o.res = r) :
    ⊢ infInv (GF := GF) γa r γf γt γi -∗ apimodel.objAt x (DFrac.own 1) o ={⊤}=∗ infObj γi r x := by
  iintro #Hinv Hx
  iunfold infInv at Hinv
  iinv Hinv with >Hi Hclose
  iunfold infRes at Hi
  icases Hi with ⟨%σp, %s, %q, %σs, %R, %pd, %ap, #Hp, Hreg, #Hsnap, #Hobjs, Hq, Hst, Hsw, Hlast,
    Hpop, Hlb, %Hok⟩
  obtain ⟨hok, hlast, hfifo, hpop, hst, hres', hgood, hfq, hpr⟩ := Hok
  cases hx : R !! x with
  | some o' =>
    ihave #Ho' := BigSepM.bigSepM_lookup (Φ := fun x o => iprop(□ apimodel.objAt x DFrac.discard o))
      hx $$ Hobjs
    ihave %hf := objAt_excl x o o' $$ [$Hx $Ho']
    exact hf.elim
  | none =>
    imod ghost_map_insert_persist (γ := γi.reg) x o hx $$ Hreg with ⟨Hreg, #Hel⟩
    imod objAt_persist x (DFrac.own 1) o $$ Hx with #Hx
    have hle := regLe_insert R x o hx
    imod Hclose $$ [Hreg Hq Hst Hsw Hlast Hpop Hlb] with -
    · inext
      unfold infRes
      iexists σp, s, q, σs, <[x := o]> R, pd, ap
      iframe
      isplitr
      · iframe #
      isplitr
      · iapply (BigSepM.bigSepM_insert (Φ := fun x o => iprop(x ↪[γi.reg]□ o)) hx).2
        iframe #
      isplitr
      · iapply (BigSepM.bigSepM_insert (Φ := fun x o => iprop(□ apimodel.objAt x DFrac.discard o))
          hx).2
        iframe #
      ipureintro
      refine ⟨hok, hlast, forall₂_fdRel_mono hle hfifo, poppedRel_mono hle σs pd ap s.popped hpr hpop,
        storeRel_mono hle σs s.store hst, ?_, hgood, hfq, pdReg_mono hle pd hpr⟩
      intro y o' hy
      rw [GMap.lookup_insert_eq_iff] at hy
      split at hy
      · cases hy; exact hres
      · exact hres' y o' hy
    imodintro
    unfold infObj
    iexists o
    iframe #
    ipureintro; exact hres

end glue

end informer
end EtcdGrove
end Perennial

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
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.HistLemmas
public import Proof.k8s_io.client_go.tools.cache.InformerDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace informer

open Iris Iris.BI Iris.ProofMode apimodel cache

section glue
variable [GooseExts] [GooseSemantics] [GooseInterp]
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
  icases Hi with ⟨%σp, %s, %q, %σs, %R, %pd, %ap, %f, #Hp, Hreg, #Hsnap, #Hobjs, Hq, Hst, Hsw, Hlast, Hpop, Hlb, Hfst,
    %Hok⟩
  ihave #Hlb' := monoNatLbOwn_get γi.rvlb 1 (rvNat s.store.rv) $$ Hlb
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ \ ↑infN from Std.LawfulSet.empty_subset)
  iintro Hclose2
  iexists σs
  iframe Hst
  iintro Hst
  imod Hclose2 with -
  imod Hclose $$ [Hreg Hq Hst Hsw Hlast Hpop Hlb Hfst] with -
  · inext
    unfold infRes
    iexists σp, s, q, σs, R, pd, ap, f
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
  icases Hi with ⟨%σp, %s, %q, %σs, %R, %pd, %ap, %f, #Hp, Hreg, #Hsnap, #Hobjs, Hq, Hst, Hsw, Hlast, Hpop, Hlb, Hfst,
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
    imod Hclose $$ [Hreg Hq Hst Hsw Hlast Hpop Hlb Hfst] with -
    · inext
      unfold infRes
      iexists σp, s, q, σs, R, [], false, f
      iframe
      iframe #
      ipureintro; exact Hok
    imodintro
    iintro %e
    iapply (hΩ e)
    iunfold procIdle
    iexact Hidle
  · iintro %hne Hq
    obtain ⟨hok, hlast, hfifo, hpop, hst, hres, hgood, hfq, hpr, hsy⟩ := Hok
    have hpop0 : s.popped = [] := by
      unfold poppedRel at hpop; simp only [Bool.false_eq_true, ↓reduceIte] at hpop
      exact forall₂_nil_left hpop
    obtain ⟨rest, hrest⟩ := FQ.batch_prefix q
    rw [← hrest] at hfifo
    obtain ⟨m1, m2, hm, h1, h2⟩ := forall₂_append_split _ _ _ hfifo
    imod ghostVar_update_halves (q.batch, false) $$ Hpop Hidle with ⟨Hpop, Hidle⟩
    imod Hclose2 with -
    imod Hclose $$ [Hreg Hq Hst Hsw Hlast Hpop Hlb Hfst] with -
    · inext
      unfold infRes
      iexists σp, ⟨s.store, m1, m2, s.last⟩, { q with items := q.items.drop q.batch.length }, σs, R,
        q.batch, false, f
      iframe
      iframe #
      ipureintro
      refine ⟨?_, hlast, ?_, ?_, hst, hres, hgood, fqOk_pop q hfq hne, ?_,
        sync_pop q s f m1 m2 _ _ hsy hpop0 hm hne⟩
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
  icases Hi with ⟨%σp, %s, %q, %σs, %R, %pd, %ap, %f, #Hp, Hreg, #Hsnap', #Hobjs, Hq, Hst, Hsw, Hlast, Hpop,
    Hlb, Hfst, %Hok⟩
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
  obtain ⟨hok, hlast, hfifo, hpop, hst, hres, hgood, hfq, hpr, hsy⟩ := Hok
  have hkf : ∀ x ∈ fdObjs pd, regKF R0 x = regKF R x := by
    intro x hx; obtain ⟨o, ho⟩ := hreg x hx; simp [regKF, ho, hsub x o ho]
  have hrvf : ∀ x ∈ fdObjs pd, regRv R0 x = regRv R x := by
    intro x hx; obtain ⟨o, ho⟩ := hreg x hx; simp [regRv, ho, hsub x o ho]
  rcases hRw with h | h
  · -- a read
    rw [h]
    imod Hclose2 with -
    imod Hclose $$ [Hreg Hq Hst Hsw Hlast Hpop Hlb Hfst] with -
    · inext
      unfold infRes
      iexists σp, s, q, σs, R, pd, ap, f
      iframe
      iframe #
      ipureintro; exact ⟨hok, hlast, hfifo, hpop, hst, hres, hgood, hfq, hpr, hsy⟩
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
      imod Hclose $$ [Hreg Hq Hst Hsw Hlast Hpop Hlb Hfst] with -
      · inext
        unfold infRes
        iexists σp, s, q, σs, R, pd, true, f
        iframe
        iframe #
        ipureintro
        refine ⟨hok, hlast, hfifo, ?_, hst, hres, hgood, hfq, hpr, hsy⟩
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
      imod Hclose $$ [Hreg Hq Hst Hsw Hlast Hpop Hlb Hfst] with -
      · inext
        unfold infRes
        iexists σp, ⟨s.store.applyAll s.popped, [], s.fifo, s.last⟩, q,
          cache.batchStore (regKF R0) (regRv R0) σs pd, R, pd, true, f
        iframe
        iframe #
        ipureintro
        refine ⟨hok', hlast, hfifo, ?_, hst', hres, hgood, hfq, hpr,
          sync_apply _ hsorted q _ s f hsy (forall₂_length hpop) hok⟩
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
  icases Hi with ⟨%σp, %s, %q, %σs, %R, %pd, %ap, %f, #Hp, Hreg, #Hsnap', #Hobjs, Hq, Hst, Hsw, Hlast, Hpop,
    Hlb, Hfst, %Hok⟩
  icombine Hsw Hsw' gives % ⟨_, hσ⟩
  subst hσ
  icombine Hpop Hpop' gives % ⟨_, hpd⟩
  simp only [Prod.mk.injEq] at hpd
  obtain ⟨rfl, rfl⟩ := hpd
  ihave ⟨%hsub, Hreg, -⟩ := reg_sub γi.reg R R0 $$ [$Hreg $Hsnap]
  obtain ⟨hok, hlast, hfifo, hpop, hst, hres, hgood, hfq, hpr, hsy⟩ := Hok
  have hkf : ∀ x ∈ fdObjs pd, regKF R0 x = regKF R x := by
    intro x hx; obtain ⟨o, ho⟩ := hreg x hx; simp [regKF, ho, hsub x o ho]
  have hrvf : ∀ x ∈ fdObjs pd, regRv R0 x = regRv R x := by
    intro x hx; obtain ⟨o, ho⟩ := hreg x hx; simp [regRv, ho, hsub x o ho]
  cases ap with
  | true =>
    imod Hclose $$ [Hreg Hq Hst Hsw Hlast Hpop Hlb Hfst] with -
    · inext
      unfold infRes
      iexists σp, s, q, σs, R, pd, true, f
      iframe
      iframe #
      ipureintro; exact ⟨hok, hlast, hfifo, hpop, hst, hres, hgood, hfq, hpr, hsy⟩
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
    imod Hclose $$ [Hreg Hq Hst Hsw Hlast Hpop Hlb Hfst] with -
    · inext
      unfold infRes
      iexists σp, ⟨s.store.applyAll s.popped, [], s.fifo, s.last⟩, q, σs, R, pd, true, f
      iframe
      iframe #
      ipureintro
      refine ⟨hok', hlast, hfifo, ?_, hst', hres, hgood, hfq, hpr,
          sync_apply _ hsorted q _ s f hsy (forall₂_length hpop) hok⟩
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
  icases Hi with ⟨%σp, %s, %q, %σs, %R, %pd, %ap, %f, #Hp, Hreg, #Hsnap', #Hobjs, Hq, Hst, Hsw, Hlast, Hpop,
    Hlb, Hfst, %Hok⟩
  iunfold procDone at Hdone
  icombine Hpop Hdone gives % ⟨_, hpd⟩
  simp only [Prod.mk.injEq] at hpd
  obtain ⟨rfl, rfl⟩ := hpd
  obtain ⟨hok, hlast, hfifo, hpop, hst, hres, hgood, hfq, hpr, hsy⟩ := Hok
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
  imod Hclose $$ [Hreg Hq Hst Hsw Hlast Hpop Hlb Hfst] with -
  · inext
    unfold infRes
    iexists σp, s, q.popDoneN pd.length, σs, R, [], false, f
    iframe
    iframe #
    ipureintro
    refine ⟨hok, hlast, ?_, ?_, hst, hres, hgood, ?_⟩
    · unfold cache.FQ.popDoneN; split <;> exact hfifo
    · unfold poppedRel; simp only [Bool.false_eq_true, ↓reduceIte, hpz]; exact .nil
    · refine ⟨⟨?_, fun h => absurd h (by simp)⟩, by simp [pdReg], sync_done q pd s f hsy hpz⟩
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
  icases Hi with ⟨%σp, %s, %q, %σs, %R, %pd, %ap, %f, #Hp, Hreg, #Hsnap', #Hobjs, Hq, Hst, Hsw, Hlast, Hpop,
    Hlb, Hfst, %Hok⟩
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
  obtain ⟨hok, hlast, hfifo, hpop, hst, hres, hgood, hfq, hpr, hsy⟩ := Hok
  have hkf : ∀ x ∈ d.objs, regKF R0 x = regKF R x := by
    intro x hx; obtain ⟨o, ho⟩ := hreg x hx; simp [regKF, ho, hsub x o ho]
  have hrvf : ∀ x ∈ d.objs, regRv R0 x = regRv R x := by
    intro x hx; obtain ⟨o, ho⟩ := hreg x hx; simp [regRv, ho, hsub x o ho]
  rcases hRw with h | h
  · rw [h]
    imod Hclose2 with -
    imod Hclose $$ [Hreg Hq Hst Hsw Hlast Hpop Hlb Hfst] with -
    · inext
      unfold infRes
      iexists σp, s, q, σs, R, [d], ap, f
      iframe
      iframe #
      ipureintro; exact ⟨hok, hlast, hfifo, hpop, hst, hres, hgood, hfq, hpr, hsy⟩
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
      imod Hclose $$ [Hreg Hq Hst Hsw Hlast Hpop Hlb Hfst] with -
      · inext
        unfold infRes
        iexists σp, s, q, σs, R, [d], true, f
        iframe
        iframe #
        ipureintro
        refine ⟨hok, hlast, hfifo, ?_, hst, hres, hgood, hfq, hpr, hsy⟩
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
        imod Hclose $$ [Hreg Hq Hst Hsw Hlast Hpop Hlb Hfst] with -
        · inext
          unfold infRes
          iexists σp, ⟨s.store.applyAll s.popped, [], s.fifo, s.last⟩, q,
            cache.storeStepFD (regKF R0) (regRv R0) σs d, R, [d], true, f
          iframe
          iframe #
          ipureintro
          refine ⟨hok', hlast, hfifo, ?_, by rw [happ]; exact hst', hres, hgood, hfq, hpr,
          sync_apply _ hsorted q _ s f hsy (forall₂_length hpop) hok⟩
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
  icases Hi with ⟨%σp, %s, %q, %σs, %R, %pd, %ap, %f, #Hp, Hreg, #Hsnap', #Hobjs, Hq, Hst, Hsw, Hlast, Hpop,
    Hlb, Hfst, %Hok⟩
  icombine Hsw Hsw' gives % ⟨_, hσ⟩
  subst hσ
  icombine Hpop Hpop' gives % ⟨_, hpd⟩
  simp only [Prod.mk.injEq] at hpd
  obtain ⟨rfl, rfl⟩ := hpd
  ihave ⟨%hsub, Hreg, -⟩ := reg_sub γi.reg R R0 $$ [$Hreg $Hsnap]
  obtain ⟨hok, hlast, hfifo, hpop, hst, hres, hgood, hfq, hpr, hsy⟩ := Hok
  have hkf : ∀ x ∈ d.objs, regKF R0 x = regKF R x := by
    intro x hx; obtain ⟨o, ho⟩ := hreg x hx; simp [regKF, ho, hsub x o ho]
  have hrvf : ∀ x ∈ d.objs, regRv R0 x = regRv R x := by
    intro x hx; obtain ⟨o, ho⟩ := hreg x hx; simp [regRv, ho, hsub x o ho]
  cases ap with
  | true =>
    imod Hclose $$ [Hreg Hq Hst Hsw Hlast Hpop Hlb Hfst] with -
    · inext
      unfold infRes
      iexists σp, s, q, σs, R, [d], true, f
      iframe
      iframe #
      ipureintro; exact ⟨hok, hlast, hfifo, hpop, hst, hres, hgood, hfq, hpr, hsy⟩
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
    imod Hclose $$ [Hreg Hq Hst Hsw Hlast Hpop Hlb Hfst] with -
    · inext
      unfold infRes
      iexists σp, ⟨s.store.applyAll s.popped, [], s.fifo, s.last⟩, q, σs, R, [d], true, f
      iframe
      iframe #
      ipureintro
      refine ⟨hok', hlast, hfifo, ?_, by rw [happ]; exact hst', hres, hgood, hfq, hpr,
          sync_apply _ hsorted q _ s f hsy (forall₂_length hpop) hok⟩
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
FIFO's and the store's contract), and its registry entry. An object owned exclusively is not
registered yet (`objAt_excl`). -/
theorem infInv_register (γa : ApiNames) (r : Res) (γf : FifoNames) (γt : TsNames)
    (γi : InfNames) (x : GoInterface) (o : Obj) (hres : o.res = r) :
    ⊢ infInv (GF := GF) γa r γf γt γi -∗ apimodel.objAt x (DFrac.own 1) o ={⊤}=∗
      infObj γi r x ∗ x ↪[γi.reg]□ o := by
  iintro #Hinv Hx
  iunfold infInv at Hinv
  iinv Hinv with >Hi Hclose
  iunfold infRes at Hi
  icases Hi with ⟨%σp, %s, %q, %σs, %R, %pd, %ap, %f, #Hp, Hreg, #Hsnap, #Hobjs, Hq, Hst, Hsw, Hlast,
    Hpop, Hlb, Hfst, %Hok⟩
  obtain ⟨hok, hlast, hfifo, hpop, hst, hres', hgood, hfq, hpr, hsy⟩ := Hok
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
    imod Hclose $$ [Hreg Hq Hst Hsw Hlast Hpop Hlb Hfst] with -
    · inext
      unfold infRes
      iexists σp, s, q, σs, <[x := o]> R, pd, ap, f
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
        storeRel_mono hle σs s.store hst, ?_, hgood, hfq, pdReg_mono hle pd hpr, hsy⟩
      intro y o' hy
      rw [GMap.lookup_insert_eq_iff] at hy
      split at hy
      · cases hy; exact hres
      · exact hres' y o' hy
    imodintro
    iframe #
    unfold infObj
    iexists o
    iframe #
    ipureintro; exact hres

/-- **The reflector's last version** (its half; the invariant holds the other). -/
def reflLast (γi : InfNames) (v : Option Nat) : IProp GF := ghostVar γi.last (1 : Qp).half v

/-- Moving the invariant to a later past state: the log grows after the versions it has. -/
theorem infP_ok_later (r : Res) (σp σ1 : apimodel.St) (s : InfP) (hle : St.le σp σ1)
    (hok : s.ok (σp.tbl r).log) (hlast : rvLe s.last (some σp.rev.toNat)) :
    s.ok (σ1.tbl r).log := by
  obtain ⟨-, -, hlog⟩ := hle
  obtain ⟨⟨l', hl'⟩, hlater⟩ := hlog r
  rw [← hl'] at hlater ⊢
  rw [List.drop_left] at hlater
  exact InfP.ok_extend _ l' s σp.rev.toNat hok hlast hlater

/-- **A watch event's change enqueued** (the reflector's `Add`/`Update`/`Delete` of the event's
object), through the invariant: the change, the next one after the reflector's last version in the
log of the past state `σ1` the event came from, is the queue's new last delta, and the reflector's
last version becomes its. The FIFO's logically atomic update. -/
theorem infInv_pushChangeAU (γa : ApiNames) (r : Res) (γf : FifoNames) (γt : TsNames)
    (γi : InfNames) (u : Nat) (σ1 : apimodel.St) (c : Change) (x : GoInterface)
    (hn : NextChange (σ1.tbl r).log u c) (hgood1 : ∀ c ∈ (σ1.tbl r).log, keyGood c.obj.key)
    (hnil : x ≠ interface.nil) (K : IProp GF) :
    ⊢ infInv γa r γf γt γi -∗ pastSt γa σ1 -∗ x ↪[γi.reg]□ c.obj -∗ reflLast γi (some u) -∗
      (reflLast γi (some c.rv.toNat) -∗ K) -∗
      |={⊤ \ ∅, ∅}=> ∃ q, fifoSt γf q ∗ (fifoSt γf (q.addObj (fdTypeOf c.typ) x) ={∅, ⊤ \ ∅}=∗ K) := by
  iintro #Hinv #Hp1 #Hx Hl HK
  rw [Iris.Std.LawfulSet.diff_empty]
  iunfold infInv at Hinv
  iinv Hinv with >Hi Hclose
  iunfold infRes at Hi
  icases Hi with ⟨%σp, %s, %q, %σs, %R, %pd, %ap, %f, #Hp, Hreg, #Hsnap, #Hobjs, Hq, Hst, Hsw, Hlast,
    Hpop, Hlb, Hfst, %Hok⟩
  obtain ⟨hok, hlast, hfifo, hpop, hst, hres, hgood, hfq, hpr, hsy⟩ := Hok
  iunfold reflLast at Hl
  icombine Hlast Hl gives % ⟨_, hu⟩
  ihave %hxR := ghost_map_lookup (γ := γi.reg) $$ Hreg Hx
  ihave %hcmp := pastSt_cmp γa σp σ1 $$ Hp Hp1
  ihave #Hp1' := Hp1
  iunfold pastSt at Hp1'
  icases Hp1' with ⟨%H1, -, %hH1⟩
  ihave #Hp' := Hp
  iunfold pastSt at Hp'
  icases Hp' with ⟨%Hp0, -, %hHp⟩
  have hwf1 := hH1.2.1
  have hwfp := hHp.2.1
  have hc1 : c.rv.toNat ≤ σ1.rev.toNat := (hwf1.log_le r c hn.1).2
  -- the state the invariant moves to, with the change pushed
  have key : ∃ σq : apimodel.St, St.le σp σq ∧ (σq = σp ∨ σq = σ1) ∧
      NextChange (σq.tbl r).log u c ∧ c.rv.toNat ≤ σq.rev.toNat ∧ s.ok (σq.tbl r).log ∧
      rvLe s.last (some σq.rev.toNat) := by
    rcases hcmp with hle | hle
    · refine ⟨σ1, hle, Or.inr rfl, hn, hc1, infP_ok_later r σp σ1 s hle hok hlast, ?_⟩
      cases hl : s.last with
      | none => trivial
      | some w =>
        rw [hl] at hlast; simp only [rvLe] at hlast ⊢
        have := hle.1; omega
    · refine ⟨σp, St.le_refl σp, Or.inl rfl, ?_, by have := hle.1; omega, hok, hlast⟩
      obtain ⟨-, -, hlog⟩ := hle
      obtain ⟨⟨l', hl'⟩, hlater⟩ := hlog r
      rw [← hl'] at hlater ⊢
      rw [List.drop_left] at hlater
      exact nextChange_extend _ l' u σ1.rev.toNat c hn hc1 hlater
  obtain ⟨σq, hleq, hσq, hnq, hcq, hokq, hlastq⟩ := key
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ \ ↑infN from Std.LawfulSet.empty_subset)
  iintro Hclose2
  iexists q
  iframe Hq
  iintro Hq
  imod ghostVar_update_halves (some c.rv.toNat) $$ Hlast Hl with ⟨Hlast, Hl⟩
  imod Hclose2 with -
  have hpush := ok_push_change (σq.tbl r).log ⟨s.store, s.popped ++ s.fifo, s.last⟩ u c hokq hu hnq
  imod Hclose $$ [Hreg Hq Hst Hsw Hlast Hpop Hlb Hfst] with -
  · inext
    unfold infRes
    iexists σq, ⟨s.store, s.popped, s.fifo ++ [.change c], some c.rv.toNat⟩,
      q.addObj (fdTypeOf c.typ) x, σs, R, pd, ap, f
    iframe
    isplitr
    · rcases hσq with rfl | rfl
      · iexact Hp
      · iexact Hp1
    iframe #
    ipureintro
    refine ⟨InfP.ok_push _ s _ _ hpush, by simp only [rvLe]; exact hcq, ?_, hpop, hst, hres, ?_, ?_,
      hpr, ?_⟩
    · show List.Forall₂ (fdRel R) (q.items ++ [cache.FD.obj (fdTypeOf c.typ) x]) (s.fifo ++ [Delta.change c])
      exact forall₂_snoc hfifo ⟨rfl, hxR, hnil⟩
    · rcases hσq with rfl | rfl
      · exact hgood
      · exact hgood1
    · refine ⟨fun h => absurd h (by simp [cache.FQ.addObj]), fun hlen => ?_⟩
      obtain ⟨_, h2⟩ := hfq.2 hlen
      exact ⟨rfl, h2⟩
    · have hqp := sync_populated q pd ap s f hsy u hu
      exact sync_push q _ pd ap s f _ _ hsy hqp rfl rfl
        (sync_addObj_synced q pd ap s f _ x hsy hqp)
  imodintro
  iapply HK
  iunfold reflLast
  iexact Hl

/-- **The state the invariant moves to** at a push from a past state `σ1`: the later of `σ1` and
the invariant's, whose log is `σ1`'s extended after `σ1`'s version. -/
theorem later_state (r : Res) (σp σ1 : apimodel.St) (s : InfP)
    (hcmp : St.le σp σ1 ∨ St.le σ1 σp) (hok : s.ok (σp.tbl r).log)
    (hlast : rvLe s.last (some σp.rev.toNat)) :
    ∃ σq : apimodel.St, St.le σp σq ∧ (σq = σp ∨ σq = σ1) ∧ s.ok (σq.tbl r).log ∧
      rvLe s.last (some σq.rev.toNat) ∧ σ1.rev.toNat ≤ σq.rev.toNat ∧
      ∃ l', (σq.tbl r).log = (σ1.tbl r).log ++ l' ∧ ∀ d ∈ l', σ1.rev.toNat < d.rv.toNat := by
  rcases hcmp with hle | hle
  · refine ⟨σ1, hle, Or.inr rfl, infP_ok_later r σp σ1 s hle hok hlast, ?_, Nat.le_refl _,
      [], by simp, by simp⟩
    cases hl : s.last with
    | none => trivial
    | some w =>
      rw [hl] at hlast; simp only [rvLe] at hlast ⊢
      have := hle.1; omega
  · refine ⟨σp, St.le_refl σp, Or.inl rfl, hok, hlast, hle.1, ?_⟩
    obtain ⟨-, -, hlog⟩ := hle
    obtain ⟨⟨l', hl'⟩, hlater⟩ := hlog r
    refine ⟨l', hl'.symm, ?_⟩
    rw [← hl', List.drop_left] at hlater
    exact hlater

theorem FQ_replace_items (objs : List GoInterface) (rv : GoString) (q : cache.FQ) :
    (q.replace objs rv).items = q.items ++ [.replaced objs rv] := by
  unfold cache.FQ.replace; split <;> rfl

/-- **A bookmark enqueued** (the reflector's `Bookmark` of a watch's bookmark event), through the
invariant: no change of the log of the past state `σ1` the event came from between the reflector's
last version and the bookmark's, which becomes the reflector's last. -/
theorem infInv_pushBookmarkAU (γa : ApiNames) (r : Res) (γf : FifoNames) (γt : TsNames)
    (γi : InfNames) (u : Nat) (σ1 : apimodel.St) (w : w64)
    (hq : Quiet (σ1.tbl r).log u w.toNat) (hw : w.toNat ≤ σ1.rev.toNat)
    (hgood1 : ∀ c ∈ (σ1.tbl r).log, keyGood c.obj.key) (K : IProp GF) :
    ⊢ infInv γa r γf γt γi -∗ pastSt γa σ1 -∗ reflLast γi (some u) -∗
      (reflLast γi (some w.toNat) -∗ K) -∗
      |={⊤ \ ∅, ∅}=> ∃ q, fifoSt γf q ∗
        (fifoSt γf { q with items := q.items ++ [.bookmark (rvStr w)] } ={∅, ⊤ \ ∅}=∗ K) := by
  iintro #Hinv #Hp1 Hl HK
  rw [Iris.Std.LawfulSet.diff_empty]
  iunfold infInv at Hinv
  iinv Hinv with >Hi Hclose
  iunfold infRes at Hi
  icases Hi with ⟨%σp, %s, %q, %σs, %R, %pd, %ap, %f, #Hp, Hreg, #Hsnap, #Hobjs, Hq, Hst, Hsw, Hlast,
    Hpop, Hlb, Hfst, %Hok⟩
  obtain ⟨hok, hlast, hfifo, hpop, hst, hres, hgood, hfq, hpr, hsy⟩ := Hok
  iunfold reflLast at Hl
  icombine Hlast Hl gives % ⟨_, hu⟩
  ihave %hcmp := pastSt_cmp γa σp σ1 $$ Hp Hp1
  obtain ⟨σq, hleq, hσq, hokq, hlastq, hrevq, l', hl', hl'gt⟩ := later_state r σp σ1 s hcmp hok hlast
  have hqq : Quiet (σq.tbl r).log u w.toNat := by
    rw [hl']; exact quiet_extend _ l' u w.toNat hq (fun d hd => by have := hl'gt d hd; omega)
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ \ ↑infN from Std.LawfulSet.empty_subset)
  iintro Hclose2
  iexists q
  iframe Hq
  iintro Hq
  imod ghostVar_update_halves (some w.toNat) $$ Hlast Hl with ⟨Hlast, Hl⟩
  imod Hclose2 with -
  have hpush := ok_push_bookmark (σq.tbl r).log ⟨s.store, s.popped ++ s.fifo, s.last⟩ u w.toNat
    hokq hu hqq
  imod Hclose $$ [Hreg Hq Hst Hsw Hlast Hpop Hlb Hfst] with -
  · inext
    unfold infRes
    iexists σq, ⟨s.store, s.popped, s.fifo ++ [.bookmark w.toNat], some w.toNat⟩,
      { q with items := q.items ++ [.bookmark (rvStr w)] }, σs, R, pd, ap, f
    iframe
    isplitr
    · rcases hσq with rfl | rfl
      · iexact Hp
      · iexact Hp1
    iframe #
    ipureintro
    refine ⟨InfP.ok_push _ s _ _ hpush, by simp only [rvLe]; omega,
      forall₂_snoc hfifo ⟨w, rfl, rfl⟩, hpop, hst, hres, ?_, ?_, hpr, ?_⟩
    · rcases hσq with rfl | rfl
      · exact hgood
      · exact hgood1
    · refine ⟨fun hp d hd => ?_, hfq.2⟩
      rcases List.mem_append.1 hd with hd | hd
      · exact hfq.1 hp d hd
      · simp at hd; exact ⟨_, hd⟩
    · have hqp := sync_populated q pd ap s f hsy u hu
      exact sync_push q _ pd ap s f _ _ hsy hqp hqp rfl rfl
  imodintro
  iapply HK
  iunfold reflLast
  iexact Hl

/-- **What the first relist gives the reflector**: before any list (`u = none`), the list's version
as the first list's (`infFirst`). -/
def firstIf (γi : InfNames) (u : Option Nat) (v : Nat) : IProp GF :=
  match u with
  | none => infFirst γi v
  | some _ => iprop(True)

instance firstIf_persistent (γi : InfNames) (u : Option Nat) (v : Nat) :
    Persistent (firstIf (GF := GF) γi u v) := by
  cases u <;> unfold firstIf <;> infer_instance

/-- The first list's ghost variable at a `Replace`: set (and made persistent) the first time. -/
theorem first_update (γ : GName) (f : Option Nat) (pop : Bool) (v : Nat)
    (hf : pop = false → f = none) :
    dghostVar (GF := GF) γ (firstDq f) f ⊢
      |==> (dghostVar γ (firstDq (if pop then f else some v)) (if pop then f else some v) ∗
        □ (⌜pop = false⌝ -∗ dghostVar γ .discard (some v))) := by
  cases pop with
  | true =>
    simp only [↓reduceIte]
    iintro H
    imodintro
    iframe H
    imodintro
    iintro %h
    cases h
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hf rfl]
    iintro H
    iunfold firstDq at H
    imod dghostVar_update (some v) γ none $$ H with H
    imod dghostVar_persist γ 1 (some v) $$ H with #H
    imodintro
    unfold firstDq
    isplitr
    · iexact H
    · imodintro
      iintro -
      iexact H

/-- **A relist's `Replace` enqueued**, through the invariant: the listed objects, registered
(`R0`), are the table of the log of the listed past state `σ1` at the list's version `w`, at
least the reflector's last version, which `w` becomes. -/
theorem infInv_pushReplaceAU (γa : ApiNames) (r : Res) (γf : FifoNames) (γt : TsNames)
    (γi : InfNames) (u : Option Nat) (σ1 : apimodel.St) (w : w64) (R0 : Reg)
    (xs : List GoInterface) (hl : listRel R0 xs (tableAt (σ1.tbl r).log w.toNat))
    (hw : w.toNat ≤ σ1.rev.toNat) (hu : rvLe u (some w.toNat))
    (hgood1 : ∀ c ∈ (σ1.tbl r).log, keyGood c.obj.key) (K : IProp GF) :
    ⊢ infInv γa r γf γt γi -∗ pastSt γa σ1 -∗ ([∗map] x ↦ o ∈ R0, x ↪[γi.reg]□ o) -∗
      reflLast γi u -∗ (reflLast γi (some w.toNat) -∗ firstIf γi u w.toNat -∗ K) -∗
      |={⊤ \ ∅, ∅}=> ∃ q, fifoSt γf q ∗ (fifoSt γf (q.replace xs (rvStr w)) ={∅, ⊤ \ ∅}=∗ K) := by
  iintro #Hinv #Hp1 #Hs0 Hl HK
  rw [Iris.Std.LawfulSet.diff_empty]
  iunfold infInv at Hinv
  iinv Hinv with >Hi Hclose
  iunfold infRes at Hi
  icases Hi with ⟨%σp, %s, %q, %σs, %R, %pd, %ap, %f, #Hp, Hreg, #Hsnap, #Hobjs, Hq, Hst, Hsw, Hlast,
    Hpop, Hlb, Hfst, %Hok⟩
  obtain ⟨hok, hlast, hfifo, hpop, hst, hres, hgood, hfq, hpr, hsy⟩ := Hok
  iunfold reflLast at Hl
  icombine Hlast Hl gives % ⟨_, hu'⟩
  ihave ⟨%hsub, Hreg, -⟩ := reg_sub γi.reg R R0 $$ [$Hreg $Hs0]
  ihave %hcmp := pastSt_cmp γa σp σ1 $$ Hp Hp1
  obtain ⟨σq, hleq, hσq, hokq, hlastq, hrevq, l', hl', hl'gt⟩ := later_state r σp σ1 s hcmp hok hlast
  have htab : tableAt (σq.tbl r).log w.toNat = tableAt (σ1.tbl r).log w.toNat := by
    rw [hl']; exact tableAt_append _ l' σ1.rev.toNat w.toNat hw hl'gt
  have hfd : fdRel R (.replaced xs (rvStr w)) (.replaced (tableAt (σq.tbl r).log w.toNat) w.toNat) :=
    fdRel_mono hsub _ _ ⟨⟨w, rfl, rfl⟩, by rw [htab]; exact hl⟩
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ \ ↑infN from Std.LawfulSet.empty_subset)
  iintro Hclose2
  iexists q
  iframe Hq
  iintro Hq
  imod ghostVar_update_halves (some w.toNat) $$ Hlast Hl with ⟨Hlast, Hl⟩
  imod Hclose2 with -
  have hpush := ok_push_replaced (σq.tbl r).log ⟨s.store, s.popped ++ s.fifo, s.last⟩ w.toNat
    hokq (by rw [← hu'] at hu; exact hu)
  have hsync : syncOk (q.replace xs (rvStr w)) pd ap
      ⟨s.store, s.popped, s.fifo ++ [.replaced (tableAt (σq.tbl r).log w.toNat) w.toNat],
        some w.toNat⟩ (if q.populated then f else some w.toNat) := by
    cases hqp : q.populated with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      obtain ⟨hpd, hit, -⟩ := hsy.1 hqp
      have hf0 : s.fifo = [] := by rw [hit] at hfifo; exact forall₂_nil_left hfifo
      have hp0 : s.popped = [] := by
        subst hpd
        unfold poppedRel at hpop
        split at hpop
        · exact hpop.1
        · exact forall₂_nil_left hpop
      exact sync_replace_first q pd ap s f xs (rvStr w) _ w.toNat hsy hqp hf0 hp0
    | true =>
      simp only [↓reduceIte]
      exact sync_push q _ pd ap s f _ _ hsy hqp
        (by unfold cache.FQ.replace; rw [hqp]; rfl) (by unfold cache.FQ.replace; rw [hqp]; rfl)
        (by unfold cache.FQ.replace; rw [hqp]; rfl)
  have hun : u = none → q.populated = false := by
    intro hn
    cases hqp : q.populated with
    | false => rfl
    | true =>
      obtain ⟨v, -, hl, -⟩ := hsy.2 hqp
      rw [hu', hn] at hl; exact absurd rfl hl
  imod first_update γi.first f q.populated w.toNat (fun h => (hsy.1 h).2.2.2.2.2) $$ Hfst
    with ⟨Hfst, #Hfirst⟩
  imod Hclose $$ [Hreg Hq Hst Hsw Hlast Hpop Hlb Hfst] with -
  · inext
    unfold infRes
    iexists σq, ⟨s.store, s.popped,
        s.fifo ++ [.replaced (tableAt (σq.tbl r).log w.toNat) w.toNat], some w.toNat⟩,
      q.replace xs (rvStr w), σs, R, pd, ap, (if q.populated then f else some w.toNat)
    iframe
    isplitr
    · rcases hσq with rfl | rfl
      · iexact Hp
      · iexact Hp1
    iframe #
    ipureintro
    refine ⟨InfP.ok_push _ s _ _ hpush, by simp only [rvLe]; omega, ?_, hpop, hst, hres, ?_, ?_,
      hpr, hsync⟩
    · rw [FQ_replace_items]; exact forall₂_snoc hfifo hfd
    · rcases hσq with rfl | rfl
      · exact hgood
      · exact hgood1
    · unfold cache.FQ.replace
      split
      · rename_i hp
        exact ⟨fun h => (by simp only at h; rw [hp] at h; cases h), hfq.2⟩
      · rename_i hp
        exact ⟨fun h => (by simp only at h; cases h), fun hl2 => absurd (hfq.2 hl2).1 hp⟩
  ihave #Hf : firstIf γi u w.toNat $$ []
  · unfold firstIf
    cases u with
    | some _ => itrivial
    | none =>
      dsimp only [infFirst]
      iapply Hfirst; ipureintro; exact hun rfl
  imodintro
  iapply HK $$ [Hl]
  · iunfold reflLast; iexact Hl
  · iexact Hf

/-- **What `HasSynced` returning `b` gives**: when `true`, the first list's version `v` and the store's
version at least `v` from now on. -/
def syncedFacts (γi : InfNames) (b : Bool) : IProp GF :=
  if b then iprop(∃ v, infFirst γi v ∗ infRvLb γi v) else iprop(True)

instance syncedFacts_persistent (γi : InfNames) (b : Bool) :
    Persistent (syncedFacts (GF := GF) γi b) := by
  unfold syncedFacts; split <;> infer_instance

/-- **`HasSynced`'s linearization point** (`RealFIFO.HasSynced`), through the invariant: once the
FIFO is synced, the store has the first list (its version at least the first list's, `syncOk`). -/
theorem infInv_hasSyncedAU (γa : ApiNames) (r : Res) (γf : FifoNames) (γt : TsNames)
    (γi : InfNames) (K : Bool → IProp GF) :
    ⊢ infInv γa r γf γt γi -∗ (∀ b, syncedFacts γi b -∗ K b) -∗
      |={⊤ \ ∅, ∅}=> ∃ q, fifoSt γf q ∗ (fifoSt γf q ={∅, ⊤ \ ∅}=∗ K q.synced) := by
  iintro #Hinv HK
  rw [Iris.Std.LawfulSet.diff_empty]
  iunfold infInv at Hinv
  iinv Hinv with >Hi Hclose
  iunfold infRes at Hi
  icases Hi with ⟨%σp, %s, %q, %σs, %R, %pd, %ap, %f, #Hp, Hreg, #Hsnap, #Hobjs, Hq, Hst, Hsw, Hlast,
    Hpop, Hlb, Hfst, %Hok⟩
  have hsy := Hok.2.2.2.2.2.2.2.2.2
  ihave #Hlb' := monoNatLbOwn_get γi.rvlb 1 (rvNat s.store.rv) $$ Hlb
  -- the synced flag's facts, from the first list's ghost variable (persistent once set)
  have hcase : q.synced = false ∨ ∃ v, f = some v ∧ v ≤ rvNat s.store.rv := by
    cases hs : q.synced with
    | false => exact Or.inl rfl
    | true =>
      right
      have hqp : q.populated = true := by
        cases hqp : q.populated with
        | true => rfl
        | false => have := (hsy.1 hqp).2.2.2.2.1; rw [hs] at this; cases this
      obtain ⟨v, hv, -, -, hsy2, -⟩ := hsy.2 hqp
      exact ⟨v, hv, hsy2 hs⟩
  rcases hcase with hs | ⟨v, rfl, hle⟩
  · iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ \ ↑infN from Std.LawfulSet.empty_subset)
    iintro Hclose2
    iexists q
    iframe Hq
    iintro Hq
    imod Hclose2 with -
    imod Hclose $$ [Hreg Hq Hst Hsw Hlast Hpop Hlb Hfst] with -
    · inext
      unfold infRes
      iexists σp, s, q, σs, R, pd, ap, f
      iframe
      iframe #
      ipureintro; exact Hok
    imodintro
    iapply HK
    rw [hs]; unfold syncedFacts; simp only [Bool.false_eq_true, ↓reduceIte]
    itrivial
  · iunfold firstDq at Hfst
    ipersist Hfst
    ihave #Hsf : syncedFacts γi q.synced $$ []
    · unfold syncedFacts
      cases q.synced with
      | false => simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
      | true =>
        simp only [↓reduceIte]
        iexists v
        unfold infFirst infRvLb
        iframe #
        iapply (monoNatLbOwn_le v hle)
        iexact Hlb'
    iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ \ ↑infN from Std.LawfulSet.empty_subset)
    iintro Hclose2
    iexists q
    iframe Hq
    iintro Hq
    imod Hclose2 with -
    imod Hclose $$ [Hreg Hq Hst Hsw Hlast Hpop Hlb] with -
    · inext
      unfold infRes
      iexists σp, s, q, σs, R, pd, ap, some v
      simp only [firstDq]
      iframe
      iframe #
      ipureintro; exact Hok
    imodintro
    iapply HK
    iexact Hsf

/-- A lower bound is at most the counter. -/
theorem auth_lb_le (γ : GName) (a n : Nat) :
    monoNatAuthOwn (GF := GF) γ 1 a ∗ monoNatLbOwn γ n ⊢
      ⌜n ≤ a⌝ ∗ (monoNatAuthOwn γ 1 a ∗ monoNatLbOwn γ n) := by
  apply persistent_entails_right
  iintro ⟨Ha, Hn⟩
  ihave %h := monoNatLbOwn_valid γ 1 a n $$ Ha Hn
  ipureintro
  exact h.2

/-- **What a reader with a lower bound `n` learns** (as `readFacts`, and the view's version at
least `n`). -/
def readFactsLb (γa : ApiNames) (r : Res) (γi : InfNames) (σs : cache.St) (n : Nat) : IProp GF :=
  iprop(∃ (σp : apimodel.St) (v : View) (R : Reg), pastSt γa σp ∗
    ([∗map] x ↦ o ∈ R, x ↪[γi.reg]□ o) ∗ monoNatLbOwn γi.rvlb (rvNat v.rv) ∗
    ⌜storeRel R σs v ∧ v.ok (σp.tbl r).log ∧ n ≤ rvNat v.rv⌝)

/-- **A store reader's linearization point with a lower bound** `n` it holds: as `infInv_readAU`,
and the store's version at least `n` (e.g. the first list's, after `HasSynced`). -/
theorem infInv_readLbAU (γa : ApiNames) (r : Res) (γf : FifoNames) (γt : TsNames) (γi : InfNames)
    (n : Nat) (K : cache.St → IProp GF) :
    ⊢ infInv γa r γf γt γi -∗ infRvLb γi n -∗ (∀ σs, readFactsLb γa r γi σs n -∗ K σs) -∗
      |={⊤ \ ∅, ∅}=> ∃ σs, storeSt γt σs ∗ (storeSt γt σs ={∅, ⊤ \ ∅}=∗ K σs) := by
  iintro #Hinv #Hn HK
  iunfold infRvLb at Hn
  rw [Iris.Std.LawfulSet.diff_empty]
  iunfold infInv at Hinv
  iinv Hinv with >Hi Hclose
  iunfold infRes at Hi
  icases Hi with ⟨%σp, %s, %q, %σs, %R, %pd, %ap, %f, #Hp, Hreg, #Hsnap, #Hobjs, Hq, Hst, Hsw, Hlast,
    Hpop, Hlb, Hfst, %Hok⟩
  ihave ⟨%hn, Hlb, -⟩ := auth_lb_le γi.rvlb (rvNat s.store.rv) n $$ [$Hlb $Hn]
  ihave #Hlb' := monoNatLbOwn_get γi.rvlb 1 (rvNat s.store.rv) $$ Hlb
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ \ ↑infN from Std.LawfulSet.empty_subset)
  iintro Hclose2
  iexists σs
  iframe Hst
  iintro Hst
  imod Hclose2 with -
  imod Hclose $$ [Hreg Hq Hst Hsw Hlast Hpop Hlb Hfst] with -
  · inext
    unfold infRes
    iexists σp, s, q, σs, R, pd, ap, f
    iframe
    iframe #
    ipureintro; exact Hok
  imodintro
  iapply HK
  unfold readFactsLb
  iexists σp, s.store, R
  iframe #
  ipureintro
  exact ⟨Hok.2.2.2.2.1, Hok.1.1, hn⟩

end glue

end informer
end EtcdGrove
end Perennial

/-
**Freezing the writer around a backend snapshot** (stage 2, M2, 2026-11-05; round 16's F2,
`notes/mvcc-api-invariants.md` §2). Lean-first (no Rocq counterpart).

`mvccImage_snapshot.law`'s code is the backend's `Snapshot()` call alone, so no step gives a later
credit before or after it: the freeze and the thaw open the writer's invariant without one
(`writerInv_freezeNL`, `writerInv_thawNL`), the taken writer's state staying under the later but
for its timeless parts the observation and the client's update need (`writerL_split`: the
writer's view of the log `γ.wv`, the API's writer slot `slotY`, the certificate).

* `snapFrozen s γ σ b`: what the freezer holds through the call: its half of the frozen flag, and
  the writer's state at the client's state `σ` (`b`: checked in, its log `σ.log`) or the open
  writer's key (`¬ b`: a write transaction open, which cannot end while frozen).
* `snapObs_M1` (**placeholder, `M1-REPLACE`**): the frozen store's part of the snapshot's
  observation, at a commit of the batch lock: the physical `Key` bucket is the entries cut at
  `σ.crev` and the compaction keys the store's records (`snapObsOk`). Not provable today: the
  store does not track its compaction job's deletes and records against the backend's
  (`notes/mvcc-api-invariants.md`, "Hand-off: stage 2, the snapshot image").
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.Instance
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.SnapImage

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

/-! ## The observation's facts (pure) -/

section pure
variable [GooseExts]

/-- **What the frozen store's observation of a commit gives** at the client's state's log `L` and
compaction revision `c`: the physical view `vd`'s `Key` bucket is the entries `ents` cut at `c`
and the compaction keys' values `v` the records `rc`, of `L`, past `0`, restoring to `c`. -/
def snapObsOk (L : Log) (c : Int) (vd : backend.VData) (v : backend.FkVals) : Prop :=
  ∃ (rc : CmpRecs) (ents : List KvEnt),
    (∀ k, vd.lookup (keyName, k) = (bucketOfEnts ents).lookup k) ∧
    v = (recBytes rc.fin, recBytes rc.sched) ∧ recsOk L rc ∧ recsPos rc ∧ entsCutAt L c ents ∧
    rc.crev = c

end pure

section frozen
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

instance curAt_timeless (γ : StoreNames) (dq : DFrac) (o : StoreObjs) :
    Timeless (curAt (GF := GF) γ dq o) := by
  unfold curAt; infer_instance
instance slotFl_timeless (γ : StoreNames) (q : Qp) (b : Bool) :
    Timeless (slotFl (GF := GF) γ q b) := by
  unfold slotFl; infer_instance
instance slotF_timeless (γ : StoreNames) : Timeless (slotF (GF := GF) γ) := by
  unfold slotF; infer_instance
instance slotFr_timeless (γ : StoreNames) : Timeless (slotFr (GF := GF) γ) := by
  unfold slotFr; infer_instance
instance slotY_timeless (γ : StoreNames) (L : Log) : Timeless (slotY (GF := GF) γ L) := by
  unfold slotY api.writerAbs api.absPart api.pndPart; infer_instance
instance writerKey_timeless (γ : StoreNames) : Timeless (writerKey (GF := GF) γ) := by
  unfold writerKey; infer_instance
instance wDep_timeless (γ : StoreNames) : Timeless (wDep (GF := GF) γ) := by
  unfold wDep; infer_instance

/-- **The image from the observation at the snapshot's data** (`vd := sData P D`,
`v := fkVals D`), at a reachable state's certified log. -/
theorem imageOk_of_snapObsOk (σ : api.MvccState) (hr : api.MvccReachable σ) (hb : LogB σ.log)
    (P : backend.BParams) (hhb : P.HB keyName = false) (D : backend.Data)
    (h : snapObsOk σ.log σ.crev (backend.sData P D) (backend.fkVals D)) :
    ∃ u : Bool, snap.imageOk D σ.log σ.crev u := by
  obtain ⟨rc, ents, hk, hv, hrec, hpos, hcut, hrc⟩ := h
  obtain ⟨R, hR, hne⟩ := snap.reach_shape σ hr
  have hwf := (api.reach_logWf σ hr).1
  have hkey : ∀ k, backend.dget D keyName k = (bucketOfEnts ents).lookup k := by
    intro k
    rw [← hk k, backend.sData_lookup]
    simp only [hhb, Bool.false_eq_true, ↓reduceIte]
  have hfin : backend.dget D go_etcd_io.etcd.server.v3.storage.schema.metaName finKeyBytes =
      recBytes rc.fin := congrArg Prod.fst hv
  have hsch : backend.dget D go_etcd_io.etcd.server.v3.storage.schema.metaName schedKeyBytes =
      recBytes rc.sched := congrArg Prod.snd hv
  rw [hR] at hb hwf hrec hcut ⊢
  exact ⟨rc.resumes, rc, ents, hkey, hfin, hsch, hrec, hpos, hcut, hrc, rfl,
    restoreCur_cut' R hne hb rc hrec ents (hrc ▸ hcut), hb, hwf, R, rfl, hne⟩

/-- The writer's state but its view of the log, its slot and its certificate, at the log `L`. -/
def writerLR (s : Loc) (γ : StoreNames) (L : Log) : IProp GF :=
  iprop(∃ ntok : Nat,
    ownTokAuthDfrac γ.revs (DFrac.own (1 : Qp).half) ntok ∗ ⌜L.length + ntok + 3 ≤ 2 ^ 63⌝ ∗
    idxWriter γ.idx L [] ∗ ghostVar γ.clog (1 : Qp).half L ∗
    (s.[store, go!"currentRev"] ↦{DFrac.own (1 : Qp).half} (W64 ((L.length : Int) - 1) : w64) :
      IProp GF) ∗
    ⌜L ≠ []⌝ ∗ lease.lessorRdOf γ.leases)

/-- **The writer's state, split** at its log: the view of the log, the API's slot and the
certificate (timeless: the freezer holds them out of the later), and the rest. -/
theorem writerL_split (s : Loc) (γ : StoreNames) :
    writerL (GF := GF) s γ ⊣⊢
      ∃ L : Log, ghostVar γ.wv (1 : Qp).half L ∗ slotY γ L ∗ idxCert γ.idx L ∗ writerLR s γ L := by
  unfold writerL writerLR
  simp only [named]
  constructor
  · iintro ⟨%L, %n, Ht, %Hb, Hw, Hcl, Hwv, Hcur, #Hc, %Hne, Hl, HY⟩
    iexists L
    iframe Hwv HY Hc
    iexists n
    iframe
    ipureintro; exact ⟨Hb, Hne⟩
  · iintro ⟨%L, Hwv, HY, #Hc, %n, Ht, %Hb, Hw, Hcl, Hcur, %Hne, Hl⟩
    iexists L, n
    iframe
    iframe #
    ipureintro; exact ⟨Hb, Hne⟩

/-- **What the freezer holds through the snapshot** (see the file header). -/
def snapFrozen (s : Loc) (γ : StoreNames) (σ : api.MvccState) (b : Bool) : IProp GF :=
  iprop(ghostVar γ.api.frz (1 : Qp).half true ∗
    if b then ghostVar γ.wv (1 : Qp).half σ.log ∗ slotY γ σ.log ∗ idxCert γ.idx σ.log ∗
        ▷ writerLR s γ σ.log ∗ ▷ writerReg s γ
    else ▷ (writerKey γ ∗ wDep γ ∗ storeRegd s γ))

/-- **Freezing the writer without a later credit** (`writerInv_freeze`'s, the taken state under
the later). -/
theorem writerInv_freezeNL (s : Loc) (γ : StoreNames) (a : api.AbsNames) (h : γ.api = a)
    (dq : DFrac) (o : StoreObjs) :
    ⊢ writerInv (GF := GF) s γ -∗ api.shareTok a 1 -∗ curAt γ dq o ={⊤}=∗
      ▷ writerTaken s γ ∗ ghostVar a.frz (1 : Qp).half true ∗ curAt γ dq o := by
  have : Inhabited PhysNames := ⟨γ.phys⟩
  have : Inhabited StoreObjs := ⟨o⟩
  iintro #Hi HF Hpin
  iunfold writerInv at Hi
  imod inv_acc (E := ⊤) (N := writerN) (P := writerInvBody (GF := GF) s γ)
    (by exact CoPset.subseteq_top) $$ Hi with ⟨HP, Hclose⟩
  iunfold writerInvBody at HP
  icases HP with (⟨%p, %o', >Hc, HP⟩ | ⟨-, -, >HFr, -⟩)
  rotate_left 1
  · iexfalso
    icases (slotFr_some h).1 $$ HFr with HFr
    iapply api.shareTok_excl a 1 $$ [HFr HF]
    iframe HFr HF
  ihave %Hv := curAt_pin γ p _ _ o o' $$ [Hpin Hc]
  · iframe Hpin Hc
  obtain ⟨rfl, rfl⟩ := Hv
  rw [StoreNames.withPhys_self]
  icases HP with (⟨>Hfz, HT⟩ | ⟨-, >HF'⟩)
  · icases (slotFl_some h 1 false).1 $$ Hfz with Hfz
    imod ghostVar_update true a.frz false $$ Hfz with Hfz
    icases (ghostVar_split_half (GF := GF) a.frz 1 true).1 $$ Hfz with ⟨Hfz1, Hfz2⟩
    imod Hclose $$ [Hc HF Hfz1] with -
    · inext; iunfold writerInvBody; ileft; iexists γ.phys, o'; rw [StoreNames.withPhys_self]
      iframe Hc; iright
      isplitl [Hfz1]
      · iapply (slotFl_some h _ true).2; iexact Hfz1
      iapply (slotF_some h).2; iexact HF
    imodintro; iframe Hpin Hfz2; iunfold writerTaken; iexact HT
  · iexfalso
    icases (slotF_some h).1 $$ HF' with HF'
    iapply api.shareTok_excl a 1 $$ [HF' HF]
    iframe HF' HF

/-- **Thawing the writer without a later credit** (`writerInv_thaw`'s, the taken state given back
under the later). -/
theorem writerInv_thawNL (s : Loc) (γ : StoreNames) (a : api.AbsNames) (h : γ.api = a)
    (dq : DFrac) (o : StoreObjs) :
    ⊢ writerInv (GF := GF) s γ -∗ ▷ writerTaken s γ -∗ ghostVar a.frz (1 : Qp).half true -∗
      curAt γ dq o ={⊤}=∗ api.shareTok a 1 ∗ curAt γ dq o := by
  have : Inhabited PhysNames := ⟨γ.phys⟩
  have : Inhabited StoreObjs := ⟨o⟩
  iintro #Hi HT Hfz Hpin
  iunfold writerInv at Hi
  imod inv_acc (E := ⊤) (N := writerN) (P := writerInvBody (GF := GF) s γ)
    (by exact CoPset.subseteq_top) $$ Hi with ⟨HP, Hclose⟩
  iunfold writerInvBody at HP
  icases HP with (⟨%p, %o', >Hc, HP⟩ | ⟨-, -, -, >Hfz'⟩)
  rotate_left 1
  · icases (slotFl_some h 1 false).1 $$ Hfz' with Hfz'
    ihave %Hv := ghostVar_valid_2 a.frz false 1 true (1 : Qp).half $$ Hfz' Hfz
    exact absurd Hv.1 (Qp_one_add_not_le _)
  ihave %Hv := curAt_pin γ p _ _ o o' $$ [Hpin Hc]
  · iframe Hpin Hc
  obtain ⟨rfl, rfl⟩ := Hv
  rw [StoreNames.withPhys_self]
  icases HP with (⟨>Hfz', -⟩ | ⟨>Hfz', >HF⟩)
  · icases (slotFl_some h 1 false).1 $$ Hfz' with Hfz'
    ihave %Hv := ghostVar_valid_2 a.frz false 1 true (1 : Qp).half $$ Hfz' Hfz
    exact absurd Hv.1 (Qp_one_add_not_le _)
  icases (slotFl_some h _ true).1 $$ Hfz' with Hfz'
  icases (slotF_some h).1 $$ HF with HF
  icases ghostVar_join_halves a.frz true true $$ [Hfz' Hfz] with ⟨Hfz, -⟩
  · iframe Hfz' Hfz
  imod ghostVar_update false a.frz true $$ Hfz with Hfz
  imod Hclose $$ [Hc HT Hfz] with -
  · inext; iunfold writerInvBody; ileft; iexists γ.phys, o'; rw [StoreNames.withPhys_self]
    iframe Hc; ileft
    isplitl [Hfz]
    · iapply (slotFl_some h 1 false).2; iexact Hfz
    iunfold writerTaken at HT; iexact HT
  imodintro; iframe HF Hpin

/-- **(Placeholder, false today.)** The frozen store's part of a snapshot's observation (see the
file header): at a commit of the batch lock (its client resource `mvccW d.gx`, the batch lock's
quarter of the readers' view `viewAtD`, its halves of the deleted entries and of the compaction
keys' values), the physical `Key` bucket and the compaction keys are the image of the client's
state `σ`, the writer checked in (`b`; an open write transaction holds the batch lock, so no commit
observes it). M1-REPLACE: mvccImage_snapshot.law's store-side tracking (mvcc's halves of `fkdOwn`
and `dlsOwn` in `compactRes`, agreeing with the records and the jobs' deletes; the records' revision
tied to the writer's; the pending registration). -/
theorem snapObs_M1 (s : Loc) (γ : StoreNames) (d : KBReal) (hk : γ.kb = some d) (hc : d.cm = true)
    (σ : api.MvccState) (hr : api.MvccReachable σ) (b : Bool) (vd X : backend.VData)
    (v : backend.FkVals) :
    snapFrozen (GF := GF) s γ σ b ∗ api.mvccW d.gx ∗ backend.viewAtD d.γB d.P vd X ∗
      backend.dlsOwn d.γB X ∗ backend.fkdOwn d.γB v ⊢ ⌜b = true ∧ snapObsOk σ.log σ.crev vd v⌝ := by
  sorry -- M1-REPLACE: mvccImage_snapshot.law (the store's compaction tracking)

end frozen

end mvcc
end EtcdGrove
end Perennial

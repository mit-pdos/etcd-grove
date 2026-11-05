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
* `writerInv_freezeR`/`reg_unlend` (the snapshot image's (d), 2026-11-05): the registration's
  invariant opened with the writer's: a pending registration's writer's resource lent to the
  freezer (`regLent`), so that an unregistered lock resource at a commit still has it.
* `snapObs` (in place of the placeholder `snapObs_M1`, 2026-11-05): the frozen store's part of the
  snapshot's observation, at a commit of the batch lock: the batch lock's writer's resource (the
  registered one, or the lent one) pins the tracked compaction (`compactRes`'s `cmpTrack`), whose
  values' halves, deleted entries and records' compaction revision agree with the lock's halves and
  the freezer's slot, so the physical `Key` bucket is the entries cut at `σ.crev` and the compaction
  keys the store's records (`snapObsOk`); an open write transaction is excluded by its key.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
import all Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
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
  unfold slotY api.absPart api.pndPart rcvW; split <;> (try split) <;> infer_instance
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

/-- **The freezer's quarter of the right to register** (the snapshot image's (d)): the real
backend's lock resource unregistered while the freezer holds the pending registration's writer's
resource (`regLent` keeps the other quarter in the registration's invariant). -/
def regTaken (γ : StoreNames) : IProp GF :=
  match γ.kb with
  | none => iprop(False)
  | some d => dghostVar d.gx (DFrac.own (1 : Qp).half.half) (none : Option (Loc × StoreNames))

instance regTaken_timeless (γ : StoreNames) : Timeless (regTaken (GF := GF) γ) := by
  unfold regTaken; split <;> infer_instance

/-- **What the freezer holds through the snapshot** (see the file header), the registration's
invariant `writerReg s' γ` being the one `mvccBackend` records: checked in (`b`), the writer's view
of the log, its slot at the client's state `σ` (its quarter of the view, its part of the pending
revision, its half of the records' compaction revision), the certificate, the rest of the writer's
state under the later, a quarter of the frozen flag, and the registration: done (with another
quarter of the flag), or pending and lent (the freezer's quarter of the right to register and the
batch lock's writer's resource, `regLent` the rest); or (a write transaction open) half the flag
and the open writer's key, its part of the deposit ghost and the registration. -/
def snapFrozen (s s' : Loc) (γ : StoreNames) (σ : api.MvccState) (b : Bool) : IProp GF :=
  if b then iprop(ghostVar γ.wv (1 : Qp).half σ.log ∗ api.absPart γ.api (1 : Qp).half.half σ.log σ.crev ∗
      api.pndPart γ.api (pndW γ) none ∗ rcvW γ (1 : Qp).half σ.crev ∗ idxCert γ.idx σ.log ∗
      ▷ writerLR s γ σ.log ∗ ▷ writerReg s γ ∗ ghostVar γ.api.frz (1 : Qp).half.half true ∗
      (storeRegd s' γ ∗ ghostVar γ.api.frz (1 : Qp).half.half true ∨ regTaken γ ∗ writerRes s' γ))
  else iprop(ghostVar γ.api.frz (1 : Qp).half true ∗ writerKey γ ∗ wDep γ ∗ storeRegd s γ)

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

section realKb
variable (γ : StoreNames) (d : KBReal) (hk : γ.kb = some d)
include hk

theorem regLent_some : regLent (GF := GF) γ ⊣⊢
    dghostVar d.gx (DFrac.own (1 : Qp).half.half) (none : Option (Loc × StoreNames)) ∗
      ghostVar γ.api.frz (1 : Qp).half.half true := by
  unfold regLent; rw [hk]; exact .rfl
theorem regTaken_some : regTaken (GF := GF) γ ⊣⊢
    dghostVar d.gx (DFrac.own (1 : Qp).half.half) (none : Option (Loc × StoreNames)) := by
  unfold regTaken; rw [hk]; exact .rfl
theorem storeRegd_some (s : Loc) : storeRegd (GF := GF) s γ ⊣⊢
    dghostVar d.gx DFrac.discard (some (s, γ)) := by
  unfold storeRegd; rw [hk]; exact .rfl
theorem bucketView_some (q : Qp) (m : Bucket) : bucketView (GF := GF) γ q m ⊣⊢
    bkView d.γB q m := by
  unfold bucketView kbView; rw [hk]; exact .rfl
theorem cmpTrack_some (hc : d.cm = true) (L : Log) (m : Bucket) (rc : CmpRecs) :
    cmpTrack (GF := GF) γ L m rc ⊣⊢
      backend.fkdOwn d.γB (recBytes rc.fin, recBytes rc.sched) ∗
        ghostVar γ.rcv (1 : Qp).half rc.crev ∗ monoNatAuthOwn γ.rcl 1 (crevN rc.crev) ∗
        ∃ (X : backend.VData) (jc : Int × Rev), backend.dlsOwn d.γB X ∗
          ghostVar γ.jc (1 : Qp).half jc ∗ ⌜snap.cmpOk L m X rc jc⌝ := by
  unfold cmpTrack; rw [hk]; simp only [hc, ↓reduceIte]; exact .rfl
theorem rcvW_some (hc : d.cm = true) (q : Qp) (c : Int) :
    rcvW (GF := GF) γ q c ⊣⊢ ghostVar γ.rcv q c := by
  unfold rcvW; rw [hk]; simp only [hc, ↓reduceIte]; exact .rfl

end realKb

/-- The pending registration's right, in quarters (the real backend's). -/
theorem kbRegRight_quarters (γ : StoreNames) (d : KBReal) (hk : γ.kb = some d) :
    kbRegRight (GF := GF) γ.kb ⊣⊢
      dghostVar d.gx (DFrac.own (1 : Qp).half.half) (none : Option (Loc × StoreNames)) ∗
      dghostVar d.gx (DFrac.own (1 : Qp).half.half) (none : Option (Loc × StoreNames)) := by
  have hf := (dghostVar_fractional (GF := GF) d.gx (none : Option (Loc × StoreNames))).fractional
    (1 : Qp).half.half (1 : Qp).half.half
  rw [Qp.half_add_half] at hf
  unfold kbRegRight lateReg
  rw [hk]
  exact hf

/-- **Freezing the writer, the registration lent** (the snapshot image's (d), 2026-11-05;
`writerInv_freezeNL`'s, with the registration's invariant `writerReg s' γ` opened while the writer's
is: lent already is excluded by the unfrozen flag). The checked-in state's registration, done or
pending: pending, its writer's resource taken out with a quarter of the right to register, the
invariant left lent (`regLent`). No later credit. -/
theorem writerInv_freezeR (s s' : Loc) (γ : StoreNames) (a : api.AbsNames) (h : γ.api = a)
    (d : KBReal) (hk : γ.kb = some d) (dq : DFrac) (o : StoreObjs) :
    ⊢ writerInv (GF := GF) s γ -∗ writerReg s' γ -∗ api.shareTok a 1 -∗ curAt γ dq o ={⊤}=∗
      curAt γ dq o ∗
      ((▷ (writerL s γ ∗ writerReg s γ) ∗ ghostVar a.frz (1 : Qp).half.half true ∗
          (storeRegd s' γ ∗ ghostVar a.frz (1 : Qp).half.half true ∨ regTaken γ ∗ writerRes s' γ)) ∨
        ghostVar a.frz (1 : Qp).half true ∗ ▷ (writerKey γ ∗ wDep γ ∗ storeRegd s γ)) := by
  have : Inhabited PhysNames := ⟨γ.phys⟩
  have : Inhabited StoreObjs := ⟨o⟩
  iintro #Hi #Hrg HF Hpin
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
  rotate_left 1
  · iexfalso
    icases (slotF_some h).1 $$ HF' with HF'
    iapply api.shareTok_excl a 1 $$ [HF' HF]
    iframe HF' HF
  icases (slotFl_some h 1 false).1 $$ Hfz with Hfz
  icases HT with (HT | HK)
  rotate_left 1
  · -- a write transaction open: as `writerInv_freezeNL`
    imod ghostVar_update true a.frz false $$ Hfz with Hfz
    icases (ghostVar_split_half (GF := GF) a.frz 1 true).1 $$ Hfz with ⟨Hfz1, Hfz2⟩
    imod Hclose $$ [Hc HF Hfz1] with -
    · inext; iunfold writerInvBody; ileft; iexists γ.phys, o'; rw [StoreNames.withPhys_self]
      iframe Hc; iright
      isplitl [Hfz1]
      · iapply (slotFl_some h _ true).2; iexact Hfz1
      iapply (slotF_some h).2; iexact HF
    imodintro; iframe Hpin; iright; iframe Hfz2 HK
  -- checked in: the registration's invariant, while the flag is down
  iunfold writerReg at Hrg
  imod inv_acc (E := ⊤ \ ↑writerN) (N := regN) (P := iprop(storeRegd (GF := GF) s' γ ∨
    kbRegRight γ.kb ∗ writerRes s' γ ∨ regLent γ)) (by solve_ndisj) $$ Hrg with ⟨HR, HRclose⟩
  ihave HR : ◇ iprop(storeRegd (GF := GF) s' γ ∨ kbRegRight γ.kb ∗ writerRes s' γ ∨ regLent γ) $$ [HR]
  · iapply Timeless.timeless; iexact HR
  imod HR with HR
  imod ghostVar_update true a.frz false $$ Hfz with Hfz
  icases (ghostVar_split_half (GF := GF) a.frz 1 true).1 $$ Hfz with ⟨Hfz1, Hfz2⟩
  icases (ghostVar_split_half (GF := GF) a.frz (1 : Qp).half true).1 $$ Hfz2 with ⟨Hfz2, Hfz3⟩
  icases HR with (#Hreg | ⟨Hrr, HWr⟩ | Hl)
  · imod HRclose $$ [] with -
    · inext; ileft; iexact Hreg
    imod Hclose $$ [Hc HF Hfz1] with -
    · inext; iunfold writerInvBody; ileft; iexists γ.phys, o'; rw [StoreNames.withPhys_self]
      iframe Hc; iright
      isplitl [Hfz1]
      · iapply (slotFl_some h _ true).2; iexact Hfz1
      iapply (slotF_some h).2; iexact HF
    imodintro; iframe Hpin; ileft; iframe HT Hfz2; ileft; iframe Hreg Hfz3
  · icases (kbRegRight_quarters γ d hk).1 $$ Hrr with ⟨Hr1, Hr2⟩
    imod HRclose $$ [Hr1 Hfz3] with -
    · inext; iright; iright; iapply (regLent_some γ d hk).2; rw [h]; iframe Hr1 Hfz3
    imod Hclose $$ [Hc HF Hfz1] with -
    · inext; iunfold writerInvBody; ileft; iexists γ.phys, o'; rw [StoreNames.withPhys_self]
      iframe Hc; iright
      isplitl [Hfz1]
      · iapply (slotFl_some h _ true).2; iexact Hfz1
      iapply (slotF_some h).2; iexact HF
    imodintro; iframe Hpin; ileft; iframe HT Hfz2; iright; iframe HWr
    iapply (regTaken_some γ d hk).2; iexact Hr2
  · iexfalso
    icases (regLent_some γ d hk).1 $$ Hl with ⟨-, Hl⟩
    rw [h]
    ihave %Hv := ghostVar_valid_2 a.frz true 1 true _ $$ [Hfz1 Hfz2 Hfz3] Hl
    · iapply (ghostVar_split_half (GF := GF) a.frz 1 true).2; iframe Hfz1
      iapply (ghostVar_split_half (GF := GF) a.frz (1 : Qp).half true).2; iframe Hfz2 Hfz3
    exact absurd Hv.1 (Qp_one_add_not_le _)

/-- **The lent registration given back** (the thaw's first step): the freezer's quarter of the
right to register and the writer's resource it took make the registration pending again, the
invariant's quarter of the frozen flag back to the freezer. -/
theorem reg_unlend (s' : Loc) (γ : StoreNames) (d : KBReal) (hk : γ.kb = some d) (E : CoPset)
    (hE : ↑regN ⊆ E) :
    writerReg (GF := GF) s' γ ⊢ regTaken γ ∗ writerRes s' γ ={E}=∗
      ghostVar γ.api.frz (1 : Qp).half.half true := by
  iintro #Hrg ⟨Ht, HW⟩
  iunfold writerReg at Hrg
  imod inv_acc (E := E) (N := regN) (P := iprop(storeRegd (GF := GF) s' γ ∨
    kbRegRight γ.kb ∗ writerRes s' γ ∨ regLent γ)) hE $$ Hrg with ⟨HR, HRclose⟩
  ihave HR : ◇ iprop(storeRegd (GF := GF) s' γ ∨ kbRegRight γ.kb ∗ writerRes s' γ ∨ regLent γ) $$ [HR]
  · iapply Timeless.timeless; iexact HR
  imod HR with HR
  ihave Ht := (regTaken_some γ d hk).1 $$ Ht
  icases HR with (#Hreg | ⟨-, HW'⟩ | Hl)
  · iexfalso
    ihave #Hreg := (storeRegd_some γ d hk s').1 $$ Hreg
    ihave %Hc := dghostVar_agree d.gx _ _ _ _ $$ Hreg Ht
    cases Hc
  · iexfalso
    iunfold writerRes at HW HW'
    icases HW with ⟨%L, Hk, -⟩
    icases HW' with ⟨%L', Hk', -⟩
    iunfold writerKey at Hk Hk'
    ihave %Hv := ghostVar_valid_2 γ.wk () 1 () 1 $$ Hk Hk'
    exact absurd Hv.1 (Qp_one_add_not_le 1)
  · icases (regLent_some γ d hk).1 $$ Hl with ⟨Hr, Hfz⟩
    imod HRclose $$ [Hr Ht HW] with -
    · inext; iright; ileft; iframe HW
      iapply (kbRegRight_quarters γ d hk).2; iframe Hr Ht
    imodintro; iexact Hfz

/-- **The physical `Key` bucket of a snapshot's observation is the cut's** (pure): the physical
view `vd` thin of the logical one `Lv`, `Lv` the store's view `m` on the `Key` bucket, the deleted
entries `X` exactly the missing ones (`dlVd`), and `m` but `X` the entries `ents`. -/
theorem vd_of_cut (P : backend.BParams) (hsb : P.SB keyName = true) (hhb : P.HB keyName = false)
    (vd Lv X : backend.VData) (m : Bucket) (ents : List KvEnt)
    (hLv : ∀ k, Lv.lookup (keyName, k) = m.lookup k)
    (hsub : ∀ nk v, vd.lookup nk = some v → Lv.lookup nk = some v)
    (hdl : backend.dlVd P vd Lv X)
    (hcut : ∀ k, snap.physLookup m X k = (bucketOfEnts ents).lookup k) :
    ∀ k, vd.lookup (keyName, k) = (bucketOfEnts ents).lookup k := by
  intro k
  rw [← hcut k]
  unfold snap.physLookup
  cases hx : X.lookup (keyName, k) with
  | some x =>
    have hxn : X.lookup (keyName, k) ≠ none := by rw [hx]; simp
    simp only [Option.isSome_some, ↓reduceIte]
    exact (hdl.2 _ hxn).2.2.1
  | none =>
    simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    cases hm : m.lookup k with
    | none =>
      cases hw : vd.lookup (keyName, k) with
      | none => rfl
      | some w => have := hsub _ w hw; rw [hLv, hm] at this; cases this
    | some v =>
      have hLn : Lv.lookup (keyName, k) ≠ none := by rw [hLv, hm]; simp
      cases hw : vd.lookup (keyName, k) with
      | none => exact absurd hx (hdl.1 _ hsb hhb hLn hw)
      | some w =>
        have := hsub _ w hw
        rw [hLv, hm] at this
        exact this.symm ▸ rfl

/-- **The batch lock's writer's resource gives the observation** (at a commit, the freezer's view
of the log `L = σ.log` and its half of the records' compaction revision at `σ.crev`): the batch
lock's halves of the compaction keys' values and the deleted entries agree with the tracked
compaction's, its eighth of the bucket's view with the quarter of the readers' view. -/
theorem snapObs_writerRes (s' : Loc) (γ : StoreNames) (d : KBReal) (hk : γ.kb = some d)
    (hc : d.cm = true) (L : Log) (c : Int) (vd X : backend.VData) (v : backend.FkVals) :
    writerRes (GF := GF) s' γ ∗ ghostVar γ.wv (1 : Qp).half L ∗ rcvW γ (1 : Qp).half c ∗
      backend.viewAtD d.γB d.P vd X ∗ backend.dlsOwn d.γB X ∗ backend.fkdOwn d.γB v ⊢
      ⌜snapObsOk L c vd v⌝ := by
  iintro ⟨HW, Hwv, Hrc, Hva, Hdl, Hfk⟩
  iunfold writerRes at HW
  icases HW with ⟨%L', -, Hwv', -, -, -, Hcres⟩
  ihave %HL := ghostVar_agree γ.wv _ _ _ _ $$ Hwv Hwv'
  subst HL
  iunfold compactRes at Hcres
  icases Hcres with ⟨%sched, %fin, %n, %m, -, -, -, -, Hbv, Htr⟩
  icases (cmpTrack_some γ d hk hc L m _).1 $$ Htr with ⟨Hfk', Hrc', -, %X', %jc, Hdl', -, %Hok⟩
  ihave Hrc := (rcvW_some γ d hk hc _ c).1 $$ Hrc
  iunfold backend.fkdOwn at Hfk Hfk'
  iunfold backend.dlsOwn at Hdl Hdl'
  ihave %Hv := ghostVar_agree d.γB.fkd _ _ _ _ $$ Hfk Hfk'
  ihave %HX := ghostVar_agree d.γB.dls _ _ _ _ $$ Hdl Hdl'
  ihave %Hcr := ghostVar_agree γ.rcv _ _ _ _ $$ Hrc Hrc'
  subst HX
  ihave Hbv := (bucketView_some γ d hk _ m).1 $$ Hbv
  iunfold bkView at Hbv
  icases Hbv with ⟨%vd', Hbv, %Hkv⟩
  iunfold backend.viewAtD at Hva
  icases Hva with ⟨%Lv, Hq, %Hdlv⟩
  iunfold backend.viewQ at Hq
  icases Hq with ⟨Hq, #Hthin⟩
  iunfold backend.bView at Hbv
  iunfold backend.bViewC at Hbv
  icases Hbv with ⟨%cc, Hbv, -, -⟩
  ihave %HLv := ghostVar_agree d.γB.view _ _ _ _ $$ Hq Hbv
  subst HLv
  iunfold backend.thinV at Hthin
  icases Hthin with ⟨%Hsub, -⟩
  ipureintro
  obtain ⟨ents, hcut, hB, hrec, hpos, -, -⟩ := Hok
  refine ⟨⟨fin, sched⟩, ents, ?_, Hv, hrec, hpos, Hcr ▸ hcut, Hcr.symm⟩
  refine vd_of_cut d.P (by simp [KBReal.P]) (by simp [KBReal.P]) vd Lv X m ents ?_ Hsub Hdlv hB
  intro k; rw [Hkv keyName k]; simp

/-- **The frozen store's part of a snapshot's observation** (the snapshot image's (a)-(e),
2026-11-05; in place of the placeholder `snapObs_M1`): at a commit of the batch lock (its client
resource `mvccW d.gx`, the batch lock's quarter of the readers' view `viewAtD`, its halves of the
deleted entries and of the compaction keys' values), the physical `Key` bucket and the compaction
keys are the image of the client's state `σ`. The lock's resource is the store's writer's resource
(registered, `storeRegd`), or unregistered while the freezer holds the pending registration's; an
open write transaction (`¬ b`) cannot be at a commit (its key, the freezer's, is the writer's
resource's). -/
theorem snapObs (s s' : Loc) (γ : StoreNames) (d : KBReal) (hk : γ.kb = some d) (hc : d.cm = true)
    (σ : api.MvccState) (b : Bool) (vd X : backend.VData) (v : backend.FkVals) :
    snapFrozen (GF := GF) s s' γ σ b ∗ api.mvccW d.gx ∗ backend.viewAtD d.γB d.P vd X ∗
      backend.dlsOwn d.γB X ∗ backend.fkdOwn d.γB v ⊢ ⌜b = true ∧ snapObsOk σ.log σ.crev vd v⌝ := by
  iintro ⟨HFR, HW, Hva, Hdl, Hfk⟩
  unfold api.mvccW lateW
  iunfold snapFrozen at HFR
  cases b with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    iexfalso
    icases HFR with ⟨-, Hk, -, #Hreg⟩
    ihave #Hreg := (storeRegd_some γ d hk s).1 $$ Hreg
    icases HW with (Hu | ⟨%s'', %γ'', #Hr, HWr⟩)
    · ihave %Hc := dghostVar_agree d.gx _ _ _ _ $$ Hreg Hu
      cases Hc
    · ihave %Hc := dghostVar_agree d.gx _ _ _ _ $$ Hreg Hr
      cases Hc
      iunfold writerRes at HWr
      icases HWr with ⟨%L, Hk', -⟩
      iunfold writerKey at Hk Hk'
      ihave %Hv := ghostVar_valid_2 γ.wk () 1 () 1 $$ Hk Hk'
      exact absurd Hv.1 (Qp_one_add_not_le 1)
  | true =>
    simp only [↓reduceIte]
    icases HFR with ⟨Hwv, -, -, Hrc, -, -, -, -, HRg⟩
    ihave %H : ⌜snapObsOk σ.log σ.crev vd v⌝ $$ [HRg HW Hwv Hrc Hva Hdl Hfk]
    · icases HRg with (⟨#Hreg, -⟩ | ⟨Ht, HWr⟩)
      · ihave #Hreg := (storeRegd_some γ d hk s').1 $$ Hreg
        icases HW with (Hu | ⟨%s'', %γ'', #Hr, HWr⟩)
        · iexfalso
          ihave %Hc := dghostVar_agree d.gx _ _ _ _ $$ Hreg Hu
          cases Hc
        · ihave %Hc := dghostVar_agree d.gx _ _ _ _ $$ Hreg Hr
          cases Hc
          iapply snapObs_writerRes s' γ d hk hc σ.log σ.crev vd X v
          iframe HWr Hwv Hrc Hva Hdl Hfk
      · ihave Ht := (regTaken_some γ d hk).1 $$ Ht
        icases HW with (Hu | ⟨%s'', %γ'', #Hr, -⟩)
        · iapply snapObs_writerRes s' γ d hk hc σ.log σ.crev vd X v
          iframe HWr Hwv Hrc Hva Hdl Hfk
        · iexfalso
          ihave %Hc := dghostVar_agree d.gx _ _ _ _ $$ Hr Ht
          cases Hc
    ipureintro; exact ⟨by simp, H⟩

end frozen

end mvcc
end EtcdGrove
end Perennial

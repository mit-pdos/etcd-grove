/-
Lean-first (no Rocq counterpart).

# The restart's accounting (W4c U5, `restartRead`/`member.restart`)

What `restartRead` and `restart` need of the oracle, pure:

* **the pending opens**: `tWithOpens o l` is the oracle with the opens `l` appended (`restartRead` appends
  one per attempt, at most two); its encoding grows by 8 bytes per open (`tEncodeOracle_withOpens_length`),
  whatever their values, and an open appended keeps a candidate's accounting (`tCandOk_addOpen`);
* **the read is an image's** (`tRead_of_readAll`): `ReadAll`'s success post gives an image of the
  candidate's history that reads the tester's `c` from the purged prefix 0 (`tRead img = some c`). Its
  premise `tReadsBackOk` is the weakest form of W4b's `walReadsBack` the proof uses: a history `ReadAll`
  reads successfully reads back. `walReadsBack` of every image of a tester history is false (a torn `Save`
  after `opRecvSnap`'s snapshot leaves its entries above a filtered-out snapshot record: `walRead` fails);
  there `ReadAll` fails too, so `tReadsBackOk` may still hold (the U5 log, eighth session);
* **the new oracle accounts for the WAL** (`tRestart_ok`): that image is among `checkRestart`'s next
  candidates (`tCheckNext_has`), with bounds at least the candidate's (`tRaiseUnl_ge`), so the oracle
  `tCheckRestart o c` accounts for the WAL as a running member's (`tMemOk`, `tMemHs`).
-/
module

public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.RestartPure
public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.OrLen
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.Inv

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI go_etcd_io.raft.v3 WalEnc Fs WalFs

section pure
variable [GooseExts]

/-- **The WAL's paths are the area's** (the premises the WAL's directory calls take: `Open`,
`ValidSnapshotEntries`, `Repair`): the WAL directory `wal` in the area, the area a clean absolute path,
the directory's name short. A world premise of the tester's area (U7). -/
def tWalPathsOk (area : GoString) : Prop :=
  InArea area (tWalDir area) go!"wal" ∧ NameOk go!"wal" ∧ cleanAbsPath area ∧
    (tWalDir area).length < 2 ^ 59

/-- **The file system does not fail on the WAL's name, its `.tmp` and the area, and the WAL directory
and its `.tmp` fit** (`wal.Create.spec`'s premise, ledgers 2026-11-21 and 2026-11-22: `Create`'s rename
then succeeds, and its `Exist`/`RemoveAll` of a leftover `.tmp` are exact). From the closed theorem's
semantics (`NoIoErr` of every path) and its world premise that the area's `wal` and `wal.tmp` paths fit. -/
def tWalFsOk [ExtSemantics fsExt] (area : GoString) : Prop :=
  FsNoErrOn (fun p => p = tWalDir area ∨ p = tWalDir area ++ go!".tmp" ∨ p = area) ∧
    PathFits (tWalDir area ++ go!".tmp") ∧ PathFits (tWalDir area)

/-! ## The pending opens -/

/-- The oracle with the opens `l` appended (`restartRead`'s stores). -/
def tWithOpens (o : TOracle) (l : List w64) : TOracle := { o with opens := o.opens ++ l }

theorem tWithOpens_nil (o : TOracle) : tWithOpens o [] = o := by
  cases o; simp [tWithOpens]

theorem tPre_withOpens {o : TOracle} (l : List w64) (h : tPre o) : tPre (tWithOpens o l) := by
  cases o; exact h

theorem tWithOpens_created (o : TOracle) (l : List w64) : (tWithOpens o l).created = o.created := rfl

/-- The WAL states before and after a restart's step, related by `P`, reflexively: none, or the same. -/
theorem tOdRel_refl {o : TOracle} {cd : TCand} {od : Option WalDur} (hok : ∀ d, od = some d → tCandOk o cd d) :
    Option.Rel (fun d d' => d'.H = d.H ∧ d'.cut = d.cut ∧ tCandOk o cd d') od od := by
  cases od with
  | none => exact Option.Rel.none
  | some d => exact Option.Rel.some ⟨rfl, rfl, hok d rfl⟩

theorem tWithOpens_add (o : TOracle) (l : List w64) (a : w64) :
    tAddOpen (tWithOpens o l) a = tWithOpens o (l ++ [a]) := by
  simp [tAddOpen, tWithOpens, List.append_assoc]

/-- **An open adds 8 bytes to the encoding**, whatever its value. -/
theorem tEncodeOracle_withOpens_length (o : TOracle) (l : List w64) :
    (tEncodeOracle (tWithOpens o l)).length = (tEncodeOracle o).length + 8 * l.length := by
  have hf : ∀ l : List w64, (l.flatMap tU64).length = 8 * l.length := by
    intro l; induction l with
    | nil => rfl
    | cons x l ih => simp only [List.flatMap_cons, List.length_append, tU64_length, ih, List.length_cons]; omega
  simp only [tEncodeOracle, tWithOpens, List.length_append, tU64_length, hf]
  omega

theorem tOrSmall_withOpens {o : TOracle} {l : List w64}
    (h : (tEncodeOracle o).length + 8 * l.length ≤ 0x40000000) : tOrSmall (tWithOpens o l) := by
  unfold tOrSmall; rw [tEncodeOracle_withOpens_length]; exact h

theorem tCandHist_withOpens (o : TOracle) (l : List w64) (c : TCand) :
    tCandHist (tWithOpens o l) c = tCandHist o c := rfl

theorem tCandMark_withOpens (o : TOracle) (l : List w64) (c : TCand) :
    tCandMark (tWithOpens o l) c = tCandMark o c := rfl

theorem tCheckWf_withOpens {o : TOracle} (l : List w64) (h : tCheckWf o) : tCheckWf (tWithOpens o l) := h

/-- An open appended keeps the accounting (the opens bound only grows). -/
theorem tCandOk_addOpen {o : TOracle} {c : TCand} {d : WalDur} (a : w64) (hc : tCandOk o c d) :
    tCandOk (tAddOpen o a) c d := by
  obtain ⟨himg, hpur, hcut, hunl, hsz, hwf⟩ := hc
  refine ⟨himg, hpur, hcut, ?_, hsz, hwf⟩
  exact Nat.le_trans hunl (Nat.max_le.2 ⟨Nat.le_max_left _ _,
    Nat.le_trans (tOpensBound_addOpen o a c).1 (Nat.le_max_right _ _)⟩)

/-- `Open`'s raise is idempotent: a second `Open` at the same snapshot leaves the state as it is. -/
theorem walOpenRaise_idem (d : WalDur) (a : w64) :
    let d1 : WalDur := { d with unl := max d.unl (walOpenPos (d.H.map WalOpG.toM) a) }
    ({ d1 with unl := max d1.unl (walOpenPos (d1.H.map WalOpG.toM) a) } : WalDur) = d1 := by
  intro d1
  cases d
  simp only [d1, WalDur.mk.injEq, and_true, true_and]
  omega

/-! ## The read is an image's -/

/-- **A history that `ReadAll` reads reads back** (the weakest form of W4b's `walReadsBack` the restart
uses; see the file header). -/
def tReadsBackOk (I : WalHist) : Prop :=
  ∀ cut s σ', walReadAllOk I cut s σ' → walReadsBack I

/-- **The WAL state a candidate accounts for reads back where `ReadAll` succeeds**: it is an image of
the candidate's history at its mark, which is disciplined (`tSim`, `ReadsBack.tSim_readsBack`). -/
theorem tCandOk_readsBack {o : TOracle} {c : TCand} {d : WalDur} (hc : tCandOk o c d) :
    tReadsBackOk (d.H.map WalOpG.toM) :=
  tSim_readsBack hc.2.2.2.2.2.2 hc.1

/-- **The restart's read is an image's** (`tCheckNext_of_read`'s core): the image `img` of the
candidate's history whose model is the WAL's reads `c` from the purged prefix 0. -/
theorem tRead_of_readAll {o : TOracle} {cd : TCand} {d : WalDur} {s : w64 × w64} {σ' : StorContents}
    {c : TContents} (hc : tCandOk o cd d)
    (hpost : walReadAllOk (d.H.map WalOpG.toM) d.cut s σ') (hb : walReadsBack (d.H.map WalOpG.toM))
    (hhs : absHs c.hs = σ'.hs) (hbi : c.baseIdx = s.1) (hbt : c.baseTerm = s.2)
    (hents : c.ents = σ'.ents.map tFromRaft) :
    ∃ img ∈ tImgs (tCandHist o cd) (tCandMark o cd), d.H.map WalOpG.toM = img.map absOp ∧
      tRead img = some c := by
  obtain ⟨himg, -, -, -, -, hwf⟩ := hc
  obtain ⟨img, himgm, hI⟩ := tImgs_complete himg
  refine ⟨img, himgm, hI, ?_⟩
  have hwi : tHistWf img := tHistWf_of_mem_tImgs hwf.1 himgm
  have hmax : ¬ walHasMaxIdx (d.H.map WalOpG.toM) := by rw [hI]; exact tHistWf_noMax hwi
  obtain ⟨σ0, h0, e1, e2, e3⟩ := walReadAllOk_read0 hpost hmax hb
  have hra := tRead_abs img
  rw [← hI, h0] at hra
  cases hr : tRead img with
  | none => rw [hr] at hra; cases hra
  | some c0 =>
    rw [hr] at hra
    simp only [Option.map_some, Option.some.injEq] at hra
    simp only [absC, projC, Prod.mk.injEq] at hra
    obtain ⟨r1, r2, r3, r4⟩ := hra
    have hw0 := tRead_ents_wf hwi hr
    cases c0; cases c
    simp only at r1 r2 r3 r4 hw0 hhs hbi hbt hents ⊢
    rw [e3] at r2 r3
    rw [Option.some.injEq, TContents.mk.injEq]
    refine ⟨absHs_inj (by rw [r1, e1, hhs]), ?_, ?_, ?_⟩
    · rw [r2, hbi]
    · rw [r3, hbt]
    · rw [hents, ← e2, ← r4, List.map_map]
      symm
      rw [List.map_congr_left (g := id) (fun e he => by
        simp only [Function.comp_apply, id]; exact tFromRaft_absEnt e (hw0 e he).1)]
      simp

/-! ## `checkRestart`'s next candidates -/

/-- `cs` holds a candidate of history `img` with bounds at least `u` and `p`. -/
def tHasCand (cs : List TCand) (img : List TOp) (u p : w64) : Prop :=
  ∃ c ∈ cs, c.h = img ∧ uint.nat u ≤ uint.nat c.unl ∧ uint.nat p ≤ uint.nat c.pur

theorem tAddCand_has (img : List TOp) (u p : w64) : ∀ cs : List TCand,
    tHasCand (tAddCand img u p cs) img u p := by
  intro cs
  induction cs with
  | nil => exact ⟨⟨img, u, p⟩, List.mem_singleton_self _, rfl, Nat.le_refl _, Nat.le_refl _⟩
  | cons c0 cs ih =>
    unfold tAddCand
    by_cases h0 : c0.h = img
    · rw [if_pos h0]
      refine ⟨_, List.mem_cons_self .., h0, ?_, ?_⟩
      · simp only; split <;> omega
      · simp only; split <;> omega
    · rw [if_neg h0]
      obtain ⟨c, hc, h1, h2, h3⟩ := ih
      exact ⟨c, List.mem_cons_of_mem _ hc, h1, h2, h3⟩

theorem tAddCand_keep (img : List TOp) (u p : w64) {img' : List TOp} {u' p' : w64} :
    ∀ cs : List TCand, tHasCand cs img' u' p' → tHasCand (tAddCand img u p cs) img' u' p' := by
  intro cs
  induction cs with
  | nil => intro ⟨_, h, _⟩; cases h
  | cons c0 cs ih =>
    intro ⟨c, hc, h1, h2, h3⟩
    unfold tAddCand
    by_cases h0 : c0.h = img
    · rw [if_pos h0]
      rcases List.mem_cons.1 hc with rfl | hc
      · refine ⟨_, List.mem_cons_self .., h1, ?_, ?_⟩
        · simp only; split <;> omega
        · simp only; split <;> omega
      · exact ⟨c, List.mem_cons_of_mem _ hc, h1, h2, h3⟩
    · rw [if_neg h0]
      rcases List.mem_cons.1 hc with rfl | hc
      · exact ⟨c, List.mem_cons_self .., h1, h2, h3⟩
      · obtain ⟨c', hc', h1', h2', h3'⟩ := ih ⟨c, hc, h1, h2, h3⟩
        exact ⟨c', List.mem_cons_of_mem _ hc', h1', h2', h3'⟩

theorem tCandNext_keep (o : TOracle) (c : TContents) (cd : TCand) {img' : List TOp} {u' p' : w64} :
    ∀ (imgs : List (List TOp)) (nx : List TCand), tHasCand nx img' u' p' →
      tHasCand (imgs.foldl (fun nx img => if tImgReads img cd.pur c then
        tAddCand img (tRaiseUnl (tImgs (tCandHist o cd) (tCandMark o cd)) o.opens cd.unl) cd.pur nx
        else nx) nx) img' u' p' := by
  intro imgs
  induction imgs with
  | nil => intro nx h; exact h
  | cons img imgs ih =>
    intro nx h
    simp only [List.foldl_cons]
    apply ih
    split
    · exact tAddCand_keep _ _ _ _ h
    · exact h

theorem tCandNext_has (o : TOracle) (c : TContents) (cd : TCand) {img : List TOp} :
    ∀ (imgs : List (List TOp)) (nx : List TCand), img ∈ imgs → tImgReads img cd.pur c = true →
      tHasCand (imgs.foldl (fun nx img => if tImgReads img cd.pur c then
        tAddCand img (tRaiseUnl (tImgs (tCandHist o cd) (tCandMark o cd)) o.opens cd.unl) cd.pur nx
        else nx) nx) img (tRaiseUnl (tImgs (tCandHist o cd) (tCandMark o cd)) o.opens cd.unl) cd.pur := by
  intro imgs
  induction imgs with
  | nil => intro nx h; cases h
  | cons i imgs ih =>
    intro nx hm hr
    simp only [List.foldl_cons]
    rcases List.mem_cons.1 hm with rfl | hm
    · apply tCandNext_keep
      rw [if_pos hr]; exact tAddCand_has _ _ _ _
    · exact ih _ hm hr

theorem tCheckNext_fold_keep (o : TOracle) (c : TContents) {img' : List TOp} {u' p' : w64} :
    ∀ (cs : List TCand) (nx : List TCand), tHasCand nx img' u' p' →
      tHasCand (cs.foldl (tCandNext o c) nx) img' u' p' := by
  intro cs
  induction cs with
  | nil => intro nx h; exact h
  | cons cd cs ih =>
    intro nx h
    simp only [List.foldl_cons]
    exact ih _ (tCandNext_keep o c cd _ _ h)

/-- **An image that reads `c` is among the next candidates**, with bounds at least its candidate's. -/
theorem tCheckNext_has {o : TOracle} {c : TContents} {cd : TCand} {img : List TOp}
    (hcd : cd ∈ o.cands) (himg : img ∈ tImgs (tCandHist o cd) (tCandMark o cd))
    (hr : tImgReads img cd.pur c = true) :
    tHasCand (tCheckNext o c) img (tRaiseUnl (tImgs (tCandHist o cd) (tCandMark o cd)) o.opens cd.unl)
      cd.pur := by
  unfold tCheckNext
  obtain ⟨l1, l2, hl⟩ := List.append_of_mem hcd
  rw [hl, List.foldl_append, List.foldl_cons]
  apply tCheckNext_fold_keep
  exact tCandNext_has o c cd _ _ himg hr

theorem tRaiseUnl_ge_u (imgs : List (List TOp)) : ∀ (opens : List w64) (u : w64),
    uint.nat u ≤ uint.nat (tRaiseUnl imgs opens u) := by
  intro opens
  induction opens with
  | nil => intro u; exact Nat.le_refl _
  | cons a l ih =>
    intro u
    unfold tRaiseUnl at ih ⊢
    simp only [List.foldl_cons]
    refine Nat.le_trans ?_ (ih _)
    split <;> omega

theorem tRaiseUnl_ge_fold (imgs : List (List TOp)) : ∀ (opens : List w64) (u : w64) (acc : Nat),
    acc ≤ uint.nat u →
    (opens.map (fun s => uint.nat (tOpenBound imgs s))).foldl max acc ≤ uint.nat (tRaiseUnl imgs opens u) := by
  intro opens
  induction opens with
  | nil => intro u acc h; exact h
  | cons a l ih =>
    intro u acc h
    unfold tRaiseUnl at ih ⊢
    simp only [List.map_cons, List.foldl_cons]
    apply ih
    split <;> omega

/-- **`checkRestart`'s unlock bound covers the accounting's**: the candidate's bound and the opens'. -/
theorem tRaiseUnl_ge (o : TOracle) (cd : TCand) :
    max (uint.nat cd.unl) (tOpensBound o cd) ≤
      uint.nat (tRaiseUnl (tImgs (tCandHist o cd) (tCandMark o cd)) o.opens cd.unl) :=
  Nat.max_le.2 ⟨tRaiseUnl_ge_u _ _ _, tRaiseUnl_ge_fold _ _ _ 0 (Nat.zero_le _)⟩


/-! ## The new oracle's candidates are images -/

/-- Every candidate of `cs` has a history among `imgsOf`. -/
def tCandsIn (P : List TOp → Prop) (cs : List TCand) : Prop := ∀ c ∈ cs, P c.h

theorem tAddCand_in {P : List TOp → Prop} (img : List TOp) (u p : w64) (himg : P img) :
    ∀ cs : List TCand, tCandsIn P cs → tCandsIn P (tAddCand img u p cs) := by
  intro cs
  induction cs with
  | nil => intro _ c hc; rw [List.mem_singleton.1 hc]; exact himg
  | cons c0 cs ih =>
    intro hcs
    unfold tAddCand
    split
    · intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · exact hcs c0 (List.mem_cons_self ..)
      · exact hcs c (List.mem_cons_of_mem _ hc)
    · intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · exact hcs _ (List.mem_cons_self ..)
      · exact ih (fun c' hc' => hcs c' (List.mem_cons_of_mem _ hc')) c hc

/-- An image of a candidate's history of `o`. -/
def tIsImg (o : TOracle) (h : List TOp) : Prop :=
  ∃ cd ∈ o.cands, h ∈ tImgs (tCandHist o cd) (tCandMark o cd)

theorem tCandNext_in (o : TOracle) (c : TContents) (cd : TCand) (hcd : cd ∈ o.cands) :
    ∀ (imgs : List (List TOp)) (nx : List TCand), (∀ i ∈ imgs, i ∈ tImgs (tCandHist o cd) (tCandMark o cd)) →
      tCandsIn (tIsImg o) nx →
      tCandsIn (tIsImg o) (imgs.foldl (fun nx img => if tImgReads img cd.pur c then
        tAddCand img (tRaiseUnl (tImgs (tCandHist o cd) (tCandMark o cd)) o.opens cd.unl) cd.pur nx
        else nx) nx) := by
  intro imgs
  induction imgs with
  | nil => intro nx _ h; exact h
  | cons i imgs ih =>
    intro nx hi h
    simp only [List.foldl_cons]
    apply ih _ (fun j hj => hi j (List.mem_cons_of_mem _ hj))
    split
    · exact tAddCand_in _ _ _ ⟨cd, hcd, hi i (List.mem_cons_self ..)⟩ _ h
    · exact h

/-- **`checkRestart`'s next candidates are images of the candidates' histories.** -/
theorem tCheckNext_imgs (o : TOracle) (c : TContents) : tCandsIn (tIsImg o) (tCheckNext o c) := by
  unfold tCheckNext
  suffices ∀ (cs : List TCand) (nx : List TCand), (∀ cd ∈ cs, cd ∈ o.cands) → tCandsIn (tIsImg o) nx →
      tCandsIn (tIsImg o) (cs.foldl (tCandNext o c) nx) from
    this _ _ (fun _ h => h) (fun _ h => by cases h)
  intro cs
  induction cs with
  | nil => intro nx _ h; exact h
  | cons cd cs ih =>
    intro nx hcs h
    simp only [List.foldl_cons]
    exact ih _ (fun x hx => hcs x (List.mem_cons_of_mem _ hx))
      (tCandNext_in o c cd (hcs cd (List.mem_cons_self ..)) _ _ (fun _ hi => hi) h)

/-- **The new oracle meets `checkRestart`'s premises again** (`tCheckWf`), within 1 GiB: its candidates
are images of well-formed histories, short by the size bound. -/
theorem tCheckWf_restart {o : TOracle} {c : TContents} (hw : tCheckWf o)
    (hs : tOrSmall (tCheckRestart o c)) : tCheckWf (tCheckRestart o c) := by
  refine ⟨Nat.zero_le _, fun c' hc' => ⟨?_, tOrSmall_hist_lt hs hc'⟩⟩
  obtain ⟨cd, hcd, hi⟩ := tCheckNext_imgs o c c' hc'
  show tHistWf (c'.h ++ [])
  rw [List.append_nil]
  exact tHistWf_of_mem_tImgs (hw.2 cd hcd).1 hi

/-! ## The read's hard state -/

/-- The hard-state step of `walLastHS`'s fold. -/
def tHsStep (p : THs) (o : TOp) : THs := if o.snap then p else tPhsNext p o.hs

theorem tSaveSnap_hs (s : TContents) (idx term : w64) : (tSaveSnap s idx term).hs = s.hs := by
  unfold tSaveSnap; split <;> rfl

theorem tFoldChkFrom_hs : ∀ (L : List TOp) (s s' : TContents), tFoldChkFrom s L = some s' →
    s'.hs = L.foldl tHsStep s.hs := by
  intro L
  induction L with
  | nil => intro s s' h; simp [tFoldChkFrom] at h; subst h; rfl
  | cons o L ih =>
    intro s s' h
    unfold tFoldChkFrom at h
    simp only [List.foldl_cons]
    split at h
    · rename_i hsn
      rw [ih _ s' h, tSaveSnap_hs]
      simp [tHsStep, hsn]
    · rename_i hsn
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨ents, -, h⟩ := h
      rw [ih _ s' h]
      simp [tHsStep, hsn]

theorem foldl_tHsStep_filter (c : w64) : ∀ (l : List TOp) (p : THs),
    (l.filter (tKeep c)).foldl tHsStep p = l.foldl tHsStep p := by
  intro l
  induction l with
  | nil => intro p; rfl
  | cons o l ih =>
    intro p
    rw [List.filter_cons]
    split
    · simp only [List.foldl_cons]; exact ih _
    · rename_i hk
      have hsn : o.snap = true := by
        unfold tKeep at hk; cases h : o.snap <;> simp_all
      simp only [List.foldl_cons]
      rw [ih]
      simp [tHsStep, hsn]

/-- **The read's hard state is the history's last.** -/
theorem tRead_hs {h : List TOp} {c : TContents} (hr : tRead h = some c) : c.hs = tLastHS h := by
  unfold tRead tFoldChk at hr
  rw [tFoldChkFrom_hs _ _ _ hr, foldl_tHsStep_filter]
  rfl

/-! ## The new oracle accounts for the WAL -/

/-- **The restart's new oracle accounts for the WAL** (see the file header): the image `img` of
candidate `cd`'s history, the WAL's model, that reads `c` from the purged prefix 0, is a candidate `c'` of
`tCheckRestart o c` that accounts for the WAL state `d` as a running member's. -/
theorem tRestart_ok {o : TOracle} {cd : TCand} {d : WalDur} {img : List TOp} {c : TContents}
    (hcd : cd ∈ o.cands) (hok : tCandOk o cd d) (himg : img ∈ tImgs (tCandHist o cd) (tCandMark o cd))
    (hI : d.H.map WalOpG.toM = img.map absOp) (hr : tRead img = some c)
    (hsim : tSim (img.map absOp) img.length) :
    ∃ c' ∈ (tCheckRestart o c).cands, c'.h = img ∧ tMemOk (tCheckRestart o c) c' d ∧
      tMemHs (tCheckRestart o c) d ∧ tCandMark (tCheckRestart o c) c' = d.H.length ∧
      tCandOk (tCheckRestart o c) c' d := by
  have hreads : tImgReads img cd.pur c = true := by
    refine tImgReads_true (kk := 0) ⟨Nat.zero_le _, Nat.zero_le _⟩ ?_
    rw [show (W64 ((0 : Nat) : Int)) = W64 0 from rfl]
    unfold tReadCut; rw [if_pos rfl]; exact hr
  obtain ⟨c', hc', hh, hu, hp⟩ := tCheckNext_has hcd himg hreads
  obtain ⟨-, hpur, hcut, hunl, hsz, hwf⟩ := hok
  have hu' := Nat.le_trans hunl (Nat.le_trans (tRaiseUnl_ge o cd) hu)
  have hlen : d.H.length = img.length := by
    have := congrArg List.length hI; simpa using this
  have hmem : tMemOk (tCheckRestart o c) c' d := by
    refine ⟨rfl, hc', rfl, ?_, Nat.le_trans hpur hp, Nat.le_trans hcut hp, hu', hsz, ?_, Nat.zero_le _, ?_⟩
    · show d.H.map WalOpG.toM = (c'.h ++ []).map absOp
      rw [List.append_nil, hh]; exact hI
    · show tHistWf (c'.h ++ [])
      rw [List.append_nil, hh]; exact tHistWf_of_mem_tImgs hwf.1 himg
    · show tSim ((c'.h ++ []).map absOp) (c'.h.length + uint.nat (W64 0))
      rw [List.append_nil, hh]; exact hsim
  have hmark : tCandMark (tCheckRestart o c) c' = d.H.length := by
    show c'.h.length + uint.nat (W64 0) = d.H.length
    rw [hh, hlen]; rfl
  refine ⟨c', hc', hh, hmem, ?_, hmark, ?_⟩
  · show absHs c.hs = walLastHS (d.H.map WalOpG.toM)
    rw [tRead_hs hr, hI, tLastHS_abs]
  · have := tMemOk_candOk hmem (by simp [tCheckRestart])
    exact this

end pure

end etcd_wal
end EtcdGrove
end Perennial

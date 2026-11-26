/- Lean-first (no Rocq counterpart).

# The WAL's records with their history (etcd-dist D6, task T2, 2026-11-24)

`notes/etcd-dist-d6.md` §3, §10. `walRecs h σ` (`WalRecs.lean`, sealed) says the WAL's records are `σ`
and hides the history they fold from. A crash leaves a prefix of that history (from the synced mark
on: `walImg`; with the fork fix of Q1, a complete prefix: `walSaveAtomic.law`), so the server's
crash-aware durability invariant (`InvWalCrash.lean`) must say what every such prefix reads as. This
module exposes the history, as the server reads it (`walSrvHist`), beside the records:
`walRecsH h σ Hs sized` is `walRecs h σ sized` with the history `Hs`, and `walRecs_iff_H` relates
the two; the history's fold is the records (`walRecsH_fold`).

The two durable facts the invariant also uses are the WAL's own: the synced lower bound
`WalFs.walSyncedLb h.dir h.γ.inc n` (persistent; `storage.Save.spec`'s post when the batch must sync) and the
history's growth at each write, which the server's contract states over `walRecsH`
(`InvWalCrash.lean`'s `walSaveH.law`, `walSaveSnapH.law`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.WalRecs
public import Proof.go_etcd_io.etcd.server.v3.storage.WalRecsCrash
import all Proof.go_etcd_io.etcd.server.v3.storage.WalRecs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The WAL `h`'s records are `σ`, its history (as the server reads it) `Hs`** (sealed; exclusive,
timeless): `walRecs h σ sized` with its history named. -/
@[no_expose] def walRecsH (h : WalH GF) (σ : StorContents) (Hs : WalHist) (sized : Bool := false) :
    IProp GF :=
  letI := h.W
  iprop(∃ d : WalDur, WalFs.walDiskAtI h.dir h.γ.inc d ∗ monoListAuthOwn h.γh 1 d.H ∗ WalFs.walNamed h.dir h.γ.inc ∗
    ⌜walFoldChkFrom walFresh (walSrvHist d.H) = some σ ∧ d.metadata = h.md ∧ d.sized = true ∧
      (sized = true → walEntsSized d.H) ∧ walSrvHist d.H = Hs⌝)

instance walRecsH_timeless (h : WalH GF) (σ : StorContents) (Hs : WalHist) (sized : Bool) :
    Timeless (walRecsH (GF := GF) h σ Hs sized) := by
  unfold walRecsH; infer_instance

/-- **The records are the records at some history.** -/
theorem walRecs_iff_H (h : WalH GF) (σ : StorContents) (sized : Bool) :
    walRecs (GF := GF) h σ sized ⊣⊢ ∃ Hs : WalHist, walRecsH h σ Hs sized := by
  unfold walRecs walRecsH
  constructor
  · iintro ⟨%d, Hd, Ha, Hn, %hf⟩
    iexists walSrvHist d.H
    iexists d
    iframe Hd Ha Hn
    ipureintro; exact ⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2, rfl⟩
  · iintro ⟨%Hs, %d, Hd, Ha, Hn, %hf⟩
    iexists d
    iframe Hd Ha Hn
    ipureintro; exact ⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1⟩

theorem walRecsH_walRecs (h : WalH GF) (σ : StorContents) (Hs : WalHist) (sized : Bool) :
    walRecsH (GF := GF) h σ Hs sized ⊢ walRecs h σ sized := by
  iintro H
  iapply (walRecs_iff_H h σ sized).2
  iexists Hs
  iexact H

/-- **The history folds to the records.** -/
theorem walRecsH_fold (h : WalH GF) (σ : StorContents) (Hs : WalHist) (sized : Bool) :
    walRecsH (GF := GF) h σ Hs sized ⊢ walRecsH h σ Hs sized ∗ ⌜walFoldChkFrom walFresh Hs = some σ⌝ := by
  unfold walRecsH
  iintro ⟨%d, Hd, Ha, Hn, %hf⟩
  isplitl [Hd Ha Hn]
  · iexists d
    iframe Hd Ha Hn
    ipureintro; exact hf
  · ipureintro; rw [← hf.2.2.2.2]; exact hf.1

/-- (P5) **After `SaveSnap(m)`, the records start at or above `m`'s index** (`walRecs_saveSnap_baseLb`
with the history kept). -/
theorem walRecsH_saveSnap_baseLb (h : WalH GF) (σ : StorContents) (m : SnapshotMetadataM) (Hs : WalHist)
    (sized : Bool) :
    walRecsH (GF := GF) h (walSaveSnap σ m) Hs sized ⊢
      walRecsH h (walSaveSnap σ m) Hs sized ∗ walBaseLb h (uint.nat m.Index') := by
  unfold walRecsH
  iintro ⟨%d, Hd, Ha, #Hn, %hf⟩
  ihave #Hl := monoListLbOwn_get h.γh 1 d.H $$ Ha
  isplitl [Hd Ha]
  · iexists d
    iframe Hd Ha Hn
    ipureintro; exact hf
  · have hle : uint.nat m.Index' ≤ (walSaveSnap σ m).b := by
      obtain ⟨h1, h2⟩ := walSaveSnap_base_ge σ m
      rcases h2 with h2 | h2 <;> omega
    iapply walBaseLb_mono h (walSaveSnap σ m).b _ hle
    unfold walBaseLb
    iexists d.H
    iframe Hl
    ipureintro; exact ⟨_, hf.1, Nat.le_refl _⟩

/-- (P5) **The empty prefix is synced** (the WAL's directory entry is durable, `walNamed`): the synced
mark a first start's durability invariant is allocated at. -/
theorem walRecsH_synced0 (h : WalH GF) (σ : StorContents) (Hs : WalHist) (sized : Bool) :
    walRecsH (GF := GF) h σ Hs sized ⊢
      walRecsH h σ Hs sized ∗ (letI := h.W; WalFs.walSyncedLb h.dir h.γ.inc 0) := by
  letI := h.W
  unfold walRecsH
  iintro ⟨%d, Hd, Ha, #Hn, %hf⟩
  isplitl [Hd Ha]
  · iexists d; iframe Hd Ha Hn; ipureintro; exact hf
  · iunfold WalFs.walNamed at Hn
    iunfold WalFs.walSyncedLb
    icases Hn with ⟨%s, %I, #Hp, %hs⟩
    iexists s, I
    iframe Hp
    ipureintro
    rcases hs with ⟨hi, d', hd, -⟩ | hlt
    · exact Or.inl ⟨hi, d', hd, Nat.zero_le _⟩
    · exact Or.inr hlt

/-- **The records across a crash** (P8, 2026-11-25; T5's `walFilesC_crash` on the records with their
history): from the crash view (`walCrashWal`, whole operations since P8), the records `σ` at the
history `Hs` (given back), their synced mark `n`, the new generation's lock token and the WAL
directory's call permission's half, a crash prefix `j` (`n ≤ j ≤ |Hs|`) whose read, if it succeeds, the
new generation's files hold (`walFilesC`, at the area with the new generation's WAL names), with the
member `id` of the cluster `cid` the WAL's metadata names. What T2's crash law's callback runs. -/
theorem walRecsH_crash (h : WalH GF) (W' : WalFs.WalGS GF) (σ : StorContents) (Hs : WalHist) (n : Nat)
    (id cid : w64) (hmd : h.md = walMetaEnc id cid) :
    letI := h.ext; letI := h.semOk; letI := h.has
    WalFs.walCrashWal h.W W' ∗ walRecsH h σ Hs true ∗ WalFs.walSyncedLb (W := h.W) h.dir h.γ.inc n ∗
      WalFs.walUnlockedTok (W := W') ∗ Fs.osCallPerm (Fs.callKey h.R h.dir) (1 : Qp).half ⊢
      walRecsH h σ Hs true ∗ ∃ j : Nat, ⌜n ≤ j ∧ j ≤ Hs.length⌝ ∗
        ∀ σ' : StorContents, ⌜walRead (Hs.take j) = some σ'⌝ -∗
          walFilesC { h.toWalA with W := W' } id cid σ' true := by
  letI := h.ext; letI := h.semOk; letI := h.has
  unfold walRecsH
  iintro ⟨Hcs, ⟨%d, Hd, Ha, #Hn, %hf⟩, #Hs, Hu, Hc⟩
  obtain ⟨hfold, hm, hsz, hes, hH⟩ := hf
  icases walFilesC_crash h.toWalA W' h.γ.inc d n id cid (by rw [hm]; exact hmd) hsz (hes rfl) $$
    [Hcs Hd Hs Hn Hu Hc] with ⟨Hd, %j, %hj, Hf⟩
  · iframe Hcs Hd Hs Hn Hu Hc
  isplitl [Hd Ha]
  · iexists d
    iframe Hd Ha Hn
    ipureintro; exact ⟨hfold, hm, hsz, hes, hH⟩
  iexists j
  isplitr
  · ipureintro; rw [← hH]; simpa [walSrvHist] using hj
  iintro %σ' %hr
  iapply Hf
  ipureintro; rw [← hH] at hr; exact hr

/-- (P5) **`Save`'s update of the records with their history, as layer 1's** (`walRecs_saveAU` with the
history: the caller's update commits at the history `walSrvHist d.H` the `Save` appended to). -/
theorem walRecsH_saveAU (h : WalH GF) (sized : Bool) (hs : HardStateM) (cs : List EntryC)
    (Q : WalHist → IProp GF)
    (hc : ∀ c ∈ cs, ufWire entrySchema c.uf ∧ entrySize c < 2 ^ 48 ∧ (sized = true → entSizeOk c)) :
    (AU <{ ∃∃ (σ : StorContents) (Hs : WalHist), walRecsH h σ Hs sized ∗
            ⌜WalSaveOk σ (cs.map EntryC.model)⌝ }>
        @ WalFs.walAuMask, ∅
        <{ walRecsH h (walSave σ hs (cs.map EntryC.model)) (Hs ++ [WalOpG.save hs (cs.map EntryC.model)])
            sized, COMM Q Hs }>) ⊢
      AU <{ ∃∃ d : WalDur, WalFs.walDiskAtI (W := h.W) h.dir h.γ.inc d ∗ ⌜d.sized = true⌝ }> @ WalFs.walAuMask, ∅
        <{ WalFs.walDiskAtI (W := h.W) h.dir h.γ.inc { d with H := d.H ++ [(WalOpG.save hs (cs.map walEntW)).toRaw] },
          COMM Q (walSrvHist d.H) }> := by
  iintro Hau
  iauintro
  unfold atomic_acc
  ihave Hacc := aupd_aacc $$ Hau
  unfold atomic_acc
  imod Hacc with Hacc
  isimp only [texist_cons, texist_nil, Std.Tele.app, ULift.down] at Hacc
  icases Hacc with ⟨%σ, %Hs, ⟨Hr, %hok⟩, Hcl⟩
  unfold walRecsH
  icases Hr with ⟨%d, Hd, Ha, #Hn, %hf⟩
  obtain ⟨hf1, hf2, hf3, hf4, hH⟩ := hf
  subst hH
  imodintro
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists d
  iframe Hd
  isplitr
  · ipureintro; exact hf3
  isplit
  · iintro ⟨Hd, -⟩
    icases Hcl with ⟨Habort, -⟩
    iapply Habort
    isplitl [Hd Ha]
    · iexists d
      iframe Hd Ha Hn
      ipureintro; exact ⟨hf1, hf2, hf3, hf4, rfl⟩
    · ipureintro; exact hok
  · iintro Hd
    icases Hcl with ⟨-, Hcommit⟩
    isimp only [tforall_nil, Std.Tele.app] at Hcommit
    imod monoListAuthOwn_update_app [(WalOpG.save hs (cs.map walEntW)).toRaw] $$ Ha with ⟨Ha, -⟩
    iapply Hcommit
    iexists { d with H := d.H ++ [(WalOpG.save hs (cs.map walEntW)).toRaw] }
    iframe Hd Ha Hn
    have hsh := walSrvHist_snoc_save d.H hs cs (fun c hcm => ⟨(hc c hcm).1, (hc c hcm).2.1⟩)
    ipureintro
    refine ⟨?_, hf2, hf3, ?_, hsh⟩
    · show walFoldChkFrom walFresh (walSrvHist (d.H ++ _)) = _
      rw [hsh]
      exact walFoldChkFrom_snoc_save hf1 hok
    · intro hsz hs' es' hmem e he
      have hmem' : WalOpG.save hs' es' ∈ d.H.map WalOpG.toM ∨
          WalOpG.save hs' es' = WalOpG.save hs (cs.map walEntW) := by
        rw [List.map_append, List.mem_append, List.map_singleton, WalOpG.toM_toRaw,
          List.mem_singleton] at hmem
        exact hmem
      rcases hmem' with hmem' | heq
      · exact hf4 hsz hs' es' hmem' e he
      · injection heq with h1 h2
        subst h2
        obtain ⟨c, hcm, rfl⟩ := List.mem_map.mp he
        exact ⟨c, rfl, (hc c hcm).2.2 hsz⟩

/-- (P5) **`SaveSnap`'s update of the records with their history, as layer 1's** (`walRecs_saveSnapAU`
with the history). -/
theorem walRecsH_saveSnapAU (h : WalH GF) (sized : Bool) (m : SnapshotMetadataM) (al : Bool)
    (Q : WalHist → IProp GF) :
    (AU <{ ∃∃ (σ : StorContents) (Hs : WalHist), walRecsH h σ Hs sized ∗
          ⌜uint.nat m.Index' = σ.b → m.Term' = σ.base.term'⌝ }>
        @ WalFs.walAuMask, ∅
        <{ walRecsH h (walSaveSnap σ m) (Hs ++ [WalOpG.snap m al]) sized, COMM Q Hs }>) ⊢
      AU <{ ∃∃ d : WalDur, WalFs.walDiskAtI (W := h.W) h.dir h.γ.inc d ∗ ⌜d.sized = true⌝ }> @ WalFs.walAuMask, ∅
        <{ WalFs.walDiskAtI (W := h.W) h.dir h.γ.inc { d with H := d.H ++ [WalOpG.snap m al] },
          COMM Q (walSrvHist d.H) ∗ monoListLbOwn h.γh (d.H ++ [WalOpG.snap m al]) }> := by
  iintro Hau
  iauintro
  unfold atomic_acc
  ihave Hacc := aupd_aacc $$ Hau
  unfold atomic_acc
  imod Hacc with Hacc
  isimp only [texist_cons, texist_nil, Std.Tele.app, ULift.down] at Hacc
  icases Hacc with ⟨%σ, %Hs, ⟨Hr, %hok⟩, Hcl⟩
  unfold walRecsH
  icases Hr with ⟨%d, Hd, Ha, #Hn, %hf⟩
  obtain ⟨hf1, hf2, hf3, hf4, hH⟩ := hf
  subst hH
  imodintro
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists d
  iframe Hd
  isplitr
  · ipureintro; exact hf3
  isplit
  · iintro ⟨Hd, -⟩
    icases Hcl with ⟨Habort, -⟩
    iapply Habort
    isplitl [Hd Ha]
    · iexists d
      iframe Hd Ha Hn
      ipureintro; exact ⟨hf1, hf2, hf3, hf4, rfl⟩
    · ipureintro; exact hok
  · iintro Hd
    icases Hcl with ⟨-, Hcommit⟩
    isimp only [tforall_nil, Std.Tele.app] at Hcommit
    imod monoListAuthOwn_update_app [WalOpG.snap m al] $$ Ha with ⟨Ha, #Hlb⟩
    imod Hcommit $$ [Hd Ha] with HQ
    · iexists { d with H := d.H ++ [WalOpG.snap m al] }
      iframe Hd Ha Hn
      ipureintro
      refine ⟨?_, hf2, hf3, ?_, walSrvHist_snoc_snap _ _ _⟩
      · show walFoldChkFrom walFresh (walSrvHist (d.H ++ _)) = _
        rw [walSrvHist_snoc_snap]
        exact walFoldChkFrom_snoc_snap hf1
      · intro hsz hs' es' hmem e he
        have hmem' : WalOpG.save hs' es' ∈ d.H.map WalOpG.toM ∨
            WalOpG.save hs' es' = (WalOpG.snap m al : WalOpG WalEnt).toM := by
          rw [List.map_append, List.mem_append, List.map_singleton, List.mem_singleton] at hmem
          exact hmem
        rcases hmem' with hmem' | heq
        · exact hf4 hsz hs' es' hmem' e he
        · cases heq
    imodintro
    iframe HQ Hlb

/-- (P5) **An atomic update of the records, as one of the records with their history** (the history's
op `o` appended; the caller's `Q` independent of the history): the history is read off the records
(`walRecs_iff_H`) and forgotten again. -/
theorem walRecs_au_toH (h : WalH GF) (sized : Bool) (P : StorContents → Prop)
    (f : StorContents → StorContents) (o : WalOp) (E : CoPset) (Q : IProp GF) :
    (AU <{ ∃∃ (σ : StorContents), walRecs h σ sized ∗ ⌜P σ⌝ }> @ E, ∅ <{ walRecs h (f σ) sized, COMM Q }>) ⊢
      AU <{ ∃∃ (σ : StorContents) (Hs : WalHist), walRecsH h σ Hs sized ∗ ⌜P σ⌝ }> @ E, ∅
        <{ walRecsH h (f σ) (Hs ++ [o]) sized, COMM Q }> := by
  iintro Hau
  iauintro
  unfold atomic_acc
  ihave Hacc := aupd_aacc $$ Hau
  unfold atomic_acc
  imod Hacc with Hacc
  isimp only [texist_cons, texist_nil, Std.Tele.app, ULift.down] at Hacc
  icases Hacc with ⟨%σ, ⟨Hr, %hok⟩, Hcl⟩
  icases (walRecs_iff_H h σ sized).1 $$ Hr with ⟨%Hs, Hr⟩
  imodintro
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists σ, Hs
  iframe Hr
  isplitr
  · ipureintro; exact hok
  isplit
  · iintro ⟨Hr, -⟩
    icases Hcl with ⟨Habort, -⟩
    iapply Habort
    isplitl [Hr]
    · iapply walRecsH_walRecs; iexact Hr
    · ipureintro; exact hok
  · iintro Hr
    icases Hcl with ⟨-, Hcommit⟩
    isimp only [tforall_nil, Std.Tele.app] at Hcommit
    iapply Hcommit
    iapply walRecsH_walRecs; iexact Hr

/-- (P5) **`Release`'s read of the records with their history** (`walRecs_releaseAU`'s): layer 1's lock
update at the snapshot record the witness names, the records and their history unchanged. -/
theorem walRecsH_releaseAU (h : WalH GF) (i : Nat) (m : SnapshotMetadataM) (Q : IProp GF) :
    walSnapRec h i m ∗
      (AU <{ ∃∃ (σ : StorContents) (Hs : WalHist) (s : Bool), walRecsH h σ Hs s }> @ WalFs.walAuMask, ∅
        <{ walRecsH h σ Hs s, COMM Q }>) ⊢
      AU <{ ∃∃ d : WalDur, WalFs.walDiskAtI (W := h.W) h.dir h.γ.inc d ∗
          ⌜(∃ al, d.H[i]? = some (WalOpG.snap ⟨m.ConfState', m.Index', m.Term'⟩ al)) ∧ i < i + 1⌝ }>
        @ WalFs.walAuMask, ∅
        <{ WalFs.walDiskAtI (W := h.W) h.dir h.γ.inc
            { d with unl := max d.unl (walReleasePos (d.H.map WalOpG.toM) m.Index') }, COMM Q }> := by
  iintro ⟨#Hw, Hau⟩
  iauintro
  unfold atomic_acc
  ihave Hacc := aupd_aacc $$ Hau
  unfold atomic_acc
  imod Hacc with Hacc
  isimp only [texist_cons, texist_nil, Std.Tele.app, ULift.down] at Hacc
  icases Hacc with ⟨%σ, %Hs, %s, Hr, Hcl⟩
  unfold walRecsH
  icases Hr with ⟨%d, Hd, Ha, #Hn, %hf⟩
  iunfold walSnapRec at Hw
  icases Hw with ⟨%H0, #Hl, -, %hi⟩
  ihave %hv := mono_list_auth_lb_valid h.γh 1 d.H H0 $$ Ha Hl
  imodintro
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists d
  iframe Hd
  isplitr
  · ipureintro
    obtain ⟨al, hi⟩ := hi
    exact ⟨⟨al, prefix_getElem? hv.2 hi⟩, Nat.lt_succ_self i⟩
  isplit
  · iintro ⟨Hd, -⟩
    icases Hcl with ⟨Habort, -⟩
    iapply Habort
    iexists d
    iframe Hd Ha Hn
    ipureintro; exact hf
  · iintro Hd
    icases Hcl with ⟨-, Hcommit⟩
    isimp only [tforall_nil, Std.Tele.app] at Hcommit
    iapply Hcommit
    iexists { d with unl := max d.unl (walReleasePos (d.H.map WalOpG.toM) m.Index') }
    iframe Hd Ha Hn
    ipureintro; exact hf

/-- (P5) **An identity update over the records turned into one over the records with their history**
(the history unchanged). -/
theorem walRecs_auId_toH (h : WalH GF) (E : CoPset) (Q : IProp GF) :
    (AU <{ ∃∃ (σ : StorContents) (s : Bool), walRecs h σ s }> @ E, ∅ <{ walRecs h σ s, COMM Q }>) ⊢
      AU <{ ∃∃ (σ : StorContents) (Hs : WalHist) (s : Bool), walRecsH h σ Hs s }> @ E, ∅
        <{ walRecsH h σ Hs s, COMM Q }> := by
  iintro Hau
  iauintro
  unfold atomic_acc
  ihave Hacc := aupd_aacc $$ Hau
  unfold atomic_acc
  imod Hacc with Hacc
  isimp only [texist_cons, texist_nil, Std.Tele.app, ULift.down] at Hacc
  icases Hacc with ⟨%σ, %s, Hr, Hcl⟩
  icases (walRecs_iff_H h σ s).1 $$ Hr with ⟨%Hs, Hr⟩
  imodintro
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists σ, Hs, s
  iframe Hr
  isplit
  · iintro Hr
    icases Hcl with ⟨Habort, -⟩
    iapply Habort
    iapply walRecsH_walRecs; iexact Hr
  · iintro Hr
    icases Hcl with ⟨-, Hcommit⟩
    isimp only [tforall_nil, Std.Tele.app] at Hcommit
    iapply Hcommit
    iapply walRecsH_walRecs; iexact Hr

/-- (etcd_safe P5, 2026-11-26) **An identity update over the records with their history turned into `Close`'s**
(layer 1's update over the WAL's durable state, which `Close` reads and leaves unchanged): what the crash-aware
`Close` (`walCloseK`, the WAL contract) fires inside the caller's invariant, so that the records stay there. -/
theorem walRecsH_closeAU (h : WalH GF) (Q : IProp GF) :
    (AU <{ ∃∃ (σ : StorContents) (Hs : WalHist) (s : Bool), walRecsH h σ Hs s }> @ WalFs.walAuMask, ∅
      <{ walRecsH h σ Hs s, COMM Q }>) ⊢
      AU <{ ∃∃ d : WalDur, WalFs.walDiskAtI (W := h.W) h.dir h.γ.inc d }> @ WalFs.walAuMask, ∅
        <{ WalFs.walDiskAtI (W := h.W) h.dir h.γ.inc d, COMM Q }> := by
  iintro Hau
  iauintro
  unfold atomic_acc
  ihave Hacc := aupd_aacc $$ Hau
  unfold atomic_acc
  imod Hacc with Hacc
  isimp only [texist_cons, texist_nil, Std.Tele.app, ULift.down] at Hacc
  icases Hacc with ⟨%σ, %Hs, %s, Hr, Hcl⟩
  unfold walRecsH
  icases Hr with ⟨%d, Hd, Ha, #Hn, %hf⟩
  imodintro
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists d
  iframe Hd
  isplit
  · iintro Hd
    icases Hcl with ⟨Habort, -⟩
    iapply Habort
    iexists d
    iframe Hd Ha Hn
    ipureintro; exact hf
  · iintro Hd
    icases Hcl with ⟨-, Hcommit⟩
    isimp only [tforall_nil, Std.Tele.app] at Hcommit
    iapply Hcommit
    iexists d
    iframe Hd Ha Hn
    ipureintro; exact hf

/-! ### (P5, ledger proposal (b), approved 2026-11-25) The records by their history alone

`walRecsH` pins the records to the history's *eager* fold (`walFoldChkFrom walFresh`), which a restart
does not keep: the reader (`walRead`) drops a snapshot record above the last commit, and keeps it again
once a later `Save` commits past it. `walHistH h Hs sized` is `walRecsH` without the fold row: the WAL
`h`'s history is `Hs` (and its entries sized), nothing said of a fold. The contract's `Save`/`SaveSnap`
and the crash-aware invariant move to it (what `Hs` reads as is the invariant's, over `walRead`). -/

/-- **The WAL `h`'s history (as the server reads it) is `Hs`** (sealed; exclusive, timeless). -/
@[no_expose] def walHistH (h : WalH GF) (Hs : WalHist) (sized : Bool := false) : IProp GF :=
  letI := h.W
  iprop(∃ d : WalDur, WalFs.walDiskAtI h.dir h.γ.inc d ∗ monoListAuthOwn h.γh 1 d.H ∗ WalFs.walNamed h.dir h.γ.inc ∗
    ⌜d.metadata = h.md ∧ d.sized = true ∧ (sized = true → walEntsSized d.H) ∧ walSrvHist d.H = Hs⌝)

instance walHistH_timeless (h : WalH GF) (Hs : WalHist) (sized : Bool) :
    Timeless (walHistH (GF := GF) h Hs sized) := by
  unfold walHistH; infer_instance

/-- **The records with their history are the history with its eager fold.** -/
theorem walRecsH_iff_hist (h : WalH GF) (σ : StorContents) (Hs : WalHist) (sized : Bool) :
    walRecsH (GF := GF) h σ Hs sized ⊣⊢ walHistH h Hs sized ∗ ⌜walFoldChkFrom walFresh Hs = some σ⌝ := by
  unfold walRecsH walHistH
  constructor
  · iintro ⟨%d, Hd, Ha, Hn, %hf⟩
    isplitl [Hd Ha Hn]
    · iexists d
      iframe Hd Ha Hn
      ipureintro; exact ⟨hf.2.1, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2⟩
    · ipureintro; rw [← hf.2.2.2.2]; exact hf.1
  · iintro ⟨⟨%d, Hd, Ha, Hn, %hf⟩, %hfo⟩
    iexists d
    iframe Hd Ha Hn
    ipureintro; exact ⟨by rw [hf.2.2.2]; exact hfo, hf.1, hf.2.1, hf.2.2.1, hf.2.2.2⟩

/-- **The records are the records at some history** (`walRecs_iff_H` through `walHistH`). -/
theorem walRecs_iff_hist (h : WalH GF) (σ : StorContents) (sized : Bool) :
    walRecs (GF := GF) h σ sized ⊣⊢
      ∃ Hs : WalHist, walHistH h Hs sized ∗ ⌜walFoldChkFrom walFresh Hs = some σ⌝ := by
  constructor
  · iintro H
    icases (walRecs_iff_H h σ sized).1 $$ H with ⟨%Hs, H⟩
    iexists Hs
    iapply (walRecsH_iff_hist h σ Hs sized).1; iexact H
  · iintro ⟨%Hs, H⟩
    iapply (walRecs_iff_H h σ sized).2
    iexists Hs
    iapply (walRecsH_iff_hist h σ Hs sized).2; iexact H

/-- (P5) **The empty prefix is synced** (`walRecsH_synced0`'s). -/
theorem walHistH_synced0 (h : WalH GF) (Hs : WalHist) (sized : Bool) :
    walHistH (GF := GF) h Hs sized ⊢
      walHistH h Hs sized ∗ (letI := h.W; WalFs.walSyncedLb h.dir h.γ.inc 0) := by
  letI := h.W
  unfold walHistH
  iintro ⟨%d, Hd, Ha, #Hn, %hf⟩
  isplitl [Hd Ha]
  · iexists d; iframe Hd Ha Hn; ipureintro; exact hf
  · iunfold WalFs.walNamed at Hn
    iunfold WalFs.walSyncedLb
    icases Hn with ⟨%s, %I, #Hp, %hs⟩
    iexists s, I
    iframe Hp
    ipureintro
    rcases hs with ⟨hi, d', hd, -⟩ | hlt
    · exact Or.inl ⟨hi, d', hd, Nat.zero_le _⟩
    · exact Or.inr hlt

/-- **The history across a crash** (`walRecsH_crash` without the fold). -/
theorem walHistH_crash (h : WalH GF) (W' : WalFs.WalGS GF) (Hs : WalHist) (n : Nat)
    (id cid : w64) (hmd : h.md = walMetaEnc id cid) :
    letI := h.ext; letI := h.semOk; letI := h.has
    WalFs.walCrashWal h.W W' ∗ walHistH h Hs true ∗ WalFs.walSyncedLb (W := h.W) h.dir h.γ.inc n ∗
      WalFs.walUnlockedTok (W := W') ∗ Fs.osCallPerm (Fs.callKey h.R h.dir) (1 : Qp).half ⊢
      walHistH h Hs true ∗ ∃ j : Nat, ⌜n ≤ j ∧ j ≤ Hs.length⌝ ∗
        ∀ σ' : StorContents, ⌜walRead (Hs.take j) = some σ'⌝ -∗
          walFilesC { h.toWalA with W := W' } id cid σ' true := by
  letI := h.ext; letI := h.semOk; letI := h.has
  unfold walHistH
  iintro ⟨Hcs, ⟨%d, Hd, Ha, #Hn, %hf⟩, #Hs, Hu, Hc⟩
  obtain ⟨hm, hsz, hes, hH⟩ := hf
  icases walFilesC_crash h.toWalA W' h.γ.inc d n id cid (by rw [hm]; exact hmd) hsz (hes rfl) $$
    [Hcs Hd Hs Hn Hu Hc] with ⟨Hd, %j, %hj, Hf⟩
  · iframe Hcs Hd Hs Hn Hu Hc
  isplitl [Hd Ha]
  · iexists d
    iframe Hd Ha Hn
    ipureintro; exact ⟨hm, hsz, hes, hH⟩
  iexists j
  isplitr
  · ipureintro; rw [← hH]; simpa [walSrvHist] using hj
  iintro %σ' %hr
  iapply Hf
  ipureintro; rw [← hH] at hr; exact hr

/-- (P5) **`Save`'s update of the history, as layer 1's** (`walRecsH_saveAU` without the fold: no
`WalSaveOk` asked, layer 1's `Save` needs none). -/
theorem walHistH_saveAU (h : WalH GF) (sized : Bool) (hs : HardStateM) (cs : List EntryC)
    (Q : WalHist → IProp GF)
    (hc : ∀ c ∈ cs, ufWire entrySchema c.uf ∧ entrySize c < 2 ^ 48 ∧ (sized = true → entSizeOk c)) :
    (AU <{ ∃∃ Hs : WalHist, walHistH h Hs sized }>
        @ WalFs.walAuMask, ∅
        <{ walHistH h (Hs ++ [WalOpG.save hs (cs.map EntryC.model)]) sized, COMM Q Hs }>) ⊢
      AU <{ ∃∃ d : WalDur, WalFs.walDiskAtI (W := h.W) h.dir h.γ.inc d ∗ ⌜d.sized = true⌝ }> @ WalFs.walAuMask, ∅
        <{ WalFs.walDiskAtI (W := h.W) h.dir h.γ.inc { d with H := d.H ++ [(WalOpG.save hs (cs.map walEntW)).toRaw] },
          COMM Q (walSrvHist d.H) }> := by
  iintro Hau
  iauintro
  unfold atomic_acc
  ihave Hacc := aupd_aacc $$ Hau
  unfold atomic_acc
  imod Hacc with Hacc
  isimp only [texist_cons, texist_nil, Std.Tele.app, ULift.down] at Hacc
  icases Hacc with ⟨%Hs, Hr, Hcl⟩
  unfold walHistH
  icases Hr with ⟨%d, Hd, Ha, #Hn, %hf⟩
  obtain ⟨hf2, hf3, hf4, hH⟩ := hf
  subst hH
  imodintro
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists d
  iframe Hd
  isplitr
  · ipureintro; exact hf3
  isplit
  · iintro ⟨Hd, -⟩
    icases Hcl with ⟨Habort, -⟩
    iapply Habort
    iexists d
    iframe Hd Ha Hn
    ipureintro; exact ⟨hf2, hf3, hf4, rfl⟩
  · iintro Hd
    icases Hcl with ⟨-, Hcommit⟩
    isimp only [tforall_nil, Std.Tele.app] at Hcommit
    imod monoListAuthOwn_update_app [(WalOpG.save hs (cs.map walEntW)).toRaw] $$ Ha with ⟨Ha, -⟩
    iapply Hcommit
    iexists { d with H := d.H ++ [(WalOpG.save hs (cs.map walEntW)).toRaw] }
    iframe Hd Ha Hn
    have hsh := walSrvHist_snoc_save d.H hs cs (fun c hcm => ⟨(hc c hcm).1, (hc c hcm).2.1⟩)
    ipureintro
    refine ⟨hf2, hf3, ?_, hsh⟩
    intro hsz hs' es' hmem e he
    have hmem' : WalOpG.save hs' es' ∈ d.H.map WalOpG.toM ∨
        WalOpG.save hs' es' = WalOpG.save hs (cs.map walEntW) := by
      rw [List.map_append, List.mem_append, List.map_singleton, WalOpG.toM_toRaw,
        List.mem_singleton] at hmem
      exact hmem
    rcases hmem' with hmem' | heq
    · exact hf4 hsz hs' es' hmem' e he
    · injection heq with h1 h2
      subst h2
      obtain ⟨c, hcm, rfl⟩ := List.mem_map.mp he
      exact ⟨c, rfl, (hc c hcm).2.2 hsz⟩

/-- (P5) **`SaveSnap`'s update of the history, as layer 1's** (`walRecsH_saveSnapAU` without the fold:
no premise on the base's term). -/
theorem walHistH_saveSnapAU (h : WalH GF) (sized : Bool) (m : SnapshotMetadataM) (al : Bool)
    (Q : WalHist → IProp GF) :
    (AU <{ ∃∃ Hs : WalHist, walHistH h Hs sized }>
        @ WalFs.walAuMask, ∅
        <{ walHistH h (Hs ++ [WalOpG.snap m al]) sized, COMM Q Hs }>) ⊢
      AU <{ ∃∃ d : WalDur, WalFs.walDiskAtI (W := h.W) h.dir h.γ.inc d ∗ ⌜d.sized = true⌝ }> @ WalFs.walAuMask, ∅
        <{ WalFs.walDiskAtI (W := h.W) h.dir h.γ.inc { d with H := d.H ++ [WalOpG.snap m al] },
          COMM Q (walSrvHist d.H) ∗ monoListLbOwn h.γh (d.H ++ [WalOpG.snap m al]) }> := by
  iintro Hau
  iauintro
  unfold atomic_acc
  ihave Hacc := aupd_aacc $$ Hau
  unfold atomic_acc
  imod Hacc with Hacc
  isimp only [texist_cons, texist_nil, Std.Tele.app, ULift.down] at Hacc
  icases Hacc with ⟨%Hs, Hr, Hcl⟩
  unfold walHistH
  icases Hr with ⟨%d, Hd, Ha, #Hn, %hf⟩
  obtain ⟨hf2, hf3, hf4, hH⟩ := hf
  subst hH
  imodintro
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists d
  iframe Hd
  isplitr
  · ipureintro; exact hf3
  isplit
  · iintro ⟨Hd, -⟩
    icases Hcl with ⟨Habort, -⟩
    iapply Habort
    iexists d
    iframe Hd Ha Hn
    ipureintro; exact ⟨hf2, hf3, hf4, rfl⟩
  · iintro Hd
    icases Hcl with ⟨-, Hcommit⟩
    isimp only [tforall_nil, Std.Tele.app] at Hcommit
    imod monoListAuthOwn_update_app [WalOpG.snap m al] $$ Ha with ⟨Ha, #Hlb⟩
    imod Hcommit $$ [Hd Ha] with HQ
    · iexists { d with H := d.H ++ [WalOpG.snap m al] }
      iframe Hd Ha Hn
      ipureintro
      refine ⟨hf2, hf3, ?_, walSrvHist_snoc_snap _ _ _⟩
      intro hsz hs' es' hmem e he
      have hmem' : WalOpG.save hs' es' ∈ d.H.map WalOpG.toM ∨
          WalOpG.save hs' es' = (WalOpG.snap m al : WalOpG WalEnt).toM := by
        rw [List.map_append, List.mem_append, List.map_singleton, List.mem_singleton] at hmem
        exact hmem
      rcases hmem' with hmem' | heq
      · exact hf4 hsz hs' es' hmem' e he
      · cases heq
    imodintro
    iframe HQ Hlb

/-- (P5 (b)) **An update of the records with their history, as one of the history** (the contract's
`Save`/`SaveSnap` are over `walHistH`; the laws over `walRecsH` derive from them): the history's eager fold
is the records (`walRecsH_iff_hist`), and at the commit the fold's step `hstep` gives the new records. -/
theorem walRecsH_au_toHist (h : WalH GF) (sized : Bool) (P : StorContents → Prop)
    (f : StorContents → StorContents) (o : WalOp) (E : CoPset) (Q : WalHist → IProp GF)
    (hstep : ∀ (Hs : WalHist) (σ : StorContents), walFoldChkFrom walFresh Hs = some σ → P σ →
      walFoldChkFrom walFresh (Hs ++ [o]) = some (f σ)) :
    (AU <{ ∃∃ (σ : StorContents) (Hs : WalHist), walRecsH h σ Hs sized ∗ ⌜P σ⌝ }> @ E, ∅
        <{ walRecsH h (f σ) (Hs ++ [o]) sized, COMM Q Hs }>) ⊢
      AU <{ ∃∃ Hs : WalHist, walHistH h Hs sized }> @ E, ∅
        <{ walHistH h (Hs ++ [o]) sized, COMM Q Hs }> := by
  iintro Hau
  iauintro
  unfold atomic_acc
  ihave Hacc := aupd_aacc $$ Hau
  unfold atomic_acc
  imod Hacc with Hacc
  isimp only [texist_cons, texist_nil, Std.Tele.app, ULift.down] at Hacc
  icases Hacc with ⟨%σ, %Hs, ⟨Hr, %hok⟩, Hcl⟩
  icases (walRecsH_iff_hist h σ Hs sized).1 $$ Hr with ⟨Hr, %hf⟩
  imodintro
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists Hs
  isplitl [Hr]
  · iexact Hr
  isplit
  · iintro Hr
    icases Hcl with ⟨Habort, -⟩
    iapply Habort
    isplitl [Hr]
    · iapply (walRecsH_iff_hist h σ Hs sized).2
      isplitl [Hr]
      · iexact Hr
      · ipureintro; exact hf
    · ipureintro; exact hok
  · iintro Hr
    icases Hcl with ⟨-, Hcommit⟩
    isimp only [tforall_nil, Std.Tele.app] at Hcommit
    iapply Hcommit
    iapply (walRecsH_iff_hist h (f σ) (Hs ++ [o]) sized).2
    isplitl [Hr]
    · iexact Hr
    · ipureintro; exact hstep Hs σ hf hok

/-- The server's history has the raw history's length. -/
theorem walSrvHist_length (H : List (WalOpG WalEnt)) : (walSrvHist H).length = H.length := by
  unfold walSrvHist; simp

/-- (P5) **`Save` syncs on the server's history as on the raw one** (`walMustSync` reads only the
hard states and whether the batch is empty; the server's view changes only the entries). -/
theorem walMustSync_srv (H : List (WalOpG WalEnt)) (hs : HardStateM) (cs : List EntryC) :
    walMustSync (walSrvHist H) hs (cs.map EntryC.model) →
      walMustSync (H.map WalOpG.toM) hs (cs.map walEntW) := by
  have hl : walLastHS (walSrvHist H) = walLastHS (H.map WalOpG.toM) := by
    unfold walSrvHist
    rw [walLastHS_eq, walLastHS_eq, List.foldl_map]
    congr 1
    funext p o
    cases o <;> rfl
  unfold walMustSync
  rw [hl]
  rintro (h | h)
  · left; intro he; apply h; simp only [List.map_eq_nil_iff] at he ⊢; exact he
  · right; exact h

end defs

/-! ## The fork fix: a torn `Save` reads as no `Save` (Q1 (a), `notes/etcd-dist-d6.md` §9) -/

/-- **A crash leaves the reads of a complete prefix** (the WAL fork fix of `notes/etcd-dist-d6.md` §9,
decided after T1: `Save` always ends with a state record, `ReadAll` drops the entry records after the
last state record, etcd bootstraps again when the WAL has no state record): for every image `I` a
crash can leave of a history `H` whose first `n` operations are synced (`walImg`, which still has the
torn case: the first `k` entry records of operation `j` without its state record), there is a
complete prefix `H.take j` at or past the mark that every restart read (`walReadCut`, from any purge
position) reads exactly as it reads `I`.

**Superseded (P8, 2026-11-25)**: the WAL's crash view `walCrashWal` now carries the whole-operation
image (`walStCrashS`, `walImgS`), and `walRecsH_crash` gives the crash prefix directly; nothing uses this law.
**False today** (the model's `walRead` reads a torn `Save`'s entries: `walImg`'s second case;
`issues/raft-commit-lost-with-entries-kept.md`); an obligation on the WAL's re-proof after the fork fix
(another task), which may restate it over the fixed model (e.g. a `walImg` without the torn case, when
the trusted reader drops it: then it is immediate with `I = H.take j`). The server's crash-aware
durability invariant (`InvWalCrash.lean`) relies on nothing else of the fix: it says what every
complete prefix from the synced mark reads as. -/
abbrev walSaveAtomic.law [GooseExts] : Prop :=
  ∀ (H I : List (WalOpG WalEnt)) (n : Nat), walImg H n I →
    ∃ j, n ≤ j ∧ j ≤ H.length ∧
      ∀ k, walReadCut (walSrvHist I) k = walReadCut (walSrvHist (H.take j)) k

end EtcdGrove
end Perennial

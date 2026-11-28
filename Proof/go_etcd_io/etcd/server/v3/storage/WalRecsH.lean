/- Lean-first (no Rocq counterpart).

# The WAL's history (etcd-dist D6, task T2, 2026-11-24; P5 (b), 2026-11-26)

`notes/etcd-dist-d6.md` §3, §10. `walRecs h σ` (`WalRecs.lean`, sealed) says the WAL's records are `σ`
and hides the history they fold from. A crash leaves a prefix of that history (from the synced mark
on: `walImg`; with the fork fix of Q1, a complete prefix: `walSaveAtomic.law`), so the server's
crash-aware durability invariant (`InvWalCrash.lean`) must say what every such prefix reads as. This
module exposes the history, as the server reads it (`walSrvHist`): `walHistH h Hs sized` says the WAL's
history is `Hs`, nothing said of a fold; `walRecs_iff_hist` relates it to the records (the history's
eager fold). (P5 (b), 2026-11-26) Until then the records with their history, `walRecsH h σ Hs sized`
(`walHistH h Hs sized ∗ ⌜walFoldChkFrom walFresh Hs = some σ⌝`, its definition's content); the
contract and the invariant are over `walHistH` and what `Hs` reads as (`walRead`), and `walRecsH` is gone.

The two durable facts the invariant also uses are the WAL's own: the synced lower bound
`WalFs.walSyncedLb h.dir h.γ.inc n` (persistent; `storage.Save.spec`'s post when the batch must sync) and the
history's growth at each write, which the server's contract states over `walHistH`
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

/-! ### (P5, ledger proposal (b), approved 2026-11-25) The records by their history alone

The eager fold (`walFoldChkFrom walFresh`) is not what a restart keeps: the reader (`walRead`) drops a
snapshot record above the last commit, and keeps it again once a later `Save` commits past it.
`walHistH h Hs sized`: the WAL `h`'s history is `Hs` (and its entries sized), nothing said of a fold.
The contract's `Save`/`SaveSnap` and the crash-aware invariant are over it (what `Hs` reads as is the
invariant's, over `walRead`). -/

/-- **The WAL `h`'s history (as the server reads it) is `Hs`** (sealed; exclusive, timeless). -/
@[no_expose] def walHistH (h : WalH GF) (Hs : WalHist) (sized : Bool := false) : IProp GF :=
  letI := h.W
  iprop(∃ d : WalDur, WalFs.walDiskAtI h.dir h.γ.inc d ∗ monoListAuthOwn h.γh 1 d.H ∗ WalFs.walNamed h.dir h.γ.inc ∗
    ⌜d.metadata = h.md ∧ d.sized = true ∧ (sized = true → walEntsSized d.H) ∧ walSrvHist d.H = Hs⌝)

instance walHistH_timeless (h : WalH GF) (Hs : WalHist) (sized : Bool) :
    Timeless (walHistH (GF := GF) h Hs sized) := by
  unfold walHistH; infer_instance

/-- **The records are the history at some history whose eager fold they are** (B2, 2026-11-28: and along
which every prefix's eager fold has its commit within its last index, `walCommitLeFrom walFresh`, which
`walRecs` carries since walcommitle and `walHistH` does not). -/
theorem walRecs_iff_hist (h : WalH GF) (σ : StorContents) (sized : Bool) :
    walRecs (GF := GF) h σ sized ⊣⊢
      ∃ Hs : WalHist, walHistH h Hs sized ∗
        ⌜walFoldChkFrom walFresh Hs = some σ ∧ walCommitLeFrom walFresh Hs⌝ := by
  unfold walRecs walHistH
  constructor
  · iintro ⟨%d, Hd, Ha, Hn, %hf⟩
    iexists walSrvHist d.H
    isplitl [Hd Ha Hn]
    · iexists d
      iframe Hd Ha Hn
      ipureintro; exact ⟨hf.2.1, hf.2.2.1, hf.2.2.2.1, rfl⟩
    · ipureintro; exact ⟨hf.1, hf.2.2.2.2⟩
  · iintro ⟨%Hs, ⟨%d, Hd, Ha, Hn, %hf⟩, %hfo⟩
    iexists d
    iframe Hd Ha Hn
    ipureintro
    exact ⟨by rw [hf.2.2.2]; exact hfo.1, hf.1, hf.2.1, hf.2.2.1, by rw [hf.2.2.2]; exact hfo.2⟩

/-- **The history with its eager fold, commit-le along it, is the records.** -/
theorem walHistH_walRecs (h : WalH GF) (σ : StorContents) (Hs : WalHist) (sized : Bool) :
    walHistH (GF := GF) h Hs sized ∗
        ⌜walFoldChkFrom walFresh Hs = some σ ∧ walCommitLeFrom walFresh Hs⌝ ⊢ walRecs h σ sized := by
  iintro H
  iapply (walRecs_iff_hist h σ sized).2
  iexists Hs
  iexact H

/-- (P5) **The empty prefix is synced** (the WAL's directory entry is durable, `walNamed`): the synced mark a first start's durability
invariant is allocated at. -/
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

/-- **The history across a crash** (P8, 2026-11-25; T5's `walFilesC_crash` on the history): from the crash
view (`walCrashWal`, whole operations since P8), the history `Hs` (given back), its synced mark `n`, the new
generation's lock token and the WAL directory's call permission's half, a crash prefix `j` (`n ≤ j ≤ |Hs|`)
whose read, if it succeeds, the new generation's files hold (`walFilesC`, at the area with the new
generation's WAL names). What T2's crash law's callback runs. -/
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

/-- (P5) **`Save`'s update of the history, as layer 1's** (no `WalSaveOk` asked, layer 1's `Save`
needs none; the caller's update commits at the history `walSrvHist d.H` the `Save` appended to). -/
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

/-- (P5) **`SaveSnap`'s update of the history, as layer 1's** (no premise on the base's term). -/
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

/-- (P5 (b)) **An update of the records, as one of the history** (the contract's `Save`/`SaveSnap` are over
`walHistH`; the laws over `walRecs` derive from them): the records are the history's eager fold
(`walRecs_iff_hist`), and at the commit the fold's step `hstep` gives the new records; the caller's `Q`
independent of the history. (B2, 2026-11-28) `hstep` also carries the eager fold's commit-le
(`walCommitLeFrom walFresh`, `walRecs`' since walcommitle) across `o`. -/
theorem walRecs_au_toHist (h : WalH GF) (sized : Bool) (P : StorContents → Prop)
    (f : StorContents → StorContents) (o : WalOp) (E : CoPset) (Q : IProp GF)
    (hstep : ∀ (Hs : WalHist) (σ : StorContents), walFoldChkFrom walFresh Hs = some σ →
      walCommitLeFrom walFresh Hs → P σ →
      walFoldChkFrom walFresh (Hs ++ [o]) = some (f σ) ∧ walCommitLeFrom walFresh (Hs ++ [o])) :
    (AU <{ ∃∃ (σ : StorContents), walRecs h σ sized ∗ ⌜P σ⌝ }> @ E, ∅
        <{ walRecs h (f σ) sized, COMM Q }>) ⊢
      AU <{ ∃∃ Hs : WalHist, walHistH h Hs sized }> @ E, ∅
        <{ walHistH h (Hs ++ [o]) sized, COMM Q }> := by
  iintro Hau
  iauintro
  unfold atomic_acc
  ihave Hacc := aupd_aacc $$ Hau
  unfold atomic_acc
  imod Hacc with Hacc
  isimp only [texist_cons, texist_nil, Std.Tele.app, ULift.down] at Hacc
  icases Hacc with ⟨%σ, ⟨Hr, %hok⟩, Hcl⟩
  icases (walRecs_iff_hist h σ sized).1 $$ Hr with ⟨%Hs, Hr, %hf⟩
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
    · iapply walHistH_walRecs h σ Hs sized
      isplitl [Hr]
      · iexact Hr
      · ipureintro; exact hf
    · ipureintro; exact hok
  · iintro Hr
    icases Hcl with ⟨-, Hcommit⟩
    isimp only [tforall_nil, Std.Tele.app] at Hcommit
    iapply Hcommit
    iapply walHistH_walRecs h (f σ) (Hs ++ [o]) sized
    isplitl [Hr]
    · iexact Hr
    · ipureintro; exact hstep Hs σ hf.1 hf.2 hok

/-- (P5) **`Release`'s read of the history** (`walRecs_releaseAU`'s): layer 1's lock update at the
snapshot record the witness names, the history unchanged. -/
theorem walHistH_releaseAU (h : WalH GF) (i : Nat) (m : SnapshotMetadataM) (Q : IProp GF) :
    walSnapRec h i m ∗
      (AU <{ ∃∃ (Hs : WalHist) (s : Bool), walHistH h Hs s }> @ WalFs.walAuMask, ∅
        <{ walHistH h Hs s, COMM Q }>) ⊢
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
  icases Hacc with ⟨%Hs, %s, Hr, Hcl⟩
  unfold walHistH
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
image (`walStCrashS`, `walImgS`), and `walHistH_crash` gives the crash prefix directly; nothing uses this law.
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

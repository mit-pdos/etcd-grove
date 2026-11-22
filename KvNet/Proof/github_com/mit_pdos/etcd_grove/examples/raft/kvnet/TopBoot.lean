/-
# kvnet's top level: a replica's generation, its boot and its crash (2026-11-22)

`notes/kvnet-part.md`, the last sections. A generation of a replica's machine boots **before its
program runs**, in the frame of the generation's obligation, from the Linux file extension's local
interpretation (Perennial's proposed change, branch `crash-genstart`: each generation's obligation
gets the node's extensions' local interpretation before its WP, and the crash obligation one later
credit). Stated against those shapes, so that the adequacy's obligations are these lemmas applied:

* `kvGen γ id f R`: what a generation starts from, before its boot (the first: the file extension's
  start resources, nothing in `dir`; a later one: what `kvGen_crash` gives): the cells' invariant, the
  whole legacy tree `R`/`V` with nothing logged, raft's durable state `S` and vacancy for `id`, the
  file's contents `v` holding `S` (`fileHolds`), and what the generation found at the file's names
  (`durFound`, `durFoundTmp`);
* `kvGen_boot`: the boot, at the file extension's local interpretation (kept): the switch to the
  shared mode (`Fs.osShare_ctx`), `durable`'s boot on the file's directory (`DurFs.durBoot`), raft's
  vacancy armed (`nodeVacant_arm`), the generation's file invariant (`kd_file_alloc`): `StartNode`'s
  start resource `kvStart` with the call permission of `dir`'s root, and what the crash keeps
  (`kvCrashKeep`: the invariants, the crash tokens);
* `kvGen_crash`: the crash, with one later credit: the file invariant opened with its token (the
  later on its contents stripped by the credit: `raftState` and `kdFileState` come out without one),
  `durable`'s crash lemma (`durInv_crash0`) inside it, then closed on its crashed side; the crashed
  tree's well-formedness (`crashRest_treeWf`) and the next generation's legacy tree
  (`crashRest_treeS`); the boot's choice (`kd_boot_choose`: raft's `readyCrashEnter` or `nodeCrash`).
  The next generation's `kvGen`.
-/
module

public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.BootLemmas
public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.lib.durable.Boot
public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.lib.durable.Crash
public import GooseLang.Ext.Fs.TreeSharedSwitchE

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 Fs DurFs

/-- `nroot.@a`'s mask misses `nroot.@b.@x`'s, for distinct names. -/
theorem ndot_sub_diff (a b : String) (h : a ≠ b) (x : Nat) :
    (↑(nroot.@a) : CoPset) ⊆ ⊤ \ ↑((nroot.@b).@x) := by
  intro p hp
  rw [Iris.Std.LawfulSet.mem_diff]
  refine ⟨CoPset.mem_full, fun h' => ?_⟩
  have := mask_ndot_ne' nroot a b h _ hp
  rw [Iris.Std.LawfulSet.mem_diff] at this
  exact this.2 (nclose_subseteq _ x p h')

/-- A directory of a tree is among its keys (the WAL's `mem_dom`). -/
theorem tree_mem_keys {m : Tree} {j : Ino} (h : j ∈ m) : j ∈ (GMap.toList m).map (·.1) := by
  cases he : m !! j with
  | none => have := (GMap.mem_iff _ _).1 h; rw [he] at this; cases this
  | some d => exact List.mem_map.2 ⟨(j, d), (GMap.mem_toList _ _ _).2 he, rfl⟩

section gen
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [KdStor GF]
variable [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]

attribute [local instance] kdStorageModel

/-- **A replica's generation before its boot** (see the file header), for replica `id`'s file `f`
under the roots `R`. -/
def kvGen (γ : KdNames) (id : w64) (f : DFile) (R : Roots) : IProp GF :=
  iprop(∃ (V : Hist) (S : RaftState) (v : Option GoString),
    ⌜V.2 = [] ∧ TreeWf R V.now⌝ ∗ osInv ∗ osTree (DFrac.own 1) R V ∗
    raftState γ.r.cluster id S ∗ nodeVacant γ.r.cluster id ∗ fileHolds γ S v ∗
    durFound f V.now v ∗ durFoundTmp f V.now)

/-- **What a generation's crash keeps** of its boot (see the file header): the file invariant and its
crash token, raft's arm's crash token, `durable`'s invariant and crash token, `os`'s shared
invariant. -/
def kvCrashKeep (γ : KdNames) (id : w64) (fl : KdFileNames) : IProp GF :=
  iprop(kdFileInvK γ id fl ∗ token fl.tk ∗ nodeCrashTok γ.r.cluster id fl.x ∗
    durInv fl.γd fl.df ∗ durCrashTok fl.γd ∗ osSharedInv fl.fR)

/-- **The boot** (see the file header): at the file extension's local interpretation `σ` (kept),
the generation's `kvGen` gives `StartNode`'s `kvStart` (with the whole call permission of `dir`'s
root) and what the crash keeps. -/
theorem kvGen_boot (γ : KdNames) (vs : List w64) (dir : GoString) (id : w64) (f : DFile)
    (R : Roots) (σ : OsState) (hR : RootsOk R) (hr : (f.d, f.J) ∈ R) (hd : f.d = dir)
    (hf : f.Ok) (hname : f.name = kdFileName dir id)
    (hid : 1 ≤ uint.nat id ∧ uint.nat id ≤ γ.max) :
    ⊢ kdCluster (GF := GF) γ vs -∗ kvGen γ id f R -∗ fs_interp.localCtx (extLocalGS fsExt) σ ={⊤}=∗
      fs_interp.localCtx (extLocalGS fsExt) σ ∗
      ∃ fl : KdFileNames, ⌜fl.df = f ∧ fl.fR = R⌝ ∗ kvStart γ vs dir id fl 1 ∗
        kvCrashKeep γ id fl := by
  iintro #Hcl Hg Hl
  unfold kvGen
  icases Hg with ⟨%V, %S, %v, ⟨%hV, %hwf⟩, #Hos, Ht, HrS, Hvac, #Hfh, Hdf, Hdt⟩
  -- the switch to the shared mode
  imod osShare_ctx (E := ⊤) R V σ $$ Ht Hl with ⟨Hl, #Hsh, -, Hperm, -, Hall⟩
  -- the claim on the file's directory, a root, so a directory of the tree
  have hJ : f.J ∈ (GMap.toList V.now).map (·.1) := by
    have hm := hwf.1 f.J (Reach.root _ _ hr)
    exact tree_mem_keys hm
  ihave Hall := (BigSepL.bigSepL_perm (Φ := fun j => osNames j (.except []) (DFrac.own 1)
    (namesOf V j (.except []))) (List.perm_cons_erase hJ)).1 $$ Hall
  icases Hall with ⟨Hj, -⟩
  -- durable's boot
  imod durBoot _ f R V v ⊤ hV hr (fun _ _ => CoPset.mem_full) $$ Hsh Hj Hdf Hdt
    with ⟨%γd, #Hdi, Hdh, Hds, Hdc⟩
  -- raft's vacancy armed, the generation's file invariant
  imod nodeVacant_arm γ.r.cluster id ⊤ $$ Hvac with ⟨%x, Hva, Hct⟩
  imod kd_file_alloc γ id γd f R x S v ⊤ $$ Hds HrS Hfh with ⟨%wr, %tk, #Hfi, Hwr, Htk⟩
  -- the root's call permission
  icases osCallPerms_root R f.d f.J hR hr $$ Hperm with ⟨Hcp, -⟩
  imodintro
  iframe Hl
  iexists ⟨γd, f, R, wr, tk, x⟩
  isplitr
  · ipureintro; exact ⟨rfl, rfl⟩
  isplitl [Hdh Hcp Hwr Hva]
  · unfold kvStart
    iexists S, v
    simp only
    iframe Hcl Hos Hsh Hdi Hdh Hcp Hfi Hwr Hfh Hva
    ipureintro; exact ⟨hf, hname, hid⟩
  · unfold kvCrashKeep
    simp only
    iframe Hfi Htk Hct Hdi Hdc Hsh

/-- **The crash** (see the file header): with one later credit, the crashed generation's
`kvCrashKeep`, its `crashed`, the crash's rest of the file system and the next generation's cells'
invariant give the next generation's `kvGen`. -/
theorem kvGen_crash (γ : KdNames) (vs : List w64) (id : w64) (fl : KdFileNames)
    (L' : GooseLocalGS GF) (V' : Hist) :
    ⊢ kdCluster (GF := GF) γ vs -∗ kvCrashKeep γ id fl -∗ £ 1 -∗
      crashed (hC := hG.goose_localGS.goose_crashGS) -∗
      crashRest (fun _ _ => True) (gooseOsGS (L := hG.goose_localGS)) (gooseOsGS (L := L')) []
        false V' -∗
      osInv (L := L') ={⊤}=∗
      kvGen (hG := ⟨hG.goose_globalGS, L'⟩) γ id fl.df fl.fR := by
  iintro #Hcl Hk Hlc #Hcr Hrest #Hos'
  unfold kvCrashKeep
  icases Hk with ⟨#Hfi, Htk, Hct, #Hdi, Hdc, #Hsh⟩
  -- the file invariant, opened with its token; the credit strips the later on its contents
  unfold kdFileInvK
  imod inv_acc (E := ⊤) (fun _ _ => CoPset.mem_full) $$ Hfi with ⟨Hb, Hclose⟩
  imod lc_fupd_elim_later $$ Hlc Hb with Hb
  iunfold kdFileBody at Hb
  icases Hb with ⟨%S, %s, %pb, Hds, Hwr, Hb⟩
  icases Hb with (⟨HrS, Hfs⟩ | ⟨-, Htk'⟩)
  rotate_left
  · iexfalso; iapply token_exclusive $$ Htk Htk'
  -- durable's crash lemma, inside it
  imod durInv_crash0 (fun _ _ => True) hG.goose_localGS L' fl.γd fl.df fl.fR false V' s
    (⊤ \ ↑(kdRepN.@(uint.nat id))) (ndot_sub_diff "durable" "kvdurable_rep" (by decide) _)
    (ndot_sub_diff "osfsShared" "kvdurable_rep" (by decide) _) $$ Hdi Hcr Hdc Hds Hsh Hrest
    with ⟨%v, %D', ⟨%hv, -⟩, Hds, Hf, Ht, Hrest⟩
  imod Hclose $$ [Hds Hwr Htk] with -
  · inext
    iunfold kdFileBody
    iexists S, s, pb
    iframe Hds Hwr
    iright
    iframe Hcr Htk
  -- the crashed tree, well formed; the next generation's legacy tree
  imod crashRest_treeWf (fun _ _ => True) hG.goose_localGS L' D' false V' fl.fR ⊤ (fun _ _ => CoPset.mem_full)
    $$ Hsh Hrest with ⟨%hwf, Hrest⟩
  imod crashRest_treeS (fun _ _ => True) hG.goose_localGS L' D' V' fl.fR ⊤ (fun _ _ => CoPset.mem_full)
    $$ Hsh Hrest with ⟨%hV', Ht', -⟩
  -- the boot's choice
  unfold kdCluster
  icases Hcl with ⟨#HisC, -⟩
  imod kd_boot_choose γ id S s pb fl.x v ⊤ (fun _ _ => CoPset.mem_full) hv $$ HisC Hcr Hct HrS Hfs
    with ⟨%S', HrS, Hvac, #Hfh⟩
  imodintro
  unfold kvGen
  iexists V', S', v
  iframe Hos' Ht' HrS Hvac Hf Ht
  isplitr
  · ipureintro; exact ⟨hV', hwf⟩
  -- (`fileHolds` names no local ghost state: the same at `L'`)
  unfold fileHolds kdSnapCert
  iexact Hfh

/-- No file holds what a node at the initial state holds (kvdurable's `kdEmpty_holds`). -/
theorem kvEmpty_holds : StorageHolds RaftState.init (kdContents none) := by
  unfold StorageHolds
  refine ⟨Int.le_refl _, ?_, ?_, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp [plogTermAt, RaftState.init, kdContents, kdEmpty]
  · rfl
  · simp [StorContents.b, StorContents.commit, kdContents, kdEmpty]
  · simp [StorContents.commit, RaftState.init, kdContents, kdEmpty]
  · simp [StorContents.commit, RaftState.init, kdContents, kdEmpty]
  · intro sv h; simp [kdContents, kdEmpty] at h
  · intro h; exact absurd rfl h

/-- No file holds the initial durable state. -/
theorem fileHolds_init (γ : KdNames) : ⊢ fileHolds (GF := GF) γ RaftState.init none := by
  unfold fileHolds
  iexists none
  isplitr
  · ipureintro; exact ⟨rfl, fun _ h => absurd h (by simp), kvEmpty_holds⟩
  · iintro %f %h; cases h

/-- **The first generation** (see the file header): the file extension's start resources of a
machine whose file system `st` starts as on disk (`FsInit`: the tree `st.fs.treeDur`, nothing logged),
with neither the file nor its temporary in its directory, and the id's durable state at
`RaftState.init` with its vacancy (the cluster's allocation), give the first generation's `kvGen`. -/
theorem kvGen_first (γ : KdNames) (id : w64) (f : DFile) (st : OsState) (E : CoPset)
    (hst : FsInit st) (hb : st.fs.treeDur.entry f.J f.b = none)
    (ht : st.fs.treeDur.entry f.J f.tb = none) :
    ⊢ osInv (GF := GF) -∗ osTree (DFrac.own 1) st.fs.roots (st.fs.treeDur, []) -∗
      raftState γ.r.cluster id RaftState.init -∗ nodeVacant γ.r.cluster id ={E}=∗
      kvGen γ id f st.fs.roots := by
  iintro #Hos Ht HrS Hvac
  imodintro
  unfold kvGen
  iexists (st.fs.treeDur, []), RaftState.init, none
  have hnow : Hist.now (st.fs.treeDur, ([] : List Fs.LogEntry)) = st.fs.treeDur := rfl
  iframe Hos Ht HrS Hvac
  isplitr
  · ipureintro; exact ⟨rfl, by rw [hnow]; exact hst.2.2.2.2.1⟩
  isplitr
  · iapply fileHolds_init
  rw [hnow]
  isplitr
  · unfold durFound; rw [hb]; ipureintro; rfl
  · unfold durFoundTmp; rw [ht]; iempintro

omit [KdStor GF] in
/-- **A generation's `kvGen` names no storage registry** (`KdStor`, per generation: its records name
the generation's heap): the same at any registry's name. -/
theorem kvGen_stor (k1 k2 : KdStor GF) (γ : KdNames) (id : w64) (f : DFile) (R : Roots) :
    (letI : KdStor GF := k1; kvGen (GF := GF) γ id f R) ⊢
      (letI : KdStor GF := k2; kvGen (GF := GF) γ id f R) := by
  unfold kvGen fileHolds kdSnapCert
  iintro H
  iexact H

omit [KdStor GF] in
/-- **A generation's storage registry** (`KdStor`): a fresh name, its invariant with no wrapper
registered. -/
theorem kdStor_alloc (E : CoPset) :
    ⊢ |={E}=> ∃ k : KdStor GF, letI : KdStor GF := k; kdStorInv (GF := GF) := by
  imod ghost_map_alloc_empty (GF := GF) (K := Loc) (V := KdStorRecT) with ⟨%γs, Hm⟩
  imod inv_alloc kdStorN E (letI : KdStor GF := ⟨γs⟩; kdStorInvBody (GF := GF)) $$ [Hm] with #Hi
  · inext
    unfold kdStorInvBody
    iexists ∅
    iframe Hm
    iapply BigSepM.bigSepM_empty.2
    itrivial
  imodintro
  iexists ⟨γs⟩
  unfold kdStorInv
  iexact Hi

end gen

end raft_kvnet
end EtcdGrove
end Perennial

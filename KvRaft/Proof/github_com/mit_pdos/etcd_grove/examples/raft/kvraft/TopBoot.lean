/-
# kvraft's top level: a replica's generation, its boot and its crash (2026-11-22)

`notes/kvraft-part.md`, the last sections. A generation of a replica's machine boots **before its
program runs**, in the frame of the generation's obligation (`Net.CrashBootWp`: the crash obligation
gets one later credit). Stated against those shapes, so that the adequacy's obligations are these
lemmas applied:

* `kvGen γ id f R` (`kvGenAt` at the generation's first tree `V`): what a generation starts from,
  before its boot (the first: the file extension's start resources, nothing in `dir`; a later one:
  what `kvGen_crash` gives): the cells' invariant, the tree's shared invariant with nothing logged,
  half of the call permission of `dir`'s root and the claim on **only the file's two names** (the
  file's and its temporary's), raft's durable state `S` and vacancy for `id`, the file's contents `v`
  holding `S` (`fileHolds`), and what the generation found at the file's names (`durFound`,
  `durFoundTmp`). The rest of the directory's claim and the call permission's other half
  (`kvDirRest`) go to the caller of `kvGen_first`/`kvGen_crash`, for another durable file in the same
  directory (kvraft-udp's `udp-boot-<id>`, `kvBootFileName`, whose names are not the file's:
  `kvBoot_names_fresh`; its claim out of the rest by `osNames_take2`); kvraft's own top level drops it;
* `kvGen_boot`: the boot: `durable`'s boot on the file's names (`DurFs.durBootOnly`), raft's
  vacancy armed (`nodeVacant_arm`), the generation's file invariant (`kd_file_alloc`): `StartNode`'s
  start resource `kvStart` with half the call permission of `dir`'s root, and what the crash keeps
  (`kvCrashKeep`: the invariants, the crash tokens);
* `kvGen_crash`: the crash, with one later credit: the file invariant opened with its token (the
  later on its contents stripped by the credit: `raftState` and `kdFileState` come out without one),
  `durable`'s crash lemma (`durInv_crash0`) inside it, then closed on its crashed side; the crashed
  tree's well-formedness (`crashRest_treeWf`) and the next generation's shared view
  (`crashRest_treeS`), split (`kvShared_split`); the boot's choice (`kd_boot_choose`: raft's
  `readyCrashEnter` or `nodeCrash`). The next generation's `kvGenAt` at the crash's tree, its
  `kvDirRest`, and the crash's rest of the file system after the file's (`crashRest` with the files
  `durable` took, named at the file's two names), so that another durable file's crash lemma can
  run (kvraft-udp's boot file: `durInv_crash`, whose premise on the taken files holds by unique naming).
-/
module

public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.BootLemmas
public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.lib.durable.Boot
public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.lib.durable.Crash
public import GooseLang.Ext.Fs.TreeShared

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvraft

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
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [KdStor GF]
variable [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]

attribute [local instance] kdStorageModel

/-- **A replica's generation before its boot, at its first tree `V`** (see the file header), for
replica `id`'s file `f` under the roots `R`: the claim on only the file's two names, half the call
permission of its directory's root. -/
def kvGenAt (γ : KdNames) (id : w64) (f : DFile) (R : Roots) (V : Hist) : IProp GF :=
  iprop(∃ (S : RaftState) (v : Option GoString),
    ⌜V.2 = []⌝ ∗ osInv ∗ osSharedInv R ∗ osCallPerm (callKey R f.d) (1 : Qp).half ∗
    osNames f.J (.only [f.b, f.tb]) (DFrac.own 1) (namesOf V f.J (.only [f.b, f.tb])) ∗
    raftState γ.r.cluster id S ∗ nodeVacant γ.r.cluster id ∗ fileHolds γ S v ∗
    durFound f V.now v ∗ durFoundTmp f V.now)

/-- **A replica's generation before its boot** (see the file header): `kvGenAt` at some first tree. -/
def kvGen (γ : KdNames) (id : w64) (f : DFile) (R : Roots) : IProp GF :=
  iprop(∃ V : Hist, kvGenAt γ id f R V)

theorem kvGen_of (γ : KdNames) (id : w64) (f : DFile) (R : Roots) (V : Hist) :
    kvGenAt (GF := GF) γ id f R V ⊢ kvGen γ id f R := by
  unfold kvGen
  iintro H
  iexists V
  iexact H

/-- **The rest of the file's directory** at a generation's first tree `V` (see the file header): the
claim on every name of `f`'s directory but the file's two, the other half of the call permission of
its root, and the shared invariant. -/
def kvDirRest (f : DFile) (R : Roots) (V : Hist) : IProp GF :=
  iprop(osSharedInv R ∗ osCallPerm (callKey R f.d) (1 : Qp).half ∗
    osNames f.J (.except [f.b, f.tb]) (DFrac.own 1) (namesOf V f.J (.except [f.b, f.tb])))

omit sem package_sem raft_sem [KdStor GF] in
/-- **Two names out of a claim `.except X`**: the claim on them, and `.except (X ++ [b, tb])`. -/
theorem osNames_take2 (R : Roots) (V : Hist) (j : Ino) (X : List GoString) (b tb : GoString)
    (hb : b ∉ X) (htb : tb ∉ X) (E : CoPset) (hE : ↑osShN ⊆ E) :
    ⊢ osSharedInv (GF := GF) R -∗ osNames j (.except X) (DFrac.own 1) (namesOf V j (.except X)) ={E}=∗
      osNames j (.only [b, tb]) (DFrac.own 1) (namesOf V j (.only [b, tb])) ∗
      osNames j (.except (X ++ [b, tb])) (DFrac.own 1) (namesOf V j (.except (X ++ [b, tb]))) := by
  iintro #Hsh H
  imod osNames_split R j (.except X) [b, tb] _ hE $$ Hsh H with ⟨Hi, Hd⟩
  have hi : (NameSet.except X).inter [b, tb] = .only [b, tb] := by
    simp [NameSet.inter, hb, htb]
  have hd : (NameSet.except X).diff [b, tb] = .except (X ++ [b, tb]) := rfl
  rw [namesOf_restrict V j (.except X) ((NameSet.except X).inter [b, tb]) (fun c hc => by
      rw [hi] at hc
      simp only [NameSet.Mem, List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
      rcases hc with rfl | rfl
      · exact hb
      · exact htb),
    namesOf_restrict V j (.except X) ((NameSet.except X).diff [b, tb]) (fun c hc => by
      simp only [NameSet.diff, NameSet.Mem, List.mem_append, not_or] at hc ⊢
      exact hc.1), hi, hd]
  imodintro
  iframe Hi Hd

omit sem package_sem raft_sem [KdStor GF] in
/-- **A generation's shared view, split at the file** (see the file header): the shared invariant,
half the call permission of the file's directory's root, the claim on the file's two names, and the
rest (`kvDirRest`). -/
theorem kvShared_split (f : DFile) (R : Roots) (V : Hist) (E : CoPset) (hR : RootsOk R)
    (hr : (f.d, f.J) ∈ R) (hwf : TreeWf R V.now) (hE : ↑osShN ⊆ E) :
    ⊢ osShared (GF := GF) R V ={E}=∗
      osSharedInv R ∗ osCallPerm (callKey R f.d) (1 : Qp).half ∗
      osNames f.J (.only [f.b, f.tb]) (DFrac.own 1) (namesOf V f.J (.only [f.b, f.tb])) ∗
      kvDirRest f R V := by
  iintro Ht
  unfold osShared
  icases Ht with ⟨#Hsh, -, Hperm, -, Hall⟩
  -- the claim on the file's directory, a root, so a directory of the tree
  have hJ : f.J ∈ (GMap.toList V.now).map (·.1) := by
    have hm := hwf.1 f.J (Reach.root _ _ hr)
    exact tree_mem_keys hm
  ihave Hall := (BigSepL.bigSepL_perm (Φ := fun j => osNames j (.except []) (DFrac.own 1)
    (namesOf V j (.except []))) (List.perm_cons_erase hJ)).1 $$ Hall
  icases Hall with ⟨Hj, -⟩
  imod osNames_take2 R V f.J [] f.b f.tb List.not_mem_nil List.not_mem_nil E hE $$ Hsh Hj
    with ⟨Hj, Hrest⟩
  rw [List.nil_append]
  -- the root's call permission, in halves
  icases osCallPerms_root R f.d f.J hR hr $$ Hperm with ⟨Hcp, -⟩
  have e : (osCallPerm (callKey R f.d) 1 : IProp GF) ⊣⊢
      osCallPerm (callKey R f.d) (1 : Qp).half ∗ osCallPerm (callKey R f.d) (1 : Qp).half := by
    have h := osCallPerm_split (GF := GF) (callKey R f.d) (1 : Qp).half (1 : Qp).half
    rw [Qp.half_add_half] at h
    exact h
  icases e.1 $$ Hcp with ⟨Hc1, Hc2⟩
  imodintro
  unfold kvDirRest
  iframe Hsh Hj Hrest Hc1 Hc2

/-- **What a generation's crash keeps** of its boot (see the file header): the file invariant and its
crash token, raft's arm's crash token, `durable`'s invariant and crash token, `os`'s shared
invariant. -/
def kvCrashKeep (γ : KdNames) (id : w64) (fl : KdFileNames) : IProp GF :=
  iprop(kdFileInvK γ id fl ∗ token fl.tk ∗ nodeCrashTok γ.r.cluster id fl.x ∗
    durInv fl.γd fl.df ∗ durCrashTok fl.γd ∗ osSharedInv fl.fR ∗
    ⌜RootsOk fl.fR ∧ (fl.df.d, fl.df.J) ∈ fl.fR⌝)

/-- **The boot** (see the file header): the generation's `kvGen` gives `StartNode`'s `kvStart` (with
the half of the call permission of `dir`'s root that `kvGen` holds) and what the crash keeps. -/
theorem kvGen_boot (γ : KdNames) (vs : List w64) (dir : GoString) (id : w64) (f : DFile)
    (R : Roots) (hR : RootsOk R) (hr : (f.d, f.J) ∈ R) (hd : f.d = dir)
    (hf : f.Ok) (hname : f.name = kdFileName dir id)
    (hid : 1 ≤ uint.nat id ∧ uint.nat id ≤ γ.max) :
    ⊢ kdCluster (GF := GF) γ vs -∗ kvGen γ id f R ={⊤}=∗
      ∃ fl : KdFileNames, ⌜fl.df = f ∧ fl.fR = R⌝ ∗ kvStart γ vs dir id fl (1 : Qp).half ∗
        kvCrashKeep γ id fl := by
  iintro #Hcl Hg
  unfold kvGen kvGenAt
  icases Hg with ⟨%V, %S, %v, %hV, #Hos, #Hsh, Hcp, Hj, HrS, Hvac, #Hfh, Hdf, Hdt⟩
  -- durable's boot, on the file's names
  imod durBootOnly _ f R V v ⊤ hV hr (fun _ _ => CoPset.mem_full) $$ Hsh Hj Hdf Hdt
    with ⟨%γd, #Hdi, Hdh, Hds, Hdc⟩
  -- raft's vacancy armed, the generation's file invariant
  imod nodeVacant_arm γ.r.cluster id ⊤ $$ Hvac with ⟨%x, Hva, Hct⟩
  imod kd_file_alloc γ id γd f R x S v ⊤ $$ Hds HrS Hfh with ⟨%wr, %tk, #Hfi, Hwr, Htk⟩
  imodintro
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
    ipureintro; exact ⟨hR, hr⟩

/-- **The crash** (see the file header): with one later credit, the crashed generation's
`kvCrashKeep`, its `crashed`, the crash's rest of the file system and the next generation's cells'
invariant give the next generation's `kvGenAt` at the crash's tree `V'`, the rest of the file's
directory (`kvDirRest`), and the crash's rest of the file system after the file's (its files taken
`D`, named at the file's two names only), for another durable file's crash lemma (`durInv_crash`,
e.g. kvraft-udp's boot file in the same directory); kvraft's own top level drops the last two. -/
theorem kvGen_crash (γ : KdNames) (vs : List w64) (id : w64) (fl : KdFileNames)
    (L' : GooseLocalGS GF) (V' : Hist) :
    ⊢ kdCluster (GF := GF) γ vs -∗ kvCrashKeep γ id fl -∗ £ 1 -∗
      crashed (hC := hG.goose_localGS.goose_crashGS) -∗
      crashRest (fun _ _ => True) (gooseOsGS (L := hG.goose_localGS)) (gooseOsGS (L := L')) []
        false V' -∗
      osInv (L := L') ={⊤}=∗
      kvGenAt (hG := ⟨hG.goose_globalGS, L'⟩) γ id fl.df fl.fR V' ∗
        kvDirRest (hG := ⟨hG.goose_globalGS, L'⟩) fl.df fl.fR V' ∗
        ∃ D : List Ino, ⌜∀ i ∈ D, V'.now.entry fl.df.J fl.df.b = some (.file i) ∨
            V'.now.entry fl.df.J fl.df.tb = some (.file i)⌝ ∗
          crashRest (fun _ _ => True) (gooseOsGS (L := hG.goose_localGS)) (gooseOsGS (L := L')) D
            true V' := by
  iintro #Hcl Hk Hlc #Hcr Hrest #Hos'
  unfold kvCrashKeep
  icases Hk with ⟨#Hfi, Htk, Hct, #Hdi, Hdc, #Hsh, %hRr⟩
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
    with ⟨%v, %D', ⟨%hv, %hD'⟩, Hds, Hf, Ht, Hrest⟩
  imod Hclose $$ [Hds Hwr Htk] with -
  · inext
    iunfold kdFileBody
    iexists S, s, pb
    iframe Hds Hwr
    iright
    iframe Hcr Htk
  -- the crashed tree, well formed; the next generation's shared view
  imod crashRest_treeWf (fun _ _ => True) hG.goose_localGS L' D' false V' fl.fR ⊤ (fun _ _ => CoPset.mem_full)
    $$ Hsh Hrest with ⟨%hwf, Hrest⟩
  imod crashRest_treeS (fun _ _ => True) hG.goose_localGS L' D' V' fl.fR ⊤ (fun _ _ => CoPset.mem_full)
    $$ Hsh Hrest with ⟨%hV', Ht', Hrest⟩
  imod kvShared_split (hG := ⟨hG.goose_globalGS, L'⟩) fl.df fl.fR V' ⊤ hRr.1 hRr.2 hwf
    (fun _ _ => CoPset.mem_full) $$ Ht' with ⟨#Hsh', Hcp, Hj, Hdr⟩
  -- the boot's choice
  unfold kdCluster
  icases Hcl with ⟨#HisC, -⟩
  imod kd_boot_choose γ id S s pb fl.x v ⊤ (fun _ _ => CoPset.mem_full) hv $$ HisC Hcr Hct HrS Hfs
    with ⟨%S', HrS, Hvac, #Hfh⟩
  imodintro
  isplitl [Hcp Hj HrS Hvac Hf Ht]
  · unfold kvGenAt
    iexists S', v
    iframe Hos' Hsh' Hcp Hj HrS Hvac Hf Ht
    isplitr
    · ipureintro; exact hV'
    -- (`fileHolds` names no local ghost state: the same at `L'`)
    unfold fileHolds kdSnapCert
    iexact Hfh
  iframe Hdr
  iexists D'
  iframe Hrest
  ipureintro; exact hD'

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
with neither the file nor its temporary in its directory, a root, and the id's durable state at
`RaftState.init` with its vacancy (the cluster's allocation), give the first generation's `kvGenAt`,
and the rest of the file's directory (`kvDirRest`). -/
theorem kvGen_first (γ : KdNames) (id : w64) (f : DFile) (st : OsState) (E : CoPset)
    (hst : FsInit st) (hb : st.fs.treeDur.entry f.J f.b = none)
    (ht : st.fs.treeDur.entry f.J f.tb = none) (hr : (f.d, f.J) ∈ st.fs.roots)
    (hE : ↑osShN ⊆ E) :
    ⊢ osInv (GF := GF) -∗ osShared st.fs.roots (st.fs.treeDur, []) -∗
      raftState γ.r.cluster id RaftState.init -∗ nodeVacant γ.r.cluster id ={E}=∗
      kvGenAt γ id f st.fs.roots (st.fs.treeDur, []) ∗
        kvDirRest f st.fs.roots (st.fs.treeDur, []) := by
  iintro #Hos Ht HrS Hvac
  have hnow : Hist.now (st.fs.treeDur, ([] : List Fs.LogEntry)) = st.fs.treeDur := rfl
  imod kvShared_split f st.fs.roots (st.fs.treeDur, []) E hst.2.2.2.1 hr
    (by rw [hnow]; exact hst.2.2.2.2.1) hE $$ Ht with ⟨#Hsh, Hcp, Hj, Hdr⟩
  imodintro
  isplitl [Hcp Hj HrS Hvac]
  · unfold kvGenAt
    iexists RaftState.init, none
    iframe Hos Hsh Hcp Hj HrS Hvac
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply fileHolds_init
    rw [hnow]
    isplitr
    · unfold durFound; rw [hb]; ipureintro; rfl
    · unfold durFoundTmp; rw [ht]; iempintro
  · iexact Hdr

omit [KdStor GF] in
/-- **A generation's `kvGen` names no storage registry** (`KdStor`, per generation: its records name
the generation's heap): the same at any registry's name. -/
theorem kvGen_stor (k1 k2 : KdStor GF) (γ : KdNames) (id : w64) (f : DFile) (R : Roots) :
    (letI : KdStor GF := k1; kvGen (GF := GF) γ id f R) ⊢
      (letI : KdStor GF := k2; kvGen (GF := GF) γ id f R) := by
  unfold kvGen kvGenAt fileHolds kdSnapCert
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

/-! ## A second file in the replica's directory -/

/-- kvraft-udp's boot file of replica `id` (Go's `BootFileOf`, `examples/raft/kvraft/nodeudp.go`):
`dir/udp-boot-<id>`. -/
def kvBootFileName (dir : GoString) (id : w64) : GoString :=
  dir ++ go!"/udp-boot-" ++ decimalB (uint.nat id)

/-- Its `durable` file: `dir/udp-boot-<id>`, `dir`'s root inode `J`. -/
def kvBootDFile (dir : GoString) (J : Ino) (id : w64) : DFile :=
  ⟨dir, J, go!"udp-boot-" ++ decimalB (uint.nat id)⟩

/-- Two strings whose first bytes differ differ, whatever follows. -/
theorem append_ne_of_head (a b x y : GoString) (h : a.head? ≠ b.head?) (ha : a ≠ []) (hb : b ≠ []) :
    a ++ x ≠ b ++ y := by
  intro e
  have he := congrArg List.head? e
  cases a with
  | nil => exact ha rfl
  | cons c a =>
    cases b with
    | nil => exact hb rfl
    | cons d b =>
      simp only [List.cons_append, List.head?_cons, Option.some.injEq] at he h
      exact h (by rw [he])

/-- **The boot file's names are not the storage file's** (`replica-…`: kvraft's file, `FileOf`): neither
the boot file's base name nor its temporary's is among the storage file's two names, whatever the
ids. -/
theorem kvBoot_names_fresh (f f' : DFile) (x y : GoString) (hf : f.b = go!"replica-" ++ x)
    (hf' : f'.b = go!"udp-boot-" ++ y) :
    f'.b ∉ [f.b, f.tb] ∧ f'.tb ∉ [f.b, f.tb] := by
  have hu : (go!"udp-boot-" : GoString).head? ≠ (go!"replica-" : GoString).head? := by decide
  have hu' : (go!"udp-boot-" : GoString).head? ≠ (go!".durable-" : GoString).head? := by decide
  have hd : (go!".durable-" : GoString).head? ≠ (go!"replica-" : GoString).head? := by decide
  have n1 : (go!"udp-boot-" : GoString) ≠ [] := by decide
  have n2 : (go!"replica-" : GoString) ≠ [] := by decide
  have n3 : (go!".durable-" : GoString) ≠ [] := by decide
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or, DFile.tb, hf, hf']
  refine ⟨⟨append_ne_of_head _ _ _ _ hu n1 n2, append_ne_of_head _ _ _ _ hu' n1 n3⟩,
    append_ne_of_head _ _ _ _ hd n3 n2, fun h => ?_⟩
  exact append_ne_of_head _ _ _ _ hu n1 n2 (List.append_cancel_left h)

/-- **The two files' paths differ** (`FileOf` and `BootFileOf`, the string forms). -/
theorem kdFileName_ne_boot (dir : GoString) (id id' : w64) :
    kdFileName dir id ≠ kvBootFileName dir id' := by
  have e1 : (go!"/replica-" : GoString) = go!"/" ++ go!"replica-" := by decide
  have e2 : (go!"/udp-boot-" : GoString) = go!"/" ++ go!"udp-boot-" := by decide
  have hu : (go!"replica-" : GoString).head? ≠ (go!"udp-boot-" : GoString).head? := by decide
  have n1 : (go!"udp-boot-" : GoString) ≠ [] := by decide
  have n2 : (go!"replica-" : GoString) ≠ [] := by decide
  unfold kdFileName kvBootFileName
  rw [e1, e2]
  simp only [List.append_assoc]
  intro h
  exact append_ne_of_head _ _ _ _ hu n2 n1 (List.append_cancel_left (List.append_cancel_left h))

end kvraft
end EtcdGrove
end Perennial

/-
The worlds of the Linux file extension's specs (`Impl.lean`, `Ghost.lean`): the resources of a
generation's ghost state, the invariant of the mapped cells, the steps that leave the tree alone
(`TreeFrame`, the data operations), the world an operation's proof works with and the lifting of a
step (`wp_os_step` for the data operations, `wp_fs_stepT` for every operation, with the tree's
world), and the tree's resources and their laws. Untrusted.

**Resources** (all of the generation's ghost state `gooseOsGS`):
* `osByte i b dq (x, cs)`: byte `b` of the page cache of the file of inode `i` is `x`, and its crash
  candidates are `cs` (a crash leaves it one of their values); fractional. `osBytes i off dq xs`:
  the bytes from `off` on.
* `osMeta i dq m`: the file of inode `i` exists and `m` (`OsMeta`) says what the ghost state knows of
  it. Fractional; a change, a sync and (un)mapping need it whole.
* `osFd fd dq d`: `fd` is open, on the file `d.ino`, with `d`'s access mode; fractional.
* `osTree dq V`: (a fraction of) the tree's history `V`. `osDir j dq g`: the directory of inode `j`,
  as `g` says: a fraction of the history, of which `g` is `j`'s view. `osDirFd fd dq x`: `fd` is an
  open directory fd, on `x.1`, its read at `x.2`. `osCall t s q`: the call on a path `t` is in flight,
  begun when the log had `s` entries.
* `osInv`: the invariant of the generation's mapped cells; every spec takes it, with `↑osN ⊆ E`.
-/
module

public import GooseLang.Ext.Fs.Cells
public import GooseLang.Ext.Fs.Facts
public import Perennial.Golang.Defn.PostLang
public import Iris.Instances.Lib.Invariants

@[expose] public section

noncomputable section

namespace Perennial
namespace Fs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode
open goose_heap

/-! ## What the extension holds of the changes in flight -/

section tokres
variable {GF : BundledGFunctors} (hL : OsGS GF)

/-- A byte the client holds a fraction of is under no change in flight: the change would hold all
of it. -/
theorem tokRes_byte_free {st : OsState} {Γb Γm Γf Γt} (hcoh : OsCoh st Γb Γm Γf Γt)
    {i : Ino} {b : Nat} {dq : DFrac} {x : ByteG} (hx : Γb !! (i, b) = some x) :
    ⊢ tokRes hL Γt -∗ gElem hL hL.γb (i, b) dq x -∗ ⌜¬ InflightAt st i b⌝ := by
  iintro Htok Hb
  by_cases hin : InflightAt st i b
  · obtain ⟨t, c, ht, hci, haff⟩ := hin
    obtain ⟨ti, hti, his⟩ := coh_tok hcoh ht
    obtain ⟨f, hf, hb, -⟩ := coh_byte hcoh hx
    obtain ⟨f', hf', -, -, hlen⟩ := hcoh.tok_file t ti hti
    obtain ⟨hino, -, hlo, hhi, -⟩ := his
    rw [← hino, hci, hf] at hf'; cases hf'
    rw [hlo, hhi] at haff
    simp only [inRange, Bool.and_eq_true, decide_eq_true_eq] at haff
    have hk : b - ti.lo < ti.saved.length := by rw [hlen]; omega
    unfold tokRes
    icases BigSepM.bigSepM_lookup (Φ := fun (_t : Nat) (ti : TokInfo) =>
      iprop(gElem hL hL.γm ti.ino (DFrac.own 1) ti.meta ∗
        bytesG hL ti.ino ti.lo (DFrac.own 1) ti.saved))
      hti $$ Htok with ⟨-, Hs⟩
    unfold bytesG
    icases BigSepL.bigSepL_lookup (Φ := fun k (x : ByteG) =>
      gElem hL hL.γb (ti.ino, ti.lo + k) (DFrac.own 1) x) (List.getElem?_eq_getElem hk) $$ Hs with Hs
    rw [show ti.lo + (b - ti.lo) = b by omega, ← hino, hci]
    icases gElem_valid_2 hL _ _ _ _ _ _ $$ Hs Hb with %Hv
    exact absurd (DFrac.valid_own_op Hv.1) (by simp)
  · ipureintro; exact hin

/-- Any fraction of a file's `OsMeta`: no change is in flight on it (a change holds it whole). -/
theorem tokRes_meta_whole {Γt : GMap Nat TokInfo} {i : Ino} {dq : DFrac} {m : OsMeta} :
    ⊢ tokRes hL Γt -∗ gElem hL hL.γm i dq m -∗ ⌜∀ t ti, Γt !! t = some ti → ti.ino ≠ i⌝ := by
  iintro Htok Hm
  iapply pure_forall.2; iintro %t
  iapply pure_forall.2; iintro %ti
  by_cases hti : Γt !! t = some ti
  · by_cases hp : ti.ino = i
    · unfold tokRes
      icases BigSepM.bigSepM_lookup (Φ := fun (_t : Nat) (ti : TokInfo) =>
        iprop(gElem hL hL.γm ti.ino (DFrac.own 1) ti.meta ∗
          bytesG hL ti.ino ti.lo (DFrac.own 1) ti.saved))
        hti $$ Htok with ⟨Hs, -⟩
      rw [hp]
      icases gElem_valid_2 hL _ _ _ _ _ _ $$ Hs Hm with %Hv
      exact absurd (DFrac.valid_own_op Hv.1) (by simp)
    · ipureintro; exact fun _ => hp
  · ipureintro; exact fun h => absurd h hti

end tokres

/-! ## Resources -/

section resources
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]

/-- The ghost state of the generation. -/
abbrev gooseOsGS : OsGS GF := extLocalGS fsExt

theorem os_local_ctx_eq (st : OsState) :
    ExtInterp.localCtx (E := fsExt) (extLocalGS fsExt) st ⊣⊢ osCtx (gooseOsGS (L := L)) st :=
  .rfl

/-- Byte `b` of the file `i` is `x.1` in the page cache, and its crash candidates are `x.2`. -/
def osByte (i : Ino) (b : Nat) (dq : DFrac) (x : ByteG) : IProp GF :=
  gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γb (i, b) dq x

/-- The bytes of the file `i` from `off` on are `xs`. -/
def osBytes (i : Ino) (off : Nat) (dq : DFrac) (xs : List (ByteG)) : IProp GF :=
  bytesG (gooseOsGS (L := L)) i off dq xs

/-- The file of inode `i` exists, as `m` says. -/
def osMeta (i : Ino) (dq : DFrac) (m : OsMeta) : IProp GF :=
  gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γm i dq m

/-- The fd `fd` is open, as `d` says. -/
def osFd (fd : w64) (dq : DFrac) (d : OsFd) : IProp GF :=
  gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γf fd dq d

/-- The change in flight `t`, as `ti` says. -/
def osTok (t : Nat) (ti : TokInfo) : IProp GF :=
  gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γt t (DFrac.own 1) ti

instance osByte_timeless (i : Ino) (b : Nat) (dq : DFrac) (x : ByteG) :
    Timeless (osByte (L := L) i b dq x) := by unfold osByte; infer_instance
instance osMeta_timeless (i : Ino) (dq : DFrac) (m : OsMeta) :
    Timeless (osMeta (L := L) i dq m) := by unfold osMeta; infer_instance
instance osFd_timeless (fd : w64) (dq : DFrac) (d : OsFd) :
    Timeless (osFd (L := L) fd dq d) := by unfold osFd; infer_instance

/-- The namespace of the invariant of the mapped cells. -/
def osN : Namespace := nroot .@ "osfs"

/-- The invariant of the generation's mapped cells: the extension's share of each (`cellsRes`), for
the view the state interpretation's half of the ghost variable names. -/
def osInv : IProp GF :=
  inv osN iprop(∃ (cv : GMap Loc (Option w8 × Bool)) (n : Nat),
    gVar (gooseOsGS (L := L)) (1 : Qp).half (cv, n) ∗ cellsRes cv)

instance osInv_persistent : Persistent (osInv (L := L)) := by unfold osInv; infer_instance

/-- The invariant of the mapped cells, from the start resources' half of its ghost variable. -/
theorem osInv_alloc (E : CoPset) :
    ⊢ gVar (gooseOsGS (L := L)) (1 : Qp).half ((∅ : GMap Loc (Option w8 × Bool)), 0) ={E}=∗
      osInv (L := L) := by
  iintro Hv
  unfold osInv
  iapply inv_alloc
  inext
  iexists ∅, 0
  iframe Hv
  unfold cellsRes; iapply BigSepM.bigSepM_empty.2; iempintro

/-- (A fraction `dq` of) the tree's roots `R` and history `V`: the tree the generation booted with,
and the entries logged since. -/
def osTree (dq : DFrac) (R : Roots) (V : Hist) : IProp GF :=
  gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γd () dq (R, V)

/-- The directory of inode `j`, as `g` says: a fraction of the history, of which `g` is `j`'s view.
-/
def osDir (j : Ino) (dq : DFrac) (g : DirG) : IProp GF :=
  iprop(∃ (R : Roots) (V : Hist), osTree dq R V ∗ ⌜g = dview V j⌝)

/-- The directory fd `fd`, on `x.1`, its read at `x.2`. -/
def osDirFd (fd : w64) (dq : DFrac) (x : Ino × DirPh) : IProp GF :=
  gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γdf fd dq x

/-- The call on a path `t` is in flight, begun when the log had `s` entries; the state
interpretation holds the fraction `q` of the history for it, which its step gives back. -/
def osCall (t : Nat) (s : Nat) (q : Qp) : IProp GF :=
  gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γc t (DFrac.own 1) (s, q)

instance osTree_timeless (dq : DFrac) (R : Roots) (V : Hist) :
    Timeless (osTree (L := L) dq R V) := by
  unfold osTree; infer_instance
instance osDir_timeless (j : Ino) (dq : DFrac) (g : DirG) : Timeless (osDir (L := L) j dq g) := by
  unfold osDir; infer_instance
instance osCall_timeless (t s : Nat) (q : Qp) : Timeless (osCall (L := L) t s q) := by
  unfold osCall; infer_instance

/-- The history held, with the authoritative one: they agree. -/
theorem osTree_auth (R R' : Roots) (V V' : Hist) (dq : DFrac) :
    ⊢ gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γd (histMap (R, V)) -∗
      osTree (L := L) dq R' V' -∗ ⌜R' = R ∧ V' = V⌝ := by
  iintro HA Hh
  unfold osTree
  icases gAuth_lookup _ _ _ _ _ _ $$ HA Hh with %h
  ipureintro
  simp only [histMap, GMap.lookup_singleton_eq, Option.some.injEq, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.symm⟩

/-- A directory held, with the authoritative history: its view. -/
theorem osDir_view (R : Roots) (V : Hist) (j : Ino) (dq : DFrac) (g : DirG) :
    ⊢ gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γd (histMap (R, V)) -∗
      osDir (L := L) j dq g -∗ ⌜g = dview V j⌝ := by
  unfold osDir
  iintro HA ⟨%R', %V', Hh, %hg⟩
  icases osTree_auth R R' V V' dq $$ HA Hh with %h
  obtain ⟨rfl, rfl⟩ := h
  ipureintro; exact hg

/-- The history updated, with the whole of it. -/
theorem osTree_update (R : Roots) (V V' : Hist) (R' : Roots) (W : Hist) :
    ⊢ gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γd (histMap (R, V)) -∗
      osTree (L := L) (DFrac.own 1) R' W ==∗
      gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γd (histMap (R, V')) ∗
      osTree (L := L) (DFrac.own 1) R V' := by
  iintro HA Hh
  unfold osTree
  imod gAuth_update _ _ _ _ _ (R, V') $$ HA Hh with ⟨HA, Hh⟩
  have : (<[() := (R, V')]> (histMap (R, V))) = histMap (R, V') := by
    apply GMap.ext; intro u; cases u; simp [histMap]
  rw [this]
  imodintro; iframe

/-- A directory held whole, with the authoritative history, updated to the history `V'`, its view
there `g'`. -/
theorem osDir_update (R : Roots) (V V' : Hist) (j : Ino) (g g' : DirG) (hg' : g' = dview V' j) :
    ⊢ gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γd (histMap (R, V)) -∗
      osDir (L := L) j (DFrac.own 1) g ==∗
      gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γd (histMap (R, V')) ∗
      osDir (L := L) j (DFrac.own 1) g' := by
  unfold osDir
  iintro HA ⟨%R', %W, Hh, -⟩
  imod osTree_update R V V' R' W $$ HA Hh with ⟨HA, Hh⟩
  imodintro
  iframe HA
  iexists R, V'
  iframe Hh
  ipureintro; exact hg'

/-- The history is a directory's view (of any directory). -/
theorem osTree_dir (dq : DFrac) (R : Roots) (V : Hist) (j : Ino) :
    osTree (L := L) dq R V ⊢ osDir (L := L) j dq (dview V j) := by
  unfold osDir
  iintro H; iexists R, V; iframe; ipureintro; rfl

/-- A call held, with the authoritative calls: it is in flight, with its start. -/
theorem osCall_auth (C : GMap Nat (Nat × Qp)) (t s : Nat) (q : Qp) :
    ⊢ gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γc C -∗ osCall (L := L) t s q -∗
      ⌜C !! t = some (s, q)⌝ := by
  iintro HA Hc
  unfold osCall
  iapply gAuth_lookup $$ HA Hc

end resources

/-! ## The steps that leave the tree alone -/

section treeframe

theorem treeFrame_proc (st : OsState) (p : ProcState) (hd : p.dfds = st.proc.dfds)
    (hc : p.calls = st.proc.calls)
    (hfd : ∀ fd, p.fds !! fd ≠ none → st.proc.fds !! fd ≠ none ∨ st.proc.dfds !! fd = none) :
    TreeFrame st (st.setProc p) :=
  ⟨rfl, rfl, rfl, rfl, rfl, hd, hc, fun _ => Iff.rfl, hfd⟩

theorem treeFrame_inflight (st : OsState) (X : GMap Nat OsChange) :
    TreeFrame st (st.setProc { st.proc with inflight := X }) :=
  treeFrame_proc st _ rfl rfl (fun _ h => Or.inl h)

theorem treeFrame_maps (st : OsState) (X : GMap Loc OsMap) :
    TreeFrame st (st.setProc { st.proc with maps := X }) :=
  treeFrame_proc st _ rfl rfl (fun _ h => Or.inl h)

theorem treeFrame_fds_delete (st : OsState) (fd : w64) :
    TreeFrame st (st.setProc { st.proc with fds := GMap.delete fd st.proc.fds }) := by
  refine treeFrame_proc st _ rfl rfl (fun fd' h => Or.inl ?_)
  intro h'; apply h; show (GMap.delete fd st.proc.fds) !! fd' = none
  rw [GMap.lookup_delete_iff]; split
  · rfl
  · exact h'

theorem treeFrame_setFile (st : OsState) (i : Ino) (f f0 : OsFile) (hf : st.file i = some f0) :
    TreeFrame st (st.setFile i f) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun k => ?_, fun _ h => Or.inl h⟩
  rw [GMap.mem_iff, GMap.mem_iff]
  show ((<[i := f]> st.fs.files) !! k).isSome = true ↔ (st.fs.files !! k).isSome = true
  by_cases he : i = k
  · subst he; rw [GMap.lookup_insert]
    have : st.fs.files !! i = some f0 := hf
    simp [this]
  · rw [GMap.lookup_insert_ne _ _ he]

theorem treeFrame_stampFile (st : OsState) (i : Ino) (g : Nat → OsFile) (f0 : OsFile)
    (hf : st.file i = some f0) : TreeFrame st (st.stampFile i g) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun k => ?_, fun _ h => Or.inl h⟩
  rw [GMap.mem_iff, GMap.mem_iff]
  show ((<[i := g (st.fs.stamp + 1)]> st.fs.files) !! k).isSome = true ↔
    (st.fs.files !! k).isSome = true
  by_cases he : i = k
  · subst he; rw [GMap.lookup_insert]
    have : st.fs.files !! i = some f0 := hf
    simp [this]
  · rw [GMap.lookup_insert_ne _ _ he]

theorem treeFrame_addInflight (st : OsState) (t : Nat) (c : OsChange) :
    TreeFrame st (st.addInflight t c) :=
  treeFrame_inflight st _

theorem treeFrame_doneInflight (st : OsState) (t : Nat) : TreeFrame st (st.doneInflight t) :=
  treeFrame_inflight st _

/-- The operations that leave the tree alone: the data operations, on fds and their files. -/
def DataOp (o : String) : Prop :=
  o ∈ ["PRead", "PWriteStart", "PWriteFinish", "Fstat", "FtruncateStart", "FtruncateFinish",
    "Fsync", "Flock", "Close", "Mmap", "Munmap", "FdKind", "FallocStart", "FallocFinish",
    "FallocKeep", "OfdLock"]

open Classical in
theorem dataOp_ne_outClose {o : String} (ho : DataOp o) : o ≠ "OutClose" := by
  simp only [DataOp, List.mem_cons, List.mem_nil_iff, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

/-- Every step of a data operation leaves the tree alone. -/
theorem treeFrame_data [GooseExts] [GoGlobalContext] {o : String} (ho : DataOp o) {v : val}
    {st st' : OsState} {e' : Expr} (h : IsFsStep o v st e' st') : TreeFrame st st' := by
  simp only [DataOp, List.mem_cons, List.mem_nil_iff, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · -- PRead
    obtain ⟨_, _, _, _, _, -, -, -, -, -, rfl, -⟩ := h; exact TreeFrame.refl _
  · -- PWriteStart
    obtain ⟨_, _, _, d, f, t, -, -, -, -, -, hf, -, -, -, h1, -⟩ := h
    rw [h1]; exact (treeFrame_stampFile _ _ _ f hf).trans (treeFrame_addInflight _ _ _)
  · -- PWriteFinish
    obtain ⟨t, c, off, data, f, k, e, -, -, -, hf, -, -, -, h1, -⟩ := h
    rw [h1]; exact (treeFrame_doneInflight st t).trans (treeFrame_setFile _ _ _ f hf)
  · -- Fstat
    obtain ⟨_, _, _, -, -, -, rfl, -⟩ := h; exact TreeFrame.refl _
  · -- FtruncateStart
    obtain ⟨_, _, t, d, f, -, -, -, -, -, hf, -, -, h1, -⟩ := h
    rw [h1]; exact (treeFrame_stampFile _ _ _ f hf).trans (treeFrame_addInflight _ _ _)
  · -- FtruncateFinish
    obtain ⟨t, c, sz, f, -, -, -, hf, hres⟩ := h
    have h0 := treeFrame_doneInflight st t
    have h1 := h0.trans (treeFrame_setFile _ c.ino (f.land c c.hi c.target) f hf)
    rcases hres with ⟨rfl, -⟩ | ⟨-, -, -, rfl | rfl⟩
    · exact h1
    · exact h0
    · exact h1
  · -- Fsync
    obtain ⟨fd, d, f, -, -, hf, hres⟩ := h
    rcases hres with ⟨rfl, -⟩ | ⟨-, -, -, -, rfl⟩
    · exact treeFrame_setFile _ _ _ f hf
    · exact TreeFrame.refl _
  · -- Flock
    obtain ⟨_, _, _, _, -, -, rfl, -⟩ := h; exact TreeFrame.refl _
  · -- Close
    obtain ⟨fd, _, _, -, -, rfl, -⟩ := h; exact treeFrame_fds_delete _ _
  · -- Mmap
    obtain ⟨_, _, _, _, _, _, -, -, -, -, -, -, -, hres⟩ := h
    rcases hres with ⟨_, -, -, -, rfl, -⟩ | ⟨_, -, rfl, -⟩
    · exact treeFrame_maps _ _
    · exact TreeFrame.refl _
  · -- Munmap
    obtain ⟨_, _, _, _, -, -, -, -, hres⟩ := h
    rcases hres with ⟨rfl, -⟩ | ⟨_, -, -, rfl | rfl⟩
    · exact treeFrame_maps _ _
    · exact TreeFrame.refl _
    · exact treeFrame_maps _ _
  · -- FdKind
    obtain ⟨_, -, rfl, -⟩ := h; exact TreeFrame.refl _
  · -- FallocStart
    obtain ⟨_, _, _, t, d, f, -, -, -, -, -, -, hf, -, -, h1, -⟩ := h
    rw [h1]; exact (treeFrame_stampFile _ _ _ f hf).trans (treeFrame_addInflight _ _ _)
  · -- FallocFinish
    obtain ⟨t, c, sz, f, -, -, -, hf, hres⟩ := h
    have h0 := treeFrame_doneInflight st t
    rcases hres with ⟨rfl, -⟩ | ⟨-, -, -, rfl | ⟨w, -, -, rfl⟩⟩
    · exact h0.trans (treeFrame_setFile _ _ _ f hf)
    · exact h0
    · exact h0.trans (treeFrame_setFile _ _ _ f hf)
  · -- FallocKeep
    obtain ⟨_, _, _, _, d, -, -, -, -, -, rfl, -⟩ := h; exact TreeFrame.refl _
  · -- OfdLock
    obtain ⟨_, _, _, _, -, -, rfl, -⟩ := h; exact TreeFrame.refl _

end treeframe

/-! ## The step of an operation -/

/-- An `Open` step on a path of the roots' trees is not its outside case. -/
theorem open_inTree [GooseExts] [GoGlobalContext] [go.BasicIntoValInj] {st : OsState} {e' : Expr}
    {st' : OsState} {k : Nat} {p : GoString} {fl : w64} {A : Prop}
    (h : A ∨ OpenOutside (PairV (osTokV k) (PairV (#p) (#fl))) st e' st') (hp : st.TreePath p) : A := by
  rcases h with h | ⟨p', fl', t, start, hv, hn, -⟩
  · exact h
  · injection hv with hv1 hv2
    injection hv2 with hv3 hv4
    cases go.intoVal_inj hv3
    exact absurd hp hn

section step
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

/-- What an operation's proof works with of the files: the state, its ghost maps, what the extension
holds of each change in flight, the invariant's share of the mapped cells, and the heap. -/
def osWorld (st : OsState) (Γb : GMap (Ino × Nat) (ByteG))
    (Γm : GMap Ino OsMeta) (Γf : GMap w64 OsFd) (Γt : GMap Nat TokInfo)
    (h : GMap Loc (NonAtomic val)) : IProp GF :=
  iprop(⌜OsWf st ∧ OsCoh st Γb Γm Γf Γt⌝ ∗
    gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γb Γb ∗ gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γm Γm ∗
    gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γf Γf ∗ gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γt Γt ∗
    tokRes (gooseOsGS (L := L)) Γt ∗ cellsRes (cellView st) ∗ naHeapCtx tls h)

/-- What a tree operation's proof works with of the tree: the state's facts, the ghost maps of the
history, the directory fds and the calls in flight, and the fractions the reads in progress hold. -/
def treeWorld (st : OsState) (V : Hist) (Γdf : GMap w64 (Ino × DirPh))
    (Γc : GMap Nat (Nat × Qp)) : IProp GF :=
  iprop(⌜FsTreeWf st ∧ TreeCoh st V Γdf Γc⌝ ∗
    gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γd (histMap (st.fs.roots, V)) ∗
    gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γdf Γdf ∗
    gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γc Γc ∗
    rdRes (gooseOsGS (L := L)) Γdf ∗ callRes (gooseOsGS (L := L)) Γc)

/-- `wp_os_step`, whose continuation also gets the semantics' own step (which may say more
than `FsStep`: `fsSemWithS`'s premise on steps, `FsStepSat`).

The lifting of a data operation `o`: from the files' world before the step, the step exists, and
every step leads to a world after it, and the rest of the program. The tree is left alone
(`treeFrame_data`). -/
theorem wp_os_stepX (o : String) (v : val) (Φ : val → IProp GF) (hv : v.isPanic = false)
    (hE : ↑osN ⊆ E) (ho : DataOp o) :
    ⊢ osInv (L := L) -∗
      (∀ st Γb Γm Γf Γt h, osWorld st Γb Γm Γf Γt h ==∗
        ⌜∃ e' h' st', FsStep o v h st () e' h' st' ()⌝ ∗
        ▷ ∀ e' h' st', ⌜FsStep o v h st () e' h' st' () ∧
            ExtSemantics.step (E := fsExt) o v h st () e' h' st' ()⌝ ==∗
          ∃ Γb' Γm' Γf' Γt', osWorld st' Γb' Γm' Γf' Γt' h' ∗ WP e' @ s; E {{ Φ }}) -∗
      WP (ExternalOp fsExt.name o (Val v)) @ s; E {{ Φ }} := by
  iintro #Hinv HF
  iapply wp_extStep o v Φ hv
  iintro %h %σ %g Hheap Hl -
  icases (os_local_ctx_eq σ).mp $$ Hl with Hl
  unfold osCtx osCtxF
  icases Hl with ⟨⟨%Γb, %Γm, %Γf, %Γt, %Hwc, HAb, HAm, HAf, HAt, Htok, Hv⟩, Hns, Hof⟩
  unfold osInv
  imod inv_acc hE $$ Hinv with ⟨Hi, Hclose⟩
  icases Hi with >Hi
  icases Hi with ⟨%cv, %n, Hv', Hcells⟩
  icases gVar_agree _ _ _ _ _ $$ Hv Hv' with %Heq
  simp only [Prod.mk.injEq] at Heq
  obtain ⟨rfl, rfl⟩ := Heq
  imod HF $$ %σ %Γb %Γm %Γf %Γt %h [HAb HAm HAf HAt Htok Hcells Hheap] with ⟨%Hex, Hcont⟩
  · unfold osWorld; iframe; ipureintro; exact Hwc
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ E \ ↑osN from Std.LawfulSet.empty_subset)
  iintro Hclose2
  isplitr
  · ipureintro
    obtain ⟨e', h', st', Hst⟩ := Hex
    exact FsSemOk.step_ex _ _ _ _ g _ _ _ ()
      (fun _ _ _ _ _ h1 h2 => mapsTo_unique Hwc.1 h1 h2) Hst
  inext
  iintro %e' %h' %σ' %g' %Hst -
  have Hst2 := And.intro (FsSemOk.step_sub _ _ _ _ _ _ _ _ _ Hst) Hst
  have Hst := Hst2.1
  imod Hclose2
  imod Hcont $$ %e' %h' %σ' %Hst2 with ⟨%Γb', %Γm', %Γf', %Γt', Hw, Hwp⟩
  unfold osWorld
  icases Hw with ⟨%Hwc', HAb, HAm, HAf, HAt, Htok, Hcells, Hheap⟩
  imod gVar_update _ _ _ (cellView σ', GMap.size σ'.proc.inflight) $$ Hv Hv' with ⟨Hv, Hv'⟩
  imod Hclose $$ [Hv' Hcells] with -
  · inext; iexists (cellView σ'), (GMap.size σ'.proc.inflight); iframe
  imod ofdCtx_step _ Hst.1 (dataOp_ne_outClose ho) $$ Hof with Hof
  imodintro
  iframe Hheap Hwp
  isplitl [HAb HAm HAf HAt Htok Hv Hns Hof]
  · iapply (os_local_ctx_eq σ').mpr
    unfold osCtx osCtxF
    isplitl [HAb HAm HAf HAt Htok Hv]
    · iexists Γb', Γm', Γf', Γt'
      iframe
      ipureintro; exact Hwc'
    iframe Hof
    · iapply treeCtx_frame _ (treeFrame_data ho Hst.1) $$ Hns
  · have : (ExtInterp.globalCtx (E := fsExt) (extGlobalGS fsExt) g' : IProp GF) =
        iprop(True) := rfl
    rw [this]; itrivial

/-- The lifting of a data operation `o`: from the files' world before the step, the step exists, and
every step leads to a world after it, and the rest of the program. The tree is left alone
(`treeFrame_data`). -/
theorem wp_os_step (o : String) (v : val) (Φ : val → IProp GF) (hv : v.isPanic = false)
    (hE : ↑osN ⊆ E) (ho : DataOp o) :
    ⊢ osInv (L := L) -∗
      (∀ st Γb Γm Γf Γt h, osWorld st Γb Γm Γf Γt h ==∗
        ⌜∃ e' h' st', FsStep o v h st () e' h' st' ()⌝ ∗
        ▷ ∀ e' h' st', ⌜FsStep o v h st () e' h' st' ()⌝ ==∗
          ∃ Γb' Γm' Γf' Γt', osWorld st' Γb' Γm' Γf' Γt' h' ∗ WP e' @ s; E {{ Φ }}) -∗
      WP (ExternalOp fsExt.name o (Val v)) @ s; E {{ Φ }} := by
  iintro #Hinv HF
  iapply wp_os_stepX o v Φ hv hE ho $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %h Hw
  imod HF $$ %st %Γb %Γm %Γf %Γt %h Hw with ⟨%Hex, Hc⟩
  imodintro
  isplitr
  · ipureintro; exact Hex
  inext
  iintro %e' %h' %st' %Hst
  iapply Hc $$ %e' %h' %st' %Hst.1

/-- A resource of the legacy mode: with the shared mode's interpretation, a contradiction. A legacy
step's proof holds one (`osTree`, `osCall`, `osDirFd`), which tells it the mode. -/
def LegacyWit (W : IProp GF) : Prop := ∀ st, W ∗ treeShared (gooseOsGS (L := L)) st ⊢ False

theorem legacyWit_tree (dq : DFrac) (R : Roots) (V : Hist) :
    LegacyWit (L := L) (osTree (L := L) dq R V) := by
  intro st
  unfold treeShared osTree
  iintro ⟨H, %V0, %s0, %Γdf, %Γc, %Γg, %hw, -, Hd, -⟩
  icases gElem_valid_2 _ _ _ _ _ _ _ $$ H Hd with %Hv
  exact absurd (DFrac.valid_op_own Hv.1) (by simp)

theorem legacyWit_call (t s : Nat) (q : Qp) : LegacyWit (L := L) (osCall (L := L) t s q) := by
  intro st
  unfold treeShared osCall
  iintro ⟨H, %V0, %s0, %Γdf, %Γc, %Γg, %hw, -, -, -, Hac, -⟩
  icases gAuth_lookup _ _ _ _ _ _ $$ Hac H with %Hv
  simp at Hv

theorem legacyWit_dirFd (fd : w64) (dq : DFrac) (x : Ino × DirPh) :
    LegacyWit (L := L) (osDirFd (L := L) fd dq x) := by
  intro st
  unfold treeShared osDirFd
  iintro ⟨H, %V0, %s0, %Γdf, %Γc, %Γg, %hw, -, -, Haf, -⟩
  icases gAuth_lookup _ _ _ _ _ _ $$ Haf H with %Hv
  simp at Hv

/-- With a legacy resource, the tree's interpretation is the legacy mode's. -/
theorem treeCtx_legacy (W : IProp GF) (hW : LegacyWit (L := L) W) (st : OsState) :
    ⊢ W -∗ treeCtx (gooseOsGS (L := L)) st -∗
      W ∗ treeLegacy (gooseOsGS (L := L)) st ∗ commitRes (gooseOsGS (L := L)) st := by
  unfold treeCtx
  iintro HW ⟨Hm, Hcm⟩
  icases Hm with (Hm | Hm)
  · iframe
  · iexfalso
    iapply hW st
    iframe

/-- The lifting of any operation of the legacy mode (`W`: a resource of it): as `wp_os_step`, with
the tree's world too (`treeWorld`). -/
theorem wp_fs_stepT (o : String) (v : val) (Φ : val → IProp GF) (hv : v.isPanic = false)
    (hE : ↑osN ⊆ E) (W : IProp GF) (hW : LegacyWit (L := L) W)
    (hO : o ≠ "OutClose" := by decide) :
    ⊢ osInv (L := L) -∗ W -∗
      (W -∗ ∀ st Γb Γm Γf Γt V Γdf Γc h, osWorld st Γb Γm Γf Γt h -∗ treeWorld st V Γdf Γc ==∗
        ⌜∃ e' h' st', FsStep o v h st () e' h' st' ()⌝ ∗
        ▷ ∀ e' h' st', ⌜FsStep o v h st () e' h' st' ()⌝ ==∗
          ∃ Γb' Γm' Γf' Γt' V' Γdf' Γc', osWorld st' Γb' Γm' Γf' Γt' h' ∗
            treeWorld st' V' Γdf' Γc' ∗ WP e' @ s; E {{ Φ }}) -∗
      WP (ExternalOp fsExt.name o (Val v)) @ s; E {{ Φ }} := by
  iintro #Hinv HW HF
  iapply wp_extStep o v Φ hv
  iintro %h %σ %g Hheap Hl -
  icases (os_local_ctx_eq σ).mp $$ Hl with Hl
  unfold osCtx osCtxF
  icases Hl with ⟨⟨%Γb, %Γm, %Γf, %Γt, %Hwc, HAb, HAm, HAf, HAt, Htok, Hv⟩, Hns, Hof⟩
  icases treeCtx_legacy W hW σ $$ HW Hns with ⟨HW, Hns, Hcm⟩
  unfold treeLegacy
  icases Hns with ⟨%V, %Γdf, %Γc, %Hns, HAd, HAdf, HAc, Hrd, Hcr, Hlh⟩
  unfold osInv
  imod inv_acc hE $$ Hinv with ⟨Hi, Hclose⟩
  icases Hi with >Hi
  icases Hi with ⟨%cv, %n, Hv', Hcells⟩
  icases gVar_agree _ _ _ _ _ $$ Hv Hv' with %Heq
  simp only [Prod.mk.injEq] at Heq
  obtain ⟨rfl, rfl⟩ := Heq
  imod HF $$ HW %σ %Γb %Γm %Γf %Γt %V %Γdf %Γc %h [HAb HAm HAf HAt Htok Hcells Hheap]
    [HAd HAdf HAc Hrd Hcr] with ⟨%Hex, Hcont⟩
  · unfold osWorld; iframe; ipureintro; exact Hwc
  · unfold treeWorld; iframe; ipureintro; exact Hns
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ E \ ↑osN from Std.LawfulSet.empty_subset)
  iintro Hclose2
  isplitr
  · ipureintro
    obtain ⟨e', h', st', Hst⟩ := Hex
    exact FsSemOk.step_ex _ _ _ _ g _ _ _ ()
      (fun _ _ _ _ _ h1 h2 => mapsTo_unique Hwc.1 h1 h2) Hst
  inext
  iintro %e' %h' %σ' %g' %Hst -
  have Hst := FsSemOk.step_sub _ _ _ _ _ _ _ _ _ Hst
  imod Hclose2
  imod Hcont $$ %e' %h' %σ' %Hst with ⟨%Γb', %Γm', %Γf', %Γt', %V', %Γdf', %Γc', Hw, Hn, Hwp⟩
  unfold osWorld
  icases Hw with ⟨%Hwc', HAb, HAm, HAf, HAt, Htok, Hcells, Hheap⟩
  imod gVar_update _ _ _ (cellView σ', GMap.size σ'.proc.inflight) $$ Hv Hv' with ⟨Hv, Hv'⟩
  imod Hclose $$ [Hv' Hcells] with -
  · inext; iexists (cellView σ'), (GMap.size σ'.proc.inflight); iframe
  imod ofdCtx_step _ Hst.1 hO $$ Hof with Hof
  imodintro
  iframe Hheap Hwp
  isplitl [HAb HAm HAf HAt Htok Hv Hn Hcm Hlh Hof]
  · iapply (os_local_ctx_eq σ').mpr
    unfold osCtx osCtxF treeCtx
    isplitl [HAb HAm HAf HAt Htok Hv]
    · iexists Γb', Γm', Γf', Γt'
      iframe
      ipureintro; exact Hwc'
    iframe Hof
    · unfold treeWorld
      icases Hn with ⟨%Hns', HAd, HAdf, HAc, Hrd, Hcr⟩
      isplitl [HAd HAdf HAc Hrd Hcr Hlh]
      · ileft
        unfold treeLegacy
        iexists V', Γdf', Γc'
        iframe HAd HAdf HAc Hrd Hcr Hlh
        ipureintro; exact Hns'
      · iapply commitRes_grow _ (fsStep_commitGrows Hst) $$ Hcm
  · have : (ExtInterp.globalCtx (E := fsExt) (extGlobalGS fsExt) g' : IProp GF) =
        iprop(True) := rfl
    rw [this]; itrivial

/-- **The lifting of any operation, in either mode**: from the files' world and the tree's whole
interpretation before the step (the shared mode's invariant may be opened across it: the mask goes
to `∅` and back), the step exists, and every step leads to a world and an interpretation after it,
and the rest of the program. -/
theorem wp_fs_stepM (o : String) (v : val) (Φ : val → IProp GF) (hv : v.isPanic = false)
    (hE : ↑osN ⊆ E) (hO : o ≠ "OutClose" := by decide) :
    ⊢ osInv (L := L) -∗
      (∀ st Γb Γm Γf Γt h, osWorld st Γb Γm Γf Γt h -∗ treeCtx (gooseOsGS (L := L)) st
        ={E \ ↑osN, ∅}=∗
        ⌜∃ e' h' st', FsStep o v h st () e' h' st' ()⌝ ∗
        ▷ ∀ e' h' st', ⌜FsStep o v h st () e' h' st' ()⌝ ={∅, E \ ↑osN}=∗
          ∃ Γb' Γm' Γf' Γt', osWorld st' Γb' Γm' Γf' Γt' h' ∗
            treeCtx (gooseOsGS (L := L)) st' ∗ WP e' @ s; E {{ Φ }}) -∗
      WP (ExternalOp fsExt.name o (Val v)) @ s; E {{ Φ }} := by
  iintro #Hinv HF
  iapply wp_extStep o v Φ hv
  iintro %h %σ %g Hheap Hl -
  icases (os_local_ctx_eq σ).mp $$ Hl with Hl
  unfold osCtx osCtxF
  icases Hl with ⟨⟨%Γb, %Γm, %Γf, %Γt, %Hwc, HAb, HAm, HAf, HAt, Htok, Hv⟩, Hns, Hof⟩
  unfold osInv
  imod inv_acc hE $$ Hinv with ⟨Hi, Hclose⟩
  icases Hi with >Hi
  icases Hi with ⟨%cv, %n, Hv', Hcells⟩
  icases gVar_agree _ _ _ _ _ $$ Hv Hv' with %Heq
  simp only [Prod.mk.injEq] at Heq
  obtain ⟨rfl, rfl⟩ := Heq
  imod HF $$ %σ %Γb %Γm %Γf %Γt %h [HAb HAm HAf HAt Htok Hcells Hheap] Hns with ⟨%Hex, Hcont⟩
  · unfold osWorld; iframe; ipureintro; exact Hwc
  imodintro
  isplitr
  · ipureintro
    obtain ⟨e', h', st', Hst⟩ := Hex
    exact FsSemOk.step_ex _ _ _ _ g _ _ _ ()
      (fun _ _ _ _ _ h1 h2 => mapsTo_unique Hwc.1 h1 h2) Hst
  inext
  iintro %e' %h' %σ' %g' %Hst -
  have Hst := FsSemOk.step_sub _ _ _ _ _ _ _ _ _ Hst
  imod Hcont $$ %e' %h' %σ' %Hst with ⟨%Γb', %Γm', %Γf', %Γt', Hw, Hn, Hwp⟩
  unfold osWorld
  icases Hw with ⟨%Hwc', HAb, HAm, HAf, HAt, Htok, Hcells, Hheap⟩
  imod gVar_update _ _ _ (cellView σ', GMap.size σ'.proc.inflight) $$ Hv Hv' with ⟨Hv, Hv'⟩
  imod Hclose $$ [Hv' Hcells] with -
  · inext; iexists (cellView σ'), (GMap.size σ'.proc.inflight); iframe
  imod ofdCtx_step _ Hst.1 hO $$ Hof with Hof
  imodintro
  iframe Hheap Hwp
  isplitl [HAb HAm HAf HAt Htok Hv Hn Hof]
  · iapply (os_local_ctx_eq σ').mpr
    unfold osCtx osCtxF
    iframe Hn Hof
    iexists Γb', Γm', Γf', Γt'
    iframe
    ipureintro; exact Hwc'
  · have : (ExtInterp.globalCtx (E := fsExt) (extGlobalGS fsExt) g' : IProp GF) =
        iprop(True) := rfl
    rw [this]; itrivial

end step

/-! ## The files' part of a tree step -/

/-- `st'` has `st`'s files, fds, changes in flight and mappings. -/
def FilesSame (st st' : OsState) : Prop :=
  st'.fs.files = st.fs.files ∧ st'.proc.fds = st.proc.fds ∧
    st'.proc.inflight = st.proc.inflight ∧ st'.proc.maps = st.proc.maps ∧ st'.fs.stamp = st.fs.stamp

theorem filesSame_refl (st : OsState) : FilesSame st st := ⟨rfl, rfl, rfl, rfl, rfl⟩

section filesSame
variable {st st' : OsState} (h : FilesSame st st')
include h

theorem filesSame_file : ∀ i, st'.file i = st.file i := by
  intro i; simp [OsState.file, h.1]

theorem filesSame_size : ∀ i, st'.size i = st.size i := by
  intro i; simp [OsState.size, filesSame_file h]

theorem filesSame_inflightAt : ∀ i b, InflightAt st' i b = InflightAt st i b :=
  inflightAt_congr h.2.2.1

theorem osWf_filesSame (hw : OsWf st) : OsWf st' := by
  have hf := filesSame_file h
  obtain ⟨h1, h2, h3, h4, hstamp⟩ := h
  refine ⟨fun fd d hd => ?_, fun b m hm => ?_, fun b1 m1 b2 m2 hm1 hm2 => ?_, fun t c ht => ?_,
    fun t1 c1 t2 c2 ht1 ht2 => ?_, fun i f hfi => ?_, fun i f b p hfi => ?_⟩
  · rw [h2] at hd; rw [hf]; exact hw.fds fd d hd
  · rw [h4] at hm; rw [hf]; exact hw.maps b m hm
  · rw [h4] at hm1 hm2; exact hw.maps_disj b1 m1 b2 m2 hm1 hm2
  · rw [h3] at ht; rw [hf]; exact hw.infl t c ht
  · rw [h3] at ht1 ht2; exact hw.infl_one t1 c1 t2 c2 ht1 ht2
  · rw [hf] at hfi; exact hw.sizes i f hfi
  · rw [hf] at hfi; rw [hstamp]; exact hw.stamps i f b p hfi

theorem metaOk_filesSame {i : Ino} {m : OsMeta} {f : OsFile} (hm : MetaOk st i m f) :
    MetaOk st' i m f :=
  hm.transfer h.2.2.2.1 h.2.2.1

theorem osCoh_filesSame {Γb Γm Γf Γt} (hc : OsCoh st Γb Γm Γf Γt) : OsCoh st' Γb Γm Γf Γt := by
  have hf := filesSame_file h
  have hmk : ∀ i m f, MetaOk st i m f → MetaOk st' i m f := fun _ _ _ hm => metaOk_filesSame h hm
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨fun i => by rw [h1]; exact hc.meta_dom i, fun i m hm => ?_, fun i b x hx => ?_,
    fun i f b hfi hb => ?_, by rw [h2]; exact hc.fds, fun t => by rw [h3]; exact hc.toks t,
    fun t ti c hti hc' => by rw [h3] at hc'; exact hc.tok_is t ti c hti hc', hc.tok_meta,
    fun t ti hti => ?_, fun t ti hti => ?_, fun t ti hti hk => by rw [hf]; exact hc.tok_rz t ti hti hk,
    fun i m c hm hc' => by rw [h5]; exact hc.cut_le i m c hm hc'⟩
  · obtain ⟨f, hfi, hmo⟩ := hc.meta_some i m hm
    exact ⟨f, by rw [h1]; exact hfi, hmk _ _ _ hmo⟩
  · obtain ⟨f, hfi, hb, hx⟩ := hc.bytes i b x hx
    exact ⟨f, by rw [hf]; exact hfi, hb, hx⟩
  · rw [hf] at hfi; exact hc.bytes_full i f b hfi hb
  · rw [hf]; exact hc.tok_file t ti hti
  · rw [hf]; exact hc.tok_cand t ti hti

theorem cellView_filesSame (hw : OsWf st) : cellView st' = cellView st :=
  cellView_congr hw (osWf_filesSame h hw) h.2.2.2.1
    (fun i => by rw [filesSame_file h]) h.2.2.1

end filesSame

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
attribute [local instance] Classical.propDecidable

theorem cells_same {st st' : OsState} {h h' : GMap Loc (NonAtomic val)} (hwf : OsWf st)
    (hwf' : OsWf st') (hr : HeapRendered st st' h h') (hfr : MapsFresh st st' h)
    (hm : st'.proc.maps = st.proc.maps) (hcv : cellView st' = cellView st) :
    naHeapCtx tls h ∗ cellsRes (GF := GF) (cellView st) ⊢ |==>
      (naHeapCtx tls h' ∗ cellsRes (cellView st')) := by
  iintro ⟨Hσ, Hc⟩
  imod cells_step st st' h h' [] ∅ ∅ hwf hwf' hr hfr (fun b m h => by rw [hm] at h; exact .inr h)
    List.nodup_nil (fun _ h => by simp at h) (fun _ _ h => by simp at h)
    (fun _ _ h => by simp at h) (fun _ h => by simp at h) (fun _ h => by simp at h)
    (fun l _ => by rw [hcv]) $$ [Hσ Hc] with ⟨Hσ, Hc, -⟩
  · iframe; unfold halves; iapply BigSepM.bigSepM_empty.2; iempintro
  imodintro; iframe

/-- The files' world after a step that leaves them alone. -/
theorem osWorld_filesSame {st st' : OsState} {Γb Γm Γf Γt} {h h' : GMap Loc (NonAtomic val)}
    (hs : FilesSame st st') (hr : HeapRendered st st' h h') (hfr : MapsFresh st st' h) :
    osWorld (L := L) st Γb Γm Γf Γt h ⊢ |==> osWorld (L := L) st' Γb Γm Γf Γt h' := by
  unfold osWorld
  iintro ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  obtain ⟨hwf, hcoh⟩ := Hwc
  have hwf' := osWf_filesSame hs hwf
  imod cells_same hwf hwf' hr hfr hs.2.2.2.1 (cellView_filesSame hs hwf) $$ [Hσ Hcells]
    with ⟨Hσ, Hcells⟩
  · iframe
  imodintro
  iframe
  ipureintro; exact ⟨hwf', osCoh_filesSame hs hcoh⟩

/-- A step that leaves the files alone exists from any heap the cells' view agrees with. -/
theorem step_filesSame {st st' : OsState} {h : GMap Loc (NonAtomic val)} (hwf : OsWf st)
    (hs : FilesSame st st')
    (Hag : ∀ l x, cellView st !! l = some x → ∃ m, h !! l = some (m, toCellVal x.1)) :
    MapsFresh st st' h ∧ HeapRendered st st' h h :=
  ⟨mapsFresh_same hs.2.2.2.1,
    heapRendered_same (osWf_filesSame hs hwf) hs.2.2.2.1 (cellView_filesSame hs hwf) Hag⟩

end specs

end Fs
end Perennial

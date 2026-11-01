/-
WP specs of the Linux file extension's operations (`GooseLang/Ext/OsFs/Impl.lean`).

**Resources** (all of the generation's ghost state `gooseOsGS`, `Ghost.lean`):
* `osByte p i dq (b, c)`: byte `i` of the page cache of the file `p` is `b`, and, if `c`, clean
  (on disk, kept by a crash); fractional. `osBytes p off dq xs`: the bytes from `off` on.
* `osMeta p dq (some m)`: the file `p` exists and `m` (`OsMeta`) says what the ghost state knows
  of it: its size, the bounds of the size a crash may leave, whether a crash keeps it
  (`named`), whether a failed sync has lost any byte of it (`ok`), its mappings. `osMeta p dq
  none`: `p` is allowed and has no file. Fractional; changing the size, syncing and (un)mapping
  need it whole, and a change in flight holds a fraction of it.
* `osFd fd dq d`: `fd` is open, on the file `d.path`, with `d`'s access mode; fractional
  (concurrent reads and writes through one fd), whole to close.
* `osInv`: the invariant of the generation's mapped cells, allocated once per generation from
  the start resources (`osInv_alloc`); every spec takes it, with `↑osN ⊆ E`.
* A mapped cell's other half is the client's, an ordinary heap points-to
  `(base +ₗ i) ↦{½} v`: a load through it is an ordinary load. While the client holds a
  fraction of the byte it maps, `v` is the byte (`osCell_agree`); a hole (past the end of the
  file, or under a change in flight) is `osHole`, which no load spec accepts.
-/
module

public import GooseLang.Ext.OsFs.Cells
public import Perennial.Golang.Defn.PostLang
public import Iris.Instances.Lib.Invariants

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode
open goose_heap

/-! ## Facts about the state -/

theorem cellView_congr {st st' : OsState} (h1 : st'.maps = st.maps) (h2 : st'.files = st.files)
    (h3 : st'.inflight = st.inflight) : cellView st' = cellView st := by
  cases st; cases st'; simp only at h1 h2 h3; subst h1 h2 h3; rfl

theorem mapsFresh_same [GooseExts] [GoGlobalContext] {st st' : OsState}
    {h : GMap Loc (NonAtomic val)} (hm : st'.maps = st.maps) : MapsFresh st st' h := by
  intro b m h1 h2; rw [hm] at h1; rw [h1] at h2; cases h2

theorem heapRendered_same [GooseExts] [GoGlobalContext] {st st' : OsState}
    {h : GMap Loc (NonAtomic val)} (hwf' : OsWf st') (hm : st'.maps = st.maps)
    (hcv : cellView st' = cellView st)
    (Hag : ∀ l x, cellView st !! l = some x → ∃ m, h !! l = some (m, toCellVal x.1)) :
    HeapRendered st st' h h := by
  have hM : ∀ l p i, MapsTo st' l p i ↔ MapsTo st l p i := by
    intro l p i; simp only [MapsTo, hm]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro l p i hpi _
    have hv := cellView_mapsTo hwf' hpi
    rw [hcv] at hv
    obtain ⟨m, hh⟩ := Hag l _ hv
    exact ⟨m, _, hh, by rw [hh, cellVal_eq]⟩
  · intro l p i hpi hn; exact absurd ⟨p, i, (hM l p i).1 hpi⟩ hn
  · intro l hn hm'; obtain ⟨p, i, hpi⟩ := hm'; exact absurd ⟨p, i, (hM l p i).2 hpi⟩ hn
  · intro l _ _; rfl

/-! ## Resources -/

section resources
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt] [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]

/-- The ghost state of the generation. -/
abbrev gooseOsGS : OsGS GF := extLocalGS osFsExt

theorem os_local_ctx_eq (st : OsState) :
    ExtInterp.localCtx (E := osFsExt) (extLocalGS osFsExt) st ⊣⊢ osCtx (gooseOsGS (L := L)) st :=
  .rfl

/-- Byte `i` of the file `p` is `x.1`, clean if `x.2`. -/
def osByte (p : GoString) (i : Nat) (dq : DFrac) (x : w8 × Bool) : IProp GF :=
  gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γb (p, i) dq x

/-- The bytes of the file `p` from `off` on are `xs`. -/
def osBytes (p : GoString) (off : Nat) (dq : DFrac) (xs : List (w8 × Bool)) : IProp GF :=
  [∗list] k ↦ x ∈ xs, osByte (L := L) p (off + k) dq x

/-- The file at `p`: `some m`, it exists, as `m` says; `none`, it does not. -/
def osMeta (p : GoString) (dq : DFrac) (mo : Option OsMeta) : IProp GF :=
  gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γm p dq mo

/-- The fd `fd` is open, as `d` says. -/
def osFd (fd : w64) (dq : DFrac) (d : OsFd) : IProp GF :=
  gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γf fd dq d

/-- The change in flight `t`, as `ti` says. -/
def osTok (t : w64) (ti : TokInfo) : IProp GF :=
  gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γt t (DFrac.own 1) ti

instance osByte_timeless (p : GoString) (i : Nat) (dq : DFrac) (x : w8 × Bool) :
    Timeless (osByte (L := L) p i dq x) := by unfold osByte; infer_instance
instance osMeta_timeless (p : GoString) (dq : DFrac) (mo : Option OsMeta) :
    Timeless (osMeta (L := L) p dq mo) := by unfold osMeta; infer_instance
instance osFd_timeless (fd : w64) (dq : DFrac) (d : OsFd) :
    Timeless (osFd (L := L) fd dq d) := by unfold osFd; infer_instance

/-- The namespace of the invariant of the mapped cells. -/
def osN : Namespace := nroot .@ "osfs"

/-- The invariant of the generation's mapped cells: the extension's share of each (`cellsRes`),
for the view the state interpretation's half of the ghost variable names, and a thread token
for each change in flight. -/
def osInv : IProp GF :=
  inv osN iprop(∃ (cv : GMap Loc (Option w8 × Bool)) (n : Nat),
    gVar (gooseOsGS (L := L)) (1 : Qp).half (cv, n) ∗ cellsRes cv ∗ threadToks n)

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
  isplitl []
  · unfold cellsRes; iapply BigSepM.bigSepM_empty.2; iempintro
  · iapply threadToks_zero

end resources

/-! ## The step of an operation -/

section step
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt] [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

/-- What an operation's proof works with: the state, its ghost maps, what the extension holds
of each change in flight, the invariant's share of the mapped cells, its thread tokens, and the
heap. -/
def osWorld (st : OsState) (Γb : GMap (GoString × Nat) (w8 × Bool))
    (Γm : GMap GoString (Option OsMeta)) (Γf : GMap w64 OsFd) (Γt : GMap w64 TokInfo)
    (h : GMap Loc (NonAtomic val)) : IProp GF :=
  iprop(⌜OsWf st ∧ OsCoh st Γb Γm Γf Γt⌝ ∗
    gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γb Γb ∗ gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γm Γm ∗
    gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γf Γf ∗ gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γt Γt ∗
    tokRes (gooseOsGS (L := L)) st Γt ∗ cellsRes (cellView st) ∗
    threadToks (GMap.size st.inflight) ∗ naHeapCtx tls h)

/-- The lifting of an operation `o` of the extension: from the world before the step, the step
exists, and every step leads to a world after it, and the rest of the program. -/
theorem wp_os_step (o : String) (v : val) (Φ : val → IProp GF) (hv : v.isPanic = false)
    (hE : ↑osN ⊆ E) :
    ⊢ osInv (L := L) -∗
      (∀ st Γb Γm Γf Γt h, osWorld st Γb Γm Γf Γt h ==∗
        ⌜∃ e' h' st', OsStep o v h st () e' h' st' ()⌝ ∗
        ∀ e' h' st', ⌜OsStep o v h st () e' h' st' ()⌝ ==∗
          ∃ Γb' Γm' Γf' Γt', osWorld st' Γb' Γm' Γf' Γt' h' ∗ WP e' @ s; E {{ Φ }}) -∗
      WP (ExternalOp osFsExt.name o (Val v)) @ s; E {{ Φ }} := by
  iintro #Hinv HF
  iapply wp_extStep o v Φ hv
  iintro %h %σ %g Hheap Hl -
  icases (os_local_ctx_eq σ).mp $$ Hl with Hl
  unfold osCtx
  icases Hl with ⟨%Γb, %Γm, %Γf, %Γt, %Hwc, HAb, HAm, HAf, HAt, Htok, Hv⟩
  unfold osInv
  imod inv_acc hE $$ Hinv with ⟨Hi, Hclose⟩
  icases Hi with >Hi
  icases Hi with ⟨%cv, %n, Hv', Hcells, Hth⟩
  icases gVar_agree _ _ _ _ _ $$ Hv Hv' with %Heq
  simp only [Prod.mk.injEq] at Heq
  obtain ⟨rfl, rfl⟩ := Heq
  imod HF $$ %σ %Γb %Γm %Γf %Γt %h [HAb HAm HAf HAt Htok Hcells Hth Hheap] with ⟨%Hex, Hcont⟩
  · unfold osWorld; iframe; ipureintro; exact Hwc
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ E \ ↑osN from Std.LawfulSet.empty_subset)
  iintro Hclose2
  isplitr
  · ipureintro
    obtain ⟨e', h', st', Hst⟩ := Hex
    exact ⟨e', h', st', g, Hst⟩
  inext
  iintro %e' %h' %σ' %g' %Hst -
  imod Hclose2
  imod Hcont $$ %e' %h' %σ' %Hst with ⟨%Γb', %Γm', %Γf', %Γt', Hw, Hwp⟩
  unfold osWorld
  icases Hw with ⟨%Hwc', HAb, HAm, HAf, HAt, Htok, Hcells, Hth, Hheap⟩
  imod gVar_update _ _ _ (cellView σ', GMap.size σ'.inflight) $$ Hv Hv' with ⟨Hv, Hv'⟩
  imod Hclose $$ [Hv' Hcells Hth] with -
  · inext; iexists (cellView σ'), (GMap.size σ'.inflight); iframe
  imodintro
  iframe Hheap Hwp
  isplitl [HAb HAm HAf HAt Htok Hv]
  · iapply (os_local_ctx_eq σ').mpr
    unfold osCtx
    iexists Γb', Γm', Γf', Γt'
    iframe
    ipureintro; exact Hwc'
  · have : (ExtInterp.globalCtx (E := osFsExt) (extGlobalGS osFsExt) g' : IProp GF) =
        iprop(True) := rfl
    rw [this]; itrivial

end step

end Perennial

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

theorem size_of_file {st : OsState} {p : GoString} {f : OsFile} (hf : st.file p = some f) :
    st.size p = f.cur.length := by
  simp [OsState.size, hf]

/-- Below the size, the bytes a change affects are the bytes it takes. -/
theorem affects_iff_affRange (st : OsState) (c : OsChange) (i : Nat) (f : OsFile)
    (hf : st.file c.path = some f) (hi : i < f.cur.length) :
    Affects st c i ↔ i ∈ affRange st c := by
  unfold Affects affRange affLo affHi inRange
  rw [size_of_file hf]
  cases c.kind <;> dsimp only <;>
    simp only [List.mem_range'_1, Bool.and_eq_true, decide_eq_true_eq] <;> omega

theorem coh_byte {st : OsState} {Γb Γm Γf Γt} (hcoh : OsCoh st Γb Γm Γf Γt) {p : GoString}
    {i : Nat} {x : w8 × Bool} (hx : Γb !! (p, i) = some x) :
    ∃ f, st.file p = some f ∧ ∃ h : i < f.cur.length, f.cur[i] = x.1 := by
  obtain ⟨f, hf, hb, -⟩ := hcoh.bytes p i x hx
  obtain ⟨h, h'⟩ := List.getElem?_eq_some_iff.1 hb
  exact ⟨f, hf, h, h'⟩

theorem coh_tok {st : OsState} {Γb Γm Γf Γt} (hcoh : OsCoh st Γb Γm Γf Γt) {t : w64}
    {c : OsChange} (ht : st.inflight !! t = some c) : ∃ ti, Γt !! t = some ti ∧ ti.c = c := by
  have := hcoh.toks t
  rw [ht] at this
  cases h : Γt !! t with
  | none => rw [h] at this; cases this
  | some ti => rw [h] at this; exact ⟨ti, rfl, Option.some.inj this⟩

/-- A size `fstat` may see is past every byte that no change affects. -/
theorem statSees_gt {st : OsState} {p : GoString} {f : OsFile} {i sz : Nat}
    (hf : st.file p = some f) (hi : i < f.cur.length) (hn : ¬ InflightAt st p i)
    (hs : StatSees st p sz) : i < sz := by
  rcases hs with rfl | ⟨t, c, ht, hcp, hlo, -⟩
  · rw [size_of_file hf]; exact hi
  · have hna : ¬ Affects st c i := fun ha => hn ⟨t, c, ht, hcp, ha⟩
    subst hcp
    rw [size_of_file hf] at hlo
    unfold Affects inRange at hna
    unfold OsChange.target at hlo
    rw [size_of_file hf] at hna hlo
    cases hk : c.kind with
    | write off data => simp only [hk] at hna hlo; simp at hna; omega
    | truncate sz' => simp only [hk] at hna hlo; omega

/-- With no change in flight on `p` that may resize it, `fstat` sees the size. -/
theorem statSees_eq {st : OsState} {p : GoString} {sz : Nat}
    (h : ∀ t c, st.inflight !! t = some c → c.path = p → ¬ Reaches st c)
    (hs : StatSees st p sz) : sz = st.size p := by
  rcases hs with rfl | ⟨t, c, ht, hcp, hlo, hhi⟩
  · rfl
  · have hr := h t c ht hcp
    subst hcp
    unfold Reaches at hr
    unfold OsChange.target at hlo hhi
    cases hk : c.kind with
    | write off data => simp only [hk] at hr hlo hhi; omega
    | truncate _ => simp [hk] at hr

/-! ## What the extension holds of the changes in flight -/

section tokres
variable {GF : BundledGFunctors} (hL : OsGS GF)

/-- A byte the client holds a fraction of is under no change in flight: the change would hold
all of it. -/
theorem tokRes_byte_free {st : OsState} {Γb Γm Γf Γt} (hcoh : OsCoh st Γb Γm Γf Γt)
    {p : GoString} {i : Nat} {dq : DFrac} {x : w8 × Bool} (hx : Γb !! (p, i) = some x) :
    ⊢ tokRes hL st Γt -∗ gElem hL hL.γb (p, i) dq x -∗ ⌜¬ InflightAt st p i⌝ := by
  iintro Htok Hb
  by_cases hin : InflightAt st p i
  · obtain ⟨t, c, ht, hcp, haff⟩ := hin
    obtain ⟨ti, hti, rfl⟩ := coh_tok hcoh ht
    obtain ⟨f, hf, hi, -⟩ := coh_byte hcoh hx
    obtain ⟨f', hf', hsaved⟩ := hcoh.tok_saved t ti hti
    subst hcp
    rw [hf] at hf'; cases hf'
    have hmem := (affects_iff_affRange st ti.c i f hf hi).1 haff
    have hlo : affLo st ti.c ≤ i ∧ i < affLo st ti.c + (affHi st ti.c - affLo st ti.c) :=
      List.mem_range'_1.1 hmem
    have hk : (affRange st ti.c)[i - affLo st ti.c]? = some i := by
      unfold affRange; rw [List.getElem?_range']; simp; omega; omega
    have hk' : ti.saved[i - affLo st ti.c]? = some (f.cur.getD i 0) := by
      rw [hsaved, List.getElem?_map, hk]; rfl
    unfold tokRes
    icases BigSepM.bigSepM_lookup (Φ := fun (_t : w64) (ti : TokInfo) =>
      iprop(gElem hL hL.γm ti.c.path (DFrac.own ti.q) (some ti.om) ∗
        [∗list] k ↦ b ∈ ti.saved, gElem hL hL.γb (ti.c.path, affLo st ti.c + k) (DFrac.own 1)
          (b, false))) hti $$ Htok with ⟨-, Hs⟩
    icases BigSepL.bigSepL_lookup (Φ := fun k (b : w8) =>
      gElem hL hL.γb (ti.c.path, affLo st ti.c + k) (DFrac.own 1) (b, false)) hk' $$ Hs with Hs
    rw [show affLo st ti.c + (i - affLo st ti.c) = i by omega]
    icases gElem_valid_2 hL _ _ _ _ _ _ $$ Hs Hb with %Hv
    exact absurd (DFrac.valid_own_op Hv.1) (by simp)
  · ipureintro; exact hin

/-- A client's fraction of a file's `OsMeta` leaves the changes in flight on it only fractions:
none of them takes the whole. -/
theorem tokRes_meta_frac {st : OsState} {Γt : GMap w64 TokInfo} {p : GoString} {dq : DFrac}
    {mo : Option OsMeta} :
    ⊢ tokRes hL st Γt -∗ gElem hL hL.γm p dq mo -∗
      ⌜∀ t ti, Γt !! t = some ti → ti.c.path = p → ti.q ≠ 1⌝ := by
  iintro Htok Hm
  iapply pure_forall.2; iintro %t
  iapply pure_forall.2; iintro %ti
  by_cases hti : Γt !! t = some ti
  · by_cases hp : ti.c.path = p
    · by_cases hq : ti.q = 1
      · unfold tokRes
        icases BigSepM.bigSepM_lookup (Φ := fun (_t : w64) (ti : TokInfo) =>
          iprop(gElem hL hL.γm ti.c.path (DFrac.own ti.q) (some ti.om) ∗
            [∗list] k ↦ b ∈ ti.saved, gElem hL hL.γb (ti.c.path, affLo st ti.c + k)
              (DFrac.own 1) (b, false))) hti $$ Htok with ⟨Hs, -⟩
        rw [hp, hq]
        icases gElem_valid_2 hL _ _ _ _ _ _ $$ Hs Hm with %Hv
        exact absurd (DFrac.valid_own_op Hv.1) (by simp)
      · ipureintro; exact fun _ _ => hq
    · ipureintro; exact fun _ h => absurd h hp
  · ipureintro; exact fun h => absurd h hti

/-- The whole of a file's `OsMeta`: no change is in flight on it. -/
theorem tokRes_meta_whole {st : OsState} {Γt : GMap w64 TokInfo} {p : GoString}
    {mo : Option OsMeta} :
    ⊢ tokRes hL st Γt -∗ gElem hL hL.γm p (DFrac.own 1) mo -∗
      ⌜∀ t ti, Γt !! t = some ti → ti.c.path ≠ p⌝ := by
  iintro Htok Hm
  iapply pure_forall.2; iintro %t
  iapply pure_forall.2; iintro %ti
  by_cases hti : Γt !! t = some ti
  · by_cases hp : ti.c.path = p
    · unfold tokRes
      icases BigSepM.bigSepM_lookup (Φ := fun (_t : w64) (ti : TokInfo) =>
        iprop(gElem hL hL.γm ti.c.path (DFrac.own ti.q) (some ti.om) ∗
          [∗list] k ↦ b ∈ ti.saved, gElem hL hL.γb (ti.c.path, affLo st ti.c + k)
            (DFrac.own 1) (b, false))) hti $$ Htok with ⟨Hs, -⟩
      rw [hp]
      icases gElem_valid_2 hL _ _ _ _ _ _ $$ Hm Hs with %Hv
      exact absurd (DFrac.valid_own_op Hv.1) (by simp)
    · ipureintro; exact fun _ => hp
  · ipureintro; exact fun h => absurd h hti

end tokres

theorem noReach_of_frac {st : OsState} {Γb Γm Γf Γt} (hcoh : OsCoh st Γb Γm Γf Γt) {p : GoString}
    (h : ∀ t ti, Γt !! t = some ti → ti.c.path = p → ti.q ≠ 1) :
    ∀ t c, st.inflight !! t = some c → c.path = p → ¬ Reaches st c := by
  intro t c ht hcp hr
  obtain ⟨ti, hti, rfl⟩ := coh_tok hcoh ht
  exact h t ti hti hcp (hcoh.tok_q t ti hti hr)

theorem noTok_of_whole {st : OsState} {Γb Γm Γf Γt} (hcoh : OsCoh st Γb Γm Γf Γt) {p : GoString}
    (h : ∀ t ti, Γt !! t = some ti → ti.c.path ≠ p) :
    ∀ t c, st.inflight !! t = some c → c.path ≠ p := by
  intro t c ht hcp
  obtain ⟨ti, hti, rfl⟩ := coh_tok hcoh ht
  exact h t ti hti hcp

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
        ▷ ∀ e' h' st', ⌜OsStep o v h st () e' h' st' ()⌝ ==∗
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


/-! ## Specs -/

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt] [GoGlobalContext]
  [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

theorem cells_same {st st' : OsState} {h h' : GMap Loc (NonAtomic val)} (hwf : OsWf st)
    (hwf' : OsWf st') (hr : HeapRendered st st' h h') (hfr : MapsFresh st st' h)
    (hm : st'.maps = st.maps) (hcv : cellView st' = cellView st) :
    naHeapCtx tls h ∗ cellsRes (GF := GF) (cellView st) ⊢ |==>
      (naHeapCtx tls h' ∗ cellsRes (cellView st')) := by
  iintro ⟨Hσ, Hc⟩
  imod cells_step st st' h h' [] ∅ ∅ hwf hwf' hr hfr (fun b m h => by rw [hm] at h; exact .inr h)
    List.nodup_nil (fun _ h => by simp at h) (fun _ _ h => by simp at h)
    (fun _ _ h => by simp at h) (fun _ h => by simp at h) (fun _ h => by simp at h)
    (fun l _ => by rw [hcv]) $$ [Hσ Hc] with ⟨Hσ, Hc, -⟩
  · iframe; unfold halves; iapply BigSepM.bigSepM_empty.2; iempintro
  imodintro; iframe

theorem osWf_fds {st : OsState} (hwf : OsWf st) (X : GMap w64 OsFd)
    (hX : ∀ fd d, X !! fd = some d → ∃ f, st.file d.path = some f) :
    OsWf { st with fds := X } :=
  { hwf with fds := hX }

theorem MetaOk.fds {st : OsState} {p : GoString} {m : OsMeta} {f : OsFile} (X : GMap w64 OsFd)
    (h : MetaOk st p m f) : MetaOk { st with fds := X } p m f :=
  ⟨h.size, h.named, h.lo, h.hi, h.ok, h.maps, h.targets⟩

theorem osCoh_fds {st : OsState} {Γb Γm Γf Γt} (hcoh : OsCoh st Γb Γm Γf Γt) (X : GMap w64 OsFd) :
    OsCoh { st with fds := X } Γb Γm X Γt :=
  { hcoh with
    fds := rfl
    meta_some := fun p m h => by
      obtain ⟨f, hf, hm⟩ := hcoh.meta_some p m h; exact ⟨f, hf, hm.fds X⟩ }

/-- `close(fd)`, with the whole fd. Whatever the errno, the fd is gone. -/
theorem wp_Close (fd : w64) (d : OsFd) (hE : ↑osN ⊆ E) :
    {{ osInv (L := L) ∗ osFd (L := L) fd (DFrac.own 1) d }}
      (ExternalOp osFsExt.name "Close" (Val (#fd))) @ s; E
    {{ (e : w64), RET #e; True }} := by
  iintro %Φ ⟨#Hinv, Hfd⟩ HΦ
  iapply wp_os_step "Close" (#fd) Φ (by simp) hE $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %h Hw
  unfold osWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hth, Hσ⟩
  obtain ⟨hwf, hcoh⟩ := Hwc
  unfold osFd
  icases gAuth_lookup _ _ _ _ _ _ $$ HAf Hfd with %Hfdl
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have hfd : st.fds !! fd = some d := hcoh.fds ▸ Hfdl
  have hwf' : ∀ X : GMap w64 OsFd, (∀ fd d, X !! fd = some d → st.fds !! fd = some d) →
      OsWf { st with fds := X } := fun X hX =>
    osWf_fds hwf X (fun fd d h => hwf.fds fd d (hX fd d h))
  have hdel : ∀ fd' d', (GMap.delete fd st.fds) !! fd' = some d' → st.fds !! fd' = some d' := by
    intro fd' d' h; rw [GMap.lookup_delete_iff] at h; split at h
    · cases h
    · exact h
  imodintro
  isplitr
  · ipureintro
    exact ⟨_, h, { st with fds := GMap.delete fd st.fds },
      ⟨fd, 0, d, rfl, hfd, rfl, rfl⟩, mapsFresh_same rfl,
      heapRendered_same (hwf' _ hdel) rfl (cellView_congr rfl rfl rfl) Hag⟩
  inext
  iintro %e' %h' %st' %Hst
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsOsStep] at Hst
  obtain ⟨fd', e, d', hv, hfd', rfl, rfl⟩ := Hst
  cases go.intoVal_inj hv
  imod gAuth_delete _ _ _ _ _ $$ HAf Hfd with HAf
  imod cells_same hwf (hwf' _ hdel) Hr Hfr rfl (cellView_congr rfl rfl rfl) $$ [Hσ Hcells]
    with ⟨Hσ, Hcells⟩
  · iframe
  imodintro
  iexists Γb, Γm, (GMap.delete fd Γf), Γt
  have htr : tokRes gooseOsGS { st with fds := GMap.delete fd st.fds } Γt =
      tokRes (gooseOsGS (L := L)) st Γt := rfl
  rw [htr]
  iframe
  isplitr
  · ipureintro; refine ⟨hwf' _ hdel, ?_⟩; rw [hcoh.fds]; exact osCoh_fds hcoh _
  iapply wp_value'
  iapply HΦ
  itrivial

end specs

end Perennial

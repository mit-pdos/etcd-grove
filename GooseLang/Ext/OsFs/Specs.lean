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
public import GooseLang.Ext.OsFs.Facts
public import Perennial.Golang.Defn.PostLang
public import Iris.Instances.Lib.Invariants

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode
open goose_heap

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
    have hk'' : (ti.saved.map (·, false))[i - affLo st ti.c]? = some (f.cur.getD i 0, false) := by
      rw [List.getElem?_map, hk']; rfl
    unfold tokRes
    icases BigSepM.bigSepM_lookup (Φ := fun (_t : Nat) (ti : TokInfo) =>
      iprop(gElem hL hL.γm ti.c.path (DFrac.own ti.q) (some ti.om) ∗
        bytesG hL ti.c.path (affLo st ti.c) (DFrac.own 1) (ti.saved.map (·, false))))
      hti $$ Htok with ⟨-, Hs⟩
    unfold bytesG
    icases BigSepL.bigSepL_lookup (Φ := fun k (x : w8 × Bool) =>
      gElem hL hL.γb (ti.c.path, affLo st ti.c + k) (DFrac.own 1) x) hk'' $$ Hs with Hs
    rw [show affLo st ti.c + (i - affLo st ti.c) = i by omega]
    icases gElem_valid_2 hL _ _ _ _ _ _ $$ Hs Hb with %Hv
    exact absurd (DFrac.valid_own_op Hv.1) (by simp)
  · ipureintro; exact hin

/-- A client's fraction of a file's `OsMeta` leaves the changes in flight on it only fractions:
none of them takes the whole. -/
theorem tokRes_meta_frac {st : OsState} {Γt : GMap Nat TokInfo} {p : GoString} {dq : DFrac}
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
        icases BigSepM.bigSepM_lookup (Φ := fun (_t : Nat) (ti : TokInfo) =>
          iprop(gElem hL hL.γm ti.c.path (DFrac.own ti.q) (some ti.om) ∗
            bytesG hL ti.c.path (affLo st ti.c) (DFrac.own 1) (ti.saved.map (·, false))))
          hti $$ Htok with ⟨Hs, -⟩
        rw [hp, hq]
        icases gElem_valid_2 hL _ _ _ _ _ _ $$ Hs Hm with %Hv
        exact absurd (DFrac.valid_own_op Hv.1) (by simp)
      · ipureintro; exact fun _ _ => hq
    · ipureintro; exact fun _ h => absurd h hp
  · ipureintro; exact fun h => absurd h hti

/-- The whole of a file's `OsMeta`: no change is in flight on it. -/
theorem tokRes_meta_whole {st : OsState} {Γt : GMap Nat TokInfo} {p : GoString}
    {mo : Option OsMeta} :
    ⊢ tokRes hL st Γt -∗ gElem hL hL.γm p (DFrac.own 1) mo -∗
      ⌜∀ t ti, Γt !! t = some ti → ti.c.path ≠ p⌝ := by
  iintro Htok Hm
  iapply pure_forall.2; iintro %t
  iapply pure_forall.2; iintro %ti
  by_cases hti : Γt !! t = some ti
  · by_cases hp : ti.c.path = p
    · unfold tokRes
      icases BigSepM.bigSepM_lookup (Φ := fun (_t : Nat) (ti : TokInfo) =>
        iprop(gElem hL hL.γm ti.c.path (DFrac.own ti.q) (some ti.om) ∗
          bytesG hL ti.c.path (affLo st ti.c) (DFrac.own 1) (ti.saved.map (·, false))))
        hti $$ Htok with ⟨Hs, -⟩
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
  bytesG (gooseOsGS (L := L)) p off dq xs

/-- The file at `p`: `some m`, it exists, as `m` says; `none`, it does not. -/
def osMeta (p : GoString) (dq : DFrac) (mo : Option OsMeta) : IProp GF :=
  gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γm p dq mo

/-- The fd `fd` is open, as `d` says. -/
def osFd (fd : w64) (dq : DFrac) (d : OsFd) : IProp GF :=
  gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γf fd dq d

/-- The change in flight `t`, as `ti` says. -/
def osTok (t : Nat) (ti : TokInfo) : IProp GF :=
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
for the view the state interpretation's half of the ghost variable names. -/
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

end resources

/-! ## The step of an operation -/

section step
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt] [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

/-- What an operation's proof works with: the state, its ghost maps, what the extension holds
of each change in flight, the invariant's share of the mapped cells, and the
heap. -/
def osWorld (st : OsState) (Γb : GMap (GoString × Nat) (w8 × Bool))
    (Γm : GMap GoString (Option OsMeta)) (Γf : GMap w64 OsFd) (Γt : GMap Nat TokInfo)
    (h : GMap Loc (NonAtomic val)) : IProp GF :=
  iprop(⌜OsWf st ∧ OsCoh st Γb Γm Γf Γt⌝ ∗
    gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γb Γb ∗ gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γm Γm ∗
    gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γf Γf ∗ gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γt Γt ∗
    tokRes (gooseOsGS (L := L)) st Γt ∗ cellsRes (cellView st) ∗ naHeapCtx tls h)

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
    exact ⟨e', h', st', g, Hst⟩
  inext
  iintro %e' %h' %σ' %g' %Hst -
  imod Hclose2
  imod Hcont $$ %e' %h' %σ' %Hst with ⟨%Γb', %Γm', %Γf', %Γt', Hw, Hwp⟩
  unfold osWorld
  icases Hw with ⟨%Hwc', HAb, HAm, HAf, HAt, Htok, Hcells, Hheap⟩
  imod gVar_update _ _ _ (cellView σ', GMap.size σ'.inflight) $$ Hv Hv' with ⟨Hv, Hv'⟩
  imod Hclose $$ [Hv' Hcells] with -
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

open Classical in
/-- The fd an open with the flags `fl` gives (as `IsOsStep` builds it). -/
def openFd (p : GoString) (fl : w64) : OsFd :=
  let acc := fl.toNat % 4
  ⟨p, acc ≠ O_WRONLY, acc ≠ O_RDONLY⟩

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt] [GoGlobalContext]
  [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}
attribute [local instance] Classical.propDecidable

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
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
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

theorem readSees_exists {st : OsState} {p : GoString} {f : OsFile} (hf : st.file p = some f)
    (off n : Nat) : ReadSees st p off n ((f.cur.drop off).take n) := by
  refine ⟨⟨st.size p, Or.inl rfl, ?_⟩, fun i hi _ => ?_⟩
  · rw [size_of_file hf]; simp
  · simp only [hf, Option.map_some, Option.bind_some]
    simp only [List.getElem_take, List.getElem_drop]
    exact List.getElem?_eq_getElem _

/-- The bytes a client holds are the file's, and under no change in flight. -/
theorem osBytes_lookup {st : OsState} {Γb Γm Γf Γt} (hcoh : OsCoh st Γb Γm Γf Γt) (p : GoString)
    (off : Nat) (dq : DFrac) (xs : List (w8 × Bool)) :
    ⊢ gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γb Γb -∗ tokRes (gooseOsGS (L := L)) st Γt -∗
      osBytes (L := L) p off dq xs -∗
      ⌜∀ k (hk : k < xs.length), ∃ f, st.file p = some f ∧ f.cur[off + k]? = some xs[k].1 ∧
        ¬ InflightAt st p (off + k)⌝ := by
  iintro HAb Htok Hbs
  iapply pure_forall.2; iintro %k
  iapply pure_forall.2; iintro %hk
  unfold osBytes bytesG
  icases BigSepL.bigSepL_lookup (Φ := fun k (x : w8 × Bool) =>
    gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γb (p, off + k) dq x)
    (List.getElem?_eq_getElem hk) $$ Hbs with Hb
  icases gAuth_lookup _ _ _ _ _ _ $$ HAb Hb with %Hx
  icases tokRes_byte_free _ hcoh Hx $$ Htok Hb with %Hn
  obtain ⟨f, hf, hb, -⟩ := hcoh.bytes p (off + k) _ Hx
  ipureintro; exact ⟨f, hf, hb, Hn⟩

theorem coh_meta {st : OsState} {Γb Γm Γf Γt} (hcoh : OsCoh st Γb Γm Γf Γt) {p : GoString}
    {m : OsMeta} (h : Γm !! p = some (some m)) :
    ∃ f, st.file p = some f ∧ MetaOk st p m f := by
  obtain ⟨f, hf, hm⟩ := hcoh.meta_some p m h
  exact ⟨f, file_eq_some.2 hf, hm⟩

/-- `flock(fd, how)`: any errno. -/
theorem wp_Flock (fd how : w64) (dq : DFrac) (d : OsFd) (hE : ↑osN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osFd (L := L) fd dq d -∗
      (∀ e : w64, osFd (L := L) fd dq d -∗ Φ (#e)) -∗
      WP (ExternalOp osFsExt.name "Flock" (Val (PairV (#fd) (#how)))) @ s; E {{ Φ }} := by
  iintro #Hinv Hfd HΦ
  iapply wp_os_step "Flock" _ Φ (by simp [val.isPanic]) hE $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %h Hw
  unfold osWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  obtain ⟨hwf, hcoh⟩ := Hwc
  unfold osFd
  icases gAuth_lookup _ _ _ _ _ _ $$ HAf Hfd with %Hfdl
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have hfd : st.fds !! fd = some d := hcoh.fds ▸ Hfdl
  imodintro
  isplitr
  · ipureintro
    exact ⟨_, h, st, ⟨fd, how, 0, d, rfl, hfd, rfl, rfl⟩, mapsFresh_same rfl,
      heapRendered_same hwf rfl rfl Hag⟩
  inext
  iintro %e' %h' %st' %Hst
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsOsStep] at Hst
  obtain ⟨fd', how', e, d', hv, -, rfl, rfl⟩ := Hst
  imod cells_same hwf hwf Hr Hfr rfl rfl $$ [Hσ Hcells] with ⟨Hσ, Hcells⟩
  · iframe
  imodintro
  iexists Γb, Γm, Γf, Γt
  iframe
  isplitr
  · ipureintro; exact ⟨hwf, hcoh⟩
  iapply wp_value'
  iapply HΦ $$ Hfd

/-- `fstat(fd)`'s size, with a fraction of the file's `OsMeta`: its size, or an errno. -/
theorem wp_Fstat (fd : w64) (dq dqm : DFrac) (d : OsFd) (m : OsMeta) (hE : ↑osN ⊆ E)
    (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osFd (L := L) fd dq d -∗ osMeta (L := L) d.path dqm (some m) -∗
      (∀ sz : w64, ∀ e : w64, ⌜e = 0 ∧ sz = (W64 m.size) ∨ e ≠ 0 ∧ sz = 0⌝ -∗
        osFd (L := L) fd dq d -∗ osMeta (L := L) d.path dqm (some m) -∗ Φ (PairV (#sz) (#e))) -∗
      WP (ExternalOp osFsExt.name "Fstat" (Val (#fd))) @ s; E {{ Φ }} := by
  iintro #Hinv Hfd Hm HΦ
  iapply wp_os_step "Fstat" _ Φ (by simp) hE $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %h Hw
  unfold osWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  obtain ⟨hwf, hcoh⟩ := Hwc
  unfold osFd osMeta
  icases gAuth_lookup _ _ _ _ _ _ $$ HAf Hfd with %Hfdl
  icases gAuth_lookup _ _ _ _ _ _ $$ HAm Hm with %Hml
  icases tokRes_meta_frac _ $$ Htok Hm with %Hq
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have hfd : st.fds !! fd = some d := hcoh.fds ▸ Hfdl
  obtain ⟨f, hf, hmo⟩ := coh_meta hcoh Hml
  have hnr := noReach_of_frac hcoh Hq
  imodintro
  isplitr
  · ipureintro
    exact ⟨_, h, st, ⟨fd, d, st.size d.path, rfl, hfd, Or.inl rfl, rfl, Or.inl rfl⟩,
      mapsFresh_same rfl, heapRendered_same hwf rfl rfl Hag⟩
  inext
  iintro %e' %h' %st' %Hst
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsOsStep] at Hst
  obtain ⟨fd', d', sz, hv, hfd', hss, rfl, hres⟩ := Hst
  cases go.intoVal_inj hv
  simp only [FdOpen, hfd, Option.some.injEq] at hfd'; subst hfd'
  have hsz := statSees_eq hnr hss
  rw [size_of_file hf, ← hmo.size] at hsz
  subst hsz
  imod cells_same hwf hwf Hr Hfr rfl rfl $$ [Hσ Hcells] with ⟨Hσ, Hcells⟩
  · iframe
  imodintro
  iexists Γb, Γm, Γf, Γt
  iframe
  isplitr
  · ipureintro; exact ⟨hwf, hcoh⟩
  rcases hres with rfl | ⟨e, he, rfl⟩
  · iapply wp_value'
    iapply HΦ $$ %_ %_ %(Or.inl ⟨rfl, rfl⟩) Hfd Hm
  · iapply wp_value'
    iapply HΦ $$ %_ %_ %(Or.inr ⟨he, rfl⟩) Hfd Hm

/-- `pread(fd, n, off)` of bytes the client holds (any fractions), with a fraction of the file's
`OsMeta`, so that the size is known: exactly the bytes from `off` up to `n` or the end of the
file; on failure, a prefix of them. -/
theorem wp_PRead (fd off n : w64) (dq dqm dqb : DFrac) (d : OsFd) (m : OsMeta)
    (xs : List (w8 × Bool)) (hE : ↑osN ⊆ E) (hrd : d.readable = true) (hoff : 0 ≤ off.toInt)
    (hlen : xs.length = min n.toNat (m.size - off.toNat)) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osFd (L := L) fd dq d -∗ osMeta (L := L) d.path dqm (some m) -∗
      osBytes (L := L) d.path off.toNat dqb xs -∗
      (∀ r : List w8, ∀ e : w64,
        ⌜e = 0 ∧ r = xs.map Prod.fst ∨ e ≠ 0 ∧ ∃ k ≤ xs.length, r = (xs.map Prod.fst).take k⌝ -∗
        osFd (L := L) fd dq d -∗ osMeta (L := L) d.path dqm (some m) -∗
        osBytes (L := L) d.path off.toNat dqb xs -∗ Φ (PairV (#r) (#e))) -∗
      WP (ExternalOp osFsExt.name "PRead" (Val (PairV (#fd) (PairV (#off) (#n))))) @ s; E
        {{ Φ }} := by
  iintro #Hinv Hfd Hm Hbs HΦ
  iapply wp_os_step "PRead" _ Φ (by simp [val.isPanic]) hE $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %h Hw
  unfold osWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  obtain ⟨hwf, hcoh⟩ := Hwc
  icases osBytes_lookup hcoh d.path off.toNat dqb xs $$ HAb Htok Hbs with %Hbl
  unfold osFd osMeta
  icases gAuth_lookup _ _ _ _ _ _ $$ HAf Hfd with %Hfdl
  icases gAuth_lookup _ _ _ _ _ _ $$ HAm Hm with %Hml
  icases tokRes_meta_frac _ $$ Htok Hm with %Hq
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have hfd : st.fds !! fd = some d := hcoh.fds ▸ Hfdl
  obtain ⟨f, hf, hmo⟩ := coh_meta hcoh Hml
  have hnr := noReach_of_frac hcoh Hq
  imodintro
  isplitr
  · ipureintro
    exact ⟨_, h, st, ⟨fd, off, n, d, _, rfl, hfd, hrd, hoff, readSees_exists hf _ _, rfl,
      Or.inl rfl⟩, mapsFresh_same rfl, heapRendered_same hwf rfl rfl Hag⟩
  inext
  iintro %e' %h' %st' %Hst
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsOsStep] at Hst
  obtain ⟨fd', off', n', d', r, hv, hfd', -, -, hrs, rfl, hres⟩ := Hst
  injection hv with h1 h2
  injection h2 with h3 h4
  cases go.intoVal_inj h1; cases go.intoVal_inj h3; cases go.intoVal_inj h4
  simp only [FdOpen, hfd, Option.some.injEq] at hfd'; subst hfd'
  -- the bytes read are the client's
  have hr : r = xs.map Prod.fst := by
    obtain ⟨⟨sz, hss, hrl⟩, hrb⟩ := hrs
    have hsz := statSees_eq hnr hss
    rw [size_of_file hf, ← hmo.size] at hsz
    subst hsz
    apply List.ext_getElem
    · rw [hrl, List.length_map, hlen]
    · intro i h1 h2
      have hi : i < xs.length := by simpa using h2
      obtain ⟨f', hf', hb, hn⟩ := Hbl i hi
      rw [hf] at hf'; cases hf'
      have := hrb i h1 hn
      simp only [hf, Option.map_some, Option.bind_some] at this
      rw [hb] at this
      simp only [List.getElem_map]
      exact (Option.some.inj this).symm
  subst hr
  imod cells_same hwf hwf Hr Hfr rfl rfl $$ [Hσ Hcells] with ⟨Hσ, Hcells⟩
  · iframe
  imodintro
  iexists Γb, Γm, Γf, Γt
  iframe
  isplitr
  · ipureintro; exact ⟨hwf, hcoh⟩
  rcases hres with rfl | ⟨k, e, hk, he, rfl⟩
  · iapply wp_value'
    iapply HΦ $$ %_ %_ %(Or.inl ⟨rfl, rfl⟩) Hfd Hm Hbs
  · iapply wp_value'
    iapply HΦ $$ %_ %_ %(Or.inr ⟨he, k, by simpa using hk, rfl⟩) Hfd Hm Hbs

/-- A racing `pread(fd, n, off)` (no `OsMeta`, as minibolt's `Snapshot`): where it reaches a
byte the client holds (any fraction), it reads it; on success it reaches every such byte below
`off + n`. Elsewhere the bytes, and how far past them it reads, are arbitrary. -/
theorem wp_PRead_racy (fd off n : w64) (dq dqb : DFrac) (d : OsFd) (lo : Nat)
    (xs : List (w8 × Bool)) (hE : ↑osN ⊆ E) (hrd : d.readable = true) (hoff : 0 ≤ off.toInt)
    (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osFd (L := L) fd dq d -∗ osBytes (L := L) d.path lo dqb xs -∗
      (∀ r : List w8, ∀ e : w64,
        ⌜∀ k (hk : k < xs.length), off.toNat ≤ lo + k → lo + k < off.toNat + n.toNat →
          (e = 0 → lo + k - off.toNat < r.length) ∧
          ∀ (h : lo + k - off.toNat < r.length), r[lo + k - off.toNat] = xs[k].1⌝ -∗
        osFd (L := L) fd dq d -∗ osBytes (L := L) d.path lo dqb xs -∗ Φ (PairV (#r) (#e))) -∗
      WP (ExternalOp osFsExt.name "PRead" (Val (PairV (#fd) (PairV (#off) (#n))))) @ s; E
        {{ Φ }} := by
  iintro #Hinv Hfd Hbs HΦ
  iapply wp_os_step "PRead" _ Φ (by simp [val.isPanic]) hE $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %h Hw
  unfold osWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  obtain ⟨hwf, hcoh⟩ := Hwc
  icases osBytes_lookup hcoh d.path lo dqb xs $$ HAb Htok Hbs with %Hbl
  unfold osFd
  icases gAuth_lookup _ _ _ _ _ _ $$ HAf Hfd with %Hfdl
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have hfd : st.fds !! fd = some d := hcoh.fds ▸ Hfdl
  obtain ⟨f, hf⟩ := hwf.fds fd d hfd
  imodintro
  isplitr
  · ipureintro
    exact ⟨_, h, st, ⟨fd, off, n, d, _, rfl, hfd, hrd, hoff, readSees_exists hf _ _, rfl,
      Or.inl rfl⟩, mapsFresh_same rfl, heapRendered_same hwf rfl rfl Hag⟩
  inext
  iintro %e' %h' %st' %Hst
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsOsStep] at Hst
  obtain ⟨fd', off', n', d', r, hv, hfd', -, -, hrs, rfl, hres⟩ := Hst
  injection hv with h1 h2
  injection h2 with h3 h4
  cases go.intoVal_inj h1; cases go.intoVal_inj h3; cases go.intoVal_inj h4
  simp only [FdOpen, hfd, Option.some.injEq] at hfd'; subst hfd'
  obtain ⟨⟨sz, hss, hrl⟩, hrb⟩ := hrs
  have key : ∀ k (hk : k < xs.length), off.toNat ≤ lo + k → lo + k < off.toNat + n.toNat →
      lo + k - off.toNat < r.length ∧
      ∀ (h : lo + k - off.toNat < r.length), r[lo + k - off.toNat] = xs[k].1 := by
    intro k hk h1 h2
    obtain ⟨f', hf', hb, hn⟩ := Hbl k hk
    rw [hf] at hf'; cases hf'
    have hlt : lo + k < f.cur.length := (List.getElem?_eq_some_iff.1 hb).1
    have hgt := statSees_gt hf hlt hn hss
    refine ⟨by rw [hrl]; omega, fun hlt' => ?_⟩
    have hn' : ¬ InflightAt st' d.path (off.toNat + (lo + k - off.toNat)) := by
      rw [show off.toNat + (lo + k - off.toNat) = lo + k by omega]; exact hn
    have := hrb _ hlt' hn'
    simp only [hf, Option.map_some, Option.bind_some] at this
    rw [show off.toNat + (lo + k - off.toNat) = lo + k by omega, hb] at this
    exact (Option.some.inj this).symm
  imod cells_same hwf hwf Hr Hfr rfl rfl $$ [Hσ Hcells] with ⟨Hσ, Hcells⟩
  · iframe
  imodintro
  iexists Γb, Γm, Γf, Γt
  iframe
  isplitr
  · ipureintro; exact ⟨hwf, hcoh⟩
  rcases hres with rfl | ⟨k', e, hk', he, rfl⟩
  · iapply wp_value'
    iapply HΦ $$ %_ %_ %(fun k hk h1 h2 => ⟨fun _ => (key k hk h1 h2).1, (key k hk h1 h2).2⟩)
      Hfd Hbs
  · iapply wp_value'
    iapply HΦ $$ %_ %_ %(fun k hk h1 h2 => ⟨fun h => absurd h he, fun hlt => by
      have h' : lo + k - off.toNat < r.length := by simp at hlt; omega
      simp only [List.getElem_take]; exact (key k hk h1 h2).2 h'⟩) Hfd Hbs

/-- The `OsMeta` after a successful sync: the size is durable. -/
def OsMeta.synced (m : OsMeta) : OsMeta := { m with lo := m.size, hi := m.size }

/-- The bytes after a successful sync: clean, unless a failed sync may have lost one. -/
def syncedBytes (m : OsMeta) (xs : List (w8 × Bool)) : List (w8 × Bool) :=
  if m.ok then xs.map (fun x => (x.1, true)) else xs

/-- `fsync(fd)` (and `fdatasync`), with the whole of the file's `OsMeta`, so that no change is in
flight on it, and some of its bytes, whole. On success the size is durable, and the bytes are
clean unless a failed sync lost one (`m.ok`); on failure, nothing more is clean, and bytes may
be lost (`ok := false`). -/
theorem wp_Fsync (fd : w64) (dq : DFrac) (d : OsFd) (m : OsMeta) (lo : Nat)
    (xs : List (w8 × Bool)) (hE : ↑osN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osFd (L := L) fd dq d -∗ osMeta (L := L) d.path (DFrac.own 1) (some m) -∗
      osBytes (L := L) d.path lo (DFrac.own 1) xs -∗
      (∀ e : w64,
        ((⌜e = 0⌝ ∗ osMeta (L := L) d.path (DFrac.own 1) (some m.synced) ∗
            osBytes (L := L) d.path lo (DFrac.own 1) (syncedBytes m xs)) ∨
         (⌜e ≠ 0⌝ ∗ osMeta (L := L) d.path (DFrac.own 1) (some { m with ok := false }) ∗
            osBytes (L := L) d.path lo (DFrac.own 1) xs)) -∗
        osFd (L := L) fd dq d -∗ Φ (#e)) -∗
      WP (ExternalOp osFsExt.name "Fsync" (Val (#fd))) @ s; E {{ Φ }} := by
  iintro #Hinv Hfd Hm Hbs HΦ
  iapply wp_os_step "Fsync" _ Φ (by simp) hE $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %h Hw
  unfold osWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  obtain ⟨hwf, hcoh⟩ := Hwc
  unfold osFd osMeta osBytes
  icases bytesG_lookup _ d.path lo _ xs Γb $$ HAb Hbs with %Hbl
  icases gAuth_lookup _ _ _ _ _ _ $$ HAf Hfd with %Hfdl
  icases gAuth_lookup _ _ _ _ _ _ $$ HAm Hm with %Hml
  icases tokRes_meta_whole _ $$ Htok Hm with %Hnt
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have hfd : st.fds !! fd = some d := hcoh.fds ▸ Hfdl
  obtain ⟨f, hf, hmo⟩ := coh_meta hcoh Hml
  have hnoI : ∀ i, ¬ InflightAt st d.path i := by
    rintro i ⟨t, c, ht, hcp, -⟩; exact noTok_of_whole hcoh Hnt t c ht hcp
  have hcohf : FileCoherent f := fun i => hwf.coherent d.path f i hf
  have hszf := hwf.sizes d.path f hf
  -- the two outcomes
  have hwfS : OsWf (st.setFile d.path (f.synced (InflightAt st d.path ·))) :=
    osWf_setFile_sameCur hwf hf rfl (by simp [OsFile.synced])
      (synced_coherent f _ hcohf hnoI)
  have hwfF : OsWf (st.setFile d.path (f.syncFailed (InflightAt st d.path ·))) :=
    osWf_setFile_sameCur hwf hf rfl hszf (syncFailed_coherent f _ hcohf hnoI)
  imodintro
  isplitr
  · ipureintro
    exact ⟨_, h, _, ⟨fd, d, f, rfl, hfd, hf, .inl ⟨rfl, rfl⟩⟩, mapsFresh_same rfl,
      heapRendered_same hwfS rfl (cellView_setFile_sameCur hwf hwfS hf rfl) Hag⟩
  inext
  iintro %e' %h' %st' %Hst
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsOsStep] at Hst
  obtain ⟨fd', d', f', hv, hfd', hf', hres⟩ := Hst
  cases go.intoVal_inj hv
  simp only [FdOpen, hfd, Option.some.injEq] at hfd'; subst hfd'
  rw [hf] at hf'; cases hf'
  have hs := sizes_setFile_sameCur (f' := f.synced (InflightAt st d.path ·)) hf rfl
  have hsF := sizes_setFile_sameCur (f' := f.syncFailed (InflightAt st d.path ·)) hf rfl
  rcases hres with ⟨rfl, rfl⟩ | ⟨e, he, rfl, rfl⟩
  · -- success
    have hkeep : ∀ i, CleanPhys f i → CleanPhys (f.synced (InflightAt st d.path ·)) i :=
      fun i hc => synced_clean f _ hcohf hnoI i (by have := hc.2.2.1; omega) hc.2.1
    imod gAuth_update _ _ _ _ _ (some m.synced) $$ HAm Hm with ⟨HAm, Hm⟩
    imod bytesG_update _ d.path lo xs (syncedBytes m xs) Γb
      (by unfold syncedBytes; split <;> simp) $$ [HAb Hbs] with ⟨HAb, Hbs⟩
    · iframe
    imod cells_same hwf hwfS Hr Hfr rfl (cellView_setFile_sameCur hwf hwfS hf rfl)
      $$ [Hσ Hcells] with ⟨Hσ, Hcells⟩
    · iframe
    imodintro
    iexists _, _, Γf, Γt
    have htr : tokRes gooseOsGS (st.setFile d.path (f.synced (InflightAt st d.path ·))) Γt =
        tokRes (gooseOsGS (L := L)) st Γt := by
      unfold tokRes; simp only [affLo_congr hs]
    rw [htr]
    iframe
    isplitr
    · ipureintro
      refine ⟨hwfS, osCoh_setFile_sameCur (f' := f.synced (InflightAt st d.path ·)) hcoh hf rfl
        ?_ lo xs (syncedBytes m xs)
        (by unfold syncedBytes; split <;> simp) Hbl ?_ hkeep ?_ hnoI⟩
      · exact ⟨by simp [OsMeta.synced, hmo.size]; rfl,
          by simp [OsMeta.synced, OsFile.synced, hmo.named],
          by simp [OsMeta.synced, OsFile.synced, hmo.size],
          by simp [OsMeta.synced, OsFile.synced, hmo.size],
          (fun hok i => by
            simp only [OsMeta.synced] at hok
            simp [OsFile.synced, hmo.ok hok i]),
          hmo.maps, fun t c ht hcp => absurd hcp (noTok_of_whole hcoh Hnt t c ht)⟩
      · intro k hk; unfold syncedBytes at hk ⊢; split <;> simp
      · intro k hk hc
        have hk' : k < xs.length := by unfold syncedBytes at hk; split at hk <;> simpa using hk
        obtain ⟨f1, h1, hb, hc1⟩ := hcoh.bytes _ _ _ (Hbl k hk')
        rw [hf] at h1; cases h1
        unfold syncedBytes at hc; split at hc
        · rename_i hok
          exact synced_clean f _ hcohf hnoI _ (List.getElem?_eq_some_iff.1 hb).1 (hmo.ok hok _)
        · exact hkeep _ (hc1 hc).1
    iapply wp_value'
    iapply HΦ $$ [Hm Hbs] Hfd
    ileft; iframe; ipureintro; rfl
  · -- failure
    have hkeep : ∀ i, CleanPhys f i → CleanPhys (f.syncFailed (InflightAt st d.path ·)) i :=
      fun i hc => syncFailed_clean f _ i hc
    imod gAuth_update _ _ _ _ _ (some { m with ok := false }) $$ HAm Hm with ⟨HAm, Hm⟩
    imod bytesG_update _ d.path lo xs xs Γb rfl $$ [HAb Hbs] with ⟨HAb, Hbs⟩
    · iframe
    imod cells_same hwf hwfF Hr Hfr rfl (cellView_setFile_sameCur hwf hwfF hf rfl)
      $$ [Hσ Hcells] with ⟨Hσ, Hcells⟩
    · iframe
    imodintro
    iexists _, _, Γf, Γt
    have htr : tokRes gooseOsGS (st.setFile d.path (f.syncFailed (InflightAt st d.path ·))) Γt =
        tokRes (gooseOsGS (L := L)) st Γt := by
      unfold tokRes; simp only [affLo_congr hsF]
    rw [htr]
    iframe
    isplitr
    · ipureintro
      refine ⟨hwfF, osCoh_setFile_sameCur (f' := f.syncFailed (InflightAt st d.path ·)) hcoh hf
        rfl ?_ lo xs xs rfl Hbl (fun _ _ => rfl)
        hkeep ?_ hnoI⟩
      · exact ⟨hmo.size, hmo.named, hmo.lo, hmo.hi, (fun h => by cases h), hmo.maps,
          fun t c ht hcp => absurd hcp (noTok_of_whole hcoh Hnt t c ht)⟩
      · intro k hk hc
        obtain ⟨f1, h1, -, hc1⟩ := hcoh.bytes _ _ _ (Hbl k hk)
        rw [hf] at h1; cases h1
        exact hkeep _ (hc1 hc).1
    iapply wp_value'
    iapply HΦ $$ [Hm Hbs] Hfd
    iright; iframe; ipureintro; exact he

/-- `mmap(nil, len, PROT_READ, MAP_SHARED[|MAP_POPULATE], fd, 0)`, with the whole of the file's
`OsMeta`, so that no change is in flight on it: on success, fresh cells at `base`, whose client
halves hold the file's bytes, then holes past its end, inside the address space; on failure,
`nil`. -/
theorem wp_Mmap (fd off len prot fl : w64) (dq : DFrac) (d : OsFd) (m : OsMeta) (hE : ↑osN ⊆ E)
    (hrd : d.readable = true) (hoff : off = 0) (hlen : 0 < len.toInt)
    (hprot : prot.toNat = PROT_READ)
    (hfl : fl.toNat = MAP_SHARED ∨ fl.toNat = MAP_SHARED + MAP_POPULATE) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osFd (L := L) fd dq d -∗ osMeta (L := L) d.path (DFrac.own 1) (some m) -∗
      (∀ base : Loc, ∀ e : w64,
        ((⌜e = 0 ∧ 0 < base.addr ∧ base.addr + len.toNat ≤ maxAddr⌝ ∗
            osMeta (L := L) d.path (DFrac.own 1) (some { m with maps := <[base := len.toNat]> m.maps }) ∗
            ∃ bs : List w8, ⌜bs.length = m.size⌝ ∗
              cellsR base 0 len.toNat (fun i => toCellVal bs[i]?)) ∨
         (⌜e ≠ 0 ∧ base = null⌝ ∗ osMeta (L := L) d.path (DFrac.own 1) (some m))) -∗
        osFd (L := L) fd dq d -∗ Φ (PairV (#base) (#e))) -∗
      WP (ExternalOp osFsExt.name "Mmap"
        (Val (PairV (#fd) (PairV (#off) (PairV (#len) (PairV (#prot) (#fl))))))) @ s; E {{ Φ }} := by
  iintro #Hinv Hfd Hm HΦ
  iapply wp_os_step "Mmap" _ Φ (by simp [val.isPanic]) hE $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %h Hw
  unfold osWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  obtain ⟨hwf, hcoh⟩ := Hwc
  unfold osFd osMeta
  icases gAuth_lookup _ _ _ _ _ _ $$ HAf Hfd with %Hfdl
  icases gAuth_lookup _ _ _ _ _ _ $$ HAm Hm with %Hml
  icases tokRes_meta_whole _ $$ Htok Hm with %Hnt
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have hfd : st.fds !! fd = some d := hcoh.fds ▸ Hfdl
  obtain ⟨f, hf, hmo⟩ := coh_meta hcoh Hml
  have hnt := noTok_of_whole hcoh Hnt
  have hnb : ¬ BusyAt st d.path := by rintro ⟨t, c, ht, hcp⟩; exact hnt t c ht hcp
  have hnoI : ∀ i, ¬ InflightAt st d.path i := by
    rintro i ⟨t, c, ht, hcp, -⟩; exact hnt t c ht hcp
  imodintro
  isplitr
  · ipureintro
    exact ⟨_, h, st, ⟨fd, off, len, prot, fl, d, rfl, hfd, hrd, hoff, hlen, hprot, hfl, hnb,
      .inr ⟨1, by decide, rfl, rfl⟩⟩, mapsFresh_same rfl, heapRendered_same hwf rfl rfl Hag⟩
  inext
  iintro %e' %h' %st' %Hst
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsOsStep] at Hst
  obtain ⟨fd', off', len', prot', fl', d', hv, hfd', -, -, hlen', -, -, -, hres⟩ := Hst
  injection hv with h1 h2; injection h2 with h3 h4; injection h4 with h5 h6
  injection h6 with h7 h8
  cases go.intoVal_inj h1; cases go.intoVal_inj h5
  simp only [FdOpen, hfd, Option.some.injEq] at hfd'; subst hfd'
  have hn0 : 0 < len.toNat := by
    have := BitVec.toInt_eq_toNat_cond len
    split at this <;> omega
  rcases hres with ⟨base, hpos, -, hnone, hst', rfl⟩ | ⟨e, he, rfl, rfl⟩
  · -- success
    generalize hn : len.toNat = n at hst' hn0 ⊢
    have hfresh := Hfr base ⟨d.path, n⟩ (by rw [hst']; exact GMap.lookup_insert _ _ _) hnone
    obtain ⟨hmax, hfree⟩ := hfresh
    -- the new cells were not mapped
    have hnotmapped : ∀ k, k < n → ¬ Mapped st (base +ₗ (k : Int)) := by
      intro k hk hm
      obtain ⟨x, hx⟩ := cellView_isSome hwf hm
      obtain ⟨m0, hm0⟩ := Hag _ x hx
      rw [hfree k (by simpa using hk)] at hm0; cases hm0
    have hwf' : OsWf st' := by
      rw [hst']
      refine { hwf with maps := ?_, maps_disj := ?_ }
      · intro b m0 hb
        simp only [GMap.lookup_insert_eq_iff] at hb
        split at hb
        · rename_i heq; subst heq; cases hb; exact ⟨⟨f, hf⟩, hpos, by simpa using hmax, hn0⟩
        · exact hwf.maps b m0 hb
      · intro b1 m1 b2 m2 hb1 hb2 hne
        simp only [GMap.lookup_insert_eq_iff] at hb1 hb2
        have key : ∀ b m0, st.maps !! b = some m0 →
            base.addr + n ≤ b.addr ∨ b.addr + m0.len ≤ base.addr := by
          intro b m0 hb
          obtain ⟨-, -, -, hl0⟩ := hwf.maps b m0 hb
          apply Classical.byContradiction; intro hc
          simp only [not_or, Int.not_le] at hc
          by_cases hle : b.addr ≤ base.addr
          · apply hnotmapped 0 hn0
            exact ⟨m0.path, (base.addr - b.addr).toNat, b, m0, hb, rfl, by omega,
              by cases b; cases base; simp [Loc.add] at *; omega⟩
          · apply hnotmapped (b.addr - base.addr).toNat (by omega)
            exact ⟨m0.path, 0, b, m0, hb, rfl, hl0, by cases b; cases base; simp [Loc.add] at *; omega⟩
        split at hb1 <;> split at hb2
        · subst_vars; exact absurd rfl hne
        · subst_vars; cases hb1; exact key b2 m2 hb2
        · subst_vars; cases hb2; exact (key b1 m1 hb1).symm
        · exact hwf.maps_disj b1 m1 b2 m2 hb1 hb2 hne
    have hI : ∀ q i, InflightAt st' q i = InflightAt st q i := fun q i => by rw [hst']; rfl
    have hT : ((List.range n).map (fun (k : Nat) => base +ₗ (k : Int))).Nodup :=
      by
        unfold List.Nodup; rw [List.pairwise_map]
        exact List.nodup_range.imp (fun {a b} hab he => hab (by have := loc_add_inj _ he; omega))
    have hmemT : ∀ l, l ∈ (List.range n).map (fun (k : Nat) => base +ₗ (k : Int)) ↔
        ∃ k, k < n ∧ l = base +ₗ (k : Int) := by
      intro l; simp only [List.mem_map, List.mem_range]; constructor
      · rintro ⟨k, hk, rfl⟩; exact ⟨k, hk, rfl⟩
      · rintro ⟨k, hk, rfl⟩; exact ⟨k, hk, rfl⟩
    have hmapsT : ∀ k, k < n → MapsTo st' (base +ₗ (k : Int)) d.path k :=
      fun k hk => ⟨base, ⟨d.path, n⟩, by rw [hst']; exact GMap.lookup_insert _ _ _, rfl, hk, rfl⟩
    let vf : Nat → val := fun i => toCellVal f.cur[i]?
    have hcb : ∀ i, cellByte st' d.path i = f.cur[i]? := fun i => by
      subst hst'; exact cellByte_noinfl (st := { st with maps := _ }) hf (hnoI i)
    imod cells_step st st' h h' _ ∅ (mkCellsR base vf 0 n) hwf hwf' Hr Hfr
      (fun b m0 hb => by
        simp only [hst', GMap.lookup_insert_eq_iff] at hb
        split at hb
        · subst_vars; exact .inl hnone
        · exact .inr hb)
      hT
      (fun l hl => by
        obtain ⟨k, hk, rfl⟩ := (hmemT l).1 hl; exact .inr ⟨_, _, hmapsT k hk⟩)
      (fun l v h => by simp at h)
      (fun l v hl => by
        rw [lookup_mkCellsR] at hl
        split at hl
        · rename_i hc
          cases hl
          have hl' : l = base +ₗ ((l.addr - base.addr).toNat : Int) := by
            cases l; cases base; simp [Loc.add] at hc ⊢; omega
          refine ⟨(hmemT l).2 ⟨_, by omega, hl'⟩, _, ?_, rfl⟩
          rw [hl', cellView_mapsTo hwf' (hmapsT _ (by omega)), hI, hcb]
          simp only [hnoI, decide_false, Option.some.injEq, Prod.mk.injEq, and_true]
          congr 2; simp only [Loc.add]; omega
        · cases hl)
      (fun l hl _ x hx => absurd (mapped_of_cellView hx) (by
        obtain ⟨k, hk, rfl⟩ := (hmemT l).1 hl; exact hnotmapped k hk))
      (fun l hl hc => by
        obtain ⟨k, hk, rfl⟩ := (hmemT l).1 hl
        rw [lookup_mkCellsR, dif_pos (by simp [Loc.add]; omega)] at hc; cases hc)
      (fun l hl => by
        apply cellView_lookup_congr hwf hwf' (by rw [hst']) (by rw [hst'])
        intro q i
        constructor
        · rintro ⟨b, m0, hb, hp, hi, rfl⟩
          simp only [hst', GMap.lookup_insert_eq_iff] at hb
          split at hb
          · subst_vars; cases hb; exact absurd ((hmemT _).2 ⟨i, hi, rfl⟩) hl
          · exact ⟨b, m0, hb, hp, hi, rfl⟩
        · rintro ⟨b, m0, hb, hp, hi, rfl⟩
          refine ⟨b, m0, ?_, hp, hi, rfl⟩
          simp only [hst', GMap.lookup_insert_eq_iff]
          split
          · subst_vars; rw [hnone] at hb; cases hb
          · exact hb)
      $$ [Hσ Hcells] with ⟨Hσ, Hcells, Hout⟩
    · iframe; unfold halves; iapply BigSepM.bigSepM_empty.2; iempintro
    imod gAuth_update _ _ _ _ _ (some { m with maps := <[base := n]> m.maps }) $$ HAm Hm
      with ⟨HAm, Hm⟩
    imodintro
    iexists Γb, _, Γf, Γt
    have htr : tokRes gooseOsGS st' Γt = tokRes (gooseOsGS (L := L)) st Γt := by rw [hst']; rfl
    rw [htr]
    iframe
    isplitr
    · ipureintro
      rw [hst']
      refine ⟨hst' ▸ hwf', osCoh_setMaps hcoh _ _ ?_ ?_ ?_⟩
      · intro q; simp only [GMap.lookup_insert_eq_iff]; split
        · subst_vars; simp [Hml]
        · rfl
      · intro q; simp only [GMap.lookup_insert_eq_iff]; split
        · subst_vars; simp [Hml]
        · rfl
      · intro q m' hq
        simp only [GMap.lookup_insert_eq_iff] at hq
        split at hq
        · subst_vars; cases hq
          refine ⟨m, Hml, rfl, rfl, rfl, rfl, rfl, fun b len0 => ?_⟩
          simp only [GMap.lookup_insert_eq_iff]
          split
          · simp
          · exact hmo.maps b len0
        · rename_i hpq
          refine ⟨m', hq, rfl, rfl, rfl, rfl, rfl, fun b len0 => ?_⟩
          obtain ⟨f1, -, hmo1⟩ := hcoh.meta_some q m' hq
          rw [hmo1.maps b len0]
          simp only [GMap.lookup_insert_eq_iff]
          split
          · subst_vars; rw [hnone]; simp only [reduceCtorEq, false_iff, Option.some.injEq]
            intro h; cases h; exact hpq rfl
          · rfl
    iapply wp_value'
    iapply HΦ $$ [Hm Hout] Hfd
    ileft
    iframe Hm
    isplitr
    · ipureintro; exact ⟨rfl, hpos, by simpa using hmax⟩
    iexists f.cur
    isplitr
    · ipureintro; exact hmo.size.symm
    iapply (cellsR_halves base 0 vf n).2 $$ Hout
  · -- failure
    imod cells_same hwf hwf Hr Hfr rfl rfl $$ [Hσ Hcells] with ⟨Hσ, Hcells⟩
    · iframe
    imodintro
    iexists Γb, Γm, Γf, Γt
    iframe
    isplitr
    · ipureintro; exact ⟨hwf, hcoh⟩
    iapply wp_value'
    iapply HΦ $$ [Hm] Hfd
    iright
    iframe
    ipureintro; exact ⟨he, rfl⟩

/-- `munmap` of a whole mapping (`unix.Munmap(b)`), with the whole of the file's `OsMeta` and
the client halves of all the mapping's cells. On success the mapping and its cells are gone; on
failure, it may be gone, or still there, with its cells back. -/
theorem wp_Munmap (base : Loc) (len cap : w64) (p : GoString) (m : OsMeta) (n : Nat)
    (vf : Nat → val) (hE : ↑osN ⊆ E) (hb : m.maps !! base = some n) (hlen : len.toNat = n)
    (hcap : cap.toNat = n) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osMeta (L := L) p (DFrac.own 1) (some m) -∗ cellsR base 0 n vf -∗
      (∀ e : w64,
        ((⌜e = 0⌝ ∗ osMeta (L := L) p (DFrac.own 1) (some { m with maps := GMap.delete base m.maps })) ∨
         (⌜e ≠ 0⌝ ∗
           (osMeta (L := L) p (DFrac.own 1) (some { m with maps := GMap.delete base m.maps }) ∨
            (osMeta (L := L) p (DFrac.own 1) (some m) ∗ cellsR base 0 n vf)))) -∗ Φ (#e)) -∗
      WP (ExternalOp osFsExt.name "Munmap" (Val (PairV (#base) (PairV (#len) (#cap))))) @ s; E
        {{ Φ }} := by
  iintro #Hinv Hm Hc HΦ
  iapply wp_os_step "Munmap" _ Φ (by simp [val.isPanic]) hE $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %h Hw
  unfold osWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  obtain ⟨hwf, hcoh⟩ := Hwc
  unfold osMeta
  icases gAuth_lookup _ _ _ _ _ _ $$ HAm Hm with %Hml
  icases tokRes_meta_whole _ $$ Htok Hm with %Hnt
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  obtain ⟨f, hf, hmo⟩ := coh_meta hcoh Hml
  have hnt := noTok_of_whole hcoh Hnt
  have hnoI : ∀ i, ¬ InflightAt st p i := by
    rintro i ⟨t, c, ht, hcp, -⟩; exact hnt t c ht hcp
  have hbase : st.maps !! base = some ⟨p, n⟩ := (hmo.maps base n).1 hb
  imodintro
  isplitr
  · ipureintro
    exact ⟨_, h, st, ⟨base, len, cap, ⟨p, n⟩, rfl, hbase, hlen, hcap,
      .inr ⟨1, by decide, rfl, .inl rfl⟩⟩, mapsFresh_same rfl, heapRendered_same hwf rfl rfl Hag⟩
  inext
  iintro %e' %h' %st' %Hst
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsOsStep] at Hst
  obtain ⟨base', len', cap', m0, hv, hm0, -, -, hres⟩ := Hst
  injection hv with h1 h2; injection h2 with h3 h4
  cases go.intoVal_inj h1
  rw [hbase] at hm0; cases hm0
  -- the state without the mapping
  have hunmap : ∀ st1 : OsState, st1 = { st with maps := GMap.delete base st.maps } →
      OsWf st1 ∧ OsCoh st1 Γb (<[p := some { m with maps := GMap.delete base m.maps }]> Γm) Γf Γt ∧
      (HeapRendered st st1 h h' → MapsFresh st st1 h →
        (naHeapCtx tls h ∗ cellsRes (GF := GF) (cellView st) ∗ cellsR base 0 n vf ⊢
          |==> (naHeapCtx tls h' ∗ cellsRes (cellView st1)))) := by
    intro st1 hst1
    have hT : ((List.range n).map (fun (k : Nat) => base +ₗ (k : Int))).Nodup := by
      unfold List.Nodup; rw [List.pairwise_map]
      exact List.nodup_range.imp (fun {a b} hab he => hab (by have := loc_add_inj _ he; omega))
    have hmemT : ∀ l, l ∈ (List.range n).map (fun (k : Nat) => base +ₗ (k : Int)) ↔
        ∃ k, k < n ∧ l = base +ₗ (k : Int) := by
      intro l; simp only [List.mem_map, List.mem_range]; constructor
      · rintro ⟨k, hk, rfl⟩; exact ⟨k, hk, rfl⟩
      · rintro ⟨k, hk, rfl⟩; exact ⟨k, hk, rfl⟩
    have hwf1 : OsWf st1 := by
      rw [hst1]
      refine { hwf with maps := fun b m1 h1 => ?_, maps_disj := fun b1 m1 b2 m2 h1 h2 => ?_ }
      · simp only [GMap.lookup_delete_iff] at h1; split at h1
        · cases h1
        · exact hwf.maps b m1 h1
      · simp only [GMap.lookup_delete_iff] at h1 h2; split at h1
        · cases h1
        · split at h2
          · cases h2
          · exact hwf.maps_disj b1 m1 b2 m2 h1 h2
    -- a cell of the mapping is mapped by no other
    have hother : ∀ k, k < n → ∀ q j, ¬ MapsTo st1 (base +ₗ (k : Int)) q j := by
      rintro k hk q j ⟨b, m1, h1, -, hj, he⟩
      rw [hst1] at h1
      simp only [GMap.lookup_delete_iff] at h1; split at h1
      · cases h1
      · rename_i hne
        have hd := hwf.maps_disj b m1 base ⟨p, n⟩ h1 hbase (fun e => hne e.symm)
        have : base.addr + k = b.addr + j := by simpa [Loc.add] using congrArg Loc.addr he
        simp at hd; omega
    refine ⟨hwf1, ?_, fun Hr Hfr => ?_⟩
    · rw [hst1]
      refine osCoh_setMaps hcoh _ _ ?_ ?_ ?_
      · intro q; simp only [GMap.lookup_insert_eq_iff]; split
        · subst_vars; simp [Hml]
        · rfl
      · intro q; simp only [GMap.lookup_insert_eq_iff]; split
        · subst_vars; simp [Hml]
        · rfl
      · intro q m' hq
        simp only [GMap.lookup_insert_eq_iff] at hq
        split at hq
        · subst_vars; cases hq
          refine ⟨m, Hml, rfl, rfl, rfl, rfl, rfl, fun b len0 => ?_⟩
          simp only [GMap.lookup_delete_iff]
          split
          · simp
          · exact hmo.maps b len0
        · rename_i hpq
          refine ⟨m', hq, rfl, rfl, rfl, rfl, rfl, fun b len0 => ?_⟩
          obtain ⟨f1, -, hmo1⟩ := hcoh.meta_some q m' hq
          rw [hmo1.maps b len0]
          simp only [GMap.lookup_delete_iff]
          split
          · subst_vars; rw [hbase]; simp only [reduceCtorEq, iff_false, Option.some.injEq]
            intro h; cases h; exact hpq rfl
          · rfl
    · iintro ⟨Hσ, Hcells, Hc⟩
      ihave Hc := (cellsR_halves base 0 vf n).1 $$ Hc
      imod cells_step st st1 h h' _ (mkCellsR base vf 0 n) ∅ hwf hwf1 Hr Hfr
        (fun b m1 h1 => by
          rw [hst1] at h1; simp only [GMap.lookup_delete_iff] at h1; split at h1
          · cases h1
          · exact .inr h1)
        hT
        (fun l hl => by
          obtain ⟨k, hk, rfl⟩ := (hmemT l).1 hl; exact .inl ⟨p, k, base, _, hbase, rfl, hk, rfl⟩)
        (fun l v hl => by
          have hl0 := hl
          rw [lookup_mkCellsR] at hl0
          split at hl0
          · rename_i hc
            obtain ⟨k, hk, rfl⟩ : ∃ k, k < n ∧ l = base +ₗ (k : Int) :=
              ⟨(l.addr - base.addr).toNat, by omega,
                by cases l; cases base; simp [Loc.add] at hc ⊢; omega⟩
            refine ⟨(hmemT _).2 ⟨k, hk, rfl⟩, cellByte st p k, ?_⟩
            rw [cellView_mapsTo hwf ⟨base, _, hbase, rfl, hk, rfl⟩]
            simp [hnoI]
          · cases hl0)
        (fun l v h => by simp at h)
        (fun l hl hc => by
          obtain ⟨k, hk, rfl⟩ := (hmemT l).1 hl
          rw [lookup_mkCellsR, dif_pos (by simp [Loc.add]; omega)] at hc; cases hc)
        (fun l hl _ x hx => by
          obtain ⟨k, hk, rfl⟩ := (hmemT l).1 hl
          obtain ⟨q, j, hqj⟩ := mapped_of_cellView hx
          exact absurd hqj (hother k hk q j))
        (fun l hl => by
          apply cellView_lookup_congr hwf hwf1 (by rw [hst1]) (by rw [hst1])
          intro q i
          constructor
          · rintro ⟨b, m1, h1, hp, hi, rfl⟩
            rw [hst1] at h1; simp only [GMap.lookup_delete_iff] at h1; split at h1
            · cases h1
            · exact ⟨b, m1, h1, hp, hi, rfl⟩
          · rintro ⟨b, m1, h1, hp, hi, rfl⟩
            refine ⟨b, m1, ?_, hp, hi, rfl⟩
            rw [hst1]
            by_cases hbb : base = b
            · subst hbb; rw [hbase] at h1; cases h1
              exact absurd ((hmemT _).2 ⟨i, hi, rfl⟩) hl
            · exact (GMap.lookup_delete_ne _ hbb).trans h1)
        $$ [Hσ Hcells Hc] with ⟨Hσ, Hcells, -⟩
      · iframe
      imodintro; iframe
  have hdone : ∀ e : w64, ∀ st1 : OsState, st1 = { st with maps := GMap.delete base st.maps } →
      HeapRendered st st1 h h' → MapsFresh st st1 h →
      (gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γb Γb ∗
        gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γm Γm ∗
        gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γf Γf ∗
        gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γt Γt ∗ tokRes (gooseOsGS (L := L)) st Γt ∗
        cellsRes (cellView st) ∗ naHeapCtx tls h ∗
        gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γm p (DFrac.own 1) (some m) ∗
        cellsR base 0 n vf ∗
        (gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γm p (DFrac.own 1)
          (some { m with maps := GMap.delete base m.maps }) -∗ Φ (#e)) ⊢
      |==> ∃ Γb' Γm' Γf' Γt', osWorld (L := L) st1 Γb' Γm' Γf' Γt' h' ∗
        WP (Val (#e)) @ s; E {{ Φ }}) := by
    intro e st1 hst1 Hr Hfr
    obtain ⟨hwf1, hcoh1, hheap⟩ := hunmap st1 hst1
    iintro ⟨HAb, HAm, HAf, HAt, Htok, Hcells, Hσ, Hm, Hc, HΦe⟩
    imod gAuth_update _ _ _ _ _ (some { m with maps := GMap.delete base m.maps }) $$ HAm Hm
      with ⟨HAm, Hm⟩
    imod hheap Hr Hfr $$ [Hσ Hcells Hc] with ⟨Hσ, Hcells⟩
    · iframe
    imodintro
    iexists Γb, _, Γf, Γt
    unfold osWorld
    have htr : tokRes gooseOsGS st1 Γt = tokRes (gooseOsGS (L := L)) st Γt := by rw [hst1]; rfl
    rw [htr]
    iframe
    isplitr
    · ipureintro; exact ⟨hwf1, hcoh1⟩
    iapply wp_value'
    iapply HΦe $$ Hm
  unfold osWorld at hdone
  rcases hres with ⟨hst1, rfl⟩ | ⟨e, he, rfl, hst1 | hst1⟩
  · iapply hdone 0 st' hst1 Hr Hfr
    iframe
    iintro Hm; iapply HΦ; ileft; iframe; ipureintro; rfl
  · subst hst1
    imod cells_same hwf hwf Hr Hfr rfl rfl $$ [Hσ Hcells] with ⟨Hσ, Hcells⟩
    · iframe
    imodintro
    iexists Γb, Γm, Γf, Γt
    iframe
    isplitr
    · ipureintro; exact ⟨hwf, hcoh⟩
    iapply wp_value'
    iapply HΦ
    iright; iframe; isplitr
    · ipureintro; exact he
    iright; iframe
  · iapply hdone e st' hst1 Hr Hfr
    iframe
    iintro Hm; iapply HΦ; iright
    isplitr [Hm]
    · ipureintro; exact he
    ileft; iframe

/-- The `OsMeta` of a file just created. -/
def newMeta : OsMeta := ⟨0, 0, 0, false, true, ∅⟩

/-- A file just created. -/
def newFile : OsFile := { OsFile.ofDisk [] with named := false }

/-- What the ghost state knows of the file at `p` after an open without `O_TRUNC`: it is created
if `creat` and absent. -/
def openMeta : Option OsMeta → Bool → Option OsMeta
  | some m, _ => some m
  | none, true => some newMeta
  | none, false => none

section create
variable {st : OsState} {p : GoString}

theorem sizes_create (hn : st.file p = none) : ∀ q, (st.setFile p newFile).size q = st.size q := by
  intro q; rw [size_setFile]; split
  · subst_vars; simp [OsState.size, hn, newFile, OsFile.ofDisk]
  · rfl

theorem osWf_create (hwf : OsWf st) (hn : st.file p = none) : OsWf (st.setFile p newFile) := by
  have hs := sizes_create hn
  have hex : ∀ q f0, st.file q = some f0 → ∃ f1, (st.setFile p newFile).file q = some f1 := by
    intro q f0 h0; rw [file_setFile]; split
    · exact ⟨_, rfl⟩
    · exact ⟨_, h0⟩
  refine ⟨fun fd d h => ?_, fun b m h => ?_, hwf.maps_disj, fun t c h => ?_, ?_, ?_, ?_⟩
  · obtain ⟨f0, h0⟩ := hwf.fds fd d h; exact hex _ _ h0
  · obtain ⟨⟨f0, h0⟩, h1, h2, h3⟩ := hwf.maps b m h; exact ⟨hex _ _ h0, h1, h2, h3⟩
  · obtain ⟨f0, h0⟩ := hwf.infl t c h; exact hex _ _ h0
  · intro t1 c1 t2 c2 i h1 h2 hne hp
    simp only [affects_congr hs]
    exact hwf.infl_disj t1 c1 t2 c2 i h1 h2 hne hp
  · intro q f1 h1
    rw [file_setFile] at h1; split at h1
    · cases h1; simp [newFile, OsFile.ofDisk]
    · exact hwf.sizes q f1 h1
  · intro q f1 i h1
    rw [file_setFile] at h1; split at h1
    · cases h1; intro _ _ hi; simp [newFile, OsFile.ofDisk] at hi
    · exact hwf.coherent q f1 i h1

theorem cellView_create (hwf : OsWf st) (hn : st.file p = none) :
    cellView (st.setFile p newFile) = cellView st := by
  have hI := inflightAt_congr (sizes_create hn) (st' := st.setFile p newFile) rfl
  refine cellView_congr' hwf (osWf_create hwf hn) rfl (fun q i => ?_) hI
  by_cases hpq : p = q
  · subst hpq; unfold cellByte; rw [file_setFile_eq, hn]; simp [newFile, OsFile.ofDisk]
  · unfold cellByte; rw [file_setFile_ne _ _ hpq, hI]

theorem osCoh_create {Γb Γm Γf Γt} (hwf : OsWf st) (hcoh : OsCoh st Γb Γm Γf Γt)
    (hn : st.file p = none)
    (hp : st.files !! p = some none) :
    OsCoh (st.setFile p newFile) Γb (<[p := some newMeta]> Γm) Γf Γt := by
  have hs := sizes_create hn
  have hI := inflightAt_congr (sizes_create hn) (st' := st.setFile p newFile) rfl
  have hnt : ∀ t c, st.inflight !! t = some c → c.path ≠ p := by
    intro t c ht hcp
    obtain ⟨ti, hti, rfl⟩ := coh_tok hcoh ht
    obtain ⟨f, hf, -⟩ := hcoh.tok_saved t ti hti
    rw [hcp, hn] at hf; cases hf
  refine ⟨fun q => ?_, fun q => ?_, fun q m hm => ?_, fun q i x hx => ?_, fun q f1 i h1 hi => ?_,
    hcoh.fds, hcoh.toks, fun t ti h => ?_, hcoh.tok_alone, fun t ti h => ?_⟩
  · rw [files_setFile, GMap.lookup_insert_eq_iff]; split
    · simp
    · exact hcoh.meta_dom q
  · rw [files_setFile, GMap.lookup_insert_eq_iff]; split
    · simp
    · exact hcoh.meta_none q
  · rw [GMap.lookup_insert_eq_iff] at hm
    split at hm
    · subst_vars; cases hm
      refine ⟨newFile, by rw [files_setFile, if_pos rfl], ⟨rfl, rfl, Nat.le_refl _, Nat.le_refl _,
        fun _ _ => rfl, fun b len => ?_, fun t c ht hc => absurd hc (hnt t c ht)⟩⟩
      simp only [newMeta, GMap.lookup_empty, reduceCtorEq, false_iff]
      intro hb
      obtain ⟨⟨f0, hf0⟩, -⟩ := hwf.maps b _ hb
      simp only at hf0; rw [hn] at hf0; cases hf0
    · rename_i hpq
      obtain ⟨f1, h1, hm1⟩ := hcoh.meta_some q m hm
      exact ⟨f1, by rw [files_setFile, if_neg hpq]; exact h1, hm1.transfer hs rfl rfl⟩
  · obtain ⟨f1, h1, hb, hc⟩ := hcoh.bytes q i x hx
    have hpq : p ≠ q := fun e => by subst e; rw [hn] at h1; cases h1
    refine ⟨f1, by rw [file_setFile_ne _ _ hpq]; exact h1, hb, fun hx2 => ?_⟩
    obtain ⟨hc1, hc2⟩ := hc hx2
    exact ⟨hc1, by rw [hI]; exact hc2⟩
  · rw [file_setFile] at h1; split at h1
    · cases h1; simp [newFile, OsFile.ofDisk] at hi
    · exact hcoh.bytes_full q f1 i h1 hi
  · rw [reaches_congr hs]; exact hcoh.tok_q t ti h
  · obtain ⟨f1, h1, hsv⟩ := hcoh.tok_saved t ti h
    rw [affRange_congr hs, file_setFile]; split
    · subst_vars; rw [hn] at h1; cases h1
    · exact ⟨f1, h1, hsv⟩

end create


theorem osWf_addFd {st : OsState} (hwf : OsWf st) (fd : w64) (d : OsFd)
    (hd : ∃ f, st.file d.path = some f) : OsWf { st with fds := <[fd := d]> st.fds } :=
  osWf_fds hwf _ (fun fd' d' h => by
    rw [GMap.lookup_insert_eq_iff] at h; split at h
    · cases h; exact hd
    · exact hwf.fds fd' d' h)

/-- `open(p, fl)` without `O_TRUNC`, with the file's `OsMeta` (whole if there is no file, so
that the open may create it): on success a new fd, whole; on failure, `-1`, and the file may
have been created. -/
theorem wp_Open (p : GoString) (fl : w64) (q : DFrac) (mo : Option OsMeta) (hE : ↑osN ⊆ E)
    (hfl : OpenFlagsOk fl.toNat) (htr : fl.toNat / O_TRUNC % 2 = 0)
    (hq : mo = none → q = DFrac.own 1) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osMeta (L := L) p q mo -∗
      (∀ fd : w64, ∀ e : w64, ∀ mo' : Option OsMeta,
        ⌜(e = 0 ∧ 0 ≤ fd.toInt ∧ mo' = openMeta mo (decide (fl.toNat / O_CREAT % 2 = 1)) ∧
            mo' ≠ none) ∨
          (e ≠ 0 ∧ fd = -1 ∧ (mo' = mo ∨ mo' = openMeta mo (decide (fl.toNat / O_CREAT % 2 = 1))))⌝ -∗
        osMeta (L := L) p q mo' -∗
        (if e = 0 then osFd (L := L) fd (DFrac.own 1) (openFd p fl) else emp) -∗
        Φ (PairV (#fd) (#e))) -∗
      WP (ExternalOp osFsExt.name "Open" (Val (PairV (#p) (#fl)))) @ s; E {{ Φ }} := by
  iintro #Hinv Hm HΦ
  iapply wp_os_step "Open" _ Φ (by simp [val.isPanic]) hE $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %h Hw
  unfold osWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  obtain ⟨hwf, hcoh⟩ := Hwc
  unfold osMeta
  icases gAuth_lookup _ _ _ _ _ _ $$ HAm Hm with %Hml
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have hpn : st.files !! p ≠ none := fun h0 => by rw [(hcoh.meta_dom p).2 h0] at Hml; cases Hml
  have hpf : p ∈ st.files := by
    have := hpn
    show (st.files.lookup p).isSome
    cases h' : st.files.lookup p
    · exact absurd h' this
    · rfl
  imodintro
  isplitr
  · ipureintro
    exact ⟨_, h, st, ⟨p, fl, rfl, hpf, hfl, .inr ⟨1, by decide, rfl, .inl rfl⟩⟩,
      mapsFresh_same rfl, heapRendered_same hwf rfl rfl Hag⟩
  inext
  iintro %e' %h' %st' %Hst
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsOsStep] at Hst
  obtain ⟨p', fl', hv, -, -, hres⟩ := Hst
  injection hv with h1 h2
  cases go.intoVal_inj h1; cases go.intoVal_inj h2
  have htr' : ¬ (fl.toNat / O_TRUNC % 2 = 1) := by omega
  -- the state after the open's effect, and its ghost maps
  have heffect : ∀ st1, openEffect st p (decide (fl.toNat / O_CREAT % 2 = 1))
      (decide (fl.toNat / O_TRUNC % 2 = 1)) = some st1 →
      (st1 = st ∧ openMeta mo (decide (fl.toNat / O_CREAT % 2 = 1)) = mo ∧
        ∃ f, st.file p = some f) ∨
      (st1 = st.setFile p newFile ∧ mo = none ∧ st.file p = none ∧
        st.files !! p = some none ∧
        openMeta mo (decide (fl.toNat / O_CREAT % 2 = 1)) = some newMeta) := by
    intro st1 he
    unfold openEffect at he
    cases hfp : st.file p with
    | some f =>
      rw [hfp] at he; simp only [htr', decide_false, Bool.false_eq_true, ↓reduceIte,
        Option.some.injEq] at he
      subst he; left; refine ⟨rfl, ?_, f, rfl⟩
      cases mo with
      | some m => rfl
      | none =>
        have := (hcoh.meta_none p).1 Hml
        rw [file_eq_some.1 hfp] at this; cases this
    | none =>
      rw [hfp] at he
      by_cases hc : fl.toNat / O_CREAT % 2 = 1
      · simp only [hc, _root_.decide_true, ↓reduceIte, Option.some.injEq] at he
        subst he
        have hnone : st.files !! p = some none := by
          cases hfo : st.files !! p with
          | none => exact absurd hfo hpn
          | some fo => cases fo with
            | none => rfl
            | some f => rw [file_eq_some.2 hfo] at hfp; cases hfp
        have hmo : mo = none := by
          have := (hcoh.meta_none p).2 hnone; rw [Hml] at this; cases this; rfl
        right; refine ⟨rfl, hmo, rfl, hnone, by rw [hmo, hc]; rfl⟩
      · simp [hc] at he
  have hghost : ∀ st1, openEffect st p (decide (fl.toNat / O_CREAT % 2 = 1))
      (decide (fl.toNat / O_TRUNC % 2 = 1)) = some st1 →
      gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γm Γm ∗
        gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γm p q mo ⊢ |==>
      ∃ Γm', ⌜OsWf st1 ∧ OsCoh st1 Γb Γm' Γf Γt ∧ cellView st1 = cellView st ∧
          st1.inflight = st.inflight ∧ st1.maps = st.maps ∧ st1.fds = st.fds ∧
          (∀ p0 f0, st.file p0 = some f0 → ∃ f1, st1.file p0 = some f1) ∧
          (∃ f1, st1.file p = some f1)⌝ ∗
        gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γm Γm' ∗
        gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γm p q
          (openMeta mo (decide (fl.toNat / O_CREAT % 2 = 1))) ∗
        ⌜tokRes (gooseOsGS (L := L)) st1 Γt = tokRes (gooseOsGS (L := L)) st Γt⌝ := by
    intro st1 he
    iintro ⟨HAm, Hm⟩
    rcases heffect st1 he with ⟨rfl, hom, f, hf⟩ | ⟨rfl, hmo, hn, hnone, hom⟩
    · rw [hom]
      imodintro
      iexists Γm
      iframe
      ipureintro
      exact ⟨⟨hwf, hcoh, rfl, rfl, rfl, rfl, fun p0 f0 h0 => ⟨f0, h0⟩, ⟨f, hf⟩⟩, rfl⟩
    · subst hmo
      rw [hq rfl, hom]
      imod gAuth_update _ _ _ _ _ (some newMeta) $$ HAm Hm with ⟨HAm, Hm⟩
      imodintro
      iexists _
      iframe
      ipureintro
      refine ⟨⟨osWf_create hwf hn, osCoh_create hwf hcoh hn hnone, cellView_create hwf hn, rfl, rfl,
        rfl, fun p0 f0 h0 => ?_, ⟨newFile, file_setFile_eq _ _ _⟩⟩, ?_⟩
      · by_cases hpp : p = p0
        · subst hpp; rw [hn] at h0; cases h0
        · exact ⟨f0, by rw [file_setFile_ne _ _ hpp]; exact h0⟩
      · unfold tokRes; simp only [affLo_congr (sizes_create hn)]
  have hne : ∀ st1, openEffect st p (decide (fl.toNat / O_CREAT % 2 = 1))
      (decide (fl.toNat / O_TRUNC % 2 = 1)) = some st1 →
      openMeta mo (decide (fl.toNat / O_CREAT % 2 = 1)) ≠ none := by
    intro st1 he
    rcases heffect st1 he with ⟨-, hom, f, hf⟩ | ⟨-, -, -, -, hom⟩
    · rw [hom]; intro hmo; subst hmo
      have := (hcoh.meta_none p).1 Hml; rw [file_eq_some.1 hf] at this; cases this
    · rw [hom]; simp
  rcases hres with ⟨st1, fd, heff, hfd0, hfdn, hst, rfl⟩ | ⟨e, he, rfl, hst⟩
  · have hst' : st' = { st1 with fds := <[fd := openFd p fl]> st1.fds } := hst
    subst hst'
    imod hghost st1 heff $$ [HAm Hm] with ⟨%Γm', %Hgh, HAm, Hm, %htr1⟩
    · iframe
    obtain ⟨hwf1, hcoh1, hcv, hin1, hmp1, hfds1, -, hex1⟩ := Hgh
    have hΓf : Γf !! fd = none := by rw [hcoh.fds]; exact hfdn
    imod gAuth_insert _ _ _ fd (openFd p fl) hΓf $$ HAf with ⟨HAf, Hfd⟩
    have hwf' := osWf_addFd hwf1 fd (openFd p fl) hex1
    have hcv' : cellView { st1 with fds := <[fd := openFd p fl]> st1.fds } = cellView st := by
      exact (cellView_congr (st := st1) rfl rfl rfl).trans hcv
    imod cells_same hwf hwf' Hr Hfr (by simp [hmp1]) hcv' $$ [Hσ Hcells] with ⟨Hσ, Hcells⟩
    · iframe
    imodintro
    iexists Γb, Γm', (<[fd := openFd p fl]> Γf), Γt
    have htr' : tokRes gooseOsGS { st1 with fds := <[fd := openFd p fl]> st1.fds } Γt =
        tokRes (gooseOsGS (L := L)) st Γt := by rw [← htr1]; rfl
    rw [htr']
    iframe
    isplitr
    · ipureintro
      refine ⟨hwf', ?_⟩
      have : Γf = st1.fds := by rw [hcoh.fds, hfds1]
      rw [this]; exact osCoh_fds hcoh1 _
    iapply wp_value'
    iapply HΦ $$ %fd %0 %_ %(.inl ⟨rfl, hfd0, rfl, hne st1 heff⟩) Hm
    rw [if_pos rfl]; unfold osFd; iexact Hfd
  · rcases hst with rfl | heff
    · imod cells_same hwf hwf Hr Hfr rfl rfl $$ [Hσ Hcells] with ⟨Hσ, Hcells⟩
      · iframe
      imodintro
      iexists Γb, Γm, Γf, Γt
      iframe
      isplitr
      · ipureintro; exact ⟨hwf, hcoh⟩
      iapply wp_value'
      iapply HΦ $$ %_ %e %mo %(.inr ⟨he, rfl, .inl rfl⟩) Hm
      rw [if_neg he]; iempintro
    · imod hghost st' heff $$ [HAm Hm] with ⟨%Γm', %Hgh, HAm, Hm, %htr1⟩
      · iframe
      obtain ⟨hwf1, hcoh1, hcv, hin1, hmp1, hfds1, -, -⟩ := Hgh
      imod cells_same hwf hwf1 Hr Hfr hmp1 hcv $$ [Hσ Hcells] with ⟨Hσ, Hcells⟩
      · iframe
      imodintro
      iexists Γb, Γm', Γf, Γt
      rw [htr1]
      iframe
      isplitr
      · ipureintro; exact ⟨hwf1, hcoh1⟩
      iapply wp_value'
      iapply HΦ $$ %_ %e %_ %(.inr ⟨he, rfl, .inr rfl⟩) Hm
      rw [if_neg he]; iempintro


/-- A mapped cell the client holds part of shows the byte it maps, while the client holds a
fraction of that byte: a load through the mapping reads the page cache. -/
theorem osCell_agree (e : Expr) (htv : toVal e = none) (p : GoString) (dqm : DFrac) (m : OsMeta)
    (base : Loc) (len i : Nat) (hb : m.maps !! base = some len) (hi : i < len) (dqb : DFrac)
    (x : w8 × Bool) (dqc : DFrac) (v : val) (hE : ↑osN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osMeta (L := L) p dqm (some m) -∗ osByte (L := L) p i dqb x -∗
      heapPointsto (base +ₗ (i : Int)) dqc v -∗
      (⌜v = LitV (LitByte x.1)⌝ -∗ osMeta (L := L) p dqm (some m) -∗ osByte (L := L) p i dqb x -∗
        heapPointsto (base +ₗ (i : Int)) dqc v -∗ WP e @ s; E {{ Φ }}) -∗
      WP e @ s; E {{ Φ }} := by
  iintro #Hinv Hm Hb Hc HΦ
  iapply wp_ext_acc (X := osFsExt) e Φ htv
  iintro %σ %g Hl Hg
  icases (os_local_ctx_eq σ).mp $$ Hl with Hl
  unfold osCtx
  icases Hl with ⟨%Γb, %Γm, %Γf, %Γt, %Hwc, HAb, HAm, HAf, HAt, Htok, Hv⟩
  obtain ⟨hwf, hcoh⟩ := Hwc
  unfold osInv
  imod inv_acc hE $$ Hinv with ⟨Hi, Hclose⟩
  icases Hi with >Hi
  icases Hi with ⟨%cv, %n, Hv', Hcells⟩
  icases gVar_agree _ _ _ _ _ $$ Hv Hv' with %Heq
  simp only [Prod.mk.injEq] at Heq
  obtain ⟨rfl, rfl⟩ := Heq
  unfold osMeta osByte
  icases gAuth_lookup _ _ _ _ _ _ $$ HAm Hm with %Hml
  icases gAuth_lookup _ _ _ _ _ _ $$ HAb Hb with %Hbl
  icases tokRes_byte_free _ hcoh Hbl $$ Htok Hb with %Hn
  obtain ⟨f, hf, hmo⟩ := coh_meta hcoh Hml
  have hmt : MapsTo σ (base +ₗ (i : Int)) p i := ⟨base, ⟨p, len⟩, (hmo.maps base len).1 hb, rfl, hi, rfl⟩
  have hcv := cellView_mapsTo hwf hmt
  rw [cellByte_noinfl hf Hn] at hcv
  obtain ⟨f1, hf1, hbx, -⟩ := hcoh.bytes p i x Hbl
  rw [hf] at hf1; cases hf1
  rw [hbx] at hcv
  unfold cellsRes
  icases BigSepM.bigSepM_lookup_acc (Φ := fun l (x : Option w8 × Bool) =>
    heapPointsto l (cellFrac x.2) (toCellVal x.1)) hcv $$ Hcells with ⟨Hl, Hcl⟩
  icombine Hl Hc gives %Hvv
  ihave Hcells := Hcl $$ Hl
  imod Hclose $$ [Hv' Hcells] with -
  · inext; iexists (cellView σ), (GMap.size σ.inflight); iframe
  imodintro
  isplitl [HAb HAm HAf HAt Htok Hv]
  · iapply (os_local_ctx_eq σ).mpr
    unfold osCtx
    iexists Γb, Γm, Γf, Γt
    iframe
    ipureintro; exact ⟨hwf, hcoh⟩
  iframe Hg
  iapply HΦ $$ %Hvv.2.symm Hm Hb Hc

end specs

end Perennial

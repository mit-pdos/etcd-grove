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
    icases BigSepM.bigSepM_lookup (Φ := fun (_t : w64) (ti : TokInfo) =>
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
            bytesG hL ti.c.path (affLo st ti.c) (DFrac.own 1) (ti.saved.map (·, false))))
          hti $$ Htok with ⟨Hs, -⟩
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
  unfold osBytes osByte
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
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hth, Hσ⟩
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
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hth, Hσ⟩
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
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hth, Hσ⟩
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
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hth, Hσ⟩
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

end specs

end Perennial

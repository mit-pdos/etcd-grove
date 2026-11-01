/-
The ghost state of the Linux file extension (`GooseLang/Ext/OsFs/Impl.lean`): its values, the
pure relations between it and the extension's state, and the extension's ghost state for the
adequacy theorem (`ExtInterp`). The specs are in `Specs.lean`.

The design (`Specs.lean`'s header says it from a client's side):

* Five ghost maps, all in the one `AllG GF` (Perennial's `ghostMap`, values stored by their
  `Pos.Countable` encodings): the bytes of the page cache, `(p, i) ↦ (b, clean)` for every
  byte `i < size` of an existing file `p`; the files, `p ↦ some m` (an `OsMeta`: the size, the
  crash bounds of the size, whether the name is durable, whether no byte of the file is lost,
  the file's mappings) or `p ↦ none` (an allowed path with no file); the fds; the in-flight
  changes (`TokInfo`: the change, the fraction of the file's `OsMeta` its first step took, the
  bytes it took, as they were, and the `OsMeta` it took).
* The relations (`OsWf`, on the state alone, and `OsCoh`, between the state and the maps) say
  that the maps mirror the state, that a byte marked clean is clean on disk, and that a file
  whose `OsMeta` says `ok` has no lost byte.
* The heap: every mapped cell is half the extension's (all of it while an in-flight change may
  change it), and the other half the client's. The extension's halves cannot live in its own
  ghost state, which cannot name the heap (`ExtInterp.localCtx` sees the extension's ghost names
  only), so they live in an invariant of each generation (`osInv`, `Specs.lean`), tied to the
  state by a ghost variable holding the cells' view (`cellView`), half of it here and half there.
  The thread tokens that bound the in-flight changes live there too.
-/
module

public import Perennial.GooseLang.Lifting
public import Perennial.GooseLang.Countable
public import Perennial.Ghost.GhostMap
public import Perennial.Ghost.GhostVar
public import GooseLang.Ext.OsFs.Impl

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

/-! ## Ghost values -/

/-- What the ghost state knows of an existing file. -/
structure OsMeta where
  /-- The size of the page cache. -/
  size : Nat
  /-- Bounds of the size a crash may leave the file with. -/
  lo : Nat
  hi : Nat
  /-- The directory entry is durable (a crash keeps the file). -/
  named : Bool
  /-- No byte of the file is lost by a failed sync. -/
  ok : Bool
  /-- The mappings of the file: base address to length. -/
  maps : GMap Loc Nat

/-- An in-flight change, as the ghost state records it. -/
structure TokInfo where
  c : OsChange
  /-- The fraction of the file's `OsMeta` the first step took. -/
  q : Qp
  /-- The file's bytes the change took (`affRange`), as they were. -/
  saved : List w8
  /-- The file's `OsMeta`, as the first step left it. -/
  om : OsMeta

instance OsMeta.countable : Pos.Countable OsMeta :=
  Pos.Countable.ofInjective
    (fun m => Pos.Countable.encode (m.size, m.lo, m.hi, m.named, m.ok, m.maps))
    (fun a b h => by
      have h := Pos.encode_inj h
      cases a; cases b; simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h; subst h1 h2 h3 h4 h5 h6; rfl)

instance Qp.countable : Pos.Countable Qp :=
  Pos.Countable.ofInjective (fun q => Pos.Countable.encode (q.val.num, q.val.den))
    (fun a b h => by
      have h := Pos.encode_inj h
      simp only [Prod.mk.injEq] at h
      exact Subtype.ext (Rat.ext h.1 h.2))

instance OsFd.countable : Pos.Countable OsFd :=
  Pos.Countable.ofInjective (fun d => Pos.Countable.encode (d.path, d.readable, d.writable))
    (fun a b h => by
      have h := Pos.encode_inj h
      cases a; cases b; simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3⟩ := h; subst h1 h2 h3; rfl)

def OsChangeKind.enc : OsChangeKind → (Nat × List w8) ⊕ Nat
  | .write off data => .inl (off, data)
  | .truncate sz => .inr sz

instance OsChange.countable : Pos.Countable OsChange :=
  Pos.Countable.ofInjective (fun c => Pos.Countable.encode (c.path, c.kind.enc))
    (fun a b h => by
      have h := Pos.encode_inj h
      obtain ⟨pa, ka⟩ := a; obtain ⟨pb, kb⟩ := b
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h; subst h1
      cases ka <;> cases kb <;> simp_all [OsChangeKind.enc])

instance TokInfo.countable : Pos.Countable TokInfo :=
  Pos.Countable.ofInjective (fun t => Pos.Countable.encode (t.c, t.q, t.saved, t.om))
    (fun a b h => by
      have h := Pos.encode_inj h
      cases a; cases b; simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3, h4⟩ := h; subst h1 h2 h3 h4; rfl)

/-! ## Derived facts about a state -/

section derived
variable (st : OsState)

/-- Byte `i` of `f` is clean: the disk holds it (not dirty, not lost, inside the durable
image, which has the page cache's byte), and it has been part of the file since the last
successful sync (so that a crash keeps it). -/
def CleanPhys (f : OsFile) (i : Nat) : Prop :=
  f.dirty i = false ∧ f.lost i = false ∧ i < f.sizeLo ∧ f.durable[i]? = f.cur[i]?

/-- The first byte the change `c` takes: a write, where its affected range starts; a truncate,
where the old and new sizes part. -/
def affLo (c : OsChange) : Nat :=
  match c.kind with
  | .write off _ => min off (st.size c.path)
  | .truncate sz => min (st.size c.path) sz

/-- The end of the bytes the change `c` takes: its affected range, cut at the size. -/
def affHi (c : OsChange) : Nat :=
  match c.kind with
  | .write off data => min (off + data.length) (st.size c.path)
  | .truncate _ => st.size c.path

/-- The file's bytes the change `c` takes: its affected bytes below the size. -/
def affRange (c : OsChange) : List Nat := List.range' (affLo st c) (affHi st c - affLo st c)

/-- The change `c` may change the size, or bytes past it: a write that ends past the size, or a
truncate. Its first step takes the file's `OsMeta` whole. -/
def Reaches (c : OsChange) : Prop :=
  match c.kind with
  | .write off data => st.size c.path < off + data.length
  | .truncate _ => True

/-- The state is well formed: what the operations maintain of it, independently of the ghost
state. -/
structure OsWf : Prop where
  fds : ∀ fd d, st.fds !! fd = some d → ∃ f, st.file d.path = some f
  maps : ∀ b m, st.maps !! b = some m →
    (∃ f, st.file m.path = some f) ∧ 0 < b.addr ∧ b.addr + m.len ≤ maxAddr
  maps_disj : ∀ b1 m1 b2 m2, st.maps !! b1 = some m1 → st.maps !! b2 = some m2 → b1 ≠ b2 →
    b1.addr + m1.len ≤ b2.addr ∨ b2.addr + m2.len ≤ b1.addr
  infl : ∀ t c, st.inflight !! t = some c → ∃ f, st.file c.path = some f
  infl_disj : ∀ t1 c1 t2 c2 i, st.inflight !! t1 = some c1 → st.inflight !! t2 = some c2 →
    t1 ≠ t2 → c1.path = c2.path → Affects st c1 i → ¬ Affects st c2 i
  sizes : ∀ p f, st.file p = some f → f.sizeLo ≤ f.cur.length ∧ f.cur.length ≤ f.sizeHi

/-- What the ghost `OsMeta` `m` of the file `f` at `p` says of it. -/
structure MetaOk (p : GoString) (m : OsMeta) (f : OsFile) : Prop where
  size : m.size = f.cur.length
  named : m.named = f.named
  lo : m.lo ≤ f.sizeLo
  hi : f.sizeHi ≤ m.hi
  ok : m.ok = true → ∀ i, f.lost i = false
  maps : ∀ b len, m.maps !! b = some len ↔ st.maps !! b = some ⟨p, len⟩
  targets : ∀ t c, st.inflight !! t = some c → c.path = p → m.lo ≤ c.target st ∧ c.target st ≤ m.hi

/-- The ghost maps mirror the state. -/
structure OsCoh (Γb : GMap (GoString × Nat) (w8 × Bool)) (Γm : GMap GoString (Option OsMeta))
    (Γf : GMap w64 OsFd) (Γt : GMap w64 TokInfo) : Prop where
  meta_dom : ∀ p, Γm !! p = none ↔ st.files !! p = none
  meta_none : ∀ p, Γm !! p = some none ↔ st.files !! p = some none
  meta_some : ∀ p m, Γm !! p = some (some m) →
    ∃ f, st.files !! p = some (some f) ∧ MetaOk st p m f
  bytes : ∀ p i x, Γb !! (p, i) = some x → ∃ f, st.file p = some f ∧ f.cur[i]? = some x.1 ∧
    (x.2 = true → CleanPhys f i ∧ ¬ InflightAt st p i)
  bytes_full : ∀ p f i, st.file p = some f → i < f.cur.length → (Γb !! (p, i)).isSome
  fds : Γf = st.fds
  toks : ∀ t, (Γt !! t).map TokInfo.c = st.inflight !! t
  tok_q : ∀ t ti, Γt !! t = some ti → Reaches st ti.c → ti.q = 1
  tok_alone : ∀ t ti, Γt !! t = some ti → ti.q = 1 →
    ∀ t' c', t' ≠ t → st.inflight !! t' = some c' → c'.path ≠ ti.c.path
  tok_saved : ∀ t ti, Γt !! t = some ti → ∃ f, st.file ti.c.path = some f ∧
    ti.saved = (affRange st ti.c).map (fun i => f.cur.getD i 0)

end derived

/-! ## The view of the mapped cells -/

section cells
attribute [local instance] Classical.propDecidable

/-- What byte `i` of a mapping of `p` shows: the file's byte, or nothing (a hole). -/
def cellByte (st : OsState) (p : GoString) (i : Nat) : Option w8 :=
  match st.file p with
  | some f => if h : i < f.cur.length then (if InflightAt st p i then none else some f.cur[i])
      else none
  | none => none

/-- The value of a cell showing `ob`. -/
def toCellVal [GooseExts] : Option w8 → val
  | some b => LitV (LitByte b)
  | none => osHole

theorem cellVal_eq [GooseExts] [GoGlobalContext] (st : OsState) (p : GoString) (i : Nat) :
    cellVal st p i = toCellVal (cellByte st p i) := by
  unfold cellVal cellByte
  rcases st.file p with _ | f
  · rfl
  · dsimp only
    by_cases hi : i < f.cur.length
    · simp only [hi, ↓reduceDIte]
      by_cases hn : InflightAt st p i
      · simp only [hn, ↓reduceIte]; rfl
      · simp only [hn, ↓reduceIte]; rfl
    · simp only [hi, ↓reduceDIte]; rfl

/-- The cells of the mappings of `maps`. -/
def mapCells (maps : GMap Loc OsMap) : List Loc :=
  maps.toList.flatMap (fun bm => (List.range bm.2.len).map (fun (i : Nat) => bm.1 +ₗ (i : Int)))

theorem mem_mapCells {maps : GMap Loc OsMap} {l : Loc} :
    l ∈ mapCells maps ↔ ∃ b m i, maps !! b = some m ∧ i < m.len ∧ l = b +ₗ (i : Int) := by
  simp only [mapCells, List.mem_flatMap, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨⟨b, m⟩, hbm, i, hi, rfl⟩
    exact ⟨b, m, i, (GMap.mem_toList _ _ _).1 hbm, hi, rfl⟩
  · rintro ⟨b, m, i, hbm, hi, rfl⟩
    exact ⟨⟨b, m⟩, (GMap.mem_toList _ _ _).2 hbm, i, hi, rfl⟩

/-- What each mapped cell shows, and whether the extension holds all of it (while an in-flight
change may change it). -/
def cellView (st : OsState) : GMap Loc (Option w8 × Bool) :=
  ⟨fun l => if h : Mapped st l then
      some (cellByte st h.choose h.choose_spec.choose,
        decide (InflightAt st h.choose h.choose_spec.choose))
    else none,
   ⟨mapCells st.maps, fun l hl => by
      by_cases h : Mapped st l
      · obtain ⟨p, i, b, m, hm, -, hi, rfl⟩ := h
        exact mem_mapCells.2 ⟨b, m, i, hm, hi, rfl⟩
      · simp [h] at hl⟩⟩

theorem mapsTo_unique {st : OsState} (hwf : OsWf st) {l : Loc} {p p' : GoString} {i i' : Nat}
    (h : MapsTo st l p i) (h' : MapsTo st l p' i') : p = p' ∧ i = i' := by
  obtain ⟨b, m, hm, rfl, hi, rfl⟩ := h
  obtain ⟨b', m', hm', rfl, hi', he⟩ := h'
  by_cases hb : b = b'
  · subst hb; rw [hm] at hm'; cases hm'
    have := loc_add_inj _ he; exact ⟨rfl, by omega⟩
  · exfalso
    have hd := hwf.maps_disj b m b' m' hm hm' hb
    have : b.addr + i = b'.addr + i' := by simpa [Loc.add] using congrArg Loc.addr he
    omega

theorem cellView_mapsTo {st : OsState} (hwf : OsWf st) {l : Loc} {p : GoString} {i : Nat}
    (h : MapsTo st l p i) :
    cellView st !! l = some (cellByte st p i, decide (InflightAt st p i)) := by
  have hm : Mapped st l := ⟨p, i, h⟩
  show (if h : Mapped st l then _ else _) = _
  rw [dite_eq_left_of_eq_true (eq_true hm)]
  obtain ⟨rfl, rfl⟩ := mapsTo_unique hwf hm.choose_spec.choose_spec h
  rfl

theorem cellView_none {st : OsState} {l : Loc} (h : ¬ Mapped st l) : cellView st !! l = none := by
  show (if h : Mapped st l then _ else _) = _
  rw [dite_eq_right_of_eq_false (eq_false h)]

theorem cellView_some {st : OsState} (hwf : OsWf st) {l : Loc} {x : Option w8 × Bool}
    (h : cellView st !! l = some x) :
    ∃ p i, MapsTo st l p i ∧ x = (cellByte st p i, decide (InflightAt st p i)) := by
  by_cases hm : Mapped st l
  · obtain ⟨p, i, hpi⟩ := hm
    rw [cellView_mapsTo hwf hpi] at h; cases h; exact ⟨p, i, hpi, rfl⟩
  · rw [cellView_none hm] at h; cases h

theorem cellView_of_maps_empty {st : OsState} (h : st.maps = ∅) : cellView st = ∅ := by
  apply GMap.ext; intro l
  rw [cellView_none]
  · rfl
  · rintro ⟨p, i, b, m, hm, -⟩; simp [h] at hm

end cells

/-! ## The ghost state -/

/-- What the adequacy theorem provides. -/
class OsGpreS (GF : BundledGFunctors) where
  osPreAllG : AllG GF

/-- The ghost names of the extension: the four maps (bytes, files, fds, in-flight changes) and
the variable that ties the mapped cells' view to the invariant. -/
structure OsGS (GF : BundledGFunctors) where
  osAllG : AllG GF
  γb : GName
  γm : GName
  γf : GName
  γt : GName
  γv : GName

/-- The ghost `OsMeta` of a file as on disk. -/
def initMeta (f : OsFile) : OsMeta :=
  ⟨f.cur.length, f.cur.length, f.cur.length, true, true, ∅⟩

/-- The bytes of the files of `st`, all clean. -/
def bytesMap (st : OsState) : GMap (GoString × Nat) (w8 × Bool) :=
  ⟨fun k => (st.file k.1).bind (fun f => f.cur[k.2]?.map (·, true)),
   ⟨st.files.toList.flatMap (fun pf => match pf.2 with
      | some f => (List.range f.cur.length).map (fun i => (pf.1, i))
      | none => []), fun ⟨p, i⟩ h => by
      simp only [List.mem_flatMap]
      cases hf : st.file p with
      | none => simp [hf] at h
      | some f =>
        simp only [hf, Option.bind_some, Option.isSome_map] at h
        refine ⟨⟨p, some f⟩, (GMap.mem_toList _ _ _).2 ?_, ?_⟩
        · simp only [OsState.file, Option.bind_eq_some_iff] at hf
          obtain ⟨fo, hfo, rfl⟩ := hf; simpa using hfo
        · simp only [List.mem_map, List.mem_range, Prod.mk.injEq]
          exact ⟨i, by simpa using h, by simp⟩⟩⟩

/-- The files of `st`, as on disk. -/
def metaMap (st : OsState) : GMap GoString (Option OsMeta) :=
  GMap.fmap (Option.map initMeta) st.files

section ghost
variable {GF : BundledGFunctors}

/-- The interpretation of the state `st`. -/
def osCtx (hL : OsGS GF) (st : OsState) : IProp GF :=
  letI := hL.osAllG
  iprop(∃ (Γb : GMap (GoString × Nat) (w8 × Bool)) (Γm : GMap GoString (Option OsMeta))
      (Γf : GMap w64 OsFd) (Γt : GMap w64 TokInfo),
    ⌜OsWf st ∧ OsCoh st Γb Γm Γf Γt⌝ ∗
    ghostMapAuth hL.γb 1 Γb ∗ ghostMapAuth hL.γm 1 Γm ∗ ghostMapAuth hL.γf 1 Γf ∗
    ghostMapAuth hL.γt 1 Γt ∗
    ([∗map] _t ↦ ti ∈ Γt,
      ghostMapElem hL.γm ti.c.path (DFrac.own ti.q) (some ti.om) ∗
      [∗list] k ↦ b ∈ ti.saved, ghostMapElem hL.γb (ti.c.path, affLo st ti.c + k) (DFrac.own 1)
        (b, false)) ∗
    ghostVar hL.γv (1 : Qp).half (cellView st, GMap.size st.inflight))

/-- The start resources for a state with no fd, change or mapping: every file and byte, whole,
and the half of the cells' view that the invariant takes (`osInv_alloc`). -/
def osStart (hL : OsGS GF) (st : OsState) : IProp GF :=
  letI := hL.osAllG
  iprop(([∗map] k ↦ x ∈ bytesMap st, ghostMapElem hL.γb k (DFrac.own 1) x) ∗
    ([∗map] p ↦ mo ∈ metaMap st, ghostMapElem hL.γm p (DFrac.own 1) mo) ∗
    ghostVar hL.γv (1 : Qp).half ((∅ : GMap Loc (Option w8 × Bool)), 0))

end ghost

/-- A state the program may start in: no fd, change or mapping, and every file as on disk. -/
def OsInit (st : OsState) : Prop :=
  st.fds = ∅ ∧ st.inflight = ∅ ∧ st.maps = ∅ ∧
    ∀ p f, st.files !! p = some (some f) → f = OsFile.ofDisk f.cur

theorem file_eq_some {st : OsState} {p : GoString} {f : OsFile} :
    st.file p = some f ↔ st.files !! p = some (some f) := by
  simp only [OsState.file, Option.bind_eq_some_iff]
  constructor
  · rintro ⟨fo, h, rfl⟩; exact h
  · intro h; exact ⟨_, h, rfl⟩

theorem osInit_wf_coh {st : OsState} (h : OsInit st) :
    OsWf st ∧ OsCoh st (bytesMap st) (metaMap st) ∅ ∅ := by
  obtain ⟨hfd, hin, hmp, hdisk⟩ := h
  have hdisk' : ∀ p f, st.file p = some f → f = OsFile.ofDisk f.cur :=
    fun p f hf => hdisk p f (file_eq_some.1 hf)
  have hnoinfl : ∀ p i, ¬ InflightAt st p i := by
    rintro p i ⟨t, c, ht, -⟩; simp [hin] at ht
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro fd d h; simp [hfd] at h
  · intro b m h; simp [hmp] at h
  · intro b1 m1 _ _ h; simp [hmp] at h
  · intro t c h; simp [hin] at h
  · intro t1 c1 _ _ _ h; simp [hin] at h
  · intro p f hf
    rw [hdisk' p f hf]; simp [OsFile.ofDisk]
  · intro p; simp [metaMap]
  · intro p; simp [metaMap]
  · intro p m hm
    simp only [metaMap, GMap.lookup_fmap] at hm
    cases hfo : st.files !! p with
    | none => simp [hfo] at hm
    | some fo =>
      cases fo with
      | none => simp [hfo] at hm
      | some f =>
        simp only [hfo, Option.map_some, Option.some.injEq] at hm
        subst hm
        have hf := hdisk p f hfo
        refine ⟨f, rfl, ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
        · rw [hf]; rfl
        · rw [hf]; simp [initMeta, OsFile.ofDisk]
        · rw [hf]; simp [initMeta, OsFile.ofDisk]
        · intro _ i; rw [hf]; rfl
        · intro b len; simp [initMeta, hmp]
        · intro t c ht; simp [hin] at ht
  · intro p i x hx
    simp only [bytesMap, GMap.lookup_mk] at hx
    cases hf : st.file p with
    | none => simp [hf] at hx
    | some f =>
      simp only [hf, Option.bind_some, Option.map_eq_some_iff] at hx
      obtain ⟨b, hb, rfl⟩ := hx
      refine ⟨f, rfl, hb, fun _ => ⟨⟨?_, ?_, ?_, ?_⟩, hnoinfl p i⟩⟩
      · rw [hdisk' p f hf]; rfl
      · rw [hdisk' p f hf]; rfl
      · rw [hdisk' p f hf]; simp only [OsFile.ofDisk]
        exact (List.getElem?_eq_some_iff.1 hb).1
      · rw [hdisk' p f hf]; rfl
  · intro p f i hf hi
    simp [bytesMap, hf, hi]
  · rw [hfd]
  · intro t; simp [hin]
  · intro t ti h; simp at h
  · intro t ti h; simp at h
  · intro t ti h; simp at h

theorem os_local_init {GF : BundledGFunctors} (hPre : OsGpreS GF) (st : OsState) (h : OsInit st) :
    ⊢@{IProp GF} |==> ∃ hL : OsGS GF, osCtx hL st ∗ osStart hL st := by
  letI := hPre.osPreAllG
  obtain ⟨hwf, hcoh⟩ := osInit_wf_coh h
  imod ghost_map_alloc (GF := GF) (bytesMap st) with ⟨%γb, Hab, Hb⟩
  imod ghost_map_alloc (GF := GF) (metaMap st) with ⟨%γm, Ham, Hm⟩
  imod ghost_map_alloc (GF := GF) (∅ : GMap w64 OsFd) with ⟨%γf, Haf, -⟩
  imod ghost_map_alloc (GF := GF) (∅ : GMap w64 TokInfo) with ⟨%γt, Hat, -⟩
  imod ghostVar_alloc (GF := GF) ((∅ : GMap Loc (Option w8 × Bool)), 0) with ⟨%γv, Hv⟩
  icases (ghostVar_split_half γv 1 _).1 $$ Hv with ⟨Hv1, Hv2⟩
  imodintro
  iexists (⟨hPre.osPreAllG, γb, γm, γf, γt, γv⟩ : OsGS GF)
  isplitl [Hab Ham Haf Hat Hv1]
  · unfold osCtx
    iexists (bytesMap st), (metaMap st), ∅, ∅
    rw [cellView_of_maps_empty h.2.2.1, h.2.1, GMap.map_size_empty]
    iframe Hab Ham Haf Hat Hv1
    isplitr
    · ipureintro; exact ⟨hwf, hcoh⟩
    · iapply BigSepM.bigSepM_empty.2; itrivial
  · unfold osStart
    iframe

/-- The ghost state of the Linux file extension. The program gets every file and byte of the
initial state, and the means to allocate the invariant of the mapped cells (`osInv_alloc`). -/
instance os_interp : ExtInterp osFsExt where
  LocalGS := OsGS
  GlobalGS _ := Unit
  localCtx := osCtx
  globalCtx _ _ := iprop(True)
  PreG := OsGpreS
  initgP _ := True
  initP st _ := OsInit st
  globalStart _ _ := iprop(True)
  localStart := osStart
  global_init _ _ _ _ := by
    iapply bupd_intro; iexists (); isplitl [] <;> itrivial
  local_init _ hPre st _ h := os_local_init hPre st h

end Perennial

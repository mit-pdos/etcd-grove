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
  /-- Durable bytes known: `some d` at `i` if byte `i` of the image on disk is `d`. Only a
  successful sync changes the image on disk; it records the bytes it is given (`OsMeta.synced`).
  At boot, all of the file is known. -/
  dur : List (Option w8)
  /-- A bound on the length of the image on disk: a successful sync makes it the size; nothing
  else changes the image (`MetaOk.durLen`). Past it, a crash leaves arbitrary bytes. -/
  durHi : Nat

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
    (fun m => Pos.Countable.encode (m.size, m.lo, m.hi, m.named, m.ok, m.maps, m.dur, m.durHi))
    (fun a b h => by
      have h := Pos.encode_inj h
      cases a; cases b; simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h; subst h1 h2 h3 h4 h5 h6 h7 h8; rfl)

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
    (∃ f, st.file m.path = some f) ∧ 0 < b.addr ∧ b.addr + m.len ≤ maxAddr ∧ 0 < m.len
  maps_disj : ∀ b1 m1 b2 m2, st.maps !! b1 = some m1 → st.maps !! b2 = some m2 → b1 ≠ b2 →
    b1.addr + m1.len ≤ b2.addr ∨ b2.addr + m2.len ≤ b1.addr
  infl : ∀ t c, st.inflight !! t = some c → ∃ f, st.file c.path = some f
  infl_disj : ∀ t1 c1 t2 c2 i, st.inflight !! t1 = some c1 → st.inflight !! t2 = some c2 →
    t1 ≠ t2 → c1.path = c2.path → Affects st c1 i → ¬ Affects st c2 i
  sizes : ∀ p f, st.file p = some f → f.sizeLo ≤ f.cur.length ∧ f.cur.length ≤ f.sizeHi
  /-- A byte neither dirty nor lost has its page-cache byte on disk. -/
  coherent : ∀ p f i, st.file p = some f → f.dirty i = false → f.lost i = false →
    i < f.cur.length → i < f.durable.length → f.durable[i]? = f.cur[i]?

/-- What the ghost `OsMeta` `m` of the file `f` at `p` says of it. -/
structure MetaOk (p : GoString) (m : OsMeta) (f : OsFile) : Prop where
  size : m.size = f.cur.length
  named : m.named = f.named
  lo : m.lo ≤ f.sizeLo
  hi : f.sizeHi ≤ m.hi
  ok : m.ok = true → ∀ i, f.lost i = false
  maps : ∀ b len, m.maps !! b = some len ↔ st.maps !! b = some ⟨p, len⟩
  targets : ∀ t c, st.inflight !! t = some c → c.path = p → m.lo ≤ c.target st ∧ c.target st ≤ m.hi
  dur : ∀ (i : Nat) (d : w8), m.dur[i]? = some (some d) → f.durable[i]? = some d
  durLen : f.durable.length ≤ m.durHi

/-- The ghost maps mirror the state. -/
structure OsCoh (Γb : GMap (GoString × Nat) (w8 × Bool)) (Γm : GMap GoString (Option OsMeta))
    (Γf : GMap w64 OsFd) (Γt : GMap Nat TokInfo) : Prop where
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

/-! ### The ghost maps of a ghost state `hL`, with the `AllG` of `hL` -/

section wrappers
variable {GF : BundledGFunctors} (hL : OsGS GF)
variable {K V : Type} [DecidableEq K] [Pos.Countable K] [Pos.Countable V]

/-- The authoritative map `m` of the ghost map `γ` of `hL`. -/
def gAuth (γ : GName) (m : GMap K V) : IProp GF :=
  letI := hL.osAllG; ghostMapAuth γ 1 m

/-- The entry `k ↦ v` of the ghost map `γ` of `hL`. -/
def gElem (γ : GName) (k : K) (dq : DFrac) (v : V) : IProp GF :=
  letI := hL.osAllG; ghostMapElem γ k dq v

/-- The ghost variable of the cells' view. -/
def gVar (q : Qp) (a : GMap Loc (Option w8 × Bool) × Nat) : IProp GF :=
  letI := hL.osAllG; ghostVar hL.γv q a

instance gElem_timeless (γ : GName) (k : K) (dq : DFrac) (v : V) :
    Timeless (gElem (K := K) (V := V) hL γ k dq v) := by
  unfold gElem; letI := hL.osAllG; infer_instance

instance gAuth_timeless (γ : GName) (m : GMap K V) : Timeless (gAuth hL γ m) := by
  unfold gAuth; letI := hL.osAllG; infer_instance

instance gVar_timeless (q : Qp) (a : GMap Loc (Option w8 × Bool) × Nat) :
    Timeless (gVar hL q a) := by
  unfold gVar; letI := hL.osAllG; infer_instance

theorem gAuth_lookup (γ : GName) (m : GMap K V) (k : K) (dq : DFrac) (v : V) :
    ⊢ gAuth hL γ m -∗ gElem hL γ k dq v -∗ ⌜m !! k = some v⌝ := by
  unfold gAuth gElem; letI := hL.osAllG
  exact ghost_map_lookup

theorem gAuth_update (γ : GName) (m : GMap K V) (k : K) (v w : V) :
    ⊢ gAuth hL γ m -∗ gElem hL γ k (DFrac.own 1) v ==∗
      gAuth hL γ (<[k := w]> m) ∗ gElem hL γ k (DFrac.own 1) w := by
  unfold gAuth gElem; letI := hL.osAllG
  exact ghost_map_update w

theorem gAuth_insert (γ : GName) (m : GMap K V) (k : K) (v : V) (h : m !! k = none) :
    ⊢ gAuth hL γ m ==∗ gAuth hL γ (<[k := v]> m) ∗ gElem hL γ k (DFrac.own 1) v := by
  unfold gAuth gElem; letI := hL.osAllG
  exact ghost_map_insert k v h

theorem gAuth_delete (γ : GName) (m : GMap K V) (k : K) (v : V) :
    ⊢ gAuth hL γ m -∗ gElem hL γ k (DFrac.own 1) v ==∗ gAuth hL γ (GMap.delete k m) := by
  unfold gAuth gElem; letI := hL.osAllG
  exact ghost_map_delete

theorem gElem_valid_2 (γ : GName) (k : K) (dq1 dq2 : DFrac) (v1 v2 : V) :
    ⊢ gElem hL γ k dq1 v1 -∗ gElem hL γ k dq2 v2 -∗ ⌜✓ (dq1 • dq2) ∧ v1 = v2⌝ := by
  unfold gElem; letI := hL.osAllG
  exact ghostMapElem_valid_2 k γ dq1 dq2 v1 v2

theorem gElem_valid (γ : GName) (k : K) (dq : DFrac) (v : V) :
    ⊢ gElem hL γ k dq v -∗ ⌜✓ dq⌝ := by
  unfold gElem; letI := hL.osAllG
  exact ghostMapElem_valid k γ dq v

theorem gElem_split (γ : GName) (k : K) (q1 q2 : Qp) (v : V) :
    gElem hL γ k (DFrac.own (q1 + q2)) v ⊣⊢ gElem hL γ k (DFrac.own q1) v ∗ gElem hL γ k (DFrac.own q2) v := by
  unfold gElem; letI := hL.osAllG
  exact (ghostMapElem_fractional k γ v).fractional q1 q2

theorem gVar_agree (q1 q2 : Qp) (a1 a2 : GMap Loc (Option w8 × Bool) × Nat) :
    ⊢ gVar hL q1 a1 -∗ gVar hL q2 a2 -∗ ⌜a1 = a2⌝ := by
  unfold gVar; letI := hL.osAllG
  exact ghostVar_agree _ _ _ _ _

theorem gVar_update (a1 a2 b : GMap Loc (Option w8 × Bool) × Nat) :
    ⊢ gVar hL (1 : Qp).half a1 -∗ gVar hL (1 : Qp).half a2 ==∗
      gVar hL (1 : Qp).half b ∗ gVar hL (1 : Qp).half b := by
  unfold gVar; letI := hL.osAllG
  exact ghostVar_update_halves _ _ _ _

end wrappers


/-! ### Runs of bytes -/

section bytes
variable {GF : BundledGFunctors} (hL : OsGS GF)

/-- The bytes `xs` of the file `p` from `off` on. -/
def bytesG (p : GoString) (off : Nat) (dq : DFrac) (xs : List (w8 × Bool)) : IProp GF :=
  [∗list] k ↦ x ∈ xs, gElem hL hL.γb (p, off + k) dq x

instance bytesG_timeless (p : GoString) (off : Nat) (dq : DFrac) (xs : List (w8 × Bool)) :
    Timeless (bytesG hL p off dq xs) := by
  unfold bytesG; infer_instance

theorem bytesG_nil (p : GoString) (off : Nat) (dq : DFrac) :
    bytesG hL p off dq [] ⊣⊢ emp := .rfl

theorem bytesG_cons (p : GoString) (off : Nat) (dq : DFrac) (x : w8 × Bool)
    (xs : List (w8 × Bool)) :
    bytesG hL p off dq (x :: xs) ⊣⊢ gElem hL hL.γb (p, off) dq x ∗ bytesG hL p (off + 1) dq xs := by
  unfold bytesG
  refine BigSepL.bigSepL_cons.trans ?_
  rw [Nat.add_zero]
  refine sep_congr .rfl (.of_eq ?_)
  apply BigSepL.bigSepL_eq_of_forall_eq
  intro k _
  rw [show off + (k + 1) = off + 1 + k by omega]

theorem bytesG_append (p : GoString) (dq : DFrac) :
    ∀ (off : Nat) (xs ys : List (w8 × Bool)),
    bytesG hL p off dq (xs ++ ys) ⊣⊢ bytesG hL p off dq xs ∗ bytesG hL p (off + xs.length) dq ys
  | off, [], ys => by
    simp only [List.nil_append, List.length_nil, Nat.add_zero]
    exact ⟨by iintro H; iframe; iempintro, by iintro ⟨-, H⟩; iexact H⟩
  | off, x :: xs, ys => by
    refine (bytesG_cons hL p off dq x (xs ++ ys)).trans ?_
    refine (sep_congr .rfl (bytesG_append p dq (off + 1) xs ys)).trans ?_
    rw [show off + 1 + xs.length = off + (x :: xs).length by simp; omega]
    refine BIBase.BiEntails.trans ?_ (sep_congr (bytesG_cons hL p off dq x xs).symm .rfl)
    exact ⟨by iintro ⟨H1, H2, H3⟩; iframe, by iintro ⟨⟨H1, H2⟩, H3⟩; iframe⟩

/-- `m` with the bytes `ys` from `off` on. -/
def insertBytes (p : GoString) : Nat → List (w8 × Bool) → GMap (GoString × Nat) (w8 × Bool) →
    GMap (GoString × Nat) (w8 × Bool)
  | _, [], m => m
  | off, y :: ys, m => insertBytes p (off + 1) ys (<[(p, off) := y]> m)

theorem lookup_insertBytes (p : GoString) : ∀ (off : Nat) (ys : List (w8 × Bool))
    (m : GMap (GoString × Nat) (w8 × Bool)) (q : GoString) (j : Nat),
    insertBytes p off ys m !! (q, j) =
      if q = p ∧ off ≤ j ∧ j < off + ys.length then ys[j - off]? else m !! (q, j)
  | off, [], m, q, j => by simp [insertBytes]; intros; omega
  | off, y :: ys, m, q, j => by
    simp only [insertBytes, lookup_insertBytes p (off + 1) ys, GMap.lookup_insert_eq_iff,
      Prod.mk.injEq, List.length_cons]
    by_cases hq : q = p
    · subst hq
      by_cases hj : j = off
      · subst hj; simp; intro h; omega
      · by_cases h1 : off + 1 ≤ j ∧ j < off + 1 + ys.length
        · rw [if_pos ⟨rfl, h1⟩, if_pos ⟨rfl, by omega, by omega⟩]
          rw [show j - off = (j - (off + 1)) + 1 by omega]; simp
        · rw [if_neg (fun h => h1 h.2), if_neg (fun h => hj (Eq.symm h.2))]
          rw [if_neg (fun h => by omega)]
    · simp [hq, Ne.symm hq]

theorem bytesG_update (p : GoString) : ∀ (off : Nat) (xs ys : List (w8 × Bool))
    (Γb : GMap (GoString × Nat) (w8 × Bool)), ys.length = xs.length →
    gAuth hL hL.γb Γb ∗ bytesG hL p off (DFrac.own 1) xs ⊢
      |==> (gAuth hL hL.γb (insertBytes p off ys Γb) ∗ bytesG hL p off (DFrac.own 1) ys)
  | off, [], [], Γb, _ => by
    simp only [insertBytes]
    iintro ⟨H, -⟩; imodintro; iframe; iapply (bytesG_nil hL p off _).2; iempintro
  | off, x :: xs, y :: ys, Γb, hl => by
    simp only [insertBytes]
    iintro ⟨H, Hb⟩
    icases (bytesG_cons hL p off _ x xs).1 $$ Hb with ⟨Hx, Hxs⟩
    imod gAuth_update hL _ _ _ _ y $$ H Hx with ⟨H, Hy⟩
    imod bytesG_update p (off + 1) xs ys _ (by simpa using hl) $$ [H Hxs] with ⟨H, Hys⟩
    · iframe
    imodintro
    iframe H
    iapply (bytesG_cons hL p off _ y ys).2
    iframe
  | _, [], _ :: _, _, hl => by simp at hl
  | _, _ :: _, [], _, hl => by simp at hl

theorem bytesG_alloc (p : GoString) : ∀ (off : Nat) (ys : List (w8 × Bool))
    (Γb : GMap (GoString × Nat) (w8 × Bool)), (∀ k, k < ys.length → Γb !! (p, off + k) = none) →
    gAuth hL hL.γb Γb ⊢
      |==> (gAuth hL hL.γb (insertBytes p off ys Γb) ∗ bytesG hL p off (DFrac.own 1) ys)
  | off, [], Γb, _ => by
    simp only [insertBytes]
    iintro H; imodintro; iframe; iapply (bytesG_nil hL p off _).2; iempintro
  | off, y :: ys, Γb, hfree => by
    simp only [insertBytes]
    iintro H
    imod gAuth_insert hL _ _ (p, off) y (by simpa using hfree 0 (by simp)) $$ H with ⟨H, Hy⟩
    imod bytesG_alloc p (off + 1) ys _ (fun k hk => by
        rw [GMap.lookup_insert_ne _ _ (by simp; omega)]
        · rw [show off + 1 + k = off + (k + 1) by omega]; exact hfree (k + 1) (by simp; omega))
      $$ H with ⟨H, Hys⟩
    imodintro
    iframe H
    iapply (bytesG_cons hL p off _ y ys).2
    iframe

/-- `m` without the bytes `[off, off + n)` of `p`. -/
def deleteBytes (p : GoString) : Nat → Nat → GMap (GoString × Nat) (w8 × Bool) →
    GMap (GoString × Nat) (w8 × Bool)
  | _, 0, m => m
  | off, n + 1, m => deleteBytes p (off + 1) n (GMap.delete (p, off) m)

theorem lookup_deleteBytes (p : GoString) : ∀ (off n : Nat)
    (m : GMap (GoString × Nat) (w8 × Bool)) (q : GoString) (j : Nat),
    deleteBytes p off n m !! (q, j) = if q = p ∧ off ≤ j ∧ j < off + n then none else m !! (q, j)
  | off, 0, m, q, j => by simp [deleteBytes]; intros; omega
  | off, n + 1, m, q, j => by
    simp only [deleteBytes, lookup_deleteBytes p (off + 1) n, GMap.lookup_delete_iff,
      Prod.mk.injEq]
    by_cases hq : q = p
    · subst hq
      by_cases hj : j = off
      · subst hj; simp
      · by_cases h1 : off + 1 ≤ j ∧ j < off + 1 + n
        · rw [if_pos ⟨rfl, h1⟩, if_pos ⟨rfl, by omega, by omega⟩]
        · rw [if_neg (fun h => h1 h.2), if_neg (fun h => hj (Eq.symm h.2)),
            if_neg (fun h => by omega)]
    · simp [hq, Ne.symm hq]

theorem bytesG_delete (p : GoString) : ∀ (off : Nat) (xs : List (w8 × Bool))
    (Γb : GMap (GoString × Nat) (w8 × Bool)),
    gAuth hL hL.γb Γb ∗ bytesG hL p off (DFrac.own 1) xs ⊢
      |==> gAuth hL hL.γb (deleteBytes p off xs.length Γb)
  | off, [], Γb => by simp only [List.length_nil, deleteBytes]; iintro ⟨H, -⟩; imodintro; iexact H
  | off, x :: xs, Γb => by
    simp only [List.length_cons, deleteBytes]
    iintro ⟨H, Hb⟩
    icases (bytesG_cons hL p off _ x xs).1 $$ Hb with ⟨Hx, Hxs⟩
    imod gAuth_delete hL _ _ _ _ $$ H Hx with H
    iapply bytesG_delete p (off + 1) xs _
    iframe

theorem bytesG_lookup (p : GoString) (off : Nat) (dq : DFrac) (xs : List (w8 × Bool))
    (Γb : GMap (GoString × Nat) (w8 × Bool)) :
    ⊢ gAuth hL hL.γb Γb -∗ bytesG hL p off dq xs -∗
      ⌜∀ k (hk : k < xs.length), Γb !! (p, off + k) = some xs[k]⌝ := by
  iintro HA Hbs
  iapply pure_forall.2; iintro %k
  iapply pure_forall.2; iintro %hk
  unfold bytesG
  icases BigSepL.bigSepL_lookup (Φ := fun k (x : w8 × Bool) => gElem hL hL.γb (p, off + k) dq x)
    (List.getElem?_eq_getElem hk) $$ Hbs with Hb
  iapply gAuth_lookup $$ HA Hb

end bytes

/-- The ghost `OsMeta` of a file as on disk: all of it durable. -/
def initMeta (f : OsFile) : OsMeta :=
  ⟨f.cur.length, f.cur.length, f.cur.length, true, true, ∅, f.cur.map some, f.cur.length⟩

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

/-- What the ext holds for each in-flight change: the fraction of the file's `OsMeta` and the
bytes its first step took. -/
def tokRes (hL : OsGS GF) (st : OsState) (Γt : GMap Nat TokInfo) : IProp GF :=
  iprop([∗map] _t ↦ ti ∈ Γt,
    gElem hL hL.γm ti.c.path (DFrac.own ti.q) (some ti.om) ∗
    bytesG hL ti.c.path (affLo st ti.c) (DFrac.own 1) (ti.saved.map (·, false)))

/-- The interpretation of the state `st`. -/
def osCtx (hL : OsGS GF) (st : OsState) : IProp GF :=
  iprop(∃ (Γb : GMap (GoString × Nat) (w8 × Bool)) (Γm : GMap GoString (Option OsMeta))
      (Γf : GMap w64 OsFd) (Γt : GMap Nat TokInfo),
    ⌜OsWf st ∧ OsCoh st Γb Γm Γf Γt⌝ ∗
    gAuth hL hL.γb Γb ∗ gAuth hL hL.γm Γm ∗ gAuth hL hL.γf Γf ∗ gAuth hL hL.γt Γt ∗
    tokRes hL st Γt ∗
    gVar hL (1 : Qp).half (cellView st, GMap.size st.inflight))

/-- The start resources for a state with no fd, change or mapping: every file and byte, whole,
and the half of the cells' view that the invariant takes (`osInv_alloc`). -/
def osStart (hL : OsGS GF) (st : OsState) : IProp GF :=
  iprop(([∗map] k ↦ x ∈ bytesMap st, gElem hL hL.γb k (DFrac.own 1) x) ∗
    ([∗map] p ↦ mo ∈ metaMap st, gElem hL hL.γm p (DFrac.own 1) mo) ∗
    gVar hL (1 : Qp).half ((∅ : GMap Loc (Option w8 × Bool)), 0))

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
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro fd d h; simp [hfd] at h
  · intro b m h; simp [hmp] at h
  · intro b1 m1 _ _ h; simp [hmp] at h
  · intro t c h; simp [hin] at h
  · intro t1 c1 _ _ _ h; simp [hin] at h
  · intro p f hf
    rw [hdisk' p f hf]; simp [OsFile.ofDisk]
  · intro p f i hf _ _ _ _
    rw [hdisk' p f hf]; rfl
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
        refine ⟨f, rfl, ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
        · rw [hf]; rfl
        · rw [hf]; simp [initMeta, OsFile.ofDisk]
        · rw [hf]; simp [initMeta, OsFile.ofDisk]
        · intro _ i; rw [hf]; rfl
        · intro b len; simp [initMeta, hmp]
        · intro t c ht; simp [hin] at ht
        · intro i d h
          simp only [initMeta, List.getElem?_map, Option.map_eq_some_iff, Option.some.injEq] at h
          obtain ⟨b, hb, rfl⟩ := h
          rw [hf]; exact hb
        · rw [hf]; simp [initMeta, OsFile.ofDisk]
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
  imod ghost_map_alloc (GF := GF) (∅ : GMap Nat TokInfo) with ⟨%γt, Hat, -⟩
  imod ghostVar_alloc (GF := GF) ((∅ : GMap Loc (Option w8 × Bool)), 0) with ⟨%γv, Hv⟩
  icases (ghostVar_split_half γv 1 _).1 $$ Hv with ⟨Hv1, Hv2⟩
  imodintro
  iexists (⟨hPre.osPreAllG, γb, γm, γf, γt, γv⟩ : OsGS GF)
  isplitl [Hab Ham Haf Hat Hv1]
  · unfold osCtx tokRes gAuth gVar
    iexists (bytesMap st), (metaMap st), ∅, ∅
    rw [cellView_of_maps_empty h.2.2.1, h.2.1, GMap.map_size_empty]
    iframe Hab Ham Haf Hat Hv1
    isplitr
    · ipureintro; exact ⟨hwf, hcoh⟩
    · iapply BigSepM.bigSepM_empty.2; itrivial
  · unfold osStart gElem gVar
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

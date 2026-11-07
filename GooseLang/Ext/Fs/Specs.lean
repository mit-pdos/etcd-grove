/-
WP specs of the Linux file extension's data operations (`Impl.lean`): `close`, `flock`, `FdKind` of a
file's fd, `fstat`, `pread`, `fsync`, `mmap`, `munmap`, loads of mapped cells. `pwrite` is in
`Write.lean`, `ftruncate` in `Truncate.lean`/`TruncateShrink.lean`, `fallocate` and the OFD lock in
`Falloc.lean`; the resources and the step lemma in `World.lean`. Untrusted.

**Resources** (`World.lean`): `osByte i b dq (x, c)`, `osBytes i off dq xs`, `osMeta i dq m`,
`osFd fd dq d`, `osInv`; a mapped cell's other half is the client's, an ordinary heap points-to.
-/
module

public import GooseLang.Ext.Fs.World
public import GooseLang.Ext.Fs.Bridge

@[expose] public section

noncomputable section

namespace Perennial
namespace Fs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode
open goose_heap

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] [GoGlobalContext]
  [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}
attribute [local instance] Classical.propDecidable
theorem osWf_fds {st : OsState} (hwf : OsWf st) (X : GMap w64 OsFd)
    (hX : ∀ fd d, X !! fd = some d → ∃ f, st.file d.ino = some f) :
    OsWf (st.setProc { st.proc with fds := X }) :=
  { hwf with fds := hX }

theorem MetaOk.fds {st : OsState} {p : Ino} {m : OsMeta} {f : OsFile} (X : GMap w64 OsFd)
    (h : MetaOk st p m f) : MetaOk (st.setProc { st.proc with fds := X }) p m f :=
  ⟨h.size, h.lo, h.hi, h.ok, h.maps, h.targets, h.dur, h.zero⟩

theorem osCoh_fds {st : OsState} {Γb Γm Γf Γt} (hcoh : OsCoh st Γb Γm Γf Γt) (X : GMap w64 OsFd) :
    OsCoh (st.setProc { st.proc with fds := X }) Γb Γm X Γt :=
  { hcoh with
    fds := rfl
    meta_some := fun p m h => by
      obtain ⟨f, hf, hm⟩ := hcoh.meta_some p m h; exact ⟨f, hf, hm.fds X⟩ }

/-- `close(fd)`, with the whole fd. Whatever the errno, the fd is gone. -/
theorem wp_osClose (fd : w64) (d : OsFd) (hE : ↑osN ⊆ E) :
    {{ osInv (L := L) ∗ osFd (L := L) fd (DFrac.own 1) d }}
      (ExternalOp fsExt.name "Close" (Val (#fd))) @ s; E
    {{ (e : w64), RET #e; True }} := by
  iintro %Φ ⟨#Hinv, Hfd⟩ HΦ
  iapply wp_os_step "Close" (#fd) Φ (by simp) hE (by simp [DataOp]) $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %h Hw
  unfold osWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  obtain ⟨hwf, hcoh⟩ := Hwc
  unfold osFd
  icases gAuth_lookup _ _ _ _ _ _ $$ HAf Hfd with %Hfdl
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have hfd : st.proc.fds !! fd = some d := hcoh.fds ▸ Hfdl
  have hwf' : ∀ X : GMap w64 OsFd, (∀ fd d, X !! fd = some d → st.proc.fds !! fd = some d) →
      OsWf (st.setProc { st.proc with fds := X }) := fun X hX =>
    osWf_fds hwf X (fun fd d h => hwf.fds fd d (hX fd d h))
  have hdel : ∀ fd' d', (GMap.delete fd st.proc.fds) !! fd' = some d' → st.proc.fds !! fd' = some d' := by
    intro fd' d' h; rw [GMap.lookup_delete_iff] at h; split at h
    · cases h
    · exact h
  imodintro
  isplitr
  · ipureintro
    exact ⟨_, h, (st.setProc { st.proc with fds := GMap.delete fd st.proc.fds }),
      ⟨fd, 0, d, rfl, hfd, rfl, rfl⟩, mapsFresh_same rfl,
      heapRendered_same (hwf' _ hdel) rfl (cellView_congr hwf (hwf' _ hdel) rfl rfl rfl) Hag⟩
  inext
  iintro %e' %h' %st' %Hst
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsFsStep] at Hst
  obtain ⟨fd', e, d', hv, hfd', rfl, rfl⟩ := Hst
  cases go.intoVal_inj hv
  imod gAuth_delete _ _ _ _ _ $$ HAf Hfd with HAf
  imod cells_same hwf (hwf' _ hdel) Hr Hfr rfl (cellView_congr hwf (hwf' _ hdel) rfl rfl rfl) $$ [Hσ Hcells]
    with ⟨Hσ, Hcells⟩
  · iframe
  imodintro
  iexists Γb, Γm, (GMap.delete fd Γf), Γt
  have htr : tokRes gooseOsGS (st.setProc { st.proc with fds := GMap.delete fd st.proc.fds }) Γt =
      tokRes (gooseOsGS (L := L)) st Γt := rfl
  rw [htr]
  iframe
  isplitr
  · ipureintro; refine ⟨hwf' _ hdel, ?_⟩; rw [hcoh.fds]; exact osCoh_fds hcoh _
  iapply wp_value'
  iapply HΦ
  itrivial

/-- A read that returns all it reached: a successful outcome. -/
theorem full_read (r : List w8) : ∃ k, k ≤ r.length ∧ (0 < k ∨ r = []) ∧
    osRes (#r) 0 = osRes (#(r.take k)) 0 := by
  refine ⟨r.length, Nat.le_refl _, ?_, by rw [List.take_length]⟩
  cases r with
  | nil => exact .inr rfl
  | cons a r => exact .inl (by simp)

theorem readSees_exists {st : OsState} {p : Ino} {f : OsFile} (hf : st.file p = some f)
    (off n : Nat) : ReadSees st p off n ((f.contents.drop off).take n) := by
  refine ⟨⟨st.size p, Or.inl rfl, ?_⟩, fun i hi _ => ?_⟩
  · rw [size_of_file hf]; simp [contents_length]
  · simp only [hf, Option.map_some, Option.bind_some]
    simp only [List.getElem_take, List.getElem_drop]
    exact List.getElem?_eq_getElem _

/-- The bytes a client holds are the file's, and under no change in flight. -/
theorem osBytes_lookup {st : OsState} {Γb Γm Γf Γt} (hcoh : OsCoh st Γb Γm Γf Γt) (p : Ino)
    (off : Nat) (dq : DFrac) (xs : List (w8 × Bool)) :
    ⊢ gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γb Γb -∗ tokRes (gooseOsGS (L := L)) st Γt -∗
      osBytes (L := L) p off dq xs -∗
      ⌜∀ k (hk : k < xs.length), ∃ f, st.file p = some f ∧ f.contents[off + k]? = some xs[k].1 ∧
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

theorem coh_meta {st : OsState} {Γb Γm Γf Γt} (hcoh : OsCoh st Γb Γm Γf Γt) {p : Ino}
    {m : OsMeta} (h : Γm !! p = some m) :
    ∃ f, st.file p = some f ∧ MetaOk st p m f := by
  obtain ⟨f, hf, hm⟩ := hcoh.meta_some p m h
  exact ⟨f, hf, hm⟩

/-- `flock(fd, how)`: any errno. -/
theorem wp_osFlock (fd how : w64) (dq : DFrac) (d : OsFd) (hE : ↑osN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osFd (L := L) fd dq d -∗
      (∀ e : w64, osFd (L := L) fd dq d -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Flock" (Val (PairV (#fd) (#how)))) @ s; E {{ Φ }} := by
  iintro #Hinv Hfd HΦ
  iapply wp_os_step "Flock" _ Φ (by simp [val.isPanic]) hE (by simp [DataOp]) $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %h Hw
  unfold osWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  obtain ⟨hwf, hcoh⟩ := Hwc
  unfold osFd
  icases gAuth_lookup _ _ _ _ _ _ $$ HAf Hfd with %Hfdl
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have hfd : st.proc.fds !! fd = some d := hcoh.fds ▸ Hfdl
  imodintro
  isplitr
  · ipureintro
    exact ⟨_, h, st, ⟨fd, how, 0, d, rfl, hfd, rfl, rfl⟩, mapsFresh_same rfl,
      heapRendered_same hwf rfl rfl Hag⟩
  inext
  iintro %e' %h' %st' %Hst
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsFsStep] at Hst
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

/-- `FdKind(fd)` of a file's fd: `0`. -/
theorem wp_osFdKind (fd : w64) (dq : DFrac) (d : OsFd) (hE : ↑osN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osFd (L := L) fd dq d -∗
      (osFd (L := L) fd dq d -∗ Φ (#(0 : w64))) -∗
      WP (ExternalOp fsExt.name "FdKind" (Val (#fd))) @ s; E {{ Φ }} := by
  iintro #Hinv Hfd HΦ
  iapply wp_os_step "FdKind" _ Φ (by simp [val.isPanic]) hE (by simp [DataOp]) $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %h Hw
  unfold osWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  obtain ⟨hwf, hcoh⟩ := Hwc
  unfold osFd
  icases gAuth_lookup _ _ _ _ _ _ $$ HAf Hfd with %Hfdl
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have hfd : st.proc.fds !! fd = some d := hcoh.fds ▸ Hfdl
  imodintro
  isplitr
  · ipureintro
    exact ⟨_, h, st, ⟨fd, rfl, rfl, .inl ⟨⟨d, hfd⟩, rfl⟩⟩, mapsFresh_same rfl,
      heapRendered_same hwf rfl rfl Hag⟩
  inext
  iintro %e' %h' %st' %Hst
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsFsStep] at Hst
  obtain ⟨fd', hv, rfl, hres⟩ := Hst
  cases go.intoVal_inj hv
  rcases hres with ⟨-, rfl⟩ | ⟨hn, -, -⟩
  · imod cells_same hwf hwf Hr Hfr rfl rfl $$ [Hσ Hcells] with ⟨Hσ, Hcells⟩
    · iframe
    imodintro
    iexists Γb, Γm, Γf, Γt
    iframe
    isplitr
    · ipureintro; exact ⟨hwf, hcoh⟩
    iapply wp_value'
    iapply HΦ $$ Hfd
  · rw [hfd] at hn; cases hn

/-- `fstat(fd)`'s size, with a fraction of the file's `OsMeta`: its size, or an errno. -/
theorem wp_osFstat (fd : w64) (dq dqm : DFrac) (d : OsFd) (m : OsMeta) (hE : ↑osN ⊆ E)
    (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osFd (L := L) fd dq d -∗ osMeta (L := L) d.ino dqm (m) -∗
      (∀ sz : w64, ∀ e : w64, ⌜e = 0 ∧ sz = (W64 m.size) ∨ e ≠ 0 ∧ sz = 0⌝ -∗
        osFd (L := L) fd dq d -∗ osMeta (L := L) d.ino dqm (m) -∗ Φ (PairV (#sz) (#e))) -∗
      WP (ExternalOp fsExt.name "Fstat" (Val (#fd))) @ s; E {{ Φ }} := by
  iintro #Hinv Hfd Hm HΦ
  iapply wp_os_step "Fstat" _ Φ (by simp) hE (by simp [DataOp]) $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %h Hw
  unfold osWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  obtain ⟨hwf, hcoh⟩ := Hwc
  unfold osFd osMeta
  icases gAuth_lookup _ _ _ _ _ _ $$ HAf Hfd with %Hfdl
  icases gAuth_lookup _ _ _ _ _ _ $$ HAm Hm with %Hml
  icases tokRes_meta_frac _ $$ Htok Hm with %Hq
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have hfd : st.proc.fds !! fd = some d := hcoh.fds ▸ Hfdl
  obtain ⟨f, hf, hmo⟩ := coh_meta hcoh Hml
  have hnr := noReach_of_frac hcoh Hq
  imodintro
  isplitr
  · ipureintro
    exact ⟨_, h, st, ⟨fd, d, st.size d.ino, rfl, hfd, Or.inl rfl, rfl, Or.inl rfl⟩,
      mapsFresh_same rfl, heapRendered_same hwf rfl rfl Hag⟩
  inext
  iintro %e' %h' %st' %Hst
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsFsStep] at Hst
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
theorem wp_osPRead (fd off n : w64) (dq dqm dqb : DFrac) (d : OsFd) (m : OsMeta)
    (xs : List (w8 × Bool)) (hE : ↑osN ⊆ E) (hrd : d.readable = true) (hoff : 0 ≤ off.toInt)
    (hlen : xs.length = min n.toNat (m.size - off.toNat)) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osFd (L := L) fd dq d -∗ osMeta (L := L) d.ino dqm (m) -∗
      osBytes (L := L) d.ino off.toNat dqb xs -∗
      (∀ r : List w8, ∀ e : w64,
        ⌜∃ k ≤ xs.length, r = (xs.map Prod.fst).take k ∧ (e = 0 → 0 < k ∨ xs = [])⌝ -∗
        osFd (L := L) fd dq d -∗ osMeta (L := L) d.ino dqm (m) -∗
        osBytes (L := L) d.ino off.toNat dqb xs -∗ Φ (PairV (#r) (#e))) -∗
      WP (ExternalOp fsExt.name "PRead" (Val (PairV (#fd) (PairV (#off) (#n))))) @ s; E
        {{ Φ }} := by
  iintro #Hinv Hfd Hm Hbs HΦ
  iapply wp_os_step "PRead" _ Φ (by simp [val.isPanic]) hE (by simp [DataOp]) $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %h Hw
  unfold osWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  obtain ⟨hwf, hcoh⟩ := Hwc
  icases osBytes_lookup hcoh d.ino off.toNat dqb xs $$ HAb Htok Hbs with %Hbl
  unfold osFd osMeta
  icases gAuth_lookup _ _ _ _ _ _ $$ HAf Hfd with %Hfdl
  icases gAuth_lookup _ _ _ _ _ _ $$ HAm Hm with %Hml
  icases tokRes_meta_frac _ $$ Htok Hm with %Hq
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have hfd : st.proc.fds !! fd = some d := hcoh.fds ▸ Hfdl
  obtain ⟨f, hf, hmo⟩ := coh_meta hcoh Hml
  have hnr := noReach_of_frac hcoh Hq
  imodintro
  isplitr
  · ipureintro
    exact ⟨_, h, st, ⟨fd, off, n, d, _, rfl, hfd, hrd, hoff, readSees_exists hf _ _, rfl,
      Or.inl (full_read _)⟩, mapsFresh_same rfl, heapRendered_same hwf rfl rfl Hag⟩
  inext
  iintro %e' %h' %st' %Hst
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsFsStep] at Hst
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
  rcases hres with ⟨k, hk, hk0, rfl⟩ | ⟨k, e, hk, he, rfl⟩
  · have hp : ∃ k' ≤ xs.length, (xs.map Prod.fst).take k = (xs.map Prod.fst).take k' ∧
        ((0 : w64) = 0 → 0 < k' ∨ xs = []) :=
      ⟨k, by simpa using hk, rfl, fun _ => by
        rcases hk0 with h | h
        · exact .inl h
        · right; simpa using h⟩
    iapply wp_value'
    iapply HΦ $$ %_ %_ %hp Hfd Hm Hbs
  · have hp : ∃ k' ≤ xs.length, (xs.map Prod.fst).take k = (xs.map Prod.fst).take k' ∧
        (e = 0 → 0 < k' ∨ xs = []) := ⟨k, by simpa using hk, rfl, fun h => absurd h he⟩
    iapply wp_value'
    iapply HΦ $$ %_ %_ %hp Hfd Hm Hbs

/-- A racing `pread(fd, n, off)` (no `OsMeta`, as minibolt's `Snapshot`): where it reaches a
byte the client holds (any fraction), it reads it; on success it reaches every such byte below
`off + n`. Elsewhere the bytes, and how far past them it reads, are arbitrary. -/
theorem wp_osPRead_racy (fd off n : w64) (dq dqb : DFrac) (d : OsFd) (lo : Nat)
    (xs : List (w8 × Bool)) (hE : ↑osN ⊆ E) (hrd : d.readable = true) (hoff : 0 ≤ off.toInt)
    (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osFd (L := L) fd dq d -∗ osBytes (L := L) d.ino lo dqb xs -∗
      (∀ r : List w8, ∀ e : w64,
        ⌜∀ k (hk : k < xs.length), off.toNat ≤ lo + k → lo + k < off.toNat + n.toNat →
          ∀ (h : lo + k - off.toNat < r.length), r[lo + k - off.toNat] = xs[k].1⌝ -∗
        osFd (L := L) fd dq d -∗ osBytes (L := L) d.ino lo dqb xs -∗ Φ (PairV (#r) (#e))) -∗
      WP (ExternalOp fsExt.name "PRead" (Val (PairV (#fd) (PairV (#off) (#n))))) @ s; E
        {{ Φ }} := by
  iintro #Hinv Hfd Hbs HΦ
  iapply wp_os_step "PRead" _ Φ (by simp [val.isPanic]) hE (by simp [DataOp]) $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %h Hw
  unfold osWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  obtain ⟨hwf, hcoh⟩ := Hwc
  icases osBytes_lookup hcoh d.ino lo dqb xs $$ HAb Htok Hbs with %Hbl
  unfold osFd
  icases gAuth_lookup _ _ _ _ _ _ $$ HAf Hfd with %Hfdl
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have hfd : st.proc.fds !! fd = some d := hcoh.fds ▸ Hfdl
  obtain ⟨f, hf⟩ := hwf.fds fd d hfd
  imodintro
  isplitr
  · ipureintro
    exact ⟨_, h, st, ⟨fd, off, n, d, _, rfl, hfd, hrd, hoff, readSees_exists hf _ _, rfl,
      Or.inl (full_read _)⟩, mapsFresh_same rfl, heapRendered_same hwf rfl rfl Hag⟩
  inext
  iintro %e' %h' %st' %Hst
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsFsStep] at Hst
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
    have hlt : lo + k < f.size := by rw [← contents_length]; exact (List.getElem?_eq_some_iff.1 hb).1
    have hgt := statSees_gt hf hlt hn hss
    refine ⟨by rw [hrl]; omega, fun hlt' => ?_⟩
    have hn' : ¬ InflightAt st' d.ino (off.toNat + (lo + k - off.toNat)) := by
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
  have hres' : ∃ k' e, e' = osRes (#(r.take k')) e := by
    rcases hres with ⟨k', -, -, rfl⟩ | ⟨k', e, -, -, rfl⟩
    · exact ⟨k', 0, rfl⟩
    · exact ⟨k', e, rfl⟩
  obtain ⟨k', e, rfl⟩ := hres'
  iapply wp_value'
  iapply HΦ $$ %_ %_ %(fun k hk h1 h2 hlt => by
    have h' : lo + k - off.toNat < r.length := by simp at hlt; omega
    simp only [List.getElem_take]; exact (key k hk h1 h2).2 h') Hfd Hbs

/-- The facts `osBytes_lookup` gives, for every range of a list of held ranges. -/
theorem osBytes_lookup_list {st : OsState} {Γb Γm Γf Γt} (hcoh : OsCoh st Γb Γm Γf Γt)
    (p : Ino) :
    ∀ (rs : List (Nat × DFrac × List (w8 × Bool))),
    ⊢ gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γb Γb -∗ tokRes (gooseOsGS (L := L)) st Γt -∗
      ([∗list] x ∈ rs, osBytes (L := L) p x.1 x.2.1 x.2.2) -∗
      ⌜∀ x ∈ rs, ∀ k (hk : k < x.2.2.length), ∃ f, st.file p = some f ∧
        f.contents[x.1 + k]? = some x.2.2[k].1 ∧ ¬ InflightAt st p (x.1 + k)⌝
  | [] => by
    iintro _ _ _; ipureintro; intro x hx; cases hx
  | x :: rs => by
    iintro HAb Htok Hbs
    icases BigSepL.bigSepL_cons.1 $$ Hbs with ⟨H1, H2⟩
    icases osBytes_lookup hcoh p x.1 x.2.1 x.2.2 $$ HAb Htok H1 with %h1
    icases osBytes_lookup_list hcoh p rs $$ HAb Htok H2 with %h2
    ipureintro
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · exact h1
    · exact h2 y hy

/-- `wp_osPRead_racy` for a list of held ranges (each `(lo, dq, xs)`: `osBytes p lo dq xs`). -/
theorem wp_osPRead_racy_list (fd off n : w64) (dq : DFrac) (d : OsFd)
    (rs : List (Nat × DFrac × List (w8 × Bool))) (hE : ↑osN ⊆ E) (hrd : d.readable = true)
    (hoff : 0 ≤ off.toInt) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osFd (L := L) fd dq d -∗
      ([∗list] x ∈ rs, osBytes (L := L) d.ino x.1 x.2.1 x.2.2) -∗
      (∀ r : List w8, ∀ e : w64,
        ⌜∀ x ∈ rs, ∀ k (hk : k < x.2.2.length), off.toNat ≤ x.1 + k →
          x.1 + k < off.toNat + n.toNat →
          ∀ (h : x.1 + k - off.toNat < r.length), r[x.1 + k - off.toNat] = x.2.2[k].1⌝ -∗
        osFd (L := L) fd dq d -∗ ([∗list] x ∈ rs, osBytes (L := L) d.ino x.1 x.2.1 x.2.2) -∗
        Φ (PairV (#r) (#e))) -∗
      WP (ExternalOp fsExt.name "PRead" (Val (PairV (#fd) (PairV (#off) (#n))))) @ s; E
        {{ Φ }} := by
  iintro #Hinv Hfd Hbs HΦ
  iapply wp_os_step "PRead" _ Φ (by simp [val.isPanic]) hE (by simp [DataOp]) $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %h Hw
  unfold osWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  obtain ⟨hwf, hcoh⟩ := Hwc
  icases osBytes_lookup_list hcoh d.ino rs $$ HAb Htok Hbs with %Hbl
  unfold osFd
  icases gAuth_lookup _ _ _ _ _ _ $$ HAf Hfd with %Hfdl
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have hfd : st.proc.fds !! fd = some d := hcoh.fds ▸ Hfdl
  obtain ⟨f, hf⟩ := hwf.fds fd d hfd
  imodintro
  isplitr
  · ipureintro
    exact ⟨_, h, st, ⟨fd, off, n, d, _, rfl, hfd, hrd, hoff, readSees_exists hf _ _, rfl,
      Or.inl (full_read _)⟩, mapsFresh_same rfl, heapRendered_same hwf rfl rfl Hag⟩
  inext
  iintro %e' %h' %st' %Hst
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsFsStep] at Hst
  obtain ⟨fd', off', n', d', r, hv, hfd', -, -, hrs, rfl, hres⟩ := Hst
  injection hv with h1 h2
  injection h2 with h3 h4
  cases go.intoVal_inj h1; cases go.intoVal_inj h3; cases go.intoVal_inj h4
  simp only [FdOpen, hfd, Option.some.injEq] at hfd'; subst hfd'
  obtain ⟨⟨sz, hss, hrl⟩, hrb⟩ := hrs
  have key : ∀ x ∈ rs, ∀ k (hk : k < x.2.2.length), off.toNat ≤ x.1 + k →
      x.1 + k < off.toNat + n.toNat →
      x.1 + k - off.toNat < r.length ∧
      ∀ (h : x.1 + k - off.toNat < r.length), r[x.1 + k - off.toNat] = x.2.2[k].1 := by
    intro x hx k hk h1 h2
    obtain ⟨f', hf', hb, hn⟩ := Hbl x hx k hk
    rw [hf] at hf'; cases hf'
    have hlt : x.1 + k < f.size := by rw [← contents_length]; exact (List.getElem?_eq_some_iff.1 hb).1
    have hgt := statSees_gt hf hlt hn hss
    refine ⟨by rw [hrl]; omega, fun hlt' => ?_⟩
    have hn' : ¬ InflightAt st' d.ino (off.toNat + (x.1 + k - off.toNat)) := by
      rw [show off.toNat + (x.1 + k - off.toNat) = x.1 + k by omega]; exact hn
    have := hrb _ hlt' hn'
    simp only [hf, Option.map_some, Option.bind_some] at this
    rw [show off.toNat + (x.1 + k - off.toNat) = x.1 + k by omega, hb] at this
    exact (Option.some.inj this).symm
  imod cells_same hwf hwf Hr Hfr rfl rfl $$ [Hσ Hcells] with ⟨Hσ, Hcells⟩
  · iframe
  imodintro
  iexists Γb, Γm, Γf, Γt
  iframe
  isplitr
  · ipureintro; exact ⟨hwf, hcoh⟩
  have hres' : ∃ k' e, e' = osRes (#(r.take k')) e := by
    rcases hres with ⟨k', -, -, rfl⟩ | ⟨k', e, -, -, rfl⟩
    · exact ⟨k', 0, rfl⟩
    · exact ⟨k', e, rfl⟩
  obtain ⟨k', e, rfl⟩ := hres'
  iapply wp_value'
  iapply HΦ $$ %_ %_ %(fun x hx k hk h1 h2 hlt => by
    have h' : x.1 + k - off.toNat < r.length := by simp at hlt; omega
    simp only [List.getElem_take]; exact (key x hx k hk h1 h2).2 h') Hfd Hbs

/-- The durable bytes a sync of the bytes `xs` from `lo` makes known: theirs. -/
def durOf (lo : Nat) (xs : List (w8 × Bool)) : List (Option w8) :=
  List.replicate lo none ++ xs.map (fun x => some x.1)

theorem durOf_some {lo : Nat} {xs : List (w8 × Bool)} {i : Nat} {d : w8}
    (h : (durOf lo xs)[i]? = some (some d)) :
    ∃ k, ∃ hk : k < xs.length, i = lo + k ∧ xs[k].1 = d := by
  unfold durOf at h
  rw [List.getElem?_append] at h
  split at h
  · rw [List.getElem?_replicate] at h; split at h <;> simp at h
  · rename_i hi
    rw [List.length_replicate] at h hi
    rw [List.getElem?_map] at h
    cases hx : xs[i - lo]? with
    | none => rw [hx] at h; cases h
    | some x =>
      rw [hx] at h; simp only [Option.map_some, Option.some.injEq] at h
      obtain ⟨hk, hx'⟩ := List.getElem?_eq_some_iff.1 hx
      exact ⟨i - lo, hk, by omega, by rw [hx']; exact h⟩

/-- The `OsMeta` after a successful sync of the bytes `xs` from `lo`: the size is durable, and the
durable bytes known are `xs`'s if no byte is lost (`m.ok`; then every byte is durable), none
otherwise. -/
def OsMeta.synced (m : OsMeta) (lo : Nat) (xs : List (w8 × Bool)) : OsMeta :=
  { m with lo := m.size, hi := m.size, dur := if m.ok then durOf lo xs else [] }

/-- The bytes after a successful sync: clean, unless a failed sync may have lost one. -/
def syncedBytes (m : OsMeta) (xs : List (w8 × Bool)) : List (w8 × Bool) :=
  if m.ok then xs.map (fun x => (x.1, true)) else xs

/-- The durable bytes known `a`, with those of `b` over them. -/
def durOverlay : List (Option w8) → List (Option w8) → List (Option w8)
  | a, [] => a
  | [], b => b
  | x :: a, y :: b => (y.or x) :: durOverlay a b

theorem durOverlay_nil (a : List (Option w8)) : durOverlay a [] = a := by
  cases a <;> rfl

theorem length_durOverlay : ∀ (a b : List (Option w8)),
    (durOverlay a b).length = max a.length b.length
  | a, [] => by simp [durOverlay_nil]
  | [], y :: b => by simp [durOverlay]
  | x :: a, y :: b => by simp [durOverlay, length_durOverlay a b, Nat.succ_max_succ]

theorem durOverlay_some : ∀ {a b : List (Option w8)} {i : Nat} {d : w8},
    (durOverlay a b)[i]? = some (some d) → b[i]? = some (some d) ∨ a[i]? = some (some d)
  | a, [], i, d, h => by rw [durOverlay_nil] at h; exact Or.inr h
  | [], y :: b, i, d, h => by simp only [durOverlay] at h; exact Or.inl h
  | x :: a, y :: b, 0, d, h => by
      simp only [durOverlay, List.getElem?_cons_zero, Option.some.injEq] at h ⊢
      cases y with
      | some y' => exact Or.inl h
      | none => exact Or.inr h
  | x :: a, y :: b, i + 1, d, h => by
      simp only [durOverlay, List.getElem?_cons_succ] at h ⊢
      exact durOverlay_some h

/-- A successful sync keeps a clean byte clean. -/
theorem synced_keepClean (f : OsFile) (busy : Nat → Prop) [DecidablePred busy] (b : Nat)
    (hsz : f.sizeLo ≤ f.size) (h : CleanPhys f b) : CleanPhys (f.synced busy) b := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨by simp [OsFile.synced]; omega, fun v hv => ?_⟩
  rw [synced_rawAt]
  simp only [OsFile.synced] at hv
  split at hv
  · simp only [List.mem_singleton] at hv; subst hv; rfl
  · exact h2 v hv

/-- The oldest version of a clean byte's sector holds the page cache's byte. -/
theorem clean_head {f : OsFile} {b : Nat} (h : CleanPhys f b) :
    ∀ v, (f.secs (b / 512)).vers.head? = some v → v.toList.getD (b % 512) 0 = f.rawAt b :=
  fun v hv => h.2 v (List.mem_of_mem_head? hv)

/-- `m.synced lo xs`, with the durable bytes known also recording the bytes `ys2` from `lo2`
(clean bytes, which the sync leaves durable: `wp_osFsync_keep`). -/
def OsMeta.syncedKeep (m : OsMeta) (lo : Nat) (xs : List (w8 × Bool)) (lo2 : Nat)
    (ys2 : List (w8 × Bool)) : OsMeta :=
  { m.synced lo xs with dur := durOverlay (m.synced lo xs).dur (durOf lo2 ys2) }

theorem OsMeta.syncedKeep_nil (m : OsMeta) (lo : Nat) (xs : List (w8 × Bool)) :
    m.syncedKeep lo xs 0 [] = m.synced lo xs := by
  simp [OsMeta.syncedKeep, durOf, durOverlay_nil]

/-- `fsync(fd)` (and `fdatasync`), as `wp_osFsync`, also given bytes `ys2` from `lo2`, at any
fraction, that the caller shows clean: a clean byte is not dirty, so the sync keeps its durable
byte, which is its page-cache byte; on success the durable bytes known include them
(`OsMeta.syncedKeep`). -/
theorem wp_osFsync_keep (fd : w64) (dq : DFrac) (d : OsFd) (m : OsMeta) (lo : Nat)
    (xs : List (w8 × Bool)) (lo2 : Nat) (dq2 : DFrac) (ys2 : List (w8 × Bool))
    (hc2 : ∀ y ∈ ys2, y.2 = true) (hE : ↑osN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osFd (L := L) fd dq d -∗ osMeta (L := L) d.ino (DFrac.own 1) (m) -∗
      osBytes (L := L) d.ino lo (DFrac.own 1) xs -∗ osBytes (L := L) d.ino lo2 dq2 ys2 -∗
      (∀ e : w64,
        ((⌜e = 0⌝ ∗ osMeta (L := L) d.ino (DFrac.own 1) ((m.syncedKeep lo xs lo2 ys2)) ∗
            osBytes (L := L) d.ino lo (DFrac.own 1) (syncedBytes m xs)) ∨
         (⌜e ≠ 0 ∧ e ≠ EINTR⌝ ∗
            osMeta (L := L) d.ino (DFrac.own 1) ({ m with ok := false }) ∗
            osBytes (L := L) d.ino lo (DFrac.own 1) xs)) -∗
        osBytes (L := L) d.ino lo2 dq2 ys2 -∗ osFd (L := L) fd dq d -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Fsync" (Val (#fd))) @ s; E {{ Φ }} := by
  iintro #Hinv Hfd Hm Hbs Hys HΦ
  iapply wp_os_step "Fsync" _ Φ (by simp) hE (by simp [DataOp]) $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %h Hw
  unfold osWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  obtain ⟨hwf, hcoh⟩ := Hwc
  unfold osFd osMeta osBytes
  icases bytesG_lookup _ d.ino lo _ xs Γb $$ HAb Hbs with %Hbl
  icases bytesG_lookup _ d.ino lo2 _ ys2 Γb $$ HAb Hys with %Hbl2
  icases gAuth_lookup _ _ _ _ _ _ $$ HAf Hfd with %Hfdl
  icases gAuth_lookup _ _ _ _ _ _ $$ HAm Hm with %Hml
  icases tokRes_meta_whole _ $$ Htok Hm with %Hnt
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have hfd : st.proc.fds !! fd = some d := hcoh.fds ▸ Hfdl
  obtain ⟨f, hf, hmo⟩ := coh_meta hcoh Hml
  have hnoI : ∀ i, ¬ InflightAt st d.ino i := by
    rintro i ⟨t, c, ht, hcp, -⟩; exact noTok_of_whole hcoh Hnt t c ht hcp
  have hnoS : ∀ n, ¬ SecBusy st d.ino n := fun n hn => by
    obtain ⟨b, -, -, hb⟩ := hn; exact hnoI b hb
  have hszf := hwf.sizes d.ino f hf
  have hvf : ∀ n, (f.secs n).vers ≠ [] := fun n => hwf.vers d.ino f n hf
  -- the two outcomes
  have hwfS : OsWf (st.setFile d.ino (f.synced (SecBusy st d.ino ·))) :=
    osWf_setFile_sameCur hwf hf rfl (by simp [OsFile.synced])
      (fun n => synced_vers f _ n (hvf n))
  have hwfF : OsWf (st.setFile d.ino (f.syncFailed (SecBusy st d.ino ·))) :=
    osWf_setFile_sameCur hwf hf rfl hszf (fun n => syncFailed_vers f _ n (hvf n))
  imodintro
  isplitr
  · ipureintro
    exact ⟨_, h, _, ⟨fd, d, f, rfl, hfd, hf, .inl ⟨rfl, rfl⟩⟩, mapsFresh_same rfl,
      heapRendered_same hwfS rfl (cellView_setFile_sameCur hwf hwfS hf (synced_contents f _) rfl)
        Hag⟩
  inext
  iintro %e' %h' %st' %Hst
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsFsStep] at Hst
  obtain ⟨fd', d', f', hv, hfd', hf', hres⟩ := Hst
  cases go.intoVal_inj hv
  simp only [FdOpen, hfd, Option.some.injEq] at hfd'; subst hfd'
  rw [hf] at hf'; cases hf'
  have hs := sizes_setFile_sameCur (f' := f.synced (SecBusy st d.ino ·)) hf rfl
  have hsF := sizes_setFile_sameCur (f' := f.syncFailed (SecBusy st d.ino ·)) hf rfl
  rcases hres with ⟨rfl, rfl⟩ | ⟨e, he, hEINTR, rfl, rfl⟩
  · -- success
    have hkeep : ∀ i, CleanPhys f i → CleanPhys (f.synced (SecBusy st d.ino ·)) i :=
      fun i hc => synced_keepClean f _ i hszf.1 hc
    -- with `ok`, every byte of the file is clean after the sync
    have hokc : m.ok = true → ∀ b, b < f.size → CleanPhys (f.synced (SecBusy st d.ino ·)) b :=
      fun hok b hb => synced_clean f _ b hb (hnoS _) (by
        cases hd : (f.secs (b / 512)).dirty
        · exact .inr (hmo.ok hok _ hd)
        · exact .inl rfl) (hvf _)
    imod gAuth_update _ _ _ _ _ (m.syncedKeep lo xs lo2 ys2) $$ HAm Hm with ⟨HAm, Hm⟩
    imod bytesG_update _ d.ino lo xs (syncedBytes m xs) Γb
      (by unfold syncedBytes; split <;> simp) $$ [HAb Hbs] with ⟨HAb, Hbs⟩
    · iframe
    imod cells_same hwf hwfS Hr Hfr rfl
      (cellView_setFile_sameCur hwf hwfS hf (synced_contents f _) rfl)
      $$ [Hσ Hcells] with ⟨Hσ, Hcells⟩
    · iframe
    imodintro
    iexists _, _, Γf, Γt
    have htr : tokRes gooseOsGS (st.setFile d.ino (f.synced (SecBusy st d.ino ·))) Γt =
        tokRes (gooseOsGS (L := L)) st Γt := by
      unfold tokRes; simp only [affLo_congr hs]
    rw [htr]
    iframe
    isplitr
    · ipureintro
      refine ⟨hwfS, osCoh_setFile_sameCur (f' := f.synced (SecBusy st d.ino ·)) hcoh hf
        (synced_contents f _) rfl ?_ lo xs (syncedBytes m xs)
        (by unfold syncedBytes; split <;> simp) Hbl ?_ hkeep ?_ hnoI⟩
      · refine ⟨by simp [OsMeta.syncedKeep, OsMeta.synced, hmo.size, synced_size],
          by simp [OsMeta.syncedKeep, OsMeta.synced, OsFile.synced, hmo.size],
          by simp [OsMeta.syncedKeep, OsMeta.synced, OsFile.synced, hmo.size],
          (fun hok n hd => by
            simp only [OsMeta.syncedKeep, OsMeta.synced] at hok
            simp only [OsFile.synced] at hd ⊢
            split
            · simp
            · rename_i hn
              split at hd
              · exact absurd ‹_› hn
              · exact hmo.ok hok n hd),
          hmo.maps, fun t c ht hcp => absurd hcp (noTok_of_whole hcoh Hnt t c ht), ?_,
          fun hz b hb => by
            rw [synced_rawAt]
            exact hmo.zero (by simpa [OsMeta.syncedKeep, OsMeta.synced] using hz) b
              (by simpa [synced_size] using hb)⟩
        intro i b hib0 v hv
        simp only [OsMeta.syncedKeep] at hib0
        rcases durOverlay_some hib0 with hib2 | hib
        · obtain ⟨k, hk, rfl, rfl⟩ := durOf_some hib2
          obtain ⟨f1, h1, hb, hc1⟩ := hcoh.bytes _ _ _ (Hbl2 k hk)
          rw [hf] at h1; cases h1
          have hc := hkeep _ (hc1 (hc2 _ (List.getElem_mem hk))).1
          rw [clean_head hc v hv, synced_rawAt]
          rw [contents_getElem?] at hb; split at hb
          · exact Option.some.inj hb
          · cases hb
        simp only [OsMeta.synced] at hib
        split at hib
        · rename_i hok
          obtain ⟨k, hk, rfl, rfl⟩ := durOf_some hib
          obtain ⟨f1, h1, hb, -⟩ := hcoh.bytes _ _ _ (Hbl k hk)
          rw [hf] at h1; cases h1
          rw [contents_getElem?] at hb; split at hb
          · rename_i hi
            rw [clean_head (hokc hok _ hi) v hv, synced_rawAt]; exact Option.some.inj hb
          · cases hb
        · simp at hib
      · intro k hk; unfold syncedBytes at hk ⊢; split <;> simp
      · intro k hk hc
        have hk' : k < xs.length := by unfold syncedBytes at hk; split at hk <;> simpa using hk
        obtain ⟨f1, h1, hb, hc1⟩ := hcoh.bytes _ _ _ (Hbl k hk')
        rw [hf] at h1; cases h1
        unfold syncedBytes at hc; split at hc
        · rename_i hok
          rw [contents_getElem?] at hb; split at hb
          · exact hokc hok _ ‹_›
          · cases hb
        · exact hkeep _ (hc1 hc).1
    iapply wp_value'
    iapply HΦ $$ [Hm Hbs] Hys Hfd
    ileft; iframe; ipureintro; rfl
  · -- failure
    have hkeep : ∀ i, CleanPhys f i → CleanPhys (f.syncFailed (SecBusy st d.ino ·)) i :=
      fun i hc => syncFailed_clean f _ i hc
    imod gAuth_update _ _ _ _ _ ({ m with ok := false }) $$ HAm Hm with ⟨HAm, Hm⟩
    imod bytesG_update _ d.ino lo xs xs Γb rfl $$ [HAb Hbs] with ⟨HAb, Hbs⟩
    · iframe
    imod cells_same hwf hwfF Hr Hfr rfl
      (cellView_setFile_sameCur hwf hwfF hf (syncFailed_contents f _) rfl)
      $$ [Hσ Hcells] with ⟨Hσ, Hcells⟩
    · iframe
    imodintro
    iexists _, _, Γf, Γt
    have htr : tokRes gooseOsGS (st.setFile d.ino (f.syncFailed (SecBusy st d.ino ·))) Γt =
        tokRes (gooseOsGS (L := L)) st Γt := by
      unfold tokRes; simp only [affLo_congr hsF]
    rw [htr]
    iframe
    isplitr
    · ipureintro
      refine ⟨hwfF, osCoh_setFile_sameCur (f' := f.syncFailed (SecBusy st d.ino ·)) hcoh hf
        (syncFailed_contents f _) rfl ?_ lo xs xs rfl Hbl (fun _ _ => rfl)
        hkeep ?_ hnoI⟩
      · refine ⟨hmo.size, hmo.lo, hmo.hi, (fun h => by cases h), hmo.maps,
          fun t c ht hcp => absurd hcp (noTok_of_whole hcoh Hnt t c ht), ?_,
          fun hz b hb => by
            rw [syncFailed_rawAt]
            exact hmo.zero (by simpa using hz) b (by simpa [syncFailed_size] using hb)⟩
        intro b d0 hb v hv
        have hv' : (f.secs (b / 512)).vers.head? = some v := by
          simpa [OsFile.syncFailed] using (by
            simp only [OsFile.syncFailed] at hv; split at hv <;> exact hv)
        exact hmo.dur b d0 hb v hv'
      · intro k hk hc
        obtain ⟨f1, h1, -, hc1⟩ := hcoh.bytes _ _ _ (Hbl k hk)
        rw [hf] at h1; cases h1
        exact hkeep _ (hc1 hc).1
    iapply wp_value'
    iapply HΦ $$ [Hm Hbs] Hys Hfd
    iright; iframe; ipureintro; exact ⟨he, hEINTR⟩

/-- `fsync(fd)` (and `fdatasync`), with the whole of the file's `OsMeta`, so that no change is in
flight on it, and some of its bytes, whole. On success the size is durable, and the bytes are
clean unless an earlier failed sync lost one (`m.ok`); on failure, which is never `EINTR`, nothing
more is clean, and bytes may be lost (`ok := false`). -/
theorem wp_osFsync (fd : w64) (dq : DFrac) (d : OsFd) (m : OsMeta) (lo : Nat)
    (xs : List (w8 × Bool)) (hE : ↑osN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osFd (L := L) fd dq d -∗ osMeta (L := L) d.ino (DFrac.own 1) (m) -∗
      osBytes (L := L) d.ino lo (DFrac.own 1) xs -∗
      (∀ e : w64,
        ((⌜e = 0⌝ ∗ osMeta (L := L) d.ino (DFrac.own 1) ((m.synced lo xs)) ∗
            osBytes (L := L) d.ino lo (DFrac.own 1) (syncedBytes m xs)) ∨
         (⌜e ≠ 0 ∧ e ≠ EINTR⌝ ∗
            osMeta (L := L) d.ino (DFrac.own 1) ({ m with ok := false }) ∗
            osBytes (L := L) d.ino lo (DFrac.own 1) xs)) -∗
        osFd (L := L) fd dq d -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Fsync" (Val (#fd))) @ s; E {{ Φ }} := by
  iintro #Hinv Hfd Hm Hbs HΦ
  have hemp : osBytes (L := L) d.ino 0 (DFrac.own 1) [] ⊣⊢ emp := by
    unfold osBytes bytesG; simp
  iapply wp_osFsync_keep fd dq d m lo xs 0 (DFrac.own 1) [] (by simp) hE Φ $$ Hinv Hfd Hm Hbs
    [] [HΦ]
  · iapply hemp.2; iempintro
  iintro %e He - Hfd
  rw [OsMeta.syncedKeep_nil]
  iapply HΦ $$ He Hfd

/-- `mmap(nil, len, PROT_READ, MAP_SHARED[|MAP_POPULATE], fd, 0)`, with the whole of the file's
`OsMeta`, so that no change is in flight on it: on success, fresh cells at `base`, whose client
halves hold the file's bytes, then holes past its end, inside the address space; on failure,
`nil`. -/
theorem wp_osMmap (fd off len prot fl : w64) (dq : DFrac) (d : OsFd) (m : OsMeta) (hE : ↑osN ⊆ E)
    (hrd : d.readable = true) (hoff : off = 0) (hlen : 0 < len.toInt)
    (hprot : prot.toNat = PROT_READ)
    (hfl : fl.toNat = MAP_SHARED ∨ fl.toNat = MAP_SHARED + MAP_POPULATE) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osFd (L := L) fd dq d -∗ osMeta (L := L) d.ino (DFrac.own 1) (m) -∗
      (∀ base : Loc, ∀ e : w64,
        ((⌜e = 0 ∧ 0 < base.addr ∧ base.addr + len.toNat ≤ maxAddr⌝ ∗
            osMeta (L := L) d.ino (DFrac.own 1) ({ m with maps := <[base := len.toNat]> m.maps }) ∗
            ∃ bs : List w8, ⌜bs.length = m.size⌝ ∗
              cellsR base 0 len.toNat (fun i => toCellVal bs[i]?)) ∨
         (⌜e ≠ 0 ∧ base = null⌝ ∗ osMeta (L := L) d.ino (DFrac.own 1) (m))) -∗
        osFd (L := L) fd dq d -∗ Φ (PairV (#base) (#e))) -∗
      WP (ExternalOp fsExt.name "Mmap"
        (Val (PairV (#fd) (PairV (#off) (PairV (#len) (PairV (#prot) (#fl))))))) @ s; E {{ Φ }} := by
  iintro #Hinv Hfd Hm HΦ
  iapply wp_os_step "Mmap" _ Φ (by simp [val.isPanic]) hE (by simp [DataOp]) $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %h Hw
  unfold osWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  obtain ⟨hwf, hcoh⟩ := Hwc
  unfold osFd osMeta
  icases gAuth_lookup _ _ _ _ _ _ $$ HAf Hfd with %Hfdl
  icases gAuth_lookup _ _ _ _ _ _ $$ HAm Hm with %Hml
  icases tokRes_meta_whole _ $$ Htok Hm with %Hnt
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have hfd : st.proc.fds !! fd = some d := hcoh.fds ▸ Hfdl
  obtain ⟨f, hf, hmo⟩ := coh_meta hcoh Hml
  have hnt := noTok_of_whole hcoh Hnt
  have hnb : ¬ BusyAt st d.ino := by rintro ⟨t, c, ht, hcp⟩; exact hnt t c ht hcp
  have hnoI : ∀ i, ¬ InflightAt st d.ino i := by
    rintro i ⟨t, c, ht, hcp, -⟩; exact hnt t c ht hcp
  imodintro
  isplitr
  · ipureintro
    exact ⟨_, h, st, ⟨fd, off, len, prot, fl, d, rfl, hfd, hrd, hoff, hlen, hprot, hfl, hnb,
      .inr ⟨1, by decide, rfl, rfl⟩⟩, mapsFresh_same rfl, heapRendered_same hwf rfl rfl Hag⟩
  inext
  iintro %e' %h' %st' %Hst
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsFsStep] at Hst
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
    have hfresh := Hfr base ⟨d.ino, n⟩ (by rw [hst']; exact GMap.lookup_insert _ _ _) hnone
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
        simp only [OsState.setProc, GMap.lookup_insert_eq_iff] at hb
        split at hb
        · rename_i heq; subst heq; cases hb; exact ⟨⟨f, hf⟩, hpos, by simpa using hmax, hn0⟩
        · exact hwf.maps b m0 hb
      · intro b1 m1 b2 m2 hb1 hb2 hne
        simp only [OsState.setProc, GMap.lookup_insert_eq_iff] at hb1 hb2
        have key : ∀ b m0, st.proc.maps !! b = some m0 →
            base.addr + n ≤ b.addr ∨ b.addr + m0.len ≤ base.addr := by
          intro b m0 hb
          obtain ⟨-, -, -, hl0⟩ := hwf.maps b m0 hb
          apply Classical.byContradiction; intro hc
          simp only [not_or, Int.not_le] at hc
          by_cases hle : b.addr ≤ base.addr
          · apply hnotmapped 0 hn0
            exact ⟨m0.ino, (base.addr - b.addr).toNat, b, m0, hb, rfl, by omega,
              by cases b; cases base; simp [Loc.add] at *; omega⟩
          · apply hnotmapped (b.addr - base.addr).toNat (by omega)
            exact ⟨m0.ino, 0, b, m0, hb, rfl, hl0, by cases b; cases base; simp [Loc.add] at *; omega⟩
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
    have hmapsT : ∀ k, k < n → MapsTo st' (base +ₗ (k : Int)) d.ino k :=
      fun k hk => ⟨base, ⟨d.ino, n⟩, by rw [hst']; exact GMap.lookup_insert _ _ _, rfl, hk, rfl⟩
    let vf : Nat → val := fun i => toCellVal f.contents[i]?
    have hcb : ∀ i, cellByte st' d.ino i = f.contents[i]? := fun i => by
      subst hst'; exact cellByte_noinfl (st := (st.setProc { st.proc with maps := _ })) hf (hnoI i)
    imod cells_step st st' h h' _ ∅ (mkCellsR base vf 0 n) hwf hwf' Hr Hfr
      (fun b m0 hb => by
        simp only [hst', OsState.setProc, GMap.lookup_insert_eq_iff] at hb
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
        apply cellView_lookup_congr hwf hwf' (by rw [hst']; rfl) (by rw [hst']; rfl)
        intro q i
        constructor
        · rintro ⟨b, m0, hb, hp, hi, rfl⟩
          simp only [hst', OsState.setProc, GMap.lookup_insert_eq_iff] at hb
          split at hb
          · subst_vars; cases hb; exact absurd ((hmemT _).2 ⟨i, hi, rfl⟩) hl
          · exact ⟨b, m0, hb, hp, hi, rfl⟩
        · rintro ⟨b, m0, hb, hp, hi, rfl⟩
          refine ⟨b, m0, ?_, hp, hi, rfl⟩
          simp only [hst', OsState.setProc, GMap.lookup_insert_eq_iff]
          split
          · subst_vars; rw [hnone] at hb; cases hb
          · exact hb)
      $$ [Hσ Hcells] with ⟨Hσ, Hcells, Hout⟩
    · iframe; unfold halves; iapply BigSepM.bigSepM_empty.2; iempintro
    imod gAuth_update _ _ _ _ _ ({ m with maps := <[base := n]> m.maps }) $$ HAm Hm
      with ⟨HAm, Hm⟩
    imodintro
    iexists Γb, _, Γf, Γt
    have htr : tokRes gooseOsGS st' Γt = tokRes (gooseOsGS (L := L)) st Γt := by rw [hst']; rfl
    rw [htr]
    iframe
    isplitr
    · ipureintro
      rw [hst']
      refine ⟨hst' ▸ hwf', osCoh_setMaps hcoh _ _ ?_ ?_⟩
      · intro q; simp only [OsState.setProc, GMap.lookup_insert_eq_iff]; split
        · subst_vars; simp [Hml]
        · rfl
      · intro q m' hq
        simp only [OsState.setProc, GMap.lookup_insert_eq_iff] at hq
        split at hq
        · subst_vars; cases hq
          refine ⟨m, Hml, rfl, rfl, rfl, rfl, rfl, rfl, fun b len0 => ?_⟩
          simp only [OsState.setProc, GMap.lookup_insert_eq_iff]
          split
          · simp
          · exact hmo.maps b len0
        · rename_i hpq
          refine ⟨m', hq, rfl, rfl, rfl, rfl, rfl, rfl, fun b len0 => ?_⟩
          obtain ⟨f1, -, hmo1⟩ := hcoh.meta_some q m' hq
          rw [hmo1.maps b len0]
          simp only [OsState.setProc, GMap.lookup_insert_eq_iff]
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
    iexists f.contents
    isplitr
    · ipureintro; rw [contents_length]; exact hmo.size.symm
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
theorem wp_osMunmap (base : Loc) (len cap : w64) (p : Ino) (m : OsMeta) (n : Nat)
    (vf : Nat → val) (hE : ↑osN ⊆ E) (hb : m.maps !! base = some n) (hlen : len.toNat = n)
    (hcap : cap.toNat = n) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osMeta (L := L) p (DFrac.own 1) (m) -∗ cellsR base 0 n vf -∗
      (∀ e : w64,
        ((⌜e = 0⌝ ∗ osMeta (L := L) p (DFrac.own 1) ({ m with maps := GMap.delete base m.maps })) ∨
         (⌜e ≠ 0⌝ ∗
           (osMeta (L := L) p (DFrac.own 1) ({ m with maps := GMap.delete base m.maps }) ∨
            (osMeta (L := L) p (DFrac.own 1) (m) ∗ cellsR base 0 n vf)))) -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Munmap" (Val (PairV (#base) (PairV (#len) (#cap))))) @ s; E
        {{ Φ }} := by
  iintro #Hinv Hm Hc HΦ
  iapply wp_os_step "Munmap" _ Φ (by simp [val.isPanic]) hE (by simp [DataOp]) $$ Hinv
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
  have hbase : st.proc.maps !! base = some ⟨p, n⟩ := (hmo.maps base n).1 hb
  imodintro
  isplitr
  · ipureintro
    exact ⟨_, h, st, ⟨base, len, cap, ⟨p, n⟩, rfl, hbase, hlen, hcap,
      .inr ⟨1, by decide, rfl, .inl rfl⟩⟩, mapsFresh_same rfl, heapRendered_same hwf rfl rfl Hag⟩
  inext
  iintro %e' %h' %st' %Hst
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsFsStep] at Hst
  obtain ⟨base', len', cap', m0, hv, hm0, -, -, hres⟩ := Hst
  injection hv with h1 h2; injection h2 with h3 h4
  cases go.intoVal_inj h1
  rw [hbase] at hm0; cases hm0
  -- the state without the mapping
  have hunmap : ∀ st1 : OsState, st1 = (st.setProc { st.proc with maps := GMap.delete base st.proc.maps }) →
      OsWf st1 ∧ OsCoh st1 Γb (<[p := { m with maps := GMap.delete base m.maps }]> Γm) Γf Γt ∧
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
      · simp only [OsState.setProc, GMap.lookup_delete_iff] at h1; split at h1
        · cases h1
        · exact hwf.maps b m1 h1
      · simp only [OsState.setProc, GMap.lookup_delete_iff] at h1 h2; split at h1
        · cases h1
        · split at h2
          · cases h2
          · exact hwf.maps_disj b1 m1 b2 m2 h1 h2
    -- a cell of the mapping is mapped by no other
    have hother : ∀ k, k < n → ∀ q j, ¬ MapsTo st1 (base +ₗ (k : Int)) q j := by
      rintro k hk q j ⟨b, m1, h1, -, hj, he⟩
      rw [hst1] at h1
      simp only [OsState.setProc, GMap.lookup_delete_iff] at h1; split at h1
      · cases h1
      · rename_i hne
        have hd := hwf.maps_disj b m1 base ⟨p, n⟩ h1 hbase (fun e => hne e.symm)
        have : base.addr + k = b.addr + j := by simpa [Loc.add] using congrArg Loc.addr he
        simp at hd; omega
    refine ⟨hwf1, ?_, fun Hr Hfr => ?_⟩
    · rw [hst1]
      refine osCoh_setMaps hcoh _ _ ?_ ?_
      · intro q; simp only [OsState.setProc, GMap.lookup_insert_eq_iff]; split
        · subst_vars; simp [Hml]
        · rfl
      · intro q m' hq
        simp only [OsState.setProc, GMap.lookup_insert_eq_iff] at hq
        split at hq
        · subst_vars; cases hq
          refine ⟨m, Hml, rfl, rfl, rfl, rfl, rfl, rfl, fun b len0 => ?_⟩
          simp only [OsState.setProc, GMap.lookup_delete_iff]
          split
          · simp
          · exact hmo.maps b len0
        · rename_i hpq
          refine ⟨m', hq, rfl, rfl, rfl, rfl, rfl, rfl, fun b len0 => ?_⟩
          obtain ⟨f1, -, hmo1⟩ := hcoh.meta_some q m' hq
          rw [hmo1.maps b len0]
          simp only [OsState.setProc, GMap.lookup_delete_iff]
          split
          · subst_vars; rw [hbase]; simp only [reduceCtorEq, iff_false, Option.some.injEq]
            intro h; cases h; exact hpq rfl
          · rfl
    · iintro ⟨Hσ, Hcells, Hc⟩
      ihave Hc := (cellsR_halves base 0 vf n).1 $$ Hc
      imod cells_step st st1 h h' _ (mkCellsR base vf 0 n) ∅ hwf hwf1 Hr Hfr
        (fun b m1 h1 => by
          rw [hst1] at h1; simp only [OsState.setProc, GMap.lookup_delete_iff] at h1; split at h1
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
          apply cellView_lookup_congr hwf hwf1 (by rw [hst1]; rfl) (by rw [hst1]; rfl)
          intro q i
          constructor
          · rintro ⟨b, m1, h1, hp, hi, rfl⟩
            rw [hst1] at h1; simp only [OsState.setProc, GMap.lookup_delete_iff] at h1; split at h1
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
  have hdone : ∀ e : w64, ∀ st1 : OsState, st1 = (st.setProc { st.proc with maps := GMap.delete base st.proc.maps }) →
      HeapRendered st st1 h h' → MapsFresh st st1 h →
      (gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γb Γb ∗
        gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γm Γm ∗
        gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γf Γf ∗
        gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γt Γt ∗ tokRes (gooseOsGS (L := L)) st Γt ∗
        cellsRes (cellView st) ∗ naHeapCtx tls h ∗
        gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γm p (DFrac.own 1) (m) ∗
        cellsR base 0 n vf ∗
        (gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γm p (DFrac.own 1)
          ({ m with maps := GMap.delete base m.maps }) -∗ Φ (#e)) ⊢
      |==> ∃ Γb' Γm' Γf' Γt', osWorld (L := L) st1 Γb' Γm' Γf' Γt' h' ∗
        WP (Val (#e)) @ s; E {{ Φ }}) := by
    intro e st1 hst1 Hr Hfr
    obtain ⟨hwf1, hcoh1, hheap⟩ := hunmap st1 hst1
    iintro ⟨HAb, HAm, HAf, HAt, Htok, Hcells, Hσ, Hm, Hc, HΦe⟩
    imod gAuth_update _ _ _ _ _ ({ m with maps := GMap.delete base m.maps }) $$ HAm Hm
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


/-- A mapped cell the client holds part of shows the byte it maps, while the client holds a
fraction of that byte: a load through the mapping reads the page cache. -/
theorem osCell_agree (e : Expr) (htv : toVal e = none) (p : Ino) (dqm : DFrac) (m : OsMeta)
    (base : Loc) (len i : Nat) (hb : m.maps !! base = some len) (hi : i < len) (dqb : DFrac)
    (x : w8 × Bool) (dqc : DFrac) (v : val) (hE : ↑osN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osMeta (L := L) p dqm (m) -∗ osByte (L := L) p i dqb x -∗
      heapPointsto (base +ₗ (i : Int)) dqc v -∗
      (⌜v = LitV (LitByte x.1)⌝ -∗ osMeta (L := L) p dqm (m) -∗ osByte (L := L) p i dqb x -∗
        heapPointsto (base +ₗ (i : Int)) dqc v -∗ WP e @ s; E {{ Φ }}) -∗
      WP e @ s; E {{ Φ }} := by
  iintro #Hinv Hm Hb Hc HΦ
  iapply wp_ext_acc (X := fsExt) e Φ htv
  iintro %σ %g Hl Hg
  icases (os_local_ctx_eq σ).mp $$ Hl with Hl
  unfold osCtx osCtxF
  icases Hl with ⟨⟨%Γb, %Γm, %Γf, %Γt, %Hwc, HAb, HAm, HAf, HAt, Htok, Hv⟩, Hns⟩
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
  · inext; iexists (cellView σ), (GMap.size σ.proc.inflight); iframe
  imodintro
  isplitl [HAb HAm HAf HAt Htok Hv Hns]
  · iapply (os_local_ctx_eq σ).mpr
    unfold osCtx osCtxF
    iframe Hns
    iexists Γb, Γm, Γf, Γt
    iframe
    ipureintro; exact ⟨hwf, hcoh⟩
  iframe Hg
  iapply HΦ $$ %Hvv.2.symm Hm Hb Hc

end specs

end Fs
end Perennial

end

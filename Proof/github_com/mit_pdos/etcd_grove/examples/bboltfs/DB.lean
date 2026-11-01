/-
minibolt's open `DB` (`examples/bboltfs/minibolt.go`): its representation predicate and the
resources of its three locks, as in bbolt.

## State

The ghost names (`DBNames`) name:
- `cur`, a ghost variable holding `(mp, failed, hwm)`: the bytes of the two meta pages, `failed`,
  and the committed high water mark (in pages). While not failed, `hwm` is the current meta's
  `pgid` (`curMeta mp`, `pickMeta`'s choice). Split 1/2 `metalock`, 1/4 `rwlock`, 1/4 the mapping's
  invariant: changing it takes the writer holding both mutexes and opening the invariant.
- `map`, a ghost variable holding `(base, len, γm)`: the mapping and the name of its invariant's
  token. 1/2 `rwlock`, 1/2 `mmaplock`'s resource (`q/2` of it at fraction `q`).
- `out`: the meta pages' meta cells are out of the mapping's invariant (with the writer, during
  the meta `WriteAt`). 1/2 the invariant, 1/4 each mutex.
- `txs`, a ghost map from txids to values (`dbTx γ t vo`, persistent: transaction `t`'s root page
  holds `vo`, `pageVal`, and the client's predicate `vp` allows it), `last` (a monotone counter: the current txid, `dbLast γ t` its lower
  bounds), `fail` (a monotone counter, 1 once failed, `dbFailed γ`), and `own` (the committer's
  token `dbOwner γ t n`: the current txid and high water mark; the other half in `metalock`,
  where it agrees with the meta pages while not failed; once closed, the committer's half is in
  `rwlock`, so that neither `Commit` nor `Close` can follow).
- `cls`, a ghost variable: the database is closed. 1/2 `rwlock`, 1/2 `metalock` (with its half of
  the meta pages' bytes while open: `Close` takes them, for its caller to reopen the file).

A committed page `r` (`2 ≤ r < hwm`) is never written again: its bytes are clean (synced) and its
`osBytes` discarded (`pageIs`, persistent), and the client halves of its mapped cells live in the
mapping's invariant, holding those bytes. A reader loads a committed byte by opening the invariant
around the load: no `OsMeta` is needed (the writer proved the cells' values with `osCell_agree`
when it mapped the file, and no write touches them since).

## The locks (as in bbolt)
- `rwlock` (`rwR`): the writer's. The whole `OsMeta` (`Truncate`, `Sync`, `Fdatasync`, `Mmap`,
  `Munmap` all take it; no sync failed while not failed, `m.ok`, so that a sync makes bytes
  clean), the bytes from `hwm` on and half the meta pages' bytes (clean while not failed), the client
  halves of the mapped cells it may write (the meta pages' header and tail, and the pages from
  `hwm` on), `filesz` (the file's size while not failed: a failed `Truncate` may grow the file; at least four
  pages and at most 1 GiB, as the mapping, whose `mmapSize` is a power of two),
  `datasz`, halves of the mapping fields, and half the file and its fd.
- `metalock` (`metaR`): `failed`, half the meta pages' bytes until closed (a meta `WriteAt` takes
  both halves: it runs under both mutexes), the transaction map (no transaction after the current
  one while not failed), and while not failed: the meta
  pages are valid (`metaPagesOk`), the current meta's root page `pageIs` its value, `dbTx` of it;
  once failed, its half of `own`, at high water mark 0 (failing the handle sets the token to
  `(t, 0)`, so that a client whose token has a positive high water mark knows the handle is not
  failed).
- `mmaplock` (`mapR γ db q`, Perennial's guarded `RWMutex`): the mapping, fractionally: the
  mapping fields, a fraction `q` of the mapping invariant's token (`ghostVar γm q ()`: a remap,
  with `q = 1`, closes the invariant and takes every cell back for `Munmap`), and fractions of the
  file and its fd for `Snapshot`'s `ReadAt`.

The mapping's invariant (`mapInv`, a closable invariant over `mapCells`) holds the committed
pages' cells and, unless `out`, the meta cells, holding the metas while not failed.

The mapping has a state (`MapSt`): mapped, or unmapped (before the first `mmap`, after a failed
remap, once closed). Unmapped, `mmaplock` guards only the nil fields (a reader that finds
`meta0` nil refuses, `issues/bbolt-failed-remap-nil-meta-panic.md`), and the writer holds the
whole file and fd and the invariant's quarter of `cur` (`writerExtra`); `rwlock`'s resource then
records the failure (`dbFailed`). Once closed, `rwlock`'s resource is the committer's half of
`own` (so that no `Commit` can follow) and halves of the mapping fields. The mapping's invariant
is closed with the whole of its token: `mmaplock`'s resource has `q/2` of it, the writer the
other half (`MapInv.lean`).

`pkgFacts` stands for the package's `isPkgInit` (`sync`'s, and the error values), until the
packages minibolt imports (`os`, `syscall`, `golang.org/x/sys/unix`) have `IsPkgInit` instances.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.bboltfs.MapCells
public import Proof.os.Base
public import Perennial.Proof.sync.RWMutexGuard
public import Perennial.Proof.sync.RWMutexThreads
public import Perennial.Ghost.GhostVar
public import Perennial.Ghost.GhostMap
public import Perennial.Ghost.MonoNat
public import Perennial.IrisLib.BI

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace github_com.mit_pdos.etcd_grove.examples.bboltfs

section pure
variable [GooseExts]

/-- The meta `pickMeta` picks from the meta pages' bytes `mp`. -/
def curMeta (mp : List w8) : Meta :=
  let m0 := fileMeta mp 0
  let m1 := fileMeta mp 1
  if uint.Z m0.txid' < uint.Z m1.txid' then (if metaValid m1 then m1 else m0)
  else (if metaValid m0 then m0 else m1)

/-- The current meta's root page. -/
def curRoot (mp : List w8) : Nat := (curMeta mp).root'.root'.toNat

/-- The current meta's high water mark. -/
def curPgid (mp : List w8) : Nat := (curMeta mp).pgid'.toNat

/-- The meta pages of an open database: a valid meta, whose root page is committed (past the
meta, freelist pages... from page 2) below its high water mark, small enough to map below 1 GiB (minibolt's `mmapSize` bound;
`ReadAt` of the file up to the high water mark is then at most 1 GiB). -/
def metaPagesOk (mp : List w8) : Prop :=
  mp.length = 8192 ∧ (metaValid (fileMeta mp 0) ∨ metaValid (fileMeta mp 1)) ∧
    2 ≤ curRoot mp ∧ curRoot mp < curPgid mp ∧ (curPgid mp + 1) * 4096 ≤ 2 ^ 30

/-- What a root page holds: a value if its `count` is 1 (`Get`'s `has`). -/
def pageVal (B : List w8) : Option w64 :=
  if (pageHdrOf B).count' = W16 1 then some (decode ((B.drop 16).take 8)) else none

/-- A file `Open` accepts (crash-free, as after a crash: all of it clean): shorter than four
pages (`init` lays it out), or with no valid meta (`init` again), or an open database's meta pages
whose high water mark is inside the file. -/
def fileOk (xs : List (w8 × Bool)) : Prop :=
  xs.length < 4 * 4096 ∨
    ((∀ x ∈ xs, x.2 = true) ∧
      let mp := (xs.map Prod.fst).take 8192
      ((¬ metaValid (fileMeta mp 0) ∧ ¬ metaValid (fileMeta mp 1)) ∨
       (metaPagesOk mp ∧ 4096 * curPgid mp ≤ xs.length)))

end pure

/-- The ghost names of an open database (see the file header). -/
structure DBNames where
  cur : GName
  map : GName
  out : GName
  txs : GName
  last : GName
  fail : GName
  own : GName
  cls : GName
  /-- What the client allows transaction `t` to hold (`dbTx`): `Open` takes it, holding of the
  transaction it opens at, and `Commit` requires it of the value it commits. -/
  vp : Nat → Option w64 → Prop

section preds
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]

/-- Committed page `r` of the file `p` holds `B`, clean (synced), forever. -/
def pageIs (p : GoString) (r : Nat) (B : List w8) : IProp GF :=
  iprop(⌜B.length = 4096⌝ ∗ osBytes (GF := GF) p (4096 * r) DFrac.discard (B.map (·, true)))

instance osBytes_discard_persistent (p : GoString) (off : Nat) (xs : List (w8 × Bool)) :
    Persistent (osBytes (GF := GF) p off DFrac.discard xs) := by
  unfold osBytes bytesG
  refine BigSepL.bigSepL_persistent ?_
  intro k x _
  unfold gElem; infer_instance

instance pageIs_persistent (p : GoString) (r : Nat) (B : List w8) :
    Persistent (pageIs (GF := GF) p r B) := by
  unfold pageIs; infer_instance

/-- Transaction `t`'s root page holds `vo`, which the client allows (`γ.vp`). -/
def dbTx (γ : DBNames) (t : Nat) (vo : Option w64) : IProp GF :=
  iprop(ghostMapElem γ.txs t DFrac.discard vo ∗ ⌜γ.vp t vo⌝)

/-- The current txid is at least `t`. -/
def dbLast (γ : DBNames) (t : Nat) : IProp GF := monoNatLbOwn γ.last t

/-- A commit failed: the handle refuses every later transaction. -/
def dbFailed (γ : DBNames) : IProp GF := monoNatLbOwn γ.fail 1

instance dbTx_persistent (γ : DBNames) (t : Nat) (vo : Option w64) :
    Persistent (dbTx (GF := GF) γ t vo) := by
  unfold dbTx; infer_instance

instance dbLast_persistent (γ : DBNames) (t : Nat) : Persistent (dbLast (GF := GF) γ t) := by
  unfold dbLast; infer_instance

instance dbFailed_persistent (γ : DBNames) : Persistent (dbFailed (GF := GF) γ) := by
  unfold dbFailed; infer_instance

/-- The committer's token: the current txid is `t` and the high water mark `n`. -/
def dbOwner (γ : DBNames) (t n : Nat) : IProp GF := ghostVar γ.own (1 : Qp).half (t, n)

/-- The committer's token, if the caller holds it (`some (t, n)`): a reader that holds it learns
that it reads transaction `t`. -/
def dbOwnerOpt (γ : DBNames) : Option (Nat × Nat) → IProp GF
  | none => emp
  | some (t, n) => dbOwner γ t n

/-- A caller's committer token agrees with `metalock`'s half of it. -/
theorem dbOwnerOpt_agree (γ : DBNames) (o : Option (Nat × Nat)) (t n : Nat) :
    dbOwnerOpt (GF := GF) γ o ∗ ghostVar γ.own (1 : Qp).half (t, n) ⊢
      (dbOwnerOpt (GF := GF) γ o ∗ ghostVar γ.own (1 : Qp).half (t, n)) ∗
        ⌜∀ x, o = some x → t = x.1⌝ := by
  rcases o with _ | ⟨t', n'⟩
  · iintro ⟨H1, H2⟩; iframe; ipureintro; intro x hx; cases hx
  · iintro ⟨H1, H2⟩
    unfold dbOwnerOpt dbOwner
    icombine H1 H2 gives % ⟨_, Heq⟩
    iframe
    ipureintro; intro x hx; cases hx; cases Heq; rfl

/-- The mapping invariant's contents: the committed pages' cells, and the meta cells unless the
writer took them (`out`), holding the metas while not failed. -/
def mapCells (γ : DBNames) (p : GoString) (base : Loc) (len : Nat) : IProp GF :=
  iprop(∃ (mp : List w8) (fl : Bool) (hwm : Nat),
    ghostVar γ.cur (1 : Qp).half.half (mp, fl, hwm) ∗ ⌜4096 * hwm ≤ len⌝ ∗
    ([∗list] r ∈ List.range' 2 (hwm - 2),
      ∃ B, pageIs (GF := GF) p r B ∗ cellsB (GF := GF) base (4096 * r) B) ∗
    (ghostVar γ.out (1 : Qp).half true ∨
      (ghostVar γ.out (1 : Qp).half false ∗ ∃ mc : List w8,
        cellsB (GF := GF) base 16 (mc.take 64) ∗ cellsB (GF := GF) base 4112 (mc.drop 64) ∗
        ⌜mc.length = 128 ∧ (fl = false →
          mc = (mp.drop 16).take 64 ++ (mp.drop 4112).take 64)⌝)))

/-- A group of cells (the bytes `B` from `l`, the client halves), lent to readers by fractions:
unlent (`none`), with the whole of the group's loan token `k ↪[γl] B`; or lent (`some d`), with
the readers' deposits `d` of the mapping's token `γm`, and of the cells and of the loan token what
the readers did not take: a reader that deposits `s` takes `s/4` of both, so the invariant keeps
`e` with `e + d/4 = 1/2`. The loan token proves to a returning reader that its loan is still
counted (`lent_return`); the deposits, that the whole of `γm` finds the group unlent. -/
def lentCells (γm γl : GName) (k : Nat) (l : Loc) (B : List w8) : IProp GF :=
  iprop(∃ o : Option Qp, match o with
    | none => k ↪[γl] B ∗ bytesPointsto (GF := GF) l (DFrac.own (1 : Qp).half) B
    | some d => ∃ e : Qp, ⌜e + d.half.half = (1 : Qp).half⌝ ∗ ghostVar γm d () ∗
        k ↪[γl]{#((1 : Qp).half + e)} B ∗ bytesPointsto (GF := GF) l (DFrac.own e) B)

/-- The client halves of the meta cells holding `mc` (the two metas), at fraction `dq`. -/
def metaBytes (base : Loc) (dq : DFrac) (mc : List w8) : IProp GF :=
  iprop(bytesPointsto (GF := GF) (base +ₗ (16 : Int)) dq (mc.take 64) ∗
    bytesPointsto (GF := GF) (base +ₗ (4112 : Int)) dq (mc.drop 64))

/-- A meta reader's deposit of `γm`: an eighth of `mmaplock`'s reader fraction (whose `γm` share
is a half of it). -/
def metaDep : Qp := sync.rfrac.half.half.half

/-- The meta cells holding `mc`: unlent, or lent whole to the one reader holding `metalock`, which
deposits `metaR`'s quarter of `out` (so that the writer, with both mutexes' quarters, finds them
unlent when it takes them out), half of `metaR`'s authority over the transactions (so that the next
holder of `metalock`, with the whole of it, finds them unlent) and `metaDep` of `γm` (so that the
whole of `γm` does), and holds half of the loan token. -/
def metaLent (γ : DBNames) (γm γl : GName) (base : Loc) (mc : List w8) : IProp GF :=
  iprop((0 ↪[γl] mc ∗ metaBytes (GF := GF) base (DFrac.own (1 : Qp).half) mc) ∨
    (ghostVar γ.out (1 : Qp).half.half false ∗
      (∃ T : GMap Nat (Option w64), ghostMapAuth γ.txs (1 : Qp).half T) ∗ ghostVar γm metaDep () ∗
      0 ↪[γl]{#(1 : Qp).half} mc))

/-- The mapping invariant's contents, as `mapCells` but with each group of cells lendable
(`lentCells`, `metaLent`), and the authority `K` over the loan tokens: key 0 for the metas,
`r` for committed page `r`. -/
def mapLend (γ : DBNames) (p : GoString) (base : Loc) (len : Nat) (γm γl : GName) : IProp GF :=
  iprop(∃ (mp : List w8) (fl : Bool) (hwm : Nat) (K : GMap Nat (List w8)),
    ghostVar γ.cur (1 : Qp).half.half (mp, fl, hwm) ∗ ⌜4096 * hwm ≤ len⌝ ∗
    ghostMapAuth γl 1 K ∗ ⌜∀ k, 0 < k → hwm ≤ k → K.lookup k = none⌝ ∗
    ([∗list] r ∈ List.range' 2 (hwm - 2),
      ∃ B, pageIs (GF := GF) p r B ∗ lentCells (GF := GF) γm γl r (base +ₗ ((4096 * r : Nat) : Int)) B) ∗
    ((ghostVar γ.out (1 : Qp).half true ∗ ∃ mc : List w8, 0 ↪[γl] mc) ∨
      (ghostVar γ.out (1 : Qp).half false ∗ ∃ mc : List w8,
        ⌜mc.length = 128 ∧ (fl = false → mc = (mp.drop 16).take 64 ++ (mp.drop 4112).take 64)⌝ ∗
        metaLent (GF := GF) γ γm γl base mc)))

/-- The namespace of a mapping's invariant. -/
def mapN : Namespace := nroot .@ "minibolt_map"

/-- The invariant of the mapping at `base`, closable with the whole of `γm`'s token (and then
holding `mapCells`, `mapInv_close`), with its loan tokens at `γl`; its length is an `int`. -/
def mapInv (γ : DBNames) (p : GoString) (base : Loc) (len : Nat) (γm : GName) : IProp GF :=
  iprop(⌜len < 2 ^ 63⌝ ∗ ∃ γl, inv mapN iprop(mapLend (GF := GF) γ p base len γm γl ∨ ghostVar γm 1 ()))

/-- The state of the mapping: `some (base, len, γm)`, the mapping at `base` of length `len`,
whose invariant is closable with `γm`'s token; `none`, no mapping (before the first one, after a
failed remap, once closed). -/
abbrev MapSt := Option (Loc × Nat × GName)

/-- `db.datasz` in the state `st`. -/
def mapLen : MapSt → Nat
  | some (_, len, _) => len
  | none => 0

/-- The mapping fields of `db` in the state `st`. -/
def mapFields (db : Loc) (dq : DFrac) : MapSt → IProp GF
  | some (base, len, _) => iprop(
      db.[DB, go!"dataref"] ↦{dq} (⟨base, W64 len, W64 len⟩ : GoSlice) ∗
      db.[DB, go!"meta0"] ↦{dq} (base +ₗ 16) ∗ db.[DB, go!"meta1"] ↦{dq} (base +ₗ 4112))
  | none => iprop(db.[DB, go!"dataref"] ↦{dq} slice.nil ∗
      db.[DB, go!"meta0"] ↦{dq} null ∗ db.[DB, go!"meta1"] ↦{dq} null)

/-- What `mmaplock` guards besides the fields at fraction `q`, in the state `st`: with a mapping,
the fraction `q/2` of its invariant's token (the writer holds the other half), the invariant, and
the fraction `q/2` of the file and its fd for `Snapshot`'s `ReadAt` (the writer holds the other
half, and all of it while there is no mapping). -/
def mapRest (γ : DBNames) (f : Loc) (fd : w64) (p : GoString) (q : Qp) : MapSt → IProp GF
  | some (base, len, γm) => iprop(⌜0 < base.addr⌝ ∗ ghostVar γm q.half () ∗ mapInv (GF := GF) γ p base len γm ∗
      os.ownFile (GF := GF) f fd p (DFrac.own q.half) ∗
      osFd (GF := GF) fd (DFrac.own q.half) ⟨p, true, true⟩)
  | none => emp

instance mapInv_persistent (γ : DBNames) (p : GoString) (base : Loc) (len : Nat) (γm : GName) :
    Persistent (mapInv (GF := GF) γ p base len γm) := by
  unfold mapInv; infer_instance

/-- `mmaplock`'s resource at fraction `q` in the state `st`. -/
def mapBody (γ : DBNames) (db f : Loc) (fd : w64) (p : GoString) (st : MapSt) (q : Qp) :
    IProp GF :=
  iprop(ghostVar γ.map q.half st ∗ mapFields (GF := GF) db (DFrac.own q.half) st ∗
    mapRest (GF := GF) γ f fd p q st)

/-- `mmaplock`'s resource at fraction `q` (see the file header). -/
def mapR (γ : DBNames) (db f : Loc) (fd : w64) (p : GoString) (q : Qp) : IProp GF :=
  iprop(∃ st, mapBody (GF := GF) γ db f fd p st q)

theorem fractional_half_of {Φ : Qp → IProp GF} (h : Fractional Φ) :
    Fractional (fun q : Qp => Φ q.half) where
  fractional p q := by rw [Qp_half_add]; exact h.fractional p.half q.half

theorem typedPointsto_frac {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (l : Loc) (v : V) :
    Fractional (fun q : Qp => typedPointsto (GF := GF) l v (DFrac.own q)) :=
  fractional_of_dfractional (fun dq => typedPointsto l v dq)

theorem ownFile_fractional (f : Loc) (fd : w64) (p : GoString) :
    Fractional (fun q : Qp => os.ownFile (GF := GF) f fd p (DFrac.own q)) where
  fractional q1 q2 := by
    refine ⟨?_, ?_⟩
    · iintro H
      unfold os.ownFile
      icases H with ⟨%inner, #Hf, Hfd, #Hn⟩
      icases ((typedPointsto_frac (GF := GF) (structFieldRef os.file go!"fd" inner) fd).fractional
        q1 q2).1 $$ Hfd with ⟨H1, H2⟩
      isplitl [H1]
      · iexists inner; iframe; iframe #
      · iexists inner; iframe; iframe #
    · iintro ⟨H1, H2⟩
      unfold os.ownFile
      icases H1 with ⟨%inner, #Hf, Hfd1, #Hn⟩
      icases H2 with ⟨%inner2, #Hf2, Hfd2, #Hn2⟩
      icombine Hf Hf2 gives %Heq
      cases Heq
      iexists inner
      iframe #
      iapply ((typedPointsto_frac (GF := GF) (structFieldRef os.file go!"fd" inner) fd).fractional
        q1 q2).2
      iframe

theorem osFd_fractional (fd : w64) (d : OsFd) :
    Fractional (fun q : Qp => osFd (GF := GF) fd (DFrac.own q) d) where
  fractional q1 q2 := by unfold osFd; exact gElem_split _ _ _ _ _ _

theorem mapBody_fractional (γ : DBNames) (db f : Loc) (fd : w64) (p : GoString) (st : MapSt) :
    Fractional (mapBody (GF := GF) γ db f fd p st) := by
  unfold mapBody
  haveI := ghostVar_half_fractional (GF := GF) γ.map st
  haveI : ∀ (l : Loc) (v : GoSlice), Fractional (fun q : Qp => typedPointsto (GF := GF) l v (DFrac.own q.half)) :=
    fun l v => fractional_half_of (typedPointsto_frac l v)
  haveI : ∀ (l : Loc) (v : Loc), Fractional (fun q : Qp => typedPointsto (GF := GF) l v (DFrac.own q.half)) :=
    fun l v => fractional_half_of (typedPointsto_frac l v)
  rcases st with _ | ⟨base, len, γm⟩
  · dsimp only [mapFields, mapRest]; infer_instance
  · dsimp only [mapFields, mapRest]
    haveI := ghostVar_half_fractional (GF := GF) γm ()
    haveI : Fractional (fun q : Qp => os.ownFile (GF := GF) f fd p (DFrac.own q.half)) :=
      fractional_half_of (ownFile_fractional (GF := GF) f fd p)
    haveI : Fractional (fun q : Qp => osFd (GF := GF) fd (DFrac.own q.half) ⟨p, true, true⟩) :=
      fractional_half_of (osFd_fractional (GF := GF) fd ⟨p, true, true⟩)
    haveI : Persistent (mapInv (GF := GF) γ p base len γm) := by unfold mapInv; infer_instance
    infer_instance

instance mapR_fractional (γ : DBNames) (db f : Loc) (fd : w64) (p : GoString) :
    Fractional (mapR (GF := GF) γ db f fd p) := by
  unfold mapR
  exact fractional_exists_agree (fun st q => mapBody (GF := GF) γ db f fd p st q)
    (mapBody_fractional γ db f fd p) (fun x y q1 q2 => by
      unfold mapBody
      iintro ⟨⟨H1, -⟩, ⟨H2, -⟩⟩
      icombine H1 H2 gives % ⟨_, Heq⟩
      ipureintro; exact Heq)

/-- What minibolt's code needs of the initialized program: `sync`'s initialization, and the
package's error values, which are not nil, and `io.EOF`, which is not nil, not a `*PathError`, and
a pointer error (a `*T`, as `errors.New`'s `*errorString`): `Snapshot` compares `ReadAt`'s error with
it, which takes its dynamic type to be comparable. (The package's `isPkgInit` would give them, once
`os`, `syscall` and `golang.org/x/sys/unix`, which it imports, have `IsPkgInit` instances.) -/
def pkgFacts : IProp GF :=
  iprop(isPkgInit (PROP := IProp GF) pkg_id.sync ∗ ∃ (e1 e2 : GoInterface),
    globalAddr errFailed ↦□ e1 ∗ globalAddr errPageSize ↦□ e2 ∗
    ⌜e1 ≠ interface.nil ∧ e2 ≠ interface.nil⌝ ∗
    ∃ eof : GoInterface, globalAddr _root_.Perennial.io.EOF ↦□ eof ∗
      ⌜eof ≠ interface.nil ∧
        (∀ pe : Loc, eof ≠ interface.mkOk (go.GoType.PointerType _root_.Perennial.io.fs.PathError.ty) #pe) ∧
        ∃ (T : go.GoType) (l : Loc), eof = interface.mkOk (go.GoType.PointerType T) #l⌝)

instance pkgFacts_persistent : Persistent (pkgFacts (GF := GF)) := by
  unfold pkgFacts; infer_instance

/-- `metalock`'s resource (see the file header). -/
def metaR (γ : DBNames) (db : Loc) (p : GoString) : IProp GF :=
  iprop(∃ (b : Bool) (mp mx : List (w8)) (hwm : Nat) (mxc : List (w8 × Bool))
      (T : GMap Nat (Option w64)),
    db.[DB, go!"failed"] ↦ b ∗ ghostVar γ.cur (1 : Qp).half (mp, b, hwm) ∗
    ((osBytes (GF := GF) p 0 (DFrac.own (1 : Qp).half) mxc ∗ ghostVar γ.cls (1 : Qp).half false) ∨
      ghostVar γ.cls (1 : Qp).half true) ∗ ⌜mxc.length = 8192 ∧ mxc.map Prod.fst = mx⌝ ∗
    ghostMapAuth γ.txs 1 T ∗ ghostVar γ.out (1 : Qp).half.half false ∗
    match b with
    | true => monoNatAuthOwn γ.fail 1 1 ∗ ∃ t : Nat, ghostVar γ.own (1 : Qp).half (t, 0)
    | false =>
      monoNatAuthOwn γ.fail 1 0 ∗ ⌜mx = mp ∧ metaPagesOk mp ∧ hwm = curPgid mp ∧
        ∀ k, (curMeta mp).txid'.toNat < k → T !! k = none⌝ ∗
      monoNatAuthOwn γ.last 1 (curMeta mp).txid'.toNat ∗
      ghostVar γ.own (1 : Qp).half ((curMeta mp).txid'.toNat, hwm) ∗
      ∃ B, pageIs (GF := GF) p (curRoot mp) B ∗ dbTx γ (curMeta mp).txid'.toNat (pageVal B) ∗
        ⌜T !! (curMeta mp).txid'.toNat = some (pageVal B)⌝)

/-- The client halves of the mapped cells at `base` the writer holds: the meta pages' headers
and tails (all but their metas), and the pages from the high water mark `hwm` on. -/
def writerCells (base : Loc) (hwm len : Nat) : IProp GF :=
  iprop((∃ vf, cellsR (GF := GF) base 0 16 vf) ∗ (∃ vf, cellsR (GF := GF) base 80 4016 vf) ∗
    (∃ vf, cellsR (GF := GF) base 4096 16 vf) ∗ (∃ vf, cellsR (GF := GF) base 4176 4016 vf) ∗
    (∃ vf, cellsR (GF := GF) base (4096 * hwm) (len - 4096 * hwm) vf))

/-- The writer's part of the file, with the mapping in the state `st` (see `rwR`). -/
def writerFile (γ : DBNames) (db f : Loc) (fd : w64) (p : GoString) (mp : List w8) (fl : Bool)
    (hwm : Nat) (st : MapSt) (m : OsMeta) : IProp GF :=
  iprop(∃ (mxc tail : List (w8 × Bool)) (fsz : Nat),
    db.[DB, go!"filesz"] ↦ W64 fsz ∗ db.[DB, go!"datasz"] ↦ W64 (mapLen st) ∗
    os.ownFile (GF := GF) f fd p (DFrac.own (1 : Qp).half) ∗
    osFd (GF := GF) fd (DFrac.own (1 : Qp).half) ⟨p, true, true⟩ ∗
    osMeta (GF := GF) p (DFrac.own 1) (some m) ∗
    osBytes (GF := GF) p 0 (DFrac.own (1 : Qp).half) mxc ∗
    osBytes (GF := GF) p (4096 * hwm) (DFrac.own 1) tail ∗
    ⌜2 ≤ hwm ∧ 4096 * hwm ≤ m.size ∧ mxc.length = 8192 ∧ tail.length = m.size - 4096 * hwm ∧
      (fl = false → mxc.map Prod.fst = mp ∧ (∀ x ∈ mxc, x.2 = true) ∧ fsz = m.size ∧
        0 ≤ fd.toInt ∧ 4 * 4096 ≤ m.size ∧ m.size ≤ 2 ^ 30 ∧ mapLen st ≤ 2 ^ 30)⌝)

/-- What the writer holds besides `writerFile` while there is no mapping: the invariant's quarter
of `cur`, and `mmaplock`'s halves of the file and its fd. -/
def writerExtra (γ : DBNames) (f : Loc) (fd : w64) (p : GoString) (mp : List w8) (fl : Bool)
    (hwm : Nat) : IProp GF :=
  iprop(ghostVar γ.cur (1 : Qp).half.half (mp, fl, hwm) ∗
    os.ownFile (GF := GF) f fd p (DFrac.own (1 : Qp).half) ∗
    osFd (GF := GF) fd (DFrac.own (1 : Qp).half) ⟨p, true, true⟩)

/-- `rwlock`'s resource (see the file header): the writer's part of an open database, with a
mapping or, after a failed remap, without one (and the handle failed); or, once closed, the
committer's half of `own` and halves of the mapping fields. -/
def rwR (γ : DBNames) (db f : Loc) (fd : w64) (p : GoString) : IProp GF :=
  iprop((∃ (mp : List w8) (fl : Bool) (hwm : Nat) (st : MapSt) (m : OsMeta),
    ghostVar γ.cur (1 : Qp).half.half (mp, fl, hwm) ∗ ghostVar γ.map (1 : Qp).half st ∗
    ghostVar γ.out (1 : Qp).half.half false ∗ mapFields (GF := GF) db (DFrac.own (1 : Qp).half) st ∗
    writerFile (GF := GF) γ db f fd p mp fl hwm st m ∗ ghostVar γ.cls (1 : Qp).half false ∗
    ⌜fl = false → m.ok = true⌝ ∗
    match st with
    | some (base, len, γm) =>
      ⌜m.maps = {[base := len]} ∧ m.size ≤ len ∧ 0 < base.addr ∧ len ≤ 2 ^ 41⌝ ∗
      ghostVar γm (1 : Qp).half () ∗ mapInv (GF := GF) γ p base len γm ∗
      writerCells (GF := GF) base hwm len
    | none => dbFailed (GF := GF) γ ∗ writerExtra (GF := GF) γ f fd p mp fl hwm) ∨
   ((∃ x : Nat × Nat, ghostVar γ.own (1 : Qp).half x) ∗ ghostVar γ.cls (1 : Qp).half true ∗
     ∃ st, ghostVar γ.map (1 : Qp).half st ∗ mapFields (GF := GF) db (DFrac.own (1 : Qp).half) st))

/-- A reader slot of an open database (one of `mmaplock`'s reader tokens), on the path of `isDB`
(`db.path`). Readers do not hold one: `isDB`'s pool lends one to a thread token for each read
transaction (`dbReader_borrow`, `dbReader_giveBack`). -/
def dbReader (γ : DBNames) (db : Loc) : IProp GF :=
  iprop(∃ (f : Loc) (fd : w64) (p : GoString), db.[DB, go!"file"] ↦□ f ∗ db.[DB, go!"path"] ↦□ p ∗
    sync.ownRWMutex db.[DB, go!"mmaplock"] (mapR (GF := GF) γ db f fd p))

/-- The namespace of an open database's pool of reader slots. -/
def dbPoolN : Namespace := nroot .@ "minibolt_readers"

/-- The persistent part of an open database: the file, its path, the three locks with
their resources, and the pool of `mmaplock`'s reader slots (`threadPool`), from which a thread
token borrows one for a read transaction. -/
def isDB (γ : DBNames) (db : Loc) : IProp GF :=
  iprop((∃ (f : Loc) (fd : w64) (p : GoString),
    pkgFacts (GF := GF) ∗ osInv (GF := GF) ∗ db.[DB, go!"file"] ↦□ f ∗ db.[DB, go!"path"] ↦□ p ∗
    sync.isMutex db.[DB, go!"rwlock"] (rwR (GF := GF) γ db f fd p) ∗
    sync.isMutex db.[DB, go!"metalock"] (metaR (GF := GF) γ db p) ∗
    sync.isRWMutexGuard db.[DB, go!"mmaplock"] (mapR (GF := GF) γ db f fd p)) ∗
    ∃ γp : GName, threadPool.isThreadPool dbPoolN γp (dbReader (GF := GF) γ db))

instance isDB_persistent (γ : DBNames) (db : Loc) : Persistent (isDB (GF := GF) γ db) := by
  unfold isDB; infer_instance

/-- A reader slot lent out by an open database's pool (`dbReader_borrow`). -/
def dbLoan (γ : DBNames) (db : Loc) : IProp GF :=
  iprop(∃ γp : GName, threadPool.isThreadPool dbPoolN γp (dbReader (GF := GF) γ db) ∗
    threadPool.ownThreadLoan γp)

/-- Borrow a reader slot of an open database with a thread token. -/
theorem dbReader_borrow (γ : DBNames) (db : Loc) :
    isDB (GF := GF) γ db ∗ threadTok ⊢ |={⊤}=> ▷ dbReader (GF := GF) γ db ∗ dbLoan (GF := GF) γ db := by
  iintro ⟨Hdb, Htok⟩
  iunfold isDB at Hdb
  icases Hdb with ⟨-, %γp, #Hpool⟩
  imod threadPool.borrow dbPoolN γp (dbReader (GF := GF) γ db) ⊤ (fun _ _ => CoPset.mem_full)
    $$ [Hpool Htok] with ⟨Hrd, Hloan⟩
  · iframe; iframe #
  imodintro
  iframe Hrd
  unfold dbLoan
  iexists γp
  iframe; iframe #

/-- Give a borrowed reader slot back, for the thread token. -/
theorem dbReader_giveBack (γ : DBNames) (db : Loc) :
    dbLoan (GF := GF) γ db ∗ dbReader (GF := GF) γ db ⊢ |={⊤}=> threadTok := by
  iintro ⟨Hl, Hrd⟩
  iunfold dbLoan at Hl
  icases Hl with ⟨%γp, #Hpool, Hloan⟩
  iapply threadPool.giveBack dbPoolN γp (dbReader (GF := GF) γ db) ⊤ (fun _ _ => CoPset.mem_full)
  iframe; iframe #

end preds

end github_com.mit_pdos.etcd_grove.examples.bboltfs

end Perennial

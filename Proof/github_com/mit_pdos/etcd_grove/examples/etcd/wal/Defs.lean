/-
Lean-first (no Rocq counterpart).

# The WAL robustness tester's model and crash invariant (WAL W4c step 2; plan §2)

The tester (`examples/etcd/wal`) keeps its reference state, the oracle (`oracle.go`), in a durable
file beside the WAL; its pure vocabulary (`ref.go`) transliterates the WAL spec's (`WalHist.lean`,
`WalDisk.lean`). This file holds:

* **the tester's records as Lean values** (`TOp`, `TContents`, `TCand`, `TOracle`), over the Go
  structs that are already pure (`hardState`, `entry`);
* **the transliteration of `ref.go`** (`tLastHS`, `tRead`, `tReadFrom`, `tReadCut`, `tImgs`,
  `tLastIdx`, `tCutPos`, `tNameBound`, `tOpenBound`): each a Lean function of the Go one's shape, in
  its own arithmetic (`w64` where Go uses `uint64`), so that the specs of the Go functions (step 3)
  return them; `RefLemmas.lean` relates them to `WalHist`'s;
* **the oracle's encoding** (`encodeOracle`, `oracle.go`'s `putU64`/`putOps`/...);
* **the abstraction into the model** (`absOp`: the tester's operation as the history's);
* **the crash invariant** (`TInv`, plan §2.3): the oracle file, the WAL directory, and the relation
  between them (`tRel`), per generation.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.Base
public import Proof.go_etcd_io.etcd.server.v3.storage.WalHistLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI go_etcd_io.raft.v3

/-! ## The tester's records -/

section pure
variable [GooseExts]

/-- `hardState` (`ref.go`), a pure Go struct. -/
abbrev THs := github_com.mit_pdos.etcd_grove.examples.etcd.wal.hardState
/-- `entry` (`ref.go`), a pure Go struct: an entry whose data is `entData` of its fields. -/
abbrev TEnt := github_com.mit_pdos.etcd_grove.examples.etcd.wal.entry

/-- The empty hard state. -/
def tHs0 : THs := ⟨W64 0, W64 0, W64 0⟩

/-- `walOp` (`ref.go`): `Save(hs, ents)` or, when `snap`, `SaveSnapshot(idx, term)`. -/
structure TOp where
  snap : Bool
  hs : THs
  ents : List TEnt
  idx : w64
  term : w64

/-- `contents` (`ref.go`): what a restart read. -/
structure TContents where
  hs : THs
  baseIdx : w64
  baseTerm : w64
  ents : List TEnt

/-- `cand` (`oracle.go`): a candidate history with its bounds on the model's `unl` and `pur`. -/
structure TCand where
  h : List TOp
  unl : w64
  pur : w64

/-- `oracle` (`oracle.go`). Candidate `c`'s history is `c.h ++ since`, its synced mark
`|c.h| + synced`. -/
structure TOracle where
  created : Bool
  cands : List TCand
  since : List TOp
  synced : w64
  lastHS : THs
  opens : List w64

/-! Injective encodings, for the ghost variable of the oracle. -/

instance : Pos.Countable THs :=
  .ofInjective (fun h => Pos.Countable.encode (h.term', h.vote', h.commit'))
    (by intro a b h; cases a; cases b; simp_all)

instance : Pos.Countable TEnt :=
  .ofInjective (fun e => Pos.Countable.encode (e.index', e.term', e.size', e.salt'))
    (by intro a b h; cases a; cases b; simp_all)

instance : Pos.Countable TOp :=
  .ofInjective (fun o => Pos.Countable.encode (o.snap, o.hs, o.ents, o.idx, o.term))
    (by intro a b h; cases a; cases b; simp_all)

instance : Pos.Countable TCand :=
  .ofInjective (fun c => Pos.Countable.encode (c.h, c.unl, c.pur))
    (by intro a b h; cases a; cases b; simp_all)

instance : Pos.Countable TOracle :=
  .ofInjective (fun o => Pos.Countable.encode (o.created, o.cands, o.since, o.synced, o.lastHS, o.opens))
    (by intro a b h; cases a; cases b; simp_all)

/-- `freshOracle()` (`oracle.go`): one candidate, the empty history. -/
def tFreshOracle : TOracle := ⟨false, [⟨[], W64 0, W64 0⟩], [], W64 0, tHs0, []⟩

instance : Inhabited TOracle := ⟨tFreshOracle⟩

/-! ## `ref.go`, transliterated -/

/-- `hsEmpty`. -/
def tHsEmpty (h : THs) : Bool :=
  decide (h.term' = W64 0) && decide (h.vote' = W64 0) && decide (h.commit' = W64 0)

/-- `phsNext`. -/
def tPhsNext (p h : THs) : THs := if tHsEmpty h then p else h

/-- `walLastHS`. -/
def tLastHS (h : List TOp) : THs :=
  h.foldl (fun p o => if o.snap then p else tPhsNext p o.hs) tHs0

/-- `walMustSync`. -/
def tMustSync (last h : THs) (nents : Nat) : Bool :=
  Bool.or (decide (0 < nents))
    (!tHsEmpty h && Bool.or (!decide (h.vote' = last.vote')) (!decide (h.term' = last.term')))

/-- `walSaveSnap`. -/
def tSaveSnap (s : TContents) (idx term : w64) : TContents :=
  if uint.nat idx < uint.nat s.baseIdx then s else
  { hs := s.hs, baseIdx := idx, baseTerm := term,
    ents := if uint.nat idx ≤ uint.nat s.hs.commit' then s.ents.drop (uint.nat (idx - s.baseIdx))
      else [] }

/-- `readEnt` (`none` for its `false`). -/
def tReadEnt (b : w64) (ents : List TEnt) (e : TEnt) : Option (List TEnt) :=
  if uint.nat e.index' ≤ uint.nat b then some []
  else if ents.length < uint.nat (e.index' - b - W64 1) then none
  else some (ents.take (uint.nat (e.index' - b - W64 1)) ++ [e])

/-- The fold of `walFoldChk`, from `s`. -/
def tFoldChkFrom (s : TContents) : List TOp → Option TContents
  | [] => some s
  | o :: h =>
    if o.snap then tFoldChkFrom (tSaveSnap s o.idx o.term) h
    else do
      let ents ← o.ents.foldlM (fun ents e => tReadEnt s.baseIdx ents e) s.ents
      tFoldChkFrom { s with hs := tPhsNext s.hs o.hs, ents := ents } h

/-- The zero `contents`. -/
def tC0 : TContents := ⟨tHs0, W64 0, W64 0, []⟩

/-- `walFoldChk`. -/
def tFoldChk (h : List TOp) : Option TContents := tFoldChkFrom tC0 h

/-- Whether a restart keeps the operation (a snapshot record only at or below the commit `c`). -/
def tKeep (c : w64) (o : TOp) : Bool := !(o.snap && uint.nat c < uint.nat o.idx)

/-- `walRead`. -/
def tRead (h : List TOp) : Option TContents :=
  tFoldChk (h.filter (tKeep (tLastHS h).commit'))

/-- The newest snapshot record of `walReadFrom`'s loop (highest index, the last of equal ones). -/
def tNewest (f : List TOp) : Option (w64 × w64) :=
  f.foldl (fun acc o => if o.snap then
      (match acc with
        | none => some (o.idx, o.term)
        | some b => if uint.nat b.1 ≤ uint.nat o.idx then some (o.idx, o.term) else acc)
    else acc) none

/-- `walReadFrom`. -/
def tReadFrom (h : List TOp) (k : Nat) : Option TContents :=
  let f := (h.drop k).filter (tKeep (tLastHS h).commit')
  match tNewest f with
  | none => none
  | some (i, t) => tFoldChkFrom ⟨tLastHS (h.take k), i, t, []⟩ f

/-- `walReadCut`. -/
def tReadCut (h : List TOp) (k : w64) : Option TContents :=
  if k = W64 0 then tRead h else tReadFrom h (uint.nat k)

/-- An image operation: the first `k` entries of a `Save`, with no state record. -/
def tTornOp (es : List TEnt) : TOp := ⟨false, tHs0, es, W64 0, W64 0⟩

/-- The torn images of `walImgs` at position `j` (empty unless operation `j` is a `Save`): the
first `k` entries of it, for `k ≤ |ents|`, but `k = |ents|` when its hard state is empty (that image
is the next prefix). -/
def tTornImgs (h : List TOp) (j : Nat) : List (List TOp) :=
  match h[j]? with
  | some o =>
    if o.snap then [] else
    (List.range (if tHsEmpty o.hs then o.ents.length else o.ents.length + 1)).map
      (fun k => h.take j ++ [tTornOp (o.ents.take k)])
  | none => []

/-- `walImgs`. -/
def tImgs (h : List TOp) (n : Nat) : List (List TOp) :=
  (List.range' n (h.length + 1 - n)).flatMap (fun j => h.take j :: tTornImgs h j)

/-- `lastIdx`. -/
def tLastIdx (h : List TOp) : w64 :=
  let e := h.foldl (fun x o => if o.snap then x else (o.ents.getLast?.map (·.index')).getD x) (W64 0)
  let sn := h.foldl (fun x o => if o.snap ∧ uint.nat x < uint.nat o.idx then o.idx else x) (W64 0)
  if uint.nat e < uint.nat sn then sn else e

/-- `cutPos`. -/
def tCutPos (h : List TOp) (b : Nat) : Bool :=
  Bool.or (decide (b = 0)) (match h[b - 1]? with
    | some o => !o.snap && !(tHsEmpty o.hs && o.ents.isEmpty)
    | none => false)

/-- `nameBound`. -/
def tNameBound (h : List TOp) (a : w64) : w64 :=
  W64 (((List.range (h.length + 1)).filter (fun b =>
    tCutPos h b && decide (uint.nat (tLastIdx (h.take b) + W64 1) ≤ uint.nat a))).getLast?.getD 0)

/-- `openBound`. -/
def tOpenBound (imgs : List (List TOp)) (a : w64) : w64 :=
  imgs.foldl (fun best i => if uint.nat best < uint.nat (tNameBound i a) then tNameBound i a else best)
    (W64 0)

/-! ## The oracle's encoding (`oracle.go`) -/

/-- `putU64`'s bytes: `x`, little-endian. -/
def tU64 (x : w64) : List w8 := (List.range 8).map (fun i : Nat => W8 (uint.Z (x >>> W64 (8 * (i : Int)))))

/-- `putHS`'s bytes. -/
def tHsBytes (h : THs) : List w8 := tU64 h.term' ++ tU64 h.vote' ++ tU64 h.commit'

/-- An entry's bytes in `putOps`. -/
def tEntBytes (e : TEnt) : List w8 := tU64 e.index' ++ tU64 e.term' ++ tU64 e.size' ++ tU64 e.salt'

/-- An operation's bytes in `putOps`. -/
def tOpBytes (o : TOp) : List w8 :=
  tU64 (if o.snap then W64 1 else W64 0) ++ tHsBytes o.hs ++ tU64 o.idx ++ tU64 o.term ++
    tU64 (W64 o.ents.length) ++ (o.ents.flatMap tEntBytes)

/-- `putOps`'s bytes. -/
def tOpsBytes (h : List TOp) : List w8 := tU64 (W64 h.length) ++ h.flatMap tOpBytes

/-- `encodeOracle`. -/
def tEncodeOracle (o : TOracle) : GoString :=
  tU64 (if o.created then W64 1 else W64 0) ++ tU64 (W64 o.cands.length) ++
    o.cands.flatMap (fun c => tOpsBytes c.h ++ tU64 c.unl ++ tU64 c.pur) ++
    tOpsBytes o.since ++ tU64 o.synced ++ tHsBytes o.lastHS ++ tU64 (W64 o.opens.length) ++
    o.opens.flatMap tU64

/-! ## The abstraction into the model -/

/-- `entData` (`wal.go`): the salt's 8 bytes, then a pattern of the index, term and position. -/
def tEntData (e : TEnt) : List w8 :=
  (List.range (min 8 (uint.nat e.size'))).map
    (fun i : Nat => W8 (uint.Z (e.salt' >>> W64 (8 * (i : Int))))) ++
  (List.range' 8 (uint.nat e.size' - 8)).map
    (fun i : Nat => W8 (uint.Z ((e.index' + W64 3 * e.term' + W64 (i : Int)) % W64 251)))

/-- The hard state as the model's (`toHS`). -/
def absHs (h : THs) : HardStateM := ⟨h.term', h.vote', h.commit'⟩

/-- The entry as the model's (`toRaft`: `EntryNormal`, data `entData`). -/
def absEnt (e : TEnt) : EntryM := ⟨e.term', e.index', W32 0, tEntData e⟩

/-- The snapshot record the tester saves at `(idx, term)`: the conf state is the model's choice,
fixed here (`SaveSnapshot`'s `walSnapAt` constrains only the index, the term and whether the conf
state is set). -/
def absSnapMd (idx term : w64) : SnapshotMetadataM := ⟨⟨[], [], [], [], false⟩, idx, term⟩

/-- The operation as the history's. -/
def absOp (o : TOp) : WalOp :=
  if o.snap then .snap (absSnapMd o.idx o.term) else .save (absHs o.hs) (o.ents.map absEnt)

/-- The read as the model's components (the tester compares the hard state, the base and the
entries; the snapshot's conf state is not read back). -/
def absC (c : TContents) : HardStateM × w64 × w64 × List EntryM :=
  (absHs c.hs, c.baseIdx, c.baseTerm, c.ents.map absEnt)

/-- The model's read, by the same components. -/
def projC (σ : StorContents) : HardStateM × w64 × w64 × List EntryM :=
  (σ.hs, σ.base.index', σ.base.term', σ.ents)

/-- **The tester's entries are well formed**: at least the salt's 8 bytes (so `fromRaft` reads the
entry back), at most 140000 (`member.size`; sized: `Save`'s `entSizeOk`), and every index and term
below `2^63` (the guards of T-4: `maxIndex = 2^62`, plus the few entries an operation adds; so no
index is `2^64-1`, `Save`'s premise, and `nameBound`'s `+1` does not wrap). -/
def tEntWf (e : TEnt) : Prop :=
  8 ≤ uint.nat e.size' ∧ uint.nat e.size' ≤ 140000 ∧ uint.nat e.index' < 2 ^ 63 ∧
    uint.nat e.term' < 2 ^ 63

/-- **The tester's operations are well formed**: entries well formed, a snapshot's index and term
below `2^63`. -/
def tOpWf (o : TOp) : Prop :=
  (o.snap = true → uint.nat o.idx < 2 ^ 63 ∧ uint.nat o.term < 2 ^ 63) ∧
  (o.snap = false → ∀ e ∈ o.ents, tEntWf e)

/-- Every operation of `h` is well formed. -/
def tHistWf (h : List TOp) : Prop := ∀ o ∈ h, tOpWf o

/-! ## The relation between the oracle and the WAL -/

/-- Candidate `c`'s history (`c.h ++ since`). -/
def tCandHist (o : TOracle) (c : TCand) : List TOp := c.h ++ o.since

/-- Candidate `c`'s synced mark (`|c.h| + synced`). -/
def tCandMark (o : TOracle) (c : TCand) : Nat := c.h.length + uint.nat o.synced

/-- The unlock bound the pending `Open`s give candidate `c` (`checkRestart`'s raise): the largest
`openBound` at an opened snapshot over the images of `c`'s history. -/
def tOpensBound (o : TOracle) (c : TCand) : Nat :=
  (o.opens.map (fun s => uint.nat (tOpenBound (tImgs (tCandHist o c) (tCandMark o c)) s))).foldl max 0

/-- **The WAL state `d` is accounted for by candidate `c`** (plan §2.3): its history is an image of
`c`'s at `c`'s mark (one shape for the running history, a pending `Save` not yet applied, and a
crash image); its purge and read positions at most `c.pur`; its unlock position at most `c.unl` or
what the pending `Open`s raise it to; sized; `c`'s history well formed. -/
def tCandOk (o : TOracle) (c : TCand) (d : WalDur) : Prop :=
  walImg ((tCandHist o c).map absOp) (tCandMark o c) (d.H.map WalOpG.toM) ∧
  d.pur ≤ uint.nat c.pur ∧ d.cut ≤ uint.nat c.pur ∧ d.unl ≤ max (uint.nat c.unl) (tOpensBound o c) ∧
  d.sized = true ∧ tHistWf (tCandHist o c)

/-- **Before `Create` returned** (`¬ created`): the oracle is fresh (its file is written only once
`created` holds) and the WAL is absent or `Create`'s fresh one, which a crash between `Create`'s
commit and the store of `created` leaves. -/
def tPreOk (o : TOracle) (od : Option WalDur) : Prop :=
  o = tFreshOracle ∧
    (od = none ∨ ∃ d, od = some d ∧ d.H = [] ∧ d.unl = 0 ∧ d.pur = 0 ∧ d.cut = 0 ∧ d.sized = true)

/-! ## Paths -/

/-- The oracle file (`Boot`: `root + "/oracle/state"`). -/
def tOrPath (root : GoString) : GoString := root ++ go!"/oracle/state"
/-- The data directory (`root + "/data"`). -/
def tDataDir (root : GoString) : GoString := root ++ go!"/data"
/-- The member directory, the WAL area (`data + "/member"`). -/
def tArea (root : GoString) : GoString := tDataDir root ++ go!"/member"
/-- The WAL directory (`memberDir + "/wal"`). -/
def tWalDir (root : GoString) : GoString := tArea root ++ go!"/wal"

/-- **The oracle file holds `o`**: its encoding, or no file and the fresh oracle. -/
def tOracleFile (root : GoString) (fs : DurableState) (o : TOracle) : Prop :=
  fs !! tOrPath root = some (tEncodeOracle o) ∨ (fs !! tOrPath root = none ∧ o = tFreshOracle)

end pure

/-! ## The crash invariant (per generation) -/

section inv
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt absDiskExt] [HasExt durableExt]
  [GoGlobalContext] [go.IntoValInj GoString]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable [AllG GF]

/-- The invariant's namespace. -/
def walN : Namespace := nroot.@"etcd_wal_tester"

/-- **What the WAL side knows, by the oracle's phase**: after `Create` returned, some candidate
accounts for the WAL (`tCandOk`), whose candidate's mark is synced and whose entry is durable;
before, `tPreOk`. -/
def tRelI (root : GoString) (o : TOracle) (od : Option WalDur) : IProp GF :=
  if o.created then
    iprop(∃ (d : WalDur) (c : TCand), ⌜od = some d ∧ c ∈ o.cands ∧ tCandOk o c d⌝ ∗
      walSyncedLb (L := L) (tWalDir root) (tCandMark o c) ∗ walNamed (L := L) (tWalDir root))
  else iprop(⌜tPreOk o od⌝)

instance tIte_timeless {c : Prop} [Decidable c] (P Q : IProp GF) [Timeless P] [Timeless Q] :
    Timeless (if c then P else Q) := by
  split <;> assumption

instance tRelI_timeless (root : GoString) (o : TOracle) (od : Option WalDur) :
    Timeless (tRelI (L := L) (GF := GF) root o od) := by
  unfold tRelI; split <;> infer_instance

/-- **The tester's crash invariant's contents** (plan §2.3), for the generation `L`: the durable
files `fs` in mode `om` (unreserved until the first `Read` reserves the WAL area), the oracle file
holding `o`, the WAL directory holding `od`, the ghost variables' halves (the program holds the
others: it knows the exact oracle and WAL state), the relation, and the facts the crash carries
(the area, the root's durability, the area's durability once a WAL may exist, durable's
reservation once made). -/
def TInvBody (root : GoString) (γo γw : GName) : IProp GF :=
  iprop(∃ (fs : DurableState) (om : Option GoString) (o : TOracle) (od : Option WalDur),
    durableOwnM (L := L) om fs ∗ ⌜om = none ∨ om = some (tArea root)⌝ ∗
    ⌜tOracleFile root fs o⌝ ∗ ghostVar γo (1 : Qp).half o ∗
    walDirIs (L := L) (tWalDir root) od ∗ ghostVar γw (1 : Qp).half od ∗
    tRelI (L := L) root o od ∗
    walArea (L := L) (tArea root) ∗ dirDurable (L := L) root ∗
    (if o.created ∨ od.isSome then dirDurable (L := L) (tArea root) else iprop(True)) ∗
    (if om.isSome then durableReserved (L := L) (tArea root) else iprop(True)))

instance TInvBody_timeless (root : GoString) (γo γw : GName) :
    Timeless (TInvBody (L := L) (GF := GF) root γo γw) := by
  unfold TInvBody; infer_instance

/-- **The tester's crash invariant** of the generation `L`. -/
def TInv (root : GoString) (γo γw : GName) : IProp GF := inv walN (TInvBody (L := L) root γo γw)

instance TInv_persistent (root : GoString) (γo γw : GName) :
    Persistent (TInv (L := L) (GF := GF) root γo γw) := by
  unfold TInv; infer_instance

/-- **The boot precondition of a generation** (plan §2.3's `P L`): the invariant, the program's
halves of the ghost variables, the generation's lock token. -/
def TBoot (root : GoString) : IProp GF :=
  iprop(∃ (γo γw : GName) (o : TOracle) (od : Option WalDur), TInv (L := L) root γo γw ∗
    ghostVar γo (1 : Qp).half o ∗ ghostVar γw (1 : Qp).half od ∗ walUnlockedTok (L := L))

end inv

end etcd_wal
end EtcdGrove
end Perennial

/-
`db.loadFreelist()` at `Open`: what its spec `DB.loadFreelist.spec_open` is written in (`openWb`,
`lfOK`, `lfPre`, `lfW`, `lfPost`) and the spec, moved unchanged out of its proof file
`DB__loadFreelist.lean` (import tiers, 2026-11-19: `Open/Facts.lean` names `lfOK`, and a proof file is
imported by linking modules only).
-/
module

public import Proof.go_etcd_io.bbolt.Open.LoadFL
public import Proof.go_etcd_io.bbolt.Open.Carve
public import Proof.go_etcd_io.bbolt.Open.OnceOwn
public import Proof.go_etcd_io.bbolt.Open.MutexOwn
public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas.SliceLen
public import Spec.go_etcd_io.bbolt.newFreelist
public import Spec.go_etcd_io.bbolt.DB__hasSyncedFreelist
public import Spec.go_etcd_io.bbolt.DB__meta
public import Spec.go_etcd_io.bbolt.DB__page
public import Spec.go_etcd_io.bbolt.DB__freepages
public import Spec.go_etcd_io.bbolt.internal.common.Meta__Freelist
public import Spec.go_etcd_io.bbolt.internal.freelist.Interface__Read
public import Spec.go_etcd_io.bbolt.internal.freelist.Interface__Init
public import Spec.go_etcd_io.bbolt.internal.freelist.Interface__FreeCount
public import Proof.go_etcd_io.bbolt.internal.common.Lemmas.Layout

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- The slots' bytes of the opened file `xs`. -/
def openWb (xs : List ByteG) : Nat → List w8 :=
  fun s => bytesAt (xs.map Prod.fst) (4096 * s) 4096

/-- The pure facts `loadFreelist` needs of the opened file `xs` (`fileHolds_decode`'s, the
mapping `(b, L)`'s, `Open`'s namespace and database). -/
def lfOK (N : Namespace) (db : Loc) (C : CommitSt) (b : Loc) (L : Nat) (m : OsMeta)
    (xs : List ByteG) : Prop :=
  fileImage (xs.map Prod.fst) C ∧ C.metaOk ∧ treeOK C ∧ flFileOK (xs.map Prod.fst) C ∧
    C.hwm * 4096 ≤ xs.length ∧ 8192 ≤ xs.length ∧ xs.length = m.size ∧ m.size ≤ L ∧
    wdbSz m (some (b, L)) ∧ m.maps = GMap.singleton b L ∧ 1 ≤ C.txid ∧ C.txid < 2 ^ 62 ∧
    (↑N : CoPset) ## ↑osN ∧ db ≠ null

/-- **What `loadFreelist` takes at `Open`**: `open_core`'s inputs, the mapping's client halves
not yet carved (the file's bytes at a half, the rest any cells). -/
def lfPre (γbq : GName) (N : Namespace) (db sp f : Loc) (fd : w64) (p : BFile) (C : CommitSt)
    (b : Loc) (L : Nat) (m : OsMeta) (xs : List ByteG) : IProp GF :=
  iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ osInv ∗ dbFixed γbq N db sp ∗
      ghostVar γbq 1 () ∗
      db.[DB, go!"metalock"] ↦ (zero_val sync.Mutex) ∗
      db.[DB, go!"mmaplock"] ↦ (zero_val sync.RWMutex) ∗
      db.[DB, go!"statlock"] ↦ (zero_val sync.RWMutex) ∗
      db.[DB, go!"opened"] ↦ true ∗ db.[DB, go!"freelist"] ↦ interface.nil ∗
      (db.[DB, go!"ops"]).[dbOps, go!"writeAt"] ↦
        methods (go.GoType.PointerType os.File.ty) go!"WriteAt" #f ∗
      db.[DB, go!"rwtx"] ↦ null ∗ db.[DB, go!"file"] ↦ f ∗ dbPathLk db p fd ∗
      db.[DB, go!"datasz"] ↦ W64 (L : Int) ∗
      mapFields db (DFrac.own 1) (some (b, L)) ∗
      bMeta p C [] m ∗ fileOwn f fd p.path (DFrac.own 1) ∗
      osFd fd (DFrac.own 1) (dbFd p.ino) ∗ Ps sp 1 ∗
      bBytes p 0 (DFrac.own 1) xs ∗
      bytesPointsto b (DFrac.own (1 : Qp).half) (xs.map Prod.fst) ∗
      ∃ vf, cellsR b xs.length (L - xs.length) vf)

/-- The writer side after `loadFreelist`. -/
def lfW (C : CommitSt) (b : Loc) (L : Nat) (m : OsMeta) (xs : List ByteG) (f : Loc)
    (fd : w64) (fl : FLPg) (fli : GoInterface) : WDb :=
  { openW C b L m (openWb xs) f fd with fl := fl, fli := fli }

/-- **What `loadFreelist` gives at `Open`**: `open_writer`'s inputs but `rwlock`. -/
def lfPost (γbq : GName) (N : Namespace) (db sp f : Loc) (fd : w64) (p : BFile)
    (C : CommitSt) (b : Loc) (L : Nat) (m : OsMeta) (xs : List ByteG) : IProp GF :=
  iprop(∃ (B : BNs) (fl : FLPg) (fli : GoInterface),
    isBoltCoreP B N db p sp C.txid ∗
    threadPool.isThreadPool (poolN N) B.pool (rdPair B db sp) ∗
    wdbCore B db p (lfW C b L m xs f fd fl fli) ∗ ghostVar B.st (1 : Qp).half.half (treeData C, C.txid) ∗
    flPgOwn fli fl ∗ sparePair B db sp ∗ ghostVar B.cls (1 : Qp).half false ∗
    boltStateDef B 1 (treeData C) ∗ dghostVar B.opn (DFrac.own 1) false ∗ ghostVar B.clo 1 () ∗
    ⌜wdbOK (lfW C b L m xs f fd fl fli) ∧ B.bq = γbq⌝)

/-- **`db.loadFreelist()` at `Open`**. -/
abbrev DB.loadFreelist.spec_open : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 29)] [ReceiptBoundLe GF (2 ^ 62)] (γbq : GName) (N : Namespace)
    (db sp f : Loc) (fd : w64) (p : BFile)
    (C : CommitSt) (b : Loc) (L : Nat) (m : OsMeta) (xs : List ByteG),
  lfOK N db C b L m xs → 0 ≤ fd.toInt →
  {{ lfPre (GF := GF) γbq N db sp f fd p C b L m xs ∗
      db.[DB, go!"freelistLoad"] ↦ (zero_val sync.Once) ∗ ⧖ C.txid ∗ bMode γbq N db p }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"loadFreelist")) (Val #()))
  {{ RET #(); lfPost γbq N db sp f fd p C b L m xs }}

end spec

end bbolt
end EtcdGrove
end Perennial

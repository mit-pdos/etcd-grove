/-
`Open` (bbolt): its one spec (session S3f, the user's rule of one canonical spec per function;
`notes/bbolt-integration-plan.md`, Log, "S3f"), over the **shared mode of the tree** (a whole claim on
the database file's name, so that several databases are opened and closed concurrently). Its error
case carries the witness `¬ FsNoErr` (the file model returned an error that `NoIoErr`/`NoMapLockErr`
exclude; `Fs.fsNoErr_of` refutes it under those premises with full coverage). Proof:
`Proof/go_etcd_io/bbolt/Open.lean` (`Open`'s proof generic in the environment's errors,
`Open.wp_proofG`, `Open.lean`).
-/
module

public import Spec.go_etcd_io.bbolt.ApiS
public import Spec.go_etcd_io.bbolt.Options
public import Spec.go_etcd_io.bbolt.Logger
public import Spec.os.OpenFileS
public import GooseLang.Ext.Fs.FsNoErr
public import Spec.go_etcd_io.bbolt.ApiCrash

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `bolt.Open(d/b, mode, opts)`: the database the file at `b` holds, open, or an error of the
environment.
- The directory `d`'s shared path (`osPathS R d dq j`), a call permission and the whole claim on the
  name `b` (`osNames j (.only [b]) 1 h`); `nameHolds h b D`: a mappable file holding `D` at `b`
  (`fileHoldsM`: at most `maxMapSize` bytes, else `mmap` fails with "mmap too large"), or nothing (and
  `D = ∅`: `Open` creates the file). They come back on every exit, the claim as the open left it
  (`crOut`, `Spec/os/OpenFileS.lean`).
- The options are read and given back; options under which the specs hold (`OptsM.ok`) and under
  which `Open` has no error of its own (`optsAtNoErr`: no `Timeout`, so a `flock` conflict is retried
  rather than reported; `NoFreelistSync`, so no write transaction is committed; an `InitialMmapSize`
  `mmapSize` accepts); a logger bbolt may call.
- On success, the handle `isBolt db γ`, the file's inode (`boltIno`), all of the committed data
  `boltState γ 1 D` (the client decides where it lives) and the closer token `boltCloser γ`, which
  `DB.Close` consumes. The namespace `N` is the caller's (`γ.ns = N`), disjoint from OsFs's `osN`.
- On an error, `¬ FsNoErr ∨ ¬ PathFits (child d b)` (the second: the path does not fit, which
  `NoIoErr` does not cover, wal-fsfix 2026-11-20); `¬ FsNoErr`: some step of the file model failed in a way `NoIoErr`/`NoMapLockErr`
  exclude (`Fs.fsNoErr_of`); the file is lost to the caller (`init` may have written part of it).
- The bounds the owner needs (`notes/bounds-plan.md`, B1): fewer than `2 ^ 29` live threads (the
  read transactions plus `Commit`'s spare reader slot fit `mmaplock`'s readers); fewer than `2 ^ 62`
  receipts (the commits' txids stay below `2 ^ 63`). -/
abbrev Open.spec : Prop :=
  ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] [ThreadBoundLe GF (2 ^ 29)]
    [ReceiptBoundLe GF (2 ^ 62)] (N : Namespace) (R : Roots) (d b : GoString) (dq : DFrac) (j : Ino)
    (qc : Qp) (h : NamesH) (mode : w32) (opts : Loc) (dqo : DFrac) (o : OptsM) (D : Data),
  NameOk b →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ osInv ∗ ⌜↑N ## ↑osN⌝ ∗
      osSharedInv R ∗ osPathS R d dq j ∗ osCallPerm (callKey R d) qc ∗ osNames j (.only [b]) (DFrac.own 1) h ∗
      nameHolds h b D ∗
      optsAtNoErr opts dqo o ∗ ⌜o.ok⌝ ∗ (⌜o.logger = GoInterface.nil⌝ ∨ boltLogger o.logger) }}
    (App (App (App (Val (@! go_etcd_io.bbolt.Open)) (Val #(child d b))) (Val #mode)) (Val #opts))
  {{ (db : Loc) (err : GoInterface), RET (PairV #db #err); optsAtNoErr opts dqo o ∗
      osPathS R d dq j ∗ osCallPerm (callKey R d) qc ∗
      (∃ oc : Option (Nat × Nat × Ino), crOut j b h (DFrac.own 1) oc ∗
        ((⌜err = GoInterface.nil⌝ ∗ ∃ (γ : BoltName) (i : Ino),
            ⌜γ.ns = N ∧ crIno b h oc i⌝ ∗ isBolt db γ ∗ boltIno γ i ∗ boltState γ 1 D ∗
            boltCloser γ) ∨
         ⌜err ≠ GoInterface.nil ∧ (¬ FsNoErr ∨ ¬ PathFits (child d b))⌝)) }}

/-- **`bolt.Open(d/b, mode, opts)` of an existing database file in crash mode** (W6; the dual of
`DB.Close.specC`): the file of inode `i` at `b`, held by the caller (in its own invariant, so that a
crash finds it) as a settled durable file of `D` (`fileHoldsMDurC`), reached through the atomic update
(mask as `Tx.Commit`'s), with options that sync (`optsAtSyncs`: `NoSync` and `NoGrowSync` off). The
commit point is `Open`'s first use of the file, right after `os.OpenFile`: the update consumes the
file and gives back bbolt's crash record of the new database `γ` (its name chosen there, `γ.ns = N`),
at `(D, D)` (`boltCrashRec`: half of the committed data, at the version the file's txid, and the
file in bbolt's crash invariant), so that a crash before it finds the file, one after it the record
(C-I1's `dbCrash`).
- Pre as `Open.spec`'s, for an existing file: the name `b` holds the inode `i` in the claim, and no
  `nameHolds` (the file is the update's).
- `FsNoErr` (the file system does not fail, a premise): every crash-mode caller has it (its records
  live under `onFs`); without it `Open` could not commit (the record carries it) and, the file being
  the caller's, could not run without committing.
- On success, as `Open.spec`'s, but the client holds half of the committed data (`boltState γ ½ D`;
  the record holds the other half), and the update's `Q γ`.
- On an error, only the path that does not fit (before `OpenFile`, the update not fired).
The claim on `b` comes back unchanged (the file exists: `OpenFile` creates nothing). -/
abbrev Open.specC : Prop :=
  ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] [ThreadBoundLe GF (2 ^ 29)]
    [ReceiptBoundLe GF (2 ^ 62)] (N : Namespace) (R : Roots) (d b : GoString) (dq : DFrac) (j : Ino)
    (qc : Qp) (h : NamesH) (i : Ino) (mode : w32) (opts : Loc) (dqo : DFrac) (o : OptsM) (D : Data)
    (Q : BoltName → IProp GF),
  NameOk b → h.cur !! b = some (.file i) → FsNoErr →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ osInv ∗ ⌜↑N ## ↑osN⌝ ∗
      osSharedInv R ∗ osPathS R d dq j ∗ osCallPerm (callKey R d) qc ∗
      osNames j (.only [b]) (DFrac.own 1) h ∗
      optsAtSyncs opts dqo o ∗ ⌜o.ok⌝ ∗ (⌜o.logger = GoInterface.nil⌝ ∨ boltLogger o.logger) ∗
      AU <{ fileHoldsMDurC i D }> @ ⊤ \ ↑N, ∅
        <{ ∀∀ (γ : BoltName), ⌜γ.ns = N⌝ ∗ boltCrashRec γ i D D, COMM Q γ }> }}
    (App (App (App (Val (@! go_etcd_io.bbolt.Open)) (Val #(child d b))) (Val #mode)) (Val #opts))
  {{ (db : Loc) (err : GoInterface), RET (PairV #db #err); optsAtSyncs opts dqo o ∗
      osPathS R d dq j ∗ osCallPerm (callKey R d) qc ∗ osNames j (.only [b]) (DFrac.own 1) h ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ γ : BoltName, ⌜γ.ns = N⌝ ∗ isBolt db γ ∗ boltIno γ i ∗
          boltState γ (1 : Qp).half D ∗ boltCloser γ ∗ Q γ) ∨
       ⌜err ≠ GoInterface.nil ∧ ¬ PathFits (child d b)⌝) }}

end spec

end bbolt
end EtcdGrove
end Perennial

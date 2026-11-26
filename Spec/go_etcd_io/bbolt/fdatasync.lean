/-
`fdatasync` (bbolt, internal): its spec (U0b of `notes/bbolt-proof-plan.md`, a frozen
cross-unit contract). Proved by U4; used by U10 (`Tx.write`, `writeMeta`). Proof:
`Proof/go_etcd_io/bbolt/fdatasync.lean` (a `sorry` until U4).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Ctx
public import Proof.go_etcd_io.bbolt.Inv.BFileCommit
public import Spec.fmt.ErrorOk

@[expose] public section

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

/-- `fdatasync(db)` (`syscall.Fdatasync` of the file's fd): in-process, nothing but the file's
sync bookkeeping changes (durability is out of scope); an error is a `fmtErrorOk` one. -/
abbrev fdatasync.spec : Prop :=
  ∀ (db f : Loc) (fd : w64) (p : BFile) (i : Ino) (m : OsMeta) (dqf dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ osInv (GF := GF) ∗
      db.[DB, go!"file"] ↦{dqf} f ∗ fileOwn f fd p.path dq ∗ osFd fd dq (dbFd i) ∗
      osMeta i (DFrac.own 1) m }}
    (App (Val #(functions fdatasync [])) (Val #db))
  {{ (err : GoInterface), RET #err; db.[DB, go!"file"] ↦{dqf} f ∗ fileOwn f fd p.path dq ∗
      osFd fd dq (dbFd i) ∗
      (∃ m' : OsMeta, osMeta i (DFrac.own 1) m' ∗ ⌜m'.size = m.size ∧ m'.maps = m.maps⌝) ∗
      (⌜err = interface.nil⌝ ∨ ⌜err ≠ interface.nil⌝ ∗ fmtErrorOk err) }}

/-- **`fdatasync(db)`, a commit's second sync in crash mode** (W1, `Tx.writeMeta`): the new meta
page's bytes (its slot, `C'`'s current meta) the only ones written since the last sync
(`bMetaCm`); it succeeds (crash mode records `FsNoErr`), the crash invariant's value idle at `C'`
again. -/
abbrev fdatasync.specC : Prop :=
  ∀ (db f : Loc) (fd : w64) (p : BFile) (c : CsN) (C' C : CommitSt) (m : OsMeta) (o : Nat)
    (ys : List ByteG) (dqf dq : DFrac),
  p.cs = some c → bNsOk p → o = 4096 * (C'.txid % 2) → ys.map Prod.fst = C'.slot C'.txid →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ osInv (GF := GF) ∗ bCsInv p ∗
      db.[DB, go!"file"] ↦{dqf} f ∗ fileOwn f fd p.path dq ∗ osFd fd dq (dbFd p.ino) ∗
      bMetaCm p C' C [(o, 4096)] m ∗ bBytes p o (DFrac.own 1) ys }}
    (App (Val #(functions fdatasync [])) (Val #db))
  {{ (err : GoInterface), RET #err; db.[DB, go!"file"] ↦{dqf} f ∗ fileOwn f fd p.path dq ∗
      osFd fd dq (dbFd p.ino) ∗ ⌜err = interface.nil⌝ ∗
      ∃ (m' : OsMeta) (ys' : List ByteG), bMeta p C' [] m' ∗ bBytes p o (DFrac.own 1) ys' ∗
        ⌜m'.size = m.size ∧ m'.maps = m.maps ∧ ys'.map Prod.fst = ys.map Prod.fst⌝ }}

end spec

end bbolt
end EtcdGrove
end Perennial

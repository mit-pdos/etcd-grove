/- Lean-first (no Rocq counterpart). `db.commit(m, v)` (`examples/bboltfs/minibolt.go`, a write transaction after `m`, the current meta): refuse with `errMapTooLarge` if the next high water mark would take the file past `maxMapSize` (1 GiB), remap if the high water mark passes the mapping (`mmap`), grow the file (`Truncate`, `Sync`), write the data page at the high water mark and `Fdatasync` it (it is then a committed page, `pageIs`), then, under `metalock`, write the meta to slot `txid % 2` and `Fdatasync` it. Its caller (`Commit`) holds `rwlock` and found the handle not failed: it has the writer's part of the database (`writerSt`, `rwR`'s open branch) at the current meta pages `mp`, the committer's token, and a value the client's predicate allows (`γ.vp`). On success, transaction `t + 1` is current, its root page holds `v`, and `rwlock`'s resource is whole again. On an error, the caller keeps its token (at high water mark 0 if `commit` failed the handle) and the writer's part (`writerStF`: the file without the facts of a handle not failed), failed (`dbFailed`) if `commit` failed the handle itself (the meta's write or sync), or not yet failed, for `Commit` to fail it (`errMapTooLarge` among them, which leaves the file as it was). -/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bboltfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.bboltfs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.bboltfs.Assumptions]

/-- The meta `commit` writes after `v`, before its checksum: the next txid, the high water mark
one page on, and the root at the old high water mark. -/
def nextMeta (v : Meta) : Meta :=
  { v with txid' := v.txid' + W64 1, pgid' := v.pgid' + W64 1,
           root' := { v.root' with root' := v.pgid' } }

/-- The writer's part of an open database at the meta pages `mp`, `failed` `fl`, high water mark
`hwm`, mapping state `st` and `OsMeta` `m`: `rwR`'s open branch, without its two facts (no sync
failed while not failed; no mapping only once failed). -/
def writerSt (γ : DBNames) (db f : Loc) (fd : w64) (p : GoString) (mp : List w8) (fl : Bool)
    (hwm : Nat) (st : MapSt) (m : OsMeta) : IProp GF :=
  iprop(ghostVar γ.cur (1 : Qp).half.half (mp, fl, hwm) ∗ ghostVar γ.map (1 : Qp).half st ∗
    ghostVar γ.out (1 : Qp).half.half false ∗ mapFields (GF := GF) db (DFrac.own (1 : Qp).half) st ∗
    writerFile (GF := GF) γ db f fd p mp fl hwm st m ∗ ghostVar γ.cls (1 : Qp).half false ∗
    match st with
    | some (base, len, γm) =>
      ⌜m.maps = {[base := len]} ∧ m.size ≤ len ∧ 0 < base.addr ∧ len ≤ 2 ^ 41⌝ ∗
      ghostVar γm (1 : Qp).half () ∗ mapInv (GF := GF) γ p base len γm ∗
      writerCells (GF := GF) base hwm len
    | none => writerExtra (GF := GF) γ f fd p mp fl hwm)

/-- The writer's part after a failed `commit`, at `failed` `fl` (`cur`'s): `writerSt`, its file
without the facts of a handle not failed (a failed `Truncate` may have grown the file past
`filesz`, a failed sync may have lost bytes). -/
def writerStF (γ : DBNames) (db f : Loc) (fd : w64) (p : GoString) (mp : List w8) (fl : Bool)
    (hwm : Nat) (st : MapSt) (m : OsMeta) : IProp GF :=
  iprop(ghostVar γ.cur (1 : Qp).half.half (mp, fl, hwm) ∗ ghostVar γ.map (1 : Qp).half st ∗
    ghostVar γ.out (1 : Qp).half.half false ∗ mapFields (GF := GF) db (DFrac.own (1 : Qp).half) st ∗
    writerFile (GF := GF) γ db f fd p mp true hwm st m ∗ ghostVar γ.cls (1 : Qp).half false ∗
    match st with
    | some (base, len, γm) =>
      ⌜m.maps = {[base := len]} ∧ m.size ≤ len ∧ 0 < base.addr ∧ len ≤ 2 ^ 41⌝ ∗
      ghostVar γm (1 : Qp).half () ∗ mapInv (GF := GF) γ p base len γm ∗
      writerCells (GF := GF) base hwm len
    | none => writerExtra (GF := GF) γ f fd p mp fl hwm)

/-- See the file header. -/
abbrev DB.commit.spec : Prop :=
  ∀ (γ : DBNames) (db f : Loc) (fd : w64) (p : GoString) (mp : List w8) (st : MapSt)
    (m : OsMeta) (v : w64),
  metaPagesOk mp → (curMeta mp).txid'.toNat + 1 < 2 ^ 64 →
  m.ok = true → st ≠ none → γ.vp ((curMeta mp).txid'.toNat + 1) (some v) →
  {{ pkgFacts (GF := GF) ∗ osInv (GF := GF) ∗ db.[DB, go!"file"] ↦□ f ∗
      sync.isMutex db.[DB, go!"metalock"] (metaR (GF := GF) γ db p) ∗
      sync.isRWMutexGuard db.[DB, go!"mmaplock"] (mapR (GF := GF) γ db f fd p) ∗
      writerSt (GF := GF) γ db f fd p mp false (curPgid mp) st m ∗
      dbOwner (GF := GF) γ (curMeta mp).txid'.toNat (curPgid mp) }}
    (App (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"commit")) (Val #(curMeta mp)))
      (Val #v))
  {{ (err : GoInterface), RET #err;
      (⌜err = interface.nil⌝ ∗ rwR (GF := GF) γ db f fd p ∗
          dbOwner (GF := GF) γ ((curMeta mp).txid'.toNat + 1) (curPgid mp + 1) ∗
          dbTx (GF := GF) γ ((curMeta mp).txid'.toNat + 1) (some v) ∗
          dbLast (GF := GF) γ ((curMeta mp).txid'.toNat + 1)) ∨
      (⌜err ≠ interface.nil⌝ ∗ (∃ n', dbOwner (GF := GF) γ (curMeta mp).txid'.toNat n') ∗
        ∃ (mp' : List w8) (fl : Bool) (hwm : Nat) (st' : MapSt) (m' : OsMeta),
          writerStF (GF := GF) γ db f fd p mp' fl hwm st' m' ∗
          (⌜fl = false⌝ ∨ (⌜fl = true⌝ ∗ dbFailed (GF := GF) γ))) }}

end spec

end bboltfs
end EtcdGrove
end Perennial

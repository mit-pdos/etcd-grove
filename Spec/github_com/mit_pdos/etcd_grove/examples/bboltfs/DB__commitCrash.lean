/- Lean-first (no Rocq counterpart). `db.commit(m, v)`'s crash-aware spec: `DB.commit.spec`
(`DB__commit.lean`) over the crash invariant of the database file (`csInv dbCrashN p γc (dbOk p)`,
`DBCrash.lean`): the writer's part is `writerStC` (`writerSt` with `writerFileC`), `metalock`'s
resource `metaRC`, and on success `rwlock`'s resource is `rwRC`. Each file operation keeps the
invariant's states `dbOk` (the `*_okS` lemmas of `CrashImg.lean`); the new current root page
satisfies `BootMinibolt`'s check (`bootOk`, a premise: `Commit` has it from `isDBC`'s `vpBoot`),
which the next `commitClean` needs. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB__commit
public import Proof.github_com.mit_pdos.etcd_grove.examples.bboltfs.DBCrash

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

/-- `writerSt` over the crash invariant `γc`: with `writerFileC`, the writer's state of the file
`m`, `bs`. -/
def writerStC (γ : DBNames) (γc : GName) (db f : Loc) (fd : w64) (p : GoString) (mp : List w8)
    (fl : Bool) (hwm : Nat) (st : MapSt) (m : OsMeta) (bs : List (w8 × Bool)) : IProp GF :=
  iprop(ghostVar γ.cur (1 : Qp).half.half (mp, fl, hwm) ∗ ghostVar γ.map (1 : Qp).half st ∗
    ghostVar γ.out (1 : Qp).half.half false ∗ mapFields (GF := GF) db (DFrac.own (1 : Qp).half) st ∗
    writerFileC (GF := GF) γc db f fd p mp fl hwm st m bs ∗ ghostVar γ.cls (1 : Qp).half false ∗
    match st with
    | some (base, len, γm) =>
      ⌜m.maps = {[base := len]} ∧ m.size ≤ len ∧ 0 < base.addr ∧ len ≤ 2 ^ 41⌝ ∗
      ghostVar γm (1 : Qp).half () ∗ mapInv (GF := GF) γ p base len γm ∗
      writerCells (GF := GF) base hwm len
    | none => writerExtra (GF := GF) γ f fd p mp fl hwm)

/-- `writerStF` over the crash invariant `γc`. -/
def writerStFC (γ : DBNames) (γc : GName) (db f : Loc) (fd : w64) (p : GoString) (mp : List w8)
    (fl : Bool) (hwm : Nat) (st : MapSt) (m : OsMeta) (bs : List (w8 × Bool)) : IProp GF :=
  iprop(ghostVar γ.cur (1 : Qp).half.half (mp, fl, hwm) ∗ ghostVar γ.map (1 : Qp).half st ∗
    ghostVar γ.out (1 : Qp).half.half false ∗ mapFields (GF := GF) db (DFrac.own (1 : Qp).half) st ∗
    writerFileC (GF := GF) γc db f fd p mp true hwm st m bs ∗ ghostVar γ.cls (1 : Qp).half false ∗
    match st with
    | some (base, len, γm) =>
      ⌜m.maps = {[base := len]} ∧ m.size ≤ len ∧ 0 < base.addr ∧ len ≤ 2 ^ 41⌝ ∗
      ghostVar γm (1 : Qp).half () ∗ mapInv (GF := GF) γ p base len γm ∗
      writerCells (GF := GF) base hwm len
    | none => writerExtra (GF := GF) γ f fd p mp fl hwm)

/-- See the file header. -/
abbrev DB.commit.specCrash : Prop :=
  ∀ (γ : DBNames) (γc : GName) (db f : Loc) (fd : w64) (p : GoString) (mp : List w8) (st : MapSt)
    (m : OsMeta) (bs : List (w8 × Bool)) (v : w64),
  metaPagesOk mp → (curMeta mp).txid'.toNat + 1 < 2 ^ 64 → (curPgid mp + 2) * 4096 ≤ 2 ^ 30 →
  m.ok = true → st ≠ none → γ.vp ((curMeta mp).txid'.toNat + 1) (some v) →
  bootOk ((curMeta mp).txid'.toNat + 1) (some v) →
  {{ pkgFacts (GF := GF) ∗ osInv (GF := GF) ∗ csInv (GF := GF) dbCrashN p γc (dbOk p) ∗
      db.[DB, go!"file"] ↦□ f ∗
      sync.isMutex db.[DB, go!"metalock"] (metaRC (GF := GF) γ db p) ∗
      sync.isRWMutexGuard db.[DB, go!"mmaplock"] (mapR (GF := GF) γ db f fd p) ∗
      writerStC (GF := GF) γ γc db f fd p mp false (curPgid mp) st m bs ∗
      dbOwner (GF := GF) γ (curMeta mp).txid'.toNat (curPgid mp) }}
    (App (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"commit")) (Val #(curMeta mp)))
      (Val #v))
  {{ (err : GoInterface), RET #err;
      (⌜err = interface.nil⌝ ∗ rwRC (GF := GF) γ γc db f fd p ∗
          dbOwner (GF := GF) γ ((curMeta mp).txid'.toNat + 1) (curPgid mp + 1) ∗
          dbTx (GF := GF) γ ((curMeta mp).txid'.toNat + 1) (some v) ∗
          dbLast (GF := GF) γ ((curMeta mp).txid'.toNat + 1)) ∨
      (⌜err ≠ interface.nil⌝ ∗ (∃ n', dbOwner (GF := GF) γ (curMeta mp).txid'.toNat n') ∗
        ∃ (mp' : List w8) (fl : Bool) (hwm : Nat) (st' : MapSt) (m' : OsMeta)
          (bs' : List (w8 × Bool)),
          writerStFC (GF := GF) γ γc db f fd p mp' fl hwm st' m' bs' ∗
          (⌜fl = false⌝ ∨ (⌜fl = true⌝ ∗ dbFailed (GF := GF) γ))) }}

end spec

end bboltfs
end EtcdGrove
end Perennial

/- Lean-first (no Rocq counterpart). `db.mmap(minsz)` (`examples/bboltfs/minibolt.go`, db.go's `mmap`): under `mmaplock`'s write lock, unmap (`DB__munmap.lean`), then map `mmapSize` of the larger of the file's size and `minsz`. Its caller is the writer: it holds the writer's part of the file (`writerFile`, as in `rwR`), the writer's halves of the mapping state and fields, and, with a mapping, the writer's half of its invariant's token and the writer's cells; without one, what the new mapping's invariant takes (the invariant's quarter of `cur`, its half of `out`, and the committed pages). The old mapping's invariant is closed and its cells unmapped. On success, the new mapping is `mmaplock`'s, with a new invariant over the committed pages' and the meta pages' cells (`mapCells`, whose bytes the writer's `OsMeta` shows), and the writer has its cells; on an error, there is no mapping, and the writer has the invariant's quarter of `cur` back. -/
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

/-- What the writer holds of the mapping in the state `st`, for `mmap` (see the file header). -/
def mmapPre (γ : DBNames) (p : GoString) (mp : List w8) (fl : Bool) (hwm : Nat) (m : OsMeta) :
    MapSt → IProp GF
  | some (base, len, γm) =>
    iprop(⌜m.maps = {[base := len]} ∧ m.size ≤ len ∧ 0 < base.addr ∧ len ≤ 2 ^ 41⌝ ∗
      ghostVar γm (1 : Qp).half () ∗ writerCells (GF := GF) base hwm len)
  | none =>
    iprop(⌜m.maps = ∅⌝ ∗ ghostVar γ.cur (1 : Qp).half.half (mp, fl, hwm) ∗
      ghostVar γ.out (1 : Qp).half false ∗
      [∗list] r ∈ List.range' 2 (hwm - 2), ∃ B, pageIs (GF := GF) p r B)

/-- See the file header. -/
abbrev DB.mmap.spec : Prop :=
  ∀ (γ : DBNames) (db f : Loc) (fd : w64) (p : GoString) (minsz : w64) (mp : List w8) (fl : Bool)
    (hwm : Nat) (st : MapSt) (m : OsMeta),
  0 ≤ sint.Z minsz → sint.Z minsz ≤ 2 ^ 40 → m.size ≤ 2 ^ 40 →
  {{ pkgFacts (GF := GF) ∗
      osInv (GF := GF) ∗ db.[DB, go!"file"] ↦□ f ∗
      sync.isRWMutexGuard db.[DB, go!"mmaplock"] (mapR (GF := GF) γ db f fd p) ∗
      ghostVar γ.cur (1 : Qp).half.half (mp, fl, hwm) ∗ ghostVar γ.map (1 : Qp).half st ∗
      ghostVar γ.out (1 : Qp).half.half false ∗ mapFields (GF := GF) db (DFrac.own (1 : Qp).half) st ∗
      writerFile (GF := GF) γ db f fd p mp fl hwm st m ∗ mmapPre (GF := GF) γ p mp fl hwm m st }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"mmap")) (Val #minsz))
  {{ (err : GoInterface), RET #err; ∃ (st' : MapSt) (m' : OsMeta),
      ghostVar γ.cur (1 : Qp).half.half (mp, fl, hwm) ∗ ghostVar γ.map (1 : Qp).half st' ∗
      ghostVar γ.out (1 : Qp).half.half false ∗ mapFields (GF := GF) db (DFrac.own (1 : Qp).half) st' ∗
      writerFile (GF := GF) γ db f fd p mp fl hwm st' m' ∗ ⌜m'.size = m.size⌝ ∗
      ((⌜err = interface.nil⌝ ∗ ∃ (base : Loc) (len : Nat) (γm : GName),
          ⌜st' = some (base, len, γm) ∧ m'.maps = {[base := len]} ∧ m.size ≤ len ∧
            sint.Z minsz ≤ len ∧ 0 < base.addr ∧ len ≤ 2 ^ 41⌝ ∗
          ghostVar γm (1 : Qp).half () ∗ writerCells (GF := GF) base hwm len) ∨
       (⌜err ≠ interface.nil ∧ st' = none⌝ ∗ ghostVar γ.cur (1 : Qp).half.half (mp, fl, hwm))) }}

end spec

end bboltfs
end EtcdGrove
end Perennial

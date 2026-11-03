/- Lean-first (no Rocq counterpart). `db.mmap(minsz)`'s crash-aware spec: `DB.mmap.spec`
(`DB__mmap.lean`) with the writer's part of the file over the crash invariant (`writerFileC`,
`DBCrash.lean`) in place of `writerFile`. The bytes of the writer's state do not change, only its
mappings (`Mmap.specCrashS`/`Munmap.specCrashS`, whose obligations `writer_okS` discharges). -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB__mmap
public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB__munmapCrash

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

/-- See the file header. -/
abbrev DB.mmap.specCrash : Prop :=
  ∀ (γ : DBNames) (γc : GName) (db f : Loc) (fd : w64) (p : GoString) (minsz : w64) (mp : List w8)
    (fl : Bool) (hwm : Nat) (st : MapSt) (m : OsMeta) (bs : List (w8 × Bool)),
  fl = false → 0 ≤ sint.Z minsz → sint.Z minsz ≤ 2 ^ 30 →
  {{ pkgFacts (GF := GF) ∗
      osInv (GF := GF) ∗ csInv (GF := GF) dbCrashN p γc (dbOk p) ∗ db.[DB, go!"file"] ↦□ f ∗
      sync.isRWMutexGuard db.[DB, go!"mmaplock"] (mapR (GF := GF) γ db f fd p) ∗
      ghostVar γ.cur (1 : Qp).half.half (mp, fl, hwm) ∗ ghostVar γ.map (1 : Qp).half st ∗
      ghostVar γ.out (1 : Qp).half.half false ∗ mapFields (GF := GF) db (DFrac.own (1 : Qp).half) st ∗
      writerFileC (GF := GF) γc db f fd p mp fl hwm st m bs ∗ mmapPre (GF := GF) γ f fd p mp fl hwm m st }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"mmap")) (Val #minsz))
  {{ (err : GoInterface), RET #err; ∃ (st' : MapSt) (m' : OsMeta),
      ghostVar γ.cur (1 : Qp).half.half (mp, fl, hwm) ∗ ghostVar γ.map (1 : Qp).half st' ∗
      ghostVar γ.out (1 : Qp).half.half false ∗ mapFields (GF := GF) db (DFrac.own (1 : Qp).half) st' ∗
      writerFileC (GF := GF) γc db f fd p mp fl hwm st' m' bs ∗
      ⌜m'.size = m.size ∧ m'.ok = m.ok ∧ m'.hi = m.hi ∧ m'.lo = m.lo⌝ ∗
      ((⌜err = interface.nil⌝ ∗ ∃ (base : Loc) (len : Nat) (γm : GName),
          ⌜st' = some (base, len, γm) ∧ m'.maps = {[base := len]} ∧ m.size ≤ len ∧
            sint.Z minsz ≤ len ∧ 0 < base.addr ∧ len ≤ 2 ^ 41⌝ ∗
          ghostVar γm (1 : Qp).half () ∗ mapInv (GF := GF) γ p base len γm ∗
          writerCells (GF := GF) base hwm len) ∨
       (⌜err ≠ interface.nil ∧ st' = none⌝ ∗ writerExtra (GF := GF) γ f fd p mp fl hwm)) }}

end spec

end bboltfs
end EtcdGrove
end Perennial

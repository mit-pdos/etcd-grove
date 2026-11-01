/- Lean-first (no Rocq counterpart). `db.munmap()` (`examples/bboltfs/minibolt.go`, bolt_unix.go's `munmap` with `db.invalidate`): with no mapping (`dataref` nil), nil; with one, `unix.Munmap` of it (all its cells' client halves and the whole of the file's `OsMeta`), whose result it returns. Afterwards `dataref` is nil, and, after an unmap, `datasz` is 0 and the meta pointers nil. -/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.bboltfs.Store
public import Proof.syscall.Base

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

/-- The mapping `db.dataref` holds: none (`slice.nil`), or a whole mapping `⟨base, len, len⟩` of
the file `p`, with the whole of its `OsMeta` `m` and its cells' client halves. -/
def mappingRes (p : GoString) (m : OsMeta) (sl : GoSlice) : IProp GF :=
  iprop(⌜sl = slice.nil⌝ ∨
    ∃ (base : Loc) (len : w64) (vf : Nat → val),
      ⌜sl = ⟨base, len, len⟩ ∧ 0 < base.addr ∧ 0 < len.toInt ∧ m.maps !! base = some len.toNat⌝ ∗
      osInv (GF := GF) ∗ osMeta (GF := GF) p (DFrac.own 1) (some m) ∗
      cellsR (GF := GF) base 0 len.toNat vf)

/-- What is left of a mapping (`mappingRes p m sl`) after `munmap` returns `err`. -/
def unmappedRes (p : GoString) (m : OsMeta) (sl : GoSlice) (err : GoInterface) : IProp GF :=
  iprop(⌜sl = slice.nil ∧ err = interface.nil⌝ ∨
    ∃ (base : Loc) (len : w64) (vf : Nat → val) (e : w64),
      ⌜sl = ⟨base, len, len⟩ ∧ err = errnoErr e⌝ ∗
      ((⌜e = 0⌝ ∗ osMeta (GF := GF) p (DFrac.own 1) (some { m with maps := GMap.delete base m.maps })) ∨
       (⌜e ≠ 0⌝ ∗
         (osMeta (GF := GF) p (DFrac.own 1) (some { m with maps := GMap.delete base m.maps }) ∨
          (osMeta (GF := GF) p (DFrac.own 1) (some m) ∗ cellsR (GF := GF) base 0 len.toNat vf)))))

/-- See the file header. -/
abbrev DB.munmap.spec : Prop :=
  ∀ (db : Loc) (sl : GoSlice) (dsz : w64) (m0 m1 : Loc) (p : GoString) (m : OsMeta),
  {{ db.[DB, go!"dataref"] ↦ sl ∗ db.[DB, go!"datasz"] ↦ dsz ∗ db.[DB, go!"meta0"] ↦ m0 ∗
      db.[DB, go!"meta1"] ↦ m1 ∗ mappingRes (GF := GF) p m sl }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"munmap")) (Val #()))
  {{ (err : GoInterface), RET #err; db.[DB, go!"dataref"] ↦ slice.nil ∗
      db.[DB, go!"datasz"] ↦ (if sl = slice.nil then dsz else W64 0) ∗
      db.[DB, go!"meta0"] ↦ (if sl = slice.nil then m0 else null) ∗
      db.[DB, go!"meta1"] ↦ (if sl = slice.nil then m1 else null) ∗
      unmappedRes (GF := GF) p m sl err }}

end spec

end bboltfs
end EtcdGrove
end Perennial

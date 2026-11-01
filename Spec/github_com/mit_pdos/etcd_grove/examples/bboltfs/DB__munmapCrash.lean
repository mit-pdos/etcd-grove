/- Lean-first (no Rocq counterpart). `db.munmap()`'s crash-aware spec: `DB.munmap.spec`
(`DB__munmap.lean`) with the writer's part of the file as an idle state of the crash invariant
(`csOwn`, `DBCrash.lean`) in place of the whole `OsMeta`. The state is one a commit may start from
(`commitClean`), so that every mapping change keeps it `dbOk` (`writer_okS`). -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB__munmap
public import Proof.github_com.mit_pdos.etcd_grove.examples.bboltfs.DBCrash
public import Spec.os.CrashSt

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bboltfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.bboltfs

theorem dbCrashN_disj : ↑osN ⊆ (⊤ : CoPset) \ ↑dbCrashN :=
  mask_ndot_ne' nroot "osfs" "minibolt_crash" (by decide)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.bboltfs.Assumptions]

/-- The mapping `sl` of the file `p` (`mappingRes`), over the crash invariant `γc`: the writer's
idle state `⟨m, bs, fa, fb⟩`, one a commit may start from. -/
def mappingResC (p : GoString) (γc : GName) (m : OsMeta) (bs : List (w8 × Bool)) (fa fb : Nat)
    (sl : GoSlice) : IProp GF :=
  iprop(⌜sl = slice.nil⌝ ∨
    ∃ (base : Loc) (len : w64) (vf : Nat → val),
      ⌜sl = ⟨base, len, len⟩ ∧ 0 < base.addr ∧ 0 < len.toInt ∧ m.maps !! base = some len.toNat ∧
        bs.length = m.size ∧ commitClean m bs⌝ ∗
      osInv (GF := GF) ∗ csInv (GF := GF) dbCrashN p γc (dbOk p) ∗
      csOwn (GF := GF) p γc (some ⟨m, bs, fa, fb, .idle⟩) ∗
      cellsR (GF := GF) base 0 len.toNat vf)

/-- What is left of a mapping (`mappingResC`) after `munmap` returns `err`. -/
def unmappedResC (p : GoString) (γc : GName) (m : OsMeta) (bs : List (w8 × Bool)) (fa fb : Nat)
    (sl : GoSlice) (err : GoInterface) : IProp GF :=
  iprop(⌜sl = slice.nil ∧ err = interface.nil⌝ ∨
    ∃ (base : Loc) (len : w64) (vf : Nat → val) (e : w64),
      ⌜sl = ⟨base, len, len⟩ ∧ err = errnoErr e⌝ ∗
      ((⌜e = 0⌝ ∗
          csOwn (GF := GF) p γc (some ⟨{ m with maps := GMap.delete base m.maps }, bs, fa, fb, .idle⟩)) ∨
       (⌜e ≠ 0⌝ ∗
         (csOwn (GF := GF) p γc (some ⟨{ m with maps := GMap.delete base m.maps }, bs, fa, fb, .idle⟩) ∨
          (csOwn (GF := GF) p γc (some ⟨m, bs, fa, fb, .idle⟩) ∗
            cellsR (GF := GF) base 0 len.toNat vf)))))

/-- See the file header. -/
abbrev DB.munmap.specCrash : Prop :=
  ∀ (db : Loc) (dq : DFrac) (sl : GoSlice) (dsz : w64) (m0 m1 : Loc) (p : GoString) (γc : GName)
    (m : OsMeta) (bs : List (w8 × Bool)) (fa fb : Nat),
  (sl ≠ slice.nil → dq = DFrac.own 1) →
  {{ db.[DB, go!"dataref"] ↦{dq} sl ∗ db.[DB, go!"datasz"] ↦{dq} dsz ∗ db.[DB, go!"meta0"] ↦{dq} m0 ∗
      db.[DB, go!"meta1"] ↦{dq} m1 ∗ mappingResC (GF := GF) p γc m bs fa fb sl }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"munmap")) (Val #()))
  {{ (err : GoInterface), RET #err; db.[DB, go!"dataref"] ↦{dq} slice.nil ∗
      db.[DB, go!"datasz"] ↦{dq} (if sl = slice.nil then dsz else W64 0) ∗
      db.[DB, go!"meta0"] ↦{dq} (if sl = slice.nil then m0 else null) ∗
      db.[DB, go!"meta1"] ↦{dq} (if sl = slice.nil then m1 else null) ∗
      unmappedResC (GF := GF) p γc m bs fa fb sl err }}

end spec

end bboltfs
end EtcdGrove
end Perennial

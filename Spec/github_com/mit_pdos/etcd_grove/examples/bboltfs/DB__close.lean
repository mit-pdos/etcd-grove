/- Lean-first (no Rocq counterpart). `db.close()` (`examples/bboltfs/minibolt.go`): `munmap` (`DB__munmap.lean`), then `Flock(fd, LOCK_UN)` and `Close` of `db.file`, ignoring their errors. The mapping fields may be held at any fraction when there is no mapping (as `munmap`). With the whole of the file and its fd, it leaves the file closed (`fd` -1) and the mapping unmapped as `munmap` does. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB__munmap
public import Proof.os.Base

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
abbrev DB.close.spec : Prop :=
  ∀ (db : Loc) (dq : DFrac) (sl : GoSlice) (dsz : w64) (m0 m1 f : Loc) (dqd : DFrac) (fd : w64)
    (name : GoString) (d : OsFd) (p : GoString) (m : OsMeta),
  (sl ≠ slice.nil → dq = DFrac.own 1) →
  {{ osInv (GF := GF) ∗ db.[DB, go!"dataref"] ↦{dq} sl ∗ db.[DB, go!"datasz"] ↦{dq} dsz ∗
      db.[DB, go!"meta0"] ↦{dq} m0 ∗ db.[DB, go!"meta1"] ↦{dq} m1 ∗ mappingRes (GF := GF) p m sl ∗
      db.[DB, go!"file"] ↦{dqd} f ∗ os.ownFile (GF := GF) f fd name (DFrac.own 1) ∗
      osFd (GF := GF) fd (DFrac.own 1) d }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"close")) (Val #()))
  {{ RET #(); db.[DB, go!"dataref"] ↦{dq} slice.nil ∗
      (∃ (dsz' : w64) (m0' m1' : Loc), db.[DB, go!"datasz"] ↦{dq} dsz' ∗
        db.[DB, go!"meta0"] ↦{dq} m0' ∗ db.[DB, go!"meta1"] ↦{dq} m1') ∗
      (∃ err, unmappedRes (GF := GF) p m sl err) ∗
      db.[DB, go!"file"] ↦{dqd} f ∗ os.ownFile f (-1 : w64) name (DFrac.own 1) }}

end spec

end bboltfs
end EtcdGrove
end Perennial

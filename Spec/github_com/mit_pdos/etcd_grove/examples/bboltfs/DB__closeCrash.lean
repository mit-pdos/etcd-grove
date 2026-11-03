/- Lean-first (no Rocq counterpart). `db.close()`'s crash-aware spec: `DB.close.spec`
(`DB__close.lean`) with the mapping over the crash invariant (`mappingResC`/`unmappedResC`,
`DB__munmapCrash.lean`). -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB__close
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
abbrev DB.close.specCrash : Prop :=
  ∀ (db : Loc) (dq : DFrac) (sl : GoSlice) (dsz : w64) (m0 m1 f : Loc) (dqd : DFrac) (fd : w64)
    (name : GoString) (d : OsFd) (p : GoString) (γc : GName) (m : OsMeta) (bs : List (w8 × Bool))
    (fa fb : Nat),
  (sl ≠ slice.nil → dq = DFrac.own 1) →
  {{ osInv (GF := GF) ∗ db.[DB, go!"dataref"] ↦{dq} sl ∗ db.[DB, go!"datasz"] ↦{dq} dsz ∗
      db.[DB, go!"meta0"] ↦{dq} m0 ∗ db.[DB, go!"meta1"] ↦{dq} m1 ∗
      mappingResC (GF := GF) p γc m bs fa fb sl ∗
      db.[DB, go!"file"] ↦{dqd} f ∗ os.ownFile (GF := GF) f fd name (DFrac.own 1) ∗
      osFd (GF := GF) fd (DFrac.own 1) d }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"close")) (Val #()))
  {{ (err : GoInterface), RET #err; db.[DB, go!"dataref"] ↦{dq} slice.nil ∗
      db.[DB, go!"datasz"] ↦{dq} (if sl = slice.nil then dsz else W64 0) ∗
      db.[DB, go!"meta0"] ↦{dq} (if sl = slice.nil then m0 else null) ∗
      db.[DB, go!"meta1"] ↦{dq} (if sl = slice.nil then m1 else null) ∗
      (∃ err', unmappedResC (GF := GF) p γc m bs fa fb sl err' ∗
        ⌜err = interface.nil → err' = interface.nil⌝) ∗
      db.[DB, go!"file"] ↦{dqd} f ∗ os.ownFile f (-1 : w64) name (DFrac.own 1) }}

end spec

end bboltfs
end EtcdGrove
end Perennial

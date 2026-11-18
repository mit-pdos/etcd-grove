/-
`DB.munmap.spec`, out of `Munmap.lean`'s proof so that the open and close modules (`Open/Close.lean`)
import it without the proof (import tiers, 2026-11-18).
-/
module

public import Proof.go_etcd_io.bbolt.Mmap.ErrPtr
public import Proof.go_etcd_io.bbolt.Mmap.LoggerDefs
public import Proof.go_etcd_io.bbolt.Mmap.Infra
public import Proof.go_etcd_io.bbolt.Mmap.FileSizeDefs
public import Spec.fmt.Errorf

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section munmap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **`db.munmap()` of the mapping `base`/`l`** (whole: the mapping fields, `datasz` and every
cell's client half): the fields cleared (`mapFields … none`, `datasz` 0); the mapping gone from
OsFs, or, on an error (`fmtErrorOk`), possibly still there with its cells. -/
abbrev DB.munmap.spec : Prop :=
  ∀ (db base : Loc) (l : Nat) (lg : GoInterface) (p : BFile) (m : OsMeta) (vf : Nat → val),
  db ≠ null → 0 < l → m.maps !! base = some l →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ osInv (GF := GF) ∗
      db.[DB, go!"logger"] ↦□ lg ∗ boltLogger lg ∗
      mapFields db (DFrac.own 1) (some (base, l)) ∗ db.[DB, go!"datasz"] ↦ W64 (l : Int) ∗
      osMeta p.ino (DFrac.own 1) m ∗ cellsR (GF := GF) base 0 l vf }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"munmap")) (Val #()))
  {{ (err : GoInterface), RET #err;
      mapFields db (DFrac.own 1) (none : MapSt) ∗ db.[DB, go!"datasz"] ↦ W64 0 ∗
      ((⌜err = interface.nil⌝ ∗
          osMeta p.ino (DFrac.own 1) { m with maps := GMap.delete base m.maps }) ∨
       (⌜err ≠ interface.nil ∧ errPtrTyped err⌝ ∗ fmtErrorOk err ∗
        (osMeta p.ino (DFrac.own 1) { m with maps := GMap.delete base m.maps } ∨
         (osMeta p.ino (DFrac.own 1) m ∗ cellsR base 0 l vf)))) }}

end munmap

end bbolt
end EtcdGrove
end Perennial

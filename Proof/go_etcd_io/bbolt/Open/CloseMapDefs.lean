/-
What `close` unmaps and gives back (`closeMapResM`, `closeKeep`, `closeMapBack`), moved unchanged out
of the proof file `CloseFile.lean` (import tiers, 2026-11-19: `Congr.lean`'s congruence lemmas name
`closeKeep`, and a proof file is imported by linking modules only).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.CloseImage
public import Proof.go_etcd_io.bbolt.Mmap.Cells

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section closeM
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- What `close` unmaps, the file's `OsMeta` `m` named (`closeMapRes`, whose `m` is hidden). -/
def closeMapResM (p : BFile) (m : OsMeta) : MapSt → IProp GF
  | none => iprop(emp)
  | some (b, l) => iprop(⌜0 < l ∧ m.maps !! b = some l⌝ ∗ osMeta p.ino (DFrac.own 1) m ∗
      ∃ vf, cellsR b 0 l vf)

/-- The file's `OsMeta` the closer keeps when nothing is mapped (`close` takes it otherwise). -/
def closeKeep (p : BFile) (m : OsMeta) : MapSt → IProp GF
  | none => iprop(osMeta p.ino (DFrac.own 1) m)
  | some _ => iprop(emp)

/-- What `close`'s unmapping gives back: the `OsMeta` with the mapping removed. -/
def closeMapBack (p : BFile) (m : OsMeta) : MapSt → IProp GF
  | none => iprop(emp)
  | some (b, _) => iprop(osMeta p.ino (DFrac.own 1) { m with maps := GMap.delete b m.maps })

end closeM

end bbolt
end EtcdGrove
end Perennial

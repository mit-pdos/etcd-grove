/-
`Open`'s `hasSyncedFreelist()` after `loadFreelist` (U11g): the mapping's fields and the meta
cells' quarter it reads, out of the idle writer side `wdbCore`, and back.
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Locks

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section s
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

theorem wdbCore_meta_acc (B : BNs) (db : Loc) (p : GoString) (w : WDb) :
    wdbCore (GF := GF) B db p w ⊢
      mapFields db (DFrac.own (1 : Qp).half) w.ms ∗ metaCellsQ (1 : Qp).half.half w.ms w.C ∗
      (mapFields db (DFrac.own (1 : Qp).half) w.ms -∗ metaCellsQ (1 : Qp).half.half w.ms w.C -∗
        wdbCore B db p w) := by
  unfold wdbCore wdbCoreG
  iintro ⟨Hcur, Hfl, Hmap, Hout, Hwv, Hfli, Hop, Hwa, Hrw, Hf, Hp, Hds, Hmf, Hom, Hfo, Hfd, Hmq,
    Hrest⟩
  iframe Hmf Hmq
  iintro Hmf Hmq
  iframe

end s

end bbolt
end EtcdGrove
end Perennial

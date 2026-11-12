/-
`Open`'s `hasSyncedFreelist()` after `loadFreelist` (U11g): the mapping's fields and the meta
cells' quarter it reads, out of the idle writer side `wdbCore`, and back. And `Open`'s
`fdatasync(db)` (bbolt `ea4cab52`, issues/bbolt-open-unsynced-meta-kill-then-power-loss.md): the
file's resources, out of `wdbCore` and back with the file's metadata changed but its size and
mappings (`fdatasync.spec`); `wdbOK` reads only those.
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

/-- `wdbOK` after the file's metadata changed but its size and mappings. -/
theorem wdbOK_withMeta (w : WDb) (m' : OsMeta) (hs : m'.size = w.m.size)
    (hm : m'.maps = w.m.maps) (h : wdbOK w) : wdbOK { w with m := m' } := by
  unfold wdbOK at h ⊢
  simpa only [hs, hm] using h

/-- The file's resources (`fdatasync`'s), out of the idle writer side and back, with the file's
metadata `m'` of the same size. -/
theorem wdbCore_file_acc (B : BNs) (db : Loc) (p : GoString) (w : WDb) :
    wdbCore (GF := GF) B db p w ⊢
      db.[DB, go!"file"] ↦ w.f ∗ fileOwn w.f w.fd p (DFrac.own 1) ∗
      osFd w.fd (DFrac.own 1) ⟨p, true, true⟩ ∗ osMeta p (DFrac.own 1) (some w.m) ∗
      (∀ m' : OsMeta, ⌜m'.size = w.m.size⌝ -∗ db.[DB, go!"file"] ↦ w.f -∗
        fileOwn w.f w.fd p (DFrac.own 1) -∗ osFd w.fd (DFrac.own 1) ⟨p, true, true⟩ -∗
        osMeta p (DFrac.own 1) (some m') -∗ wdbCore B db p { w with m := m' }) := by
  unfold wdbCore wdbCoreG
  iintro ⟨Hcur, Hfl, Hmap, Hout, Hwv, Hfli, Hop, Hwa, Hrw, Hf, Hp, Hds, Hmf, Hom, Hfo, Hfd, Hmq,
    Hmb, Hwc, Hwb, Hj⟩
  iframe Hf Hfo Hfd Hom
  iintro %m' %hs Hf Hfo Hfd Hom
  simp only [hs]
  iframe

end s

end bbolt
end EtcdGrove
end Perennial

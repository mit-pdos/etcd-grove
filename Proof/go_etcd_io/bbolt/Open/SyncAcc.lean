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

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section s
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

theorem wdbCore_meta_acc (B : BNs) (db : Loc) (p : BFile) (w : WDb) :
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
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h
  refine ⟨?_, ?_, ?_, ?_, h5, h6, h7, h8, h9, ?_, h11, h12, h13.congr hs rfl, ?_, ?_, ?_, h17⟩ <;>
    simp only [hs, hm] <;> assumption

/-- The file's resources (`fdatasync`'s), out of the idle writer side and back, with the file's
metadata `m'` of the same size. -/
theorem wdbCore_file_acc (B : BNs) (db : Loc) (p : BFile) (w : WDb) :
    wdbCore (GF := GF) B db p w ⊢
      db.[DB, go!"file"] ↦{DFrac.own (1 : Qp).half} w.f ∗ fileOwn w.f w.fd p.path (DFrac.own (1 : Qp).half) ∗
      osFd w.fd (DFrac.own (1 : Qp).half) (dbFd p.ino) ∗ bMeta p w.C [] w.m ∗
      (∀ m' : OsMeta, ⌜m'.size = w.m.size⌝ -∗ db.[DB, go!"file"] ↦{DFrac.own (1 : Qp).half} w.f -∗
        fileOwn w.f w.fd p.path (DFrac.own (1 : Qp).half) -∗ osFd w.fd (DFrac.own (1 : Qp).half) (dbFd p.ino) -∗
        bMeta p w.C [] m' -∗ wdbCore B db p { w with m := m' }) := by
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

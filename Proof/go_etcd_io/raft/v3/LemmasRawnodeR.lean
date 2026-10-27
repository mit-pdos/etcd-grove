/-
Lemmas of group G1 of stage R5 phase 3 (the `RawNode` API, `confChangeToMsg`, the storage
acknowledgements): building the messages the node layer steps.
-/
module

public import Proof.go_etcd_io.raft.v3.InvPbMsg
public import Proof.go_etcd_io.raft.v3.LemmasSendR
public import Proof.go_etcd_io.raft.v3.InvPbLog

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `m.Index = new(last.index)` (`newStorageAppendRespMsg`, `rawnode.go:342`). -/
theorem msgPtsC_store_Index (l : Loc) (dqe : DFrac) (cap : Bool) (ms : MsgSt) :
    msgPtsC (GF := GF) l (DFrac.own 1) dqe cap ms ⊢
      ∃ p : Loc, l.[raftpb.Message, go!"Index"] ↦ p ∗
        (∀ (p' : Loc) (v : w64), l.[raftpb.Message, go!"Index"] ↦ p' -∗ cellRO p' v -∗
          msgPtsC l (DFrac.own 1) dqe cap { ms with msg := { ms.msg with Index' := v } }) := by
  iintro H
  iNamed H
  iexists pix
  iframe HIx
  iintro %p' %v HIx #cIx'
  iunfold msgPtsC
  iexists pty, pto, pfr, pte, plt, p', pco, pvo, prj, prh, es, els, ps, cs, rs, uf
  isplitr
  · ipureintro; exact Hnn
  iframe
  iframe cTy cTo cFr cTe cLt cIx' cCo cVo cRj cRh Hents Hcs Hpb

/-- `m.LogTerm = new(last.term)` (`newStorageAppendRespMsg`, `rawnode.go:343`). -/
theorem msgPtsC_store_LogTerm (l : Loc) (dqe : DFrac) (cap : Bool) (ms : MsgSt) :
    msgPtsC (GF := GF) l (DFrac.own 1) dqe cap ms ⊢
      ∃ p : Loc, l.[raftpb.Message, go!"LogTerm"] ↦ p ∗
        (∀ (p' : Loc) (v : w64), l.[raftpb.Message, go!"LogTerm"] ↦ p' -∗ cellRO p' v -∗
          msgPtsC l (DFrac.own 1) dqe cap { ms with msg := { ms.msg with LogTerm' := v } }) := by
  iintro H
  iNamed H
  iexists plt
  iframe HLt
  iintro %p' %v HLt #cLt'
  iunfold msgPtsC
  iexists pty, pto, pfr, pte, p', pix, pco, pvo, prj, prh, es, els, ps, cs, rs, uf
  isplitr
  · ipureintro; exact Hnn
  iframe
  iframe cTy cTo cFr cTe cLt' cIx cCo cVo cRj cRh Hents Hcs Hpb

/-- (D22 S-d3a, 2026-10-21) `m.Snapshot = rd.Snapshot` (`newStorageAppendRespMsg`, `rawnode.go:349`):
the field stored; the message's snapshot is then the one the pointer holds, once that is owned. -/
theorem msgPtsC_store_Snapshot (l : Loc) (dqe : DFrac) (cap : Bool) (ms : MsgSt) :
    msgPtsC (GF := GF) l (DFrac.own 1) dqe cap ms ⊢
      ∃ p : Loc, l.[raftpb.Message, go!"Snapshot"] ↦ p ∗
        (∀ (p' : Loc) (o : Option SnapshotM), l.[raftpb.Message, go!"Snapshot"] ↦ p' -∗
          snapOpt p' (DFrac.own 1) o -∗ msgPtsC l (DFrac.own 1) dqe cap { ms with snap := o }) := by
  iintro H
  iNamed H
  iexists ps
  iframe HSn
  iintro %p' %o HSn Hsn'
  iunfold msgPtsC
  iexists pty, pto, pfr, pte, plt, pix, pco, pvo, prj, prh, es, els, p', cs, rs, uf
  isplitr
  · ipureintro; exact Hnn
  iframe
  iframe cTy cTo cFr cTe cLt cIx cCo cVo cRj cRh Hents Hcs Hpb

/-- A read-only hard state is one that may be `nil` (`raft.hardState()`'s result handed to
`IsEmptyHardState`/`isHardStateEqual`). -/
theorem hsRO_to_hsOpt (p : Loc) (h : HardStateM) : hsRO (GF := GF) p h ⊢ hsOpt p h := by
  iintro H; unfold hsOpt; iright; iexact H

end lemmas

end EtcdGrove
end Perennial

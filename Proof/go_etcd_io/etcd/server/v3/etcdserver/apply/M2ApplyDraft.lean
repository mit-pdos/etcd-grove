/-
**M2, the apply side: the apply package's compaction arm (Draft, what is left of it)**
(`notes/m2-apply-plan.md`). Imported by nothing but the server's apply-side Draft; no `axiom`, no
`sorry`.

The switch's stages 1-3 (2026-10-31) put this Draft's statements in place: `cmpTriple` in
`applierTriples` and the compaction vocabulary (`Chain.lean`), `applierV3backend.Compaction.spec`,
`dispatchOk` (item 1), the answers with the compaction's case (item 2), `dispatchCrev`/`cmpAdmit`
and A1's record (`ApplyKV.crev`, `applyKV`'s `cmpOwn`, `applyStep`'s crev clause: `InvUber.lean`),
the uber's `dispatch`/`Apply` specs and `apply.Apply.specRec` (items 11, 21). What is left, for the
server's Draft (stage 4):
- `dispatchOkD`, now `dispatchOk` itself (its laws trivial), which the server Draft's copies of the
  shapes are written over;
- `applyCrev` (what `Apply` does to the revision; `applyStep_crev`: `applyStep`'s clause);
- the glue `cmp_not_future` (F-1's argument).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.InvUber
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvCompact
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Compact
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.LockArm
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.ApplyRec
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.CompactArm

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.apply go_etcd_io.etcd.api.v3

namespace apply

/-! ## The pure part -/

/-- **`dispatchOk` as item 1 drafted it** (in place since the switch's stage 3). -/
abbrev dispatchOkD (on : Bool) (rq : IRRModel) : Prop := dispatchOk on rq

theorem dispatchOkD_of (on : Bool) (rq : IRRModel) (h : dispatchOk on rq) : dispatchOkD on rq := h

theorem dispatchOkD_iff (on : Bool) (rq : IRRModel) (_h : dispatchKind rq ≠ .compaction) :
    dispatchOkD on rq ↔ dispatchOk on rq := Iff.rfl

/-- **What `Apply` does to the compaction revision**: a dispatched request's `dispatchCrev`; a
skipped or rejected one nothing. -/
def applyCrev (rq : IRRModel) (v3 : Bool) (c : Chain) (crev : Int) : ApplyOut → Int
  | .dispatched _ _ => dispatchCrev c rq v3 crev
  | _ => crev

/-- `applyStep`'s crev clause, as `applyCrev`. -/
theorem applyStep_crev (rq : IRRModel) (v3 : Bool) (x x' : ApplyKV) (out : ApplyOut)
    (h : applyStep rq v3 x x' out) : x'.crev = applyCrev rq v3 x.chain x.crev out := by
  cases out with
  | skipped => rw [h.2]; rfl
  | rejected => rw [h.2]; rfl
  | dispatched o skip => exact h.2.2.2.2


/-! ## The glue: `store.Compact`'s precondition from the backend's -/

section glue
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- **F-1's argument** (why `store.Compact.spec` and `store.updateCompactRev.spec` drop the
`ErrFutureRev` arm, for the mvcc Probe): in that branch the store holds its committed log's
authority (`revMuBody`'s `idxLogAuth γ.idx (revQ γ q) log`), which extends the caller's certificate
(`idxLogAuth_cert_prefix`), so a revision of the caller's log is one of the committed log's: the
branch's `rev > currentRev = |log| - 1` is contradictory. -/
theorem cmp_not_future (γ : mvcc.IdxNames) (q : Qp) (ilog log : mvcc.Log) (rev : w64) :
    mvcc.idxLogAuth (GF := GF) γ q ilog ∗ mvcc.idxCert γ log ⊢
      ⌜sint.Z rev < log.length → sint.Z rev < ilog.length⌝ := by
  iintro H
  ihave %h := mvcc.idxLogAuth_cert_prefix γ q ilog log $$ H
  ipureintro
  intro hr
  have := h.length_le
  omega

end glue

end apply


end EtcdGrove
end Perennial

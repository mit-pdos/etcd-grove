/-
**A compaction's proposer's facts** (M2; the stage-4c switch of the apply side, 2026-10-31: until then
the compaction mode's family of statements beside the compaction-off ones, `kvInvC`,
`isServerReqC`, `reqPropOkC`, ...; the one KV invariant `kvInv` admits compactions in the cluster's
compaction mode, and `reqPropOk` has their form).

* `srvRevLb`: a revision the store has reached (a certified log longer than it): what a compaction's
  proposer holds of its revision (review round 1, S2-3), and the compactor's `RevLb` on the server;
  read as a committed raft log's model by `kvCert_of_srvRevLb` (G2, the user's (a')), and as the cluster's
  revision reached by `kvRevLb_of_srvRevLb` (the client's `kv.Compact`, 2026-10-31).
* `compactResultIs`: the apply thread's result of a compaction (`applierV3backend.Compaction`
  through the uber-applier), as `EtcdServer.Compact` reads it: the response, or the error the
  request path reports.

Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvProposer
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver


section pure
variable [GooseExts]

/-- **A compaction is within protobuf's recursion limit** (`proto.MarshalIRR`'s premise):
`dispatch` tests `.txn` before `.compaction` (`apply.dispatchKind`), so it has no transaction. -/
theorem irrDepthOk_of_compactPropOk {rq : apply.IRRModel} (h : compactPropOk rq) :
    apply.irrDepthOk rq := by
  apply apply.irrDepthOk_of_txn_none
  apply apply.txn_none_of_dispatchKind
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [h.1.1] <;> decide

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **A revision the store has reached** (persistent): a lower bound of the store's committed
log (`kvLogLb`) longer than it, with the environment's raft witness of it (`E.Nx`: the store's
`Rev` gives both; M2, the apply side, G2 by the user's (a'), 2026-10-31: the server reads it as the
KV's revision reached, `kvRevLb_of_srvRevLb`). (The `lean` merge, 2026-11-06, over mvcc's API: at the
apply environment, the store's floor `kvLogLb E.γs` and the witness `E.Nx` in place of mvcc's
`idxCert γ.idx` and `certOk γ`.) -/
def srvRevLb (E : apply.AEnv GF) (n : Int) : IProp GF :=
  iprop(∃ log : mvcc.Log, srvApi.kvLogLb E.γs log ∗ □ E.Nx log ∗ ⌜n < log.length⌝)

instance srvRevLb_persistent (E : apply.AEnv GF) (n : Int) :
    Persistent (srvRevLb (GF := GF) E n) := by
  unfold srvRevLb; infer_instance

/-- A revision below one the store has reached is reached. -/
theorem srvRevLb_mono (E : apply.AEnv GF) (n m : Int) (h : n ≤ m) :
    srvRevLb (GF := GF) E m ⊢ srvRevLb E n := by
  iintro H
  iunfold srvRevLb at H
  icases H with ⟨%log, #Hc, #Hok, %Hl⟩
  iunfold srvRevLb
  iexists log
  iframe Hc Hok
  ipureintro; omega

/-- **G2, the proposer's reach** (Q3's (a'), the user's, 2026-10-31): a revision the server's store has
reached (`srvRevLb`, the compactor's `RevLb` and `EtcdServer.Compact.spec`'s premise) is a
committed raft log's model longer than it: the store's witness, tied to the KV model's (`kvNxOff`,
`srvKVInvs`'s). (The `lean` merge, 2026-11-06: until then a KV certificate, `kvCert`, from mvcc's
`certOk`.) -/
theorem kvCert_of_srvRevLb (γ : ServerRaftNames) (γk : KVNames) (Ev : apply.AEnv GF)
    (hNx : Ev.Nx = kvNxOff γ γk) (r : w64) :
    srvRevLb (GF := GF) Ev (sint.Z r) ⊢
      □ ∃ A : List EntryModel, srvRLogLb γ A ∗ ⌜sint.Z r < (kvModel γk A).length⌝ := by
  iintro #Hlb
  iunfold srvRevLb at Hlb
  icases Hlb with ⟨%l, -, #Hok, %Hl⟩
  rw [hNx]
  iunfold kvNxOff at Hok
  icases Hok with ⟨%A, #HA, %hA⟩
  imodintro
  iexists A
  iframe HA
  ipureintro; rw [hA]; exact Hl

/-- **A revision the store has reached is the KV's** (the client's `kv.Compact`, 2026-10-31): a
member's `srvRevLb` (its store's witness, `KV.Rev`'s; a `Put`'s reply's) is the cluster's
`kvRevLb`: the witness is the model of a committed raft log (`kvCert_of_srvRevLb`), read on the
cluster's requested log (`srvReqLogLb_of_rlogLb`), whose name the KV invariant ties to the KV's
(`γk.rlog = γ.raft.log`) with the start index below the log's (`c0 ≤ ai0`, `kvModel_eqv`'s gate). -/
theorem kvRevLb_of_srvRevLb (γ : ServerRaftNames) (γk : KVNames) (Ev : apply.AEnv GF)
    (hNx : Ev.Nx = kvNxOff γ γk) (E : CoPset) (hE1 : ↑kvN ⊆ E) (hE3 : ↑srvRaftN ⊆ E)
    (r : w64) :
    ⊢ kvInv (GF := GF) γ γk -∗ srvRaftLogInv γ -∗ srvRevLb Ev (sint.Z r) ={E}=∗
      kvRevLb γk r := by
  iintro #Hkv #Hrl #Hlb
  ihave ⟨%A, #HA, %HAr⟩ := kvCert_of_srvRevLb γ γk Ev hNx r $$ Hlb
  imod (srvReqLogLb_of_rlogLb γ E hE3 A) $$ Hrl HA with ⟨%L₀, #HL0, %Heqv⟩
  iunfold kvInv at Hkv
  iinv Hkv with >Hi Hclose
  icases Hi with ⟨%L, HL, Hσ, %Hok, #Hw, HG⟩
  imod Hclose $$ [HL Hσ HG] with -
  · inext; iexists L; iframe HL Hσ Hw HG; ipureintro; exact Hok
  imodintro
  unfold kvRevLb kvRevLbZ
  iexists L₀
  isplitr
  · rw [Hok.2.2.2.2.2.2.1]; iunfold srvReqLogLb at HL0; iexact HL0
  ipureintro
  rw [← (kvModel_eqv γ γk A L₀ Heqv Hok.2.2.1).1]
  exact HAr

/-- **The result of a compaction** (S2-S3): the apply thread's `*apply.Result`, read-only, with
its trace, if any, owned (`apply.traceRes`: `Compact` uses `result.Trace` before it checks
`result.Err`; on success the applier's trace, on an error a nil one, `apply/backend.go`), and the compaction's response (`*pb.CompactionResponse`, its header if any, owned:
`Compact` writes the revision into it) or the error the request path reports (`applyErrIs`: the
store's `ErrCompacted`; `store.Compact`'s spec excludes its `ErrFutureRev`, M2's item 18). -/
def compactResultIs (res : Loc) : IProp GF :=
  iprop(⌜res ≠ null⌝ ∗ ∃ v : go_etcd_io.etcd.server.v3.etcdserver.apply.Result, res ↦□ v ∗
    apply.traceRes v.Trace' ∗
    ((⌜v.Err' = GoInterface.nil⌝ ∗ ∃ rp : Loc,
        ⌜v.Resp' = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.api.v3.etcdserverpb.CompactionResponse.ty) #rp⌝ ∗
        (⌜rp = null⌝ ∨ ∃ cv : go_etcd_io.etcd.api.v3.etcdserverpb.CompactionResponse, rp ↦ cv ∗
          (⌜cv.Header' = null⌝ ∨ ∃ hv : go_etcd_io.etcd.api.v3.etcdserverpb.ResponseHeader, cv.Header' ↦ hv))) ∨
      (⌜v.Err' ≠ GoInterface.nil⌝ ∗ applyErrIs v.Err')))

end defs

end EtcdGrove
end Perennial

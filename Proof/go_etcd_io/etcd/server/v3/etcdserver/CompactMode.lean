/-
**A compaction's proposer's facts** (M2; the stage-4c switch of the apply side, 2026-10-31: until then
the compaction mode's family of statements beside the compaction-off ones, `kvInvC`,
`isServerReqC`, `reqPropOkC`, ...; the one KV invariant `kvInv` admits compactions in the cluster's
compaction mode, and `reqPropOk` has their form).

* `srvRevLb`: a revision the store has reached (a certified log longer than it): what a compaction's
  proposer holds of its revision (review round 1, S2-3), and the compactor's `RevLb` on the server;
  read as a KV certificate by `cmpReach_of_srvRevLb` (G2, the user's (a')).
* `compactResultIs`: the apply thread's result of a compaction (`applierV3backend.Compaction`
  through the uber-applier), as `EtcdServer.Compact` reads it: the response, or the error the
  request path reports.

Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvProposer

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver


section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **A revision the store has reached** (persistent): a certificate of a log longer than it,
certified by the caller's map (`certOk`: `store.Rev` gives both; M2, the apply side, G2 by the
user's (a'), 2026-10-31: the server reads it as a KV certificate, `cmpReach_of_srvRevLb`). -/
def srvRevLb (γ : mvcc.StoreNames) (n : Int) : IProp GF :=
  iprop(∃ log : mvcc.Log, mvcc.idxCert γ.idx log ∗ mvcc.certOk γ log ∗ ⌜n < log.length⌝)

instance srvRevLb_persistent (γ : mvcc.StoreNames) (n : Int) :
    Persistent (srvRevLb (GF := GF) γ n) := by
  unfold srvRevLb; infer_instance

/-- A revision below one the store has reached is reached. -/
theorem srvRevLb_mono (γ : mvcc.StoreNames) (n m : Int) (h : n ≤ m) :
    srvRevLb (GF := GF) γ m ⊢ srvRevLb γ n := by
  iintro H
  iunfold srvRevLb at H
  icases H with ⟨%log, #Hc, #Hok, %Hl⟩
  iunfold srvRevLb
  iexists log
  iframe Hc Hok
  ipureintro; omega

/-- **G2, the proposer's reach** (Q3's (a'), the user's, 2026-10-31): a revision the server's store has
reached (`srvRevLb`, the compactor's `RevLb` and `EtcdServer.Compact.spec`'s premise) is a
compaction's revision reached (`cmpReach`): the log's `certOk` is a KV certificate, the store's free
one (`0 ↦ []`) excluded by the certificates' invariant (no model log is empty), as in
`kv_cert_read`. -/
theorem cmpReach_of_srvRevLb (γ : ServerRaftNames) (γk : KVNames) (γs : mvcc.StoreNames)
    (hγ : γs.cok = γk.cok) (E : CoPset) (hE : ↑kvcN ⊆ E) (r : w64) :
    ⊢ kvCertInv (GF := GF) γ γk -∗ srvRevLb γs (sint.Z r) ={E}=∗ cmpReach γk r := by
  iintro #Hinv #Hlb
  iunfold srvRevLb at Hlb
  icases Hlb with ⟨%l, -, #Hok, %Hl⟩
  iunfold mvcc.certOk at Hok
  rw [hγ] at *
  icases Hok with (%h | #He | #He)
  · imodintro
    iunfold cmpReach
    iexists l
    isplitr
    · iunfold kvCert; ileft; ipureintro; exact h
    ipureintro; exact Hl
  · imodintro
    iunfold cmpReach
    iexists l
    isplitr
    · iunfold kvCert; iright; iexact He
    ipureintro; exact Hl
  · iunfold kvCertInv at Hinv
    iinv Hinv with >Hi Hclose
    icases Hi with ⟨%C, %hi, %Lb, HC, Hhi', #HLb, %Hok⟩
    ihave %Hm := ghost_map_lookup $$ HC He
    obtain ⟨-, -, -, A, -, hm⟩ := Hok.1 _ _ Hm
    have h0 := kvRaftOf_extends γk.c0 γk.ch0 γk.log0 A
    unfold kvModel at hm
    rw [hm] at h0
    have := h0.length_le
    simp only [List.length_nil] at this
    omega

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

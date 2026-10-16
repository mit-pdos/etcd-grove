/-
**The server's construction: the ghost allocations** (unit N2 of the server-construction unit;
statements placed at stage N0, 2026-10-16; D13 and D13a-d, `notes/decisions.md`). Lean-first (no
Rocq counterpart). The statements are the interface `NewServer`'s proof (unit N1) uses; their
proofs are unit N2's.

* `srvReadNamesFresh_alloc`: the read names, fresh (`InvBuild.lean`), chosen before
  `newRaftNode` (D13a), at the given raft names and KV start values.
* `kvInv_alloc_boot`: the KV invariant at the bootstrap log, from the client's half of raft's
  committed log (`allocClientBoot`'s continuation output `rLog γ bootLog`), and the client's
  `etcdKV` at the bootstrap log's model.
* `kvCertInv_alloc`: the certificates' invariant, from the store's certificate authority (which
  `mvcc.New` returns, D13a) and the certified length's half.
* `srvIndices_alloc`: the applied and committed indices' invariants and the term's, at index `0`.
* `srvMintInv_alloc`: the mints, from `allocClientBoot`'s fresh-token authorities and raft's read
  credits.
* `consInv_alloc`: the apply protocol's invariant over a fresh consistent index (for whoever
  discharges `bootstrap`'s contract, `InvBoot.lean`: the backend's batch lock's resource names the
  protocol's names, so they exist before the backend does).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvBuild

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section alloc
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The read names, fresh**, at the raft names `raft` and the KV start values (`c0`, `ch0`,
`log0`), the KV names' certificate map `cok` (the store's, chosen before `mvcc.New`), and the KV
state's variable at `σ`. -/
theorem srvReadNamesFresh_alloc (raft : ServerRaftNames) (c0 : w64) (ch0 : apply.Chain)
    (log0 : mvcc.Log) (cok : GName) (σ : KVState) :
    ⊢ |==> ∃ γr : ReadNames,
      ⌜γr.raft = raft ∧ γr.kv.c0 = c0 ∧ γr.kv.ch0 = ch0 ∧ γr.kv.log0 = log0 ∧ γr.kv.cok = cok⌝ ∗
      srvReadNamesFresh (GF := GF) γr σ := by
  sorry

/-- **The KV invariant at the bootstrap log** (a new cluster: the server's start log empty, its
start index `0`, the consistent index `0`, the base chain, a non-empty start log): from the
client's half of raft's committed log at `bootLog` and the KV state's variable at the bootstrap
log's model, the invariant and the client's `etcdKV`. -/
theorem kvInv_alloc_boot (γs : ServerRaftNames) (γk : KVNames) (ccOk : w32 → List w8 → Prop)
    (ps : List w64) (bootLog : List EntryM) (E : CoPset)
    (hpre : γs.pre = []) (hai : γs.ai0 = W64 0) (hboot : BootLogOk ccOk ps bootLog)
    (hc0 : γk.c0 = W64 0) (hch : γk.ch0 = apply.alarmChain false false false)
    (hlog : γk.log0 ≠ []) :
    ⊢ rLog (GF := GF) γs.raft bootLog -∗
      ghostVar γk.st 1 (kvStateOf (kvModel γk (bootEntries bootLog))) ={E}=∗
      kvInv γs γk ∗ etcdKV γk (kvStateOf (kvModel γk (bootEntries bootLog))) := by
  sorry

/-- **The certificates' invariant**: from the store's certificate authority (empty), the
certified length's half at the start log's length, and the empty log committed. -/
theorem kvCertInv_alloc (γs : ServerRaftNames) (γk : KVNames) (E : CoPset)
    (h2 : 2 ≤ γk.log0.length) :
    ⊢ ghostMapAuth (GF := GF) γk.cok 1 (∅ : GMap w64 mvcc.Log) -∗
      ghostVar γk.hi (1 : Qp).half γk.log0.length -∗ srvRLogLb γs [] ={E}=∗
      kvCertInv γs γk := by
  sorry

/-- **The indices' invariants at index `0`** (the server's start index `0`): from the three
atomics at `0` (the zero fields of the `EtcdServer` literal), the indices' fresh authorities, the
applied logs' empty map, the pending flag, the store's certificate of the start log and the empty
log committed: the applied index's invariant with the apply thread's half and the start log
applied at `0`; the committed index's with the writer's half; the term's. -/
theorem srvIndices_alloc (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) (Ec : CoPset)
    (hai : γr.raft.ai0 = W64 0) :
    ⊢ sync.atomic.ownUint64 (srvAppliedIndexAddr s) (DFrac.own 1) (W64 0) -∗
      sync.atomic.ownUint64 (srvCommittedIndexAddr s) (DFrac.own 1) (W64 0) -∗
      sync.atomic.ownUint64 (srvTermAddr s) (DFrac.own 1) (W64 0) -∗
      monoNatAuthOwn γr.applied 1 0 -∗ monoNatAuthOwn γr.committed 1 0 -∗
      ghostMapAuth γr.logs 1 (∅ : GMap w64 mvcc.Log) -∗ ghostVar γr.pend 1 false -∗
      mvcc.idxCert E.γ.idx γr.kv.log0 -∗ srvRLogLb γr.raft [] ={Ec}=∗
      srvAppliedInv s E γr ∗ srvAppliedOwn γr (W64 0) ∗ appliedLogAt γr (W64 0) γr.kv.log0 ∗
      srvCommittedInv s γr ∗ srvCommittedOwn γr (W64 0) ∗
      inv srvN (∃ t : w64, sync.atomic.ownUint64 (srvTermAddr s) (DFrac.own 1) t) := by
  sorry

/-- **The mints** (`srvMintInv`): from raft's fresh-data and fresh read-context authorities
(empty) and its whole read budget (`allocClientBoot`'s continuation outputs and
`ownRaftGhost_alloc_boot`'s credits). -/
theorem srvMintInv_alloc (ρ : ReqNames) (E : CoPset) :
    ⊢ ghostMapAuth (GF := GF) ρ.raft.raft.reFresh 1 (∅ : GMap (List w8) Unit) -∗
      ghostMapAuth ρ.raft.raft.reRdFresh 1 (∅ : GMap (List w8) Unit) -∗
      rdCred ρ.raft.raft (2 ^ 64 - 2) ={E}=∗ srvMintInv ρ := by
  sorry

/-- **The apply protocol's invariant** over a fresh consistent index (its client half at `0`),
with the backend's initial meta keys `m0`: the protocol's names, its invariant, the apply
thread's half at nothing processed beyond `m0`'s index, the batch lock's half of the stored
index's mirror and its token. -/
theorem consInv_alloc (γci : CINames) (m0 : MetaCI) (E : CoPset) :
    ⊢ ciIdx (GF := GF) γci (W64 0) ={E}=∗ ∃ γA : ApplyNames, ⌜γA.ci = γci ∧ γA.m0 = m0⌝ ∗
      inv applyN (consInv γA) ∗ applyThread γA ⟨W64 0, m0.1, m0.1, false⟩ ∗
      ghostVar γA.mt (1 : Qp).half m0.1 ∗ token γA.pend := by
  sorry

end alloc

end EtcdGrove
end Perennial

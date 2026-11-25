/-
`run(srvs, ms, lg)` (`examples/etcd/authlease/authlease.go`; auth-lease S4, item 9): **proved**, over
its callees' specs. Lean-first (no Rocq counterpart). authN's `run.wp_proof` (`authN/run.lean`) for the
serve loop (`serve_member_lease`: authN's `serve_member` in the revocable lease mode, then
`etcdstart.lease_served_on`), the set-up and the clients, with:

- the driver's cell (`Cell.lean`) allocated over member `0`'s KV state before the set-up, the set-up's
  puts through it (`cell_setupAu`);
- the two barrier rounds through `barriers` (`bArg`: each member's barrier arguments; the second
  round's read update `cell_readAu`, its floor seeing the three attachments);
- the leases (`grantPut` with the ghost step `cell_fix`, u's transaction `cell_txnTAu`), the checks
  (`noAuth`, u's refused put and transaction `refused_update`, `absent`, `foreign`, root's read of
  `z/lease`, u's revocation `cell_revokeUAu` and the absences after it), the lessor facts from the
  second barrier's floor (`cell_holds`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.authN.run
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.ServedLeaseOnLinked
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.authlease.run
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.authlease.barriers
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.authlease.grantPut
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.authlease.noAuth
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.authlease.foreign
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.authlease.absent
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.authlease.refused
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.authlease.newUserClient
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.authlease.Refusals
public import Spec.go_etcd_io.etcd.client.v3.WithLease
public import Spec.context.WithTimeoutBackgroundMd
public import Spec.go_etcd_io.etcd.client.v3.OpPut
public import Proof.go_etcd_io.etcd.client.v3.TxnPlain
public import Proof.go_etcd_io.etcd.client.v3.ResultsOn

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_authlease

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver etcd_auth etcdstart
open etcd_authN (Wit akV mod_len_sint srvdW srvdAt serve_member leaseReady)
open etcd_auth3 (admStates_same srvAuthAtLog_same srvRLogLb_same srvReqLogLb_same authHistFrozen_same)

section pure
variable [GooseExts]

/-- **u's leased transaction's shape** (`client_txn_on`'s and `txnUpdAtOn`'s side conditions):
`Txn().Then(OpPut(k, "v", WithLease(L)))` writes, fits a gRPC message, each permission of the shape the
cache decides, a leased (not plain) transaction, no zero range end, the nested shape. -/
theorem leaseTxn_ok (k : GoString) (L : w64) (hk : k ≠ []) (hkl : k.length ≤ 2 ^ 20) :
    txn.txnReadonly (txnWireOf (leaseTxn k L)) = false ∧ txnSizeOk (txnWireOf (leaseTxn k L)) ∧
    (∀ tw : txn.TxnModelW, tw.toModel = txnWireOf (leaseTxn k L) → kvShapeAll (irrTxn tw)) ∧
    txnPlainL (txnWireOf (leaseTxn k L)) ∧ txnNoZeroEnd (txnWireOf (leaseTxn k L)) ∧
    client.txnNestOk (txnWireOf (leaseTxn k L)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [leaseTxn, txnWireOf, opWire, txn.txnReadonly, txn.opIsGet]
  · refine txnSizeOk_of_bounds (N := 2 ^ 20) (M := 3) ⟨?_, ?_, ?_⟩ ?_ (by decide)
    · intro c hc; simp [leaseTxn, txnWireOf] at hc
    · intro o ho
      simp [leaseTxn, txnWireOf, opWire] at ho
      subst ho
      simp only [TxnOp.bytesLe]; exact ⟨hkl, by decide⟩
    · intro o ho; simp [leaseTxn, txnWireOf] at ho
    · simp [TxnModel.nodes, leaseTxn, txnWireOf, opWire, TxnOp.nodes]
  · intro tw htw
    refine etcd_auth.kvShapeAll_irrTxn tw (by rw [htw]; simp [leaseTxn, txnWireOf]) ?_
    rw [htw]
    intro op hop
    simp [leaseTxn, txnWireOf, opWire] at hop
    subst hop
    exact hk
  · simp [txnPlainL, txn.txnLeased, leaseTxn, txnWireOf, opWire, txn.opsLeased, txn.opLeased]
  · refine ⟨by simp [leaseTxn, txnWireOf], ?_, by simp [leaseTxn, txnWireOf, txnOpsNoZeroEnd]⟩
    simp [leaseTxn, txnWireOf, opWire, txnOpsNoZeroEnd, txnOpNoZeroEnd]
  · simp [client.txnNestOk, leaseTxn, txnWireOf, opWire, txn.OpsNoCut, txn.OpNoCut, client.txnSibSafeL, client.txnSibSafe]

/-- `OpPut(k, "v", WithLease(L))`'s transaction operation. -/
theorem txnOpOf_leasePut (k : GoString) (L : w64) :
    txnOpOf (opPutModel k go!"v" [withLeaseM L]) = some (.put k go!"v" L) := by
  simp [txnOpOf, opPutModel, opFold, withLeaseM, OpFull.putInit, OpFull.newOp, OpModel.zero]

end pure

section served
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [go_etcd_io.etcd.client.v3.Assumptions]

/-- **A served member with its Lease service** (the serve loop's accumulated fact): authN's `srvdW`
and the member's Lease service with auth on (`etcdstart.etcdLeaseServedOn`). -/
def srvdWL (s : Loc) (x : GMember × MemberG GF) (w : Wit GF) : IProp GF :=
  iprop(srvdW s x w ∗ etcdstart.etcdLeaseServedOn x.1.Client' s w.E { x.2.ρ with wait := w.γw })

instance srvdWL_persistent (s : Loc) (x : GMember × MemberG GF) (w : Wit GF) :
    Persistent (srvdWL s x w) := by
  unfold srvdWL; infer_instance

/-- **A member served with its Lease service** (`Run`'s `Serve` step, for a member in the revocable
lease mode): authN's `serve_member`, then `etcdstart.lease_served_on` from its `leaseReady`; on
success, `serve_member`'s served facts and the member's Lease service with auth on. -/
theorem serve_member_lease [HasExt idIssueExt] [go_etcd_io.etcd.cache.v3.Assumptions]
    (wp_Serve : etcdstart.Serve.spec (GF := GF) (hG := hG))
    (wp_BcryptCost : auth.authStore.BcryptCost.spec (GF := GF) (hG := hG))
    (hP : mvcc.api.persistent.law (GF := GF))
    (hR : mvcc.api.mvccState_reachable.law (GF := GF))
    (s lg : Loc) (addr : GoString) (ρ : ReqNames) (E₀ : apply.AEnv GF) (γn : NetNames GF)
    (id : w64) (γa : auth.AuthNames)
    (Htb : threadBound GF ≤ 2 ^ 28) (HLv : srvLevels (GF := GF)) (Hrb48 : receiptBound GF ≤ 2 ^ 48)
    (Hbuq : apply.backendUnderQuota) (Hrf : grpcRepliesFit) (Hms : v3rpc.ServerMethodSets)
    (hlog : ρ.rd.kv.log0 = [[], []]) (hlm : ρ.rd.kv.lm = .revocable) (hLp : leasePeersOk) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗ client.eofOk ∗
        zapLoggerOk lg ∗ netAddrFree addr ∗ etcdstart.memberUpOn s ρ E₀ lg γn id γa .revocable }}
      (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Serve)) (Val #s))
        (Val #addr))
    {{ (err : GoInterface), RET #err; ⌜err ≠ GoInterface.nil⌝ ∨
        (⌜err = GoInterface.nil⌝ ∗ threadTok ∗
          ∃ (E : apply.AEnv GF) (γw : GName) (cid mid : w64) (R : v3rpc.WSrv GF),
            ⌜E.authMode = .on γa ∧ R.E = E ∧ R.s = s⌝ ∗ isServerReadM true s E ρ.rd ∗
            □ (srvTLSId s -∗ False) ∗ akKVOn addr s E { ρ with wait := γw } cid mid ∗
            setupAuthServed addr s E { ρ with wait := γw } ∗
            isGrpcRpc addr authnMethod (client.etcdAuthenticateSpec γa) ∗
            watchAddrFacts (akV addr ρ R) ∗ auth.modeTag R.tag (.on γa) ∗
            etcdstart.etcdLeaseServedOn addr s E { ρ with wait := γw }) }} := by
  iintro %Φ ⟨#Pst, #Psrv, #Pv3, #Ppb, #Heo, #Hlgz, Haddr, Hup⟩ HΦ
  iapply wp_fupd
  wp_apply (serve_member wp_Serve wp_BcryptCost hP hR s lg addr ρ E₀ γn id γa .revocable
      Htb HLv Hrb48 Hbuq Hrf Hms hlog) $$ [Haddr Hup] as %err Hs
  · iframe; iframe #
  icases Hs with (%Herr | ⟨%Herr, Htok, %E, %γw, %cid, %mid, %R, %HR, #Hrd, #Htls,
    #HKV, #HSA, #HAu, #HWF, #Htag, #HLR⟩)
  · imodintro; iapply HΦ; ileft; ipureintro; exact Herr
  iunfold leaseReady at HLR
  icases HLR with ⟨%A, %il, %im, %iu, %regs, %γ, %HA, #Hreq, #Hrd', #Hlb, #Hlr, #Hlu, #Hil, #Him,
    #Hiu, #Hat, #Hb, #Hrp⟩
  imod (etcdstart.lease_served_on addr s E { ρ with wait := γw } A il im iu regs γ γa HR.1 hlm HA
      (by omega) (by omega) hLp HLv) $$ [] with #HLS
  · iframe #
    iintro !>
    imodintro
    iunfold idCred
    ipureintro; exact Hrb48
  imodintro
  iapply HΦ
  iright
  iframe Htok
  isplitl []
  · ipureintro; exact Herr
  iexists E, γw, cid, mid, R
  iframe #
  ipureintro; exact HR

end served

section barriers
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **A served member's barrier arguments** (`barriers`' `bs`): its address, watch environment, server,
witnesses and names, the set-up's frozen history `hs` (`γz`), requested and committed logs, the auth
state's revision `r`, the read update `Q`. -/
abbrev bArg (γz : GName) (hs : List auth.AuthState) (Lset Lc : List EntryModel) (r : Nat)
    (Q : KVState → IProp GF) (q : (Loc × (GMember × MemberG GF)) × Wit GF) : BArgs GF :=
  { addr := q.1.2.1.Client', V := akV q.1.2.1.Client' q.1.2.2.ρ q.2.R, s := q.1.1, E := q.2.E,
    ρ := { q.1.2.2.ρ with wait := q.2.γw }, cid := q.2.cid, mid := q.2.mid, γa := q.2.γa, γz := γz,
    hs := hs, Lset := Lset, Lc := Lc, r := r, Q := Q }

/-- **Every served member's barrier precondition**: its served facts, the set-up's facts at member
`x0`'s names carried to its own (`*_same`), and the read update at its KV names. -/
theorem barrierPre_all (x0 : GMember × MemberG GF) (w0 : Wit GF) (γz : GName) (hs : List auth.AuthState)
    (Lset Lc : List EntryModel) (r : Nat) (Q : KVState → IProp GF)
    (l : List ((Loc × (GMember × MemberG GF)) × Wit GF))
    (hl : ∀ q ∈ l, etcdstart.sameCluster x0.2.ρ q.1.2.2.ρ ∧ plainEndpoint q.1.2.1.Client')
    (hadm : admStates { x0.2.ρ with wait := w0.γw }.kv srvAuthSt0 Lset = hs ∧
      srvAuthAtLog { x0.2.ρ with wait := w0.γw }.kv srvAuthSt0 Lset = setupSt r)
    (hlc : srvAuthAtLog { x0.2.ρ with wait := w0.γw }.kv srvAuthSt0 Lc = setupSt r) :
    ([∗list] q ∈ l, srvdWL q.1.1 q.1.2 q.2) ∗
      authHistFrozen { x0.2.ρ with wait := w0.γw }.kv γz hs ∗
      srvReqLogLb { x0.2.ρ with wait := w0.γw }.raft Lset ∗
      srvRLogLb { x0.2.ρ with wait := w0.γw }.raft Lc ∗
      □ (∀ ρ' : ReqNames, ⌜etcdstart.sameCluster x0.2.ρ ρ'⌝ -∗
        (⌜Q = fun _ => iprop(True)⌝ ∨ kvReadAu ρ'.rd.kv Q)) ⊢
      [∗list] q ∈ l, barrierPre (bArg γz hs Lset Lc r Q q) := by
  induction l with
  | nil => iintro _; iapply BigSepL.bigSepL_nil.2; itrivial
  | cons q l ih =>
    iintro ⟨Hs, #Hfz, #Hllb, #HLc, #HQ⟩
    ihave Hs := BigSepL.bigSepL_cons.1 $$ Hs
    icases Hs with ⟨#Hq, Hs⟩
    iapply BigSepL.bigSepL_cons.2
    obtain ⟨hsc, hpe⟩ := hl q List.mem_cons_self
    isplitr [Hs]
    · iunfold srvdWL at Hq
      iunfold srvdW at Hq
      iunfold srvdAt at Hq
      icases Hq with ⟨⟨%HR, #Hrd, -, #HKV, -, #HAu, -, -⟩, -⟩
      have hon : q.2.E.authOn = true := by unfold apply.AEnv.authOn; rw [HR.1]; rfl
      iunfold barrierPre
      isplitl []
      · ipureintro; exact ⟨hpe, HR.1⟩
      iframe HAu HKV
      ihave #Hrd' : isServerReadM q.2.E.authOn q.1.1 q.2.E q.1.2.2.ρ.rd $$ []
      · rw [hon]; iexact Hrd
      iframe Hrd'
      ihave #Hfzq := authHistFrozen_same { x0.2.ρ with wait := w0.γw } { q.1.2.2.ρ with wait := q.2.γw }
        hsc γz hs $$ Hfz
      ihave #Hllbq := srvReqLogLb_same { x0.2.ρ with wait := w0.γw } { q.1.2.2.ρ with wait := q.2.γw }
        hsc Lset $$ Hllb
      ihave #HLcq := srvRLogLb_same { x0.2.ρ with wait := w0.γw } { q.1.2.2.ρ with wait := q.2.γw }
        hsc Lc $$ HLc
      iframe Hfzq Hllbq HLcq
      isplitl []
      · ipureintro
        rw [admStates_same { x0.2.ρ with wait := w0.γw } { q.1.2.2.ρ with wait := q.2.γw } hsc,
          srvAuthAtLog_same { x0.2.ρ with wait := w0.γw } { q.1.2.2.ρ with wait := q.2.γw } hsc]
        exact hadm
      isplitl []
      · ipureintro
        rw [srvAuthAtLog_same { x0.2.ρ with wait := w0.γw } { q.1.2.2.ρ with wait := q.2.γw } hsc]
        exact hlc
      imodintro
      iapply HQ
      ipureintro; exact hsc
    · iapply (ih (fun q' hq' => hl q' (List.mem_cons_of_mem _ hq')))
      iframe Hs
      iframe #

/-- **A linearizable get of one key** (`absent`'s and root's reads of `run`, with the read update `Q`):
the reply's key-values are those of `k` at a sorted state where `Q` fired. -/
theorem getReply_state (E : apply.AEnv GF) (γr : ReadNames) (c cid mid : w64) (F : mvcc.Log) (k : GoString)
    (Q : KVState → IProp GF) (m : RangeRespM) :
    client.rangeReplyOk E γr c F (rangeWireOf (opGetModel k [])) cid mid Q m ⊢
      ∃ σ : KVState, □ Q σ ∗ ⌜m.kvs = σ.kvs.filter (fun v => decide (v.key = k)) ∧
        σ.kvs.Pairwise etcdKvLess⌝ := by
  iintro #H
  iunfold client.rangeReplyOk at H
  icases H with ⟨%l, -, -, %Hl, -, #HQ⟩
  have hs : (rangeWireOf (opGetModel k [])).base.serializable = false := rfl
  have hr : (rangeWireOf (opGetModel k [])).base.rev = W64 0 := rfl
  isimp only [hs, Bool.false_eq_true, ↓reduceIte] at HQ
  icases HQ with ⟨%lt, -, #HQ⟩
  obtain ⟨hlen, hlen', hrev, -, -, -, -, hsel, -⟩ := Hl
  have hst : mvcc.stateAt l (sint.nat (mvcc.rangeRev m.hdr.revision
      (rangeWireOf (opGetModel k [])).base.rev)) = mvcc.stateAfter l := by
    have h1 : mvcc.rangeRev m.hdr.revision (rangeWireOf (opGetModel k [])).base.rev = m.hdr.revision := by
      simp [mvcc.rangeRev, hr]
    rw [h1, hrev]
    have h2 : sint.nat (W64 ((l.length : Int) - 1)) = l.length - 1 := by
      unfold sint.nat; word
    rw [h2, mvcc.stateAt_last]
  rw [hst] at hsel
  iexists kvStateOf l lt
  iframe HQ
  ipureintro
  rw [kvStateOf_kvs]
  exact ⟨(client.srvRangeOk_getKey k _ _ _ (by exact hsel)).1, mvcc.stateAfter_sorted l⟩

/-- What a state the cell saw satisfies. -/
theorem seen_cell (γc : CellNames) (ps1 : List Nat) (d1 : Nat) (σ : KVState) :
    cellSeen (GF := GF) γc ps1 d1 σ ⊢ ⌜∃ ids ps gs d, CellOk σ ids ps gs d ∧ ps1 <+: ps ∧ d1 ≤ d⌝ := by
  iintro H
  iunfold cellSeen at H
  icases H with ⟨%ids, %ps, %gs, %d, %h, -⟩
  ipureintro; exact ⟨ids, ps, gs, d, h⟩

/-- **A state the cell saw after root's attachment has `z/lease` on `Lz`.** -/
theorem seen_z (γc : CellNames) (ps1 : List Nat) (d1 : Nat) (σ : KVState) (lz : w64) (h1 : 1 ≤ ps1.length) :
    cellSeen (GF := GF) γc ps1 d1 σ ∗ monoListLbOwn γc.ids [lz] ⊢ ⌜leaseOf zK σ.kvs = some lz⌝ := by
  iintro ⟨H, #Hl⟩
  iunfold cellSeen at H
  icases H with ⟨%ids, %ps, %gs, %d, %h, #Hil, -⟩
  ihave %Hc := mono_list_lb_valid γc.ids ids [lz] $$ Hil Hl
  ipureintro
  obtain ⟨hok, hps, -⟩ := h
  have hp1 : 1 ≤ ps.length := Nat.le_trans h1 hps.length_le
  have hz := hok.1.z_at hp1
  have hi1 := hok.1.ps_ids.2.1 hp1
  have hl : lzOf ids = lz := by
    rcases Hc with ⟨t, ht⟩ | ⟨t, ht⟩
    · cases ids with
      | nil => simp at hi1
      | cons a r => simp at ht; simp [lzOf, ht.1]
    · subst ht; simp [lzOf]
  rw [hz, hl]

/-- **A state the cell saw after u's revocation has neither `a/lease` nor `a/txn`.** -/
theorem seen_gone (γc : CellNames) (ps1 : List Nat) (σ : KVState) :
    cellSeen (GF := GF) γc ps1 1 σ ⊢ ⌜mvcc.findKey aK σ.kvs = none ∧ mvcc.findKey tK σ.kvs = none⌝ := by
  iintro H
  ihave %Hc := seen_cell γc ps1 1 σ $$ H
  ipureintro
  obtain ⟨ids, ps, gs, d, hok, -, hd⟩ := Hc
  exact hok.1.gone (by have := hok.1.d_le; omega)

end barriers

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.authlease.Assumptions]

set_option maxHeartbeats 3200000 in
set_option maxRecDepth 10000 in
theorem run.wp_proof
    (wp_Serve : etcdstart.Serve.spec (GF := GF) (hG := hG))
    (wp_NewClient : etcdstart.NewClient.spec (GF := GF) (hG := hG))
    (wp_BcryptCost : auth.authStore.BcryptCost.spec (GF := GF) (hG := hG))
    (wp_ErrAny : context.ErrAny.spec (GF := GF) (hG := hG))
    (wp_SetUp : etcd_auth.SetUp.spec (GF := GF) (hG := hG))
    (wp_newUserClient : newUserClient.spec (GF := GF) (hG := hG))
    (wp_barriers : barriers.spec (GF := GF) (hG := hG))
    (wp_grantPut : grantPut.spec (GF := GF) (hG := hG))
    (wp_noAuth : noAuth.spec (GF := GF) (hG := hG))
    (wp_refused : refused.spec (GF := GF) (hG := hG))
    (wp_absent : absent.spec (GF := GF) (hG := hG))
    (wp_foreign : foreign.spec (GF := GF) (hG := hG))
    (wp_WithTimeout : context.WithTimeoutBackgroundMd.spec (GF := GF) (hG := hG))
    (wp_WithLease : WithLease.spec (GF := GF) (hG := hG))
    (wp_OpPut : OpPut.spec (GF := GF) (hG := hG))
    (hP : mvcc.api.persistent.law (GF := GF))
    (hR : mvcc.api.mvccState_reachable.law (GF := GF))
    (hlaw : lessor_keys_of_read_stmt (GF := GF)) :
    run.spec (GF := GF) (hG := hG) := by
  intro CS ES FS RS srvsl msl lg ss xs x0 γn σ0 hx0 hxl Hpe Htb HLv Hrb48 Hbuq Hrf Hms hAs hc0
    hlog hlm hLp hns hsc hx
  have Htb31 : threadBound GF ≤ 2 ^ 31 := by omega
  have hk1 : 1 ≤ xs.length := by
    cases xs with
    | nil => simp at hx0
    | cons _ _ => simp
  have hlogx : ∀ x ∈ xs, x.2.ρ.rd.kv.log0 = [[], []] := fun x hx => by rw [(hsc x hx).2.2.2.1, hlog]
  wp_start as ⟨#Hlgz, Hss, #Hmsl, Htok, Hcfree, Hups, HkV, Hview⟩
  -- the driver's cell, over member 0's KV state (before the set-up)
  imod (cell_alloc x0.2.ρ.rd.kv σ0 hx) $$ HkV with ⟨%γc, #Hinv, #Hi0, #Hp0, #Hg0, #Hd0, Ha, Hids⟩
  ihave %Hlg := zapLoggerOk_ne_null lg $$ Hlgz
  ihave #Hcci : context.isClosedchanInit (GF := GF) $$ []
  · iapply context.isClosedchanInit_of_init
    iPkgInit
  ihave #Psrv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver $$ []
  · iPkgInit
  ihave #Pv3 : isPkgInit (PROP := IProp GF)
      pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc $$ []
  · iPkgInit
  ihave #Ppb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb $$ []
  · iPkgInit
  ihave #Pst : isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart $$ []
  · iPkgInit
  ihave #Heo : client.eofOk (GF := GF) $$ []
  · iapply (client.eofOk_of_init hAs)
    iPkgInit
  ihave %Hupl := BigSepL2.bigSepL2_length $$ Hups
  ihave %Hssl := ownSlice_len $$ Hss
  ihave %Hmsll := ownSlice_len $$ Hmsl
  have hkl : uint.nat msl.len = xs.length := by have := Hmsll.1; simp at this; word
  have Hb0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z msl.len := by
    have := Hmsll.1; simp at this; constructor <;> word
  have hm0 : (xs.map (·.1))[(sint.Z (W64 0)).toNat]? = some x0.1 := by
    rw [show (sint.Z (W64 0)).toNat = 0 from rfl, List.getElem?_map, hx0]; rfl
  have hk0 : ¬ (uint.Z msl.len = 0) := by word
  -- (for `run`'s indexing) u's member `1 % k`, v's member `2 % k`
  have hmodZ := fun c hc => mod_len_sint msl.len xs.length c hkl (by omega) hxl hc
  obtain ⟨xu, hxu⟩ : ∃ x, xs[1 % xs.length]? = some x :=
    ⟨_, List.getElem?_eq_getElem (Nat.mod_lt _ (by omega))⟩
  obtain ⟨xv, hxv⟩ : ∃ x, xs[2 % xs.length]? = some x :=
    ⟨_, List.getElem?_eq_getElem (Nat.mod_lt _ (by omega))⟩
  have hmsZ : sint.Z msl.len = (xs.length : Int) := by have := Hmsll.1; simp at this; word
  have hu : sint.Z (W64 1 % msl.len) = ((1 % xs.length : Nat) : Int) := hmodZ 1 (by omega)
  have hv : sint.Z (W64 2 % msl.len) = ((2 % xs.length : Nat) : Int) := hmodZ 2 (by omega)
  have Hbu : 0 ≤ sint.Z (W64 1 % msl.len) ∧ sint.Z (W64 1 % msl.len) < sint.Z msl.len := by
    rw [hu, hmsZ]; have := Nat.mod_lt 1 (by omega : xs.length > 0); omega
  have Hbv : 0 ≤ sint.Z (W64 2 % msl.len) ∧ sint.Z (W64 2 % msl.len) < sint.Z msl.len := by
    rw [hv, hmsZ]; have := Nat.mod_lt 2 (by omega : xs.length > 0); omega
  have hmu : (xs.map (·.1))[(sint.Z (W64 1 % msl.len)).toNat]? = some xu.1 := by
    rw [hu, Int.toNat_natCast, List.getElem?_map, hxu]; rfl
  have hmv : (xs.map (·.1))[(sint.Z (W64 2 % msl.len)).toNat]? = some xv.1 := by
    rw [hv, Int.toNat_natCast, List.getElem?_map, hxv]; rfl
  imod ownSlice_persist _ _ _ $$ Hss with #Hss
  (try wp_auto)
  -- the serve loop: `for j, m := range ms { if err := Serve(srvs[j], m.Client); err != nil { return
  -- Failed } }`, the thread token from member to member
  ihave IH : (∃ (n jv : w64) (mv : GMember) (ws : List (Wit GF)),
      "i" ∷ i_ptr ↦ n ∗ "j" ∷ j_ptr ↦ jv ∗ "m" ∷ m_ptr ↦ mv ∗ "Htok" ∷ threadTok ∗
      "Hups" ∷ ([∗list] s; x ∈ ss.drop (sint.nat n); xs.drop (sint.nat n),
        (threadTok -∗ ∃ γa : auth.AuthNames, etcdstart.memberUpOn s x.2.ρ x.2.E lg γn x.2.id γa .revocable)) ∗
      "Hcfree" ∷ ([∗list] x ∈ xs.drop (sint.nat n), netAddrFree (GF := GF) x.1.Client') ∗
      "#Hsv" ∷ ([∗list] q ∈ ((ss.zip xs).take (sint.nat n)).zip ws, srvdWL q.1.1 q.1.2 q.2) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.nat n ≤ xs.length ∧ ws.length = sint.nat n⌝ : IProp GF)
      $$ [i j m Htok Hups Hcfree]
  · iexists W64 0, _, _, []
    have h00 : sint.nat (W64 0) = 0 := rfl
    simp only [h00, List.drop_zero, List.take_zero, List.zip_nil_left]
    iframe
    isplitl
    · iapply BigSepL.bigSepL_nil.2; itrivial
    ipureintro; exact ⟨by decide, by omega, rfl⟩
  wp_for IH
  wp_if_destruct
  · have hlt : sint.nat n < xs.length := by have := Hmsll.1; simp at this; word
    list_elem ss (sint.nat n) as sj
    list_elem xs (sint.nat n) as xj
    have hnz : (sint.Z n).toNat = sint.nat n := by word
    have Hbm : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z msl.len := ⟨Hn.1, Hif⟩
    have Hbs : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z srvsl.len := ⟨Hn.1, by have := Hssl.1; word⟩
    (try wp_auto)
    simp only [Hbm, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index msl (sint.Z n) _ _ xj.1 Hbm.1 $$ [Hmsl] as -
    · iframe #; ipureintro; rw [hnz, List.getElem?_map, Hxj_lookup]; rfl
    (try wp_auto)
    simp only [Hbs, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index srvsl (sint.Z n) _ _ sj Hbs.1 $$ [Hss] as -
    · iframe #; ipureintro; rw [hnz]; exact Hsj_lookup
    (try wp_auto)
    -- the member's `memberUpOn`, the token given to it
    isimp only [drop_cons_of_getElem? ss _ sj Hsj_lookup, drop_cons_of_getElem? xs _ xj Hxj_lookup] at Hups
    ihave Hups := BigSepL2.bigSepL2_cons.1 $$ Hups
    icases Hups with ⟨Hupj, Hups⟩
    ihave ⟨%γa, Hupj⟩ := Hupj $$ Htok
    isimp only [drop_cons_of_getElem? xs _ xj Hxj_lookup] at Hcfree
    ihave Hcfree := BigSepL.bigSepL_cons.1 $$ Hcfree
    icases Hcfree with ⟨Hcj, Hcfree⟩
    have hxj : xj ∈ xs := List.mem_of_getElem? Hxj_lookup
    wp_apply (serve_member_lease wp_Serve wp_BcryptCost hP hR sj lg xj.1.Client' xj.2.ρ xj.2.E γn xj.2.id γa
        Htb HLv Hrb48 Hbuq Hrf Hms (hlogx xj hxj) (hlm xj hxj) hLp) $$ [Hcj Hupj] as %serr Hs
    · iframe; iframe #
    icases Hs with (%Hserr | ⟨%Hserr, Htok, %E, %γw, %cid, %mid, %R, %HR, #Hrd, #Htls,
      #HKV, #HSA, #HAu, #HWF, #Htag, #HLS⟩)
    · cases serr with
      | nil => exact absurd rfl Hserr
      | ok ei => ?_
      (try wp_auto)
      wp_for_post
      iapply HΦ; ipureintro; right; rfl
    subst Hserr
    (try wp_auto)
    have hzj : (ss.zip xs)[sint.nat n]? = some (sj, xj) :=
      List.getElem?_zip_eq_some.2 ⟨Hsj_lookup, Hxj_lookup⟩
    have htl : ((ss.zip xs).take (sint.nat n)).length = ws.length := by
      rw [List.length_take, List.length_zip, Hupl, Hn.2.2]; omega
    have hzz : ((ss.zip xs).take (sint.nat n + 1)).zip (ws ++ [⟨γa, E, γw, cid, mid, R⟩]) =
        ((ss.zip xs).take (sint.nat n)).zip ws ++ [((sj, xj), ⟨γa, E, γw, cid, mid, R⟩)] := by
      rw [List.take_add_one, hzj, Option.toList_some, List.zip_append htl]; rfl
    ihave #Hsv' : [∗list] q ∈ ((ss.zip xs).take (sint.nat n + 1)).zip (ws ++ [⟨γa, E, γw, cid, mid, R⟩]),
        srvdWL q.1.1 q.1.2 q.2 $$ []
    · rw [hzz]
      iapply BigSepL.bigSepL_snoc.2
      iframe #
      iunfold srvdWL
      iframe #
      iunfold srvdW
      iunfold srvdAt
      iframe #
      ipureintro; exact HR
    iclear Hsv
    wp_for_post
    iframe
    have hn1 : sint.nat (n + W64 1) = sint.nat n + 1 := by word
    iexists n + W64 1, n, xj.1, ws ++ [⟨γa, E, γw, cid, mid, R⟩]
    rw [hn1]
    iframe
    iframe #
    ipureintro; exact ⟨by word, by omega, by simp [Hn.2.2]⟩
  -- every member served
  have hnk : sint.nat n = xs.length := by have := Hmsll.1; simp at this; word
  have hwl : ws.length = xs.length := by rw [Hn.2.2, hnk]
  ihave #Hsv : [∗list] q ∈ (ss.zip xs).zip ws, srvdWL q.1.1 q.1.2 q.2 $$ []
  · iExactEq Hsv; rw [hnk, List.take_of_length_le (by simp [Hupl])]
  iclear Hups Hcfree
  -- `a0 := ms[0].Client`, `au := ms[1%k].Client`, `av := ms[2%k].Client`
  simp only [Hb0, _root_.and_self, ↓reduceIte]
  icases ownSlice_elem_acc _ _ _ _ _ Hb0.1 hm0 $$ Hmsl with ⟨#Hm0, -⟩
  iStructNamedSuffix Hm0 "_m0"
  (try wp_auto)
  simp only [hk0, ↓reduceIte]
  (try wp_auto)
  simp only [Hbu, _root_.and_self, ↓reduceIte]
  icases ownSlice_elem_acc _ _ _ _ _ Hbu.1 hmu $$ Hmsl with ⟨#Hmu, -⟩
  iStructNamedSuffix Hmu "_mu"
  (try wp_auto)
  simp only [hk0, ↓reduceIte]
  (try wp_auto)
  simp only [Hbv, _root_.and_self, ↓reduceIte]
  icases ownSlice_elem_acc _ _ _ _ _ Hbv.1 hmv $$ Hmsl with ⟨#Hmv, -⟩
  iStructNamedSuffix Hmv "_mv"
  (try wp_auto)
  -- member 0's served facts (its witnesses `w0`), u's member's and v's member's witnesses
  have hx0m : x0 ∈ xs := List.mem_of_getElem? hx0
  have hxum : xu ∈ xs := List.mem_of_getElem? hxu
  have hxvm : xv ∈ xs := List.mem_of_getElem? hxv
  have hzl : ((ss.zip xs).zip ws).length = xs.length := by simp [Hupl, hwl]
  have hgz : ∀ (i : Nat) (x : GMember × MemberG GF), xs[i]? = some x →
      ∃ s w, ((ss.zip xs).zip ws)[i]? = some ((s, x), w) := by
    intro i x hx
    have hi : i < xs.length := (List.getElem?_eq_some_iff.1 hx).1
    obtain ⟨s, hs⟩ : ∃ s, ss[i]? = some s := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨w, hw⟩ : ∃ w, ws[i]? = some w := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    exact ⟨s, w, List.getElem?_zip_eq_some.2 ⟨List.getElem?_zip_eq_some.2 ⟨hs, hx⟩, hw⟩⟩
  obtain ⟨s0, w0, hy0⟩ := hgz 0 x0 hx0
  obtain ⟨su, wu, hyu⟩ := hgz _ xu hxu
  obtain ⟨sv, wv, hyv⟩ := hgz _ xv hxv
  ihave #H0' := BigSepL.bigSepL_lookup hy0 $$ Hsv
  ihave #H0 : srvdWL s0 x0 w0 $$ []
  · iexact H0'
  iclear H0'
  iunfold srvdWL at H0
  iunfold srvdW at H0
  iunfold srvdAt at H0
  icases H0 with ⟨⟨%HR₁, #Hrd₁, #Htls₁, #HKV₁, #HSA₁, #HAu₁, #HWF₁, #Htag₁⟩, #HLS₁⟩
  -- `NewClient(a1, lg)`: the client with no user name, at member 0
  wp_apply (wp_NewClient x0.1.Client' lg (akV x0.1.Client' x0.2.ρ w0.R) (Hpe x0 hx0m) Htb31) as %cl %cerr Hcl
  · iframe #
  icases Hcl with (⟨%Hcerr, #Hnc, #Hctk, -⟩ | %Hcfail)
  rotate_left
  · obtain ⟨Hcerr, -⟩ := Hcfail
    cases cerr with
    | nil => exact absurd rfl Hcerr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ipureintro; right; rfl
  subst Hcerr
  wp_auto
  -- `SetUp(cli)` through member 0
  ihave #Hsau : iprop(□ ∀ k : GoString, ⌜k ∈ setupKeys⌝ -∗
      kvOpAu1 x0.2.ρ.rd.kv (.put (client.putKeyOp k go!"setup")) (fun _ => iprop(True))) $$ []
  · iintro !> %k %hk
    ihave #H := cell_setupAu x0.2.ρ.rd.kv γc k hk $$ Hinv
    iexact H
  ihave #Hput : isGrpcRpcMd x0.1.Client' go!"/etcdserverpb.KV/Put"
      (client.etcdPutSpecOn (srvTLSId s0) w0.E { x0.2.ρ with wait := w0.γw } w0.cid w0.mid) $$ []
  · iunfold akKVOn at HKV₁
    icases HKV₁ with ⟨#H, -, -, -⟩
    iexact H
  wp_apply (wp_SetUp cl x0.1.Client' (akV x0.1.Client' x0.2.ρ w0.R) s0 w0.E { x0.2.ρ with wait := w0.γw } w0.cid w0.mid w0.γa HR₁.1
      (by show uint.Z x0.2.ρ.rd.kv.c0 ≤ uint.Z x0.2.ρ.rd.raft.ai0; rw [hc0]; word) hAs)
    $$ [Hview] as %ok Hok
  · iframe; iframe #
  cases ok
  · wp_auto
    iapply HΦ; ipureintro; right; rfl
  rw [ite_eq_left rfl]
  icases Hok with ⟨%γz, %hs, %Lset, %kpub, %rset, #Hfz, #Hllb, %Hadm, -, -, %Lc, #HLc,
    %HLcst⟩
  (try wp_auto)
  -- `barriers(ms, lg)`: each member's auth state fixed after the set-up
  have hlq : ∀ q ∈ (ss.zip xs).zip ws, etcdstart.sameCluster x0.2.ρ q.1.2.2.ρ ∧
      plainEndpoint q.1.2.1.Client' := by
    intro q hq
    have hx := List.of_mem_zip (List.of_mem_zip hq).1 |>.2
    exact ⟨hsc _ hx, Hpe _ hx⟩
  have hmsb : ∀ (Q : KVState → IProp GF), (xs.map (·.1)).map (·.Client') =
      (((ss.zip xs).zip ws).map (bArg γz hs Lset Lc rset Q)).map (·.addr) := by
    intro Q
    have h1 : ((ss.zip xs).zip ws).map Prod.fst = ss.zip xs :=
      List.map_fst_zip (by simp [Hupl, hwl])
    have h2 : (ss.zip xs).map Prod.snd = xs := List.map_snd_zip (by simp [Hupl])
    calc (xs.map (·.1)).map (·.Client') = (((((ss.zip xs).zip ws).map Prod.fst).map Prod.snd).map
          (·.1)).map (·.Client') := by rw [h1, h2]
      _ = _ := by simp only [List.map_map]; rfl
  ihave #Hbp1 : [∗list] b ∈ ((ss.zip xs).zip ws).map (bArg γz hs Lset Lc rset (fun _ => iprop(True))),
      barrierPre b $$ []
  · rw [BigSepL.bigSepL_map]
    iapply (barrierPre_all x0 w0 γz hs Lset Lc rset _ _ hlq Hadm HLcst)
    iframe #
    iintro !> %ρ' %_
    ileft; ipureintro; rfl
  wp_apply (wp_barriers msl lg (xs.map (·.1)) _ (hmsb _) (by omega) hAs) as %okb Hb1
  · iframe #
  icases Hb1 with (%Hb | ⟨%Hb, #Hbq1⟩) <;> subst Hb
  · wp_auto
    iapply HΦ; ipureintro; right; rfl
  wp_auto
  ihave #Hbq1' : [∗list] q ∈ (ss.zip xs).zip ws,
      barrierPost (bArg γz hs Lset Lc rset (fun _ => iprop(True)) q) $$ []
  · rw [← BigSepL.bigSepL_map (fun q => bArg γz hs Lset Lc rset (fun _ => iprop(True)) q)]
    iexact Hbq1
  iclear Hbq1
  ihave #F0 := BigSepL.bigSepL_lookup hy0 $$ Hbq1'
  iunfold barrierPost at F0
  icases F0 with ⟨⟨%i₁, #Hfix₁⟩, %F₁, %lt₁, #HF₁, -⟩
  ihave #Hu' := BigSepL.bigSepL_lookup hyu $$ Hsv
  ihave #Hu : srvdWL su xu wu $$ []
  · iexact Hu'
  iclear Hu'
  iunfold srvdWL at Hu
  iunfold srvdW at Hu
  iunfold srvdAt at Hu
  icases Hu with ⟨⟨%HR₂, #Hrd₂, #Htls₂, #HKV₂, -, #HAu₂, #HWF₂, #Htag₂⟩, #HLS₂⟩
  ihave #Fu := BigSepL.bigSepL_lookup hyu $$ Hbq1'
  iunfold barrierPost at Fu
  icases Fu with ⟨⟨%i₂, #Hfix₂⟩, %F₂, %lt₂, #HF₂, -⟩
  ihave #Hv' := BigSepL.bigSepL_lookup hyv $$ Hsv
  ihave #Hv : srvdWL sv xv wv $$ []
  · iexact Hv'
  iclear Hv'
  iunfold srvdWL at Hv
  iunfold srvdW at Hv
  iunfold srvdAt at Hv
  icases Hv with ⟨⟨%HR₃, #Hrd₃, #Htls₃, #HKV₃, -, #HAu₃, #HWF₃, #Htag₃⟩, #HLS₃⟩
  ihave #Fv := BigSepL.bigSepL_lookup hyv $$ Hbq1'
  iunfold barrierPost at Fv
  icases Fv with ⟨⟨%i₃, #Hfix₃⟩, -⟩
  -- the clients: root at member 0, u at member `1 % k`, v at member `2 % k`, the one with no token at
  -- member `1 % k`
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave #Hall : client.ctxErrClientAll (GF := GF) $$ []
  · ihave #Hw := client.ctxErrClientAllW_of wp_ErrAny hAs $$ Pctx
    iunfold client.ctxErrClientAllW at Hw
    iunfold client.ctxErrClientAll
    iexact Hw
  wp_apply (wp_newUserClient x0.1.Client' go!"root" go!"root-pw" lg (akV x0.1.Client' x0.2.ρ w0.R)
      (fun t => auth.tokIssued w0.γa t go!"root") (Hpe x0 hx0m) (by omega) (by unfold strsSizeOk; decide))
    as %rcl %rerr Hrc
  · iframe #
    iapply (client.authTokReg_of _ _ _ w0.γa)
    iexact HAu₁
  icases Hrc with (⟨%Hrerr, #Hrnc, #Hrtk⟩ | %Hrfail)
  rotate_left
  · obtain ⟨Hrerr, -⟩ := Hrfail
    cases rerr with
    | nil => exact absurd rfl Hrerr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ipureintro; right; rfl
  subst Hrerr
  wp_auto
  wp_apply (wp_newUserClient xu.1.Client' go!"u" go!"u-pw" lg (akV xu.1.Client' xu.2.ρ wu.R)
      (akTokP wu.γa go!"u") (Hpe xu hxum) (by omega) (by unfold strsSizeOk; decide))
    as %ucl %uerr Huc
  · iframe #
    have hP : akTokP (GF := GF) wu.γa go!"u" = fun t => auth.tokIssued wu.γa t go!"u" := by
      unfold akTokP; rw [if_pos (by decide)]
    rw [hP]
    iapply (client.authTokReg_of _ _ _ wu.γa)
    iexact HAu₂
  icases Huc with (⟨%Huerr, #Hunc, #Hutk⟩ | %Hufail)
  rotate_left
  · obtain ⟨Huerr, -⟩ := Hufail
    cases uerr with
    | nil => exact absurd rfl Huerr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ipureintro; right; rfl
  subst Huerr
  wp_auto
  wp_apply (wp_newUserClient xv.1.Client' go!"v" go!"v-pw" lg (akV xv.1.Client' xv.2.ρ wv.R)
      (akTokP wv.γa go!"v") (Hpe xv hxvm) (by omega) (by unfold strsSizeOk; decide))
    as %vcl %verr Hvc
  · iframe #
    have hP : akTokP (GF := GF) wv.γa go!"v" = fun t => auth.tokIssued wv.γa t go!"v" := by
      unfold akTokP; rw [if_pos (by decide)]
    rw [hP]
    iapply (client.authTokReg_of _ _ _ wv.γa)
    iexact HAu₃
  icases Hvc with (⟨%Hverr, #Hvnc, #Hvtk⟩ | %Hvfail)
  rotate_left
  · obtain ⟨Hverr, -⟩ := Hvfail
    cases verr with
    | nil => exact absurd rfl Hverr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ipureintro; right; rfl
  subst Hverr
  wp_auto
  wp_apply (wp_NewClient xu.1.Client' lg (akV xu.1.Client' xu.2.ρ wu.R) (Hpe xu hxum) Htb31) as %bcl %berr Hbc
  · iframe #
  icases Hbc with (⟨%Hberr, #Hbnc, #Hbtk, -⟩ | %Hbfail)
  rotate_left
  · obtain ⟨Hberr, -⟩ := Hbfail
    cases berr with
    | nil => exact absurd rfl Hberr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ipureintro; right; rfl
  subst Hberr
  wp_auto
  -- `lz, ok := grantPut(root, zKey)`: root's lease `Lz` on `z/lease` (Fix: `cell_fix`, `cell_putZAu`)
  have hon₁ : w0.E.authOn = true := by unfold apply.AEnv.authOn; rw [HR₁.1]; rfl
  have hszL : ∀ (k : GoString) (id : w64), k.length ≤ 2 ^ 20 →
      opSizeOk (opPutModel k go!"v" [withLeaseM id]) := by
    intro k id hk
    simp [opSizeOk, opPutModel, opFold, withLeaseM, OpFull.putInit, OpFull.newOp, OpModel.zero]
    omega
  iunfold etcdstart.etcdLeaseServedOn at HLS₁
  icases HLS₁ with ⟨#HLG₁, #HLR₁, #HLT₁, #HLL₁⟩
  ihave #Hput₁ : isGrpcRpcMd x0.1.Client' go!"/etcdserverpb.KV/Put"
      (client.etcdPutSpecOn (srvTLSId s0) w0.E { x0.2.ρ with wait := w0.γw } w0.cid w0.mid) $$ []
  · iunfold akKVOn at HKV₁
    icases HKV₁ with ⟨#H, -, -, -⟩
    iexact H
  ihave #Hll₁ : srvReqLogLb x0.2.ρ.rd.raft Lset $$ []
  · iunfold akAuthFixed at Hfix₁
    icases Hfix₁ with ⟨-, -, #H, -⟩
    iexact H
  ihave #Hpub₁ : auth.authPubLbM w0.E.authMode i₁ $$ []
  · rw [HR₁.1]
    iunfold akAuthFixed at Hfix₁
    icases Hfix₁ with ⟨#H, -⟩
    iunfold auth.authPubLbM
    iexact H
  wp_apply (wp_grantPut rcl zK x0.1.Client' s0 w0.E { x0.2.ρ with wait := w0.γw } w0.cid w0.mid i₁ F₁
      (fun t => auth.tokIssued w0.γa t go!"root") (fun id => gsHas γc id) (fun _ => psAtLeast γc 1)
      (monoListAuthOwn γc.ids (1 : Qp).half ([] : List w64))
      (fun id => iprop(monoListAuthOwn γc.ids (1 : Qp).half [id] ∗ monoListLbOwn γc.ids [id] ∗
        ⌜id ≠ W64 0⌝))
      hon₁ (hlm x0 hx0m) (fun id => hszL zK id (by decide)) hAs) $$ [Hids] as %lz %okz Hz
  · iframe Hids; iframe #
    isplitl []
    · iintro !> %conn %ctx %id
      iunfold client.clientOpAuOn
      iexists Lset
      iframe Hll₁
      ihave #Hg := cell_grantAu s0 w0.E { x0.2.ρ with wait := w0.γw } conn ctx γc grantTTLv Lset
        (by decide) (hlm x0 hx0m) $$ Hinv
      iapply Hg
    iintro %id %hid ⟨%σ, Hg⟩ HR
    iunfold gsHas at Hg
    icases Hg with ⟨%gs, #Hgs, %hgs⟩
    imod (cell_fix x0.2.ρ.rd.kv γc [] id [] hid (by simp) (by simp) ⊤ (by simp)) $$ [HR] with ⟨HR', #Hlb⟩
    · iframe HR; iframe #
    imodintro
    ihave #Hlb1 : monoListLbOwn γc.ids [id] $$ []
    · iExactEq Hlb; simp
    isplitl [HR']
    · isplitl [HR']
      · iExactEq HR'; simp
      iframe Hlb1
      ipureintro; exact hid
    iintro !> %conn %ctx #Htk %hout
    iunfold client.clientOpAuOn
    iexists Lset
    iframe Hll₁
    ihave #Hpz := cell_putZAu x0.2.ρ.rd.kv γc id gs hgs
      (client.clientGrant (srvTLSId s0) w0.E { x0.2.ρ with wait := w0.γw } conn ctx (.put (leasePutOp zK id)) Lset) $$ [Hlb]
    · iframe #
    iexact Hpz
  icases Hz with (%Hz | ⟨%Hz, ⟨HidsZ, #HlbZ, %hlz0⟩, %σz, #HpsZ⟩) <;> subst Hz
  · wp_auto
    iapply HΦ; ipureintro; right; rfl
  wp_auto
  -- `lu, ok := grantPut(ucli, aKey)`: u's lease `Lu` on `a/lease` at member `1 % k` (Fix: `cell_fix`,
  -- `cell_putAAu`; `Lu ≠ Lz`: u's put with root's lease is refused, `grantG_refuted`)
  have hsu := hsc xu hxum
  have hon₂ : wu.E.authOn = true := by unfold apply.AEnv.authOn; rw [HR₂.1]; rfl
  ihave #Hinvu := cellInv_same x0.2.ρ.rd.kv xu.2.ρ.rd.kv γc hsu.1 $$ Hinv
  iunfold etcdstart.etcdLeaseServedOn at HLS₂
  icases HLS₂ with ⟨#HLG₂, #HLR₂, #HLT₂, #HLL₂⟩
  ihave #Hput₂ : isGrpcRpcMd xu.1.Client' go!"/etcdserverpb.KV/Put"
      (client.etcdPutSpecOn (srvTLSId su) wu.E { xu.2.ρ with wait := wu.γw } wu.cid wu.mid) $$ []
  · iunfold akKVOn at HKV₂
    icases HKV₂ with ⟨#H, -, -, -⟩
    iexact H
  ihave #Hll₂ : srvReqLogLb xu.2.ρ.rd.raft Lset $$ []
  · iunfold akAuthFixed at Hfix₂
    icases Hfix₂ with ⟨-, -, #H, -⟩
    iexact H
  ihave #Hpub₂ : auth.authPubLbM wu.E.authMode i₂ $$ []
  · rw [HR₂.1]
    iunfold akAuthFixed at Hfix₂
    icases Hfix₂ with ⟨#H, -⟩
    iunfold auth.authPubLbM
    iexact H
  iunfold psAtLeast at HpsZ
  icases HpsZ with ⟨%ps1, #Hps1, %hps1⟩
  have hau : akOut go!"u" = none := by unfold akOut; rw [if_neg (by decide)]
  wp_apply (wp_grantPut ucl aK xu.1.Client' su wu.E { xu.2.ρ with wait := wu.γw } wu.cid wu.mid i₂ F₂
      (akTokP wu.γa go!"u") (fun id => gsHas γc id) (fun _ => psAtLeast γc 2)
      (monoListAuthOwn γc.ids (1 : Qp).half [lz])
      (fun id => iprop(monoListAuthOwn γc.ids (1 : Qp).half [lz, id] ∗ monoListLbOwn γc.ids [lz, id] ∗
        ⌜id ≠ W64 0⌝))
      hon₂ (hlm xu hxum) (fun id => hszL aK id (by decide)) hAs) $$ [HidsZ] as %lu %oku Hu
  · iframe HidsZ; iframe #
    isplitl []
    · iintro !> %conn %ctx %id
      iunfold client.clientOpAuOn
      iexists Lset
      iframe Hll₂
      ihave #Hg := cell_grantAu su wu.E { xu.2.ρ with wait := wu.γw } conn ctx γc grantTTLv Lset
        (by decide) (hlm xu hxum) $$ Hinvu
      iapply Hg
    iintro %id %hid ⟨%σ, Hg⟩ HR
    iunfold gsHas at Hg
    icases Hg with ⟨%gs, #Hgs, %hgs⟩
    imod (cell_fix x0.2.ρ.rd.kv γc [lz] id ps1 hid (by simp) (by simp; omega) ⊤ (by simp)) $$ [HR]
      with ⟨HR', #Hlb⟩
    · iframe HR; iframe #
    imodintro
    ihave #Hlb1 : monoListLbOwn γc.ids [lz, id] $$ []
    · iExactEq Hlb; simp
    isplitl [HR']
    · isplitl [HR']
      · iExactEq HR'; simp
      iframe Hlb1
      ipureintro; exact hid
    iintro !> %conn %ctx #Htk %hout
    iunfold client.clientOpAuOn
    iexists Lset
    iframe Hll₂
    ihave #Hpa := cell_putAAu xu.2.ρ.rd.kv γc lz id gs ps1 hgs (by omega)
      (client.clientGrant (srvTLSId su) wu.E { xu.2.ρ with wait := wu.γw } conn ctx (.put (leasePutOp aK id)) Lset)
      $$ [Hlb1]
    · iframe #
      iintro !> %σ' %hz HG
      by_cases hil : id = lz
      · subst hil
        iunfold client.clientGrant at HG
        icases HG with ⟨%md, %Hmd, HG⟩
        ihave #Hs := akTokSeen_attempt wu.γa go!"u" conn md
          (by unfold clientAttemptMd at Hmd; rw [hout, ← hau] at Hmd; exact Hmd) $$ Htk
        iunfold v3rpc.opGrantT at HG
        imod (grantG_refuted su wu.E wu.γa { xu.2.ρ with wait := wu.γw } Lset i₂ go!"u" _
            (irrPut (leasePutOp aK id)) σ' zK id HR₂.1 hz hlz0
            (Or.inr (Or.inr (Or.inr ⟨rfl, not_inRangeK_zK⟩)))
            (fun r I hm h => leaseGranted_put r I _ hm h)) $$ [HG] with ⟨⟩
        · iframe #; iframe HG
      · imodintro; ipureintro; exact hil
    iexact Hpa
  icases Hu with (%Hu | ⟨%Hu, ⟨HidsU, #HlbU, %hlu0⟩, %σu, #HpsU⟩) <;> subst Hu
  · wp_auto
    iapply HΦ; ipureintro; right; rfl
  wp_auto
  -- u's transaction `Txn().Then(OpPut(txnKey, "v", WithLease(lu))).Commit()` (`cell_txnTAu`)
  ihave #Pcli : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ihave #Hutk0 := Hutk
  iunfold clientTokAt at Hutk0
  icases Hutk0 with ⟨%uapi, %uconn, #Hukvf, #Huobj, #Hutok, -, -, %ulp, #Hulf, #Hurem⟩
  iunfold psAtLeast at HpsU
  icases HpsU with ⟨%ps2, #Hps2, %hps2⟩
  ihave #HLc₂ := srvRLogLb_same { x0.2.ρ with wait := w0.γw } { xu.2.ρ with wait := wu.γw } hsu Lc $$ HLc
  ihave #Hc₂ : committedAtLeast xu.2.ρ.rd (W64 0) $$ []
  · iapply (committedAtLeast_of_rlog xu.2.ρ.rd (W64 0) Lc (by word))
    iexact HLc₂
  obtain ⟨hro, htsz, htsh, htpl, htnz, htnest⟩ := leaseTxn_ok tK lu (by decide) (by decide)
  ihave #HTx₂ : isGrpcRpcMd xu.1.Client' go!"/etcdserverpb.KV/Txn"
      (client.etcdTxnSpecOn (srvTLSId su) wu.E { xu.2.ρ with wait := wu.γw } xu.2.ρ.rd wu.cid wu.mid) $$ []
  · iunfold akKVOn at HKV₂
    icases HKV₂ with ⟨-, -, -, #H⟩
    iexact H
  wp_apply context.wp_Background
  (try wp_auto)
  wp_apply (client.wp_WithTimeout_bgMd wp_WithTimeout wp_ErrAny hAs _)
    as %tctx %tcd %tcancel ⟨#Htcancel, #Htctx, #Htce, -, #Htout, -⟩
  (try wp_auto)
  wp_apply wp_WithLease lu as %f #Hf
  (try wp_auto)
  wp_apply wp_slice_literal (l := [f])
  isplitr
  · ipureintro; rfl
  iintro %slo ⟨Hslo, -⟩
  ipersist Hslo
  ihave #Hopts := etcd_auth.optsAt_one (GF := GF) _ f (withLeaseM lu) $$ [Hslo Hf]
  · iframe #
  (try wp_auto)
  wp_apply (wp_OpPut tK go!"v" _ [withLeaseM lu]) as %op1 #Hop1
  · iframe #
    ipureintro
    simp [opPutModel, OpFull.putPanics, opFold, withLeaseM, OpFull.putInit, OpFull.newOp, OpModel.zero]
  (try wp_auto)
  wp_apply wp_slice_literal (l := [op1])
  isplitr
  · ipureintro; rfl
  iintro %tsl ⟨Htsl, -⟩
  ipersist Htsl
  ihave #Hops := etcd_auth.opsAt_one (GF := GF) _ op1 (opPutModel tK go!"v" [withLeaseM lu]) $$ [Htsl Hop1]
  · iframe #
  (try wp_auto)
  wp_apply (etcd_auth.client_Txn_on ucl uapi uconn xu.1.Client' tctx tcd) as %tv ⟨%tp, %Htv, Hobj, #Hkt⟩
  · iframe #
  subst Htv
  (try wp_auto)
  wp_apply (client.v3.txn.wp_Then_plain tp _ tctx tcd TxnBuild.empty _ _ [.put tK go!"v" lu]) $$ [Hobj] as Hobj
  · iframe #
    iframe Hobj
    ipureintro
    exact ⟨by simp [txnOpOf_leasePut], rfl, rfl⟩
  ihave Hobj : txnObjAt (GF := GF) tp [xu.1.Client'] tctx tcd ⟨leaseTxn tK lu, false, true, false⟩ $$ [Hobj]
  · iExactEq Hobj
    simp [TxnModel.empty, leaseTxn]
  (try wp_auto)
  wp_apply (client.client_txn_on tp uapi uconn xu.1.Client' (srvTLSId su) wu.E { xu.2.ρ with wait := wu.γw } xu.2.ρ.rd
      wu.cid wu.mid (W64 0) i₂ tctx none tcd ⟨leaseTxn tK lu, false, true, false⟩ (psAtLeast γc 3) F₂
      (fun h => by simp [hro] at h) htsz (fun _ => htsh)) $$ [Hobj] as %tresp %terr Ht
  · iframe Hobj; iframe #
    ileft
    imodintro
    iunfold client.txnUpdAtOn
    iright; iright
    isplitl []
    · ipureintro; exact ⟨hro, Or.inr ⟨hlm xu hxum, htpl⟩, htnz, htnest⟩
    iunfold client.clientOpAuOn
    iexists Lset
    iframe Hll₂
    ihave #Htx := cell_txnTAu xu.2.ρ.rd.kv γc lz lu ps2 hps2
      (client.clientGrant (srvTLSId su) wu.E { xu.2.ρ with wait := wu.γw } uconn none
        (.txn (txnWireOf (leaseTxn tK lu))) Lset) $$ []
    · iframe #
    iexact Htx
  (try wp_auto)
  wp_apply Htcancel
  (try wp_auto)
  icases Ht with (⟨%Hterr, %mt, -, Hrep, -⟩ | ⟨%Hterr, -⟩)
  rotate_left
  · cases terr with
    | nil => exact absurd rfl Hterr.1
    | ok ei =>
      (try wp_auto)
      iapply HΦ; ipureintro; right; rfl
  subst Hterr
  iunfold client.txnReplied at Hrep
  isimp only [hro, Bool.false_eq_true, ↓reduceIte] at Hrep
  icases Hrep with ⟨%tw, %hm, %rq', %t', %xa, %xa', %l, %skip, -, -, -, -, -, %ltt, -, #HpsT⟩
  iunfold psAtLeast at HpsT
  icases HpsT with ⟨%ps3, #Hps3, %hps3⟩
  (try wp_auto)
  -- `barriers(ms, lg)` again, the read update seeing the three attachments (`cell_readAu`); the lessor
  -- facts at u's member (Lz on z/lease) and v's member (Lu on a/lease) from their floors (`cell_holds`)
  ihave #Hbp2 : [∗list] b ∈ ((ss.zip xs).zip ws).map (bArg γz hs Lset Lc rset (cellSeen γc ps3 0)),
      barrierPre b $$ []
  · iclear Hbp1 Hbq1'
    rw [BigSepL.bigSepL_map (fun q => bArg γz hs Lset Lc rset (cellSeen γc ps3 0) q)]
    iapply (barrierPre_all x0 w0 γz hs Lset Lc rset _ _ hlq Hadm HLcst)
    iframe #
    iintro !> %ρ' %hρ'
    iright
    ihave #Hinv' := cellInv_same x0.2.ρ.rd.kv ρ'.rd.kv γc hρ'.1 $$ Hinv
    iapply (cell_readAu ρ'.rd.kv γc ps3 0)
    iframe #
  wp_apply (wp_barriers msl lg (xs.map (·.1)) _ (hmsb _) (by omega) hAs) as %okb2 Hb2
  · iframe #
  icases Hb2 with (%Hb | ⟨%Hb, #Hbq2⟩) <;> subst Hb
  · wp_auto
    iapply HΦ; ipureintro; right; rfl
  wp_auto
  ihave #Hbq2' : [∗list] q ∈ (ss.zip xs).zip ws,
      barrierPost (bArg γz hs Lset Lc rset (cellSeen γc ps3 0) q) $$ []
  · iclear Hbp1 Hbq1' Hbp2
    rw [← BigSepL.bigSepL_map (fun q => bArg γz hs Lset Lc rset (cellSeen γc ps3 0) q)]
    iexact Hbq2
  iclear Hbq2
  have hsv := hsc xv hxvm
  have hon₃ : wv.E.authOn = true := by unfold apply.AEnv.authOn; rw [HR₃.1]; rfl
  ihave #Gu := BigSepL.bigSepL_lookup hyu $$ Hbq2'
  iunfold barrierPost at Gu
  icases Gu with ⟨-, %Fu₂, %ltu₂, #HFu₂, #HSu⟩
  ihave #Gv := BigSepL.bigSepL_lookup hyv $$ Hbq2'
  iunfold barrierPost at Gv
  icases Gv with ⟨-, %Fv₂, %ltv₂, #HFv₂, #HSv⟩
  ihave #Hrdu : isServerReadM wu.E.authOn su wu.E xu.2.ρ.rd $$ []
  · rw [hon₂]; iexact Hrd₂
  ihave #Hrdv : isServerReadM wv.E.authOn sv wv.E xv.2.ρ.rd $$ []
  · rw [hon₃]; iexact Hrd₃
  ihave #Hinvv := cellInv_same x0.2.ρ.rd.kv xv.2.ρ.rd.kv γc hsv.1 $$ Hinv
  imod (cell_holds hlaw su wu.E xu.2.ρ.rd γc Fu₂ ltu₂ lz lu lz zK ps3 0 hps3
      (by rw [hsu.2.2.2.2.2.1]; exact hns) (Or.inl ⟨rfl, rfl⟩)) $$ [] with ⟨%mz, #Hlbz, #Hhz⟩
  · iframe #
  imod (cell_holds hlaw sv wv.E xv.2.ρ.rd γc Fv₂ ltv₂ lz lu lu aK ps3 0 hps3
      (by rw [hsv.2.2.2.2.2.1]; exact hns) (Or.inr ⟨rfl, rfl⟩)) $$ [] with ⟨%mu, #Hlbu, #Hhu⟩
  · iframe #
  -- `noAuth(cli, "anon", lu)` at member 0, `noAuth(bcli, "bad", lu)` at member `1 % k`: member 0's
  -- lessor bound from the lessor law at its second barrier's floor
  ihave #G0 := BigSepL.bigSepL_lookup hy0 $$ Hbq2'
  iunfold barrierPost at G0
  icases G0 with ⟨-, %F0₂, %lt0₂, #HF0₂, -⟩
  ihave #Hrd0 : isServerReadM w0.E.authOn s0 w0.E x0.2.ρ.rd $$ []
  · rw [hon₁]; iexact Hrd₁
  imod (hlaw s0 w0.E x0.2.ρ.rd F0₂ lz zK hns) $$ [] with ⟨%m0, #Hlb0, -⟩
  · iframe Hrd0 HF0₂
  have hpa : akTokP (GF := GF) w0.γa go!"anon" = fun _ => iprop(False) := by
    unfold akTokP; rw [if_neg (by decide)]
  ihave #HLS0 : etcdstart.etcdLeaseServedOn x0.1.Client' s0 w0.E { x0.2.ρ with wait := w0.γw } $$ []
  · iunfold etcdstart.etcdLeaseServedOn; iframe #
  ihave #Hna0 := noAuth_refutes s0 w0.E w0.γa _ Lset i₁ go!"anon" HR₁.1 (Or.inl rfl) $$ [Hfix₁ Htls₁]
  · iframe #
  ihave #Hrv0 := revokeLu_update s0 w0.E w0.γa { x0.2.ρ with wait := w0.γw } Lset i₁ go!"anon" γc lz lu ps3
    hps3 hlu0 HR₁.1 (Or.inl rfl) $$ [Hinv HlbU Hps3 Hfix₁ Htls₁]
  · iframe #
  wp_apply (wp_noAuth cl go!"anon" x0.1.Client' lu s0 w0.E { x0.2.ρ with wait := w0.γw } w0.γa i₁ m0
      (fun id => gsHas γc id) (revoked γc) (Or.inl rfl) hAs)
  · rw [hpa]; iframe #
    iintro !> %conn %ctx %id
    iunfold client.clientOpAuOn
    iexists Lset
    iframe Hll₁
    ihave #Hg := cell_grantAu s0 w0.E { x0.2.ρ with wait := w0.γw } conn ctx γc grantTTLv Lset
      (by decide) (hlm x0 hx0m) $$ Hinv
    iapply Hg
  (try wp_auto)
  have hpb : akTokP (GF := GF) wu.γa go!"bad" = fun _ => iprop(False) := by
    unfold akTokP; rw [if_neg (by decide)]
  ihave #HLSu : etcdstart.etcdLeaseServedOn xu.1.Client' su wu.E { xu.2.ρ with wait := wu.γw } $$ []
  · iunfold etcdstart.etcdLeaseServedOn; iframe #
  ihave #Hnau := noAuth_refutes su wu.E wu.γa _ Lset i₂ go!"bad" HR₂.1 (Or.inr rfl) $$ [Hfix₂ Htls₂]
  · iframe #
  ihave #Hrvu := revokeLu_update su wu.E wu.γa { xu.2.ρ with wait := wu.γw } Lset i₂ go!"bad" γc lz lu ps3
    hps3 hlu0 HR₂.1 (Or.inr (Or.inl rfl)) $$ [Hinvu HlbU Hps3 Hfix₂ Htls₂]
  · iframe #
  wp_apply (wp_noAuth bcl go!"bad" xu.1.Client' lu su wu.E { xu.2.ρ with wait := wu.γw } wu.γa i₂ mz
      (fun id => gsHas γc id) (revoked γc) (Or.inr rfl) hAs)
  · rw [hpb]; iframe #
    iintro !> %conn %ctx %id
    iunfold client.clientOpAuOn
    iexists Lset
    iframe Hll₂
    ihave #Hg := cell_grantAu su wu.E { xu.2.ρ with wait := wu.γw } conn ctx γc grantTTLv Lset
      (by decide) (hlm xu hxum) $$ Hinvu
    iapply Hg
  (try wp_auto)
  -- u's put of `a/x` with root's lease `Lz`, refused (`refused_update`: `Lz` holds `z/lease`)
  have hcellZ : ∀ σ ids ps gs d, CellOk σ ids ps gs d → [lz] <+: ids → ps1.length ≤ ps.length →
      leaseOf zK σ.kvs = some lz ∧ lz ≠ W64 0 := by
    intro σ ids ps gs d h hpre hps
    obtain ⟨t, rfl⟩ := hpre
    have hz := h.1.z_at (by omega)
    simp [lzOf] at hz
    exact ⟨hz, hlz0⟩
  ihave #Hrfp := refused_update su wu.E wu.γa { xu.2.ρ with wait := wu.γw } Lset i₂ go!"u" γc
      (.put (leasePutOp xK lz)) zK lz [lz] ps1 (fun _ => iprop(False)) HR₂.1
      (opChecksLease_put su wu.E _ (leasePutOp xK lz)) hcellZ
      (Or.inr (Or.inr (Or.inr ⟨rfl, not_inRangeK_zK⟩))) $$ [Hinvu HlbZ Hps1 Hfix₂ Htls₂]
  · iframe #
  wp_apply context.wp_Background
  (try wp_auto)
  wp_apply (client.wp_WithTimeout_bgMd wp_WithTimeout wp_ErrAny hAs _)
    as %pctx %pcd %pcancel ⟨#Hpcancel, #Hpctx, #Hpce, -, #Hpout, -⟩
  (try wp_auto)
  wp_apply wp_WithLease lz as %f2 #Hf2
  (try wp_auto)
  wp_apply wp_slice_literal (l := [f2])
  isplitr
  · ipureintro; rfl
  iintro %slo2 ⟨Hslo2, -⟩
  ipersist Hslo2
  ihave #Hopts2 := etcd_auth.optsAt_one (GF := GF) _ f2 (withLeaseM lz) $$ [Hslo2 Hf2]
  · iframe #
  (try wp_auto)
  rw [go_etcd_io.etcd.client.v3.Client.TypeAssumptions.ptr_Put_unfold.method_unfold]
  wp_pures
  (try wp_auto)
  have hokx : ¬ (opPutModel xK go!"v" [withLeaseM lz]).putPanics ∧
      (opPutModel xK go!"v" [withLeaseM lz]).t = W64 2 :=
    ⟨by simp [opPutModel, OpFull.putPanics, opFold, withLeaseM, OpFull.putInit, OpFull.newOp, OpModel.zero],
      rfl⟩
  wp_apply (client.client_put_on uapi uconn xu.1.Client' (srvTLSId su) wu.E { xu.2.ρ with wait := wu.γw } wu.cid wu.mid
      pctx none pcd xK go!"v" _ [withLeaseM lz] (fun _ => iprop(False)) F₂
      (hszL xK lz (by decide)) hokx.1 hokx.2 (Or.inr (hlm xu hxum))) as %presp %perr Hp
  · iframe #
    ileft
    imodintro
    rw [leasePut_wire]
    iapply Hrfp
    · iexact Hutok
    · ipureintro; exact hau.symm
  (try wp_auto)
  wp_apply Hpcancel
  (try wp_auto)
  icases Hp with (⟨%Hperr, %mp, -, Hrep, -⟩ | ⟨%Hperr, -⟩)
  · iunfold client.putReplied at Hrep
    icases Hrep with ⟨%hm', %x, %x', %l, %skip, -, -, -, -, -, %lt, -, Hf⟩
    iexfalso
    iexact Hf
  wp_apply (wp_refused go!"u" _ perr Hperr.1)
  (try wp_auto)
  -- u's transaction putting `a/x` with `Lz`, refused (`refused_update`, `opChecksLease_txn`)
  ihave #Hrft := refused_update su wu.E wu.γa { xu.2.ρ with wait := wu.γw } Lset i₂ go!"u" γc
      (.txn (txnWireOf (leaseTxn xK lz))) zK lz [lz] ps1 (fun _ => iprop(False)) HR₂.1
      (opChecksLease_txn su wu.E _ xK lz) hcellZ
      (Or.inr (Or.inr (Or.inr ⟨rfl, not_inRangeK_zK⟩))) $$ [Hinvu HlbZ Hps1 Hfix₂ Htls₂]
  · iframe #
  obtain ⟨hro', htsz', htsh', htpl', htnz', htnest'⟩ := leaseTxn_ok xK lz (by decide) (by decide)
  wp_apply context.wp_Background
  (try wp_auto)
  wp_apply (client.wp_WithTimeout_bgMd wp_WithTimeout wp_ErrAny hAs _)
    as %xctx %xcd %xcancel ⟨#Hxcancel, #Hxctx, #Hxce, -, #Hxout, -⟩
  (try wp_auto)
  wp_apply wp_WithLease lz as %f3 #Hf3
  (try wp_auto)
  wp_apply wp_slice_literal (l := [f3])
  isplitr
  · ipureintro; rfl
  iintro %slo3 ⟨Hslo3, -⟩
  ipersist Hslo3
  ihave #Hopts3 := etcd_auth.optsAt_one (GF := GF) _ f3 (withLeaseM lz) $$ [Hslo3 Hf3]
  · iframe #
  (try wp_auto)
  wp_apply (wp_OpPut xK go!"v" _ [withLeaseM lz]) as %op3 #Hop3
  · iframe #
    ipureintro
    simp [opPutModel, OpFull.putPanics, opFold, withLeaseM, OpFull.putInit, OpFull.newOp, OpModel.zero]
  (try wp_auto)
  wp_apply wp_slice_literal (l := [op3])
  isplitr
  · ipureintro; rfl
  iintro %tsl3 ⟨Htsl3, -⟩
  ipersist Htsl3
  ihave #Hops3 := etcd_auth.opsAt_one (GF := GF) _ op3 (opPutModel xK go!"v" [withLeaseM lz]) $$ [Htsl3 Hop3]
  · iframe #
  (try wp_auto)
  wp_apply (etcd_auth.client_Txn_on ucl uapi uconn xu.1.Client' xctx xcd) as %tv3 ⟨%tp3, %Htv3, Hobj3, #Hkt3⟩
  · iframe #
  subst Htv3
  (try wp_auto)
  wp_apply (client.v3.txn.wp_Then_plain tp3 _ xctx xcd TxnBuild.empty _ _ [.put xK go!"v" lz]) $$ [Hobj3]
    as Hobj3
  · iframe #
    iframe Hobj3
    ipureintro
    exact ⟨by simp [txnOpOf_leasePut], rfl, rfl⟩
  ihave Hobj3 : txnObjAt (GF := GF) tp3 [xu.1.Client'] xctx xcd ⟨leaseTxn xK lz, false, true, false⟩ $$ [Hobj3]
  · iExactEq Hobj3
    simp [TxnModel.empty, leaseTxn]
  (try wp_auto)
  wp_apply (client.client_txn_on tp3 uapi uconn xu.1.Client' (srvTLSId su) wu.E { xu.2.ρ with wait := wu.γw } xu.2.ρ.rd
      wu.cid wu.mid (W64 0) i₂ xctx none xcd ⟨leaseTxn xK lz, false, true, false⟩ (fun _ => iprop(False)) F₂
      (fun h => by simp [hro'] at h) htsz' (fun _ => htsh')) $$ [Hobj3] as %xresp %xerr Hx
  · iframe Hobj3; iframe #
    ileft
    imodintro
    iunfold client.txnUpdAtOn
    iright; iright
    isplitl []
    · ipureintro; exact ⟨hro', Or.inr ⟨hlm xu hxum, htpl'⟩, htnz', htnest'⟩
    iapply Hrft
    · iexact Hutok
    · ipureintro; exact hau.symm
  (try wp_auto)
  wp_apply Hxcancel
  (try wp_auto)
  icases Hx with (⟨%Hxerr, %mx, -, Hrepx, -⟩ | ⟨%Hxerr, -⟩)
  · iunfold client.txnReplied at Hrepx
    isimp only [hro', Bool.false_eq_true, ↓reduceIte] at Hrepx
    icases Hrepx with ⟨%tw', %hm', %rq'', %t'', %xb, %xb', %l', %skip', -, -, -, -, -, %ltt', -, Hf⟩
    iexfalso
    iexact Hf
  wp_apply (wp_refused go!"u" _ xerr Hxerr.1)
  (try wp_auto)
  -- `absent(root, xKey, ...)` at member 0 (the read update `cellSeen`: `a/x` is never written)
  ihave #Hc₁ : committedAtLeast x0.2.ρ.rd (W64 0) $$ []
  · iapply (committedAtLeast_of_rlog x0.2.ρ.rd (W64 0) Lc (by word))
    iexact HLc
  ihave #Hrng₁ : isGrpcRpcMd x0.1.Client' go!"/etcdserverpb.KV/Range"
      (client.etcdRangeSpecOn (srvTLSId s0) w0.E x0.2.ρ.rd w0.cid w0.mid) $$ []
  · iunfold akKVOn at HKV₁
    icases HKV₁ with ⟨-, #H, -⟩
    iexact H
  have hszG : ∀ k : GoString, k.length ≤ 2 ^ 20 → opSizeOk (opGetModel k []) := fun k hk =>
    opSizeOk_opGetModel (K := 2 ^ 28) (E := 0) (V := 0) (optsKeep_nil _ _ _) (by omega) (by decide)
  wp_apply (wp_absent rcl xK _ x0.1.Client' s0 w0.E x0.2.ρ.rd w0.cid w0.mid (W64 0) i₁ F0₂
      (fun t => auth.tokIssued w0.γa t go!"root") (cellSeen γc ps3 0) (hszG xK (by decide)) hAs)
    as %okx -
  · iframe #
    isplitl []
    · iintro !>
      iright
      iapply (cell_readAu x0.2.ρ.rd.kv γc ps3 0)
      iframe #
    iintro !> %m Hm
    ihave ⟨%σ, #HQ, %Hk⟩ := getReply_state w0.E x0.2.ρ.rd (W64 0) w0.cid w0.mid F0₂ xK _ m $$ Hm
    ihave %Hc := seen_cell γc ps3 0 σ $$ HQ
    obtain ⟨ids, ps, gs, d, hok, -, -⟩ := Hc
    ipureintro
    rw [Hk.1]
    exact client.filter_key_of_findKey_none _ _ hok.1.x_none
  cases okx
  · wp_auto
    iapply HΦ; ipureintro; right; rfl
  (try wp_auto)
  -- `foreign(ucli, "u", lz)` at member `1 % k`: its revocation refused (`Lz` holds `z/lease`), its
  -- lessor reads refuted while the main thread holds u's revocation unpermitted (`R`, `holdsFrom`)
  ihave #Hrfr := refused_update su wu.E wu.γa { xu.2.ρ with wait := wu.γw } Lset i₂ go!"u" γc
      (.leaseRevoke lz) zK lz [lz] ps1 (fun _ => iprop(False)) HR₂.1
      (opChecksLease_revoke su wu.E _ lz) hcellZ
      (Or.inr (Or.inr (Or.inr ⟨rfl, not_inRangeK_zK⟩))) $$ [Hinvu HlbZ Hps1 Hfix₂ Htls₂]
  · iframe #
  ihave ⟨#Hfu1, #Hfu2⟩ := foreign_reads_refuted su wu.E wu.γa _ Lset i₂ go!"u" γc
      (mvcc.api.mvccLeases wu.E.γ) mz lz zK HR₂.1 (by decide) (Or.inl ⟨rfl, not_inRangeK_zK⟩)
      $$ [Hfix₂ Htls₂ Hhz]
  · iframe #
  wp_apply (wp_foreign ucl go!"u" xu.1.Client' lz su wu.E { xu.2.ρ with wait := wu.γw } wu.γa i₂ mz
      (fun _ => iprop(False)) (monoNatAuthOwn γc.a (1 : Qp).half 0) (Or.inl rfl) hon₂ hAs) $$ [Ha] as Ha
  · iframe Ha; iframe #
    iintro !> %σ Hf _
    iexfalso; iexact Hf
  (try wp_auto)
  -- `foreign(vcli, "v", lu)` at member `2 % k`: a revocation of `Lu` tells `revoked`, refuted while
  -- the main thread holds u's revocation unpermitted (`cell_not_revoked`)
  ihave #Hpub₃ : auth.authPubLbM wv.E.authMode i₃ $$ []
  · rw [HR₃.1]
    iunfold akAuthFixed at Hfix₃
    icases Hfix₃ with ⟨#H, -⟩
    iunfold auth.authPubLbM
    iexact H
  iunfold etcdstart.etcdLeaseServedOn at HLS₃
  icases HLS₃ with ⟨#HLG₃, #HLR₃, #HLT₃, #HLL₃⟩
  ihave #HLSv : etcdstart.etcdLeaseServedOn xv.1.Client' sv wv.E { xv.2.ρ with wait := wv.γw } $$ []
  · iunfold etcdstart.etcdLeaseServedOn; iframe #
  ihave #Hrvv := revokeLu_update sv wv.E wv.γa { xv.2.ρ with wait := wv.γw } Lset i₃ go!"v" γc lz lu ps3
    hps3 hlu0 HR₃.1 (Or.inr (Or.inr rfl)) $$ [Hinvv HlbU Hps3 Hfix₃ Htls₃]
  · iframe #
  ihave ⟨#Hfv1, #Hfv2⟩ := foreign_reads_refuted sv wv.E wv.γa _ Lset i₃ go!"v" γc
      (mvcc.api.mvccLeases wv.E.γ) mu lu aK HR₃.1 (by decide) (Or.inr rfl) $$ [Hfix₃ Htls₃ Hhu]
  · iframe #
  wp_apply (wp_foreign vcl go!"v" xv.1.Client' lu sv wv.E { xv.2.ρ with wait := wv.γw } wv.γa i₃ mu
      (revoked γc) (monoNatAuthOwn γc.a (1 : Qp).half 0) (Or.inr rfl) hon₃ hAs) $$ [Ha] as Ha
  · iframe Ha; iframe #
    iintro !> %σ #Hr Ha
    iapply (cell_not_revoked xv.2.ρ.rd.kv γc σ ⊤ (by simp))
    iframe Ha; iframe #
  (try wp_auto)
  -- root's `Get(zKey)` at member 0: `z/lease` on `Lz` (the read update `cellSeen`, `seen_z`)
  ihave #Hrtk0 := Hrtk
  iunfold clientTokAt at Hrtk0
  icases Hrtk0 with ⟨%rapi, %rconn, #Hrkvf, #Hrobj, -, -, -⟩
  wp_apply context.wp_Background
  (try wp_auto)
  wp_apply (client.wp_WithTimeout_bgMd wp_WithTimeout wp_ErrAny hAs _)
    as %gctx %gcd %gcancel ⟨#Hgcancel, #Hgctx, #Hgce, -, #Hgout, -⟩
  (try wp_auto)
  ihave #Hnil := optsAt_nil (GF := GF)
  ihave Hres := optsAt_res slice.nil [] iprop(True) $$ Hnil
  wp_apply (etcd_auth.client_Get_on rcl rapi rconn x0.1.Client' s0 w0.E x0.2.ρ.rd w0.cid w0.mid (W64 0) i₁
      gctx none gcd zK slice.nil [] iprop(True) (cellSeen γc ps1 0) F0₂ (hszG zK (by decide))) $$ [Hres]
    as %gresp %gerr Hgout
  · iframe #
    rw [show (opGetModel zK []).base.sortSet = false from rfl]
    isplitl []
    · unfold sortNamesIf; simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
    isplitl []
    · ipureintro; exact ⟨by simp [opGetPanics, opFold, OpFull.newOp, OpModel.zero], rfl⟩
    iintro !>
    iright
    isplitl []
    · ipureintro; rfl
    iapply (cell_readAu x0.2.ρ.rd.kv γc ps1 0)
    iframe #
  (try wp_auto)
  wp_apply Hgcancel
  (try wp_auto)
  icases Hgout with ⟨-, (⟨%Hgerr, %mg, #Hmg, #Hgok, -⟩ | ⟨%Hgerr, -⟩)⟩
  rotate_left
  · cases gerr with
    | nil => exact absurd rfl Hgerr.1
    | ok e =>
      (try wp_auto)
      iapply HΦ; ipureintro; right; rfl
  subst Hgerr
  (try wp_auto)
  ihave ⟨%σg, #HQg, %Hkg⟩ := getReply_state w0.E x0.2.ρ.rd (W64 0) w0.cid w0.mid F0₂ zK _ mg $$ Hgok
  ihave %Hzg := seen_z γc ps1 0 σg lz hps1 $$ [HQg HlbZ]
  · iframe #
  obtain ⟨kvz, hfz, hlz⟩ := leaseOf_some_findKey Hzg
  have hkvs : mg.kvs = [kvz] := by
    rw [Hkg.1]; exact client.filter_key_of_findKey zK _ Hkg.2 kvz hfz
  iunfold rangeRespMsg at Hmg
  icases Hmg with ⟨%Hnn, %h, %sl, %kvps, #Hh, #Hhf, #Hkvf', #Hsl, #Hkvs, #Hmore, #Hcount⟩
  iunfold txn.kvsIs at Hkvs
  icases Hkvs with ⟨%Hlen', #Hall⟩
  obtain ⟨p0, Hp0⟩ : ∃ p0, kvps[0]? = some p0 := by
    have : 0 < kvps.length := by rw [Hlen', hkvs]; simp
    exact ⟨kvps[0], List.getElem?_eq_getElem this⟩
  ihave #Hkv := Hall $$ %0 %p0 %kvz %Hp0 %(by rw [hkvs]; rfl)
  iunfold txn.kvIs at Hkv
  icases Hkv with ⟨%kSl, %vSl, -, -, -, -, -, -, -, #HlF, -⟩
  ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
  have H1 : sl.len = W64 1 := by
    have hl := Hsll.1
    rw [Hlen', hkvs] at hl
    simp at hl
    word
  (try wp_auto)
  simp only [H1]
  (try wp_auto)
  have Hbnd : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z sl.len := by rw [H1]; constructor <;> word
  simp only [Hbnd, _root_.and_self, ↓reduceIte]
  wp_apply wp_load_slice_index _ (sint.Z (W64 0)) _ DFrac.discard p0 Hbnd.1 $$ [Hsl] as -
  · iframe Hsl; ipureintro; exact Hp0
  (try wp_auto)
  simp only [hlz]
  (try wp_auto)
  -- u revokes its own lease `Lu` (`cell_permit`, then `cell_revokeUAu`): the update tells `revoked`
  imod (cell_permit x0.2.ρ.rd.kv γc ⊤ (by simp)) $$ [Ha] with ⟨Ha1, #Hal1⟩
  · iframe Ha; iframe #
  wp_apply context.wp_Background
  (try wp_auto)
  wp_apply (client.wp_WithTimeout_bgMd wp_WithTimeout wp_ErrAny hAs _)
    as %rctx %rcd %rcancel ⟨#Hrcancel, #Hrctx, #Hrce, -, #Hrout, -⟩
  (try wp_auto)
  wp_apply (client.client_lease_revoke_on ulp uconn xu.1.Client' (srvTLSId su) wu.E { xu.2.ρ with wait := wu.γw } rctx none rcd
      i₂ lu (revoked γc)) as %rresp %rerr Hrv
  · iframe #
    iintro !>
    iunfold client.clientOpAuOn
    iexists Lset
    iframe Hll₂
    ihave #Hrvk := cell_revokeUAu xu.2.ρ.rd.kv γc lz lu ps3 hps3
      (client.clientGrant (srvTLSId su) wu.E { xu.2.ρ with wait := wu.γw } uconn none (.leaseRevoke lu) Lset)
      $$ [Hinvu HlbU Hps3 Hal1]
    · iframe #
    iexact Hrvk
  (try wp_auto)
  wp_apply Hrcancel
  (try wp_auto)
  icases Hrv with (⟨%Hrerr, %mr, -, -, %rmd, -, Hres, -⟩ | ⟨%Hrerr, -⟩)
  rotate_left
  · cases rerr with
    | nil => exact absurd rfl Hrerr.1
    | ok e =>
      (try wp_auto)
      iapply HΦ; ipureintro; right; rfl
  subst Hrerr
  iunfold v3rpc.leaseRevokeResT at Hres
  ihave Hres := Hres $$ %hon₂
  icases Hres with ⟨%hmr, %Lr, -, -, -, #Hrvd⟩
  iunfold revoked at Hrvd
  (try wp_auto)
  -- `absent(root, aKey, ...)`, `absent(root, txnKey, ...)` (the read update `cellSeen … 1`: `seen_gone`)
  wp_apply (wp_absent rcl aK _ x0.1.Client' s0 w0.E x0.2.ρ.rd w0.cid w0.mid (W64 0) i₁ F0₂
      (fun t => auth.tokIssued w0.γa t go!"root") (cellSeen γc ps3 1) (hszG aK (by decide)) hAs)
    as %oka -
  · iframe #
    isplitl []
    · iintro !>
      iright
      iapply (cell_readAu x0.2.ρ.rd.kv γc ps3 1)
      iframe #
    iintro !> %m Hm
    ihave ⟨%σ, #HQ, %Hk⟩ := getReply_state w0.E x0.2.ρ.rd (W64 0) w0.cid w0.mid F0₂ aK _ m $$ Hm
    ihave %Hg := seen_gone γc ps3 σ $$ HQ
    ipureintro
    rw [Hk.1]
    exact client.filter_key_of_findKey_none _ _ Hg.1
  cases oka
  · wp_auto
    iapply HΦ; ipureintro; right; rfl
  (try wp_auto)
  wp_apply (wp_absent rcl tK _ x0.1.Client' s0 w0.E x0.2.ρ.rd w0.cid w0.mid (W64 0) i₁ F0₂
      (fun t => auth.tokIssued w0.γa t go!"root") (cellSeen γc ps3 1) (hszG tK (by decide)) hAs)
    as %okt -
  · iframe #
    isplitl []
    · iintro !>
      iright
      iapply (cell_readAu x0.2.ρ.rd.kv γc ps3 1)
      iframe #
    iintro !> %m Hm
    ihave ⟨%σ, #HQ, %Hk⟩ := getReply_state w0.E x0.2.ρ.rd (W64 0) w0.cid w0.mid F0₂ tK _ m $$ Hm
    ihave %Hg := seen_gone γc ps3 σ $$ HQ
    ipureintro
    rw [Hk.1]
    exact client.filter_key_of_findKey_none _ _ Hg.2
  cases okt
  · wp_auto
    iapply HΦ; ipureintro; right; rfl
  (try wp_auto)
  iapply HΦ; ipureintro; left; rfl

end proof

end etcd_authlease
end EtcdGrove
end Perennial

/-
**`applyAll`'s `msgSnapC` branch, its two calls** (D22 S-h, 2026-10-20; `notes/decisions.md`, "D22
S-h carried out"): `s.sendMergedSnap(s.createMergedSnapshotMessage(m, ep.appliedt, ep.appliedi,
ep.confState))` (`server.go`; the `merged` local inlined), over the two proved specs and the
bundle lemma (`srvMergedBundle`). Lean-first (no Rocq counterpart).

The branch is dead in the proof until S-l (`isServerApplyAll`'s `msgSnapC` carries nothing);
`snapBranch_send` is what S-l applies there, after the receive and the `m.GetTerm() ==
apply.raftTerm` check, with these premises to discharge:
* the received message owned (`msgOwn m (DFrac.own 1) st`, a `MsgSnap` of raft's with its snapshot
  `sn0` at most the applied index) with its protocol facts (`isRaftMsg`, `termLB`): since D22 S-l's
  sender items (2026-10-22) `msgSnapC`'s bag carries exactly these (`rnSnapMsg`, `isRNMsgSnapC`);
  `sn0`'s bound is still to be stated (raft's storage snapshot, at an applied index); raft's
  commit invariant;
* `rnRtBound γ T ai` at the message's term `T = apply.raftTerm` (D22l; `rnRtBound_of_rtOk` from the
  batch's `rnRtOk`, `rnApP_rtOk`, for `T ≠ 0` and the batch's log reaching `ai`);
* the applied committed prefix `A` (`|A| = ai`, last term `at`: `kvApplied`'s `srvRLogLb` with
  S-0's `at' = lastTerm` amendment);
* the contracts of `s.KV().Commit()` (`srvKVCommitOk_of_kv`, from `store.Commit`, translated and
  proved since D22 S-l's sender items: the writer's fragment, reader token and a write token,
  `srvWTPool_take_extra`) and `s.be.Snapshot()` (`srvBeSnapOk_of_backend`) with their resources, and the image
  certificate from the snapshot's observation (`□ (∀ D, ⌜Qd D⌝ -∗ srvImage γ ai D)`: the modeled
  half from `backend.Snapshot`'s observation, `imageAt_of_snap`, the rest from the D22c
  determinism fact);
* `sendMergedSnap`'s resources (`GoAttach`'s, the started transport of the network whose payload
  is the server's, `srvNet γ bud`, `s.inflightSnapshots`'s invariant, `s.stopping`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapSendBundle
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__createMergedSnapshotMessage
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__sendMergedSnap
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__Snapshot
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__Commit
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.KVView
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.KVWrite

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The merged snapshot made and sent** (see the file header). -/
theorem snapBranch_send
    (hCM : EtcdServer.createMergedSnapshotMessage.spec (GF := GF) (hG := hG))
    (hSMS : EtcdServer.sendMergedSnap.spec (GF := GF) (hG := hG))
    (s ml : Loc) (st : MsgSt) (sn0 : SnapshotM) (ai at_ : w64) (cs lg : Loc) (kv be : GoInterface)
    (RC RC' RS RS' : IProp GF) (Qd : backend.Data → Prop) (γ : RaftNames) (bud : BudgetNames)
    (A : List EntryM) (id : w64) (stg : Loc) (tr : GoInterface) (γn : NetNames GF)
    (Hty : st.msg.Type' = MsgSnap) (Hsn : st.snap = some sn0)
    (Hix : uint.Z sn0.Metadata'.Index' ≤ uint.Z ai)
    (HAlen : (A.length : Int) = uint.Z ai) (HAlast : A.getLast?.map EntryM.Term' = some at_)
    (HN : γn.N = srvNet γ bud)
    -- (D22 S-r, 2026-10-21) the cluster admits the merged snapshot's (empty) data
    (Hsok : γ.reSnapOk A []) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        srvGoRes s ∗ srvLgReader s ∗ srvLgAddr s ↦□ lg ∗ ⌜lg ≠ null⌝ ∗
        srvKVAddr s ↦□ kv ∗ srvKVCommitOk kv RC RC' ∗ RC ∗
        srvBeAddr s ↦□ be ∗ srvBeSnapOk be RS RS' Qd ∗ RS ∗
        msgOwn ml (DFrac.own 1) st ∗ epCsOk cs ∗
        raftCommitInv γ ∗ isRaftMsg γ st ∗ termLB bud st.msg.Term' ∗ rnRtBound γ st.msg.Term' ai ∗
        isCommitted γ A ∗ □ (∀ D, ⌜Qd D⌝ -∗ srvImage γ ai D) ∗
        -- (D22 S-b′3, 2026-10-20) the merged content's configuration certificate, of whatever
        -- `ep.confState` holds
        □ (∀ c : ConfStateM, csOpt cs DFrac.discard c -∗
          raftSnapCert γ ⟨⟨at_, ai⟩, ConfStateM.lists c, c.AutoLeave', []⟩) ∗
        srvMemberIDAddr s ↦□ id ∗ srvInflight s ∗ srvStoppingAddr s ↦□ stg ∗ stopChan stg ∗
        rnTransportAddr (srvRAddr s) ↦□ tr ∗ netTransport γn tr }}
      (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"sendMergedSnap"))
        (App (App (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!!
          go!"createMergedSnapshotMessage")) (Val #ml)) (Val #at_)) (Val #ai)) (Val #cs)))
    {{ RET #(); srvGoRes s ∗ srvLgReader s ∗ RC' ∗ RS' }} := by
  iintro %Φ ⟨#Hpkg, Hgr, Hlr, #Hlgf, %Hlgnn, #Hkvf, Hkc, HRC, #Hbef, Hbs, HRS, Hm, #Hcs, #Hinv,
    #Hrm, #Htlb, #Hbnd, #HA, #Himg, #Hccs, #Hidf, #Hinf, #Hstgf, #Hstg, #Htrf, #Htr⟩ HΦ
  wp_apply hCM s ml st at_ ai cs lg kv be RC RC' RS RS' Qd $$ [Hlr Hkc HRC Hbs HRS Hm]
    as %mg ⟨Hlr, HRC', HRS', %rc, %D, %c, #Hmg, #Hml, #Hcso, Hrs, %HQ⟩
  · iframe #; iframe
    ipureintro; exact Hlgnn
  ihave #HimgD := Himg $$ %D %HQ
  ihave #Hcc := Hccs $$ %c Hcso
  imod srvMergedBundle γ bud ⊤ ml st sn0 c ai at_ A rc D (by simp) Hty Hsn Hix HAlen HAlast Hsok
    $$ Hinv Hrm Htlb Hbnd HA Hcc Hml Hrs HimgD with Hbun
  wp_apply hSMS s mg ml rc lg id stg tr γn $$ [Hgr Hlr Hbun] as ⟨Hgr, Hlr⟩
  · iframe #; iframe Hgr Hlr
    isplitr
    · ipureintro; exact Hlgnn
    rw [HN]; iexact Hbun
  iapply HΦ
  iframe

/-- **The snapshot contract from the backend's** (`backend.Snapshot.spec`): the real backend `bl`'s
`Snapshot()`, with an open share, a write-back's budget token and the caller's resource `R`, whose
observation `Q` of every commit (with the batch lock's client resource `W` and hooks' `Pk`) is
what the snapshot's data `D` satisfies (as `Q (sData P D) (hkData P D)`). -/
theorem srvBeSnapOk_of_backend (hSnap : backend.backend.Snapshot.spec (GF := GF) (hG := hG))
    (γ : backend.BNames) (P : backend.BParams) (W Pk : IProp GF) (bl : Loc) (qo : Qp)
    (R : IProp GF)
    (Q : backend.VData → GMap (GoString × GoString) GoString → Prop) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      backend.isBackend γ P W Pk bl ∗
      □ (∀ (vd : backend.VData) (d : GMap (GoString × GoString) GoString),
        R -∗ W -∗ Pk -∗ backend.viewAt γ vd -∗ backend.hkOwn γ d -∗ ⌜Q vd d⌝) ⊢
      srvBeSnapOk
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty)
          #bl)
        iprop(backend.bOpen γ qo ∗ backend.wbTok γ ∗ R) iprop(backend.bOpen γ qo ∗ R)
        (fun D => Q (backend.sData P D) (backend.hkData P D)) := by
  iintro ⟨#Hpkg, #Hb, #HQ⟩
  iunfold srvBeSnapOk
  iexists ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty, #bl⟩
  isplitr
  · ipureintro; rfl
  iintro %Φ !> ⟨Ho, Hwb, HR⟩ HΦ
  wp_apply hSnap γ P W Pk bl qo R Q $$ [Ho Hwb HR] as %sp %D ⟨Hsn, Ho, HR, %HQD⟩
  · iframe #; iframe
  iapply HΦ
  iframe
  ipureintro; exact HQD

/-- **`s.KV().Commit()`'s contract from `store.Commit`** (D22 S-l's sender items, 2026-10-22:
`store.Commit` translated and proved): over a KV of the store `st` (`txn.isKV`: the store itself
or the watchable store over it, whose `Commit` is promoted), for the store's sole writer: its
fragment, its reader token of the backend and a write session's token (`storeWT`: for the real
backend, a write-back's budget, `srvWTPool_take_extra`). -/
theorem srvKVCommitOk_of_kv (hC : mvcc.store.Commit.spec (GF := GF) (hG := hG))
    (kv : GoInterface) (st : Loc) (γ : mvcc.StoreNames) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ txn.isKV kv st γ ⊢
      srvKVCommitOk kv iprop(mvcc.writerFrag γ ∗ mvcc.writerOwn γ ∗ mvcc.storeWT γ)
        iprop(mvcc.writerFrag γ ∗ mvcc.writerOwn γ) := by
  iintro ⟨#Hpkg, #Hkv⟩
  ihave ⟨#Hko, #Hs⟩ := txn.isKV_kvOver kv st γ $$ Hkv
  ihave %Hok := mvcc.kvOver_ok kv st $$ Hko
  obtain ⟨ty, v, rfl⟩ := Hok
  iunfold srvKVCommitOk
  iexists ⟨ty, v⟩
  isplitr
  · ipureintro; rfl
  iintro %Φ !> ⟨Hfr, Hro, Hwt⟩ HΦ
  iapply mvcc.kvOver_commit_wp ty v st
  iframe Hko
  iapply (hC st γ) $$ [Hfr Hro Hwt] HΦ
  iframe #; iframe

/-- **The recorded term's commit bound from the batch's** (D22 S-l's sender items; D22l's
`rnRtOk`, `rnApP_rtOk`): a non-zero raft term recorded with a batch whose log reaches `n`, at least
the applied index `ai`, has a commit witness at `c ≥ ai` (`rnRtBound`, `snapBranch_send`'s). -/
theorem rnRtBound_of_rtOk (γ : RNNames) (t ai : w64) (n : Nat) (ht : uint.Z t ≠ 0)
    (hn : uint.Z ai ≤ (n : Int)) :
    rnRtOk (GF := GF) γ t n ⊢ rnRtBound γ.node.raft t ai := by
  iintro H
  iunfold rnRtOk at H
  icases H with (%Hz | ⟨%c, #Hc, %Hle⟩)
  · exact absurd Hz ht
  iunfold rnRtBound
  iexists c
  iframe Hc
  ipureintro; omega

end proof

end EtcdGrove
end Perennial

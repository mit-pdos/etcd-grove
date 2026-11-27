/-
Lean-first (no Rocq counterpart).

# The in-process instance of the k8s library's etcd client (K5, `notes/k8s-dist-lean-plan.md` §4.1)

`inProcEtcd ms V`: a client of the in-process members `ms` (`client.SrvAt`), whose handle is `New`'s
client of them (`isNewClient`, sending a write at most once, each member's KV registered), with an
update at every member's KV, live when no member refuses connections. `inProcEtcd_laws`: its laws,
from the in-process specs of the calls (hypotheses, which the linking modules pass).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.EtcdClient
public import Proof.go_etcd_io.etcd.client.v3.ClientCallLaws
public import Proof.go_etcd_io.etcd.client.v3.InvOpLemmas
public import Proof.go_etcd_io.etcd.client.v3.KVService
public import Proof.go_etcd_io.etcd.client.v3.kubernetes.Defs
public import Proof.go_etcd_io.etcd.client.v3.TxnPlainSpec
public import Proof.go_etcd_io.etcd.client.v3.KVMembers
public import Spec.go_etcd_io.etcd.client.v3.Client__Endpoints
public import Spec.go_etcd_io.etcd.client.v3.kv__Txn
public import Spec.go_etcd_io.etcd.client.v3.txn__If

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver EtcdGrove.kubernetes

/-! ## The compactor's round transaction through the members (C3; formerly in `Compact.lean`) -/

section pure
variable [GooseExts]

open etcd_txnlin in
/-- The round's transaction is small (its strings below linkvtxn's `inMax`). -/
theorem casTxn_size (ev rev : w64) :
    txnSizeOk (txnWireOf (etcd_txnlin.clientTxn [.ver compactRevKey ev]
      [.put compactRevKey (fmtInt rev (W64 10))] [.get compactRevKey])) := by
  rw [txnWireOf_clientTxn]
  apply txnSizeOk_txnOf _ _ _ (by simp)
  have hv := fmtInt_length_le rev (W64 10)
  refine ⟨fun c hc => ?_, fun o ho => ?_⟩
  · simp only [List.mem_singleton] at hc
    subst hc
    simp [mcmpBytesLe, compactRevKey, inMax]
  · simp only [List.mem_append, List.mem_singleton] at ho
    rcases ho with rfl | rfl
    · exact ⟨by simp [compactRevKey, inMax], by unfold inMax; omega⟩
    · simp [mopBytesLe, compactRevKey, inMax]

end pure

section inproc
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

open etcd_txnlin in
/-- **The round's `Commit()`** through a client of the members `ms`, each at the KV `γk`: its
update fired at most once at each member (as linkvtxn's `txn_Commit_st`'s writing case, through
`txn.Commit.specM`, which keeps the reply's revision reached, `txnRevLb`): the reply's verdict and
responses the server's run at the state `σ` the update fired at, its revision `σ`'s after it,
positive and reached. -/
theorem cas_commit [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions] [go_etcd_io.etcd.cache.v3.Assumptions]
    (wp_CommitM : EtcdGrove.txn.Commit.specM (GF := GF) (hG := hG)) (tp : Loc) (ms : List (client.SrvAt GF))
    (γk : KVNames) (hsame : ∀ x ∈ ms, kvSame x.γr.kv γk) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (b : TxnBuild) (ev rev : w64)
    (Q : KVState → IProp GF) (hb : b.model = casClientTxn ev rev) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
        txnObjAt tp (ms.map client.SrvAt.addr) ci cd b ∗
        ([∗list] x ∈ ms, client.kvRegsAt x) ∗ ([∗list] x ∈ ms, client.srvStart x) ∗
        client.txnWriteOnce tp (ms.map client.SrvAt.addr) ∗
        ([∧list] x ∈ ms, kvOpAu1 x.γr.kv (.txn (casTxn ev rev)) Q) }}
      (App (Val (tp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.txn.ty @!! go!"Commit"))
        (Val #()))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗
        ((⌜err = GoInterface.nil⌝ ∗ ∃ (m : TxnRespM) (σ : KVState), txnRespMsg resp m ∗ Q σ ∗
          ⌜m.succeeded = casWins ev rev σ ∧
            client.opRespsRel false ((casTxn ev rev).branch m.succeeded)
              (txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs (casTxn ev rev)).2.2 m.resps ∧
            0 < sint.Z m.hdr.revision⌝ ∗ kvRevLb γk m.hdr.revision) ∨
          (⌜err ≠ GoInterface.nil⌝ ∗ kvErr err)) }} := by
  iintro %Φ ⟨#Pc, Hlt, Hobj, #Hregs, #Hst, Hone, Hau⟩ HΦ
  have hw : txnWireOf b.model = casTxn ev rev := by rw [hb, txnWireOf_clientTxn]
  have hp : client.TxnModel.plain b.model := by rw [hb]; exact clientTxn_plain _ _ _
  have hin : client.txnModelIn (txnWireOf b.model) := by rw [hw]; exact txnModelIn_txnOf _ _ _
  have hsz : txnSizeOk (txnWireOf b.model) := by rw [hb]; exact casTxn_size ev rev
  have hro : txn.txnReadonly (casTxn ev rev) = false := by
    rw [txnReadonly_txnOf]; rfl
  ihave #Hst' := client.srvStart_both ms $$ Hst
  have hm : ∀ (k : Nat) (x : client.SrvAt GF), ms[k]? = some x →
      kvOpAu1 x.γr.kv (.txn (casTxn ev rev)) Q ⊢
        client.txnUpdAt x.γr x.γr (txnWireOf b.model) Q :=
    fun _ _ _ => by
      iintro H
      unfold client.txnUpdAt
      iright; iright
      isplitr
      · ipureintro
        rw [hw]
        exact ⟨hro, linkv.txnPlain_txnOf _ _ _, txnNoZeroEnd_txnOf _ _ _⟩
      rw [hw]
      iexact H
  ihave Hau' := (BigAndL.bigAndL_mono hm) $$ Hau
  iapply (wp_CommitM tp ms ci cd b (W64 0) [] Q) $$ [$Hlt Hobj Hau' Hone]
  · iframe Hobj
    iframe #
    isplitl []
    · iunfold client.kvRegs; iframe #
    isplitl []
    · ipureintro; exact ⟨hp, hin⟩
    isplitl []
    · iunfold client.knownAt; iframe #
    isplitl [Hau' Hone]; rotate_left
    · ipureintro; exact hsz
    unfold txnReqPre client.txnUpd
    iright
    iunfold client.txnWriteOnce at Hone
    icases Hone with %Hnr
    isplitl []
    · ipureintro; exact Hnr
    inext
    iexact Hau'
  inext
  iintro %resp %err ⟨Hlt, Hout⟩
  iapply HΦ
  iframe Hlt
  iunfold txnCallOut at Hout
  icases Hout with (⟨%Herr, %m, Hm, Hq⟩ | ⟨%Herr, #Hse, #Hcl⟩)
  · ileft
    isplitl []
    · ipureintro; exact Herr
    iunfold client.txnAns at Hq
    icases Hq with ⟨%x, %hx, Hr, #Hrv⟩
    ihave #Hrv' := client.txnRevLb_same x.γr.kv γk (hsame x hx) _ m $$ Hrv
    rw [hw]
    unfold client.txnRevLb client.txnReplied
    simp only [hro, Bool.false_eq_true, ↓reduceIte]
    icases Hr with ⟨%tw, %hmd, %rq', %t', %y, %y', %l, %skip, %Hp, -, -, -, -, ⟨%ltq, -, HQ⟩⟩
    obtain ⟨Htw, -, -, Hz, hap, hrev, -, -, -, hlen, hb4, hok, hrel, hsk⟩ := Hp
    have ht : t' = casTxn ev rev := Hz (irrNoZeroEnd_txnOf _ _ _ tw Htw)
    subst ht hsk
    have hr : ((kvStateOf y.log ltq).rev + 1 : Nat) = y.log.length := client.kvStateOf_rev_succ _ hlen
    have hs : (kvStateOf y.log ltq).kvs = mvcc.stateAfter y.log := kvStateOf_kvs _
    iexists m, kvStateOf y.log ltq
    iframe Hm HQ Hrv'
    ipureintro
    refine ⟨?_, ?_, ?_⟩
    · unfold casWins; rw [hr, hs]; exact hok
    · rw [hr, hs]; exact hrel
    · rw [hrev]
      have h1 : 1 ≤ mvcc.writeRev y.log
          (txn.srvRunTxn (W64 (y.log.length : Int)) (mvcc.stateAfter y.log) (casTxn ev rev)).2.1 := by
        unfold mvcc.writeRev; split <;> omega
      have h2 : mvcc.writeRev y.log
          (txn.srvRunTxn (W64 (y.log.length : Int)) (mvcc.stateAfter y.log) (casTxn ev rev)).2.1 <
          2 ^ 63 := by
        unfold mvcc.writeRev; split <;> omega
      word
  · iright
    isplitl
    · ipureintro; exact Herr.1
    · iunfold kvErr; iframe #; ipureintro; exact Herr.2.1

/-- **The client of the in-process members `ms`** (see the file header). -/
def inProcEtcd [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (ms : List (client.SrvAt GF)) (V : client.WEnv GF) : K8sEtcd GF where
  kvs := ms.map (fun x => x.γr.kv)
  live := ∀ x ∈ ms, noRefusalAt x.addr
  eps := ms.map client.SrvAt.addr
  handle cl := iprop(isNewClient cl (ms.map client.SrvAt.addr) V ∗
    client.clientWriteOnce cl (ms.map client.SrvAt.addr) ∗ [∗list] x ∈ ms, client.kvRegsAt x)
  kvAt api := iprop(EtcdGrove.kvObjAt api (ms.map client.SrvAt.addr) ∗ [∗list] x ∈ ms, client.kvRegsAt x)
  txnAt tp ci cd b := iprop(txnObjAt tp (ms.map client.SrvAt.addr) ci cd b ∗
    client.txnWriteOnce tp (ms.map client.SrvAt.addr) ∗ [∗list] x ∈ ms, client.kvRegsAt x)

theorem inProcEtcd_kvs [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (ms : List (client.SrvAt GF)) (V : client.WEnv GF) :
    (inProcEtcd ms V).kvs = ms.map (fun x => x.γr.kv) := rfl

/-- **The in-process client's laws**, from the in-process specs. -/
theorem inProcEtcd_laws [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (wp_Get : ∀ [go_etcd_io.etcd.client.v3.kubernetes.Assumptions],
      kubernetes.Client.Get.spec (GF := GF) (hG := hG))
    (wp_List : ∀ [go_etcd_io.etcd.client.v3.kubernetes.Assumptions],
      kubernetes.Client.List.spec (GF := GF) (hG := hG))
    (wp_OptimisticPut : ∀ [go_etcd_io.etcd.client.v3.kubernetes.Assumptions],
      kubernetes.Client.OptimisticPut.spec (GF := GF) (hG := hG))
    (wp_OptimisticDelete : ∀ [go_etcd_io.etcd.client.v3.kubernetes.Assumptions],
      kubernetes.Client.OptimisticDelete.spec (GF := GF) (hG := hG))
    (h_range_any : client.client_range_any.law (GF := GF) (hG := hG))
    (wp_Endpoints : EtcdGrove.Client.Endpoints.spec (GF := GF) (hG := hG))
    (wp_Txn : EtcdGrove.kv.Txn.spec (GF := GF) (hG := hG))
    (wp_If : EtcdGrove.txn.If.spec (GF := GF) (hG := hG))
    (wp_Then : EtcdGrove.txn.Then.spec (GF := GF) (hG := hG))
    (wp_Else : EtcdGrove.txn.Else.spec (GF := GF) (hG := hG))
    (wp_CommitM : EtcdGrove.txn.Commit.specM (GF := GF) (hG := hG))
    (ms : List (client.SrvAt GF)) (V : client.WEnv GF) : (inProcEtcd ms V).Laws where
  get := by
    intro _ _ _ kc ci cd key opts Q h1 h2
    simp only [inProcEtcd, BigAndL.bigAndL_map]
    iintro %Φ ⟨#P1, #P2, Hlt, ⟨#Hnc, -, #Hregs⟩, #Hctx, #Hce, Hau⟩ HΦ
    iapply (wp_Get kc ms V ci cd key opts Q h1 h2) $$ [Hlt Hau] [HΦ]
    · iframe Hlt Hau
      iframe #
    · iexact HΦ
  list := by
    intro _ _ _ kc ci cd pfx opts Q h1 h2 h3 h4 h5
    simp only [inProcEtcd, BigAndL.bigAndL_map]
    iintro %Φ ⟨#P1, #P2, Hlt, ⟨#Hnc, -, #Hregs⟩, #Hctx, #Hce, Hau⟩ HΦ
    iapply (wp_List kc ms V ci cd pfx opts Q h1 h2 h3 h4 h5) $$ [Hlt Hau] [HΦ]
    · iframe Hlt Hau
      iframe #
    · iexact HΦ
  optimisticPut := by
    intro _ _ _ kc ci cd key vsl val rev opts Q h1 h2 h3
    simp only [inProcEtcd, BigAndL.bigAndL_map]
    iintro %Φ ⟨#P1, #P2, Hlt, ⟨#Hnc, #Hwo, #Hregs⟩, #Hctx, #Hce, #Hv, Hau⟩ HΦ
    iapply (wp_OptimisticPut kc ms V ci cd key vsl val rev opts Q h1 h2 h3) $$ [Hlt Hau] [HΦ]
    · iframe Hlt Hau
      iframe #
    · iexact HΦ
  optimisticDelete := by
    intro _ _ _ kc ci cd key rev opts Q h1
    simp only [inProcEtcd, BigAndL.bigAndL_map]
    iintro %Φ ⟨#P1, #P2, Hlt, ⟨#Hnc, #Hwo, #Hregs⟩, #Hctx, #Hce, Hau⟩ HΦ
    iapply (wp_OptimisticDelete kc ms V ci cd key rev opts Q h1) $$ [Hlt Hau] [HΦ]
    · iframe Hlt Hau
      iframe #
    · iexact HΦ
  ctxFields := by
    intro cl
    simp only [inProcEtcd]
    iintro ⟨#Hnc, -, -⟩
    iapply EtcdGrove.isNewClient_ctxOk $$ Hnc
  kvField := by
    intro cl
    simp only [inProcEtcd]
    iintro ⟨#Hnc, -, #Hregs⟩
    iunfold isNewClient at Hnc
    icases Hnc with ⟨-, -, ⟨%api, #Hkvf, #Hkv⟩, -⟩
    iexists api
    isplitr
    · iexact Hkvf
    imodintro
    isplitr
    · iexact Hkv
    iexact Hregs
  kvGet := by
    intro _ _ api ctx cdw pk osl gs Qr hsz hg hser hss
    simp only [inProcEtcd]
    iintro %Φ ⟨#Pc, Hlt, ⟨#Hkv, #Hregs⟩, #Hctx, #Hce, #Hopts, #Hra⟩ HΦ
    imod (client.srvStart_alloc (GF := GF) ms) with #Hst
    ihave #Hopts' := optsAt_res osl gs iprop(True) $$ Hopts
    ihave #Hst' := client.srvStart_both ms $$ Hst
    ihave #Hau : (□ [∧list] x ∈ ms, ⌜Qr = fun _ => iprop(True)⌝ ∨
        (⌜(rangeWireOf (opGetModel pk gs)).base.serializable = false⌝ ∗ kvReadAu x.γr.kv Qr)) $$ [Hra]
    · imodintro
      iapply (BigAndL.bigAndL_intro
        (P := iprop(□ [∗list] γ ∈ ms.map (fun x => x.γr.kv), kvReadAu γ Qr)) (fun k x hk => ?_)) $$ Hra
      iintro #H'
      ihave #Hx := BigSepL.bigSepL_lookup
        (show (ms.map (fun x : client.SrvAt GF => x.γr.kv))[k]? = some x.γr.kv by simp [hk]) $$ H'
      iright
      iframe Hx
      ipureintro; exact hser
    wp_apply (h_range_any api ms (W64 0) ctx cdw pk osl gs iprop(True) Qr [] hsz) $$ [$Hlt]
      as %resp %err ⟨Hlt, -, Hout, -⟩
    · iframe #
      isplitl []
      · rw [hss]; iapply sortNamesIf_false
      ipureintro; exact hg
    iapply HΦ
    iframe Hlt
    icases Hout with (⟨%Herr, %m, Hm, %x, %hx, #Hq⟩ | ⟨⟨%Herr, %Hrn⟩, #Hke⟩)
    · subst Herr
      ihave Hs := kubernetes.rangeReply_state_at x.E x.γr (W64 0) x.cid x.mid _ [] Qr m hser $$ Hq
      icases Hs with ⟨%σ, #HQ, %Hσ⟩
      obtain ⟨hsel, -, hrevσ, hle, hb, -⟩ := Hσ
      ileft
      isplitr
      · ipureintro; rfl
      iexists m, σ
      iframe Hm HQ
      ipureintro
      exact ⟨hsel, hrevσ, hle, hb⟩
    · iright
      iunfold kvErr at Hke
      icases Hke with ⟨%Hce, #Hse, #Hcl⟩
      isplitr
      · ipureintro; exact Herr
      iframe Hse Hcl
      ipureintro; exact ⟨Herr, Hce⟩
  endpoints := by
    intro cl
    simp only [inProcEtcd]
    iintro %Φ ⟨#Pc, Hlt, ⟨#Hnc, -, -⟩⟩ HΦ
    ihave #Hcl' := Hnc
    iunfold isNewClient at Hcl'
    icases Hcl' with ⟨-, #Hrco, -⟩
    ihave #Heps := isNewClient_endpoints $$ Hnc
    iunfold clientEndpointsAt at Heps
    icases Heps with ⟨%esl0, #Hef, #Hes⟩
    wp_apply wp_Endpoints cl $$ [$Hlt] as %esl ⟨Hlt, %eps, Hesl, Heq⟩
    · iframe #
    ihave %Heq' := Heq $$ %esl0 %_ Hef Hes
    subst Heq'
    iapply HΦ
    iframe
  kvTxn := by
    intro cl api ci cd
    simp only [inProcEtcd]
    iintro %Φ ⟨#Pc, ⟨#Hnc, #Hone, #Hregs⟩, #Hkvf, ⟨#Hkv, -⟩, #Hctx, #Hce⟩ HΦ
    ihave #Hwo := client.clientWriteOnce_api cl api _ $$ [Hkvf Hone]
    · iframe #
    wp_apply (wp_Txn api (ms.map client.SrvAt.addr) ci cd) as %t ⟨%tp, %Ht, Hobj, -⟩
    · iframe #
    iapply HΦ
    iexists tp
    isplitr
    · ipureintro; exact Ht
    iframe Hobj
    isplitl []
    · iunfold client.txnWriteOnce
      iunfold client.writeOnce at Hwo
      iexact Hwo
    iexact Hregs
  txnIf := by
    intro tp ci cd b sl cs
    simp only [inProcEtcd]
    iintro %Φ ⟨#Pc, ⟨Hobj, Htwo, #Hregs⟩, #Hcs, %Hb⟩ HΦ
    wp_apply (wp_If tp (ms.map client.SrvAt.addr) ci cd b sl cs) $$ [Hobj] as Hobj
    · iframe #
      iframe Hobj
      ipureintro; exact Hb
    iapply HΦ
    iframe Hobj Htwo
    iexact Hregs
  txnThen := by
    intro tp ci cd b sl os ops
    simp only [inProcEtcd]
    iintro %Φ ⟨#Pc, ⟨Hobj, Htwo, #Hregs⟩, #Hos, %Hb⟩ HΦ
    wp_apply ((EtcdGrove.txn.Then.spec_plain wp_Then) tp (ms.map client.SrvAt.addr) ci cd b sl os ops)
      $$ [Hobj] as Hobj
    · iframe #
      iframe Hobj
      ipureintro; exact Hb
    iapply HΦ
    iframe Hobj Htwo
    iexact Hregs
  txnElse := by
    intro tp ci cd b sl os ops
    simp only [inProcEtcd]
    iintro %Φ ⟨#Pc, ⟨Hobj, Htwo, #Hregs⟩, #Hos, %Hb⟩ HΦ
    wp_apply ((EtcdGrove.txn.Else.spec_plain wp_Else) tp (ms.map client.SrvAt.addr) ci cd b sl os ops)
      $$ [Hobj] as Hobj
    · iframe #
      iframe Hobj
      ipureintro; exact Hb
    iapply HΦ
    iframe Hobj Htwo
    iexact Hregs
  casCommit := by
    intro _ tp γk hsame ci cd b ev rev Q hb
    have hsame' : ∀ x ∈ ms, kvSame x.γr.kv γk := fun x hx =>
      hsame x.γr.kv (List.mem_map_of_mem (f := fun x : client.SrvAt GF => x.γr.kv) hx)
    simp only [inProcEtcd, BigAndL.bigAndL_map]
    iintro %Φ ⟨#Pc, Hlt, ⟨Hobj, Htwo, #Hregs⟩, Hau⟩ HΦ
    imod (client.srvStart_alloc (GF := GF) ms) with #Hst
    iapply (cas_commit wp_CommitM tp ms γk hsame' ci cd b ev rev Q hb) $$ [Hlt Hobj Htwo Hau] HΦ
    iframe Hlt Hobj Htwo Hau
    iframe #

/-- **The in-process client** from `New`'s client of the members (`isStore`'s former conjuncts). -/
theorem k8sClient_inProc [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (ms : List (client.SrvAt GF)) (V : client.WEnv GF) (hl : (inProcEtcd ms V).Laws) (cl : Loc) :
    isNewClient cl (ms.map client.SrvAt.addr) V ∗
      client.clientWriteOnce cl (ms.map client.SrvAt.addr) ∗ ([∗list] x ∈ ms, client.kvRegsAt x) ⊢
    k8sClient (inProcEtcd ms V) cl := by
  iintro #H
  unfold k8sClient
  isplitr
  · ipureintro; exact hl
  imodintro
  simp only [inProcEtcd]
  iexact H

end inproc

end k8s
end EtcdGrove
end Perennial

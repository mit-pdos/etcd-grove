/-
Lean-first (no Rocq counterpart).

The proof of `Compact`: the round's transaction (`casTxn ev rev`) built as `kubernetes`'
`OptimisticPut` builds its (`kv.Txn`, `If(Version(key) = ev)`, `Then(OpPut(key,
FormatInt(rev, 10)))`, `Else(OpGet(key))`), committed through the members (`cas_commit`, as
linkvtxn's `txn_Commit_st` with the reply's revision reached kept: `txnRevLb`); then
- the compare failed: the else branch's get is the key's key-values (`failure_resps`), which the
  caller's `casPost` says hold `FormatInt c` for a recorded, reached `c`: `Kvs[0]` exists and
  `ParseInt` reads `c` back;
- it held: at `rev ≠ 0` the client's `Compact(rev)` (`rev` reached, the caller's `revOk`).

The client's `Compact` goes through `kv.Compact.spec`, at the client's KV handle (`clientKvOk`: its
`isKv` carries the store's receipt bound).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.Compact
public import Proof.go_etcd_io.etcd.client.v3.ClientPutGet
public import Proof.go_etcd_io.etcd.client.v3.TxnPlain
public import Proof.go_etcd_io.etcd.client.v3.LinkMembers
public import Spec.go_etcd_io.etcd.client.v3.Compare
public import Spec.go_etcd_io.etcd.client.v3.Version
public import Spec.go_etcd_io.etcd.client.v3.OpPut
public import Spec.go_etcd_io.etcd.client.v3.OpGet
public import Spec.go_etcd_io.etcd.client.v3.Client__Endpoints
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.ResponseOp__GetResponseRange
public import Spec.strconv.FormatInt
public import Spec.strconv.ParseInt
public import Spec.k8s_io.klog.v2.V
public import Spec.k8s_io.klog.v2.Verbose__Infof

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open go_etcd_io.etcd.server.v3.etcdserver etcd_txnlin

/-! ## Pure part -/

section pure
variable [GooseExts]

/-- The round's transaction is small (its strings below linkvtxn's `inMax`). -/
theorem casTxn_size (ev rev : w64) :
    txnSizeOk (txnWireOf (clientTxn [.ver compactRevKey ev]
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

/-! ## The round's commit -/

section commit
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- The round's transaction, as the builder holds it. -/
abbrev casClientTxn (ev rev : w64) : TxnModel :=
  clientTxn [.ver compactRevKey ev] [.put compactRevKey (fmtInt rev (W64 10))] [.get compactRevKey]

/-- **The round's `Commit()`** through a client of the members `ms`, each at the KV `γk`: its
update fired at most once at each member (as linkvtxn's `txn_Commit_st`'s writing case, through
`txn.Commit.specM`, which keeps the reply's revision reached, `txnRevLb`): the reply's verdict and
responses the server's run at the state `σ` the update fired at, its revision `σ`'s after it,
positive and reached. -/
theorem cas_commit [go_etcd_io.etcd.cache.v3.Assumptions] (tp : Loc) (ms : List (client.SrvAt GF))
    (γk : KVNames) (hsame : ∀ x ∈ ms, kvSame x.γr.kv γk) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (b : TxnBuild) (ev rev : w64)
    (Q : KVState → IProp GF) (hb : b.model = casClientTxn ev rev) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
        txnObjAt tp (ms.map client.SrvAt.addr) ci cd b ∗
        ([∗list] x ∈ ms, client.kvRegsAt x) ∗ ([∗list] x ∈ ms, client.srvStart x) ∗
        client.txnWriteOnce tp (ms.map client.SrvAt.addr) ∗
        ([∧list] x ∈ ms, kvOpAu1 x.γr.kv (.txn (casTxn ev rev)) Q) }}
      (App (Val (tp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.txn.ty @!! go!"Commit"))
        (Val #()))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        (⌜err = GoInterface.nil⌝ ∗ ∃ (m : TxnRespM) (σ : KVState), txnRespMsg resp m ∗ Q σ ∗
          ⌜m.succeeded = casWins ev rev σ ∧
            client.opRespsRel false ((casTxn ev rev).branch m.succeeded)
              (txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs (casTxn ev rev)).2.2 m.resps ∧
            0 < sint.Z m.hdr.revision⌝ ∗ kvRevLb γk m.hdr.revision) ∨
          (⌜err ≠ GoInterface.nil⌝ ∗ kvErr err) }} := by
  iintro %Φ ⟨#Pc, Hobj, #Hregs, #Hst, Hone, Hau⟩ HΦ
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
  iapply (client.v3.txn.wp_CommitM tp ms ci cd b (W64 0) [] Q) $$ [Hobj Hau' Hone]
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
  iintro %resp %err Hout
  iapply HΦ
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
    icases Hr with ⟨%tw, %hmd, %rq', %t', %y, %y', %l, %skip, %Hp, -, -, -, -, -, HQ⟩
    obtain ⟨Htw, -, -, Hz, hap, hrev, -, -, -, hlen, hb4, hok, hrel, hsk⟩ := Hp
    have ht : t' = casTxn ev rev := Hz (irrNoZeroEnd_txnOf _ _ _ tw Htw)
    subst ht hsk
    have hr : ((kvStateOf y.log).rev + 1 : Nat) = y.log.length := client.kvStateOf_rev_succ _ hlen
    have hs : (kvStateOf y.log).kvs = mvcc.stateAfter y.log := kvStateOf_kvs _
    iexists m, kvStateOf y.log
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

end commit


/-! ## The proof -/

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

/-- See the file header. -/
theorem Compact.wp_proof
    (wp_Version : EtcdGrove.Version.spec (GF := GF) (hG := hG))
    (wp_Compare : EtcdGrove.Compare.spec (GF := GF) (hG := hG))
    (wp_OpPut : EtcdGrove.OpPut.spec (GF := GF) (hG := hG)) (wp_OpGet : EtcdGrove.OpGet.spec (GF := GF) (hG := hG))
    (wp_FormatInt : EtcdGrove.strconv.FormatInt.spec (GF := GF) (hG := hG))
    (wp_ParseInt : EtcdGrove.strconv.ParseInt.spec (GF := GF) (hG := hG))
    (wp_GetResponseRange : EtcdGrove.ResponseOp.GetResponseRange.spec (GF := GF) (hG := hG))
    (wp_Endpoints : EtcdGrove.Client.Endpoints.spec (GF := GF) (hG := hG))
    (wp_V : EtcdGrove.klog.V.spec (GF := GF) (hG := hG))
    (wp_Infof : EtcdGrove.klog.Verbose.Infof.spec (GF := GF) (hG := hG)) :
    Compact.spec (GF := GF) (hG := hG) := by
  intro _ _ cl ms V γk ci cd Seen recorded _ _ ev rev hsame hcmp hcret
  wp_start as ⟨#Hcl, #Hone, #Hregs, #Hko, #Hctx, #Hce, #Hcas, #Hev, #Hrev⟩
  ihave #Psc : isPkgInit (PROP := IProp GF) pkg_id.strconv $$ []
  · iPkgInit
  rw [show k8s_io.apiserver.pkg.storage.etcd3.compactRevKey = #compactRevKey from rfl]
  wp_auto
  ihave #Hnil := optsAt_nil (GF := GF)
  wp_apply wp_OpGet compactRevKey slice.nil [] $$ [] as %op2 #Hop2
  · iframe #
    ipureintro
    unfold opGetPanics opFold OpFull.newOp; simp
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl4 ⟨Hsl4, -⟩
  ipersist Hsl4
  wp_auto
  generalize hsl4 : slice.mk sl4 _ _ = esl
  ihave #Heops : opsAt esl [opGetModel compactRevKey []] $$ []
  · iunfold opsAt
    iexists _
    iframe Hsl4
    isplitr
    · ipureintro; rfl
    imodintro
    iintro %i %o %m %Ho %Hm
    rcases i with _ | i
    · cases Ho; cases Hm; iexact Hop2
    · simp at Ho
  wp_apply wp_FormatInt rev (W64 10) $$ [] as %str %Hstr
  · iframe #; ipureintro; decide
  subst Hstr
  wp_apply wp_OpPut compactRevKey (fmtInt rev (W64 10)) slice.nil [] $$ [] as %op #Hop
  · iframe #
    ipureintro
    simp [opPutModel, opFold, OpFull.putPanics, OpFull.putInit, OpFull.newOp, OpModel.zero]
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl2 ⟨Hsl2, -⟩
  ipersist Hsl2
  wp_auto
  generalize hsl2 : slice.mk sl2 _ _ = tsl
  ihave #Hops : opsAt tsl [opPutModel compactRevKey (fmtInt rev (W64 10)) []] $$ []
  · iunfold opsAt
    iexists _
    iframe Hsl2
    isplitr
    · ipureintro; rfl
    imodintro
    iintro %i %o %m %Ho %Hm
    rcases i with _ | i
    · cases Ho; cases Hm; iexact Hop
    · simp at Ho
  wp_apply wp_Version compactRevKey as %c0 #Hc0
  wp_apply wp_Compare c0 _ go!"=" .eq _ (.num ev) $$ [] as %c1 #Hc1
  · iframe #
    ipureintro
    exact ⟨rfl, ⟨ev, Or.inl rfl, rfl⟩⟩
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl3 ⟨Hsl3, -⟩
  ipersist Hsl3
  wp_auto
  generalize hsl3 : slice.mk sl3 _ _ = csl
  ihave #Hcmps : cmpsAt csl [compareM (cmpKeyM .version compactRevKey) .eq (.num ev)] $$ []
  · iunfold cmpsAt
    iexists _
    iframe Hsl3
    isplitr
    · ipureintro; rfl
    imodintro
    iintro %i %c %m %Hc %Hm
    rcases i with _ | i
    · cases Hc; cases Hm; iexact Hc1
    · simp at Hc
  ihave #Hcl' := Hcl
  iunfold isNewClient at Hcl'
  icases Hcl' with ⟨-, #Hrco, ⟨%api, #Hkvf, #Hkv⟩, -⟩
  ihave #Hwo := client.clientWriteOnce_api cl api _ $$ [Hkvf Hone]
  · iframe #
  wp_auto
  wp_apply (client.v3.kv.wp_Txn api (ms.map client.SrvAt.addr) ci cd) as %t ⟨%tp, %Ht, Hobj, #Hkt⟩
  · iframe #
  subst Ht
  ihave Htwo : client.txnWriteOnce tp (ms.map client.SrvAt.addr) $$ []
  · iunfold client.txnWriteOnce
    iunfold client.writeOnce at Hwo
    iexact Hwo
  (try wp_auto)
  wp_apply (client.v3.txn.wp_If tp (ms.map client.SrvAt.addr) ci cd TxnBuild.empty csl
      [compareM (cmpKeyM .version compactRevKey) .eq (.num ev)]) $$ [Hobj] as Hobj
  · iframe #
    iframe Hobj
    ipureintro; simp [TxnBuild.empty]
  (try wp_auto)
  wp_apply (client.v3.txn.wp_Then_plain tp (ms.map client.SrvAt.addr) ci cd _ tsl
      [opPutModel compactRevKey (fmtInt rev (W64 10)) []]
      [.put compactRevKey (fmtInt rev (W64 10)) (W64 0)]) $$ [Hobj] as Hobj
  · iframe #
    iframe Hobj
    ipureintro; exact ⟨rfl, rfl, rfl⟩
  (try wp_auto)
  wp_apply (client.v3.txn.wp_Else_plain tp (ms.map client.SrvAt.addr) ci cd _ esl
      [opGetModel compactRevKey []] [.get (opGetModel compactRevKey [])]) $$ [Hobj] as Hobj
  · iframe #
    iframe Hobj
    ipureintro; exact ⟨rfl, rfl⟩
  (try wp_auto)
  ihave Hobj : txnObjAt (GF := GF) tp (ms.map client.SrvAt.addr) ci cd
      ⟨casClientTxn ev rev, true, true, true⟩ $$ [Hobj]
  · iExactEq Hobj
    simp [TxnModel.empty, clientTxn, linkv.cmpOf, compareM, cmpKeyM, clientTOp]
  imod (client.srvStart_alloc (GF := GF) ms) with #Hst
  ihave #Hcas' := Hcas
  iunfold casOk at Hcas'
  ihave Hau := Hcas' $$ %ev %rev Hev Hrev
  wp_apply (cas_commit tp ms γk hsame ci cd ⟨casClientTxn ev rev, true, true, true⟩ ev rev
      (casPost γk Seen recorded ev rev) rfl) $$ [Hobj Hau Htwo]
    as %resp %err Hout
  · iframe #
    iframe
  icases Hout with (⟨%Herr, %m, %σ, #Hm, HQ, %Hσ, #Hrvl⟩ | ⟨%Herr, #Hke⟩)
  rotate_left
  · -- the transaction failed: no revision
    cases err with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    wp_auto
    iapply HΦ
    iframe #
    isplitr
    · unfold recRevOk; ileft; ipureintro; rfl
    ipureintro; intro _; rfl
  subst Herr
  obtain ⟨hok, hrel, hpos⟩ := Hσ
  iunfold txnRespMsg at Hm
  icases Hm with ⟨%Hnn, %h, %rsl, %ps, #Hh, #Hhf, #Hsucc, #Hrs, #Hrsl, #Hms⟩
  iunfold hdrFull at Hhf
  icases Hhf with ⟨%Hhn, -, -, #Hrevf, -, -⟩
  iunfold casPost at HQ
  icases HQ with ⟨#HSeen, HQ⟩
  ihave #Hcr : revOk γk m.hdr.revision $$ []
  · unfold revOk; iright
    isplitr
    · ipureintro; exact hpos
    iunfold kvRevLb at Hrvl; iexact Hrvl
  wp_auto
  cases hs : m.succeeded
  · -- the compare failed: the key's value
    rw [hs] at hok hrel
    rw [← hok]
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases HQ with ⟨%c, %Hkv, #Hrc, #Hoc⟩
    have hok' : (txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs (casTxn ev rev)).1 = false := by
      unfold casWins at hok; exact hok.symm
    obtain ⟨rv, more, count, hresps⟩ := kubernetes.failure_resps σ.kvs
      (W64 ((σ.rev + 1 : Nat) : Int)) [.ver compactRevKey ev]
      [.put compactRevKey (fmtInt rev (W64 10))] compactRevKey m.resps hok' hrel
    -- the key's key-values: the first holds `FormatInt c`
    obtain ⟨v0, rest, hF, hv0⟩ : ∃ v0 rest, σ.kvs.filter (fun v => decide (v.key = compactRevKey)) =
        v0 :: rest ∧ v0.value = fmtInt c (W64 10) := by
      unfold keyValue at Hkv
      revert Hkv
      cases σ.kvs.filter (fun v => decide (v.key = compactRevKey)) with
      | nil => intro h; simp at h
      | cons v0 rest => intro h; simp at h; exact ⟨v0, rest, rfl, h⟩
    rw [hF] at hresps
    ihave ⟨%Hpl, #Hmall⟩ := opRespsMsg_getElem ps m.resps $$ Hms
    rw [hresps] at Hpl
    obtain ⟨p0, rfl⟩ : ∃ p0, ps = [p0] := by
      match ps, Hpl with
      | [p0], _ => exact ⟨p0, rfl⟩
    ihave #Hp0 := Hmall $$ %0 %p0 %(OpRespM.range rv (v0 :: rest) more count) %rfl
      %(by rw [hresps]; rfl)
    simp only [opRespMsg]
    icases Hp0 with ⟨%Hp0nn, %w, %rr, #Hw0, #Hrr0, #Hrange⟩
    iunfold txn.rangeResponseIs at Hrange
    icases Hrange with ⟨%Hrrnn, %h2, %ksl, %kps, #Hh2, %Hh2nn, #Hrev2, #Hkvsf, #Hksl, #Hkvsis, #Hmore,
      #Hcount⟩
    iunfold txn.kvsIs at Hkvsis
    icases Hkvsis with ⟨%Hklen, #Hkall⟩
    obtain ⟨kp0, kps', rfl⟩ : ∃ kp0 kps', kps = kp0 :: kps' := by
      cases kps with
      | nil => simp at Hklen
      | cons kp0 kps' => exact ⟨kp0, kps', rfl⟩
    ihave #Hk0 := Hkall $$ %0 %kp0 %v0 %rfl %rfl
    iunfold txn.kvIs at Hk0
    icases Hk0 with ⟨%keySl, %valSl, #Hkey, #Hkeys, #Hcrt, #Hmod, #Hver, #Hval, #Hvals, #Hlease⟩
    ihave %Hrsll := ownSlice_len _ _ _ $$ Hrsl
    ihave %Hksll := ownSlice_len _ _ _ $$ Hksl
    ihave #Ppb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb $$ []
    · iPkgInit
    wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z rsl.len by
      simp at Hrsll; constructor <;> word))]
    wp_apply wp_load_slice_index rsl (sint.Z (W64 0)) [p0] _ p0 (by decide) $$ [Hrsl] as -
    · iframe Hrsl; ipureintro; rfl
    wp_apply wp_GetResponseRange p0 w rr $$ [$Ppb $Hw0 $Hrr0]
    · ipureintro; exact Hp0nn
    (try wp_auto)
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z ksl.len by
      simp at Hksll; constructor <;> word))]
    wp_apply wp_load_slice_index ksl (sint.Z (W64 0)) (kp0 :: kps') _ kp0 (by decide) $$ [Hksl] as -
    · iframe Hksl; ipureintro; rfl
    (try wp_auto)
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z rsl.len by
      simp at Hrsll; constructor <;> word))]
    wp_apply wp_load_slice_index rsl (sint.Z (W64 0)) [p0] _ p0 (by decide) $$ [Hrsl] as -
    · iframe Hrsl; ipureintro; rfl
    wp_apply wp_GetResponseRange p0 w rr $$ [$Ppb $Hw0 $Hrr0]
    · ipureintro; exact Hp0nn
    (try wp_auto)
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z ksl.len by
      simp at Hksll; constructor <;> word))]
    wp_apply wp_load_slice_index ksl (sint.Z (W64 0)) (kp0 :: kps') _ kp0 (by decide) $$ [Hksl] as -
    · iframe Hksl; ipureintro; rfl
    (try wp_auto)
    wp_apply wp_bytes_to_string valSl v0.value DFrac.discard $$ [Hvals] as -
    · iexact Hvals
    wp_apply wp_ParseInt v0.value (W64 10) (W64 64) as %n %perr %Hp
    obtain ⟨rfl, rfl⟩ := Hp c hv0 rfl rfl
    wp_auto
    iapply HΦ
    iframe #
    isplitr
    · unfold recRevOk
      iunfold revOk at Hoc
      icases Hoc with (%Hc0 | ⟨%Hcpos, #Hclb⟩)
      · ileft; ipureintro; exact Hc0
      · iright; iframe #; ipureintro; exact Hcpos
    ipureintro; intro h; exact absurd rfl h
  · -- the compare held: the put, then the compaction
    rw [hs] at hok
    rw [← hok]
    simp only [↓reduceIte]
    wp_auto
    wp_if_destruct
    · -- `rev = 0`: the first round, no compaction
      (try wp_auto)
      iapply HΦ
      iframe #
      isplitr
      · unfold recRevOk; ileft; ipureintro; rfl
      ipureintro; intro _; rfl
    -- the client's `Compact(rev)`, `rev` reached
    ihave #Hrev' := Hrev
    iunfold revOk at Hrev'
    icases Hrev' with (%Hr0 | ⟨%Hrpos, #Hrlb⟩)
    · exact absurd Hr0 Hif
    ihave #Hko' := Hko
    iunfold clientKvOk at Hko'
    icases Hko' with ⟨%api', %dup, #Hkvf', #HkvOk⟩
    wp_apply (client.client_Compact_kv cl api' γk dup ci cd rev (by word) hcmp) $$ []
      as %cresp %cerr Hcout
    · iframe #
      rw [hcret]
      iExactEq Hrlb
      simp
    icases Hcout with (⟨%Hce0, %cm, -⟩ | ⟨%Hce0, #Hcke⟩)
    · subst Hce0
      (try wp_auto)
      ihave #Pkl : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.klog.v2 $$ []
      · iPkgInit
      wp_apply wp_Endpoints cl $$ [] as %esl ⟨%eps, Hesl, -⟩
      · iframe #
      (try wp_auto)
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sl5 -
      wp_auto
      wp_apply wp_V (W32 4) as %vb -
      wp_apply wp_Infof vb _ _ $$ []
      (try wp_auto)
      iapply HΦ
      iframe #
      isplitl [HQ]
      · unfold recRevOk; iright
        isplitr
        · ipureintro; exact Hrpos
        iframe
        iframe #
      ipureintro; intro h; exact absurd rfl h
    · cases cerr with
      | nil => exact absurd rfl Hce0.1
      | ok ei => ?_
      wp_auto
      iapply HΦ
      iframe #
      isplitr
      · unfold recRevOk; ileft; ipureintro; rfl
      ipureintro; intro _; rfl

end proof

end k8s
end EtcdGrove
end Perennial

/-
**etcd's server serves its KV methods with auth on** (the auth plan's E3zb, 2026-10-28;
`Results.lean`'s `etcd_*HandlerOk`, `etcd_*MethodOk` and `etcd_kv_served`, for a member started
with auth on): the handlers of `*kvServer` meet the auth-on specs (`KVServiceOn.lean`) at the
metadata of the run's context, from the server's answers with auth on (`v3rpc.*_end_to_end_on`,
at the run's token `auth.ctxTokenOf`, which is `auth.mdTokenOf` of the context's incoming metadata
by definition); grpc runs them through the quota wrapper and the interceptor chain as with auth
off. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.Results
public import Proof.go_etcd_io.etcd.client.v3.KVServiceOn

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace client

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `kvServerAt` reads of the server's parameters with auth on only the KV's `Rev()` resources
(`kvServerAt_srvKVAns`'s). -/
theorem kvServerAt_srvKVAnsOn (p s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (c c' cid mid n : w64) (F F' : mvcc.Log) (d d' : v3rpc.KVDep GF) (na na' : Nat)
    (tok tok' : Option GoString) :
    v3rpc.kvServerAt (GF := GF) p s (v3rpc.srvKVAnsOn s E ρ γr c F d na tok) cid mid n =
      v3rpc.kvServerAt p s (v3rpc.srvKVAnsOn s E ρ γr c' F' d' na' tok') cid mid n := by
  have h : (v3rpc.srvKVAnsOn (GF := GF) s E ρ γr c F d na tok).revR =
      (v3rpc.srvKVAnsOn s E ρ γr c' F' d' na' tok').revR := rfl
  unfold v3rpc.kvServerAt v3rpc.hdrIs
  rw [h]

/-- `readQ_of_ans` at the mode-`on` model (`rangeDepQOn`: the state of the log read is
`kvStM true`'s). -/
theorem readQ_of_ansOn (γr : ReadNames) (d : v3rpc.KVDep GF) (Q : KVState → IProp GF)
    (ser : Bool) (log : mvcc.Log)
    (h : (d = .none ∧ Q = fun _ => iprop(True)) ∨ d = .read Q) :
    (if ser then iprop(True) else
      ∃ L : List EntryModel, srvRLogLb γr.raft L ∗ ⌜kvModelM true γr.kv L = log⌝ ∗
        □ v3rpc.rangeDepQOn γr.kv d L : IProp GF) ⊢
      (if ser then iprop(True) else □ Q (kvStateOf log)) := by
  cases hs : ser
  · simp only [Bool.false_eq_true, ↓reduceIte]
    iintro ⟨%L, -, %HL, #HQ⟩
    rcases h with ⟨rfl, rfl⟩ | rfl
    · iintro !>; itrivial
    · simp only [v3rpc.rangeDepQOn, kvStM_true, kvStOn]
      rw [← HL, kvModelM_true]
      iintro !>
      iexact HQ
  · simp only [↓reduceIte]; iintro -; itrivial

mutual
theorem allPuts_toTxnOp : ∀ (u : v3rpc.ReqOp) (op : TxnOp), v3rpc.ReqOp.toTxnOp u = some op →
    u.allPuts = opPutKeys op
  | .range o, op, h => by simp only [v3rpc.ReqOp.toTxnOp, Option.some.injEq] at h; subst h; rfl
  | .put o, op, h => by
    simp only [v3rpc.ReqOp.toTxnOp, Option.some.injEq] at h; subst h
    simp only [v3rpc.ReqOp.allPuts, txn.putTxnOp]
    by_cases h1 : o.ignoreValue = true <;> by_cases h2 : o.ignoreLease = true <;> simp [h1, h2, opPutKeys]
  | .delete o, op, h => by simp only [v3rpc.ReqOp.toTxnOp, Option.some.injEq] at h; subst h; rfl
  | .empty, op, h => by simp [v3rpc.ReqOp.toTxnOp] at h
  | .txn cs ts es, op, h => by
    simp only [v3rpc.ReqOp.toTxnOp] at h
    cases ha : v3rpc.ReqOp.toTxnOps ts <;> cases hb : v3rpc.ReqOp.toTxnOps es <;>
      simp only [ha, hb] at h <;> try cases h
    rename_i a b
    simp only [v3rpc.ReqOp.allPuts, opPutKeys, allPutsL_toTxnOps ts a ha, allPutsL_toTxnOps es b hb]

theorem allPutsL_toTxnOps : ∀ (us : List v3rpc.ReqOp) (ops : List TxnOp),
    v3rpc.ReqOp.toTxnOps us = some ops → v3rpc.ReqOp.allPutsL us = opsPutKeys ops
  | [], ops, h => by simp only [v3rpc.ReqOp.toTxnOps, Option.some.injEq] at h; subst h; rfl
  | u :: us, ops, h => by
    simp only [v3rpc.ReqOp.toTxnOps] at h
    cases ha : v3rpc.ReqOp.toTxnOp u <;> cases hb : v3rpc.ReqOp.toTxnOps us <;>
      simp only [ha, hb] at h <;> try cases h
    rename_i a b
    simp only [v3rpc.ReqOp.allPutsL, opsPutKeys, allPuts_toTxnOp u a ha, allPutsL_toTxnOps us b hb]
end

mutual
theorem allDels_toTxnOp : ∀ (u : v3rpc.ReqOp) (op : TxnOp), v3rpc.ReqOp.toTxnOp u = some op →
    u.allDels = (opDelOps op).map v3rpc.delIvl
  | .range o, op, h => by simp only [v3rpc.ReqOp.toTxnOp, Option.some.injEq] at h; subst h; rfl
  | .put o, op, h => by
    simp only [v3rpc.ReqOp.toTxnOp, Option.some.injEq] at h; subst h
    simp only [v3rpc.ReqOp.allDels, txn.putTxnOp]
    by_cases h1 : o.ignoreValue = true <;> by_cases h2 : o.ignoreLease = true <;> simp [h1, h2, opDelOps]
  | .delete o, op, h => by simp only [v3rpc.ReqOp.toTxnOp, Option.some.injEq] at h; subst h; rfl
  | .empty, op, h => by simp [v3rpc.ReqOp.toTxnOp] at h
  | .txn cs ts es, op, h => by
    simp only [v3rpc.ReqOp.toTxnOp] at h
    cases ha : v3rpc.ReqOp.toTxnOps ts <;> cases hb : v3rpc.ReqOp.toTxnOps es <;>
      simp only [ha, hb] at h <;> try cases h
    rename_i a b
    simp only [v3rpc.ReqOp.allDels, opDelOps, allDelsL_toTxnOps ts a ha, allDelsL_toTxnOps es b hb,
      List.map_append]

theorem allDelsL_toTxnOps : ∀ (us : List v3rpc.ReqOp) (ops : List TxnOp),
    v3rpc.ReqOp.toTxnOps us = some ops → v3rpc.ReqOp.allDelsL us = (opsDelOps ops).map v3rpc.delIvl
  | [], ops, h => by simp only [v3rpc.ReqOp.toTxnOps, Option.some.injEq] at h; subst h; rfl
  | u :: us, ops, h => by
    simp only [v3rpc.ReqOp.toTxnOps] at h
    cases ha : v3rpc.ReqOp.toTxnOp u <;> cases hb : v3rpc.ReqOp.toTxnOps us <;>
      simp only [ha, hb] at h <;> try cases h
    rename_i a b
    simp only [v3rpc.ReqOp.allDelsL, opsDelOps, allDels_toTxnOp u a ha, allDelsL_toTxnOps us b hb,
      List.map_append]
end

theorem mem_toTxnOps : ∀ (us : List v3rpc.ReqOp) (ops : List TxnOp),
    v3rpc.ReqOp.toTxnOps us = some ops → ∀ v ∈ us, ∃ op ∈ ops, v3rpc.ReqOp.toTxnOp v = some op
  | [], _, _, v, hv => by cases hv
  | u :: us, ops, h, v, hv => by
    simp only [v3rpc.ReqOp.toTxnOps] at h
    cases ha : v3rpc.ReqOp.toTxnOp u <;> cases hb : v3rpc.ReqOp.toTxnOps us <;>
      simp only [ha, hb] at h <;> try cases h
    rename_i a b
    rcases List.mem_cons.mp hv with rfl | hv
    · exact ⟨a, List.mem_cons_self, ha⟩
    · obtain ⟨op, hop, h'⟩ := mem_toTxnOps us b hb v hv
      exact ⟨op, List.mem_cons_of_mem _ hop, h'⟩

theorem hits_map_delIvl (L : List OpFull) (k : GoString)
    (h : ∀ o ∈ L, inRange o.key o.base.rangeEnd k = false) : v3rpc.hits (L.map v3rpc.delIvl) k = false := by
  unfold v3rpc.hits
  rw [List.any_eq_false]
  intro d hd hc
  obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hd
  have h1 : v3rpc.hits [v3rpc.delIvl o] k = true := by
    unfold v3rpc.hits; simpa using hc
  have h2 := v3rpc.inRange_of_hits o k h1
  rw [h o ho] at h2; cases h2

mutual
theorem siblingSafe_of_model : ∀ (u : v3rpc.ReqOp) (op : TxnOp), v3rpc.ReqOp.toTxnOp u = some op →
    txnSibSafe op → v3rpc.ReqOp.siblingSafe u
  | .txn cs ts es, op, h, hs => by
    simp only [v3rpc.ReqOp.toTxnOp] at h
    cases ha : v3rpc.ReqOp.toTxnOps ts <;> cases hb : v3rpc.ReqOp.toTxnOps es <;>
      simp only [ha, hb] at h <;> try cases h
    rename_i a b
    exact ⟨siblingSafeL_of_model' ts a ha hs.1, siblingSafeL_of_model' es b hb hs.2⟩
  | .range _, _, _, _ => trivial
  | .put _, _, _, _ => trivial
  | .delete _, _, _, _ => trivial
  | .empty, _, _, _ => trivial

theorem siblingSafeL_of_model' : ∀ (us : List v3rpc.ReqOp) (ops : List TxnOp),
    v3rpc.ReqOp.toTxnOps us = some ops → txnSibSafeL ops → v3rpc.ReqOp.siblingSafeL us
  | [], _, _, _ => trivial
  | u :: us, ops, h, hs => by
    simp only [v3rpc.ReqOp.toTxnOps] at h
    cases ha : v3rpc.ReqOp.toTxnOp u <;> cases hb : v3rpc.ReqOp.toTxnOps us <;>
      simp only [ha, hb] at h <;> try cases h
    rename_i a b
    obtain ⟨h1, h2, h3⟩ := hs
    refine ⟨fun v hv => ?_, siblingSafe_of_model u a ha h2, siblingSafeL_of_model' us b hb h3⟩
    obtain ⟨b', hb', hvb⟩ := mem_toTxnOps us b hb v hv
    have hso := h1 b' hb'
    cases u with
    | txn cs ts es =>
      intro k hk
      rw [allPuts_toTxnOp _ _ ha] at hk
      rw [allDels_toTxnOp v b' hvb]
      simp only [v3rpc.ReqOp.toTxnOp] at ha
      cases hc : v3rpc.ReqOp.toTxnOps ts <;> cases hd : v3rpc.ReqOp.toTxnOps es <;>
        simp only [hc, hd] at ha <;> try cases ha
      exact hits_map_delIvl _ k (hso k hk)
    | _ => trivial
end

/-- **The model's sibling safety is the handler's** (`notes/txn-nested.md`, L7): request operations
whose model is sibling-safe (`txnSibSafeL`, over the model's ranges) are (`ReqOp.siblingSafeL`, over
the handler's intervals; by `v3rpc.inRange_of_hits`). -/
theorem siblingSafeL_of_model (us : List v3rpc.ReqOp) (ops : List TxnOp)
    (h : v3rpc.ReqOp.toTxnOps us = some ops) (hs : txnSibSafeL ops) : v3rpc.ReqOp.siblingSafeL us := by
  exact siblingSafeL_of_model' us ops h hs

/-- **etcd's `Put` handler meets etcd's `Put` spec with auth on** (`grpcHandlerOkMd`; from
`put_end_to_end_on`, at no lower bound of the published auth index): as `etcd_putHandlerOk`, the
reply also with the put's grant at the run's token. -/
theorem etcd_putHandlerOn (p s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (cid mid n : w64) (γa : auth.AuthNames) (hγa : E.authMode = .on γa) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReqM true s E ρ ∗ isServerReadM true s E γr ∗ srvAuthLb s E ∗
        v3rpc.kvServerAt p s (v3rpc.srvKVAnsOn s E ρ γr (W64 0) [] .none 0 none) cid mid n ∗
        □ (|==> idCred ρ.ids 1) ⊢
      grpcHandlerOkMd (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty @!!
      go!"Put") (etcdRunSlot s E γr) (etcdPutSpecOn s E ρ cid mid) := by
  iintro ⟨#Pv, #Ps, #Hsrv, #Hsrd, #Hlb, #Hat, #HNR⟩
  unfold grpcHandlerOkMd
  iintro %o %Φ %ci %cd %r !> %Ψ ⟨Hslot, #Hctx, #Hrc, #Hr, Hspec⟩ HΨ
  ihave #Htr := ctxTraceIs_none_of_runCtx ci $$ Hrc
  rw [show (pbPutRequest (GF := GF)).recv r o = txn.putRequestIs r o from rfl]
  iunfold etcdPutSpecOn at Hspec
  rw [← auth.ctxTokenOf_md]
  icases Hspec with ⟨%F, #HF, Hspec⟩
  ihave ⟨%d, Hdep, %Hdp, Hk⟩ : iprop(∃ d : v3rpc.KVDep GF, v3rpc.kvDepOwnOn s E ρ γr (auth.ctxTokenOf (GoInterface.ok ci)) d ∗
      ⌜v3rpc.kvDepPre d (.put o)⌝ ∗
      ∀ m : PutRespM, putReplied E ρ.rd F o (v3rpc.opDepQ d) cid mid m -∗
        v3rpc.writeGrantOn s E ρ (auth.ctxTokenOf (GoInterface.ok ci)) (irrPut o) -∗ Φ m)
      $$ [Hspec]
  · icases Hspec with ⟨%Q, %Hpl, Hau, Hk⟩
    iexists (.op1 (.put o) Q)
    rw [show v3rpc.kvDepOwnOn (GF := GF) s E ρ γr (auth.ctxTokenOf (GoInterface.ok ci)) (.op1 (.put o) Q) =
      v3rpc.kvOpAuOn s E ρ (auth.ctxTokenOf (GoInterface.ok ci)) (.put o) Q from rfl]
    isplitl [Hau]
    · iexact Hau
    isplitr
    · ipureintro; exact ⟨⟨Q, rfl⟩, Hpl⟩
    iintro %m Hm
    iapply Hk
    simp only [v3rpc.opDepQ]; iexact Hm
  rw [kvServerAt_srvKVAnsOn p s E ρ γr (W64 0) (W64 0) cid mid n [] F .none d 0 0 none
    (auth.ctxTokenOf (GoInterface.ok ci))]
  iunfold etcdRunSlot at Hslot
  icases Hslot with ⟨Hlt, Hsr, Hlg, Hrd, Hard⟩
  ihave Hu := HNR
  imod Hu with Hid
  imod (monoNatLbOwn_0 (GF := GF) γr.committed) with #H0
  imod (authPubLbM_zero (GF := GF) E.authMode) with #Hna
  iapply wp_fupd
  iapply (v3rpc.put_end_to_end_on p s E ρ γr (W64 0) cid mid n (GoInterface.ok ci) r o F d 0 γa hγa) $$
    [Hlt Hsr Hlg Hrd Hard Hid Hdep]
  · iframe #
    unfold v3rpc.srvCall srvRdCall committedAtLeast
    isplitl [Hlt Hid]
    · iexists ci, cd
      iframe
      iframe #
      ipureintro; rfl
    iframe
    rw [show uint.nat (W64 0) = 0 from rfl]
    iframe H0
    ipureintro; exact ⟨Hdp, trivial⟩
  inext
  iintro %resp %err Hpost
  cases hc : v3rpc.putCheck o with
  | some e =>
    icases Hpost with ⟨#Hco, Hc, Hc0, -⟩
    unfold v3rpc.srvCall
    icases Hc with ⟨%ci', %cd', -, -, -, -, Hlt⟩
    iunfold v3rpc.checkOut at Hco
    icases Hco with ⟨-, #Hev⟩
    iunfold txn.errVarIs at Hev
    icases Hev with ⟨%e', -, %He'⟩
    imodintro
    iapply HΨ
    isplitl [Hlt Hc0]
    · iapply etcdRunSlot_back s E γr (W64 0)
      iframe
    iintro %Hnil
    rw [He'] at Hnil; cases Hnil
  | none =>
    icases Hpost with (⟨%Herr, %h, %rv, %rv', #Hh, Hf, -, Hc0, Hap, #Hg⟩ | ⟨%Herr, %e, Hc0, Hep⟩)
    · obtain ⟨rfl, Hrn⟩ := Herr
      iunfold v3rpc.putAppliedOk at Hap
      icases Hap with ⟨Hlt, Hap⟩
      iunfold v3rpc.putApplied at Hap
      icases Hap with ⟨%hm, %x, %x', %l, %skip, %Hst, Hout, #Hcert, Htok, #Hwit, #Hcok, HQv⟩
      imod readM_keys true s E γr x'.log $$ Hsrd Hcert Hcok with %Hkeys
      iunfold apply.putOutcomeIs at Hout
      icases Hout with ⟨#Hpr, -⟩
      iunfold txn.putResponseIs at Hpr
      icases Hpr with ⟨-, %h2, %pk, #Hh2, %Hh2n, #Hrev, #Hpk, #Hprev⟩
      icombine Hh Hh2 gives %Heq
      subst Heq
      iunfold v3rpc.hdrFilled at Hf
      icases Hf with ⟨-, %t, %ld, Hcid, Hmid, Ht, Hl⟩
      ipersist Hcid
      ipersist Hmid
      ipersist Ht
      ipersist Hl
      imodintro
      iapply HΨ
      isplitl [Hlt Hc0]
      · iapply etcdRunSlot_back s E γr (W64 0)
        iframe
      iintro -
      iexists (PutRespM.mk (HdrM.mk cid mid (W64 (x.log.length : Int)) t ld)
        (if o.base.prevKV then mvcc.findKey o.key (mvcc.stateAfter x.log) else none))
      isplitl []
      · simp only [pbPutResponse]
        unfold putRespMsg hdrFull
        isplitl []
        · ipureintro; exact Hrn
        iexists h, pk
        iframe #
        ipureintro; exact Hh2n
      · iapply Hk $$ [Htok HQv] Hg
        unfold putReplied
        iexists hm, x, x', l, skip
        iframe Htok HQv
        iframe #
        ipureintro
        exact ⟨⟨Hst.1, rfl, rfl, rfl, rfl, Hst.2.2⟩, Hkeys⟩
    · iunfold v3rpc.putErrOk at Hep
      icases Hep with ⟨Hlt, -⟩
      imodintro
      iapply HΨ
      isplitl [Hlt Hc0]
      · iapply etcdRunSlot_back s E γr (W64 0)
        iframe
      iintro %Hnil
      exact absurd Hnil Herr.2

/-- **etcd's `Range` handler meets etcd's `Range` spec with auth on** (`grpcHandlerOkMd`; from
`range_end_to_end_on`, at the caller's lower bound of the published auth index): as
`etcd_rangeHandlerOk`, the reply also with the read's check at the run's token. -/
theorem etcd_rangeHandlerOn (p s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (cid mid n : w64) (γa : auth.AuthNames) (hγa : E.authMode = .on γa) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReqM true s E ρ ∗ isServerReadM true s E γr ∗ srvAuthLb s E ∗
        v3rpc.kvServerAt p s (v3rpc.srvKVAnsOn s E ρ γr (W64 0) [] .none 0 none) cid mid n ∗
        □ (|==> idCred ρ.ids 1) ⊢
      grpcHandlerOkMd (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty @!!
      go!"Range") (etcdRunSlot s E γr) (etcdRangeSpecOn s E γr cid mid) := by
  iintro ⟨#Pv, #Ps, #Hsrv, #Hsrd, #Hlb, #Hat, #HNR⟩
  unfold grpcHandlerOkMd
  iintro %o %Φ %ci %cd %r !> %Ψ ⟨Hslot, #Hctx, #Hrc, #Hr, Hspec⟩ HΨ
  ihave #Htr := ctxTraceIs_none_of_runCtx ci $$ Hrc
  rw [show (pbRangeRequest (GF := GF)).recv r o = txn.rangeRequestIs r o from rfl]
  iunfold etcdRangeSpecOn at Hspec
  rw [← auth.ctxTokenOf_md]
  icases Hspec with ⟨%c, %F, %Q, %na, #Hc0, #HF, #Hna, Hdq, Hk⟩
  ihave ⟨%d, Hdep, %Hdp, %Hdd⟩ : iprop(∃ d : v3rpc.KVDep GF, v3rpc.kvDepOwn ρ γr d ∗
      ⌜v3rpc.kvDepPre d (.range o)⌝ ∗
      ⌜(d = .none ∧ Q = fun _ => iprop(True)) ∨ d = .read Q⌝) $$ [Hdq]
  · icases Hdq with (%HQ | ⟨%Hser, #Hau⟩)
    · iexists .none
      rw [show v3rpc.kvDepOwn (GF := GF) ρ γr .none = iprop(True) from rfl]
      isplitr
      · itrivial
      ipureintro
      exact ⟨(fun Q' h => by cases h), Or.inl ⟨rfl, HQ⟩⟩
    · iexists (.read Q)
      rw [show v3rpc.kvDepOwn (GF := GF) ρ γr (.read Q) = kvReadAu γr.kv Q from rfl]
      iframe Hau
      ipureintro
      exact ⟨(fun Q' h => by cases h; exact Hser), Or.inr rfl⟩
  rw [kvServerAt_srvKVAnsOn p s E ρ γr (W64 0) c cid mid n [] F .none d 0 na none
    (auth.ctxTokenOf (GoInterface.ok ci))]
  iunfold etcdRunSlot at Hslot
  icases Hslot with ⟨Hlt, Hsr, Hlg, Hrd, Hard⟩
  ihave Hu := HNR
  imod Hu with Hid
  imod (v3rpc.kvDepOwnOn_of_dep s E ρ γr (auth.ctxTokenOf (GoInterface.ok ci)) d) $$ Hdep with Hdep
  iapply wp_fupd
  iapply (v3rpc.range_end_to_end_on p s E ρ γr c cid mid n (GoInterface.ok ci) r o F d na γa hγa) $$
    [Hlt Hsr Hlg Hrd Hard Hid Hdep]
  · iframe #
    unfold v3rpc.srvCall srvRdCall
    isplitl [Hlt Hid]
    · iexists ci, cd
      iframe
      iframe #
      ipureintro; rfl
    iframe
    iframe Hc0
    ipureintro; exact ⟨Hdp, trivial⟩
  inext
  iintro %resp %err Hpost
  cases hc : v3rpc.rangeCheck o with
  | some e =>
    icases Hpost with ⟨#Hco, Hc, Hcr, -⟩
    unfold v3rpc.srvCall
    icases Hc with ⟨%ci', %cd', -, -, -, -, Hlt⟩
    iunfold v3rpc.checkOut at Hco
    icases Hco with ⟨-, #Hev⟩
    iunfold txn.errVarIs at Hev
    icases Hev with ⟨%e', -, %He'⟩
    imodintro
    iapply HΨ
    isplitl [Hlt Hcr]
    · iapply etcdRunSlot_back s E γr c
      iframe
    iintro %Hnil
    rw [He'] at Hnil; cases Hnil
  | none =>
    icases Hpost with (⟨%Herr, %h, %rv, %rv', #Hh, Hf, -, Hcr, -, Hlt, Hans, Hau⟩ |
      ⟨%Herr, %e, Hcr, -, Hlt⟩)
    · obtain ⟨rfl, Hrn⟩ := Herr
      iunfold v3rpc.rangeAnsOkOn at Hans
      icases Hans with ⟨%log, #Hcert, #Hcok, %Hlog, #Hrl, HQl, Hres⟩
      imod readM_keys true s E γr log $$ Hsrd Hcert Hcok with %Hkeys
      ihave #HQl' := readQ_of_ansOn γr d Q o.base.serializable log Hdd $$ HQl
      icases Hres with ⟨%crev, Hres⟩
      iunfold txn.rangeResult at Hres
      icases Hres with (⟨%Hx, -⟩ | ⟨%Hx, -⟩ | ⟨%Hx, %kvs, %more, #Hrr, %Hsel⟩ | ⟨%Hx, -⟩)
      · exact absurd Hx.2 Hrn
      · exact absurd Hx.2.2.2.1 Hrn
      rotate_left
      · exact absurd Hx.2.2 Hrn
      iunfold txn.rangeResponseIs at Hrr
      icases Hrr with ⟨-, %h2, %sl, %ps, #Hh2, %Hh2n, #Hrev, #Hkvs, #Hps, #Hkv, #Hmore, #Hcount⟩
      icombine Hh Hh2 gives %Heq
      subst Heq
      iunfold v3rpc.hdrFilled at Hf
      icases Hf with ⟨-, %t, %ld, Hcid, Hmid, Ht, Hl⟩
      ipersist Hcid
      ipersist Hmid
      ipersist Ht
      ipersist Hl
      imodintro
      iapply HΨ
      isplitl [Hlt Hcr]
      · iapply etcdRunSlot_back s E γr c
        iframe
      iintro -
      iexists (RangeRespM.mk (HdrM.mk cid mid (W64 ((log.length : Int) - 1)) t ld) kvs more
        (txn.srvCount o (mvcc.stateAt log (sint.nat (mvcc.rangeRev (W64 ((log.length : Int) - 1))
          o.base.rev))) true))
      isplitl []
      · simp only [pbRangeResponse]
        unfold rangeRespMsg hdrFull
        isplitl []
        · ipureintro; exact Hrn
        iexists h, sl, ps
        iframe #
        ipureintro; exact Hh2n
      · iapply Hk $$ [] Hau
        unfold rangeReplyOk
        iexists log
        iframe #
        ipureintro
        exact ⟨Hkeys, Hlog.1, Hlog.2.1, rfl, rfl, rfl, Hx.1, rfl, Hsel, Hlog.2.2.2⟩
    · imodintro
      iapply HΨ
      isplitl [Hlt Hcr]
      · iapply etcdRunSlot_back s E γr c
        iframe
      iintro %Hnil
      exact absurd Hnil Herr.2

/-- **etcd's `DeleteRange` handler meets etcd's `DeleteRange` spec with auth on**
(`grpcHandlerOkMd`; from `deleteRange_end_to_end_on`): as `etcd_putHandlerOn`. -/
theorem etcd_deleteHandlerOn (p s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (cid mid n : w64) (γa : auth.AuthNames) (hγa : E.authMode = .on γa) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReqM true s E ρ ∗ isServerReadM true s E γr ∗ srvAuthLb s E ∗
        v3rpc.kvServerAt p s (v3rpc.srvKVAnsOn s E ρ γr (W64 0) [] .none 0 none) cid mid n ∗
        □ (|==> idCred ρ.ids 1) ⊢
      grpcHandlerOkMd
        (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty @!!
          go!"DeleteRange")
        (etcdRunSlot s E γr) (etcdDeleteSpecOn s E ρ cid mid) := by
  iintro ⟨#Pv, #Ps, #Hsrv, #Hsrd, #Hlb, #Hat, #HNR⟩
  unfold grpcHandlerOkMd
  iintro %o %Φ %ci %cd %r !> %Ψ ⟨Hslot, #Hctx, #Hrc, #Hr, Hspec⟩ HΨ
  ihave #Htr := ctxTraceIs_none_of_runCtx ci $$ Hrc
  rw [show (pbDeleteRangeRequest (GF := GF)).recv r o = txn.deleteRangeRequestIs r o from rfl]
  iunfold etcdDeleteSpecOn at Hspec
  rw [← auth.ctxTokenOf_md]
  icases Hspec with ⟨%Hsh, %F, #HF, %Q, %Hz, Hau, Hk⟩
  rw [kvServerAt_srvKVAnsOn p s E ρ γr (W64 0) (W64 0) cid mid n [] F .none
    (.op1 (.deleteRange o) Q) 0 0 none (auth.ctxTokenOf (GoInterface.ok ci))]
  iunfold etcdRunSlot at Hslot
  icases Hslot with ⟨Hlt, Hsr, Hlg, Hrd, Hard⟩
  ihave Hu := HNR
  imod Hu with Hid
  imod (monoNatLbOwn_0 (GF := GF) γr.committed) with #H0
  imod (authPubLbM_zero (GF := GF) E.authMode) with #Hna
  rw [show v3rpc.kvOpAuOn (GF := GF) s E ρ (auth.ctxTokenOf (GoInterface.ok ci)) (.deleteRange o) Q =
      v3rpc.kvDepOwnOn s E ρ γr (auth.ctxTokenOf (GoInterface.ok ci)) (.op1 (.deleteRange o) Q)
      from rfl]
  iapply wp_fupd
  iapply (v3rpc.deleteRange_end_to_end_on p s E ρ γr (W64 0) cid mid n (GoInterface.ok ci) r o F
      (.op1 (.deleteRange o) Q) 0 γa hγa) $$ [Hlt Hsr Hlg Hrd Hard Hid Hau]
  · iframe # Hau
    unfold v3rpc.srvCall srvRdCall committedAtLeast
    isplitl [Hlt Hid]
    · iexists ci, cd
      iframe
      iframe #
      ipureintro; rfl
    iframe
    rw [show uint.nat (W64 0) = 0 from rfl]
    iframe H0
    ipureintro; exact ⟨⟨⟨Q, rfl⟩, Hz⟩, Hsh⟩
  inext
  iintro %resp %err Hpost
  cases hc : v3rpc.deleteCheck o with
  | some e =>
    icases Hpost with ⟨#Hco, Hc, Hc0, -⟩
    unfold v3rpc.srvCall
    icases Hc with ⟨%ci', %cd', -, -, -, -, Hlt⟩
    iunfold v3rpc.checkOut at Hco
    icases Hco with ⟨-, #Hev⟩
    iunfold txn.errVarIs at Hev
    icases Hev with ⟨%e', -, %He'⟩
    imodintro
    iapply HΨ
    isplitl [Hlt Hc0]
    · iapply etcdRunSlot_back s E γr (W64 0)
      iframe
    iintro %Hnil
    rw [He'] at Hnil; cases Hnil
  | none =>
    icases Hpost with (⟨%Herr, %h, %rv, %rv', #Hh, Hf, -, Hc0, Hap, #Hg⟩ | ⟨%Herr, %e, Hc0, Hep⟩)
    · obtain ⟨rfl, Hrn⟩ := Herr
      iunfold v3rpc.deleteAppliedOk at Hap
      icases Hap with ⟨Hlt, Hap⟩
      iunfold v3rpc.deleteApplied at Hap
      icases Hap with ⟨%hm, %rq', %op', %x, %x', %l, %skip, %Hst, Hout, #Hcert, Htok, #Hwit, #Hcok,
        HQv⟩
      imod readM_keys true s E γr x'.log $$ Hsrd Hcert Hcok with %Hkeys
      simp only [v3rpc.opDepQ] at *
      iunfold apply.deleteOutcomeIs at Hout
      icases Hout with ⟨#Hdr, -⟩
      iunfold txn.deleteRangeResponseIs at Hdr
      icases Hdr with ⟨-, %h2, %sl, %ps, #Hh2, %Hh2n, #Hrev, #Hdel, #Hpk, #Hps, #Hkvs⟩
      icombine Hh Hh2 gives %Heq
      subst Heq
      iunfold v3rpc.hdrFilled at Hf
      icases Hf with ⟨-, %t, %ld, Hcid, Hmid, Ht, Hl⟩
      ipersist Hcid
      ipersist Hmid
      ipersist Ht
      ipersist Hl
      imodintro
      iapply HΨ
      isplitl [Hlt Hc0]
      · iapply etcdRunSlot_back s E γr (W64 0)
        iframe
      iintro -
      iexists (DelRespM.mk (HdrM.mk cid mid
          (W64 ((mvcc.writeRev x.log (txn.delChanges (mvcc.stateAfter x.log) op') : Nat) : Int))
          t ld)
        (W64 ((rangeIn (mvcc.stateAfter x.log) op').length : Int))
        (if op'.base.prevKV then rangeIn (mvcc.stateAfter x.log) op' else []))
      isplitl []
      · simp only [pbDeleteRangeResponse]
        unfold delRespMsg hdrFull
        isplitl []
        · ipureintro; exact Hrn
        iexists h, sl, ps
        iframe #
        ipureintro; exact Hh2n
      · iapply Hk $$ [Htok HQv] Hg
        unfold deleteReplied
        iexists hm, rq', op', x, x', l, skip
        iframe Htok HQv
        iframe #
        ipureintro
        exact ⟨⟨Hst.1, Hst.2.1, Hst.2.2.1, Hst.2.2.2.1, rfl, rfl, rfl, rfl, rfl, Hst.2.2.2.2.2⟩,
          Hkeys⟩
    · iunfold v3rpc.deleteErrOk at Hep
      icases Hep with ⟨Hlt, -⟩
      imodintro
      iapply HΨ
      isplitl [Hlt Hc0]
      · iapply etcdRunSlot_back s E γr (W64 0)
        iframe
      iintro %Hnil
      exact absurd Hnil Herr.2

/-- **etcd's `Txn` handler meets etcd's `Txn` spec with auth on** (`grpcHandlerOkMd`; from
`txn_end_to_end_on`, at the caller's lower bound of the published auth index): as
`etcd_txnHandlerOk`, the reply also with the transaction's auth facts at the run's token
(`txnAuthOn`). -/
theorem etcd_txnHandlerOn (p s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (cid mid n : w64) (γa : auth.AuthNames) (hγa : E.authMode = .on γa) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReqM true s E ρ ∗ isServerReadM true s E γr ∗ srvAuthLb s E ∗
        v3rpc.kvServerAt p s (v3rpc.srvKVAnsOn s E ρ γr (W64 0) [] .none 0 none) cid mid n ∗
        □ (|==> idCred ρ.ids 1) ⊢
      grpcHandlerOkMd (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty @!!
      go!"Txn") (etcdRunSlot s E γr) (etcdTxnSpecOn s E ρ γr cid mid) := by
  iintro ⟨#Pv, #Ps, #Hsrv, #Hsrd, #Hlb, #Hat, #HNR⟩
  unfold grpcHandlerOkMd
  iintro %t %Φ %ci %cd %r !> %Ψ ⟨Hslot, #Hctx, #Hrc, #Hr, Hspec⟩ HΨ
  ihave #Htr := ctxTraceIs_none_of_runCtx ci $$ Hrc
  rw [show (pbTxnRequest (GF := GF)).recv r t = iprop(txn.txnRequestIs r t ∗ txnWireOk r t)
    from rfl]
  iunfold etcdTxnSpecOn at Hspec
  rw [← auth.ctxTokenOf_md]
  icases Hspec with ⟨%Hpl, %Q, Hnp, %c, %F, %na, #Hc0, #HF, #Hna, Hspec⟩
  obtain ⟨hin, hsh⟩ := Hpl
  icases Hr with ⟨#Hreq, #Hw⟩
  ihave ⟨%ts, %es, #Htq, #Htw, %Hmod⟩ := txnReq_of_requestIs r t $$ [$Hreq $Hw]
  ihave ⟨%d, Hdep, %Hdp, %HdQ⟩ : iprop(∃ d : v3rpc.KVDep GF, v3rpc.kvDepOwnOn s E ρ γr (auth.ctxTokenOf (GoInterface.ok ci)) d ∗
      ⌜v3rpc.kvDepPre d (.txn t.cmps ts es)⌝ ∗
      ⌜(txn.txnReadonly t = true ∧ ((d = .none ∧ Q = fun _ => iprop(True)) ∨ d = .read Q)) ∨
        (txn.txnReadonly t = false ∧ d = .op1 (.txn t) Q)⌝) $$ [Hnp]
  · icases Hnp with (%Hro | ⟨%Hrs, #Hau⟩ | ⟨%Hw, Hau⟩)
    · iexists .none
      rw [show v3rpc.kvDepOwnOn (GF := GF) s E ρ γr (auth.ctxTokenOf (GoInterface.ok ci)) .none = iprop(True) from rfl]
      isplitr
      · itrivial
      ipureintro
      refine ⟨?_, Or.inl ⟨Hro.1, Or.inl ⟨rfl, Hro.2⟩⟩⟩
      intro t' ht'
      rw [Hmod] at ht'
      cases ht'
      left; exact ⟨Hro.1, fun Q' h => by cases h⟩
    · iexists (.read Q)
      rw [show v3rpc.kvDepOwnOn (GF := GF) s E ρ γr (auth.ctxTokenOf (GoInterface.ok ci)) (.read Q) = kvReadAu γr.kv Q from rfl]
      iframe Hau
      ipureintro
      refine ⟨?_, Or.inl ⟨Hrs.1, Or.inr rfl⟩⟩
      intro t' ht'
      rw [Hmod] at ht'
      cases ht'
      left; exact ⟨Hrs.1, fun Q' _ => Hrs.2⟩
    · iexists (.op1 (.txn t) Q)
      rw [show v3rpc.kvDepOwnOn (GF := GF) s E ρ γr (auth.ctxTokenOf (GoInterface.ok ci)) (.op1 (.txn t) Q) =
        v3rpc.kvOpAuOn s E ρ (auth.ctxTokenOf (GoInterface.ok ci)) (.txn t) Q from rfl]
      iframe Hau
      ipureintro
      refine ⟨?_, Or.inr ⟨Hw.1, rfl⟩⟩
      intro t' ht'
      rw [Hmod] at ht'
      cases ht'
      right
      have hfl := v3rpc.txnModelOf_ops Hmod
      obtain ⟨-, hpl, hnz, hn1, hn2, hs1, hs2⟩ := Hw
      exact ⟨⟨Q, rfl⟩, hpl, hnz,
        siblingSafeL_of_model ts t.thenOps hfl.1 hs1,
        siblingSafeL_of_model es t.elseOps hfl.2 hs2, hn1, hn2⟩
  rw [kvServerAt_srvKVAnsOn p s E ρ γr (W64 0) c cid mid n [] F .none d 0 na none
    (auth.ctxTokenOf (GoInterface.ok ci))]
  iunfold etcdRunSlot at Hslot
  icases Hslot with ⟨Hlt, Hsr, Hlg, Hrd⟩
  ihave Hu := HNR
  imod Hu with Hid
  iapply wp_fupd
  iapply (v3rpc.txn_end_to_end_on p s E ρ γr c cid mid n (GoInterface.ok ci) r t.cmps ts es F d na
    γa hγa) $$ [Hlt Hsr Hlg Hrd Hid Hdep]
  · iframe #
    unfold v3rpc.srvCall srvRdCall
    isplitl [Hlt Hid]
    · iexists ci, cd
      iframe
      iframe #
      ipureintro; rfl
    iframe
    iframe Hc0
    isplitr
    · ipureintro; exact txnInModel_of t _ _ _ hin Hmod
    ipureintro
    refine ⟨Hdp, fun t' ht' hro tw htw => ?_⟩
    rw [Hmod] at ht'
    cases ht'
    exact hsh hro tw htw
  inext
  iintro %resp %err Hpost
  cases hc : v3rpc.txnAllCheck (sint.Z n) t.cmps ts es with
  | some e =>
    simp only [hc]
    icases Hpost with ⟨#Hco, Hc, Hcr, -⟩
    unfold v3rpc.srvCall
    icases Hc with ⟨%ci', %cd', -, -, -, -, Hlt⟩
    iunfold v3rpc.checkOut at Hco
    icases Hco with ⟨-, #Hev⟩
    iunfold txn.errVarIs at Hev
    icases Hev with ⟨%e', -, %He'⟩
    imodintro
    iapply HΨ
    isplitl [Hlt Hcr]
    · iapply etcdRunSlot_back s E γr c
      iframe
    iintro %Hnil
    rw [He'] at Hnil; cases Hnil
  | none =>
    simp only [hc]
    icases Hpost with (⟨%Herr, %h, %rv, %rv', #Hh, Hf, -, Hcr, Hlt, %t', %Ht', Hans⟩ |
      ⟨%Herr, %e, Hcr, Hlt, -⟩)
    · rw [Hmod] at Ht'
      cases Ht'
      obtain ⟨rfl, Hrn⟩ := Herr
      cases hro : txn.txnReadonly t with
      | true =>
        simp only [hro, ↓reduceIte]
        icases Hans with ⟨-, Hans, Hau⟩
        iunfold v3rpc.txnReadAnsOn at Hans
        icases Hans with ⟨%log, #Hcert, #Hcok, %Hlog, #Hrl, HQl, Hres⟩
        imod readM_keys true s E γr log $$ Hsrd Hcert Hcok with %Hkeys
        have hdq : (d = .none ∧ Q = fun _ => iprop(True)) ∨ d = .read Q := by
          rcases HdQ with ⟨-, h⟩ | ⟨h, -⟩
          · exact h
          · rw [hro] at h; cases h
        ihave #HQl' := readQ_of_ansOn γr d Q (txn.txnSerializable t) log hdq $$ HQl
        ihave Ha : txnAuthOn s E ρ γr c na (auth.ctxTokenOf (GoInterface.ok ci)) t $$ [Hau]
        · unfold txnAuthOn; simp only [hro, ↓reduceIte]; iexact Hau
        imod (txnRespMsg_of_server false resp h _ t _ _ cid mid) $$ [$Hh $Hf $Hres]
          with ⟨%m, #Hm, %Hmm⟩
        imodintro
        iapply HΨ
        isplitl [Hlt Hcr]
        · iapply etcdRunSlot_back s E γr c
          iframe
        iintro -
        iexists m
        isplitl []
        · simp only [pbTxnResponse]; iexact Hm
        iapply Hspec $$ [] Ha
        unfold txnReplied
        simp only [hro, ↓reduceIte]
        iexists log
        iframe #
        ipureintro
        obtain ⟨h1, h2, h3, h4, h5⟩ := Hmm
        refine ⟨Hkeys, Hlog.1, Hlog.2.1, Hlog.2.2.2, ?_, h2, h3, h4, ?_⟩
        · rw [h1]
        · rw [h4]; exact h5
      | false =>
        simp only [hro, Bool.false_eq_true, ↓reduceIte]
        icases Hans with ⟨Hans, Hg⟩
        ihave Ha : txnAuthOn s E ρ γr c na (auth.ctxTokenOf (GoInterface.ok ci)) t $$ [Hg]
        · unfold txnAuthOn; simp only [hro, Bool.false_eq_true, ↓reduceIte]; iexact Hg
        iunfold v3rpc.txnAppliedAns at Hans
        icases Hans with ⟨%tw, %hm, %rq', %t'', %x, %x', %l, %skip, %Hst, Hout, #Hcert, HMint, #Hwit,
          #Hcok, HQv⟩
        imod readM_keys true s E γr x'.log $$ Hsrd Hcert Hcok with %Hkeys
        have hdq : d = .op1 (.txn t) Q := by
          rcases HdQ with ⟨h, -⟩ | ⟨-, h⟩
          · rw [hro] at h; cases h
          · exact h
        subst hdq
        simp only [v3rpc.opDepQ] at *
        iunfold apply.txnOutcomeIs at Hout
        icases Hout with ⟨#Hres, -⟩
        imod (txnRespMsg_of_server skip resp h _ t'' _ _ cid mid) $$ [$Hh $Hf $Hres]
          with ⟨%m, #Hm, %Hmm⟩
        imodintro
        iapply HΨ
        isplitl [Hlt Hcr]
        · iapply etcdRunSlot_back s E γr c
          iframe
        iintro -
        iexists m
        isplitl []
        · simp only [pbTxnResponse]; iexact Hm
        iapply Hspec $$ [Hcert HMint Hwit Hcok HQv] Ha
        unfold txnReplied
        simp only [hro, Bool.false_eq_true, ↓reduceIte]
        iexists tw, hm, rq', t'', x, x', l, skip
        iframe Hcert HMint Hwit Hcok HQv
        ipureintro
        obtain ⟨h1, h2, h3, h4, h5⟩ := Hmm
        obtain ⟨s0, s1, s2, s3, s4, s5, s6, s7, s8, s9⟩ := Hst
        refine ⟨⟨s0, s1, s2, s3, s4, ?_, h2, h3, s6, s7, s8, h4, ?_, s9⟩, Hkeys⟩
        · rw [h1]
        · rw [h4]; exact h5
    · obtain ⟨-, Hne⟩ := Herr
      imodintro
      iapply HΨ
      isplitl [Hlt Hcr]
      · iapply etcdRunSlot_back s E γr c
        iframe
      iintro %Hnil
      exact absurd Hnil Hne


/-- **A `*quotaKVServer`'s `Put`, as grpc runs it, at a metadata-indexed spec** (`etcd_putMethodOk`'s). -/
theorem etcd_putMethodOn (q : Loc) (S : IProp GF) (ics : List GoFunc) (Rs : List (IProp GF))
    (Spec : GrpcSpecMd (GF := GF) pbPutRequest pbPutResponse) :
    grpcHandlerOkMd (q @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaKVServer.ty @!! go!"Put")
        S Spec ∗ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
        srvInterceptorsOk v3rpc.learnerReqOk ics Rs ⊢
      grpcMethodOkMd (@! etcdserverpb._KV_Put_Handler)
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaKVServer.ty) #q)
        ics iprop(S ∗ [∗list] R ∈ Rs, R) Spec := by
  iintro ⟨#Hh, #Ppb, #Hics⟩
  unfold grpcMethodOkMd
  iintro %m %Φ %ci %cd %dec %ui !> %Ψ ⟨⟨HS, HRs⟩, #Hctx, #Hrc, #Hdec, #Hch, HSpec⟩ HΨ
  ihave #Hbl : iprop(□ ∀ l : Loc, l ↦ (zero_val etcdserverpb.PutRequest) -∗
      (pbPutRequest (GF := GF)).blank l) $$ []
  · iintro !> %l Hl; simp only [pbPutRequest]; iexact Hl
  ihave #HQr : iprop(□ ∀ l : Loc, (pbPutRequest (GF := GF)).recv l m -∗
      v3rpc.learnerReqOk (interface.mkOk (go.GoType.PointerType etcdserverpb.PutRequest.ty) #l)) $$ []
  · iintro !> %l -
    iapply putReq_learnerOk
  iapply (v3rpc.etcdserverpb.wp__KV_Put_Handler pbPutRequest pbPutResponse Spec
    ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaKVServer.ty, #q⟩
    S ics Rs v3rpc.learnerReqOk m Φ ci cd dec ui rfl rfl v3rpc.QuotaKVServerIsKVServer.is_kv)
    $$ [HS HRs HSpec]
  · iframe; iframe #
  inext
  iintro %resp %err ⟨HS, HRs, Hres⟩
  iapply HΨ
  iframe

/-- **`Range`, as grpc runs it, at a metadata-indexed spec** (`etcd_rangeMethodOk`'s). -/
theorem etcd_rangeMethodOn (q : Loc) (S : IProp GF) (ics : List GoFunc) (Rs : List (IProp GF))
    (Spec : GrpcSpecMd (GF := GF) pbRangeRequest pbRangeResponse) :
    grpcHandlerOkMd (q @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaKVServer.ty @!! go!"Range")
        S Spec ∗ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
        srvInterceptorsOk v3rpc.learnerReqOk ics Rs ⊢
      grpcMethodOkMd (@! etcdserverpb._KV_Range_Handler)
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaKVServer.ty) #q)
        ics iprop(S ∗ [∗list] R ∈ Rs, R) Spec := by
  iintro ⟨#Hh, #Ppb, #Hics⟩
  unfold grpcMethodOkMd
  iintro %m %Φ %ci %cd %dec %ui !> %Ψ ⟨⟨HS, HRs⟩, #Hctx, #Hrc, #Hdec, #Hch, HSpec⟩ HΨ
  ihave #Hbl : iprop(□ ∀ l : Loc, l ↦ (zero_val etcdserverpb.RangeRequest) -∗
      (pbRangeRequest (GF := GF)).blank l) $$ []
  · iintro !> %l Hl; simp only [pbRangeRequest]; iexact Hl
  ihave #HQr : iprop(□ ∀ l : Loc, (pbRangeRequest (GF := GF)).recv l m -∗
      v3rpc.learnerReqOk (interface.mkOk (go.GoType.PointerType etcdserverpb.RangeRequest.ty) #l)) $$ []
  · iintro !> %l #Hr
    rw [show (pbRangeRequest (GF := GF)).recv l m = txn.rangeRequestIs l m from rfl]
    iapply (v3rpc.learnerReqOk_range l m)
    iexact Hr
  iapply (v3rpc.etcdserverpb.wp__KV_Range_Handler pbRangeRequest pbRangeResponse Spec
    ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaKVServer.ty, #q⟩
    S ics Rs v3rpc.learnerReqOk m Φ ci cd dec ui rfl rfl v3rpc.QuotaKVServerIsKVServer.is_kv)
    $$ [HS HRs HSpec]
  · iframe; iframe #
  inext
  iintro %resp %err ⟨HS, HRs, Hres⟩
  iapply HΨ
  iframe

/-- **`DeleteRange`, as grpc runs it, at a metadata-indexed spec** (`etcd_deleteMethodOk`'s). -/
theorem etcd_deleteMethodOn (q : Loc) (S : IProp GF) (ics : List GoFunc) (Rs : List (IProp GF))
    (Spec : GrpcSpecMd (GF := GF) pbDeleteRangeRequest pbDeleteRangeResponse) :
    grpcHandlerOkMd (q @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaKVServer.ty @!! go!"DeleteRange")
        S Spec ∗ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
        srvInterceptorsOk v3rpc.learnerReqOk ics Rs ⊢
      grpcMethodOkMd (@! etcdserverpb._KV_DeleteRange_Handler)
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaKVServer.ty) #q)
        ics iprop(S ∗ [∗list] R ∈ Rs, R) Spec := by
  iintro ⟨#Hh, #Ppb, #Hics⟩
  unfold grpcMethodOkMd
  iintro %m %Φ %ci %cd %dec %ui !> %Ψ ⟨⟨HS, HRs⟩, #Hctx, #Hrc, #Hdec, #Hch, HSpec⟩ HΨ
  ihave #Hbl : iprop(□ ∀ l : Loc, l ↦ (zero_val etcdserverpb.DeleteRangeRequest) -∗
      (pbDeleteRangeRequest (GF := GF)).blank l) $$ []
  · iintro !> %l Hl; simp only [pbDeleteRangeRequest]; iexact Hl
  ihave #HQr : iprop(□ ∀ l : Loc, (pbDeleteRangeRequest (GF := GF)).recv l m -∗
      v3rpc.learnerReqOk (interface.mkOk (go.GoType.PointerType etcdserverpb.DeleteRangeRequest.ty) #l)) $$ []
  · iintro !> %l -
    iapply deleteReq_learnerOk
  iapply (v3rpc.etcdserverpb.wp__KV_DeleteRange_Handler pbDeleteRangeRequest pbDeleteRangeResponse Spec
    ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaKVServer.ty, #q⟩
    S ics Rs v3rpc.learnerReqOk m Φ ci cd dec ui rfl rfl v3rpc.QuotaKVServerIsKVServer.is_kv)
    $$ [HS HRs HSpec]
  · iframe; iframe #
  inext
  iintro %resp %err ⟨HS, HRs, Hres⟩
  iapply HΨ
  iframe

/-- **`Txn`, as grpc runs it, at a metadata-indexed spec** (`etcd_txnMethodOk`'s). -/
theorem etcd_txnMethodOn (q : Loc) (S : IProp GF) (ics : List GoFunc) (Rs : List (IProp GF))
    (Spec : GrpcSpecMd (GF := GF) pbTxnRequest pbTxnResponse) :
    grpcHandlerOkMd (q @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaKVServer.ty @!! go!"Txn")
        S Spec ∗ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
        srvInterceptorsOk v3rpc.learnerReqOk ics Rs ⊢
      grpcMethodOkMd (@! etcdserverpb._KV_Txn_Handler)
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaKVServer.ty) #q)
        ics iprop(S ∗ [∗list] R ∈ Rs, R) Spec := by
  iintro ⟨#Hh, #Ppb, #Hics⟩
  unfold grpcMethodOkMd
  iintro %m %Φ %ci %cd %dec %ui !> %Ψ ⟨⟨HS, HRs⟩, #Hctx, #Hrc, #Hdec, #Hch, HSpec⟩ HΨ
  ihave #Hbl : iprop(□ ∀ l : Loc, l ↦ (zero_val etcdserverpb.TxnRequest) -∗
      (pbTxnRequest (GF := GF)).blank l) $$ []
  · iintro !> %l Hl; simp only [pbTxnRequest]; iexact Hl
  ihave #HQr : iprop(□ ∀ l : Loc, (pbTxnRequest (GF := GF)).recv l m -∗
      v3rpc.learnerReqOk (interface.mkOk (go.GoType.PointerType etcdserverpb.TxnRequest.ty) #l)) $$ []
  · iintro !> %l -
    iapply txnReq_learnerOk
  iapply (v3rpc.etcdserverpb.wp__KV_Txn_Handler pbTxnRequest pbTxnResponse Spec
    ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaKVServer.ty, #q⟩
    S ics Rs v3rpc.learnerReqOk m Φ ci cd dec ui rfl rfl v3rpc.QuotaKVServerIsKVServer.is_kv)
    $$ [HS HRs HSpec]
  · iframe; iframe #
  inext
  iintro %resp %err ⟨HS, HRs, Hres⟩
  iapply HΨ
  iframe

/-- **etcd's KV methods with auth on** (`etcdKVMethods`'s, at the auth-on specs). -/
def etcdKVMethodsOn (q s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (cid mid : w64) :
    List (GrpcMethod GF) :=
  [⟨go!"/etcdserverpb.KV/Put", pbPutRequest, pbPutResponse, etcdPutSpecOn s E ρ cid mid,
     (@! etcdserverpb._KV_Put_Handler), interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaKVServer.ty) #q⟩,
   ⟨go!"/etcdserverpb.KV/Range", pbRangeRequest, pbRangeResponse, etcdRangeSpecOn s E γr cid mid,
     (@! etcdserverpb._KV_Range_Handler), interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaKVServer.ty) #q⟩,
   ⟨go!"/etcdserverpb.KV/DeleteRange", pbDeleteRangeRequest, pbDeleteRangeResponse,
     etcdDeleteSpecOn s E ρ cid mid, (@! etcdserverpb._KV_DeleteRange_Handler),
     interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaKVServer.ty) #q⟩,
   ⟨go!"/etcdserverpb.KV/Txn", pbTxnRequest, pbTxnResponse,
     etcdTxnSpecOn s E ρ γr cid mid, (@! etcdserverpb._KV_Txn_Handler),
     interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaKVServer.ty) #q⟩]

/-- **etcd's server serves its KV methods with auth on** (`etcd_kv_served`'s, for a server started
with auth on: `isServerReqM true`, `isServerReadM true`, the auth store's published index
`srvAuthLb`, the KV server's answers with auth on `srvKVAnsOn`): registers the auth-on specs
(`isGrpcRpcMd`: a call's spec at the metadata the run's context carries). -/
theorem etcd_kv_served_on (addr : GoString) (p q s : Loc)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (cid mid n : w64) (il im iu : GoFunc)
    (regs : List (GoString × val × GoInterface)) (N : Nat) (γa : auth.AuthNames)
    (hγa : E.authMode = .on γa)
    (hregs : ∀ x ∈ etcdKVRegs (GF := GF) q, x ∈ regs) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReqM true s E ρ ∗ isServerReadM true s E γr ∗ srvAuthLb s E ∗
        v3rpc.kvServerAt p s (v3rpc.srvKVAnsOn s E ρ γr (W64 0) [] .none 0 none) cid mid n ∗
        □ (|==> idCred ρ.ids 1) ∗
        v3rpc.quotaKVServerAt q
          ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty, #p⟩ s ∗
        srvInterceptorOk il (srvLgReader s) v3rpc.learnerReqOk ∗
        srvInterceptorOk im iprop(True) v3rpc.learnerReqOk ∗
        srvInterceptorOk iu iprop(True) v3rpc.learnerReqOk ∗
        grpcServerAt addr [il, im, iu] regs ∗
        ([∗list] _x ∈ List.replicate N (), etcdGrpcSlot s E γr) ⊢
      |={⊤}=> isGrpcRpcMd addr go!"/etcdserverpb.KV/Put" (etcdPutSpecOn s E ρ cid mid) ∗
        isGrpcRpcMd addr go!"/etcdserverpb.KV/Range" (etcdRangeSpecOn s E γr cid mid) ∗
        isGrpcRpcMd addr go!"/etcdserverpb.KV/DeleteRange" (etcdDeleteSpecOn s E ρ cid mid) ∗
        isGrpcRpcMd addr go!"/etcdserverpb.KV/Txn" (etcdTxnSpecOn s E ρ γr cid mid) := by
  iintro ⟨#Pv, #Ps, #Hsrv, #Hsrd, #Hlb, #Hat, #HNR, #Hq, #Hil, #Him, #Hiu, Hl, Hslots⟩
  ihave #Hp := etcd_putHandlerOn p s E ρ γr cid mid n γa hγa $$ []
  · iframe #
  ihave #Hr := etcd_rangeHandlerOn p s E ρ γr cid mid n γa hγa $$ []
  · iframe #
  ihave #Hd := etcd_deleteHandlerOn p s E ρ γr cid mid n γa hγa $$ []
  · iframe #
  ihave #Ht := etcd_txnHandlerOn p s E ρ γr cid mid n γa hγa $$ []
  · iframe #
  ihave #Hqt := v3rpc.quotaKV_txnHandlerOkMd_of v3rpc.quotaKVServer.wp_Txn (etcdTxnSpecOn s E ρ γr cid mid) q s
    ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty, #p⟩
    (etcdRunSlot s E γr) $$ []
  · iframe #
  ihave #Hqp := v3rpc.quotaKV_putHandlerOkMd_of v3rpc.quotaKVServer.wp_Put (etcdPutSpecOn s E ρ cid mid) q s
    ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty, #p⟩
    (etcdRunSlot s E γr) $$ []
  · iframe #
  ihave #Hr' := grpcHandlerOkMd_frame _ _ (v3rpc.quotaRd s) (etcdRangeSpecOn s E γr cid mid) $$ Hr
  ihave #Hd' := grpcHandlerOkMd_frame _ _ (v3rpc.quotaRd s) (etcdDeleteSpecOn s E ρ cid mid) $$ Hd
  ihave #Hqr := v3rpc.quotaKV_promotedHandlerOkMd (etcdRangeSpecOn s E γr cid mid) q s
    ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty, #p⟩
    iprop(etcdRunSlot s E γr ∗ v3rpc.quotaRd s) go!"Range" inferInstance $$ [Hq Hr']
  · iframe #
  ihave #Hqd := v3rpc.quotaKV_promotedHandlerOkMd (etcdDeleteSpecOn s E ρ cid mid) q s
    ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty, #p⟩
    iprop(etcdRunSlot s E γr ∗ v3rpc.quotaRd s) go!"DeleteRange" inferInstance $$ [Hq Hd']
  · iframe #
  ihave #Hics : srvInterceptorsOk (GF := GF) v3rpc.learnerReqOk [il, im, iu] (etcdIcRs s) $$ []
  · unfold etcdIcRs srvInterceptorsOk srvInterceptorsOk srvInterceptorsOk srvInterceptorsOk
    iframe #
  ihave #Ppb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb $$ []
  · iPkgInit
  ihave #Hmp := etcd_putMethodOn q _ _ _ (etcdPutSpecOn s E ρ cid mid) $$ [Hqp Ppb Hics]
  · iframe #
  ihave #Hmr := etcd_rangeMethodOn q _ _ _ (etcdRangeSpecOn s E γr cid mid) $$ [Hqr Ppb Hics]
  · iframe #
  ihave #Hmd := etcd_deleteMethodOn q _ _ _ (etcdDeleteSpecOn s E ρ cid mid) $$ [Hqd Ppb Hics]
  · iframe #
  ihave #Hmt := etcd_txnMethodOn q _ _ _ (etcdTxnSpecOn s E ρ γr cid mid) $$ [Hqt Ppb Hics]
  · iframe #
  imod (grpc_serve_rpcs addr [il, im, iu] regs (etcdKVMethodsOn q s E ρ γr cid mid)
    (etcdGrpcSlot s E γr) N (by simp only [etcdKVMethodsOn, List.map]; decide)
    (by
      intro x hx
      apply hregs
      simp only [etcdKVMethodsOn, List.mem_cons, List.mem_nil_iff, _root_.or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> simp [etcdKVRegs])) $$ [Hl Hslots] with Hrpcs
  · iframe
    imodintro
    simp only [etcdKVMethodsOn]
    unfold etcdGrpcSlot
    iframe #
    iapply BigSepL.bigSepL_nil.2
    itrivial
  simp only [etcdKVMethodsOn]
  icases Hrpcs with ⟨#H1, #H2, #H3, #H4, -⟩
  imodintro
  iframe #

/-- A method meeting the metadata-indexed `Spec` with the slot `S` meets it with a slot `S'` that
splits into `S` and a frame `F` and is rebuilt from them. -/
theorem grpcMethodOkMd_slot {Req Rep : ProtoMsg GF} (mh : val) (srv : GoInterface)
    (ics : List GoFunc) (S S' F : IProp GF) (Spec : GrpcSpecMd Req Rep)
    (h1 : S' ⊢ S ∗ F) (h2 : S ∗ F ⊢ S') :
    grpcMethodOkMd mh srv ics S Spec ⊢ grpcMethodOkMd mh srv ics S' Spec := by
  iintro #Hm
  unfold grpcMethodOkMd
  iintro %m %Φ %ci %cd %dec %ui !> %Ψ ⟨HS, Hctx, Hrc, Hd, Hch, HSpec⟩ HΨ
  ihave ⟨HS, HF⟩ := h1 $$ HS
  iapply Hm $$ %m %Φ %ci %cd %dec %ui [HS Hctx Hrc Hd Hch HSpec]
  · iframe
  inext
  iintro %resp %err ⟨HS, Hres⟩
  iapply HΨ
  iframe Hres
  iapply h2
  iframe

/-- The KV methods' run slot is the Auth methods' (`authSlot` and the interceptors'), with the rest
of the KV handlers' slot and the quota check's. -/
theorem etcdGrpcSlot_auth (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) :
    etcdGrpcSlot (GF := GF) s E γr ⊣⊢
      iprop((v3rpc.authSlot s E ∗ [∗list] R ∈ etcdIcRs s, R) ∗
        (mvcc.storeReader E.s E.γ ∗ srvLgReader s ∗ srvReadReader s γr ∗ v3rpc.quotaRd s)) := by
  unfold etcdGrpcSlot etcdRunSlot v3rpc.authSlot
  constructor
  · iintro ⟨⟨⟨Hlt, Hsr, Hlg, Hrd, Hard⟩, Hq⟩, Hics⟩
    iframe
  · iintro ⟨⟨⟨Hlt, Hard⟩, Hics⟩, Hsr, Hlg, Hrd, Hq⟩
    iframe

/-- **etcd's server serves its KV methods with auth on and its Auth methods** (one gRPC server:
`etcd_kv_served_on` and `etcd_auth_served` together, as `grpc.serve` takes every served method at
once; the run slot the KV's `etcdGrpcSlot`, of which the Auth methods' is a part). -/
theorem etcd_kv_auth_served_on (addr : GoString) (p q pa s : Loc)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (cid mid n : w64) (il im iu : GoFunc)
    (ast : GoInterfaceOk) (regs : List (GoString × val × GoInterface)) (N : Nat)
    (γa : auth.AuthNames) (hγa : E.authMode = .on γa)
    (hregs : ∀ x ∈ etcdKVRegs (GF := GF) q ++ v3rpc.authRegs pa, x ∈ regs) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReqM true s E ρ ∗ isServerReadM true s E γr ∗ srvAuthLb s E ∗
        v3rpc.kvServerAt p s (v3rpc.srvKVAnsOn s E ρ γr (W64 0) [] .none 0 none) cid mid n ∗
        □ (|==> idCred ρ.ids 1) ∗
        v3rpc.quotaKVServerAt q
          ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty, #p⟩ s ∗
        v3rpc.authServerIs pa s ∗
        structFieldRef EtcdServer go!"authStore" s ↦□ GoInterface.ok ast ∗ bcryptCostOk ast ∗
        srvInterceptorOk il (srvLgReader s) v3rpc.learnerReqOk ∗
        srvInterceptorOk im iprop(True) v3rpc.learnerReqOk ∗
        srvInterceptorOk iu iprop(True) v3rpc.learnerReqOk ∗
        grpcServerAt addr [il, im, iu] regs ∗
        ([∗list] _x ∈ List.replicate N (), etcdGrpcSlot s E γr) ⊢
      |={⊤}=> isGrpcRpcMd addr go!"/etcdserverpb.KV/Put" (etcdPutSpecOn s E ρ cid mid) ∗
        isGrpcRpcMd addr go!"/etcdserverpb.KV/Range" (etcdRangeSpecOn s E γr cid mid) ∗
        isGrpcRpcMd addr go!"/etcdserverpb.KV/DeleteRange" (etcdDeleteSpecOn s E ρ cid mid) ∗
        isGrpcRpcMd addr go!"/etcdserverpb.KV/Txn" (etcdTxnSpecOn s E ρ γr cid mid) ∗
        isGrpcRpcMd addr go!"/etcdserverpb.Auth/UserAdd" (v3rpc.etcdUserAddSpec s E ρ) ∗
        isGrpcRpcMd addr go!"/etcdserverpb.Auth/UserGrantRole" (v3rpc.etcdUserGrantRoleSpec s E ρ) ∗
        isGrpcRpcMd addr go!"/etcdserverpb.Auth/RoleAdd" (v3rpc.etcdRoleAddSpec s E ρ) ∗
        isGrpcRpcMd addr go!"/etcdserverpb.Auth/RoleGrantPermission"
          (v3rpc.etcdRoleGrantPermissionSpec s E ρ) ∗
        isGrpcRpcMd addr go!"/etcdserverpb.Auth/AuthEnable" (v3rpc.etcdAuthEnableSpec s E ρ) := by
  iintro ⟨#Pv, #Ps, #Hsrv, #Hsrd, #Hlb, #Hat, #HNR, #Hq, #Has, #Hast, #Hcost, #Hil, #Him, #Hiu,
    Hl, Hslots⟩
  ihave #Hp := etcd_putHandlerOn p s E ρ γr cid mid n γa hγa $$ []
  · iframe #
  ihave #Hr := etcd_rangeHandlerOn p s E ρ γr cid mid n γa hγa $$ []
  · iframe #
  ihave #Hd := etcd_deleteHandlerOn p s E ρ γr cid mid n γa hγa $$ []
  · iframe #
  ihave #Ht := etcd_txnHandlerOn p s E ρ γr cid mid n γa hγa $$ []
  · iframe #
  ihave #Hqt := v3rpc.quotaKV_txnHandlerOkMd_of v3rpc.quotaKVServer.wp_Txn (etcdTxnSpecOn s E ρ γr cid mid) q s
    ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty, #p⟩
    (etcdRunSlot s E γr) $$ []
  · iframe #
  ihave #Hqp := v3rpc.quotaKV_putHandlerOkMd_of v3rpc.quotaKVServer.wp_Put (etcdPutSpecOn s E ρ cid mid) q s
    ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty, #p⟩
    (etcdRunSlot s E γr) $$ []
  · iframe #
  ihave #Hr' := grpcHandlerOkMd_frame _ _ (v3rpc.quotaRd s) (etcdRangeSpecOn s E γr cid mid) $$ Hr
  ihave #Hd' := grpcHandlerOkMd_frame _ _ (v3rpc.quotaRd s) (etcdDeleteSpecOn s E ρ cid mid) $$ Hd
  ihave #Hqr := v3rpc.quotaKV_promotedHandlerOkMd (etcdRangeSpecOn s E γr cid mid) q s
    ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty, #p⟩
    iprop(etcdRunSlot s E γr ∗ v3rpc.quotaRd s) go!"Range" inferInstance $$ [Hq Hr']
  · iframe #
  ihave #Hqd := v3rpc.quotaKV_promotedHandlerOkMd (etcdDeleteSpecOn s E ρ cid mid) q s
    ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty, #p⟩
    iprop(etcdRunSlot s E γr ∗ v3rpc.quotaRd s) go!"DeleteRange" inferInstance $$ [Hq Hd']
  · iframe #
  ihave #Hics : srvInterceptorsOk (GF := GF) v3rpc.learnerReqOk [il, im, iu] (etcdIcRs s) $$ []
  · unfold etcdIcRs srvInterceptorsOk srvInterceptorsOk srvInterceptorsOk srvInterceptorsOk
    iframe #
  ihave #Ppb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb $$ []
  · iPkgInit
  ihave #Hmp := etcd_putMethodOn q _ _ _ (etcdPutSpecOn s E ρ cid mid) $$ [Hqp Ppb Hics]
  · iframe #
  ihave #Hmr := etcd_rangeMethodOn q _ _ _ (etcdRangeSpecOn s E γr cid mid) $$ [Hqr Ppb Hics]
  · iframe #
  ihave #Hmd := etcd_deleteMethodOn q _ _ _ (etcdDeleteSpecOn s E ρ cid mid) $$ [Hqd Ppb Hics]
  · iframe #
  ihave #Hmt := etcd_txnMethodOn q _ _ _ (etcdTxnSpecOn s E ρ γr cid mid) $$ [Hqt Ppb Hics]
  · iframe #
  -- the Auth methods, at their slot (`authSlot` and the interceptors'), then at the KV's
  ihave #Hu := v3rpc.etcd_userAddHandlerOk pa s E ρ ast $$ []
  · iframe #
  ihave #Hg := v3rpc.etcd_userGrantRoleHandlerOk pa s E ρ $$ []
  · iframe #
  ihave #Hra := v3rpc.etcd_roleAddHandlerOk pa s E ρ $$ []
  · iframe #
  ihave #Hrp := v3rpc.etcd_roleGrantPermissionHandlerOk pa s E ρ $$ []
  · iframe #
  ihave #He := v3rpc.etcd_authEnableHandlerOk pa s E ρ $$ []
  · iframe #
  ihave #Hmu := v3rpc.etcd_userAddMethodOk pa _ _ [il, im, iu] (etcdIcRs s) $$ [Hu Ppb Hics]
  · iframe #
  ihave #Hmg := v3rpc.etcd_userGrantRoleMethodOk pa _ _ [il, im, iu] (etcdIcRs s) $$ [Hg Ppb Hics]
  · iframe #
  ihave #Hmra := v3rpc.etcd_roleAddMethodOk pa _ _ [il, im, iu] (etcdIcRs s) $$ [Hra Ppb Hics]
  · iframe #
  ihave #Hmrp := v3rpc.etcd_roleGrantPermissionMethodOk pa _ _ [il, im, iu] (etcdIcRs s) $$
    [Hrp Ppb Hics]
  · iframe #
  ihave #Hme := v3rpc.etcd_authEnableMethodOk pa _ _ [il, im, iu] (etcdIcRs s) $$ [He Ppb Hics]
  · iframe #
  have hs1 := (etcdGrpcSlot_auth (GF := GF) s E γr).1
  have hs2 := (etcdGrpcSlot_auth (GF := GF) s E γr).2
  ihave #Hmu' := grpcMethodOkMd_slot _ _ _ _ _ _ _ hs1 hs2 $$ Hmu
  ihave #Hmg' := grpcMethodOkMd_slot _ _ _ _ _ _ _ hs1 hs2 $$ Hmg
  ihave #Hmra' := grpcMethodOkMd_slot _ _ _ _ _ _ _ hs1 hs2 $$ Hmra
  ihave #Hmrp' := grpcMethodOkMd_slot _ _ _ _ _ _ _ hs1 hs2 $$ Hmrp
  ihave #Hme' := grpcMethodOkMd_slot _ _ _ _ _ _ _ hs1 hs2 $$ Hme
  imod (grpc_serve_rpcs addr [il, im, iu] regs (etcdKVMethodsOn q s E ρ γr cid mid ++
      v3rpc.etcdAuthMethods pa s E ρ)
    (etcdGrpcSlot s E γr) N
    (by simp only [etcdKVMethodsOn, v3rpc.etcdAuthMethods, List.map, List.cons_append,
          List.nil_append]
        decide)
    (by
      intro x hx
      apply hregs
      simp only [etcdKVMethodsOn, v3rpc.etcdAuthMethods, List.cons_append, List.nil_append,
        List.mem_cons, List.mem_nil_iff, _root_.or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [etcdKVRegs, v3rpc.authRegs]))
    $$ [Hl Hslots] with Hrpcs
  · iframe
    imodintro
    simp only [etcdKVMethodsOn, v3rpc.etcdAuthMethods, List.cons_append, List.nil_append]
    unfold etcdGrpcSlot
    iframe #
    iapply BigSepL.bigSepL_nil.2
    itrivial
  simp only [etcdKVMethodsOn, v3rpc.etcdAuthMethods, List.cons_append, List.nil_append]
  icases Hrpcs with ⟨#H1, #H2, #H3, #H4, #H5, #H6, #H7, #H8, #H9, -⟩
  imodintro
  iframe #

end proofs

end client
end EtcdGrove
end Perennial


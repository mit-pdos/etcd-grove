/-
**etcd's specs of its KV service's methods**, as etcd's server registers them with grpc
(`etcdPutSpec`, `etcdRangeSpec`, `etcdDeleteSpec`, `etcdTxnSpec`: predicate transformers over the
messages' models, `GrpcSpec`), the per-run slots the server hands grpc's runtime (`etcdRunSlot`,
`etcdGrpcSlot`) and the methods `RegisterKVServer` registers (`etcdKVMethods`, `etcdKVRegs`); the
proof that the server meets them: `KVServed.lean`. Moved here from `client/v3/Results.lean`
(2026-10-15): the server's specs belong to the server's package; the client's results
(`client/v3/Results.lean`) instantiate the client's specs, proved for any `GrpcSpec`, with these.
Lean-first (no Rocq counterpart); the design: `notes/decisions.md`, "A generic gRPC
specification".

**The specs**: a caller asking the request `o` gets a reply message `m` with `putReplied`
(`putReplyOk`, persistent, with the write's witness `appliedWit γr` since unit C2a, and the token of
the revision the put made, `revMinted`: the slice's unit V1, carried since a reply's `Φ` is
delivered once), `rangeReplyOk` at the committed index `c` the caller knows of
(`committedAtLeast γr c`, persistent, `0` free), `deleteReplied` (`deleteReplyOk` and the token),
`txnReplied`; a put, delete or transaction with the caller's persistent update over the whole
state (unit T2), a range with its read update.

**What the client learns** (`putReplyOk`, `rangeReplyOk`, `deleteReplyOk`, persistent): for a
`Put`, the apply thread's application of the put the server decoded at the log the entry met, the
reply's header revision that log's length, its ids the cluster's and member's, its previous
key-value the state's if asked, mvcc's certificate of the log after (`put_end_to_end`'s
`putAppliedOk`, carried to the reply); for a `Get`, the txn package's range at a certified log of
at least two revisions (`range_end_to_end`'s `rangeAnsOk`), read after the read index unless
serializable (`readLogOk γr c log`), the reply's key-values, `More` and `Count` the server's
selection; for a `DeleteRange`, the application of the delete the proposed data decode to.

Also here: the wire's request and response models of a transaction related to the server's
(`reqOp_of_requestOp`, `txnReq_of_requestIs`, `opResp_of_responseOp`, `txnRespMsg_of_server`;
plain operations, `TxnOp.plain`: what the client's builder makes).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Results
public import Proof.go_etcd_io.etcd.client.v3.InvKVConn

@[expose] public section

set_option pp.fullNames true
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace v3rpc

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver

/-! ## Plain operations -/

/-- An operation that is not a nested transaction (what the client's builder makes: `txnOpOf`
never gives one). -/
def TxnOp.plain : TxnOp → Prop
  | .txn _ _ _ => False
  | _ => True

/-- A transaction of plain operations, in both branches. -/
def TxnModel.plain (t : TxnModel) : Prop :=
  (∀ op ∈ t.thenOps, TxnOp.plain op) ∧ ∀ op ∈ t.elseOps, TxnOp.plain op

theorem opWire_plain (op : TxnOp) (h : TxnOp.plain op) : TxnOp.plain (opWire op) := by
  cases op <;> simp_all [TxnOp.plain, opWire]

theorem txnOpOf_plain (o : OpFull) (op : TxnOp) (h : txnOpOf o = some op) : TxnOp.plain op := by
  unfold txnOpOf at h
  repeat' split at h
  all_goals first
    | (simp only [Option.some.injEq] at h; subst h; trivial)
    | cases h

/-- A delete's count of plain operations: `delCountT` and `v3rpc.delCount` agree. -/
theorem delCount_toTxnOps : ∀ (us : List v3rpc.ReqOp) (ops : List TxnOp),
    v3rpc.ReqOp.toTxnOps us = some ops → (∀ op ∈ ops, TxnOp.plain op) → v3rpc.delCount us = delCountT ops
  | [], ops, h, _ => by
    simp [v3rpc.ReqOp.toTxnOps] at h; subst h; simp [v3rpc.delCount, delCountT]
  | u :: us, ops, h, hp => by
    simp only [v3rpc.ReqOp.toTxnOps] at h
    split at h
    · rename_i t ts h1 h2
      simp only [Option.some.injEq] at h
      subst h
      have ih := delCount_toTxnOps us ts h2 (fun op hm => hp op (List.mem_cons_of_mem _ hm))
      have ht := hp t (List.mem_cons_self ..)
      cases u with
      | range o => simp [v3rpc.ReqOp.toTxnOp] at h1; subst h1; simp [v3rpc.delCount, delCountT, ih]
      | put o =>
        simp [v3rpc.ReqOp.toTxnOp] at h1; subst h1
        unfold txn.putTxnOp
        split <;> (try split) <;> simp [v3rpc.delCount, delCountT, ih]
      | delete o => simp [v3rpc.ReqOp.toTxnOp] at h1; subst h1; simp [v3rpc.delCount, delCountT, ih]
      | txn cs ts' es' =>
        simp only [v3rpc.ReqOp.toTxnOp] at h1
        split at h1 <;> simp at h1
        subst h1; exact ht.elim
      | empty => simp [v3rpc.ReqOp.toTxnOp] at h1
    · cases h

section bridge
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **A plain operation of the server's copy is the handler's request operation**: the txn
package's `requestOpIs` of a plain operation is `v3rpc.reqOpIs` of a request operation whose
model it is. -/
theorem reqOp_of_requestOp (p : Loc) (op : TxnOp) (hp : TxnOp.plain op) :
    txn.requestOpIs (GF := GF) p op ⊢ ∃ u : v3rpc.ReqOp, v3rpc.reqOpIs p u ∗ ⌜v3rpc.ReqOp.toTxnOp u = some op⌝ := by
  cases op with
  | txn cs ts es => exact hp.elim
  | get o =>
    iintro #H
    iunfold txn.requestOpIs at H
    icases H with ⟨%Hn, %u, %w, %r, %o', #Hu, (⟨%Hx, #Hw, #Hr⟩ | ⟨%Hx, -⟩ | ⟨%Hx, -⟩)⟩
    · obtain ⟨rfl, Ho⟩ := Hx
      cases Ho
      iexists (v3rpc.ReqOp.range o)
      isplitl
      · unfold v3rpc.reqOpIs; imodintro; isplitl; · ipureintro; exact Hn
        iexists w, r; iframe #
      · ipureintro; rfl
    · exfalso
      have := Hx.2
      unfold txn.putTxnOp at this; split at this <;> (try split at this) <;> simp at this
    · cases Hx.2
  | delete o =>
    iintro #H
    iunfold txn.requestOpIs at H
    icases H with ⟨%Hn, %u, %w, %r, %o', #Hu, (⟨%Hx, -⟩ | ⟨%Hx, -⟩ | ⟨%Hx, #Hw, #Hr⟩)⟩
    · cases Hx.2
    · exfalso
      have := Hx.2
      unfold txn.putTxnOp at this; split at this <;> (try split at this) <;> simp at this
    · obtain ⟨rfl, Ho⟩ := Hx
      cases Ho
      iexists (v3rpc.ReqOp.delete o)
      isplitl
      · unfold v3rpc.reqOpIs; imodintro; isplitl; · ipureintro; exact Hn
        iexists w, r; iframe #
      · ipureintro; rfl
  | put k v l =>
    iintro #H
    iunfold txn.requestOpIs at H
    icases H with ⟨%Hn, %u, %w, %r, %o', #Hu, (⟨%Hx, -⟩ | ⟨%Hx, #Hw, #Hr⟩ | ⟨%Hx, -⟩)⟩
    · cases Hx.2
    · obtain ⟨rfl, Ho⟩ := Hx
      iexists (v3rpc.ReqOp.put o')
      isplitl
      · unfold v3rpc.reqOpIs; imodintro; isplitl; · ipureintro; exact Hn
        iexists w, r; iframe #
      · ipureintro; simp [v3rpc.ReqOp.toTxnOp, Ho]
    · cases Hx.2
  | putKeep k l =>
    iintro #H
    iunfold txn.requestOpIs at H
    icases H with ⟨%Hn, %u, %w, %r, %o', #Hu, (⟨%Hx, -⟩ | ⟨%Hx, #Hw, #Hr⟩ | ⟨%Hx, -⟩)⟩
    · cases Hx.2
    · obtain ⟨rfl, Ho⟩ := Hx
      iexists (v3rpc.ReqOp.put o')
      isplitl
      · unfold v3rpc.reqOpIs; imodintro; isplitl; · ipureintro; exact Hn
        iexists w, r; iframe #
      · ipureintro; simp [v3rpc.ReqOp.toTxnOp, Ho]
    · cases Hx.2
  | putIgnVal k l =>
    iintro #H
    iunfold txn.requestOpIs at H
    icases H with ⟨%Hn, %u, %w, %r, %o', #Hu, (⟨%Hx, -⟩ | ⟨%Hx, #Hw, #Hr⟩ | ⟨%Hx, -⟩)⟩
    · cases Hx.2
    · obtain ⟨rfl, Ho⟩ := Hx
      iexists (v3rpc.ReqOp.put o')
      isplitl
      · unfold v3rpc.reqOpIs; imodintro; isplitl; · ipureintro; exact Hn
        iexists w, r; iframe #
      · ipureintro; simp [v3rpc.ReqOp.toTxnOp, Ho]
    · cases Hx.2

/-- **The plain operations of the server's copy are the handler's request operations** (in
order). -/
theorem reqOps_of_requestOps : ∀ (ps : List Loc) (ops : List TxnOp),
    (∀ op ∈ ops, TxnOp.plain op) →
    txn.requestOpsIs (GF := GF) ps ops ⊢
      ∃ us : List v3rpc.ReqOp, v3rpc.reqOpsIs ps us ∗ ⌜v3rpc.ReqOp.toTxnOps us = some ops⌝
  | [], [], _ => by
    iintro -
    iexists []
    unfold v3rpc.reqOpsIs
    isplitl; · itrivial
    ipureintro; rfl
  | p :: ps, op :: ops, hp => by
    iintro H
    iunfold txn.requestOpsIs at H
    icases H with ⟨H1, H2⟩
    ihave ⟨%u, H1, %Hu⟩ := reqOp_of_requestOp p op (hp op (List.mem_cons_self ..)) $$ H1
    ihave ⟨%us, H2, %Hus⟩ := reqOps_of_requestOps ps ops
      (fun o hm => hp o (List.mem_cons_of_mem _ hm)) $$ H2
    iexists u :: us
    rw [v3rpc.reqOpsIs.eq_2]
    iframe H1 H2
    ipureintro
    simp [v3rpc.ReqOp.toTxnOps, Hu, Hus]
  | [], _ :: _, _ => by iintro H; iunfold txn.requestOpsIs at H; iexfalso; iexact H
  | _ :: _, [], _ => by iintro H; iunfold txn.requestOpsIs at H; iexfalso; iexact H

/-- A request operation that is not a nested transaction. -/
def reqNotTxn : v3rpc.ReqOp → Prop
  | .txn _ _ _ => False
  | _ => True

theorem reqNotTxn_of_toTxnOps : ∀ (us : List v3rpc.ReqOp) (ops : List TxnOp),
    v3rpc.ReqOp.toTxnOps us = some ops → (∀ op ∈ ops, TxnOp.plain op) → ∀ u ∈ us, reqNotTxn u
  | [], _, _, _ => by simp
  | u :: us, ops, h, hp => by
    simp only [v3rpc.ReqOp.toTxnOps] at h
    split at h
    · rename_i t ts h1 h2
      simp only [Option.some.injEq] at h
      subst h
      have ih := reqNotTxn_of_toTxnOps us ts h2 (fun op hm => hp op (List.mem_cons_of_mem _ hm))
      intro u' hu'
      rcases List.mem_cons.mp hu' with rfl | hm
      · have ht := hp t (List.mem_cons_self ..)
        cases u' with
        | txn cs ts' es' =>
          simp only [v3rpc.ReqOp.toTxnOp] at h1
          split at h1 <;> simp at h1
          subst h1; exact ht.elim
        | _ => trivial
      · exact ih u' hm
    · cases h

/-- The deletes' range ends of the operations `ps` are `nil` or not empty (what `txnWireOk` says
of each branch). -/
def delWireAt (ps : List Loc) : IProp GF :=
  iprop(□ ∀ (i : Nat) (p w d : Loc) (esl : GoSlice), ⌜ps[i]? = some p⌝ -∗
      structFieldRef etcdserverpb.RequestOp go!"Request" p ↦□
        (interface.mkOk (go.GoType.PointerType etcdserverpb.RequestOp_RequestDeleteRange.ty) #w :
          GoInterface) -∗
      structFieldRef etcdserverpb.RequestOp_RequestDeleteRange go!"RequestDeleteRange" w ↦□ d -∗
      structFieldRef etcdserverpb.DeleteRangeRequest go!"RangeEnd" d ↦□ esl -∗
      ⌜esl = slice.nil ∨ esl.len ≠ W64 0⌝)

instance delWireAt_persistent (ps : List Loc) : Persistent (delWireAt (GF := GF) ps) := by
  unfold delWireAt; infer_instance

theorem reqOpsWire_of_delWireAt : ∀ (ps : List Loc) (us : List v3rpc.ReqOp),
    (∀ u ∈ us, reqNotTxn u) → delWireAt (GF := GF) ps ⊢ v3rpc.reqOpsWire ps us
  | [], [], _ => by iintro -; unfold v3rpc.reqOpsWire; itrivial
  | [], _ :: _, _ => by iintro -; unfold v3rpc.reqOpsWire; itrivial
  | _ :: _, [], _ => by iintro -; unfold v3rpc.reqOpsWire; itrivial
  | p :: ps, u :: us, hu => by
    iintro #H
    iunfold delWireAt at H
    have ih := reqOpsWire_of_delWireAt ps us (fun u' hm => hu u' (List.mem_cons_of_mem _ hm))
    rw [v3rpc.reqOpsWire.eq_2]
    isplitl
    · cases u with
      | delete o =>
        unfold v3rpc.reqOpWire
        iintro !> %w %d %esl #H1 #H2 #H3
        iapply H $$ %0 %p %w %d %esl %rfl H1 H2 H3
      | txn cs ts es => exact (hu _ (List.mem_cons_self ..)).elim
      | range o => unfold v3rpc.reqOpWire; itrivial
      | put o => unfold v3rpc.reqOpWire; itrivial
      | empty => unfold v3rpc.reqOpWire; itrivial
    · iapply ih
      unfold delWireAt
      iintro !> %i %q %w %d %esl %Hi #H1 #H2 #H3
      iapply H $$ %(i + 1) %q %w %d %esl %Hi H1 H2 H3

/-- **The transport's request is the gRPC handler's** (see the file header): the server's copy of
a transaction `t` of plain operations, as decoded (`txnRequestIs`, `txnWireOk`), is the handler's
request `txnReqIs r t.cmps ts es` with its wire facts, whose model is `t`. -/
theorem txnReq_of_requestIs (r : Loc) (t : TxnModel) (hp : TxnModel.plain t) :
    txn.txnRequestIs (GF := GF) r t ∗ txnWireOk r t ⊢
      ∃ ts es : List v3rpc.ReqOp, v3rpc.txnReqIs r t.cmps ts es ∗ v3rpc.txnReqWire r ts es ∗
        ⌜v3rpc.txnModelOf t.cmps ts es = some t⌝ := by
  iintro ⟨#Hreq, #Hw⟩
  iunfold txn.txnRequestIs at Hreq
  icases Hreq with ⟨%Hrn, Hreq⟩
  iunfold txn.txnFieldsIs at Hreq
  icases Hreq with ⟨%csl, %ssl, %fsl, %cps, %sps, %fps, #Hc, #Hcs, #Hcm, #Hs, #Hss, #Hsm,
    #Hf, #Hfs, #Hfm⟩
  ihave ⟨%ts, #Hts, %Hts'⟩ := reqOps_of_requestOps sps t.thenOps hp.1 $$ Hsm
  ihave ⟨%es, #Hes, %Hes'⟩ := reqOps_of_requestOps fps t.elseOps hp.2 $$ Hfm
  iexists ts, es
  iunfold txnWireOk at Hw
  icases Hw with ⟨%Hcnt, #Hw⟩
  isplitl
  · unfold v3rpc.txnReqIs
    isplitl; · ipureintro; exact Hrn
    iexists csl, ssl, fsl, cps, sps, fps
    iframe #
  isplitl
  · unfold v3rpc.txnReqWire
    isplitl
    · ipureintro
      rw [delCount_toTxnOps ts _ Hts' hp.1, delCount_toTxnOps es _ Hes' hp.2]
      exact Hcnt
    iintro !> %ssl' %fsl' %sps' %fps' #Hs' #Hss' #Hf' #Hfs'
    isplitl
    · iapply reqOpsWire_of_delWireAt sps' ts (reqNotTxn_of_toTxnOps ts _ Hts' hp.1)
      unfold delWireAt
      iintro !> %i %q %w %d %esl %Hi #H1 #H2 #H3
      iapply Hw $$ %ssl' %sps' %i %q %w %d %esl [] Hss' %Hi H1 H2 H3
      ileft; iexact Hs'
    · iapply reqOpsWire_of_delWireAt fps' es (reqNotTxn_of_toTxnOps es _ Hes' hp.2)
      unfold delWireAt
      iintro !> %i %q %w %d %esl %Hi #H1 #H2 #H3
      iapply Hw $$ %fsl' %fps' %i %q %w %d %esl [] Hfs' %Hi H1 H2 H3
      iright; iexact Hf'
  · ipureintro
    simp [v3rpc.txnModelOf, Hts', Hes']

end bridge

/-! ## The response's model -/

mutual
/-- **A response message of an operation answers it** (`skip`: ranges header-only): the
message `m` of the server's response of the operation `op` with result `res` (the txn package's
`responseOpIs`): a get's count and key-values (as the range model's: `rangeKvsOk`, the leases
zeroed by a fast keys-only read), or nothing if header-only; a put's; a delete's count; a nested
transaction's verdict and its branch's responses. The inner headers' revisions and a put's or
delete's previous key-values are unconstrained (the server's `responseOpIs` leaves them so). -/
def opRespRel (skip : Bool) : TxnOp → TxnOpResult → OpRespM → Prop
  | .get o, .range sel n, .range _ kvs more count =>
      if skip then kvs = [] ∧ more = false ∧ count = W64 0
      else count = W64 (n : Int) ∧
        ∃ kvs', rangeKvsOk o sel kvs' ∧ kvs = kvs'.map (txn.leaseZ (txn.fastKeysOnly o))
  | .put .., .put, .put _ _ => True
  | .putKeep .., .put, .put _ _ => True
  | .putIgnVal .., .put, .put _ _ => True
  | .delete _, .delete n, .delete _ d _ => d = W64 (n : Int)
  | .txn _ ts es, .txn ok rs, .txn _ ok' ms =>
      ok' = ok ∧ (if ok then opRespsRel skip ts rs ms else opRespsRel skip es rs ms)
  | _, _, _ => False

/-- `opRespRel` of each operation, in order. -/
def opRespsRel (skip : Bool) : List TxnOp → List TxnOpResult → List OpRespM → Prop
  | [], [], [] => True
  | op :: ops, res :: rs, m :: ms => opRespRel skip op res m ∧ opRespsRel skip ops rs ms
  | _, _, _ => False
end

section resp
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

mutual
/-- **The server's response of an operation is a response message that answers it**
(`opRespRel`). -/
theorem opResp_of_responseOp (skip : Bool) (p : Loc) (op : TxnOp) (res : TxnOpResult) :
    txn.responseOpIs (GF := GF) skip p op res ⊢
      ∃ m : OpRespM, opRespMsg p m ∗ ⌜opRespRel skip op res m⌝ := by
  match op, res with
  | .txn cs ts es, .txn ok rs =>
    rw [txn.responseOpIs.eq_1]
    iintro #H
    icases H with ⟨%Hn, %w, %r, #Hu0, #Hw, %Hrn, %h, %sl, %ps, #Hh, %Hhn, #Hrev, #Hok, #Hsl, #Hps,
      Hrs⟩
    cases ok with
    | true =>
      ihave ⟨%ms, #Hms, %Hrel⟩ := opResps_of_responseOps skip ps ts rs $$ Hrs
      iexists (OpRespM.txn (W64 0) true ms)
      isplitl
      · unfold opRespMsg
        isplitl; · ipureintro; exact Hn
        iexists w, r, h, sl, ps
        iframe #
        isplitl; · ipureintro; exact Hrn
        ipureintro; exact Hhn
      · ipureintro; simp only [opRespRel]; exact ⟨trivial, by simpa using Hrel⟩
    | false =>
      ihave ⟨%ms, #Hms, %Hrel⟩ := opResps_of_responseOps skip ps es rs $$ Hrs
      iexists (OpRespM.txn (W64 0) false ms)
      isplitl
      · unfold opRespMsg
        isplitl; · ipureintro; exact Hn
        iexists w, r, h, sl, ps
        iframe #
        isplitl; · ipureintro; exact Hrn
        ipureintro; exact Hhn
      · ipureintro; simp only [opRespRel]; exact ⟨trivial, by simpa using Hrel⟩
  | .txn cs ts es, .range .. | .txn cs ts es, .put | .txn cs ts es, .delete .. =>
    simp only [txn.responseOpIs]
    iintro #H
    icases H with ⟨%Hn, %u, %w, %r, -, Hf⟩
    iexfalso; iexact Hf
  | .get o, .range sel n =>
    cases skip with
    | true =>
      simp only [txn.responseOpIs, ↓reduceIte]
      iintro #H
      icases H with ⟨%Hn, %u, %w, %r, #Hu0, %Hu, #Hw, %rev, Hr⟩
      subst Hu
      iexists (OpRespM.range rev [] false (W64 0))
      isplitl
      · unfold opRespMsg
        isplitl; · ipureintro; exact Hn
        iexists w, r
        iframe #
      · ipureintro; simp [opRespRel]
    | false =>
      simp only [txn.responseOpIs, ↓reduceIte, Bool.false_eq_true]
      iintro #H
      icases H with ⟨%Hn, %u, %w, %r, #Hu0, %Hu, #Hw, %rev, Hr⟩
      subst Hu
      icases Hr with ⟨%kvs, %more, #Hrr, %Hk⟩
      iexists (OpRespM.range rev kvs more (W64 (n : Int)))
      isplitl
      · unfold opRespMsg
        isplitl; · ipureintro; exact Hn
        iexists w, r
        iframe #
      · ipureintro; simp only [opRespRel]; exact ⟨by simp, Hk⟩
  | .delete o, .delete n =>
    simp only [txn.responseOpIs]
    iintro #H
    icases H with ⟨%Hn, %u, %w, %r, #Hu0, %Hu, #Hw, %rev, %prevs, #Hrr⟩
    subst Hu
    iunfold txn.deleteRangeResponseIs at Hrr
    icases Hrr with ⟨%Hrn, %h, %sl, %ps, #Hh, %Hhn, #Hrev, #Hd, #Hsl, #Hps, #Hkvs⟩
    iexists (OpRespM.delete rev (W64 (n : Int)) prevs)
    isplitl
    · unfold opRespMsg
      isplitl; · ipureintro; exact Hn
      iexists w, r
      iframe #
      isplitl
      · ipureintro; exact Hrn
      · ipureintro; exact Hhn
    · ipureintro; simp [opRespRel]
  | .put k v l, .put | .putKeep k v, .put | .putIgnVal k l, .put =>
    simp only [txn.responseOpIs]
    iintro #H
    icases H with ⟨%Hn, %u, %w, %r, #Hu0, %Hu, #Hw, %rev, %prev, #Hrr⟩
    subst Hu
    iexists (OpRespM.put rev prev)
    isplitl
    · unfold opRespMsg
      isplitl; · ipureintro; exact Hn
      iexists w, r
      iframe #
    · ipureintro; simp [opRespRel]
  | .get _, .put | .get _, .delete _ | .get _, .txn .. | .delete _, .range .. | .delete _, .put
  | .delete _, .txn .. | .put .., .range .. | .put .., .delete _ | .put .., .txn ..
  | .putKeep .., .range .. | .putKeep .., .delete _ | .putKeep .., .txn ..
  | .putIgnVal .., .range .. | .putIgnVal .., .delete _ | .putIgnVal .., .txn .. =>
    simp only [txn.responseOpIs]
    iintro #H
    icases H with ⟨%Hn, %u, %w, %r, -, Hf⟩
    iexfalso; iexact Hf
termination_by sizeOf op

/-- **The server's responses are response messages that answer them** (in order). -/
theorem opResps_of_responseOps (skip : Bool) (ps : List Loc) (ops : List TxnOp)
    (rs : List TxnOpResult) :
    txn.responseOpsIs (GF := GF) skip ps ops rs ⊢
      ∃ ms : List OpRespM, opRespsMsg ps ms ∗ ⌜opRespsRel skip ops rs ms⌝ := by
  match ps, ops, rs with
  | [], [], [] =>
    iintro -
    iexists []
    unfold opRespsMsg
    isplitl; · itrivial
    ipureintro; simp [opRespsRel]
  | p :: ps, op :: ops, res :: rs =>
    iintro #H
    iunfold txn.responseOpsIs at H
    icases H with ⟨H1, H2⟩
    ihave ⟨%m, #H1, %Hm⟩ := opResp_of_responseOp skip p op res $$ H1
    ihave ⟨%ms, #H2, %Hms⟩ := opResps_of_responseOps skip ps ops rs $$ H2
    iexists m :: ms
    rw [opRespsMsg.eq_2]
    iframe #
    ipureintro
    simp only [opRespsRel]
    exact ⟨Hm, Hms⟩
  | [], [], _ :: _ | [], _ :: _, _ | _ :: _, [], _ | _ :: _, _ :: _, [] =>
    iintro H; iunfold txn.responseOpsIs at H; iexfalso; iexact H
termination_by sizeOf ops
end

end resp

/-! ## What a transaction's reply tells the client -/

/-- **A transaction within the txn package's model** (`v3rpc.txnInModel` of the model; a
premise): if read-only, each of its gets reads the transaction's revision and is not a sort cut
early by a limit (`txn.cutEarly`, `issues/etcd-range-sort-none-limit.md`). -/
def txnModelIn (t : TxnModel) : Prop :=
  txn.txnReadonly t = true →
    ∀ o : OpFull, TxnOp.get o ∈ t.thenOps ++ t.elseOps → o.base.rev = W64 0 ∧ ¬ txn.cutEarly o

theorem txnInModel_of (t : TxnModel) (cs : List CmpModel) (ts es : List v3rpc.ReqOp)
    (h : txnModelIn t) (hm : v3rpc.txnModelOf cs ts es = some t) : v3rpc.txnInModel cs ts es := by
  intro t' ht'
  rw [hm] at ht'
  cases ht'
  exact h

theorem txnWireOf_plain (t : TxnModel) (h : TxnModel.plain t) : TxnModel.plain (txnWireOf t) := by
  refine ⟨?_, ?_⟩
  · intro op hm
    simp only [txnWireOf, List.mem_map] at hm
    obtain ⟨op0, h0, rfl⟩ := hm
    exact opWire_plain op0 (h.1 op0 h0)
  · intro op hm
    simp only [txnWireOf, List.mem_map] at hm
    obtain ⟨op0, h0, rfl⟩ := hm
    exact opWire_plain op0 (h.2 op0 h0)

section reply
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **What a successful `Txn` of `t` delivers to the client** with the reply's message `m`, for a
client that knows the committed index `c` and has the floor `F` (the vertical slice's unit V2).
A read-only `t`: the server's run of `t` at a certified log extending `F`, after the read index
unless serializable (`readLogOk`), the header's revision its last; the verdict and the chosen
branch's responses the run's (`opRespsRel`). A writing `t`: the apply thread's application of
the request the proposed data decode to (`rq'`, whose transaction `t'` is `t` unless a range end
is `[0]`), at `x.log` extending `F`, the header's revision the write's; the verdict and the
responses the run's (ranges header-only if `skip`); mvcc's certificate of the log after and the
token minted (`revMinted`, exclusive: a reply's `Φ` is delivered once), with the write's witness
(`appliedWit γw`, unit C2a, at the request path's read names). -/
def txnReplied (E : apply.AEnv GF) (γw γr : ReadNames) (c : w64) (F : mvcc.Log) (t : TxnModel)
    (cid mid : w64) (m : TxnRespM) : IProp GF :=
  if txn.txnReadonly t then
    iprop(∃ log : mvcc.Log, mvcc.idxCert E.γ.idx log ∗
      ⌜2 ≤ log.length ∧ log.length + 3 ≤ 2 ^ 63 ∧ F <+: log ∧
        m.hdr.revision = W64 ((log.length : Int) - 1) ∧ m.hdr.clusterId = cid ∧
        m.hdr.memberId = mid ∧
        m.succeeded = (txn.srvRunTxn (W64 (log.length : Int)) (mvcc.stateAfter log) t).1 ∧
        opRespsRel false (t.branch m.succeeded)
          (txn.srvRunTxn (W64 (log.length : Int)) (mvcc.stateAfter log) t).2.2 m.resps⌝ ∗
      (if txn.txnSerializable t then iprop(True) else readLogOk γr c log))
  else
    iprop(∃ (hm : apply.HeaderModel) (rq' : apply.IRRModel) (t' : TxnModel)
        (x x' : apply.ApplyKV) (l : mvcc.Log) (skip : Bool),
      ⌜irrWireOf (apply.withHeader (irrTxn t) hm) rq' ∧ rq'.txn = some t' ∧
        (irrNoZeroEnd (irrTxn t) → t' = t) ∧
        apply.applyStep rq' true x x' (.dispatched (.applied l false) skip) ∧
        m.hdr.revision = W64 (mvcc.writeRev x.log
          (txn.srvRunTxn (W64 (x.log.length : Int)) (mvcc.stateAfter x.log) t').2.1 : Int) ∧
        m.hdr.clusterId = cid ∧ m.hdr.memberId = mid ∧
        F <+: x.log ∧ 2 ≤ x.log.length ∧ x.log.length + 4 ≤ 2 ^ 63 ∧
        m.succeeded = (txn.srvRunTxn (W64 (x.log.length : Int)) (mvcc.stateAfter x.log) t').1 ∧
        opRespsRel skip (t'.branch m.succeeded)
          (txn.srvRunTxn (W64 (x.log.length : Int)) (mvcc.stateAfter x.log) t').2.2 m.resps⌝ ∗
      mvcc.idxCert E.γ.idx x'.log ∗ revMinted E x.log x'.log ∗ appliedWit γw x'.log)

/-- **etcd's spec of the KV service's `Txn`** (the vertical slice's unit V2; a predicate
transformer, as `etcdPutSpec`): a caller asking a transaction `t` of plain operations (no nested
transaction: what the client's builder sends) within the txn package's model (`txnModelIn`: if
read-only, gets at the transaction's revision, no sort cut early by a limit), who knows the
committed index `c` and has the floor `F`, gets a reply message `m` with `txnReplied`. A writing
transaction (2026-10-15, unit T2) is plain in the KV model (`txn.txnPlain`: its gets at revision
`0`, its puts with no lease and no `IgnoreLease`), no range end `[0]` (`txnNoZeroEnd`), with the
caller's persistent update over the whole state `kvOpAu (.txn t) Q`, whose `□ Q` of the state it
linearized at the reply carries; a read-only one takes none (`Q` trivial). -/
def etcdTxnSpec (E : apply.AEnv GF) (γw γr : ReadNames) (cid mid : w64) :
    GrpcSpec (GF := GF) pbTxnRequest pbTxnResponse :=
  fun (t : TxnModel) (Φ : TxnRespM → IProp GF) =>
    iprop(⌜TxnModel.plain t ∧ txnModelIn t⌝ ∗ ∃ Q : KVState → IProp GF,
      (⌜txn.txnReadonly t = true ∧ Q = fun _ => iprop(True)⌝ ∨
        (⌜txn.txnReadonly t = false ∧ txn.txnPlain t ∧ txnNoZeroEnd t⌝ ∗
          kvOpAu γw.kv (.txn t) Q)) ∗
      ∃ (c : w64) (F : mvcc.Log), committedAtLeast γr c ∗
      mvcc.idxCert E.γ.idx F ∗
      ∀ m : TxnRespM, txnReplied E γw γr c F t cid mid m ∗ (∃ σ, □ Q σ) -∗ Φ m)

end reply

section proofs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- **The server's `TxnResponse` is a message** (`txnRespMsg`) whose verdict and responses are
the run's: from the txn package's `txnResponseIs` and the handler's filled header. -/
theorem txnRespMsg_of_server (skip : Bool) (resp h : Loc) (rev : w64) (t : TxnModel) (ok : Bool)
    (rs : List TxnOpResult) (cid mid : w64) :
    structFieldRef etcdserverpb.TxnResponse go!"Header" resp ↦□ h ∗ v3rpc.hdrFilled h cid mid ∗
      txn.txnResponseIs (GF := GF) skip resp rev t ok rs ⊢ |==>
    ∃ m : TxnRespM, txnRespMsg resp m ∗
      ⌜m.hdr.revision = rev ∧ m.hdr.clusterId = cid ∧ m.hdr.memberId = mid ∧ m.succeeded = ok ∧
        opRespsRel skip (t.branch ok) rs m.resps⌝ := by
  iintro ⟨#Hh, Hf, #Hres⟩
  iunfold txn.txnResponseIs at Hres
  icases Hres with ⟨%Hrn, Hres⟩
  iunfold txn.txnRespFieldsIs at Hres
  icases Hres with ⟨%h2, #Hh2, %Hh2n, #Hrev, #Hok, Hrs⟩
  iunfold txn.respsIs at Hrs
  icases Hrs with ⟨%sl, %ps, #Hsl, #Hps, Hrs⟩
  ihave ⟨%ms, #Hms, %Hrel⟩ := opResps_of_responseOps skip ps (t.branch ok) rs $$ Hrs
  icombine Hh Hh2 gives %Heq
  subst Heq
  iunfold v3rpc.hdrFilled at Hf
  icases Hf with ⟨-, %tm, %ld, Hcid, Hmid, Ht, Hl⟩
  ipersist Hcid
  ipersist Hmid
  ipersist Ht
  ipersist Hl
  imodintro
  iexists (TxnRespM.mk (HdrM.mk cid mid rev tm ld) ok ms)
  isplitl
  · unfold txnRespMsg hdrFull
    isplitl; · ipureintro; exact Hrn
    iexists h, sl, ps
    iframe #
    ipureintro; exact Hh2n
  · ipureintro; exact ⟨rfl, rfl, rfl, rfl, Hrel⟩

end proofs

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **A run's slot** (see the file header): the reader slots a run of etcd's KV handlers holds
and gives back: `s.leadTimeMu`'s (`srvCall`'s), the store's, the logger's, the read loop's and the
auth store's reader resource (`E.RD`, 2026-10-14, unit A2; `srvRdCall`'s). The server hands the
gRPC runtime a number of them when it serves (bounded `RWMutex` slots: at most that many runs at
a time). -/
def etcdRunSlot (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) : IProp GF :=
  iprop(srvLeadTimeReader s ∗ mvcc.storeReader E.s E.γ ∗ srvLgReader s ∗ srvReadReader s γr ∗
    E.RD)

/-- **What a successful `Put` of `o` tells the client** about the reply's message `m` (persistent;
see the file header): since 2026-10-14 (unit C2a) with the witness that the log after is applied
through an index of the committed log at the read names `γr` (`appliedWit`: a linearizable read
at that index reads a log extending it, `client_get_after_put`). -/
def putReplyOk (E : apply.AEnv GF) (γr : ReadNames) (F : mvcc.Log) (o : OpFull) (cid mid : w64)
    (m : PutRespM) : IProp GF :=
  iprop(∃ (hm : apply.HeaderModel) (x x' : apply.ApplyKV) (l : mvcc.Log) (skip : Bool),
    ⌜apply.applyStep (apply.withHeader (irrPut o) hm) true x x'
        (.dispatched (.applied l false) skip) ∧
      m.hdr.revision = W64 (x.log.length : Int) ∧ m.hdr.clusterId = cid ∧ m.hdr.memberId = mid ∧
      m.prev = (if o.base.prevKV then mvcc.findKey o.key (mvcc.stateAfter x.log) else none) ∧
      F <+: x.log ∧ 2 ≤ x.log.length ∧ x.log.length + 4 ≤ 2 ^ 63⌝ ∗
    mvcc.idxCert E.γ.idx x'.log ∗ appliedWit γr x'.log)

instance putReplyOk_persistent (E : apply.AEnv GF) (γr : ReadNames) (F : mvcc.Log) (o : OpFull)
    (cid mid : w64) (m : PutRespM) : Persistent (putReplyOk E γr F o cid mid m) := by
  unfold putReplyOk; infer_instance

/-- **What a successful `Get` of `o` tells the client** about the reply's message `m`
(persistent; see the file header); 2026-10-14 (unit T1): a linearizable get's result `□ Q` at the
log read (its update, deposited with the read index, fired there; 2026-10-15, unit T2: at the
whole state of the log read, `kvStateOf`); the log read extends the caller's floor `F` (the
vertical slice's unit V2). -/
def rangeReplyOk (E : apply.AEnv GF) (γr : ReadNames) (c : w64) (F : mvcc.Log) (o : OpFull)
    (cid mid : w64) (Q : KVState → IProp GF) (m : RangeRespM) : IProp GF :=
  iprop(∃ log : mvcc.Log, mvcc.idxCert E.γ.idx log ∗
    ⌜2 ≤ log.length ∧ log.length + 3 ≤ 2 ^ 63 ∧
      m.hdr.revision = W64 ((log.length : Int) - 1) ∧ m.hdr.clusterId = cid ∧
      m.hdr.memberId = mid ∧ sint.Z o.base.rev ≤ sint.Z m.hdr.revision ∧
      m.count = txn.srvCount o
        (mvcc.stateAt log (sint.nat (mvcc.rangeRev m.hdr.revision o.base.rev))) true ∧
      txn.srvRangeOk o (mvcc.stateAt log (sint.nat (mvcc.rangeRev m.hdr.revision o.base.rev)))
        m.kvs m.more ∧ F <+: log⌝ ∗
    (if o.base.serializable then iprop(True) else readLogOk γr c log) ∗
    (if o.base.serializable then iprop(True) else □ Q (kvStateOf log)))

instance rangeReplyOk_persistent (E : apply.AEnv GF) (γr : ReadNames) (c : w64) (F : mvcc.Log)
    (o : OpFull) (cid mid : w64) (Q : KVState → IProp GF) (m : RangeRespM) :
    Persistent (rangeReplyOk E γr c F o cid mid Q m) := by
  unfold rangeReplyOk; split <;> infer_instance

/-- **What a successful `Put` of `o` delivers to the client** with the reply's message `m`
(the merge of the generic gRPC specification with the slice's unit V1, 2026-10-14): `putReplyOk`'s
knowledge (with its witness at the read names `γr`, unit C2a) and the token of the revision the
put made (`revMinted`, exclusive: a reply's `Φ` is delivered once, so the generic spec carries it;
`putReplied_ok` drops it). -/
def putReplied (E : apply.AEnv GF) (γr : ReadNames) (F : mvcc.Log) (o : OpFull) (cid mid : w64)
    (m : PutRespM) : IProp GF :=
  iprop(∃ (hm : apply.HeaderModel) (x x' : apply.ApplyKV) (l : mvcc.Log) (skip : Bool),
    ⌜apply.applyStep (apply.withHeader (irrPut o) hm) true x x'
        (.dispatched (.applied l false) skip) ∧
      m.hdr.revision = W64 (x.log.length : Int) ∧ m.hdr.clusterId = cid ∧ m.hdr.memberId = mid ∧
      m.prev = (if o.base.prevKV then mvcc.findKey o.key (mvcc.stateAfter x.log) else none) ∧
      F <+: x.log ∧ 2 ≤ x.log.length ∧ x.log.length + 4 ≤ 2 ^ 63⌝ ∗
    mvcc.idxCert E.γ.idx x'.log ∗ revMinted E x.log x'.log ∗ appliedWit γr x'.log)

open Iris.ProofMode in
/-- The knowledge of a delivered put (its token dropped; the witness kept). -/
theorem putReplied_ok (E : apply.AEnv GF) (γr : ReadNames) (F : mvcc.Log) (o : OpFull)
    (cid mid : w64) (m : PutRespM) : putReplied E γr F o cid mid m ⊢ putReplyOk E γr F o cid mid m := by
  iintro H
  unfold putReplied putReplyOk
  icases H with ⟨%hm, %x, %x', %l, %skip, %Hp, #Hc, -, #Hw⟩
  iexists hm, x, x', l, skip
  iframe Hc Hw
  ipureintro; exact Hp

/-- **etcd's spec of the KV service's `Put`** (a predicate transformer; see the file header): a
caller asking the put `o` gets a reply message `m` with `putReplied` (`putReplyOk`, with its
witness at the read names `γr` (2026-10-14, unit C2a), and the revision's token), at a log
extending the caller's floor `F` (the vertical slice's unit V2); since 2026-10-15 (unit T2) a put
with no lease (any other flags) with the caller's persistent update over the whole state
`kvOpAu (.put o) Q`, whose `□ Q` of the state it linearized at the reply carries. -/
def etcdPutSpec (E : apply.AEnv GF) (γr : ReadNames) (cid mid : w64) :
    GrpcSpec (GF := GF) pbPutRequest pbPutResponse :=
  fun (o : OpFull) (Φ : PutRespM → IProp GF) =>
    iprop(∃ F : mvcc.Log, mvcc.idxCert E.γ.idx F ∗
      ∃ Q : KVState → IProp GF, ⌜o.leaseID = W64 0⌝ ∗ kvOpAu γr.kv (.put o) Q ∗
          ∀ m : PutRespM, putReplied E γr F o cid mid m ∗ (∃ σ, □ Q σ) -∗ Φ m)


/-- **etcd's spec of the KV service's `Range`**: a caller that knows the committed index `c`
(`committedAtLeast γr c`; `0` is free) asking the range `o` gets a reply message `m` with
`rangeReplyOk` at `c`; since 2026-10-14 (unit T1) with the caller's persistent read update
(`kvReadAu`, over the whole state since 2026-10-15, unit T2: a linearizable range), or none (`Q`
trivial). -/
def etcdRangeSpec (E : apply.AEnv GF) (γr : ReadNames) (cid mid : w64) :
    GrpcSpec (GF := GF) pbRangeRequest pbRangeResponse :=
  fun (o : OpFull) (Φ : RangeRespM → IProp GF) =>
    iprop(∃ (c : w64) (F : mvcc.Log) (Q : KVState → IProp GF), committedAtLeast γr c ∗
      mvcc.idxCert E.γ.idx F ∗
      (⌜Q = fun _ => iprop(True)⌝ ∨ (⌜o.base.serializable = false⌝ ∗ kvReadAu γr.kv Q)) ∗
      ∀ m : RangeRespM, rangeReplyOk E γr c F o cid mid Q m -∗ Φ m)

/-- **What a successful `DeleteRange` of `o` tells the client** about the reply's message `m`
(persistent): the apply thread's application of the delete `op'` the proposed data decode to
(`o` itself unless a range end is empty, `deleteRange_end_to_end`'s `deleteAppliedOk`), at the log
the entry met, the reply's header revision the delete's write revision, its ids the cluster's and
member's, `Deleted` the number of keys in the range, `PrevKvs` their key-values if asked;
mvcc's certificate of the log after. -/
def deleteReplyOk (E : apply.AEnv GF) (γr : ReadNames) (F : mvcc.Log) (o : OpFull) (cid mid : w64)
    (m : DelRespM) : IProp GF :=
  iprop(∃ (hm : apply.HeaderModel) (rq' : apply.IRRModel) (op' : OpFull) (x x' : apply.ApplyKV)
      (l : mvcc.Log) (skip : Bool),
    ⌜irrWireOf (apply.withHeader (irrDeleteRange o) hm) rq' ∧ rq'.deleteRange = some op' ∧
      (irrNoZeroEnd (irrDeleteRange o) → op' = o) ∧
      apply.applyStep rq' true x x' (.dispatched (.applied l false) skip) ∧
      m.hdr.revision =
        W64 ((mvcc.writeRev x.log (txn.delChanges (mvcc.stateAfter x.log) op') : Nat) : Int) ∧
      m.hdr.clusterId = cid ∧ m.hdr.memberId = mid ∧
      m.deleted = W64 ((rangeIn (mvcc.stateAfter x.log) op').length : Int) ∧
      m.prevs = (if op'.base.prevKV then rangeIn (mvcc.stateAfter x.log) op' else []) ∧
      F <+: x.log ∧ 2 ≤ x.log.length ∧ x.log.length + 4 ≤ 2 ^ 63⌝ ∗
    mvcc.idxCert E.γ.idx x'.log ∗ appliedWit γr x'.log)

instance deleteReplyOk_persistent (E : apply.AEnv GF) (γr : ReadNames) (F : mvcc.Log) (o : OpFull)
    (cid mid : w64) (m : DelRespM) : Persistent (deleteReplyOk E γr F o cid mid m) := by
  unfold deleteReplyOk; infer_instance

/-- **What a successful `DeleteRange` of `o` delivers to the client** (as `putReplied`):
`deleteReplyOk`'s knowledge and the revision's token (`revMinted`; none minted if nothing was
deleted). -/
def deleteReplied (E : apply.AEnv GF) (γr : ReadNames) (F : mvcc.Log) (o : OpFull) (cid mid : w64)
    (m : DelRespM) : IProp GF :=
  iprop(∃ (hm : apply.HeaderModel) (rq' : apply.IRRModel) (op' : OpFull) (x x' : apply.ApplyKV)
      (l : mvcc.Log) (skip : Bool),
    ⌜irrWireOf (apply.withHeader (irrDeleteRange o) hm) rq' ∧ rq'.deleteRange = some op' ∧
      (irrNoZeroEnd (irrDeleteRange o) → op' = o) ∧
      apply.applyStep rq' true x x' (.dispatched (.applied l false) skip) ∧
      m.hdr.revision =
        W64 ((mvcc.writeRev x.log (txn.delChanges (mvcc.stateAfter x.log) op') : Nat) : Int) ∧
      m.hdr.clusterId = cid ∧ m.hdr.memberId = mid ∧
      m.deleted = W64 ((rangeIn (mvcc.stateAfter x.log) op').length : Int) ∧
      m.prevs = (if op'.base.prevKV then rangeIn (mvcc.stateAfter x.log) op' else []) ∧
      F <+: x.log ∧ 2 ≤ x.log.length ∧ x.log.length + 4 ≤ 2 ^ 63⌝ ∗
    mvcc.idxCert E.γ.idx x'.log ∗ revMinted E x.log x'.log ∗ appliedWit γr x'.log)

open Iris.ProofMode in
/-- The knowledge of a delivered delete (its token dropped). -/
theorem deleteReplied_ok (E : apply.AEnv GF) (γr : ReadNames) (F : mvcc.Log) (o : OpFull)
    (cid mid : w64) (m : DelRespM) : deleteReplied E γr F o cid mid m ⊢ deleteReplyOk E γr F o cid mid m := by
  iintro H
  unfold deleteReplied deleteReplyOk
  icases H with ⟨%hm, %rq', %op', %x, %x', %l, %skip, %Hp, #Hc, -, #Hw⟩
  iexists hm, rq', op', x, x', l, skip
  iframe Hc Hw
  ipureintro; exact Hp

/-- **etcd's spec of the KV service's `DeleteRange`**: a caller asking the delete `o` gets a
reply message `m` with `deleteReplied` (`deleteReplyOk` and the revision's token); since
2026-10-15 (unit T2) a delete whose range end is not `[0]` (the wire keeps it), with the caller's
persistent update over the whole state `kvOpAu (.deleteRange o) Q`, whose `□ Q` of the state it
linearized at the reply carries. -/
def etcdDeleteSpec (E : apply.AEnv GF) (γr : ReadNames) (cid mid : w64) :
    GrpcSpec (GF := GF) pbDeleteRangeRequest pbDeleteRangeResponse :=
  fun (o : OpFull) (Φ : DelRespM → IProp GF) =>
    iprop(∃ F : mvcc.Log, mvcc.idxCert E.γ.idx F ∗
      ∃ Q : KVState → IProp GF, ⌜o.base.rangeEnd ≠ [W8 0]⌝ ∗ kvOpAu γr.kv (.deleteRange o) Q ∗
      ∀ m : DelRespM, deleteReplied E γr F o cid mid m ∗ (∃ σ, □ Q σ) -∗ Φ m)

/-- **etcd's KV methods** as registered (unit P3b): `Put`, `Range` and `DeleteRange`, the generated
handlers of `KV_ServiceDesc` (`rpc_grpc.pb.go`) with the service value `RegisterKVServer` is
given (`v3rpc.Server`: `NewQuotaKVServer(s)`, the `*quotaKVServer` `q`), with etcd's specs (the
`Put`'s witness at the request path's read names `γw`, 2026-10-14, unit C2a). -/
def etcdKVMethods (q : Loc) (E : apply.AEnv GF) (γw γr : ReadNames) (cid mid : w64) :
    List (GrpcMethod GF) :=
  [⟨go!"/etcdserverpb.KV/Put", pbPutRequest, pbPutResponse, etcdPutSpec E γw cid mid,
     (@! etcdserverpb._KV_Put_Handler),
     interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaKVServer.ty) #q⟩,
   ⟨go!"/etcdserverpb.KV/Range", pbRangeRequest, pbRangeResponse, etcdRangeSpec E γr cid mid,
     (@! etcdserverpb._KV_Range_Handler),
     interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaKVServer.ty) #q⟩,
   ⟨go!"/etcdserverpb.KV/DeleteRange", pbDeleteRangeRequest, pbDeleteRangeResponse,
     etcdDeleteSpec E γw cid mid, (@! etcdserverpb._KV_DeleteRange_Handler),
     interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaKVServer.ty) #q⟩,
   ⟨go!"/etcdserverpb.KV/Txn", pbTxnRequest, pbTxnResponse,
     etcdTxnSpec E γw γr cid mid, (@! etcdserverpb._KV_Txn_Handler),
     interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaKVServer.ty) #q⟩]

/-- **What `RegisterKVServer(gs, q)` registers of the KV service's unary methods we specify**
(the `ServiceDesc`'s `MethodDesc`s under `"/etcdserverpb.KV/"`, with the service value). -/
def etcdKVRegs (q : Loc) : List (GoString × val × GoInterface) :=
  [(go!"/etcdserverpb.KV/Put", (@! etcdserverpb._KV_Put_Handler),
     interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaKVServer.ty) #q),
   (go!"/etcdserverpb.KV/Range", (@! etcdserverpb._KV_Range_Handler),
     interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaKVServer.ty) #q),
   (go!"/etcdserverpb.KV/DeleteRange", (@! etcdserverpb._KV_DeleteRange_Handler),
     interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaKVServer.ty) #q),
   (go!"/etcdserverpb.KV/Txn", (@! etcdserverpb._KV_Txn_Handler),
     interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaKVServer.ty) #q)]

/-- **The interceptors' per-run resources** (`v3rpc.Server`'s chain: `newLogUnaryInterceptor`'s
reader slot of `s.lgMu`, the metrics interceptor's and `newUnaryInterceptor`'s none). -/
def etcdIcRs (s : Loc) : List (IProp GF) := [srvLgReader s, iprop(True), iprop(True)]

/-- **A run's slot, as grpc's runtime holds it** (unit P3b): the handlers' (`etcdRunSlot`), the
quota wrapper's reader slot of `s.leadTimeMu` and auth reader resource `E.RD` (its NOSPACE alarm's
`raftRequest`; `E.RD` since unit A2), and the interceptors' (`etcdIcRs`). -/
def etcdGrpcSlot (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) : IProp GF :=
  iprop((etcdRunSlot s E γr ∗ srvLeadTimeReader s ∗ E.RD) ∗ [∗list] R ∈ etcdIcRs s, R)

end defs

end v3rpc
end EtcdGrove
end Perennial

/-
**A client of several members** (2026-10-21, `notes/client-cut-plan.md` K4, `notes/decisions.md`
D27). Lean-first (no Rocq counterpart).

A client configured with several members' endpoints (`clientCfgOk cfg eps`) sends each attempt to
one of them, grpc's balancer's choice: a call needs its method registered at every endpoint with
one spec (`isGrpcRpcs`). Each member registers etcd's spec at its own apply environment, read
names and ids (`SrvAt`: `etcd_kv_started`'s), so a call through the client passes **the
conjunction of the members' specs** (`anySpec`): the caller proves each conjunct from the same
resources, and the member whose handler runs uses its own (`isGrpcRpcs_anySpec`, from
`isGrpcRpc_mono`). The reply is that member's: the results below say "some member `x` of `ms`".

The write results are for a write sent at most once (`writeOnce`): a client configured for one
attempt (`kvOnce`, D21 M6), or (2026-10-21, D29) a client of refusal-free members, whose retry
interceptor never sends a write again (`noRefusalAt`). Either way an update fired at most once, by
the one member the attempt reached. One member (`ms = [x]`) is the `client_*_end_to_end`
results' case.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.Results

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace client

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver

/-- **A member as its client sees it**: its client address and what etcd's specs it registers
there are at (`etcd_kv_started`'s): its apply environment, read names, cluster and member ids. -/
structure SrvAt (GF : BundledGFunctors) [FfiSyntax] where
  addr : GoString
  E : apply.AEnv GF
  γr : ReadNames
  cid : w64
  mid : w64

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The conjunction of the members' specs** (see the file header). -/
def anySpec {Req Rep : ProtoMsg GF} {α : Type _} (ms : List α) (S : α → GrpcSpec Req Rep) :
    GrpcSpec Req Rep :=
  fun m Φ => iprop([∧list] x ∈ ms, S x m Φ)

/-- Each member registering its own spec registers, at every member's address, the conjunction. -/
theorem isGrpcRpcs_anySpec {Req Rep : ProtoMsg GF} {α : Type _} (ms : List α) (addr : α → GoString)
    (name : GoString) (S : α → GrpcSpec Req Rep) :
    ([∗list] x ∈ ms, isGrpcRpc (addr x) name (S x)) ⊢
      isGrpcRpcs (ms.map addr) name (anySpec ms S) := by
  refine .trans ?_ (isGrpcRpcs_of_all (ms.map addr) name (anySpec ms S))
  rw [BigSepL.bigSepL_map]
  refine BigSepL.bigSepL_mono fun {k x} hk => ?_
  have hx : x ∈ ms := List.mem_of_getElem? hk
  exact isGrpcRpc_mono (addr x) name (S x) (anySpec ms S) fun m Φ => by
    unfold anySpec; exact BigAndL.bigAndL_mem (Φ := fun y => S y m Φ) hx

/-- **Proving the conjunction**: each member's conjunct from its persistent facts `C x` and its
share `R x` of the caller's resources (`∧`: the same resources serve every conjunct). -/
theorem anySpec_intro {Req Rep : ProtoMsg GF} {α : Type _} (ms : List α) (S : α → GrpcSpec Req Rep)
    (m : Req.M) (Φ : Rep.M → IProp GF) (C R : α → IProp GF) [∀ x, Persistent (C x)]
    (h : ∀ x, x ∈ ms → C x ∗ R x ⊢ S x m Φ) :
    ([∗list] x ∈ ms, C x) ∗ ([∧list] x ∈ ms, R x) ⊢ anySpec ms S m Φ := by
  unfold anySpec
  refine BigAndL.bigAndL_intro fun k x hk => ?_
  have hx : x ∈ ms := List.mem_of_getElem? hk
  iintro ⟨#HC, HR⟩
  iapply (h x hx)
  isplitl []
  · iapply (BigSepL.bigSepL_mem (Φ := C) hx) $$ HC
  · iapply (BigAndL.bigAndL_mem (Φ := R) hx) $$ HR

/-- **A conjunct per member from shared resources** `R` and each member's persistent facts
`C x` (`∧`: `R` serves every conjunct). -/
theorem bigAndL_of_sep {α : Type _} (ms : List α) (R : IProp GF) (C Φ : α → IProp GF)
    [∀ x, Persistent (C x)] (h : ∀ x, x ∈ ms → R ∗ C x ⊢ Φ x) :
    R ∗ ([∗list] x ∈ ms, C x) ⊢ [∧list] x ∈ ms, Φ x := by
  refine BigAndL.bigAndL_intro fun k x hk => ?_
  have hx : x ∈ ms := List.mem_of_getElem? hk
  iintro ⟨HR, #HC⟩
  iapply (h x hx)
  iframe HR
  iapply (BigSepL.bigSepL_mem (Φ := C) hx) $$ HC

end defs

/-! ## The calls -/

section e2e
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **A write through the `*kv` `api` sent at most once** (persistent; D21 M6, D29): a client
configured for one attempt, or a client of refusal-free members (any retry bound). -/
def writeOnce (api : Loc) (addrs : List GoString) : IProp GF :=
  iprop(kvOnce api addrs ∨ ⌜∀ a ∈ addrs, noRefusalAt a⌝)

instance writeOnce_persistent (api : Loc) (addrs : List GoString) :
    Persistent (writeOnce (GF := GF) api addrs) := by
  unfold writeOnce; infer_instance

/-- **A transaction through the `*txn` `tp` sent at most once** (D21 M6, D29): `writeOnce` of the
`*kv` it was made from, or refusal-free members. -/
def txnWriteOnce (tp : Loc) (addrs : List GoString) : IProp GF :=
  iprop((∃ api : Loc, txnKvIs tp api ∗ kvOnce api addrs) ∨ ⌜∀ a ∈ addrs, noRefusalAt a⌝)

/-- **etcd's KV registrations at a member** (persistent): etcd's `Put`, `Range`, `DeleteRange` and `Txn` at its address, at its apply environment, read names
and ids (`etcd_kv_started`'s). -/
def kvRegsAt (x : SrvAt GF) : IProp GF :=
  iprop(isGrpcRpc x.addr go!"/etcdserverpb.KV/Put" (etcdPutSpec x.E x.γr x.cid x.mid) ∗
    isGrpcRpc x.addr go!"/etcdserverpb.KV/Range" (etcdRangeSpec x.E x.γr x.cid x.mid) ∗
    isGrpcRpc x.addr go!"/etcdserverpb.KV/DeleteRange"
      (etcdDeleteSpec x.E x.γr x.cid x.mid) ∗
    isGrpcRpc x.addr go!"/etcdserverpb.KV/Txn" (etcdTxnSpec x.E x.γr x.γr x.cid x.mid))

instance kvRegsAt_persistent (x : SrvAt GF) : Persistent (kvRegsAt x) := by
  unfold kvRegsAt; infer_instance

/-- **`kv.Put(ctx, key, val)` through a client of the members `ms`** (`client_put_end_to_end`'s
one-attempt case, failover): each member's `Put` registered at its address, the members' floors
`[]` and their updates, one per member (`[∧ list]`: only the member the attempt reaches fires
its own); `nil` and the reply with `putReplied` of some member, or an error. -/
theorem client_put_any (api : Loc) (ms : List (SrvAt GF)) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (key val : GoString) (sl : GoSlice)
    (Q : KVState → IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
        kvObjAt api (ms.map SrvAt.addr) ∗ writeOnce api (ms.map SrvAt.addr) ∗
        ([∗list] x ∈ ms, isGrpcRpc x.addr go!"/etcdserverpb.KV/Put"
          (etcdPutSpec x.E x.γr x.cid x.mid)) ∗
        ([∗list] x ∈ ms, mvcc.idxCert x.E.γ.idx []) ∗
        ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAt sl [] ∗
        ([∧list] x ∈ ms, kvOpAu1 x.γr.kv (.put (putKeyOp key val)) Q) }}
      (App (App (App (App (Val (api @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!!
          go!"Put")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #val)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        (⌜err = GoInterface.nil⌝ ∗ ∃ m : PutRespM, putRespMsg resp m ∗ ∃ x : SrvAt GF, ⌜x ∈ ms⌝ ∗
            putReplied x.E x.γr [] (txn.putOpOf key val (W64 0) false false false) Q x.cid x.mid m) ∨
          ⌜err ≠ GoInterface.nil ∧ resp = null⌝ }} := by
  iintro %Φ ⟨#Pc, #Hkv, #Ho, #Hregs, #HF, #Hctx', #Hce, #Hopts, Hau⟩ HΦ
  have Hw : putWireOf (opPutModel key val []) =
      txn.putOpOf key val (W64 0) false false false := rfl
  have Hpm : ¬ (opPutModel key val []).putPanics ∧ (opPutModel key val []).t = W64 2 := by
    refine ⟨?_, rfl⟩
    unfold opPutModel OpFull.putPanics opFold OpFull.putInit OpFull.newOp OpModel.zero
    simp
  have hs : ([∗list] x ∈ ms, mvcc.idxCert (GF := GF) x.E.γ.idx []) ∗
      ([∧list] x ∈ ms, kvOpAu1 (GF := GF) x.γr.kv (.put (putKeyOp key val)) Q) ⊢
      anySpec ms (fun x : SrvAt GF => etcdPutSpec x.E x.γr x.cid x.mid)
        (txn.putOpOf key val (W64 0) false false false)
        (fun m => iprop(∃ x : SrvAt GF, ⌜x ∈ ms⌝ ∗
          putReplied x.E x.γr [] (txn.putOpOf key val (W64 0) false false false) Q x.cid x.mid m)) :=
    anySpec_intro _ _ _ _ (fun x : SrvAt GF => mvcc.idxCert x.E.γ.idx [])
      (fun x : SrvAt GF => kvOpAu1 x.γr.kv (.put (putKeyOp key val)) Q) (fun x hx => by
        iintro ⟨#HFx, Haux⟩
        unfold etcdPutSpec
        iexists []
        iframe HFx
        iexists Q
        isplitr
        · ipureintro; rfl
        iframe Haux
        iintro %m Hm
        iexists x
        iframe Hm
        ipureintro; exact hx)
  have hreg := isGrpcRpcs_anySpec (GF := GF) ms SrvAt.addr go!"/etcdserverpb.KV/Put"
    (fun x : SrvAt GF => etcdPutSpec x.E x.γr x.cid x.mid)
  ihave #Hrpc := hreg $$ Hregs
  iapply (v3.kv.wp_Put api (ms.map SrvAt.addr) ci cd key val sl []
    (anySpec ms (fun x : SrvAt GF => etcdPutSpec x.E x.γr x.cid x.mid))
    (fun m => iprop(∃ x : SrvAt GF, ⌜x ∈ ms⌝ ∗
      putReplied x.E x.γr [] (txn.putOpOf key val (W64 0) false false false) Q x.cid x.mid m)))
    $$ [Hau]
  · iframe #
    isplitr
    · ipureintro; exact Hpm
    unfold kvReqPre
    iright
    iunfold writeOnce at Ho
    icases Ho with (#Ho | %Hnr)
    · ileft
      iframe Ho
      inext
      rw [Hw]
      ihave Hsp := hs $$ [Hau]
      · iframe #
        iexact Hau
      iExactEq Hsp
      rfl
    · iright
      isplitl []
      · ipureintro; exact Hnr
      inext
      rw [Hw]
      ihave Hsp := hs $$ [Hau]
      · iframe #
        iexact Hau
      iExactEq Hsp
      rfl
  inext
  iintro %resp %err Hout
  iapply HΦ
  iunfold putCallOut at Hout
  icases Hout with (⟨%Herr, %m, Hm, Hq⟩ | ⟨%Herr, -⟩)
  · ileft
    isplitl []
    · ipureintro; exact Herr
    iexists m
    iframe
  · iright
    ipureintro; exact ⟨Herr.1, Herr.2.2⟩

/-- **`kv.Get(ctx, key, opts...)` through a client of the members `ms`** (`client_range_end_to_end`,
failover): each member's `Range` registered at its address, its committed index at least `c` and
floor `[]`, and the caller's read update at each member's names, persistent (`□ [∧ list]`: a read
may be answered by any member); `R` back, and `nil` with the reply's `rangeReplyOk` of some member,
or an error. -/
theorem client_range_any (api : Loc) (ms : List (SrvAt GF)) (c : w64) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (key : GoString) (sl : GoSlice)
    (gs : List (OpFull → OpFull)) (R : IProp GF) (Q : KVState → IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
        kvObjAt api (ms.map SrvAt.addr) ∗
        ([∗list] x ∈ ms, isGrpcRpc x.addr go!"/etcdserverpb.KV/Range"
          (etcdRangeSpec x.E x.γr x.cid x.mid)) ∗
        ([∗list] x ∈ ms, committedAtLeast x.γr c ∗ mvcc.idxCert x.E.γ.idx []) ∗
        ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAtRes sl gs R ∗ R ∗
        sortNamesIf (opGetModel key gs).base.sortSet ∗
        ⌜¬ opGetPanics gs ∧ (opGetModel key gs).t = W64 1⌝ ∗
        □ ([∧list] x ∈ ms, ⌜Q = fun _ => iprop(True)⌝ ∨
          (⌜(rangeWireOf (opGetModel key gs)).base.serializable = false⌝ ∗ kvReadAu x.γr.kv Q)) }}
      (App (App (App (Val (api @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!!
          go!"Get")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); R ∗
        ((⌜err = GoInterface.nil⌝ ∗ ∃ m : RangeRespM, rangeRespMsg resp m ∗ ∃ x : SrvAt GF,
            ⌜x ∈ ms⌝ ∗ rangeReplyOk x.E x.γr c [] (rangeWireOf (opGetModel key gs)) x.cid x.mid Q m) ∨
          ⌜err ≠ GoInterface.nil ∧ resp = null⌝) }} := by
  iintro %Φ ⟨#Pc, #Hkv, #Hregs, #Hfacts, #Hctx', #Hce, Hopts, HR, Hsn, %Hg, #Hdq⟩ HΦ
  have hreg := isGrpcRpcs_anySpec (GF := GF) ms SrvAt.addr go!"/etcdserverpb.KV/Range"
    (fun x : SrvAt GF => etcdRangeSpec x.E x.γr x.cid x.mid)
  ihave #Hrpc := hreg $$ Hregs
  have hs : ([∗list] x ∈ ms, committedAtLeast (GF := GF) x.γr c ∗ mvcc.idxCert x.E.γ.idx []) ∗
      ([∧list] x ∈ ms, iprop(⌜Q = fun _ => iprop(True)⌝ ∨
        (⌜(rangeWireOf (opGetModel key gs)).base.serializable = false⌝ ∗ kvReadAu x.γr.kv Q))) ⊢
      anySpec ms (fun x : SrvAt GF => etcdRangeSpec x.E x.γr x.cid x.mid)
        (rangeWireOf (opGetModel key gs))
        (fun m => iprop(∃ x : SrvAt GF, ⌜x ∈ ms⌝ ∗
          rangeReplyOk x.E x.γr c [] (rangeWireOf (opGetModel key gs)) x.cid x.mid Q m)) :=
    anySpec_intro _ _ _ _
      (fun x : SrvAt GF => iprop(committedAtLeast x.γr c ∗ mvcc.idxCert x.E.γ.idx []))
      (fun x : SrvAt GF => iprop(⌜Q = fun _ => iprop(True)⌝ ∨
        (⌜(rangeWireOf (opGetModel key gs)).base.serializable = false⌝ ∗ kvReadAu x.γr.kv Q)))
      (fun x hx => by
        iintro ⟨⟨#Hcx, #HFx⟩, Hdqx⟩
        unfold etcdRangeSpec
        iexists c, [], Q
        iframe Hcx HFx Hdqx
        iintro %m Hm
        iexists x
        iframe Hm
        ipureintro; exact hx)
  iapply (v3.kv.wp_Get api (ms.map SrvAt.addr) ci cd key sl gs R
    (anySpec ms (fun x : SrvAt GF => etcdRangeSpec x.E x.γr x.cid x.mid))
    (fun m => iprop(∃ x : SrvAt GF, ⌜x ∈ ms⌝ ∗
      rangeReplyOk x.E x.γr c [] (rangeWireOf (opGetModel key gs)) x.cid x.mid Q m)))
    $$ [Hopts HR Hsn]
  · iframe #
    iframe Hopts HR Hsn
    isplitl []
    · ipureintro; exact Hg
    imodintro
    inext
    ihave Hsp := hs $$ []
    · iframe #
    iExactEq Hsp
    rfl
  inext
  iintro %resp %err ⟨HR, Hout⟩
  iapply HΦ
  iframe HR
  iunfold rangeCallOut at Hout
  icases Hout with (⟨%Herr, %m, Hm, Hq⟩ | ⟨%Herr, -⟩)
  · ileft
    isplitl []
    · ipureintro; exact Herr
    iexists m
    iframe
  · iright
    ipureintro; exact ⟨Herr.1, Herr.2.2⟩

/-- **`kv.Delete(ctx, key)` through a client of the members `ms`** (`client_delete_end_to_end`'s
one-attempt case, failover; as `client_put_any`). -/
theorem client_delete_any (api : Loc) (ms : List (SrvAt GF)) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (key : GoString) (sl : GoSlice)
    (Q : KVState → IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
        kvObjAt api (ms.map SrvAt.addr) ∗ writeOnce api (ms.map SrvAt.addr) ∗
        ([∗list] x ∈ ms, isGrpcRpc x.addr go!"/etcdserverpb.KV/DeleteRange"
          (etcdDeleteSpec x.E x.γr x.cid x.mid)) ∗
        ([∗list] x ∈ ms, mvcc.idxCert x.E.γ.idx []) ∗
        ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAt sl [] ∗
        ([∧list] x ∈ ms, kvOpAu1 x.γr.kv (.deleteRange (txn.deleteOpOf key [] false)) Q) }}
      (App (App (App (Val (api @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!!
          go!"Delete")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        (⌜err = GoInterface.nil⌝ ∗ ∃ m : DelRespM, delRespMsg resp m ∗ ∃ x : SrvAt GF, ⌜x ∈ ms⌝ ∗
            deleteReplied x.E x.γr [] (txn.deleteOpOf key [] false) Q x.cid x.mid m) ∨
          ⌜err ≠ GoInterface.nil ∧ resp = null⌝ }} := by
  iintro %Φ ⟨#Pc, #Hkv, #Ho, #Hregs, #HF, #Hctx', #Hce, #Hopts, Hau⟩ HΦ
  have Hw : deleteWireOf (opDeleteModel key []) = txn.deleteOpOf key [] false := rfl
  have hreg := isGrpcRpcs_anySpec (GF := GF) ms SrvAt.addr go!"/etcdserverpb.KV/DeleteRange"
    (fun x : SrvAt GF => etcdDeleteSpec x.E x.γr x.cid x.mid)
  ihave #Hrpc := hreg $$ Hregs
  have hs : ([∗list] x ∈ ms, mvcc.idxCert (GF := GF) x.E.γ.idx []) ∗
      ([∧list] x ∈ ms, kvOpAu1 (GF := GF) x.γr.kv (.deleteRange (txn.deleteOpOf key [] false)) Q) ⊢
      anySpec ms (fun x : SrvAt GF => etcdDeleteSpec x.E x.γr x.cid x.mid)
        (txn.deleteOpOf key [] false)
        (fun m => iprop(∃ x : SrvAt GF, ⌜x ∈ ms⌝ ∗
          deleteReplied x.E x.γr [] (txn.deleteOpOf key [] false) Q x.cid x.mid m)) :=
    anySpec_intro _ _ _ _ (fun x : SrvAt GF => mvcc.idxCert x.E.γ.idx [])
      (fun x : SrvAt GF => kvOpAu1 x.γr.kv (.deleteRange (txn.deleteOpOf key [] false)) Q)
      (fun x hx => by
        iintro ⟨#HFx, Haux⟩
        unfold etcdDeleteSpec
        iexists []
        iframe HFx
        iexists Q
        isplitr
        · ipureintro; simp [txn.deleteOpOf]
        iframe Haux
        iintro %m Hm
        iexists x
        iframe Hm
        ipureintro; exact hx)
  iapply (v3.kv.wp_Delete api (ms.map SrvAt.addr) ci cd key sl []
    (anySpec ms (fun x : SrvAt GF => etcdDeleteSpec x.E x.γr x.cid x.mid))
    (fun m => iprop(∃ x : SrvAt GF, ⌜x ∈ ms⌝ ∗
      deleteReplied x.E x.γr [] (txn.deleteOpOf key [] false) Q x.cid x.mid m))) $$ [Hau]
  · iframe #
    isplitl []
    · ipureintro
      refine ⟨?_, rfl⟩
      simp [opGetModel, opFold, OpFull.getInit, OpFull.newOp, OpModel.zero, opDeleteModel,
        OpFull.deleteInit, opDeletePanics, opGetPanics, OpFull.deletePanics]
    rw [Hw]
    unfold kvReqPre
    iright
    iunfold writeOnce at Ho
    icases Ho with (#Ho | %Hnr)
    · ileft
      iframe Ho
      inext
      ihave Hsp := hs $$ [Hau]
      · iframe #
        iexact Hau
      iExactEq Hsp
      rfl
    · iright
      isplitl []
      · ipureintro; exact Hnr
      inext
      ihave Hsp := hs $$ [Hau]
      · iframe #
        iexact Hau
      iExactEq Hsp
      rfl
  inext
  iintro %resp %err Hout
  iapply HΦ
  iunfold deleteCallOut at Hout
  icases Hout with (⟨%Herr, %m, Hm, Hq⟩ | ⟨%Herr, -⟩)
  · ileft
    isplitl []
    · ipureintro; exact Herr
    iexists m
    iframe
  · iright
    ipureintro; exact ⟨Herr.1, Herr.2.2⟩

/-- **A transaction's update at a member**, as `client_txn_end_to_end` takes it: none (read-only),
a read update (read-only, linearizable) or an update fired at most once (writing). -/
def txnUpdAt (γw γr : ReadNames) (t : TxnModel) (Q : KVState → IProp GF) : IProp GF :=
  iprop(⌜txn.txnReadonly t = true ∧ Q = fun _ => iprop(True)⌝ ∨
    (⌜txn.txnReadonly t = true ∧ txn.txnSerializable t = false⌝ ∗ kvReadAu γr.kv Q) ∨
    (⌜txn.txnReadonly t = false ∧ txn.txnPlain t ∧ txnNoZeroEnd t⌝ ∗ kvOpAu1 γw.kv (.txn t) Q))

/-- **`Commit()` through a client of the members `ms`** (`client_txn_end_to_end`'s one-attempt
case, failover): each member's `Txn` registered at its address, its committed index at least `c`
and floor `[]`, and the caller's update at each member's names (`[∧ list]`; for a read-only
transaction a read update or none, persistent); `nil` with the reply's `txnReplied` of some member,
or an error. -/
theorem client_txn_any (tp : Loc) (ms : List (SrvAt GF)) (c : w64) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (b : TxnBuild) (Q : KVState → IProp GF)
    (hp : TxnModel.plain b.model) (hin : txnModelIn (txnWireOf b.model)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
        txnObjAt tp (ms.map SrvAt.addr) ci cd b ∗
        ([∗list] x ∈ ms, isGrpcRpc x.addr go!"/etcdserverpb.KV/Txn"
          (etcdTxnSpec x.E x.γr x.γr x.cid x.mid)) ∗
        ([∗list] x ∈ ms, committedAtLeast x.γr c ∗ mvcc.idxCert x.E.γ.idx []) ∗
        ((⌜txn.txnReadonly (txnWireOf b.model) = true⌝ ∗
            □ ([∧list] x ∈ ms, txnUpdAt x.γr x.γr (txnWireOf b.model) Q)) ∨
          (txnWriteOnce tp (ms.map SrvAt.addr) ∗
            [∧list] x ∈ ms, txnUpdAt x.γr x.γr (txnWireOf b.model) Q)) }}
      (App (Val (tp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.txn.ty @!! go!"Commit"))
        (Val #()))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        (⌜err = GoInterface.nil⌝ ∗ ∃ m : TxnRespM, txnRespMsg resp m ∗ ∃ x : SrvAt GF, ⌜x ∈ ms⌝ ∗
            txnReplied x.E x.γr x.γr c [] (txnWireOf b.model) Q x.cid x.mid m) ∨
          ⌜err ≠ GoInterface.nil ∧ resp = null⌝ }} := by
  iintro %Φ ⟨#Pc, Hobj, #Hregs, #Hfacts, Hnp⟩ HΦ
  have hreg := isGrpcRpcs_anySpec (GF := GF) ms SrvAt.addr go!"/etcdserverpb.KV/Txn"
    (fun x : SrvAt GF => etcdTxnSpec x.E x.γr x.γr x.cid x.mid)
  ihave #Hrpc := hreg $$ Hregs
  have hs : ([∗list] x ∈ ms, committedAtLeast (GF := GF) x.γr c ∗ mvcc.idxCert x.E.γ.idx []) ∗
      ([∧list] x ∈ ms, txnUpdAt (GF := GF) x.γr x.γr (txnWireOf b.model) Q) ⊢
      anySpec ms (fun x : SrvAt GF => etcdTxnSpec x.E x.γr x.γr x.cid x.mid) (txnWireOf b.model)
        (fun m => iprop(∃ x : SrvAt GF, ⌜x ∈ ms⌝ ∗
          txnReplied x.E x.γr x.γr c [] (txnWireOf b.model) Q x.cid x.mid m)) :=
    anySpec_intro _ _ _ _
      (fun x : SrvAt GF => iprop(committedAtLeast x.γr c ∗ mvcc.idxCert x.E.γ.idx []))
      (fun x : SrvAt GF => txnUpdAt x.γr x.γr (txnWireOf b.model) Q)
      (fun x hx => by
        iintro ⟨⟨#Hcx, #HFx⟩, Hu⟩
        unfold etcdTxnSpec
        isplitl []
        · ipureintro; exact ⟨txnWireOf_plain _ hp, hin⟩
        iexists Q
        iunfold txnUpdAt at Hu
        iframe Hu
        iexists c, []
        iframe Hcx HFx
        iintro %m Hm
        iexists x
        iframe Hm
        ipureintro; exact hx)
  iapply (v3.txn.wp_Commit tp (ms.map SrvAt.addr) ci cd b
    (anySpec ms (fun x : SrvAt GF => etcdTxnSpec x.E x.γr x.γr x.cid x.mid))
    (fun m => iprop(∃ x : SrvAt GF, ⌜x ∈ ms⌝ ∗
      txnReplied x.E x.γr x.γr c [] (txnWireOf b.model) Q x.cid x.mid m))) $$ [Hobj Hnp]
  · iframe Hobj
    iframe #
    unfold txnReqPre
    icases Hnp with (⟨%Hro, #Hu⟩ | ⟨Ho, Hu⟩)
    · ileft
      imodintro
      inext
      ihave Hsp := hs $$ []
      · iframe #
      iExactEq Hsp
      rfl
    · iright
      iunfold txnWriteOnce at Ho
      icases Ho with (Ho | %Hnr)
      · ileft
        iframe Ho
        inext
        ihave Hsp := hs $$ [Hu]
        · iframe #
          iexact Hu
        iExactEq Hsp
        rfl
      · iright
        isplitl []
        · ipureintro; exact Hnr
        inext
        ihave Hsp := hs $$ [Hu]
        · iframe #
          iexact Hu
        iExactEq Hsp
        rfl
  inext
  iintro %resp %err Hout
  iapply HΦ
  iunfold txnCallOut at Hout
  icases Hout with (⟨%Herr, %m, Hm, Hq⟩ | ⟨%Herr, -⟩)
  · ileft
    isplitl []
    · ipureintro; exact Herr
    iexists m
    iframe
  · iright
    ipureintro; exact ⟨Herr.1, Herr.2.2⟩

end e2e

end client
end EtcdGrove
end Perennial

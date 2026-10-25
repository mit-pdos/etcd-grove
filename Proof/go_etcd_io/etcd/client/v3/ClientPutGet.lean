/-
**`(*Client).Put`/`Get` by the client `New` returns** (item 9, point 7, 2026-10-18): the methods
of `*Client` promoted from its embedded `KV` interface reduce to the `*kv`'s (`kv.Put`/`kv.Get`)
that `New` stores in the `KV` field (`isNewClient`), so `client_put_end_to_end` and `client_get_end_to_end` at
`PutThenGet.lean`'s updates hold of the calls the adequacy example makes (`cli.Put(ctx, k, v)`,
`cli.Get(ctx, k)`). Lean-first (no Rocq counterpart).

The reduction is the translation's method-set rules `Client.TypeAssumptions.ptr_Put_unfold` and
`ptr_Get_unfold` (a promoted method of an embedded interface is a method resolution on the field's
value), which the Goose configuration emits once the filter names the methods
(`Code/go_etcd_io/etcd/client/v3.toml`: `Client.Put`, `Client.Get`); no translator change.

**The client's calls, one family** (2026-10-22, D31): every example calls `New`'s client through
the lemmas of this file.

- With a persistent update (any client): `client_Put_own`, `client_Get_own` (putget's
  `putGetInv`).
- Through a client of the members `ms` (`Results.lean`'s `SrvAt`; one member is `[x]`), each
  stated with the state `σ` its update fired at and the reply's fields as functions of `σ`:
  - `client_Get_st`: a linearizable get of one key, with a persistent read update (`kvReadAu`) or
    none: `□ Q σ`, the reply's key-values the state's of the key, its header revision `σ`'s;
  - `client_Put_rep`, `client_Put_st`: a put with an update fired at most once, on a client that
    sends a write at most once (`clientWriteOnce`: refusal-free members, D29): a
    member's `putReplied`; or `Q σ` and the reply's header revision;
  - `client_Delete_st`: a delete, as the put: `Q σ`, the reply's count and header revision;
  - `client_Txn_st`: `cli.Txn(ctx)`, the builder made from the client's `*kv`, with
    `txnWriteOnce` for its `Commit`.
- What a call starts from at each member: `srvStart` (free, `srvStart_alloc`); the members'
  registrations, `kvRegsAt` (the `*kv`'s calls take them all, D43).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.PutThenGet
public import Proof.go_etcd_io.etcd.client.v3.InvClientNewResult
public import Proof.go_etcd_io.etcd.client.v3.ReplyValues

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace client

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver

section e2e
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **The client's invariant at a log's state** (allocated with the put not fired; every log's
state is sorted by key, `mvcc.stateAfter_sorted`): from the client's `etcdKV` at `kvStateOf l`
(the bootstrap log's model, as the server's allocation gives it, `srvBootOut`). -/
theorem putGetInv_alloc_log (γr : ReadNames) (l : mvcc.Log) (key val : GoString) (Em : CoPset) :
    etcdKV (GF := GF) γr.kv (kvStateOf l) ⊢ |={Em}=> ∃ γf : GName, putGetInv γr γf key val := by
  iintro Hσ
  imod (mono_nat_own_alloc (GF := GF) 0) with ⟨%γf, Hm, -⟩
  imod inv_alloc kvClientN Em (iprop(∃ (σ : KVState) (n : Nat), etcdKV γr.kv σ ∗
      monoNatAuthOwn γf 1 n ∗ ⌜putGetOk key val σ n⌝)) $$ [Hσ Hm] with #Hinv
  · inext; iexists kvStateOf l, 0; iframe Hσ Hm
    ipureintro; exact ⟨mvcc.stateAfter_sorted l, fun h => absurd h (by omega)⟩
  imodintro
  iexists γf
  iunfold putGetInv
  iexact Hinv

/-- **`cli.Put(ctx, key, val)` by `New`'s client `cl`** (`client_put_end_to_end` at `putAu_of_putGetInv`, through the
`KV` field):
`nil`, the reply and the put's flag; or an error. -/
theorem client_Put_own (cl : Loc) (ep : GoString) (V : WEnv GF) (E : apply.AEnv GF)
    (γr : ReadNames) (γf : GName) (cid mid : w64) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (key val : GoString) (sl : GoSlice) (F : mvcc.Log) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ isNewClient cl [ep] V ∗
        kvRegsAt (⟨ep, E, γr, cid, mid⟩ : SrvAt GF) ∗
        ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAt sl [] ∗
        putGetInv γr γf key val ∗ mvcc.idxCert E.γ.idx F }}
      (App (App (App (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
          go!"Put")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #val)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        (⌜err = GoInterface.nil⌝ ∗ (∃ m : PutRespM, putRespMsg resp m ∗
            putReplied E γr F (putKeyOp key val) (fun _ => monoNatLbOwn γf 1) cid mid m) ∗
            monoNatLbOwn γf 1) ∨
          ⌜err ≠ GoInterface.nil ∧ resp = null⌝ }} := by
  iintro %Φ ⟨#Pc, #Hcl, #Hrpc0, #Hctx, #Hce, #Hopts, #Hinv, #HF⟩ HΦ
  ihave #Hrpc := kvRegs_one ep E γr cid mid $$ Hrpc0
  iunfold isNewClient at Hcl
  icases Hcl with ⟨-, -, ⟨%api, #Hkvf, #Hkv⟩, -⟩
  rw [go_etcd_io.etcd.client.v3.Client.TypeAssumptions.ptr_Put_unfold.method_unfold]
  wp_pures
  wp_auto
  ihave #Hau := putAu_of_putGetInv γr γf key val $$ Hinv
  -- (2026-10-19, D21 M6) a persistent update, its result persistent
  ihave Hau' := putAuOk_of_box api [ep] γr.kv _ _ $$ Hau
  wp_apply (client_put_end_to_end api [ep] E γr cid mid ci cd key val sl
    (fun _ => iprop(□ monoNatLbOwn γf 1)) F) $$ [Hau'] as %resp %err Hout
  · iframe #
  iapply HΦ
  icases Hout with (⟨%Herr, %m, Hm, Hp⟩ | %Herr)
  · ihave Hp := putReplied_mono E γr F _ (fun _ => iprop(□ monoNatLbOwn γf 1))
      (fun _ => monoNatLbOwn γf 1) cid mid m (fun _ => intuitionistically_elim) $$ Hp
    ileft
    ihave #Hlb : monoNatLbOwn γf 1 $$ [Hp]
    · iunfold putReplied at Hp
      icases Hp with ⟨%hm, %x, %x', %l, %skip, -, -, -, -, -, #Hq⟩
      iexact Hq
    isplitr
    · ipureintro; exact Herr
    isplitl
    · iexists m; iframe
    · iexact Hlb
  · iright
    ipureintro; exact Herr

/-- **`cli.Get(ctx, key)` by `New`'s client `cl`, after its put fired** (`client_get_end_to_end`
at `getAu_of_putGetInv`, then `client_get_value`, through the `KV` field): `nil` and a reply whose first key-value's value is `val`; or an error. -/
theorem client_Get_own (cl : Loc) (ep : GoString) (V : WEnv GF) (E : apply.AEnv GF)
    (γr : ReadNames) (γf : GName) (c cid mid : w64) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (key val : GoString) (sl : GoSlice) (F : mvcc.Log) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ isNewClient cl [ep] V ∗
        kvRegsAt (⟨ep, E, γr, cid, mid⟩ : SrvAt GF) ∗
        ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAt sl [] ∗ committedAtLeast γr c ∗
        putGetInv γr γf key val ∗ monoNatLbOwn γf 1 ∗ mvcc.idxCert E.γ.idx F }}
      (App (App (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
          go!"Get")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        (⌜err = GoInterface.nil⌝ ∗ ∃ m : RangeRespM, rangeRespMsg resp m ∗
            ⌜m.kvs.head?.map EtcdKv.value = some val⌝) ∨
          ⌜err ≠ GoInterface.nil ∧ resp = null⌝ }} := by
  iintro %Φ ⟨#Pc, #Hcl, #Hrpc0, #Hctx, #Hce, #Hopts, #Hc, #Hinv, #Hlb, #HF⟩ HΦ
  ihave #Hrpc := kvRegs_one ep E γr cid mid $$ Hrpc0
  iunfold isNewClient at Hcl
  icases Hcl with ⟨-, -, ⟨%api, #Hkvf, #Hkv⟩, -⟩
  rw [go_etcd_io.etcd.client.v3.Client.TypeAssumptions.ptr_Get_unfold.method_unfold]
  wp_pures
  wp_auto
  ihave #Hau := getAu_of_putGetInv γr γf key val $$ [Hinv Hlb]
  · iframe #
  wp_apply (client_get_end_to_end api [ep] E γr c cid mid ci cd key sl
    (fun σ => iprop(⌜(mvcc.findKey key σ.kvs).map EtcdKv.value = some val⌝)) F) $$ []
    as %resp %err Hout
  · iframe #
  iapply HΦ
  icases Hout with (⟨%Herr, %m, Hm, #Hq⟩ | %Herr)
  · ileft
    ihave Hv := client_get_value E γr c cid mid key F _ m $$ Hq
    icases Hv with ⟨%σ, %Hσ, %Hval, -⟩
    isplitr
    · ipureintro; exact Herr
    iexists m
    iframe Hm
    ipureintro
    rw [Hval, Hσ]
  · iright
    ipureintro; exact Herr

end e2e

/-! ## Through a client of the members `ms` (see the file header) -/

section family
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **What a linearizable range's reply says** (any range at the latest revision): the client's
read update fired at a state `σ` (`□ Q σ`) whose key-values give the reply's (`srvRangeOk`), whose
revision is the reply's header revision, and which is below `2 ^ 63`. -/
theorem rangeReply_state_bnd (E : apply.AEnv GF) (γr : ReadNames) (c cid mid : w64) (o : OpFull)
    (F : mvcc.Log) (Q : KVState → IProp GF) (m : RangeRespM) (hs : o.base.serializable = false)
    (hr : o.base.rev = W64 0) :
    rangeReplyOk E γr c F o cid mid Q m ⊢
      ∃ σ : KVState, □ Q σ ∗ ⌜txn.srvRangeOk o σ.kvs m.kvs m.more ∧
        m.hdr.revision = W64 (σ.rev : Int) ∧ σ.rev + 3 < 2 ^ 63⌝ := by
  iintro #H
  iunfold rangeReplyOk at H
  icases H with ⟨%l, -, -, %Hl, -, #HQ⟩
  simp only [hs, Bool.false_eq_true, ↓reduceIte]
  obtain ⟨hlen, hlen', hrev, -, -, -, -, hsel, -⟩ := Hl
  have hst : mvcc.stateAt l (sint.nat (mvcc.rangeRev m.hdr.revision o.base.rev)) =
      mvcc.stateAfter l := by
    have h1 : mvcc.rangeRev m.hdr.revision o.base.rev = m.hdr.revision := by
      simp [mvcc.rangeRev, hr]
    rw [h1, hrev]
    have h2 : sint.nat (W64 ((l.length : Int) - 1)) = l.length - 1 := by
      unfold sint.nat; word
    rw [h2, mvcc.stateAt_last]
  rw [hst] at hsel
  iexists kvStateOf l
  iframe HQ
  ipureintro
  try rw [kvStateOf_kvs]
  refine ⟨hsel, ?_, ?_⟩
  · rw [hrev]
    simp only [kvStateOf_rev, kvStateOf_kvs]
    congr 1
    omega
  · simp only [kvStateOf_rev, kvStateOf_kvs]
    omega

/-- **The members' read updates, persistent** (each is: a read update, or none). -/
theorem readUpds_box (ms : List (SrvAt GF)) (Q : KVState → IProp GF) :
    ([∧list] x ∈ ms, iprop(⌜Q = fun _ => iprop(True)⌝ ∨ kvReadAu (GF := GF) x.γr.kv Q)) ⊢
      □ ([∧list] x ∈ ms, iprop(⌜Q = fun _ => iprop(True)⌝ ∨ kvReadAu x.γr.kv Q)) := by
  haveI : Persistent ([∧list] x ∈ ms,
      iprop(⌜Q = fun _ => iprop(True)⌝ ∨ kvReadAu (GF := GF) x.γr.kv Q)) :=
    BigAndL.bigAndL_persistent fun {_ _} _ => inferInstance
  exact intuitionistic_alias

/-- `cli.Get(ctx, key)` by `New`'s client of the members `ms`, with a read update or none (see
the file header). -/
theorem client_Get_st (cl : Loc) (ms : List (SrvAt GF)) (V : WEnv GF) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (key : GoString) (sl : GoSlice)
    (Q : KVState → IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
        isNewClient cl (ms.map SrvAt.addr) V ∗
        ([∗list] x ∈ ms, kvRegsAt x) ∗ ([∗list] x ∈ ms, srvStart x) ∗
        ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAt sl [] ∗
        □ ([∧list] x ∈ ms, ⌜Q = fun _ => iprop(True)⌝ ∨ kvReadAu x.γr.kv Q) }}
      (App (App (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
          go!"Get")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        (⌜err = GoInterface.nil⌝ ∗ ∃ (m : RangeRespM) (σ : KVState), rangeRespMsg resp m ∗
          □ Q σ ∗ ⌜m.kvs = σ.kvs.filter (fun v => decide (v.key = key)) ∧
            m.hdr.revision = W64 (σ.rev : Int) ∧ σ.rev + 3 < 2 ^ 63⌝) ∨
          (⌜err ≠ GoInterface.nil⌝ ∗ kvErr err) }} := by
  iintro %Φ ⟨#Pc, #Hcl, #Hrr, #Hst, #Hctx, #Hce, #Hopts, #Hau⟩ HΦ
  iunfold isNewClient at Hcl
  icases Hcl with ⟨-, -, ⟨%api, #Hkvf, #Hkv⟩, -⟩
  ihave #Hopts' := optsAt_res sl [] iprop(True) $$ Hopts
  have hm : ∀ (k : Nat) (x : SrvAt GF), ms[k]? = some x →
      iprop(⌜Q = fun _ => iprop(True)⌝ ∨ kvReadAu x.γr.kv Q) ⊢
      iprop(⌜Q = fun _ => iprop(True)⌝ ∨
        (⌜(rangeWireOf (opGetModel key [])).base.serializable = false⌝ ∗ kvReadAu x.γr.kv Q)) :=
    fun _ _ _ => by
      iintro (%h | #h)
      · ileft; ipureintro; exact h
      · iright; iframe h; ipureintro; rfl
  ihave #Hau' := (BigAndL.bigAndL_mono hm) $$ Hau
  ihave #Hst' := srvStart_both ms $$ Hst
  rw [go_etcd_io.etcd.client.v3.Client.TypeAssumptions.ptr_Get_unfold.method_unfold]
  wp_pures
  wp_auto
  wp_apply (client_range_any api ms (W64 0) ci cd key sl [] iprop(True) Q []) $$ []
    as %resp %err ⟨-, Hout⟩
  · iframe #
    isplitl []
    · rw [show (opGetModel key []).base.sortSet = false from rfl]
      iapply sortNamesIf_false
    ipureintro
    first
      | rfl
      | (refine ⟨?_, rfl⟩; unfold opGetPanics opFold OpFull.newOp; simp)
  iapply HΦ
  icases Hout with (⟨%Herr, %m, #Hm, %x, %hx, #Hq⟩ | ⟨%Herr, #Hke⟩)
  · ileft
    isplitl []
    · ipureintro; exact Herr
    ihave Hs := rangeReply_state_bnd x.E x.γr (W64 0) x.cid x.mid _ [] Q m rfl rfl $$ Hq
    icases Hs with ⟨%σ, #HQ, %Hσ⟩
    obtain ⟨hsel, hrev, hb⟩ := Hσ
    iexists m, σ
    iframe Hm HQ
    ipureintro
    exact ⟨(srvRangeOk_getKey key _ _ _ hsel).1, hrev, hb⟩
  · iright
    isplitl
    · ipureintro; exact Herr.1
    · iexact Hke

/-- A write through `New`'s client sent at most once (D29): its `*kv`'s (`KV` field's). -/
theorem clientWriteOnce_api (cl api : Loc) (addrs : List GoString) :
    clientF cl go!"KV" ↦□
        interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty) #api ∗
      clientWriteOnce (GF := GF) cl addrs ⊢ writeOnce api addrs := by
  iintro ⟨-, #Hw⟩
  iunfold clientWriteOnce at Hw
  iunfold writeOnce
  iexact Hw

/-- `cli.Put(ctx, key, val)` by `New`'s client of the members `ms` that sends a write at most
once, with an update fired at most once, one per member (see the file header): `nil`, the reply's
message and some member's `putReplied`; or an error. -/
theorem client_Put_rep (cl : Loc) (ms : List (SrvAt GF)) (V : WEnv GF) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (key val : GoString) (sl : GoSlice)
    (Q : KVState → IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
        isNewClient cl (ms.map SrvAt.addr) V ∗ clientWriteOnce cl (ms.map SrvAt.addr) ∗
        ([∗list] x ∈ ms, kvRegsAt x) ∗ ([∗list] x ∈ ms, mvcc.idxCert x.E.γ.idx []) ∗
        ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAt sl [] ∗
        ([∧list] x ∈ ms, kvOpAu1 x.γr.kv (.put (putKeyOp key val)) Q) }}
      (App (App (App (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
          go!"Put")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #val)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        (⌜err = GoInterface.nil⌝ ∗ ∃ m : PutRespM, putRespMsg resp m ∗ ∃ x : SrvAt GF, ⌜x ∈ ms⌝ ∗
            putReplied x.E x.γr [] (putKeyOp key val) Q x.cid x.mid m) ∨
          (⌜err ≠ GoInterface.nil⌝ ∗ kvErr err) }} := by
  iintro %Φ ⟨#Pc, #Hcl, #Hone, #Hrr, #HF, #Hctx, #Hce, #Hopts, Hau⟩ HΦ
  iunfold isNewClient at Hcl
  icases Hcl with ⟨-, -, ⟨%api, #Hkvf, #Hkv⟩, -⟩
  ihave #Hwo := clientWriteOnce_api cl api _ $$ [Hkvf Hone]
  · iframe #
  rw [go_etcd_io.etcd.client.v3.Client.TypeAssumptions.ptr_Put_unfold.method_unfold]
  wp_pures
  wp_auto
  wp_apply (client_put_any api ms ci cd key val sl Q []) $$ [Hau] as %resp %err Hout
  · iframe #
    iright
    iframe #
    iexact Hau
  iapply HΦ
  icases Hout with (⟨%Herr, %m, #Hm, Hr⟩ | ⟨%Herr, #Hke⟩)
  · ileft
    isplitl []
    · ipureintro; exact Herr
    iexists m
    iframe Hm Hr
  · iright
    isplitl
    · ipureintro; exact Herr.1
    · iexact Hke

/-- `cli.Put(ctx, key, val)` by `New`'s client of the members `ms` that sends a write at most
once, with an update fired at most once, one per member (see the file header): `nil`, `Q σ` and
the reply's header revision, the put's at `σ`; or an error. -/
theorem client_Put_st (cl : Loc) (ms : List (SrvAt GF)) (V : WEnv GF) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (key val : GoString) (sl : GoSlice)
    (Q : KVState → IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
        isNewClient cl (ms.map SrvAt.addr) V ∗ clientWriteOnce cl (ms.map SrvAt.addr) ∗
        ([∗list] x ∈ ms, kvRegsAt x) ∗ ([∗list] x ∈ ms, mvcc.idxCert x.E.γ.idx []) ∗
        ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAt sl [] ∗
        ([∧list] x ∈ ms, kvOpAu1 x.γr.kv (.put (putKeyOp key val)) Q) }}
      (App (App (App (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
          go!"Put")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #val)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        (⌜err = GoInterface.nil⌝ ∗ ∃ (m : PutRespM) (σ : KVState), putRespMsg resp m ∗ Q σ ∗
          ⌜m.hdr.revision = W64 ((σ.rev + 1 : Nat) : Int) ∧ σ.rev + 4 < 2 ^ 63⌝) ∨
          (⌜err ≠ GoInterface.nil⌝ ∗ kvErr err) }} := by
  iintro %Φ H HΦ
  wp_apply (client_Put_rep cl ms V ci cd key val sl Q) $$ [H] as %resp %err Hout
  · iexact H
  iapply HΦ
  icases Hout with (⟨%Herr, %m, #Hm, %x, %hx, Hr⟩ | ⟨%Herr, #Hke⟩)
  · ileft
    isplitl []
    · ipureintro; exact Herr
    iunfold putReplied at Hr
    icases Hr with ⟨%hm, %y, %y', %l, %skip, %Hp, -, -, -, -, HQ⟩
    obtain ⟨-, hrev, -, -, -, -, hlen, hb⟩ := Hp
    iexists m, kvStateOf y.log
    iframe Hm HQ
    ipureintro
    refine ⟨?_, ?_⟩
    · rw [hrev, kvStateOf_rev_succ _ hlen]
    · simp only [kvStateOf_rev, kvStateOf_kvs]; omega
  · iright
    isplitl
    · ipureintro; exact Herr
    · iexact Hke

/-- `cli.Delete(ctx, key)` by `New`'s client of the members `ms` that sends a write at most once,
with an update fired at most once, one per member (see the file header). -/
theorem client_Delete_st (cl : Loc) (ms : List (SrvAt GF)) (V : WEnv GF) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (key : GoString) (sl : GoSlice)
    (Q : KVState → IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
        isNewClient cl (ms.map SrvAt.addr) V ∗ clientWriteOnce cl (ms.map SrvAt.addr) ∗
        ([∗list] x ∈ ms, kvRegsAt x) ∗ ([∗list] x ∈ ms, mvcc.idxCert x.E.γ.idx []) ∗
        ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAt sl [] ∗
        ([∧list] x ∈ ms, kvOpAu1 x.γr.kv (.deleteRange (txn.deleteOpOf key [] false)) Q) }}
      (App (App (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
          go!"Delete")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        (⌜err = GoInterface.nil⌝ ∗ ∃ (m : DelRespM) (σ : KVState), delRespMsg resp m ∗ Q σ ∗
          ⌜m.deleted = W64 ((rangeIn σ.kvs (txn.deleteOpOf key [] false)).length : Int) ∧
            m.hdr.revision =
              W64 ((kvOpStep (.deleteRange (txn.deleteOpOf key [] false)) σ).rev : Int) ∧
            σ.rev + 4 < 2 ^ 63⌝) ∨
          (⌜err ≠ GoInterface.nil⌝ ∗ kvErr err) }} := by
  iintro %Φ ⟨#Pc, #Hcl, #Hone, #Hrr, #HF, #Hctx, #Hce, #Hopts, Hau⟩ HΦ
  iunfold isNewClient at Hcl
  icases Hcl with ⟨-, -, ⟨%api, #Hkvf, #Hkv⟩, -⟩
  ihave #Hwo := clientWriteOnce_api cl api _ $$ [Hkvf Hone]
  · iframe #
  rw [go_etcd_io.etcd.client.v3.Client.TypeAssumptions.ptr_Delete_unfold.method_unfold]
  wp_pures
  wp_auto
  wp_apply (client_delete_any api ms ci cd key sl Q []) $$ [Hau] as %resp %err Hout
  · iframe #
    iright
    iframe #
    iexact Hau
  iapply HΦ
  icases Hout with (⟨%Herr, %m, #Hm, %x, %hx, Hr⟩ | ⟨%Herr, #Hke⟩)
  · ileft
    isplitl []
    · ipureintro; exact Herr
    iunfold deleteReplied at Hr
    icases Hr with ⟨%hm, %rq', %op', %y, %y', %l, %skip, %Hp, -, -, -, -, HQ⟩
    obtain ⟨-, -, Hz, -, hrev, -, -, hdel, -, -, hlen, hb⟩ := Hp
    have hnz : irrNoZeroEnd (irrDeleteRange (txn.deleteOpOf key [] false)) := by
      refine ⟨fun o' h => by simp [irrDeleteRange, apply.irrEmpty] at h, fun o' h => ?_,
        fun t h => by simp [irrDeleteRange, apply.irrEmpty] at h⟩
      simp only [irrDeleteRange, Option.some.injEq] at h
      subst h
      simp [txn.deleteOpOf, op_simps]
    have hop : op' = txn.deleteOpOf key [] false := Hz hnz
    subst hop
    iexists m, kvStateOf y.log
    iframe Hm HQ
    ipureintro
    refine ⟨hdel, ?_, ?_⟩
    · rw [hrev]
      unfold kvOpStep
      rw [kvStateOf_commit_rev _ _ hlen]
      rfl
    · simp only [kvStateOf_rev, kvStateOf_kvs]; omega
  · iright
    isplitl
    · ipureintro; exact Herr.1
    · iexact Hke

/-- `cli.Txn(ctx)` by `New`'s client of the members `ms`: the builder, empty, made from the
client's `*kv` (which sends a write at most once: `txnWriteOnce`). -/
theorem client_Txn_st (cl : Loc) (ms : List (SrvAt GF)) (V : WEnv GF) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
        isNewClient cl (ms.map SrvAt.addr) V ∗ clientWriteOnce cl (ms.map SrvAt.addr) ∗
        ctxOk ci cd ∗ ctxErrClient ci cd }}
      (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
          go!"Txn")) (Val #(GoInterface.ok ci)))
    {{ (t : GoInterface), RET #t; ∃ tp : Loc,
        ⌜t = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.txn.ty) #tp⌝ ∗
        txnObjAt tp (ms.map SrvAt.addr) ci cd TxnBuild.empty ∗
        txnWriteOnce tp (ms.map SrvAt.addr) }} := by
  iintro %Φ ⟨#Pc, #Hcl, #Hone, #Hctx, #Hce⟩ HΦ
  iunfold isNewClient at Hcl
  icases Hcl with ⟨-, -, ⟨%api, #Hkvf, #Hkv⟩, -⟩
  ihave #Hwo := clientWriteOnce_api cl api _ $$ [Hkvf Hone]
  · iframe #
  rw [go_etcd_io.etcd.client.v3.Client.TypeAssumptions.ptr_Txn_unfold.method_unfold]
  wp_pures
  wp_auto
  wp_apply (v3.kv.wp_Txn api (ms.map SrvAt.addr) ci cd) as %t ⟨%tp, %Ht, Hobj, #Hkt⟩
  · iframe #
  iapply HΦ
  iexists tp
  iframe Hobj
  isplitr
  · ipureintro; exact Ht
  iunfold txnWriteOnce
  iunfold writeOnce at Hwo
  iexact Hwo

end family

end client
end EtcdGrove
end Perennial

#print axioms Perennial.EtcdGrove.client.putGetInv_alloc_log
#print axioms Perennial.EtcdGrove.client.client_Put_own
#print axioms Perennial.EtcdGrove.client.client_Get_own
#print axioms Perennial.EtcdGrove.client.client_Get_st
#print axioms Perennial.EtcdGrove.client.client_Put_rep
#print axioms Perennial.EtcdGrove.client.client_Put_st
#print axioms Perennial.EtcdGrove.client.client_Delete_st
#print axioms Perennial.EtcdGrove.client.client_Txn_st

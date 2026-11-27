/-
**The auth example's linked calls, as hypotheses** (the import tiers, 2026-11-18): the statements of
`ClientOn.lean`'s `client_Put_on`/`client_Get_on`/`client_Txn_on` and `WorkCallsLinked.lean`'s `work_*`, each as
`<name>.law : Prop`, which a function's proof (`SetUp`, `Work`, the barriers of `auth3`/`authN`) takes
as a hypothesis instead of importing those linking modules; `<name>_law_holds` (beside the lemma)
proves it, and the `Link`s pass it.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.authwork.WorkCalls

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_auth

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver client

section laws1
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- `client_Put_on`'s statement (`ClientOn.lean`, a linking module), as a hypothesis of the proofs
that use it (the import tiers); `client_Put_on_law_holds` proves it. -/
abbrev client_Put_on.law : Prop :=
  ∀ (cl api conn : Loc) (addr : GoString) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
      (cid mid : w64) (ci : GoInterfaceOk) (om : GrpcMd) (cd : context.ContextDesc (IProp GF))
      (key val : GoString) (sl : GoSlice) (Q : KVState → IProp GF) (F : mvcc.Log)
      (hsz : opSizeOk (opPutModel key val [])),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗ (structFieldRef go_etcd_io.etcd.client.v3.Client go!"KV" cl ↦□
            (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty) #api :
              GoInterface) ∗
          kvObjAtC api conn [addr] ∗
          isGrpcRpcMd addr go!"/etcdserverpb.KV/Put" (etcdPutSpecOn (srvTLSId s) E ρ cid mid) ∗
          srvApi.kvLogLb E.γs F ∗ metadata.outMD ci om ∗ ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAt sl [] ∗
          □ kvOpAu1 ρ.rd.kv (.put (putKeyOp key val)) Q) }}
        (App (App (App (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
            go!"Put")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #val)) (Val #sl))
      {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗ ((⌜err = GoInterface.nil⌝ ∗ ∃ m : PutRespM, putRespMsg resp m ∗
              putReplied E ρ.rd F (putKeyOp key val) Q cid mid m ∗
              ∃ md, clientAttemptMd conn om md ∗
                v3rpc.writeGrantOn (srvTLSId s) E ρ (auth.mdTokenOf md) (irrPut (putKeyOp key val))) ∨
            (⌜err ≠ GoInterface.nil⌝ ∗ kvErr err)) }}

/-- `client_Get_on`'s statement (`ClientOn.lean`, a linking module), as a hypothesis of the proofs
that use it (the import tiers); `client_Get_on_law_holds` proves it. -/
abbrev client_Get_on.law : Prop :=
  ∀ (cl api conn : Loc) (addr : GoString) (s : Loc) (E : apply.AEnv GF) (γr : ReadNames)
      (cid mid c : w64) (n : Nat) (ci : GoInterfaceOk) (om : GrpcMd) (cd : context.ContextDesc (IProp GF))
      (key : GoString) (sl : GoSlice) (gs : List (OpFull → OpFull)) (R : IProp GF)
      (Q : KVState → IProp GF) (F : mvcc.Log) (hsz : opSizeOk (opGetModel key gs)),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗ (structFieldRef go_etcd_io.etcd.client.v3.Client go!"KV" cl ↦□
            (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty) #api :
              GoInterface) ∗
          kvObjAtC api conn [addr] ∗
          isGrpcRpcMd addr go!"/etcdserverpb.KV/Range" (etcdRangeSpecOn (srvTLSId s) E γr cid mid) ∗
          committedAtLeast γr c ∗ srvApi.kvLogLb E.γs F ∗ auth.authPubLbM E.authMode n ∗
          metadata.outMD ci om ∗ ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAtRes sl gs R ∗ R ∗
          sortNamesIf (opGetModel key gs).base.sortSet ∗
          ⌜¬ opGetPanics gs ∧ (opGetModel key gs).t = W64 1⌝ ∗
          □ (⌜Q = fun _ => iprop(True)⌝ ∨
            (⌜(rangeWireOf (opGetModel key gs)).base.serializable = false⌝ ∗ kvReadAu γr.kv Q))) }}
        (App (App (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
            go!"Get")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #sl))
      {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗ (R ∗
          ((⌜err = GoInterface.nil⌝ ∗ ∃ m : RangeRespM, rangeRespMsg resp m ∗
              rangeReplyOk E γr c F (rangeWireOf (opGetModel key gs)) cid mid Q m ∗
              ∃ md, clientAttemptMd conn om md ∗
                v3rpc.rangeAuthed (srvTLSId s) E γr c n (auth.mdTokenOf md) (rangeWireOf (opGetModel key gs))) ∨
            (⌜err ≠ GoInterface.nil ∧ resp = null⌝ ∗ kvErr err))) }}

/-- `client_Txn_on`'s statement (`ClientOn.lean`, a linking module), as a hypothesis of the proofs
that use it (the import tiers); `client_Txn_on_law_holds` proves it. -/
abbrev client_Txn_on.law : Prop :=
  ∀ (cl api conn : Loc) (addr : GoString) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
          structFieldRef go_etcd_io.etcd.client.v3.Client go!"KV" cl ↦□
            (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty) #api :
              GoInterface) ∗
          kvObjAtC api conn [addr] ∗ ctxOk ci cd ∗ ctxErrClient ci cd }}
        (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
            go!"Txn")) (Val #(GoInterface.ok ci)))
      {{ (t : GoInterface), RET #t; ∃ tp : Loc,
          ⌜t = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.txn.ty) #tp⌝ ∗
          txnObjAt tp [addr] ci cd TxnBuild.empty ∗ txnKvIs tp api }}

end laws1

end etcd_auth
end EtcdGrove
end Perennial

namespace Perennial
namespace EtcdGrove
namespace etcd_auth

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver client

section laws2
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- `work_put`'s statement (`WorkCallsLinked.lean`, a linking module), as a hypothesis of the proofs
that use it (the import tiers); `work_put_law_holds` proves it. -/
abbrev work_put.law : Prop :=
  ∀ (cl api conn : Loc) (addr : GoString) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
      (cid mid : w64) (γa : auth.AuthNames) (Lset : List EntryModel) (n : Nat) (who : GoString)
      (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (k v : GoString)
      (hγa : E.authMode = .on γa)
      (hop : akOpGranted who (.put (putKeyOp k v)) → opHistOk (.put (putKeyOp k v)))
      (hsz : opSizeOk (opPutModel k v [])),
    {{ levelTok 0 ∗ (akCallEnv cl api conn addr s E ρ cid mid γa Lset n who ∗ metadata.outMD ci (akOut who) ∗
          ctxOk ci cd ∗ ctxErrClient ci cd) }}
        (App (App (App (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
            go!"Put")) (Val #(GoInterface.ok ci))) (Val #k)) (Val #v)) (Val #slice.nil))
      {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗ (⌜err = GoInterface.nil → akOpGranted who (.put (putKeyOp k v))⌝) }}

/-- `work_delete`'s statement (`WorkCallsLinked.lean`, a linking module), as a hypothesis of the
proofs that use it (the import tiers); `work_delete_law_holds` proves it. -/
abbrev work_delete.law : Prop :=
  ∀ (cl api conn : Loc) (addr : GoString) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
      (cid mid : w64) (γa : auth.AuthNames) (Lset : List EntryModel) (n : Nat) (who : GoString)
      (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (k : GoString) (hk : k ≠ [])
      (hγa : E.authMode = .on γa)
      (hop : akOpGranted who (.deleteRange (txn.deleteOpOf k [] false)) → opHistOk (.deleteRange (txn.deleteOpOf k [] false)))
      (hsz : opSizeOk (opDeleteModel k [])),
    {{ levelTok 0 ∗ (akCallEnv cl api conn addr s E ρ cid mid γa Lset n who ∗ metadata.outMD ci (akOut who) ∗
          ctxOk ci cd ∗ ctxErrClient ci cd) }}
        (App (App (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
            go!"Delete")) (Val #(GoInterface.ok ci))) (Val #k)) (Val #slice.nil))
      {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗ (⌜err = GoInterface.nil → akOpGranted who (.deleteRange (txn.deleteOpOf k [] false))⌝) }}

/-- `work_get`'s statement (`WorkCallsLinked.lean`, a linking module), as a hypothesis of the proofs
that use it (the import tiers); `work_get_law_holds` proves it. -/
abbrev work_get.law : Prop :=
  ∀ (cl api conn : Loc) (addr : GoString) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
      (cid mid : w64) (γa : auth.AuthNames) (Lset : List EntryModel) (n : Nat) (who : GoString)
      (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (key : GoString) (sl : GoSlice)
      (gs : List (OpFull → OpFull)) (hγa : E.authMode = .on γa)
     
      (hg : ¬ opGetPanics gs ∧ (opGetModel key gs).t = W64 1)
      (hs : (opGetModel key gs).base.sortSet = false) (hsz : opSizeOk (opGetModel key gs)),
    {{ levelTok 0 ∗ (akCallEnv cl api conn addr s E ρ cid mid γa Lset n who ∗ metadata.outMD ci (akOut who) ∗
          ctxOk ci cd ∗ ctxErrClient ci cd ∗
          optsAt sl gs) }}
        (App (App (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
            go!"Get")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #sl))
      {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗ (⌜err ≠ GoInterface.nil⌝ ∨
          (⌜err = GoInterface.nil⌝ ∗ ∃ m : RangeRespM, rangeRespMsg resp m ∗
            ⌜(∃ (r : Nat) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (e : GoString),
                akUser who info.Username' ∧
                apply.authEndOf (rangeWireOf (opGetModel key gs)).base.rangeEnd e ∧
                auth.granted (setupSt r) (auth.authInfoM info) (rangeWireOf (opGetModel key gs)).key
                  e .read) ∧
              ∀ kv ∈ m.kvs, inRange (rangeWireOf (opGetModel key gs)).key
                (rangeWireOf (opGetModel key gs)).base.rangeEnd kv.key = true⌝)) }}

/-- `work_commit`'s statement (`WorkCallsLinked.lean`, a linking module), as a hypothesis of the
proofs that use it (the import tiers); `work_commit_law_holds` proves it. -/
abbrev work_commit.law : Prop :=
  ∀ (cl api conn tp : Loc) (addr : GoString) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
      (cid mid : w64) (γa : auth.AuthNames) (Lset : List EntryModel) (n : Nat) (who : GoString)
      (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (b : TxnBuild)
      (hγa : E.authMode = .on γa)
      (hp : TxnModel.plain (txnWireOf b.model)) (hin : txnModelIn (txnWireOf b.model))
      (hsz : txnSizeOk (txnWireOf b.model))
      (hsh : ∀ tw : txn.TxnModelW, tw.toModel = txnWireOf b.model → kvShapeAll (irrTxn tw))
      (hro : txn.txnReadonly (txnWireOf b.model) = false)
      (hpl : txn.txnPlain (txnWireOf b.model) ∧ txnNoZeroEnd (txnWireOf b.model))
      (hop : akOpGranted who (.txn (txnWireOf b.model)) → opHistOk (.txn (txnWireOf b.model))),
    {{ levelTok 0 ∗ (akCallEnv cl api conn addr s E ρ cid mid γa Lset n who ∗ txnObjAt tp [addr] ci cd b ∗
          metadata.outMD ci (akOut who) ∗
          txnKvIs tp api) }}
        (App (Val (tp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.txn.ty @!! go!"Commit"))
          (Val #()))
      {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗ (⌜err = GoInterface.nil → akOpGranted who (.txn (txnWireOf b.model))⌝ ∗
          (⌜err ≠ GoInterface.nil⌝ ∨ ∃ m : TxnRespM, txnRespMsg resp m ∗
            ⌜∃ (r : w64) (s0 : List EtcdKv) (skip : Bool),
              m.succeeded = (txn.srvRunTxn r s0 (txnWireOf b.model)).1 ∧
              opRespsRel skip ((txnWireOf b.model).branch m.succeeded)
                (txn.srvRunTxn r s0 (txnWireOf b.model)).2.2 m.resps⌝)) }}

/-- `then_commit_nested_refused`'s statement (`WorkCallsLinked.lean`, a linking module), as a
hypothesis of the proofs that use it (the import tiers); `then_commit_nested_refused_law_holds`
proves it. -/
abbrev then_commit_nested_refused.law : Prop :=
  ∀ (cl api conn tp : Loc) (addr : GoString) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
      (cid mid : w64) (γa : auth.AuthNames) (Lset : List EntryModel) (n : Nat) (who : GoString)
      (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (sl tsl : GoSlice)
      (op : go_etcd_io.etcd.client.v3.Op) (hwho : who ∈ principals) (hγa : E.authMode = .on γa)
     ,
    {{ akCallEnv cl api conn addr s E ρ cid mid γa Lset n who ∗
          txnObjAt tp [addr] ci cd TxnBuild.empty ∗ metadata.outMD ci (akOut who) ∗ txnKvIs tp api ∗
          sl ↦*□ [op] ∗ opFullAt op OpFull.txnInit ∗ cmpsAt op.cmps' [] ∗
          ⌜op.thenOps' = tsl ∧ op.elseOps' = slice.nil⌝ ∗
          opsAt tsl [opPutModel (keyOfK go!"c" who go!"t3") go!"vt" []] }}
        (App (Val (tp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.txn.ty @!! go!"Then"))
          (Val #sl))
      {{ RET #(interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.txn.ty) #tp :
            GoInterface); ∀ Φ, levelTok 0 -∗
            (∀ (resp : Loc) (err : GoInterface), levelTok 0 -∗ ⌜err ≠ GoInterface.nil⌝ -∗
              Φ (PairV #resp #err)) -∗
            WP (App (Val (tp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.txn.ty @!!
              go!"Commit")) (Val #())) {{ Φ }} }}

end laws2

end etcd_auth
end EtcdGrove
end Perennial

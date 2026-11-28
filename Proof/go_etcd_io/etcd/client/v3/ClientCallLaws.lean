/-
**The client's linked calls, as hypotheses** (the import tiers, 2026-11-18): the statements of
`ClientPutGet.lean`'s calls through `New`'s client (`client_Get_st`, `client_Put_st`, ...) and of
`Results.lean`'s `client_range_any`, each as `<name>.law : Prop`, which a function's proof takes as a
hypothesis instead of importing those linking modules; `<name>_law_holds` (`ClientPutGet.lean`) proves
it, and the `Link`s pass it. Also `ClientPutGet.lean`'s lemmas that use no linked result
(`clientWriteOnce_api`, `srvRangeOk_getKeyRev`), moved here unchanged.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvClientNewResult
public import Proof.go_etcd_io.etcd.client.v3.InvServerKV
public import Proof.go_etcd_io.etcd.client.v3.KeyOps

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace client

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver

section laws1
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `client_range_any`'s statement (`Results.lean`, a linking module), as a hypothesis of the proofs
that use it (the import tiers); `client_range_any_law_holds` proves it. -/
abbrev client_range_any.law : Prop :=
  ∀ (api : Loc) (ms : List (SrvAt GF)) (c : w64) (ci : GoInterfaceOk)
      (cd : context.ContextDesc (IProp GF)) (key : GoString) (sl : GoSlice)
      (gs : List (OpFull → OpFull)) (R : IProp GF) (Q : KVState → IProp GF) (F : mvcc.Log)
      (hsz : opSizeOk (opGetModel key gs)),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗ (kvObjAt api (ms.map SrvAt.addr) ∗ ([∗list] x ∈ ms, kvRegsAt x) ∗
          ([∗list] x ∈ ms, committedAtLeast x.γr c ∗ srvApi.kvLogLb x.E.γs F) ∗
          ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAtRes sl gs R ∗ R ∗
          sortNamesIf (opGetModel key gs).base.sortSet ∗
          ⌜¬ opGetPanics gs ∧ (opGetModel key gs).t = W64 1⌝ ∗
          □ ([∧list] x ∈ ms, ⌜Q = fun _ => iprop(True)⌝ ∨
            (⌜(rangeWireOf (opGetModel key gs)).base.serializable = false⌝ ∗ kvReadAu x.γr.kv Q))) }}
        (App (App (App (Val (api @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!!
            go!"Get")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #sl))
      {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗ (R ∗
          ((⌜err = GoInterface.nil⌝ ∗ ∃ m : RangeRespM, rangeRespMsgO resp m ∗ ∃ x : SrvAt GF,
              ⌜x ∈ ms⌝ ∗ rangeReplyOk x.E x.γr c F (rangeWireOf (opGetModel key gs)) x.cid x.mid Q m) ∨
            (⌜err ≠ GoInterface.nil ∧ resp = null⌝ ∗ kvErr err)) ∗
          (⌜sortValid (opGetModel key gs) = true⌝ →
            rangeErrOut ms c F (rangeWireOf (opGetModel key gs)) Q err)) }}

end laws1

end client
end EtcdGrove
end Perennial

namespace Perennial
namespace EtcdGrove
namespace client

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver

section laws2
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `client_Get_st`'s statement (`ClientPutGet.lean`, a linking module), as a hypothesis of the
proofs that use it (the import tiers); `client_Get_st_law_holds` proves it. -/
abbrev client_Get_st.law : Prop :=
  ∀ (cl : Loc) (ms : List (SrvAt GF)) (V : WEnv GF) (ci : GoInterfaceOk)
      (cd : context.ContextDesc (IProp GF)) (key : GoString) (sl : GoSlice) (Q : KVState → IProp GF)
      (hsz : opSizeOk (opGetModel key [])),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗ (isNewClient cl (ms.map SrvAt.addr) V ∗
          ([∗list] x ∈ ms, kvRegsAt x) ∗ ([∗list] x ∈ ms, srvStart x) ∗
          ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAt sl [] ∗
          □ ([∧list] x ∈ ms, ⌜Q = fun _ => iprop(True)⌝ ∨ kvReadAu x.γr.kv Q)) }}
        (App (App (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
            go!"Get")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #sl))
      {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗ ((⌜err = GoInterface.nil⌝ ∗ ∃ (m : RangeRespM) (σ : KVState), rangeRespMsg resp m ∗
            □ Q σ ∗ ⌜m.kvs = σ.kvs.filter (fun v => decide (v.key = key)) ∧
              m.hdr.revision = W64 (σ.rev : Int) ∧ kvRevFits σ.rev⌝) ∨
            (⌜err ≠ GoInterface.nil⌝ ∗ kvErr err)) }}

/-- `client_Put_st`'s statement (`ClientPutGet.lean`, a linking module), as a hypothesis of the
proofs that use it (the import tiers); `client_Put_st_law_holds` proves it. -/
abbrev client_Put_st.law : Prop :=
  ∀ (cl : Loc) (ms : List (SrvAt GF)) (V : WEnv GF) (ci : GoInterfaceOk)
      (cd : context.ContextDesc (IProp GF)) (key val : GoString) (sl : GoSlice)
      (Q : KVState → IProp GF) (hsz : opSizeOk (opPutModel key val [])),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗ (isNewClient cl (ms.map SrvAt.addr) V ∗ clientWriteOnce cl (ms.map SrvAt.addr) ∗
          ([∗list] x ∈ ms, kvRegsAt x) ∗ ([∗list] x ∈ ms, srvApi.kvLogLb x.E.γs []) ∗
          ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAt sl [] ∗
          ([∧list] x ∈ ms, kvOpAu1 x.γr.kv (.put (putKeyOp key val)) Q)) }}
        (App (App (App (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
            go!"Put")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #val)) (Val #sl))
      {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗ ((⌜err = GoInterface.nil⌝ ∗ ∃ (m : PutRespM) (σ : KVState), putRespMsg resp m ∗ Q σ ∗
            ⌜m.hdr.revision = W64 ((σ.rev + 1 : Nat) : Int) ∧ kvRevFits (σ.rev + 1)⌝) ∨
            (⌜err ≠ GoInterface.nil⌝ ∗ kvErr err)) }}

/-- `client_Delete_st`'s statement (`ClientPutGet.lean`, a linking module), as a hypothesis of the
proofs that use it (the import tiers); `client_Delete_st_law_holds` proves it. -/
abbrev client_Delete_st.law : Prop :=
  ∀ (cl : Loc) (ms : List (SrvAt GF)) (V : WEnv GF) (ci : GoInterfaceOk)
      (cd : context.ContextDesc (IProp GF)) (key : GoString) (sl : GoSlice) (Q : KVState → IProp GF)
      (hsz : opSizeOk (opDeleteModel key [])),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗ (isNewClient cl (ms.map SrvAt.addr) V ∗ clientWriteOnce cl (ms.map SrvAt.addr) ∗
          ([∗list] x ∈ ms, kvRegsAt x) ∗ ([∗list] x ∈ ms, srvApi.kvLogLb x.E.γs []) ∗
          ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAt sl [] ∗
          ([∧list] x ∈ ms, kvOpAu1 x.γr.kv (.deleteRange (txn.deleteOpOf key [] false)) Q)) }}
        (App (App (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
            go!"Delete")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #sl))
      {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗ ((⌜err = GoInterface.nil⌝ ∗ ∃ (m : DelRespM) (σ : KVState), delRespMsg resp m ∗ Q σ ∗
            ⌜m.deleted = W64 ((rangeIn σ.kvs (txn.deleteOpOf key [] false)).length : Int) ∧
              m.hdr.revision =
                W64 ((kvOpStep (.deleteRange (txn.deleteOpOf key [] false)) σ).rev : Int) ∧
              kvRevFits (σ.rev + 1)⌝) ∨
            (⌜err ≠ GoInterface.nil⌝ ∗ kvErr err)) }}

/-- `client_Txn_st`'s statement (`ClientPutGet.lean`, a linking module), as a hypothesis of the
proofs that use it (the import tiers); `client_Txn_st_law_holds` proves it. -/
abbrev client_Txn_st.law : Prop :=
  ∀ (cl : Loc) (ms : List (SrvAt GF)) (V : WEnv GF) (ci : GoInterfaceOk)
      (cd : context.ContextDesc (IProp GF)),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗ (isNewClient cl (ms.map SrvAt.addr) V ∗ clientWriteOnce cl (ms.map SrvAt.addr) ∗
          ctxOk ci cd ∗ ctxErrClient ci cd) }}
        (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
            go!"Txn")) (Val #(GoInterface.ok ci)))
      {{ (t : GoInterface), RET #t; levelTok 0 ∗ (∃ tp : Loc,
          ⌜t = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.txn.ty) #tp⌝ ∗
          txnObjAt tp (ms.map SrvAt.addr) ci cd TxnBuild.empty ∗
          txnWriteOnce tp (ms.map SrvAt.addr)) }}

end laws2

end client
end EtcdGrove
end Perennial

namespace Perennial
namespace EtcdGrove
namespace client

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver

section laws3
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `client_Put_kv`'s statement (`ClientPutGet.lean`, a linking module), as a hypothesis of the
proofs that use it (the import tiers); `client_Put_kv_law_holds` proves it. -/
abbrev client_Put_kv.law : Prop :=
  ∀ (cl api : Loc) (γ : KVNames) (dup : Bool) (ci : GoInterfaceOk)
      (cd : context.ContextDesc (IProp GF)) (key val : GoString) (sl : GoSlice)
      (Q : KVState → IProp GF) (hsz : opSizeOk (opPutModel key val [])),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗ (structFieldRef go_etcd_io.etcd.client.v3.Client go!"KV" cl ↦□ GoInterface.ok (kvIfaceOf api) ∗
          isKv api γ dup ∗
          ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAt sl [] ∗
          □?dup (AU <{ ∃∃ (σ : KVState), etcdKV γ σ }> @ (⊤ \ ↑srvRaftN) \ ↑kvN, ∅
            <{ etcdKV γ (kvOpStep (.put (putWireOf (opPutModel key val []))) σ) ∗ ⌜kvRoom σ⌝,
              COMM Q σ }>)) }}
        (App (App (App (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
            go!"Put")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #val)) (Val #sl))
      {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗ ((⌜err = GoInterface.nil⌝ ∗ ∃ (m : PutRespM) (σ : KVState), putRespMsg resp m ∗ Q σ ∗
            ⌜m.hdr.revision = W64 ((σ.rev + 1 : Nat) : Int) ∧ kvRevFits (σ.rev + 1) ∧ kvLogOk σ ∧
              kvLogOk (kvOpStep (.put (putWireOf (opPutModel key val []))) σ)⌝ ∗
            kvRevLb γ m.hdr.revision) ∨
            (⌜err ≠ GoInterface.nil⌝ ∗ kvErr err)) }}

/-- `client_Compact_kv`'s statement (`ClientPutGet.lean`, a linking module), as a hypothesis of the
proofs that use it (the import tiers); `client_Compact_kv_law_holds` proves it. -/
abbrev client_Compact_kv.law : Prop :=
  ∀ (cl api : Loc) (γ : KVNames) (dup : Bool) (ci : GoInterfaceOk)
      (cd : context.ContextDesc (IProp GF)) (rev : w64) (hr : 1 ≤ sint.Z rev) (hc : γ.cmp = true),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗ (structFieldRef go_etcd_io.etcd.client.v3.Client go!"KV" cl ↦□ GoInterface.ok (kvIfaceOf api) ∗
          isKv api γ dup ∗ ctxOk ci cd ∗ ctxErrClient ci cd ∗ kvRevLbZ γ (sint.Z rev + γ.cret)) }}
        (App (App (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
            go!"Compact")) (Val #(GoInterface.ok ci))) (Val #rev)) (Val #slice.nil))
      {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗ ((⌜err = GoInterface.nil⌝ ∗ ∃ m : CompactRespM, compactRespMsg resp m) ∨
            (⌜err ≠ GoInterface.nil ∧ resp = null⌝ ∗ kvErr err)) }}

/-- `client_Get_kv`'s statement (`ClientPutGet.lean`, a linking module), as a hypothesis of the
proofs that use it (the import tiers); `client_Get_kv_law_holds` proves it. -/
abbrev client_Get_kv.law : Prop :=
  ∀ (cl api : Loc) (γ : KVNames) (dup : Bool) (ci : GoInterfaceOk)
      (cd : context.ContextDesc (IProp GF)) (key : GoString) (rev : w64) (sl : GoSlice)
      (Q : KVState → IProp GF) (hsz : opSizeOk (opGetModel key [withRevM rev])),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗ (structFieldRef go_etcd_io.etcd.client.v3.Client go!"KV" cl ↦□ GoInterface.ok (kvIfaceOf api) ∗
          isKv api γ dup ∗ ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAt sl [withRevM rev] ∗
          kvReadAu γ Q) }}
        (App (App (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
            go!"Get")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #sl))
      {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗ ((⌜err = GoInterface.nil⌝ ∗ ∃ (m : RangeRespM) (σ : KVState), rangeRespMsg resp m ∗
            □ Q σ ∗ ⌜sint.Z rev ≤ (σ.rev : Int) ∧
              m.kvs = (σ.at (σ.readRev rev)).kvs.filter (fun v => decide (v.key = key))⌝) ∨
            (⌜err ≠ GoInterface.nil ∧ resp = null⌝ ∗ kvErr err)) }}

end laws3

end client
end EtcdGrove
end Perennial

namespace Perennial
namespace EtcdGrove
namespace client

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver

section laws4
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- A write through `New`'s client sent at most once (D29): its `*kv`'s (`KV` field's). -/
theorem clientWriteOnce_api (cl api : Loc) (addrs : List GoString) :
    clientF cl go!"KV" ↦□
        interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty) #api ∗
      clientWriteOnce (GF := GF) cl addrs ⊢ writeOnce api addrs := by
  iintro ⟨-, #Hw⟩
  iunfold clientWriteOnce at Hw
  iunfold writeOnce
  iexact Hw

end laws4

end client
end EtcdGrove
end Perennial

namespace Perennial
namespace EtcdGrove
namespace client

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver

section laws5
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- The get of one key at revision `rev` selects the key's key-values of the store it reads, as
the get at the latest (pure; `srvRangeOk_getKey`: the selection does not read the revision). -/
theorem srvRangeOk_getKeyRev (key : GoString) (rev : w64) (s kvs : List EtcdKv) (more : Bool)
    (h : txn.srvRangeOk (rangeWireOf (opGetModel key [withRevM rev])) s kvs more) :
    kvs = s.filter (fun v => decide (v.key = key)) := by
  generalize ho : rangeWireOf (opGetModel key [withRevM rev]) = o at h
  have ho' : o = { getKeyOp key with base := { (getKeyOp key).base with rev := rev } } := by
    rw [← ho]; rfl
  subst ho'
  obtain ⟨L, hsort, hmore, hkvs⟩ := h
  have hpre : txn.srvPre { getKeyOp key with base := { (getKeyOp key).base with rev := rev } } s =
      s.filter (fun v => decide (v.key = key)) := by
    have hr : txn.kvRead false = id := by funext v; simp [txn.kvRead]
    unfold txn.srvPre
    simp [txn.rangeLimitOf, txn.hasRevFilters, mvcc.limitOf, mvcc.takeLimit, txn.fastKeysOnly,
      rangeIn, inRange, hr]
    apply List.filter_congr
    intro v _
    simp [kvFilterOk]
  have hord : ({ getKeyOp key with base := { (getKeyOp key).base with rev := rev } } :
      OpFull).effSortOrder = W64 0 := by
    simp [OpFull.effSortOrder]
  have hL : L = txn.srvPre { getKeyOp key with base := { (getKeyOp key).base with rev := rev } } s := by
    obtain ⟨-, -, -, h4⟩ := hsort
    exact h4 (by rw [hord]; decide) (by rw [hord]; decide)
  have hm : txn.srvMore { getKeyOp key with base := { (getKeyOp key).base with rev := rev } } L =
      false := by
    simp [txn.srvMore]
  rw [hkvs]
  unfold txn.srvTrunc
  rw [hm, hL, hpre]
  have hresp : ∀ o : OpFull, o.keysOnly = false → txn.respKv o = id := fun o h => by
    funext v; simp [txn.respKv, h]
  rw [hresp _ rfl]
  simp

end laws5

end client
end EtcdGrove
end Perennial

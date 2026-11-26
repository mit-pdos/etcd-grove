/-
`Work`'s calls at the cluster view (F7 stage S11; `Work.wp_proof_dist`, `WorkDist.lean`): the dist copies of
`WorkCallsLinked.lean`'s `work_put`, `work_delete`, `work_get`, `work_commit`, with the same posts, each over
its auth-on contract taken as a hypothesis (`KV_PutOn_dist`, `KV_DeleteOn_dist`, `KV_GetOn_dist`,
`Txn_CommitOn_dist`). The call environment `akCallEnvD` is what `akDistEnv` gives a principal's client at
one endpoint: the KV and history invariants, the frozen history after the set-up's prefix `Lset` (auth
state `setupSt r`), `Lset`'s lower bound, the view's facts and the principal's premise (`akPrin`). A write's
update is `akWriteAuD` at `L₀ := Lset` (its result: the write granted to `who`); a get's check
(`readCheckedD`) is read at the frozen history (`readCheckedD_granted`: `setupSt r`'s grant to a user of
`who`'s), as `work_get`'s `akRead_granted`.

T4's commit (`commit_t4D.law`) is a hypothesis: `Txn_CommitOn_dist` takes `TxnModel.plain b.model`, which T4's
nested transaction is not (`notes/etcd-dist-f7.md`, "Handoff W-3"). Lean-first.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.AuthRunWrites
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.AuthLeaseDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.auth.WorkCalls
public import Proof.go_etcd_io.etcd.client.v3.InvOpLemmas
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.KVPutOnDist
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.KVDeleteOnDist
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.KVGetOnDist
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.TxnCommitOnDist

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_auth

open Iris Iris.BI Iris.ProofMode Net client go_etcd_io.etcd.server.v3.etcdserver
open etcd_dist etcd_dist.authd etcd_dist_client

section pure
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]

/-- **`Work.spec_dist`'s principal premise**: anonymous, or for `u` and `v`, `who` itself. -/
def akPrin (who : GoString) (P : Option GoString) : Prop :=
  P = none ∨ (P = some who ∧ (who = go!"u" ∨ who = go!"v"))

theorem akPrin_bad {who : GoString} {P : Option GoString} (h : akPrin who P) :
    who = go!"bad" → P = none := by
  intro hb
  rcases h with h | ⟨-, hw⟩
  · exact h
  · subst hb; rcases hw with h | h <;> exact absurd h (by decide)

theorem akPrin_user {who : GoString} {P : Option GoString} (h : akPrin who P) :
    ∀ u, userOk P u → akUser who u := by
  rcases h with rfl | ⟨rfl, hw⟩
  · exact userOk_none_akUser who
  · exact userOk_some_akUser who hw

theorem akPrin_three {who : GoString} {P : Option GoString} (h : akPrin who P) :
    P = none ∨ P = some go!"u" ∨ P = some go!"v" := by
  rcases h with h | ⟨rfl, rfl | rfl⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

/-- `OpDelete(k)`'s request. -/
theorem deleteWire_nil (k : GoString) : deleteWireOf (opDeleteModel k []) = txn.deleteOpOf k [] false := by
  simp [op_simps, deleteWireOf, txn.deleteOpOf]

/-- **A read of `[a, b)` granted at `setupSt` to a user of `who`'s is `u`'s** (`read_ab_u`, a user's name). -/
theorem read_ab_uD (who : GoString)
    (h : ∃ (r : Nat) (user : GoString) (rv : Nat) (e : GoString),
      akUser who user ∧ apply.authEndOf hi e ∧ auth.granted (setupSt r) ⟨user, rv⟩ lo e .read) :
    who = go!"u" := by
  obtain ⟨r, user, rv, e, hu, he, hg⟩ := h
  rcases he with rfl | ⟨-, h0⟩
  · exact granted_ab_u r who _ _ hu hg
  · exact absurd h0 (by decide)

/-- **No read of `[c/, c0)` is granted at `setupSt` to a user of `who`'s.** -/
theorem read_c_refusedD (who : GoString)
    (h : ∃ (r : Nat) (user : GoString) (rv : Nat) (e : GoString),
      akUser who user ∧ apply.authEndOf go!"c0" e ∧ auth.granted (setupSt r) ⟨user, rv⟩ go!"c/" e .read) :
    False := by
  obtain ⟨r, user, rv, e, hu, he, hg⟩ := h
  rcases he with rfl | ⟨-, h0⟩
  · exact not_granted_c r who _ _ hu hg
  · exact absurd h0 (by decide)

/-- **No read of `[a, d)` is granted at `setupSt` to a user of `who`'s.** -/
theorem read_past_refusedD (who : GoString)
    (h : ∃ (r : Nat) (user : GoString) (rv : Nat) (e : GoString),
      akUser who user ∧ apply.authEndOf go!"d" e ∧ auth.granted (setupSt r) ⟨user, rv⟩ lo e .read) :
    False := by
  obtain ⟨r, user, rv, e, hu, he, hg⟩ := h
  rcases he with rfl | ⟨-, h0⟩
  · exact not_granted_past r who _ _ hu hg
  · exact absurd h0 (by decide)

end pure

section env
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **A principal's call environment at the cluster view** (see the file header). -/
def akCallEnvD [NetProtoGS] (cl api : Loc) (a : GoString) (V : WEnv GF) (Γ : DistView)
    (cfg : go_etcd_io.etcd.client.v3.Config) (γR : ServerRaftNames) (who : GoString) (γz : GName)
    (hs : List auth.AuthState) (Lset : List EntryModel) (r : Nat) : IProp GF :=
  iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ etcd_dist.authd.userClientAt cl api [a] V Γ cfg ∗
    kvInvOn γR Γ.kv srvAuthSt0 ∗ akHistInv Γ.kv ∗ authHistFrozen Γ.kv γz hs ∗ srvReqLogLb γR Lset ∗
    ⌜admStates Γ.kv srvAuthSt0 Lset = hs ∧ srvAuthAtLog Γ.kv srvAuthSt0 Lset = setupSt r ∧
      γR.raft.log = Γ.kv.rlog ∧ Γ.auth = true ∧ (∀ x y : w64, Γ.au x = Γ.au y → x = y) ∧
      akPrin who (principalOf cfg)⌝)

instance akCallEnvD_persistent [NetProtoGS] (cl api : Loc) (a : GoString) (V : WEnv GF) (Γ : DistView)
    (cfg : go_etcd_io.etcd.client.v3.Config) (γR : ServerRaftNames) (who : GoString) (γz : GName)
    (hs : List auth.AuthState) (Lset : List EntryModel) (r : Nat) :
    Persistent (akCallEnvD (GF := GF) cl api a V Γ cfg γR who γz hs Lset r) := by
  unfold akCallEnvD; infer_instance

/-- **The call environment from the principals' environment** (`Work.spec_dist`'s premises). -/
theorem akCallEnvD_of [NetProtoGS] (cl api : Loc) (a : GoString) (addrs : List GoString) (V : WEnv GF)
    (Γ : DistView) (cfg : go_etcd_io.etcd.client.v3.Config) (γR : ServerRaftNames) (who : GoString)
    (hauth : Γ.auth = true) (hau : ∀ x y : w64, Γ.au x = Γ.au y → x = y)
    (hP : akPrin who (principalOf cfg)) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ etcd_dist.authd.userClientAt cl api [a] V Γ cfg ∗
      akDistEnv addrs Γ γR ⊢
      ∃ (γz : GName) (hs : List auth.AuthState) (Lset : List EntryModel) (r : Nat),
        akCallEnvD cl api a V Γ cfg γR who γz hs Lset r := by
  iintro ⟨#Pc, #Huc, #Henv⟩
  iunfold akDistEnv at Henv
  icases Henv with ⟨%γz, %hs, %Lset, %r, #HkvI, #Hhist, #Hfz, #HL, -, %Hset⟩
  obtain ⟨hadm, hst, hγR⟩ := Hset
  iexists γz, hs, Lset, r
  iunfold akCallEnvD
  iframe #
  ipureintro
  exact ⟨hadm, hst, hγR, hauth, hau, hP⟩

/-- **A get's check, read at the frozen history** (`↑kvN`, `↑authHistN` in the mask): `setupSt r`'s grant
of the range to a user of `who`'s. -/
theorem readCheckedD_granted [NetProtoGS] (eps : List GoString) (Γ : DistView) (γR : ServerRaftNames)
    (who : GoString) (P : Option GoString) (Lset : List EntryModel) (γz : GName) (hs : List auth.AuthState)
    (r : Nat) (o : OpFull) (hadm : admStates Γ.kv srvAuthSt0 Lset = hs)
    (hst : srvAuthAtLog Γ.kv srvAuthSt0 Lset = setupSt r) (hPw : ∀ u, userOk P u → akUser who u)
    (E : CoPset) (hE1 : ↑kvN ⊆ E) (hE2 : ↑authHistN ⊆ E) :
    ⊢ kvInvOn (GF := GF) γR Γ.kv srvAuthSt0 -∗ authHistFrozen Γ.kv γz hs -∗
      readCheckedD eps Γ γR P Lset o ={E}=∗
      ⌜∃ (r' : Nat) (user : GoString) (rv : Nat) (e : GoString), akUser who user ∧
        apply.authEndOf o.base.rangeEnd e ∧ auth.granted (setupSt r') ⟨user, rv⟩ o.key e .read⌝ := by
  iintro #Hinv #Hfz Hc
  iunfold readCheckedD at Hc
  icases Hc with ⟨%mid, %info, %m, %L, -, %Hp, #HL, -, -⟩
  obtain ⟨-, user, e, rv, hu, hpre, he, hperm⟩ := Hp
  imod authHistLb_of_reqLogLb γR Γ.kv srvAuthSt0 L E hE1 $$ Hinv HL with #Hlb
  imod authHistFrozen_prefix Γ.kv γz hs _ E hE2 $$ Hfz Hlb with %hp
  imodintro
  ipureintro
  have hL := srvAuthAtLog_frozen Γ.kv Lset Lset L hs (List.prefix_refl _) hpre hadm hp
  rw [hL, hst] at hperm
  refine ⟨r, user, rv, e, hPw _ hu, he, ?_⟩
  rcases hperm with hd | hg
  · simp [setupSt] at hd
  · exact hg

end env

section calls
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

set_option maxHeartbeats 800000 in
/-- **`cli.Put(ctx, k, v)` of `who`'s at the cluster view** (`work_put`'s post): a reply with no error was
granted to `who`. -/
theorem work_putD (wp_Put : KV_PutOn_dist.spec (GF := GF) (hG := hG)) [NetProtoGS]
    (cl api : Loc) (a : GoString) (V : WEnv GF) (Γ : DistView) (cfg : go_etcd_io.etcd.client.v3.Config)
    (γR : ServerRaftNames) (who : GoString) (γz : GName) (hs : List auth.AuthState) (Lset : List EntryModel)
    (r : Nat) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (k v : GoString)
    (hop : akOpGranted who (.put (putKeyOp k v)) → opHistOk (.put (putKeyOp k v)))
    (hsz : opSizeOk (opPutModel k v [])) :
    {{ levelTok 0 ∗ akCallEnvD cl api a V Γ cfg γR who γz hs Lset r ∗ metadata.outMD ci (akOut who) ∗
          ctxOk ci cd ∗ ctxErrClient ci cd }}
      (App (App (App (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
          go!"Put")) (Val #(GoInterface.ok ci))) (Val #k)) (Val #v)) (Val #slice.nil))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗
        ⌜err = GoInterface.nil → akOpGranted who (.put (putKeyOp k v))⌝ }} := by
  iintro %Φ ⟨Hlt, #Henv, #Hom, #Hctx, #Hce⟩ HΦ
  iunfold akCallEnvD at Henv
  icases Henv with ⟨#Pc, #Huc, #HkvI, #Hinv, #Hfz, #HL, %Hf⟩
  obtain ⟨hadm, hst, hγR, hauth, hau, hP⟩ := Hf
  ihave #Huc' := Huc
  iunfold etcd_dist.authd.userClientAt at Huc'
  icases Huc' with ⟨#Hkc, -⟩
  iunfold kvClientAt at Hkc
  icases Hkc with ⟨-, -, #Hkvf, -⟩
  ihave #Hw := akWriteAuD Γ.kv γz hs Lset Lset r (principalOf cfg) who (.put (putKeyOp k v))
    (List.prefix_refl _) hadm hst (akPrin_user hP) hop $$ [Hinv Hfz]
  · iframe #
  ihave #Hnil := optsAt_nil (GF := GF)
  rw [go_etcd_io.etcd.client.v3.Client.TypeAssumptions.ptr_Put_unfold.method_unfold]
  wp_pures
  wp_auto
  wp_apply (wp_Put cl api [a] V Γ cfg γR Lset ci cd (akOut who) k v slice.nil []
      (fun _ => iprop(⌜akOpGranted who (.put (putKeyOp k v))⌝)) hauth hγR
      (outTokOk_reqMd _ who (akPrin_bad hP))) $$ [Hlt] as %resp %err ⟨Hlt, Hout⟩
  · iframe Hlt
    iframe #
    isplitl []
    · ipureintro
      refine ⟨not_putPanics k v, rfl, Or.inl ?_⟩
      simp [opPutModel, putWireOf, opFold, OpFull.putInit, OpFull.newOp, OpModel.zero]
    isplitl []
    · rw [show putWireOf (opPutModel k v []) = putKeyOp k v from rfl]
      iexact Hw
    ipureintro; exact hsz
  iapply HΦ
  iframe Hlt
  icases Hout with (⟨%Herr, %m, %σ, -, %HQ, -⟩ | %Herr)
  · ipureintro; intro _; exact HQ
  · ipureintro; intro h; exact absurd h Herr.1

set_option maxHeartbeats 800000 in
/-- **`cli.Delete(ctx, k)` of `who`'s at the cluster view** (`work_delete`'s post). -/
theorem work_deleteD (wp_Delete : KV_DeleteOn_dist.spec (GF := GF) (hG := hG)) [NetProtoGS]
    (cl api : Loc) (a : GoString) (V : WEnv GF) (Γ : DistView) (cfg : go_etcd_io.etcd.client.v3.Config)
    (γR : ServerRaftNames) (who : GoString) (γz : GName) (hs : List auth.AuthState) (Lset : List EntryModel)
    (r : Nat) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (k : GoString)
    (hop : akOpGranted who (.deleteRange (txn.deleteOpOf k [] false)) →
      opHistOk (.deleteRange (txn.deleteOpOf k [] false)))
    (hsz : opSizeOk (opDeleteModel k [])) :
    {{ levelTok 0 ∗ akCallEnvD cl api a V Γ cfg γR who γz hs Lset r ∗ metadata.outMD ci (akOut who) ∗
          ctxOk ci cd ∗ ctxErrClient ci cd }}
      (App (App (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
          go!"Delete")) (Val #(GoInterface.ok ci))) (Val #k)) (Val #slice.nil))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗
        ⌜err = GoInterface.nil → akOpGranted who (.deleteRange (txn.deleteOpOf k [] false))⌝ }} := by
  iintro %Φ ⟨Hlt, #Henv, #Hom, #Hctx, #Hce⟩ HΦ
  iunfold akCallEnvD at Henv
  icases Henv with ⟨#Pc, #Huc, #HkvI, #Hinv, #Hfz, #HL, %Hf⟩
  obtain ⟨hadm, hst, hγR, hauth, hau, hP⟩ := Hf
  ihave #Huc' := Huc
  iunfold etcd_dist.authd.userClientAt at Huc'
  icases Huc' with ⟨#Hkc, -⟩
  iunfold kvClientAt at Hkc
  icases Hkc with ⟨-, -, #Hkvf, -⟩
  ihave #Hw := akWriteAuD Γ.kv γz hs Lset Lset r (principalOf cfg) who
    (.deleteRange (txn.deleteOpOf k [] false)) (List.prefix_refl _) hadm hst (akPrin_user hP) hop
    $$ [Hinv Hfz]
  · iframe #
  ihave #Hnil := optsAt_nil (GF := GF)
  rw [go_etcd_io.etcd.client.v3.Client.TypeAssumptions.ptr_Delete_unfold.method_unfold]
  wp_pures
  wp_auto
  wp_apply (wp_Delete cl api [a] V Γ cfg γR Lset ci cd (akOut who) k slice.nil []
      (fun _ => iprop(⌜akOpGranted who (.deleteRange (txn.deleteOpOf k [] false))⌝)) hauth hγR
      (outTokOk_reqMd _ who (akPrin_bad hP))) $$ [Hlt] as %resp %err ⟨Hlt, Hout⟩
  · iframe Hlt
    iframe #
    isplitl []
    · ipureintro
      refine ⟨?_, rfl, ?_⟩
      · simp [op_simps, opDeletePanics, opGetPanics, OpFull.deletePanics]
      · simp [op_simps, deleteWireOf, txn.deleteOpOf]
    isplitl []
    · rw [deleteWire_nil]
      iexact Hw
    ipureintro; exact hsz
  iapply HΦ
  iframe Hlt
  icases Hout with (⟨%Herr, %m, %σ, -, %HQ, -⟩ | %Herr)
  · ipureintro; intro _; exact HQ
  · ipureintro; intro h; exact absurd h Herr.1

set_option maxHeartbeats 800000 in
/-- **`cli.Get(ctx, key, opts...)` of `who`'s at the cluster view** (no sort, no panic, linearizable;
`work_get`'s post, the grant's principal a user's name and revision): a reply with no error was granted at
`setupSt` to a user of `who`'s (`readCheckedD_granted`), and its keys are in the request's range. -/
theorem work_getD (wp_Get : KV_GetOn_dist.spec (GF := GF) (hG := hG)) [NetProtoGS]
    (cl api : Loc) (a : GoString) (V : WEnv GF) (Γ : DistView) (cfg : go_etcd_io.etcd.client.v3.Config)
    (γR : ServerRaftNames) (who : GoString) (γz : GName) (hs : List auth.AuthState) (Lset : List EntryModel)
    (r : Nat) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (key : GoString) (sl : GoSlice)
    (gs : List (OpFull → OpFull))
    (hg : ¬ opGetPanics gs ∧ (opGetModel key gs).t = W64 1)
    (hso : (opGetModel key gs).base.sortSet = false)
    (hser : (rangeWireOf (opGetModel key gs)).base.serializable = false)
    (hsz : opSizeOk (opGetModel key gs)) :
    {{ levelTok 0 ∗ akCallEnvD cl api a V Γ cfg γR who γz hs Lset r ∗ metadata.outMD ci (akOut who) ∗
          ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAt sl gs }}
      (App (App (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
          go!"Get")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗ (
        ⌜err ≠ GoInterface.nil⌝ ∨
        (⌜err = GoInterface.nil⌝ ∗ ∃ m : RangeRespM, rangeRespMsg resp m ∗
          ⌜(∃ (r' : Nat) (user : GoString) (rv : Nat) (e : GoString), akUser who user ∧
              apply.authEndOf (rangeWireOf (opGetModel key gs)).base.rangeEnd e ∧
              auth.granted (setupSt r') ⟨user, rv⟩ (rangeWireOf (opGetModel key gs)).key e .read) ∧
            ∀ kv ∈ m.kvs, inRange (rangeWireOf (opGetModel key gs)).key
              (rangeWireOf (opGetModel key gs)).base.rangeEnd kv.key = true⌝)) }} := by
  iintro %Φ ⟨Hlt, #Henv, #Hom, #Hctx, #Hce, #Hopts⟩ HΦ
  iunfold akCallEnvD at Henv
  icases Henv with ⟨#Pc, #Huc, #HkvI, #Hinv, #Hfz, #HL, %Hf⟩
  obtain ⟨hadm, hst, hγR, hauth, hau, hP⟩ := Hf
  ihave #Huc' := Huc
  iunfold etcd_dist.authd.userClientAt at Huc'
  icases Huc' with ⟨#Hkc, -⟩
  iunfold kvClientAt at Hkc
  icases Hkc with ⟨-, -, #Hkvf, -⟩
  ihave Hres := optsAt_res sl gs iprop(True) $$ Hopts
  rw [go_etcd_io.etcd.client.v3.Client.TypeAssumptions.ptr_Get_unfold.method_unfold]
  wp_pures
  wp_auto
  iapply wp_fupd
  wp_apply (wp_Get cl api [a] V Γ cfg γR Lset ci cd (akOut who) key sl gs iprop(True)
      (fun _ => iprop(True)) hau hauth hγR (outTokOk_reqMd _ who (akPrin_bad hP)))
    $$ [Hlt Hres] as %resp %err ⟨Hlt, -, Hout⟩
  · iframe Hlt Hres
    iframe #
    isplitl []
    · itrivial
    rw [hso]
    isplitl []
    · iapply sortNamesIf_false
    isplitl []
    · ipureintro; exact ⟨hg.1, hg.2, hser⟩
    isplitl []
    · iintro !>
      ileft
      ipureintro; rfl
    ipureintro; exact hsz
  icases Hout with (⟨%Herr, %m, %σ, #Hm, -, %Hs, Hck⟩ | %Herr)
  · imod (readCheckedD_granted [a] Γ γR who (principalOf cfg) Lset γz hs r _ hadm hst (akPrin_user hP) ⊤
      (fun _ _ => CoPset.mem_full) (fun _ _ => CoPset.mem_full)) $$ HkvI Hfz Hck with %Hg
    imodintro
    iapply HΦ
    iframe Hlt
    iright
    isplitl []
    · ipureintro; exact Herr
    iexists m
    iframe Hm
    ipureintro
    exact ⟨Hg, srvRangeOk_keys _ _ _ _ Hs.2.1⟩
  · imodintro
    iapply HΦ
    iframe Hlt
    ileft
    ipureintro; exact Herr.1

set_option maxHeartbeats 800000 in
/-- **`t.Commit()` of `who`'s writing transaction at the cluster view** (plain, no range end `[0]`;
`work_commit`'s post). -/
theorem work_commitD (wp_Commit : Txn_CommitOn_dist.spec (GF := GF) (hG := hG)) [NetProtoGS]
    (cl api tp : Loc) (a : GoString) (V : WEnv GF) (Γ : DistView) (cfg : go_etcd_io.etcd.client.v3.Config)
    (γR : ServerRaftNames) (who : GoString) (γz : GName) (hs : List auth.AuthState) (Lset : List EntryModel)
    (r : Nat) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (b : TxnBuild)
    (hp0 : TxnModel.plain b.model) (hin : txnModelIn (txnWireOf b.model))
    (hsz : txnSizeOk (txnWireOf b.model))
    (hro : txn.txnReadonly (txnWireOf b.model) = false)
    (hpl : txn.txnPlain (txnWireOf b.model) ∧ txnNoZeroEnd (txnWireOf b.model))
    (hop : akOpGranted who (.txn (txnWireOf b.model)) → opHistOk (.txn (txnWireOf b.model))) :
    {{ levelTok 0 ∗ akCallEnvD cl api a V Γ cfg γR who γz hs Lset r ∗ txnObjAt tp [a] ci cd b ∗
          metadata.outMD ci (akOut who) ∗ txnKvIs tp api }}
      (App (Val (tp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.txn.ty @!! go!"Commit"))
        (Val #()))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗ (
        ⌜err = GoInterface.nil → akOpGranted who (.txn (txnWireOf b.model))⌝ ∗
        (⌜err ≠ GoInterface.nil⌝ ∨ ∃ m : TxnRespM, txnRespMsg resp m ∗
          ⌜∃ (r : w64) (s0 : List EtcdKv) (skip : Bool),
            m.succeeded = (txn.srvRunTxn r s0 (txnWireOf b.model)).1 ∧
            opRespsRel skip ((txnWireOf b.model).branch m.succeeded)
              (txn.srvRunTxn r s0 (txnWireOf b.model)).2.2 m.resps⌝)) }} := by
  iintro %Φ ⟨Hlt, #Henv, Hobj, #Hom, #Hkt⟩ HΦ
  iunfold akCallEnvD at Henv
  icases Henv with ⟨#Pc, #Huc, #HkvI, #Hinv, #Hfz, #HL, %Hf⟩
  obtain ⟨hadm, hst, hγR, hauth, hau, hP⟩ := Hf
  ihave #Hw := akWriteAuD Γ.kv γz hs Lset Lset r (principalOf cfg) who (.txn (txnWireOf b.model))
    (List.prefix_refl _) hadm hst (akPrin_user hP) hop $$ [Hinv Hfz]
  · iframe #
  wp_apply (wp_Commit cl api tp [a] V Γ cfg γR Lset ci cd (akOut who) b
      (fun _ => iprop(⌜akOpGranted who (.txn (txnWireOf b.model))⌝)) hau hauth hγR
      (outTokOk_reqMd _ who (akPrin_bad hP))) $$ [Hlt Hobj] as %resp %err ⟨Hlt, Hout⟩
  · iframe Hlt Hobj
    iframe #
    isplitl []
    · ipureintro; exact ⟨hp0, hin⟩
    isplitl []
    · iright
      ipureintro; exact ⟨hro, Or.inl hpl.1, hpl.2⟩
    ipureintro; exact hsz
  iapply HΦ
  iframe Hlt
  icases Hout with (⟨%Herr, %m, %σ, #Hm, HQ, %Hs, -⟩ | %Herr)
  · isimp only [hro, Bool.false_eq_true, ↓reduceIte] at HQ
    icases HQ with %HQ
    isplitl []
    · ipureintro; intro _; exact HQ
    iright
    iexists m
    iframe Hm
    ipureintro
    exact ⟨_, _, false, Hs.1, Hs.2.1⟩
  · isplitl []
    · ipureintro; intro h; exact absurd h Herr.1
    ileft; ipureintro; exact Herr.1

end calls

section law
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **T4 at the cluster view, refused** (`then_commit_nested_refused.law` at `akCallEnvD`): `t.Then(OpTxn(nil,
[OpPut(c/who/t3, "vt")], nil))` returns the builder, whose `Commit` replies with an error. Not provable from
the auth-on contracts: `Txn_CommitOn_dist` takes `TxnModel.plain b.model`, and T4's then branch is a nested
transaction (`t4M`), not plain (the in-process `client_txn_on` has no such premise). A hypothesis of
`Work.wp_proof_dist` until the contract admits nested writing transactions (`notes/etcd-dist-f7.md`,
"Handoff W-3"). -/
abbrev then_commit_nested_refusedD.law : Prop :=
  ∀ [NetProtoGS] (cl api tp : Loc) (a : GoString) (V : WEnv GF) (Γ : DistView)
      (cfg : go_etcd_io.etcd.client.v3.Config) (γR : ServerRaftNames) (who : GoString) (γz : GName)
      (hs : List auth.AuthState) (Lset : List EntryModel) (r : Nat) (ci : GoInterfaceOk)
      (cd : context.ContextDesc (IProp GF)) (sl tsl : GoSlice) (op : go_etcd_io.etcd.client.v3.Op),
    who ∈ principals →
    {{ akCallEnvD cl api a V Γ cfg γR who γz hs Lset r ∗
          txnObjAt tp [a] ci cd TxnBuild.empty ∗ metadata.outMD ci (akOut who) ∗ txnKvIs tp api ∗
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

end law

end etcd_auth
end EtcdGrove
end Perennial

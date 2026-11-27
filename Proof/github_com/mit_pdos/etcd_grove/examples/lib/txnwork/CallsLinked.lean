/-
The calls by `New`'s client (`client_List_st`, `txn_Commit_st`), over the client's linked results,
moved out of `Calls.lean` (2026-11-18) so that the definitions there (`GenIn`, `callUpd`, ...),
which specs name, import no linked result (CLAUDE.md, "Import tiers"). See `Calls.lean`'s header.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.txnwork.Calls
public import Proof.go_etcd_io.etcd.client.v3.ClientPutGet
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.txnwork.CallsLaws

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_txnlin

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open go_etcd_io.etcd.server.v3.etcdserver mvcc
open client (srvStart srvStart_both kvRegs_range kvRegs_txn)

/-! ## Pure part -/

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
-- (2026-10-22) the client's and the server's package assumptions, not linkvtxn's: any caller of
-- `New`'s client uses these calls (also `client/v3/kubernetes`)
variable [go_etcd_io.etcd.client.v3.Assumptions]
variable [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- `cli.Get(ctx, listFrom, WithRange(listTo))` by `New`'s client of the members `ms`, with a read
update or none (see the file header). -/
theorem client_List_st [go_etcd_io.etcd.cache.v3.Assumptions] (cl : Loc)
    (ms : List (client.SrvAt GF)) (V : client.WEnv GF) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (sl : GoSlice) (Q : KVState → IProp GF)
    (hsz : opSizeOk (opGetModel listFrom [withRangeM listTo])) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
        isNewClient cl (ms.map client.SrvAt.addr) V ∗
        ([∗list] x ∈ ms, client.kvRegsAt x) ∗ ([∗list] x ∈ ms, srvStart x) ∗
        ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAt sl [withRangeM listTo] ∗
        □ ([∧list] x ∈ ms, ⌜Q = fun _ => iprop(True)⌝ ∨ kvReadAu x.γr.kv Q) }}
      (App (App (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
          go!"Get")) (Val #(GoInterface.ok ci))) (Val #listFrom)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗
        ((⌜err = GoInterface.nil⌝ ∗ ∃ (m : RangeRespM) (σ : KVState), rangeRespMsg resp m ∗
          □ Q σ ∗ ⌜m.kvs = σ.kvs.filter (fun v => inRange listFrom listTo v.key) ∧
            m.hdr.revision = W64 (σ.rev : Int) ∧ kvRevFits σ.rev⌝) ∨
          ⌜err ≠ GoInterface.nil⌝) }} := by
  iintro %Φ ⟨#Pc, Hlt, #Hcl, #Hregs, #Hst, #Hctx, #Hce, #Hopts, #Hau⟩ HΦ
  iunfold isNewClient at Hcl
  icases Hcl with ⟨-, -, ⟨%api, #Hkvf, #Hkv⟩, -⟩
  ihave #Hopts' := optsAt_res sl [withRangeM listTo] iprop(True) $$ Hopts
  ihave #Hrr := kvRegs_range ms $$ Hregs
  ihave #Hst' := srvStart_both ms $$ Hst
  have hm : ∀ (k : Nat) (x : client.SrvAt GF), ms[k]? = some x →
      iprop(⌜Q = fun _ => iprop(True)⌝ ∨ kvReadAu x.γr.kv Q) ⊢
      iprop(⌜Q = fun _ => iprop(True)⌝ ∨
        (⌜(rangeWireOf (opGetModel listFrom [withRangeM listTo])).base.serializable = false⌝ ∗
          kvReadAu x.γr.kv Q)) :=
    fun _ _ _ => by
      iintro (%h | #h)
      · ileft; ipureintro; exact h
      · iright; iframe h; ipureintro; rfl
  ihave #Hau' := (BigAndL.bigAndL_mono hm) $$ Hau
  rw [go_etcd_io.etcd.client.v3.Client.TypeAssumptions.ptr_Get_unfold.method_unfold]
  wp_pures
  wp_auto
  iapply wp_fupd
  wp_apply (client.client_range_any api ms (W64 0) ci cd listFrom sl [withRangeM listTo]
      iprop(True) Q [] hsz) $$ [Hlt] as %resp %err ⟨Hlt, -, Hout, -⟩
  · iframe Hlt; iframe #
    isplitl []
    · rw [show (opGetModel listFrom [withRangeM listTo]).base.sortSet = false from rfl]
      iapply sortNamesIf_false
    ipureintro
    first
      | rfl
      | (refine ⟨?_, rfl⟩; simp [opGetPanics, op_simps])
  icases Hout with (⟨%Herr, %m, Hm, %x, %hx, #Hq⟩ | ⟨%Herr, -⟩)
  · imod rangeRespMsgO_persist _ _ $$ Hm with #Hm
    imodintro
    iapply HΦ
    iframe Hlt
    ileft
    isplitl []
    · ipureintro; exact Herr
    ihave Hs := client.rangeReply_state_bnd x.E x.γr (W64 0) x.cid x.mid _ [] Q m rfl rfl $$ Hq
    icases Hs with ⟨%σ, #HQ, %Hσ⟩
    obtain ⟨hsel, hrev, hb, -⟩ := Hσ
    iexists m, σ
    iframe Hm HQ
    ipureintro
    exact ⟨(srvRangeOk_list _ _ _ hsel).1, hrev, hb⟩
  · imodintro
    iapply HΦ
    iframe Hlt
    iright
    ipureintro; exact Herr.1

theorem client_List_st_law_holds : client_List_st.law (GF := GF) (hG := hG) :=
  client_List_st

/-- **`Commit()` of the model's transaction** through a client of the members `ms` (see the file
header): its update by its kind, one per member. -/
theorem txn_Commit_st [go_etcd_io.etcd.cache.v3.Assumptions] (tp : Loc)
    (ms : List (client.SrvAt GF)) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (b : TxnBuild) (Q : KVState → IProp GF) (cs : List (linkv.MCmp GoString GoString))
    (t e : List (linkv.MOp GoString GoString)) (hb : b.model = clientTxn cs t e)
    (hne : t ++ e ≠ []) (hsz : txnSizeOk (txnWireOf b.model)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
        txnObjAt tp (ms.map client.SrvAt.addr) ci cd b ∗
        ([∗list] x ∈ ms, client.kvRegsAt x) ∗ ([∗list] x ∈ ms, srvStart x) ∗
        client.txnWriteOnce tp (ms.map client.SrvAt.addr) ∗
        ([∧list] x ∈ ms, callUpd x.γr.kv (.txn cs t e) Q) }}
      (App (Val (tp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.txn.ty @!! go!"Commit"))
        (Val #()))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗
        ((⌜err = GoInterface.nil⌝ ∗ ∃ (m : TxnRespM) (σ : KVState), txnRespMsg resp m ∗
          callRes (.txn cs t e) Q σ ∗
          ⌜m.succeeded = (txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs
              (linkv.txnOf cs t e)).1 ∧
            client.opRespsRel false ((linkv.txnOf cs t e).branch m.succeeded)
              (txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs (linkv.txnOf cs t e)).2.2
              m.resps ∧
            m.hdr.revision = W64 ((if (linkv.MIn.txn cs t e).isWrite then
              (kvOpStep (opIn (.txn cs t e)) σ).rev else σ.rev : Nat) : Int) ∧
            kvRevFits σ.rev ∧
            -- (2026-10-31, `notes/vallen.md`) the state's values are short (the reply's log's)
            ∀ v ∈ σ.kvs, v.value.length ≤ etcdKeyMax⌝) ∨
          (⌜err ≠ GoInterface.nil⌝ ∗ kvErr err)) }} := by
  iintro %Φ ⟨#Pc, Hlt, Hobj, #Hregs, #Hst, Hone, Hau⟩ HΦ
  have hw : txnWireOf b.model = linkv.txnOf cs t e := by rw [hb, txnWireOf_clientTxn]
  have hp : client.TxnModel.plain b.model := by rw [hb]; exact clientTxn_plain cs t e
  have hin : client.txnModelIn (txnWireOf b.model) := by rw [hw]; exact txnModelIn_txnOf cs t e
  have hro := txnReadonly_txnOf cs t e
  ihave #Hrr := kvRegs_txn ms $$ Hregs
  ihave #Hst' := srvStart_both ms $$ Hst
  unfold callUpd callRes
  cases hwr : (linkv.MIn.txn cs t e).isWrite
  · -- read-only
    simp only [Bool.false_eq_true, ↓reduceIte]
    simp only [hwr, Bool.not_false] at hro
    have hser := txnSerializable_txnOf cs t e hne
    have hm : ∀ (k : Nat) (x : client.SrvAt GF), ms[k]? = some x →
        iprop(⌜Q = fun _ => iprop(True)⌝ ∨ kvReadAu x.γr.kv Q) ⊢
        client.txnUpdAt x.γr x.γr (txnWireOf b.model) Q :=
      fun _ _ _ => by
        iintro (%h | #h)
        · unfold client.txnUpdAt; ileft; ipureintro; rw [hw]; exact ⟨hro, h⟩
        · unfold client.txnUpdAt; iright; ileft; iframe h; ipureintro; rw [hw]; exact ⟨hro, hser⟩
    have hbox : ([∧list] x ∈ ms,
        iprop(⌜Q = fun _ => iprop(True)⌝ ∨ kvReadAu (GF := GF) x.γr.kv Q)) ⊢
        □ ([∧list] x ∈ ms, client.txnUpdAt x.γr x.γr (txnWireOf b.model) Q) := by
      haveI : Persistent ([∧list] x ∈ ms,
          iprop(⌜Q = fun _ => iprop(True)⌝ ∨ kvReadAu (GF := GF) x.γr.kv Q)) :=
        BigAndL.bigAndL_persistent fun {_ _} _ => inferInstance
      exact intuitionistic_alias.trans (intuitionistically_mono (BigAndL.bigAndL_mono hm))
    ihave #Hau' := hbox $$ Hau
    wp_apply (client.client_txn_any tp ms (W64 0) ci cd b Q [] hp hin hsz) $$ [Hlt Hobj]
      as %resp %err ⟨Hlt, Hout⟩
    · iframe Hlt Hobj
      iframe #
    iapply HΦ
    iframe Hlt
    icases Hout with (⟨%Herr, %m, #Hm, %x, %hx, Hr⟩ | ⟨%Herr, #Hke⟩)
    · ileft
      isplitl []
      · ipureintro; exact Herr
      rw [hw]
      unfold client.txnReplied
      simp only [hro, hser, Bool.false_eq_true, ↓reduceIte]
      icases Hr with ⟨%log, -, %Hlk, %Hp, -, ⟨%ltq, -, #HQ⟩⟩
      obtain ⟨hlen, hb3, -, hrev, -, -, hok, hrel⟩ := Hp
      have hr : ((kvStateOf log ltq).rev + 1 : Nat) = log.length := client.kvStateOf_rev_succ _ hlen
      have hs : (kvStateOf log ltq).kvs = mvcc.stateAfter log := kvStateOf_kvs _
      iexists m, kvStateOf log ltq
      iframe Hm HQ
      ipureintro
      rw [hr, hs]
      refine ⟨hok, hrel, ?_, ?_, mvcc.stateAfter_vals Hlk⟩
      · rw [hrev]
        (try simp only [Bool.false_eq_true, ↓reduceIte])
        rw [kvStateOf_rev]
        congr 1
        omega
      · exact kvRevFits.of_lt (by rw [kvStateOf_rev]; omega)
    · iright
      isplitl
      · ipureintro; first | exact Herr | exact Herr.1
      · iexact Hke
  · -- writing
    simp only [↓reduceIte]
    simp only [hwr, Bool.not_true] at hro
    have hm : ∀ (k : Nat) (x : client.SrvAt GF), ms[k]? = some x →
        kvOpAu1 x.γr.kv (opIn (.txn cs t e)) Q ⊢ client.txnUpdAt x.γr x.γr (txnWireOf b.model) Q :=
      fun _ _ _ => by
        iintro H
        unfold client.txnUpdAt
        iright; iright
        isplitr
        · ipureintro
          rw [hw]
          exact ⟨hro, linkv.txnPlain_txnOf cs t e, txnNoZeroEnd_txnOf cs t e⟩
        rw [hw]
        iExactEq H; rfl
    ihave Hau' := (BigAndL.bigAndL_mono hm) $$ Hau
    wp_apply (client.client_txn_any tp ms (W64 0) ci cd b Q [] hp hin hsz)
      $$ [Hlt Hobj Hau' Hone]
      as %resp %err ⟨Hlt, Hout⟩
    · iframe Hlt Hobj
      iframe #
      iright
      iframe Hone
      iexact Hau'
    iapply HΦ
    iframe Hlt
    icases Hout with (⟨%Herr, %m, #Hm, %x, %hx, Hr⟩ | ⟨%Herr, #Hke⟩)
    · ileft
      isplitl []
      · ipureintro; exact Herr
      rw [hw]
      unfold client.txnReplied
      simp only [hro, Bool.false_eq_true, ↓reduceIte]
      icases Hr with ⟨%tw, %hm, %rq', %t', %y, %y', %l, %skip, %Hp, -, -, -, %Hlk, ⟨%ltq, -, HQ⟩⟩
      obtain ⟨Htw, -, -, Hz, hap, hrev, -, -, -, hlen, hb4, hok, hrel, hsk⟩ := Hp
      have ht : t' = linkv.txnOf cs t e := Hz (irrNoZeroEnd_txnOf cs t e tw Htw)
      subst ht hsk
      have hr : ((kvStateOf y.log ltq).rev + 1 : Nat) = y.log.length := client.kvStateOf_rev_succ _ hlen
      have hs : (kvStateOf y.log ltq).kvs = mvcc.stateAfter y.log := kvStateOf_kvs _
      iexists m, kvStateOf y.log ltq
      iframe Hm HQ
      ipureintro
      rw [hr, hs]
      refine ⟨hok, hrel, ?_, ?_,
        mvcc.stateAfter_vals (Hlk.prefix (applyStep_prefix _ _ _ _ _ hap))⟩
      · (try simp only [↓reduceIte])
        rw [kvOpStep_txnOf_eq, hrev, ← hs, client.kvStateOf_commit_rev _ _ hlen, hs, hr]
      · exact kvRevFits.of_lt (by rw [kvStateOf_rev]; omega)
    · iright
      isplitl
      · ipureintro; first | exact Herr | exact Herr.1
      · iexact Hke

theorem txn_Commit_st_law_holds : txn_Commit_st.law (GF := GF) (hG := hG) :=
  txn_Commit_st

end proofs

end etcd_txnlin
end EtcdGrove
end Perennial

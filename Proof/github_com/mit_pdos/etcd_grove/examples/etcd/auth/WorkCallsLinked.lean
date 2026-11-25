/-
`Work`'s calls (`work_put`, `work_delete`, `work_get`, `work_commit`, `then_commit_nested_refused`),
over the client's linked results: moved out of `WorkCalls.lean` (2026-11-18) so that its lemmas,
which other definitions use, import no linked result (CLAUDE.md, "Import tiers"). See
`WorkCalls.lean`'s header.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.auth.WorkCalls
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.auth.ClientOn
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.auth.CallLaws

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_auth

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver client

section calls
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- **`cli.Put(ctx, k, v)` of `who`'s**: a reply with no error was granted to `who` (`hop`: a
granted put keeps the history). -/
theorem work_put (cl api conn : Loc) (addr : GoString) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (cid mid : w64)
    (γa : auth.AuthNames) (Lset : List EntryModel) (n : Nat) (who : GoString) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (k v : GoString) (hγa : E.authMode = .on γa)
    (hop : akOpGranted who (.put (putKeyOp k v)) → opHistOk (.put (putKeyOp k v)))
    (hsz : opSizeOk (opPutModel k v [])) :
    {{ levelTok 0 ∗ akCallEnv cl api conn addr s E ρ cid mid γa Lset n who ∗ metadata.outMD ci (akOut who) ∗
          ctxOk ci cd ∗ ctxErrClient ci cd }}
      (App (App (App (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
          go!"Put")) (Val #(GoInterface.ok ci))) (Val #k)) (Val #v)) (Val #slice.nil))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗ (
        ⌜err = GoInterface.nil → akOpGranted who (.put (putKeyOp k v))⌝) }} := by
  iintro %Φ ⟨Hlt, #Henv, #Hom, #Hctx, #Hce⟩ HΦ
  iunfold akCallEnv at Henv
  icases Henv with ⟨#Pc, #Hkvf, #Hobj, #Hat, #Hkv, #Htls, #Hinv, #Hf, #HF, #Hnil⟩
  ihave #Hau := akWriteAu s E γa ρ Lset n who conn (.put (putKeyOp k v))
    hγa hop $$ []
  · iframe #
  iunfold akKVOn at Hkv
  icases Hkv with ⟨#Hput, -, -, -⟩
  wp_apply (client_Put_onG cl api conn _ s E ρ cid mid ci (akOut who) cd k v slice.nil _ [] hsz) $$ [$Hlt]
    as %resp %err ⟨Hlt, Hout⟩
  · iframe #
  iapply HΦ
  iframe Hlt
  icases Hout with (⟨%Herr, %m, -, Hr, -⟩ | ⟨%Herr, -⟩)
  · ihave %Hq := putReplied_Q _ _ _ _ _ _ _ _ $$ Hr
    ipureintro; intro _; exact Hq
  · ipureintro; intro h; exact absurd h Herr

theorem work_put_law_holds : work_put.law (GF := GF) (hG := hG) :=
  work_put

/-- **`cli.Delete(ctx, k)` of `who`'s**: a reply with no error was granted to `who`. -/
theorem work_delete (cl api conn : Loc) (addr : GoString) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
    (cid mid : w64) (γa : auth.AuthNames) (Lset : List EntryModel) (n : Nat) (who : GoString)
    (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (k : GoString) (hk : k ≠ [])
    (hγa : E.authMode = .on γa)
    (hop : akOpGranted who (.deleteRange (txn.deleteOpOf k [] false)) →
      opHistOk (.deleteRange (txn.deleteOpOf k [] false)))
    (hsz : opSizeOk (opDeleteModel k [])) :
    {{ levelTok 0 ∗ akCallEnv cl api conn addr s E ρ cid mid γa Lset n who ∗ metadata.outMD ci (akOut who) ∗
          ctxOk ci cd ∗ ctxErrClient ci cd }}
      (App (App (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
          go!"Delete")) (Val #(GoInterface.ok ci))) (Val #k)) (Val #slice.nil))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗ (
        ⌜err = GoInterface.nil → akOpGranted who (.deleteRange (txn.deleteOpOf k [] false))⌝) }} := by
  iintro %Φ ⟨Hlt, #Henv, #Hom, #Hctx, #Hce⟩ HΦ
  iunfold akCallEnv at Henv
  icases Henv with ⟨#Pc, #Hkvf, #Hobj, #Hat, #Hkv, #Htls, #Hinv, #Hf, #HF, #Hnil⟩
  ihave #Hau := akWriteAu s E γa ρ Lset n who conn
    (.deleteRange (txn.deleteOpOf k [] false)) hγa hop $$ []
  · iframe #
  iunfold akKVOn at Hkv
  icases Hkv with ⟨-, -, #Hdel, -⟩
  wp_apply (client_Delete_on cl api conn _ s E ρ cid mid ci (akOut who) cd k slice.nil _ [] hk hsz) $$ [$Hlt]
    as %resp %err ⟨Hlt, Hout⟩
  · iframe #
  iapply HΦ
  iframe Hlt
  icases Hout with (⟨%Herr, %m, -, Hr, -⟩ | ⟨%Herr, -⟩)
  · ihave %Hq := deleteReplied_Q _ _ _ _ _ _ _ _ $$ Hr
    ipureintro; intro _; exact Hq
  · ipureintro; intro h; exact absurd h Herr.1

theorem work_delete_law_holds : work_delete.law (GF := GF) (hG := hG) :=
  work_delete

/-- **`cli.Get(ctx, key, opts...)` of `who`'s** (no sort, no panic): a reply with no error was
granted at `setupSt` to a user of `who`'s, for the request's range (`akRead_granted`), and its
keys are in that range (`srvRangeOk_keys`). -/
theorem work_get (cl api conn : Loc) (addr : GoString) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
    (cid mid : w64) (γa : auth.AuthNames) (Lset : List EntryModel) (n : Nat) (who : GoString)
    (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (key : GoString) (sl : GoSlice)
    (gs : List (OpFull → OpFull)) (hγa : E.authMode = .on γa)
    (hg : ¬ opGetPanics gs ∧ (opGetModel key gs).t = W64 1)
    (hs : (opGetModel key gs).base.sortSet = false) (hsz : opSizeOk (opGetModel key gs)) :
    {{ levelTok 0 ∗ akCallEnv cl api conn addr s E ρ cid mid γa Lset n who ∗ metadata.outMD ci (akOut who) ∗
          ctxOk ci cd ∗ ctxErrClient ci cd ∗
        optsAt sl gs }}
      (App (App (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
          go!"Get")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗ (
        ⌜err ≠ GoInterface.nil⌝ ∨
        (⌜err = GoInterface.nil⌝ ∗ ∃ m : RangeRespM, rangeRespMsg resp m ∗
          ⌜(∃ (r : Nat) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (e : GoString),
              akUser who info.Username' ∧
              apply.authEndOf (rangeWireOf (opGetModel key gs)).base.rangeEnd e ∧
              auth.granted (setupSt r) (auth.authInfoM info) (rangeWireOf (opGetModel key gs)).key
                e .read) ∧
            ∀ kv ∈ m.kvs, inRange (rangeWireOf (opGetModel key gs)).key
              (rangeWireOf (opGetModel key gs)).base.rangeEnd kv.key = true⌝)) }} := by
  iintro %Φ ⟨Hlt, #Henv, #Hom, #Hctx, #Hce, #Hopts⟩ HΦ
  iunfold akCallEnv at Henv
  icases Henv with ⟨#Pc, #Hkvf, #Hobj, #Hat, #Hkv, #Htls, #Hinv, #Hf, #HF, #Hnil⟩
  iunfold akKVOn at Hkv
  icases Hkv with ⟨-, #Hrange, -, -⟩
  ihave #Hpub : auth.authPubLbM E.authMode n $$ []
  · rw [hγa]
    iunfold akAuthFixed at Hf
    icases Hf with ⟨#Hp, -⟩
    unfold auth.authPubLbM
    iexact Hp
  imod (monoNatLbOwn_0 (GF := GF) ρ.rd.committed) with #H0
  ihave #Hc0 : committedAtLeast ρ.rd (W64 0) $$ []
  · unfold committedAtLeast; ileft
    rw [show uint.nat (W64 0) = 0 from rfl]
    iexact H0
  ihave Hres := optsAt_res sl gs iprop(True) $$ Hopts
  iapply wp_fupd
  wp_apply (client_Get_on cl api conn _ s E ρ.rd cid mid (W64 0) n ci (akOut who) cd key sl gs iprop(True)
      (fun _ => iprop(True)) [] hsz) $$ [$Hlt Hres] as %resp %err ⟨Hlt, Hout⟩
  · iframe #
    isplitl []
    · itrivial
    rw [hs]
    isplitl []
    · unfold sortNamesIf; simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
    isplitl []
    · ipureintro; exact hg
    iintro !>
    ileft
    ipureintro; rfl
  icases Hout with ⟨-, (⟨%Herr, %m, #Hm, #Hok, %md, %Hmd, #Hauth⟩ | ⟨%Herr, -⟩)⟩
  · ihave #Hseen := akTokSeen_attempt γa who conn md Hmd $$ Hat
    imod (akRead_granted s E γa ρ ρ.rd Lset n who (W64 0) _ _ hγa) $$ [] Hauth with %Hg
    · iframe #
    imodintro
    iapply HΦ
    iframe Hlt
    iunfold rangeReplyOk at Hok
    icases Hok with ⟨%log, -, -, %Hl, -⟩
    iright
    isplitl []
    · ipureintro; exact Herr
    iexists m
    iframe Hm
    ipureintro
    exact ⟨Hg, srvRangeOk_keys _ _ _ _ Hl.2.2.2.2.2.2.2.1⟩
  · imodintro
    iapply HΦ
    iframe Hlt
    ileft
    ipureintro; exact Herr.1

theorem work_get_law_holds : work_get.law (GF := GF) (hG := hG) :=
  work_get

/-- **`t.Commit()` of `who`'s writing transaction** (plain, no range end `[0]`, of the shape the
permission cache decides): a reply with no error was granted to `who` (`hop`: a granted
transaction keeps the history). -/
theorem work_commit (cl api conn tp : Loc) (addr : GoString) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
    (cid mid : w64) (γa : auth.AuthNames) (Lset : List EntryModel) (n : Nat) (who : GoString)
    (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (b : TxnBuild)
    (hγa : E.authMode = .on γa)
    (hp : TxnModel.plain (txnWireOf b.model)) (hin : txnModelIn (txnWireOf b.model))
    (hsz : txnSizeOk (txnWireOf b.model))
    (hsh : ∀ tw : txn.TxnModelW, tw.toModel = txnWireOf b.model → kvShapeAll (irrTxn tw))
    (hro : txn.txnReadonly (txnWireOf b.model) = false)
    (hpl : txn.txnPlain (txnWireOf b.model) ∧ txnNoZeroEnd (txnWireOf b.model))
    (hop : akOpGranted who (.txn (txnWireOf b.model)) → opHistOk (.txn (txnWireOf b.model))) :
    {{ levelTok 0 ∗ akCallEnv cl api conn addr s E ρ cid mid γa Lset n who ∗ txnObjAt tp [addr] ci cd b ∗
          metadata.outMD ci (akOut who) ∗
        txnKvIs tp api }}
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
  iunfold akCallEnv at Henv
  icases Henv with ⟨#Pc, #Hkvf, #Hobjc, #Hat, #Hkv, #Htls, #Hinv, #Hf, #HF, #Hnil⟩
  ihave #Hau := akWriteAu s E γa ρ Lset n who conn
    (.txn (txnWireOf b.model)) hγa hop $$ []
  · iframe #
  iunfold akKVOn at Hkv
  icases Hkv with ⟨-, -, -, #Htxn⟩
  ihave #Hpub : auth.authPubLbM E.authMode n $$ []
  · rw [hγa]
    iunfold akAuthFixed at Hf
    icases Hf with ⟨#Hp, -⟩
    unfold auth.authPubLbM
    iexact Hp
  imod (monoNatLbOwn_0 (GF := GF) ρ.rd.committed) with #H0
  ihave #Hc0 : committedAtLeast ρ.rd (W64 0) $$ []
  · unfold committedAtLeast; ileft
    rw [show uint.nat (W64 0) = 0 from rfl]
    iexact H0
  wp_apply (client_txn_on tp api conn _ (srvTLSId s) E ρ ρ.rd cid mid (W64 0) n ci (akOut who) cd b
      (fun _ => iprop(⌜akOpGranted who (.txn (txnWireOf b.model))⌝)) [] (fun _ => hin) hsz
      (fun _ => hsh)) $$ [$Hlt Hobj] as %resp %err ⟨Hlt, Hout⟩
  · iframe #
    iframe Hobj
    ileft
    iintro !>
    unfold txnUpdAtOn
    iright
    iright
    isplitl []
    · ipureintro; exact ⟨hro, Or.inl hpl.1, hpl.2, txnNestOk_of_plain _ hp hin⟩
    iexact Hau
  iapply HΦ
  iframe Hlt
  icases Hout with (⟨%Herr, %m, #Hm, Hr, -⟩ | ⟨%Herr, -⟩)
  · ihave %Hq := txnReplied_facts _ _ _ _ _ _ _ _ _ _ hro hpl.2 $$ Hr
    isplitl []
    · ipureintro; intro _; exact Hq.1
    iright
    iexists m
    iframe Hm
    ipureintro; exact Hq.2
  · isplitl []
    · ipureintro; intro h; exact absurd h Herr.1
    ileft; ipureintro; exact Herr.1

theorem work_commit_law_holds : work_commit.law (GF := GF) (hG := hG) :=
  work_commit

/-- **T4, a nested transaction putting outside `[a, b)`, is refused**: `t.Then(OpTxn(nil,
[OpPut(c/who/t3, "vt")], nil))` returns the builder, whose `Commit` replies with an error (no
principal may write `c/...`: `t4M_not_granted`; etcd checks a nested transaction's operations,
`checkTxnReqsPermission`). `hwho`: `who` is a principal of the program, so the request fits a gRPC
message (`t4M_size`; `Commit`'s size premise, 2026-10-30, postdates this statement). -/
theorem then_commit_nested_refused (cl api conn tp : Loc) (addr : GoString) (s : Loc) (E : apply.AEnv GF)
    (ρ : ReqNames) (cid mid : w64) (γa : auth.AuthNames) (Lset : List EntryModel) (n : Nat)
    (who : GoString) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (sl tsl : GoSlice)
    (op : go_etcd_io.etcd.client.v3.Op) (hwho : who ∈ principals) (hγa : E.authMode = .on γa) :
    {{ akCallEnv cl api conn addr s E ρ cid mid γa Lset n who ∗
        txnObjAt tp [addr] ci cd TxnBuild.empty ∗ metadata.outMD ci (akOut who) ∗ txnKvIs tp api ∗
        sl ↦*□ [op] ∗ opFullAt op OpFull.txnInit ∗ cmpsAt op.cmps' [] ∗
        ⌜op.thenOps' = tsl ∧ op.elseOps' = slice.nil⌝ ∗
        opsAt tsl [opPutModel (keyOfK go!"c" who go!"t3") go!"vt" []] }}
      (App (Val (tp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.txn.ty @!! go!"Then"))
        (Val #sl))
    {{ RET #(interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.txn.ty) #tp :
          GoInterface);
        ∀ Φ, levelTok 0 -∗ (∀ (resp : Loc) (err : GoInterface), levelTok 0 -∗ ⌜err ≠ GoInterface.nil⌝ -∗
            Φ (PairV #resp #err)) -∗
          WP (App (Val (tp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.txn.ty @!!
            go!"Commit")) (Val #())) {{ Φ }} }} := by
  iintro %Φ ⟨#Henv, Hobj, #Hom, #Hkt, #Hsl, #Hof, #Hcm, %Hs, #Hops⟩ HΦ
  ihave #Hts := opsAt_leaves (GF := GF) tsl [opPutModel (keyOfK go!"c" who go!"t3") go!"vt" []]
      [.put (keyOfK go!"c" who go!"t3") go!"vt" (W64 0)] (by simp [txnOpOf_put]) $$ Hops
  ihave #Hnil := opsTAt_nil (GF := GF)
  ihave #Htop := opTAtC_opTxn (GF := GF) op [] tsl slice.nil _ [] Hs $$ [Hof Hcm Hts Hnil]
  · iframe #
  ihave #Hsl1 := opsTAt_one (GF := GF) sl op _ $$ [Hsl Htop]
  · iframe #
  iunfold akCallEnv at Henv
  icases Henv with ⟨#Pc, #Hkvf, #Hobjc, #Hat, #Hkv, #Htls, #Hinv, #Hf, #HF, #Honil⟩
  wp_apply (v3.txn.wp_Then tp _ ci cd TxnBuild.empty sl _
      [.txn [] [.put (keyOfK go!"c" who go!"t3") go!"vt" (W64 0)] []]) $$ [Hobj] as Hobj
  · iframe #
    iframe Hobj
    ipureintro
    exact ⟨by simp [OpT.txnOps, OpT.txnOp, txnOpOf_put], rfl, rfl⟩
  ihave Hobj : txnObjAt (GF := GF) tp [addr] ci cd
      ⟨t4M (keyOfK go!"c" who go!"t3") go!"vt", false, true, false⟩ $$ [Hobj]
  · iExactEq Hobj
    simp [TxnModel.empty, t4M]
  iapply HΦ
  iintro %Φ' Hlt HΦ'
  have hw := t4M_wire (keyOfK go!"c" who go!"t3") go!"vt"
  have hro : txn.txnReadonly (txnWireOf (t4M (keyOfK go!"c" who go!"t3") go!"vt")) = false := by
    rw [hw]; exact t4M_ro _ _
  have hk : keyOfK go!"c" who go!"t3" ≠ [] := keyOfK_ne_nil _ _ _ (by decide)
  have hsz : txnSizeOk (txnWireOf (t4M (keyOfK go!"c" who go!"t3") go!"vt")) := by
    rw [hw]; exact t4M_size _ _ (keyOfK_principal_le hwho (by decide) (by decide)) (by decide)
  have hng : ¬ akOpGranted who (.txn (txnWireOf (t4M (keyOfK go!"c" who go!"t3") go!"vt"))) := by
    rw [hw]; exact t4M_not_granted who go!"t3" go!"vt"
  have hupd : txn.txnPlain (txnWireOf (t4M (keyOfK go!"c" who go!"t3") go!"vt")) ∧
      txnNoZeroEnd (txnWireOf (t4M (keyOfK go!"c" who go!"t3") go!"vt")) ∧
      txnNestOk (txnWireOf (t4M (keyOfK go!"c" who go!"t3") go!"vt")) := by
    rw [hw]; exact t4M_upd _ _
  ihave #Hau := akWriteAu s E γa ρ Lset n who conn
    (.txn (txnWireOf (t4M (keyOfK go!"c" who go!"t3") go!"vt"))) hγa
    (fun h => absurd h hng) $$ []
  · iframe #
  iunfold akKVOn at Hkv
  icases Hkv with ⟨-, -, -, #Htxn⟩
  ihave #Hpub : auth.authPubLbM E.authMode n $$ []
  · rw [hγa]
    iunfold akAuthFixed at Hf
    icases Hf with ⟨#Hp, -⟩
    unfold auth.authPubLbM
    iexact Hp
  imod (monoNatLbOwn_0 (GF := GF) ρ.rd.committed) with #H0
  ihave #Hc0 : committedAtLeast ρ.rd (W64 0) $$ []
  · unfold committedAtLeast; ileft
    rw [show uint.nat (W64 0) = 0 from rfl]
    iexact H0
  wp_apply (client_txn_on tp api conn _ (srvTLSId s) E ρ ρ.rd cid mid (W64 0) n ci (akOut who) cd
      ⟨t4M (keyOfK go!"c" who go!"t3") go!"vt", false, true, false⟩
      (fun _ => iprop(⌜akOpGranted who (.txn (txnWireOf (t4M (keyOfK go!"c" who go!"t3") go!"vt")))⌝))
      [] (fun h => absurd h (by rw [hro]; decide)) hsz
      (fun _ tw htw => t4M_shape _ _ hk tw (htw.trans hw))) $$ [$Hlt Hobj] as %resp %err ⟨Hlt, Hout⟩
  · iframe #
    iframe Hobj
    ileft
    iintro !>
    unfold txnUpdAtOn
    iright
    iright
    isplitl []
    · ipureintro
      exact ⟨hro, Or.inl hupd.1, hupd.2⟩
    iexact Hau
  icases Hout with (⟨%Herr, %m, #Hm, Hr, -⟩ | ⟨%Herr, -⟩)
  · ihave %Hq := txnReplied_Q _ _ _ _ _ _ _ _ _ _ hro $$ Hr
    exact absurd Hq hng
  · iapply HΦ' $$ Hlt
    ipureintro; exact Herr.1

theorem then_commit_nested_refused_law_holds : then_commit_nested_refused.law (GF := GF) (hG := hG) :=
  then_commit_nested_refused

end calls

end etcd_auth
end EtcdGrove
end Perennial

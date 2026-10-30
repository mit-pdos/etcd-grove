/-
**`Work`'s calls, one at a time** (`notes/authkv-main-plan.md`, "Proving the stubs", layer 4;
2026-10-30). Lean-first (no Rocq counterpart).

A request of `Work`'s is sent in `reqCtx(who)`'s context, whose outgoing metadata is `akOut who`
(`reqCtx_out`). A write sends the update `akWriteAu`: `akHist_writeAu` at the write's grant, which
`akOpGranted_of_grant` reads at `setupSt` (`Q`: the write was granted to `who`). So a write's
reply with no error was granted (`work_put`, `work_delete`): its point permission is `who`'s
(`akGranted_point`), and a refused write's reply is an error.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.authkv.WorkAuth
public import Proof.github_com.mit_pdos.etcd_grove.examples.authkv.ClientOn

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authkv

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver client

section pure
variable [GooseExts]

/-- **`reqCtx(who)`'s context carries `akOut who`** (`reqCtx.spec`'s post). -/
theorem reqCtx_out (who : GoString) (c c0 : GoInterface) (h0 : metadata.outgoingOf c0 = none)
    (h : if who = go!"bad" then
      metadata.outgoingOf c = metadata.mdAdd (metadata.outgoingOf c0) go!"token" badToken
      else c = c0) :
    metadata.outgoingOf c = akOut who := by
  unfold akOut
  by_cases hb : who = go!"bad"
  · rw [if_pos hb] at h; rw [if_pos hb, h, h0]
  · rw [if_neg hb] at h; rw [if_neg hb, h, h0]

/-- A put's request needs the write permission on its key. -/
theorem put_perm_mem (o : OpFull) :
    ((o.key, [], .write) : apply.Perm3) ∈ reqPerms (irrPut o) := by
  simp [reqPerms, irrPut, apply.dispatchKind, apply.putPerms, apply.irrEmpty]

/-- A delete's request needs the write permission on its range. -/
theorem delete_perm_mem (o : OpFull) :
    ((o.key, o.base.rangeEnd, .write) : apply.Perm3) ∈ reqPerms (irrDeleteRange o) := by
  simp [reqPerms, irrDeleteRange, apply.dispatchKind, apply.irrEmpty]

/-- **A granted put of `who`'s on a non-empty key is `who`'s to make.** -/
theorem akOpGranted_put (who k v : GoString) (hk : k ≠ [])
    (h : akOpGranted who (.put (putKeyOp k v))) : permittedK who k :=
  akGranted_point who _ k .write h (put_perm_mem (putKeyOp k v)) hk

/-- **A granted point delete of `who`'s on a non-empty key is `who`'s to make.** -/
theorem akOpGranted_delete (who k : GoString) (hk : k ≠ [])
    (h : akOpGranted who (.deleteRange (txn.deleteOpOf k [] false))) : permittedK who k :=
  akGranted_point who _ k .write h (delete_perm_mem (txn.deleteOpOf k [] false)) hk

/-- **A key `c/…` is no one's to write** (`c` sorts after `hi = "b"`). -/
theorem not_permitted_c (who n : GoString) : ¬ permittedK who (keyOfK go!"c" who n) := by
  intro ⟨_, _, hlt⟩
  rw [show keyOfK go!"c" who n = W8 99 :: (go!"/" ++ who ++ go!"/" ++ n) by
    simp [keyOfK], show hi = [W8 98] from rfl, go.goStringLt_cons_iff] at hlt
  rcases hlt with h | ⟨h, -⟩ <;> revert h <;> decide

/-- `Work`'s keys are not empty. -/
theorem keyOfK_ne_nil (x who n : GoString) (hx : x ≠ []) : keyOfK x who n ≠ [] := by
  unfold keyOfK; simp [hx]

/-- **A granted put of `who`'s on `a/who/n` keeps the history** (`opHistOk_putKey`): it is `u`'s
(`akOpGranted_put`), and `u` writes `a/u/n` (`hw`). -/
theorem opHistOk_put_a (who n v : GoString) (hw : writerK (keyOfK go!"a" go!"u" n) = go!"u")
    (h : akOpGranted who (.put (putKeyOp (keyOfK go!"a" who n) v))) :
    opHistOk (.put (putKeyOp (keyOfK go!"a" who n) v)) := by
  obtain ⟨rfl, hr⟩ := akOpGranted_put who _ v (keyOfK_ne_nil _ _ _ (by decide)) h
  exact opHistOk_putKey _ _ (Or.inl (by rw [hw]; exact ⟨rfl, hr⟩))

/-- **A range reply's keys are in its range** (`srvRangeOk`: the state's range, cut, sorted and
read). -/
theorem srvRangeOk_keys (o : OpFull) (st kvs : List EtcdKv) (more : Bool)
    (h : txn.srvRangeOk o st kvs more) :
    ∀ kv ∈ kvs, inRange o.key o.base.rangeEnd kv.key = true := by
  obtain ⟨l, ⟨hperm, -⟩, -, rfl⟩ := h
  intro kv hkv
  obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hkv
  have hvl : v ∈ l := by
    unfold txn.srvTrunc at hv
    split at hv
    · exact List.mem_of_mem_take hv
    · exact hv
  have hvp := hperm.mem_iff.1 hvl
  unfold txn.srvPre at hvp
  split at hvp
  · simp at hvp
  obtain ⟨hvm, -⟩ := List.mem_filter.1 hvp
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hvm
  have hw' : w ∈ rangeIn st o := by
    unfold mvcc.takeLimit at hw
    split at hw
    · exact List.mem_of_mem_take hw
    · exact hw
  have hk := (List.mem_filter.1 hw').2
  unfold txn.respKv txn.kvRead
  split <;> split <;> simpa using hk

/-! ### `Work`'s three ranges -/

/-- A key in `[a, b)` is `u`'s to read. -/
theorem permitted_of_inRange_ab (k : GoString) (h : inRange lo hi k = true) :
    permittedK go!"u" k := by
  unfold inRange at h
  rw [if_neg (by decide), if_neg (by decide)] at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    decide_eq_true_eq] at h
  refine ⟨rfl, ?_, h.2⟩
  by_cases hl : go.GoStringLt lo k
  · exact Or.inr hl
  · exact Or.inl (go.goStringLt_eq_of_not_lt hl h.1)

/-- `Get(lo, WithRange(hi))`: the range `[a, b)`, sent as is. -/
theorem get_ab_ok : (¬ opGetPanics [withRangeM hi] ∧ (opGetModel lo [withRangeM hi]).t = W64 1) ∧
    (opGetModel lo [withRangeM hi]).base.sortSet = false ∧
    (rangeWireOf (opGetModel lo [withRangeM hi])).key = lo ∧
    (rangeWireOf (opGetModel lo [withRangeM hi])).base.rangeEnd = hi :=
  ⟨⟨by simp [opGetPanics, opFold, withRangeM, OpFull.newOp], rfl⟩, rfl, rfl, rfl⟩

/-- `Get("c/", WithPrefix())`: the range `[c/, c0)`. -/
theorem get_c_ok : (¬ opGetPanics [withPrefixM] ∧ (opGetModel go!"c/" [withPrefixM]).t = W64 1) ∧
    (opGetModel go!"c/" [withPrefixM]).base.sortSet = false ∧
    (rangeWireOf (opGetModel go!"c/" [withPrefixM])).key = go!"c/" ∧
    (rangeWireOf (opGetModel go!"c/" [withPrefixM])).base.rangeEnd = go!"c0" :=
  ⟨⟨by simp [opGetPanics, opFold, withPrefixM, OpFull.newOp], rfl⟩, rfl, rfl, by decide⟩

/-- `Get(lo, WithRange("d"))`: the range `[a, d)`. -/
theorem get_past_ok :
    (¬ opGetPanics [withRangeM go!"d"] ∧ (opGetModel lo [withRangeM go!"d"]).t = W64 1) ∧
    (opGetModel lo [withRangeM go!"d"]).base.sortSet = false ∧
    (rangeWireOf (opGetModel lo [withRangeM go!"d"])).key = lo ∧
    (rangeWireOf (opGetModel lo [withRangeM go!"d"])).base.rangeEnd = go!"d" :=
  ⟨⟨by simp [opGetPanics, opFold, withRangeM, OpFull.newOp], rfl⟩, rfl, rfl, rfl⟩

/-- **A read of `[a, b)` granted at `setupSt` to a user of `who`'s is `u`'s.** -/
theorem read_ab_u (who : GoString)
    (h : ∃ (r : Nat) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (e : GoString),
      akUser who info.Username' ∧ apply.authEndOf hi e ∧
      auth.granted (setupSt r) (auth.authInfoM info) lo e .read) : who = go!"u" := by
  obtain ⟨r, info, e, hu, he, hg⟩ := h
  rcases he with rfl | ⟨-, h0⟩
  · exact granted_ab_u r who _ _ hu hg
  · exact absurd h0 (by decide)

/-- **No read of `[c/, c0)` is granted at `setupSt` to a user of `who`'s.** -/
theorem read_c_refused (who : GoString)
    (h : ∃ (r : Nat) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (e : GoString),
      akUser who info.Username' ∧ apply.authEndOf go!"c0" e ∧
      auth.granted (setupSt r) (auth.authInfoM info) go!"c/" e .read) : False := by
  obtain ⟨r, info, e, hu, he, hg⟩ := h
  rcases he with rfl | ⟨-, h0⟩
  · exact not_granted_c r who _ _ hu hg
  · exact absurd h0 (by decide)

/-- **No read of `[a, d)` is granted at `setupSt` to a user of `who`'s.** -/
theorem read_past_refused (who : GoString)
    (h : ∃ (r : Nat) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (e : GoString),
      akUser who info.Username' ∧ apply.authEndOf go!"d" e ∧
      auth.granted (setupSt r) (auth.authInfoM info) lo e .read) : False := by
  obtain ⟨r, info, e, hu, he, hg⟩ := h
  rcases he with rfl | ⟨-, h0⟩
  · exact not_granted_past r who _ _ hu hg
  · exact absurd h0 (by decide)

end pure

section calls
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- The set-up's requested log, a lower bound (`akAuthFixed`'s). -/
theorem akAuthFixed_lb (γa : auth.AuthNames) (ρ : ReqNames) (Lset : List EntryModel) (n : Nat) :
    akAuthFixed (GF := GF) γa ρ Lset n ⊢ srvReqLogLb ρ.raft Lset := by
  iintro #Hf
  iunfold akAuthFixed at Hf
  icases Hf with ⟨-, -, #HL, -⟩
  iexact HL

/-- **The update a write of `who`'s sends**: `akHist_writeAu` at the write's grant, read at
`setupSt` (`akOpGranted_of_grant`), at the set-up's log; its result, the write granted to `who`.
`hop`: a granted write is one the history admits. -/
theorem akWriteAu (s : Loc) (E : apply.AEnv GF) (γa : auth.AuthNames) (ρ : ReqNames)
    (Lset : List EntryModel) (n : Nat) (who : GoString) (conn : Loc) (ctx : GoInterface)
    (op : KVOp) (hγa : E.authMode = .on γa) (hout : metadata.outgoingOf ctx = akOut who)
    (hop : akOpGranted who op → opHistOk op) :
    akHistInv (GF := GF) ρ.kv ∗ akAuthFixed γa ρ Lset n ∗ attemptTokOk conn (akTokP γa who) ∗
      □ (srvTLSId s -∗ False) ⊢
      □ clientOpAuOn s E ρ conn ctx op (fun _ => iprop(⌜akOpGranted who op⌝)) := by
  iintro ⟨#Hinv, #Hf, #Hat, #Htls⟩
  ihave #HL := akAuthFixed_lb γa ρ Lset n $$ Hf
  ihave #Hw := akHist_writeAu ρ.kv op (clientGrant s E ρ conn ctx op Lset)
    (fun _ => iprop(⌜akOpGranted who op⌝)) $$ [Hinv]
  · iframe Hinv
    iintro !> %σ Hg
    imod (akOpGranted_of_grant s E γa ρ Lset n who conn ctx op σ _ hγa hout authHistN_akMask)
      $$ [] Hg with %Hok
    · iframe #
    imodintro
    isplitl []
    · ipureintro; exact hop Hok
    · ipureintro; exact Hok
  imodintro
  unfold clientOpAuOn
  iexists Lset
  iframe HL
  iexact Hw

/-- A put's reply holds its update's result. -/
theorem putReplied_Q (E : apply.AEnv GF) (γr : ReadNames) (F : mvcc.Log) (o : OpFull)
    (P : Prop) (cid mid : w64) (m : PutRespM) :
    putReplied E γr F o (fun _ => iprop(⌜P⌝)) cid mid m ⊢ ⌜P⌝ := by
  iintro H
  iunfold putReplied at H
  icases H with ⟨%_, %_, %_, %_, %_, -, -, -, -, -, %HP⟩
  ipureintro; exact HP

/-- A delete's reply holds its update's result. -/
theorem deleteReplied_Q (E : apply.AEnv GF) (γr : ReadNames) (F : mvcc.Log) (o : OpFull)
    (P : Prop) (cid mid : w64) (m : DelRespM) :
    deleteReplied E γr F o (fun _ => iprop(⌜P⌝)) cid mid m ⊢ ⌜P⌝ := by
  iintro H
  iunfold deleteReplied at H
  icases H with ⟨%_, %_, %_, %_, %_, %_, %_, -, -, -, -, -, %HP⟩
  ipureintro; exact HP

/-- **What every call of `Work`'s holds** (persistent): the client's `KV` field over `conn`, whose
attempts carry `who`'s tokens, the member's KV methods with auth on, the TLS refutation, the
history invariant, the auth state fixed after the set-up, an empty index certificate and an
empty option list. -/
def akCallEnv (cl api conn : Loc) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (cid mid : w64)
    (γa : auth.AuthNames) (Lset : List EntryModel) (n : Nat) (who : GoString) : IProp GF :=
  iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
    structFieldRef go_etcd_io.etcd.client.v3.Client go!"KV" cl ↦□
      (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty) #api : GoInterface) ∗
    kvObjAtC api conn [go!"127.0.0.1:23916"] ∗ attemptTokOk conn (akTokP γa who) ∗
    akKVOn go!"127.0.0.1:23916" s E ρ cid mid ∗ □ (srvTLSId s -∗ False) ∗ akHistInv ρ.kv ∗
    akAuthFixed γa ρ Lset n ∗ mvcc.idxCert E.γ.idx [] ∗ optsAt slice.nil [])

instance akCallEnv_persistent (cl api conn : Loc) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
    (cid mid : w64) (γa : auth.AuthNames) (Lset : List EntryModel) (n : Nat) (who : GoString) :
    Persistent (akCallEnv (GF := GF) cl api conn s E ρ cid mid γa Lset n who) := by
  unfold akCallEnv; infer_instance

/-- **`cli.Put(ctx, k, v)` of `who`'s**: a reply with no error was granted to `who` (`hop`: a
granted put keeps the history). -/
theorem work_put (cl api conn : Loc) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (cid mid : w64)
    (γa : auth.AuthNames) (Lset : List EntryModel) (n : Nat) (who : GoString) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (k v : GoString) (hγa : E.authMode = .on γa)
    (hout : metadata.outgoingOf (GoInterface.ok ci) = akOut who)
    (hop : akOpGranted who (.put (putKeyOp k v)) → opHistOk (.put (putKeyOp k v))) :
    {{ akCallEnv cl api conn s E ρ cid mid γa Lset n who ∗ ctxOk ci cd ∗ ctxErrClient ci cd }}
      (App (App (App (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
          go!"Put")) (Val #(GoInterface.ok ci))) (Val #k)) (Val #v)) (Val #slice.nil))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        ⌜err = GoInterface.nil → akOpGranted who (.put (putKeyOp k v))⌝ }} := by
  iintro %Φ ⟨#Henv, #Hctx, #Hce⟩ HΦ
  iunfold akCallEnv at Henv
  icases Henv with ⟨#Pc, #Hkvf, #Hobj, #Hat, #Hkv, #Htls, #Hinv, #Hf, #HF, #Hnil⟩
  ihave #Hau := akWriteAu s E γa ρ Lset n who conn (GoInterface.ok ci) (.put (putKeyOp k v))
    hγa hout hop $$ []
  · iframe #
  iunfold akKVOn at Hkv
  icases Hkv with ⟨#Hput, -, -, -⟩
  wp_apply (client_Put_onG cl api conn _ s E ρ cid mid ci cd k v slice.nil _ []) $$ []
    as %resp %err Hout
  · iframe #
  iapply HΦ
  icases Hout with (⟨%Herr, %m, -, Hr, -⟩ | ⟨%Herr, -⟩)
  · ihave %Hq := putReplied_Q _ _ _ _ _ _ _ _ $$ Hr
    ipureintro; intro _; exact Hq
  · ipureintro; intro h; exact absurd h Herr

/-- **`cli.Delete(ctx, k)` of `who`'s**: a reply with no error was granted to `who`. -/
theorem work_delete (cl api conn : Loc) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
    (cid mid : w64) (γa : auth.AuthNames) (Lset : List EntryModel) (n : Nat) (who : GoString)
    (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (k : GoString) (hk : k ≠ [])
    (hγa : E.authMode = .on γa) (hout : metadata.outgoingOf (GoInterface.ok ci) = akOut who)
    (hop : akOpGranted who (.deleteRange (txn.deleteOpOf k [] false)) →
      opHistOk (.deleteRange (txn.deleteOpOf k [] false))) :
    {{ akCallEnv cl api conn s E ρ cid mid γa Lset n who ∗ ctxOk ci cd ∗ ctxErrClient ci cd }}
      (App (App (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
          go!"Delete")) (Val #(GoInterface.ok ci))) (Val #k)) (Val #slice.nil))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        ⌜err = GoInterface.nil → akOpGranted who (.deleteRange (txn.deleteOpOf k [] false))⌝ }} := by
  iintro %Φ ⟨#Henv, #Hctx, #Hce⟩ HΦ
  iunfold akCallEnv at Henv
  icases Henv with ⟨#Pc, #Hkvf, #Hobj, #Hat, #Hkv, #Htls, #Hinv, #Hf, #HF, #Hnil⟩
  ihave #Hau := akWriteAu s E γa ρ Lset n who conn (GoInterface.ok ci)
    (.deleteRange (txn.deleteOpOf k [] false)) hγa hout hop $$ []
  · iframe #
  iunfold akKVOn at Hkv
  icases Hkv with ⟨-, -, #Hdel, -⟩
  wp_apply (client_Delete_on cl api conn _ s E ρ cid mid ci cd k slice.nil _ [] hk) $$ []
    as %resp %err Hout
  · iframe #
  iapply HΦ
  icases Hout with (⟨%Herr, %m, -, Hr, -⟩ | ⟨%Herr, -⟩)
  · ihave %Hq := deleteReplied_Q _ _ _ _ _ _ _ _ $$ Hr
    ipureintro; intro _; exact Hq
  · ipureintro; intro h; exact absurd h Herr.1

/-- **`cli.Get(ctx, key, opts...)` of `who`'s** (no sort, no panic): a reply with no error was
granted at `setupSt` to a user of `who`'s, for the request's range (`akRead_granted`), and its
keys are in that range (`srvRangeOk_keys`). -/
theorem work_get (cl api conn : Loc) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
    (cid mid : w64) (γa : auth.AuthNames) (Lset : List EntryModel) (n : Nat) (who : GoString)
    (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (key : GoString) (sl : GoSlice)
    (gs : List (OpFull → OpFull)) (hγa : E.authMode = .on γa)
    (hout : metadata.outgoingOf (GoInterface.ok ci) = akOut who)
    (hg : ¬ opGetPanics gs ∧ (opGetModel key gs).t = W64 1)
    (hs : (opGetModel key gs).base.sortSet = false) :
    {{ akCallEnv cl api conn s E ρ cid mid γa Lset n who ∗ ctxOk ci cd ∗ ctxErrClient ci cd ∗
        optsAt sl gs }}
      (App (App (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
          go!"Get")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        ⌜err ≠ GoInterface.nil⌝ ∨
        (⌜err = GoInterface.nil⌝ ∗ ∃ m : RangeRespM, rangeRespMsg resp m ∗
          ⌜(∃ (r : Nat) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (e : GoString),
              akUser who info.Username' ∧
              apply.authEndOf (rangeWireOf (opGetModel key gs)).base.rangeEnd e ∧
              auth.granted (setupSt r) (auth.authInfoM info) (rangeWireOf (opGetModel key gs)).key
                e .read) ∧
            ∀ kv ∈ m.kvs, inRange (rangeWireOf (opGetModel key gs)).key
              (rangeWireOf (opGetModel key gs)).base.rangeEnd kv.key = true⌝) }} := by
  iintro %Φ ⟨#Henv, #Hctx, #Hce, #Hopts⟩ HΦ
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
  · unfold committedAtLeast
    rw [show uint.nat (W64 0) = 0 from rfl]
    iexact H0
  ihave Hres := optsAt_res sl gs iprop(True) $$ Hopts
  iapply wp_fupd
  wp_apply (client_Get_on cl api conn _ s E ρ.rd cid mid (W64 0) n ci cd key sl gs iprop(True)
      (fun _ => iprop(True)) []) $$ [Hres] as %resp %err Hout
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
  · ihave #Hseen := akTokSeen_attempt γa who conn md (by rw [← hout]; exact Hmd) $$ Hat
    imod (akRead_granted s E γa ρ ρ.rd Lset n who (W64 0) _ _ hγa) $$ [] Hauth with %Hg
    · iframe #
    imodintro
    iapply HΦ
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
    ileft
    ipureintro; exact Herr.1

end calls

end authkv
end EtcdGrove
end Perennial

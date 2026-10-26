/-
**A client of etcd's KV meets the recipes' put and delete contracts** (D48, 2026-10-26).
Lean-first, no Rocq counterpart.

As `KMGet.lean` for gets: the call is `kv.Put.spec`'s (`kv.Delete.spec`'s), with the adapter's
write update after the floor the caller knows (`km_write_au` at `km_reached_lb`'s changes); its
reply's state `σ` (a well-formed log's, `kvLogOk`) is one the client saw, and so is the state
after the write (`kmWriteQ`'s lower bound of its changes), whose log is `σ`'s with the write's
revision. The pure reasoning is `ServerKVPut.lean`'s (`applyTxnOp_put_underPfx`, ...), on `σ`'s
log instead of the apply thread's.

* `putResult_of_km`, `deleteResult_of_km`: what a write's reply gives the model, the state after
  it well formed (`kvLogOk`, which the specs give of the state after a write).
* `isEtcdPutKVTodo_of_km`, `isEtcdDeleteKVTodo_of_km`: the recipes' contracts. A put with a lease
  or that needs the key's previous key-value (`kv.Put.spec` covers neither, or does not say such
  a put wrote) by the premise `kmPutRestTodo`; a delete given that etcd reached revision `1`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.ServerKVPut
public import Proof.go_etcd_io.etcd.client.v3.EtcdModelKV
public import Proof.go_etcd_io.etcd.client.v3.Link

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace client

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver
  mvcc txn

/-! ## The state after a write -/

/-- A commit of changes appends them to the log. -/
theorem commit_log (σ : KVState) (cs : List Change) (h : cs ≠ []) :
    (σ.commit cs).log = σ.log ++ [cs] := by
  simp [KVState.commit, KVState.log, h]

/-- A put that needs no previous key-value commits its change. -/
theorem kvOpStep_put (w : OpFull) (σ : KVState) (h : txn.needsPrev w = false) :
    kvOpStep (.put w) σ = σ.commit [putChangeOf w (findKey w.key σ.kvs)] := by
  simp [kvOpStep, h]

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **What a put's reply gives the clients' model** (see the file header): for the put `w` (one
that needs no previous key-value) of the operation `op` under `pfx`, the reply's state `σ` met
after the changes `l0` (at least `lo` of them), `σ` and the state after the put well formed:
`putResult`, its revision `σ`'s next, with its token. -/
theorem putResult_of_km (γ : KMNames) [KMWritable γ] (pfx : GoString) (lo : w64) (w : OpFull) (op : TxnOp)
    (hw : putTxnOp w = op) (hu : op.Under pfx) (hnp : txn.needsPrev w = false)
    (l0 : List (List Change)) (hlo : sint.Z lo ≤ l0.length) (σ : KVState) (hok : kvLogOk σ)
    (h63 : σ.rev + 4 < 2 ^ 63) (hpost : kvLogOk (kvOpStep (.put w) σ)) :
    kmWriteQ (GF := GF) γ l0 (.put w) σ ⊢
      putResult (EM := etcdModelOfKV γ) pfx lo op GoInterface.nil := by
  subst hw
  have hst := kvOpStep_put w σ hnp
  have hkvs := kvLogOk_kvs σ hok
  have hrc := kvLogOk_rev σ hok
  have hll := (kvLogOk_log hok).2.2.2
  have hne : [putChangeOf w (findKey w.key σ.kvs)] ≠ [] := by simp
  have hrev' := KVState.commit_rev σ _ hne
  have hlog' := commit_log σ _ hne
  rw [hst] at hpost
  unfold kmWriteQ
  rw [hst, hrev', if_pos rfl]
  iintro ⟨#Hlb', #Hlb, %Hpre, Htok⟩
  obtain ⟨hg, hd, ht, hres⟩ := putTxnOp_putLike w
  have hS := stateAfter_sorted σ.log
  have hr : sint.Z (W64 ((σ.rev + 1 : Nat) : Int)) = σ.rev + 1 := by word
  have hr1 : W64 ((σ.rev + 1 : Nat) : Int) - W64 1 = W64 (σ.rev : Int) := by word
  have hrun : runTxn (W64 ((σ.rev + 1 : Nat) : Int)) (underPfx pfx (stateAfter σ.log))
      (putTxn (putTxnOp w)) =
      (true, underPfx pfx (applyTxnOp (W64 ((σ.rev + 1 : Nat) : Int)) (stateAfter σ.log)
        (putTxnOp w)).1, [.put]) := by
    have := applyTxnOp_put_underPfx pfx (W64 ((σ.rev + 1 : Nat) : Int)) (stateAfter σ.log) hS
      (putTxnOp w) hg hd ht hu
    simp only [runTxn, putTxn, TxnModel.branch, List.all_nil, ↓reduceIte, runOps, this, hres]
  have e2 : stateAfter (σ.commit [putChangeOf w (findKey w.key σ.kvs)]).log =
      (applyTxnOp (W64 ((σ.rev + 1 : Nat) : Int)) (stateAfter σ.log) (putTxnOp w)).1 := by
    rw [hlog', hkvs, stateAfter_put, hll]
  have hlo' : sint.Z lo ≤ σ.rev := by have := Hpre.length_le; omega
  ihave ⟨#Hs1, %Hwf1⟩ := km_etcdState_last γ σ pfx hok $$ Hlb
  ihave ⟨#Hs2, -⟩ := km_etcdState_last γ _ pfx hpost $$ Hlb'
  ihave ⟨#Hreach, -⟩ := km_reached_of γ (σ.commit [putChangeOf w (findKey w.key σ.kvs)]).changes
    (σ.rev + 1) (by have := kvLogOk_rev _ hpost; omega) (by omega) $$ Hlb'
  rw [hrev', e2]
  unfold putResult
  iright
  isplitr
  · ipureintro; rfl
  iexists (W64 ((σ.rev + 1 : Nat) : Int)), (underPfx pfx (stateAfter σ.log))
  rw [hrun]
  iframe Hreach
  isplitr
  · ipureintro
    refine ⟨by rw [hr]; omega, by rw [hr]; omega, by rw [hr]; omega, Hwf1⟩
  isplitr
  · unfold txnStates
    simp only [txnWrote, List.any_cons, List.any_nil, TxnOpResult.wrote, Bool.or_false,
      ↓reduceIte]
    rw [etcdModelOfKV_etcdState, hr1]
    isplitl
    · iexact Hs1
    · iexact Hs2
  · rw [etcdModelOfKV_etcdRevToken]
    unfold kmRevTok
    rw [hr, show ((σ.rev : Int) + 1).toNat = σ.rev + 1 by omega]
    iexact Htok

/-- **What a delete's reply gives the clients' model** (as `putResult_of_km`): for the delete `o`
of a range under `pfx` (the server's `deleteWireOf o`), the reply's state `σ` met after the
changes `l0` (at least `lo` of them, and one), `σ` and the state after the delete well formed:
`deleteResult`, its revision `σ`'s next if it deleted a key, `σ`'s otherwise. -/
theorem deleteResult_of_km (γ : KMNames) [KMWritable γ] (pfx : GoString) (lo : w64) (o : OpFull)
    (hu : KeyRangeUnder pfx o.key o.base.rangeEnd)
    (l0 : List (List Change)) (hlo : sint.Z lo ≤ l0.length) (h1 : 1 ≤ l0.length)
    (σ : KVState) (hok : kvLogOk σ)
    (h63 : σ.rev + 4 < 2 ^ 63) (hpost : kvLogOk (kvOpStep (.deleteRange (deleteWireOf o)) σ)) :
    kmWriteQ (GF := GF) γ l0 (.deleteRange (deleteWireOf o)) σ ⊢
      deleteResult (EM := etcdModelOfKV γ) pfx lo o GoInterface.nil := by
  have hkvs := kvLogOk_kvs σ hok
  have hrc := kvLogOk_rev σ hok
  have hll := (kvLogOk_log hok).2.2.2
  have hrin : rangeIn (stateAfter σ.log) (deleteWireOf o) = rangeIn (stateAfter σ.log) o := rfl
  have hrun : ∀ r, runTxn r (underPfx pfx (stateAfter σ.log)) (deleteTxn o) =
      (true, underPfx pfx (applyTxnOp r (stateAfter σ.log) (.delete o)).1,
        [.delete (rangeIn (stateAfter σ.log) o).length]) := by
    intro r
    have := applyTxnOp_delete_underPfx pfx r (stateAfter σ.log) o hu
    simp only [runTxn, deleteTxn, TxnModel.branch, List.all_nil, ↓reduceIte, runOps, this]
    simp [applyTxnOp]
  have hst : kvOpStep (.deleteRange (deleteWireOf o)) σ =
      σ.commit (delChanges (stateAfter σ.log) (deleteWireOf o)) := by
    simp only [kvOpStep, hkvs]
  rw [hst] at hpost
  unfold kmWriteQ
  rw [hst]
  unfold deleteResult
  by_cases hE : rangeIn (stateAfter σ.log) o = []
  · -- nothing deleted: the state as it was, the revision its last
    have hdc : delChanges (stateAfter σ.log) (deleteWireOf o) = [] := by
      simp [delChanges, hrin, hE]
    rw [hdc, KVState.commit_nil]
    iintro ⟨#Hlb', #Hlb, %Hpre, -⟩
    have hlo' : sint.Z lo ≤ σ.rev := by have := Hpre.length_le; omega
    have h1' : 1 ≤ σ.rev := by have := Hpre.length_le; omega
    have hr : sint.Z (W64 (σ.rev : Int)) = σ.rev := by word
    ihave ⟨#Hs1, %Hwf1⟩ := km_etcdState_last γ σ pfx hok $$ Hlb
    ihave ⟨#Hreach, -⟩ := km_reached_of γ σ.changes σ.rev (by omega) (by omega) $$ Hlb
    iright
    isplitr
    · ipureintro; rfl
    iexists (W64 (σ.rev : Int)), (underPfx pfx (stateAfter σ.log))
    rw [hrun]
    iframe Hreach
    isplitr
    · ipureintro
      refine ⟨by rw [hr]; omega, by rw [hr]; omega, by rw [hr]; omega, Hwf1⟩
    unfold txnStates
    simp only [txnWrote, List.any_cons, List.any_nil, TxnOpResult.wrote, Bool.or_false, hE,
      List.length_nil, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    rw [etcdModelOfKV_etcdState]
    iexact Hs1
  · -- a key deleted: the next revision
    have hdc : delChanges (stateAfter σ.log) (deleteWireOf o) ≠ [] := by
      simp [delChanges, hrin, hE]
    have hrev' := KVState.commit_rev σ _ hdc
    have hlog' := commit_log σ _ hdc
    rw [hrev', if_pos rfl]
    iintro ⟨#Hlb', #Hlb, %Hpre, -⟩
    have hr : sint.Z (W64 ((σ.rev + 1 : Nat) : Int)) = σ.rev + 1 := by word
    have hr1 : W64 ((σ.rev + 1 : Nat) : Int) - W64 1 = W64 (σ.rev : Int) := by word
    have e2 : stateAfter (σ.commit (delChanges (stateAfter σ.log) (deleteWireOf o))).log =
        (applyTxnOp (W64 ((σ.rev + 1 : Nat) : Int)) (stateAfter σ.log) (.delete o)).1 := by
      have := stateAfter_commit_delete σ.log (deleteWireOf o)
      simp only [commitLog, hdc, ↓reduceIte] at this
      rw [hlog', this, hll]
      rfl
    have hlo' : sint.Z lo ≤ σ.rev := by have := Hpre.length_le; omega
    ihave ⟨#Hs1, %Hwf1⟩ := km_etcdState_last γ σ pfx hok $$ Hlb
    ihave ⟨#Hs2, -⟩ := km_etcdState_last γ _ pfx hpost $$ Hlb'
    ihave ⟨#Hreach, -⟩ := km_reached_of γ
      (σ.commit (delChanges (stateAfter σ.log) (deleteWireOf o))).changes
      (σ.rev + 1) (by have := kvLogOk_rev _ hpost; omega) (by omega) $$ Hlb'
    rw [hrev', e2]
    have hne : ((rangeIn (stateAfter σ.log) o).length != 0) = true := by
      simp [List.length_eq_zero_iff, hE]
    iright
    isplitr
    · ipureintro; rfl
    iexists (W64 ((σ.rev + 1 : Nat) : Int)), (underPfx pfx (stateAfter σ.log))
    rw [hrun]
    iframe Hreach
    isplitr
    · ipureintro
      refine ⟨by rw [hr]; omega, by rw [hr]; omega, by rw [hr]; omega, Hwf1⟩
    unfold txnStates
    simp only [txnWrote, List.any_cons, List.any_nil, TxnOpResult.wrote, Bool.or_false, hne,
      ↓reduceIte]
    rw [etcdModelOfKV_etcdState, hr1]
    isplitl
    · iexact Hs1
    · iexact Hs2

end proofs

/-! ## The bridges -/

section bridges
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **The puts `kv.Put.spec` does not cover, in the clients' model** (a premise, persistent; as
`ServerKVPut.lean`'s `kvLeasedPutTodo`): the recipes' put contract for a put with a lease, or one
that needs the key's previous key-value (`WithIgnoreValue`, `WithIgnoreLease`: `txn.needsPrev`;
the spec's reply does not say that such a put wrote, so gives no revision token). -/
def kmPutRestTodo (api : Loc) (γ : KMNames) [KMWritable γ] (pfx : GoString) : IProp GF :=
  iprop(□ ∀ (key val : GoString) (sl : GoSlice) (gs : List (OpFull → OpFull)) (op : TxnOp)
      (lo : w64),
    ⌜¬ (opPutModel key val gs).putPanics ∧ txnOpOf (opPutModel key val gs) = some op ∧
      op.Under pfx ∧ (opPutModel key val gs).t = W64 2 ∧
      ((putWireOf (opPutModel key val gs)).leaseID ≠ W64 0 ∨
        txn.needsPrev (putWireOf (opPutModel key val gs)) = true)⌝ -∗
    {{ optsAt sl gs ∗ etcdReached (EM := etcdModelOfKV γ) lo }}
      (App (App (App (App (Val #(methods (kvIfaceOf api).ty go!"Put" (kvIfaceOf api).v))
        (Val #(GoInterface.ok todoCtxVal))) (Val #key)) (Val #val)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        putResult (EM := etcdModelOfKV γ) pfx lo op err }})

instance kmPutRestTodo_persistent (api : Loc) (γ : KMNames) [KMWritable γ] (pfx : GoString) :
    Persistent (kmPutRestTodo (GF := GF) api γ pfx) := by
  unfold kmPutRestTodo; infer_instance

/-- **A client of etcd's KV meets the recipes' put contract** (`isEtcdPutKVTodo`) at the adapter's
model: `kv.Put(context.TODO(), ...)` returns `putResult` (`putResult_of_km`), a put with no lease
that needs no previous key-value by `kv.Put.spec` with the adapter's write update (fired at most
once: `isKv api γ.kv false`), any other by the premise `kmPutRestTodo`; `errors.As` can take
`*rpctypes.EtcdError` (`hAs`, `todo_ctx`). -/
theorem isEtcdPutKVTodo_of_km (api : Loc) (γ : KMNames) [KMWritable γ] (pfx : GoString)
    (hAs : errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ isKv api γ.kv false ∗
        kmInv γ ∗ kmPutRestTodo api γ pfx ⊢
      isEtcdPutKVTodo (EM := etcdModelOfKV γ) (kvIfaceOf api) pfx := by
  iintro ⟨#Pc, #Hkv, #Hinv, #Hrest⟩
  unfold isEtcdPutKVTodo
  iintro !> %key %val %sl %gs %op %lo %Φ !> ⟨#Hopts, #Hlo, %Hp⟩ HΦ
  obtain ⟨hpan, hop, hu, ht⟩ := Hp
  have hw := putTxnOp_wire _ _ hop ht
  by_cases hl : (putWireOf (opPutModel key val gs)).leaseID = W64 0 ∧
    txn.needsPrev (putWireOf (opPutModel key val gs)) = false
  rotate_left
  · have hl' : (putWireOf (opPutModel key val gs)).leaseID ≠ W64 0 ∨
        txn.needsPrev (putWireOf (opPutModel key val gs)) = true := by
      by_cases h0 : (putWireOf (opPutModel key val gs)).leaseID = W64 0
      · right; simpa [h0] using hl
      · left; exact h0
    iunfold kmPutRestTodo at Hrest
    ihave #Ht := Hrest $$ %key %val %sl %gs %op %lo %(⟨hpan, hop, hu, ht, hl'⟩)
    iapply Ht $$ [] HΦ
    iframe #
  imod (todo_ctx (GF := GF) hAs) with ⟨%cd, #Hctx, #Hce⟩
  imod km_reached_lb γ lo $$ Hlo with ⟨%l0, #Hl0, %Hll⟩
  ihave Hau := km_write_au γ l0 (.put (putWireOf (opPutModel key val gs))) (KMWritable.keep _) $$ [$Hinv $Hl0]
  iunfold kvOpAu1 at Hau
  iunfold kvAu1 at Hau
  iapply (v3.kv.wp_Put api γ.kv false todoCtxVal cd key val sl gs
    (kmWriteQ γ l0 (.put (putWireOf (opPutModel key val gs))))) $$ [Hau]
  · iframe #
    isplitl []
    · ipureintro; exact ⟨hpan, ht, hl.1⟩
    iexact Hau
  inext
  iintro %resp %err Hout
  iapply HΦ
  icases Hout with (⟨%Herr, %m, %σ, -, HQ, %Hs⟩ | ⟨%Herr, -⟩)
  · subst Herr
    obtain ⟨-, -, h63, hok, hpost⟩ := Hs
    iapply (putResult_of_km γ pfx lo _ op hw hu hl.2 l0 Hll σ hok h63 hpost) $$ HQ
  · unfold putResult
    ileft
    ipureintro; exact Herr.1

/-- **A client of etcd's KV meets the recipes' delete contract** (`isEtcdDeleteKVTodo`) at the
adapter's model: `kv.Delete(context.TODO(), ...)` returns `deleteResult` (`deleteResult_of_km`),
by `kv.Delete.spec` with the adapter's write update (fired at most once: `isKv api γ.kv false`),
given that etcd has reached revision `1` (`kmReachedAt γ (W64 1)`: a delete that deletes nothing
answers the state's revision, which the contract has positive; etcd's store starts at revision
`1`) and that `errors.As` can take `*rpctypes.EtcdError` (`hAs`). -/
theorem isEtcdDeleteKVTodo_of_km (api : Loc) (γ : KMNames) [KMWritable γ] (pfx : GoString)
    (hAs : errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ isKv api γ.kv false ∗
        kmInv γ ∗ kmReachedAt γ (W64 1) ⊢
      isEtcdDeleteKVTodo (EM := etcdModelOfKV γ) (kvIfaceOf api) pfx := by
  iintro ⟨#Pc, #Hkv, #Hinv, #H1⟩
  unfold isEtcdDeleteKVTodo
  iintro !> %key %sl %gs %lo %Φ !> ⟨#Hopts, #Hlo, %Hp⟩ HΦ
  obtain ⟨hpan, hu, hz, ht⟩ := Hp
  imod (todo_ctx (GF := GF) hAs) with ⟨%cd, #Hctx, #Hce⟩
  imod km_reached_lb γ lo $$ Hlo with ⟨%l0, #Hl0, %Hll⟩
  -- the longer of the floor and the first revision's changes
  iunfold kmReachedAt at H1
  icases H1 with ⟨%l1, #Hl1, %H1l⟩
  ihave %Hcmp := mono_list_lb_valid γ.ch l0 l1 $$ Hl0 Hl1
  have h1z : sint.Z (W64 1) = 1 := by decide
  ihave ⟨%L, #HL, %HLl⟩ : ∃ L : List (List Change), monoListLbOwn γ.ch L ∗
      ⌜sint.Z lo ≤ L.length ∧ 1 ≤ L.length⌝ $$ []
  · rcases Hcmp with h | h
    · iexists l1; iframe Hl1; ipureintro
      have := h.length_le; omega
    · iexists l0; iframe Hl0; ipureintro
      have := h.length_le; omega
  ihave Hau := km_write_au γ L (.deleteRange (deleteWireOf (opDeleteModel key gs))) (KMWritable.keep _) $$ [$Hinv $HL]
  iunfold kvOpAu1 at Hau
  iunfold kvAu1 at Hau
  iapply (v3.kv.wp_Delete api γ.kv false todoCtxVal cd key sl gs
    (kmWriteQ γ L (.deleteRange (deleteWireOf (opDeleteModel key gs))))) $$ [Hau]
  · iframe #
    isplitl []
    · ipureintro; exact ⟨hpan, ht, by simpa [deleteWireOf, txn.deleteOpOf] using hz⟩
    iexact Hau
  inext
  iintro %resp %err Hout
  iapply HΦ
  icases Hout with (⟨%Herr, %m, %σ, -, HQ, %Hs⟩ | ⟨%Herr, -⟩)
  · subst Herr
    obtain ⟨-, -, -, h63, hok, hpost⟩ := Hs
    iapply (deleteResult_of_km γ pfx lo _ hu L HLl.1 HLl.2 σ hok h63 hpost) $$ HQ
  · unfold deleteResult
    ileft
    ipureintro; exact Herr.1

end bridges


end client
end EtcdGrove
end Perennial

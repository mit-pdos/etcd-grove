/-
The pure and persistent facts `RunAuthLease.wp_proof` uses at its checks (F7 stage S5): the anonymous and the
bad client's lease checks refuted at a member whose floor is above the frozen set-up (`noAuth_refutesD`,
`noAuth`'s last premise), u's put of `a/lease` with root's lease `Lz` refused (`uPutA_neqD`, `cell_putAAu`'s
premise at the view's grant `opGrantD`), and the leased transaction's model facts `Txn_CommitOn_dist` asks
(`leaseTxnD_model`). Ports of the single-process `noAuth_refutes`, `grantG_refuted` use and `leaseTxn_ok`'s
model half (`Proof/.../examples/etcd/authlease/run.lean`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.AuthLeaseTxn
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.AuthFrozenFloor

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic Iris.Std Net go_etcd_io.etcd.server.v3.etcdserver client
open etcd_dist etcd_dist.authd etcd_authlease

section pure
variable [GooseExts]

/-- `Txn().Then(OpPut(k, "v", WithLease(L)))`'s model is plain (no nested transaction) and has no read. -/
theorem leaseTxnD_model (k : GoString) (L : w64) :
    TxnModel.plain (leaseTxn k L) ∧ txnModelIn (txnWireOf (leaseTxn k L)) := by
  constructor
  · simp [TxnModel.plain, TxnOp.plain]
  · intro o ho
    simp [txnWireOf, opWire] at ho

end pure

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **No lease call of the anonymous principal passes at a member above the frozen set-up**
(`noAuth.spec`'s last premise, at the member's floor `m` from a barrier at `Lset`): `authFloorD_frozen`
fixes the member's auth states from an index `i ≤ m` on at `setupSt r`, where `leaseCheckD_none_frozen`
refutes an anonymous check. -/
theorem noAuth_refutesD (Γ : DistView) (γR : ServerRaftNames) (mid : w64) (Lset : List EntryModel) (m : Nat)
    (γz : GName) (hs : List auth.AuthState) (r : Nat) (hadm : admStates Γ.kv srvAuthSt0 Lset = hs)
    (hst : srvAuthAtLog Γ.kv srvAuthSt0 Lset = etcd_auth.setupSt r) :
    ⊢ kvInvOn (GF := GF) γR Γ.kv srvAuthSt0 -∗ authHistFrozen Γ.kv γz hs -∗ authFloorD Γ γR mid Lset m -∗
      □ (∀ (n : Nat) (K : go_etcd_io.etcd.server.v3.auth.AuthInfo → IProp GF), ⌜m ≤ n⌝ -∗
          leaseCheckD (Γ.au mid) none n K ={⊤}=∗ False) := by
  iintro #Hk #Hz #Hf
  ihave ⟨%i, %hi, #Hfz⟩ := authFloorD_frozen Γ γR mid Lset Lset m γz hs r (List.prefix_refl _) hadm hst ⊤
    CoPset.subseteq_top $$ Hk Hz Hf
  iintro !> %n %K %hn Hc
  ihave H := leaseCheckD_none_frozen (GF := GF) (Γ.au mid) i n r (by omega) ⊤ K $$ Hfz
  iapply H
  iexact Hc

/-- **u's put of `a/lease` with root's lease is refused** (`cell_putAAu`'s premise at the view's grant
`opGrantD` of u's put, at the set-up's prefix `Lset`): while `z/lease` holds `Lz`, a grant of the put with
`Lz` is a grant at `setupSt` (`akGrantedL_of_writeGrantGD`) of a request checking `Lz`, which u may not
use (`not_akGrantedL_lease`: `z/lease` is outside u's range). -/
theorem uPutA_neqD (γk : KVNames) (γz : GName) (hs : List auth.AuthState) (Lset : List EntryModel) (r : Nat)
    (hadm : admStates γk srvAuthSt0 Lset = hs) (hst : srvAuthAtLog γk srvAuthSt0 Lset = etcd_auth.setupSt r)
    (Lz id : w64) (hLz : Lz ≠ W64 0) :
    authHistFrozen (GF := GF) γk γz hs ⊢
      □ (∀ σ : KVState, ⌜leaseOf zK σ.kvs = some Lz⌝ -∗
        opGrantD γk (some go!"u") (.put (leasePutOp aK id)) Lset σ ={cellM}=∗ ⌜id ≠ Lz⌝) := by
  iintro #Hz
  iintro !> %σ %hk HG
  by_cases hil : id = Lz
  · have hop := opChecksLeaseD_put (GF := GF) γk (some go!"u") (leasePutOp aK id)
    ihave HG := hop Lset σ $$ HG
    icases HG with ⟨%rq, %hrq, HG⟩
    imod (akGrantedL_of_writeGrantGD γk γz hs Lset Lset r (some go!"u") go!"u" rq σ cellM authHistN_cellM
      (List.prefix_refl _) hadm hst (userOk_some_akUser go!"u" (Or.inl rfl))) $$ Hz HG with %Hg
    have hk' : leaseOf zK σ.kvs = some id := by rw [hil]; exact hk
    have hL' : id ≠ W64 0 := by rw [hil]; exact hLz
    exact absurd Hg (not_akGrantedL_lease go!"u" σ rq zK id hk' hL'
      (Or.inr (Or.inr (Or.inr ⟨rfl, not_inRangeK_zK⟩))) hrq)
  · imodintro
    ipureintro
    exact hil

/-- **Root's grant fixed, then its put of `z/lease`** (`grantPut.spec`'s step for root's `grantPut(root,
zKey)`, any principal): the granted id is recorded first in the cell (`cell_fix`), and the put's update
records the first attachment (`cell_putZAu`). -/
theorem fixZD (γk : KVNames) (γc : CellNames) (P : Option GoString) (L₀ : List EntryModel) :
    cellInv (GF := GF) γk γc ∗ monoListLbOwn γc.ps ([] : List Nat) ⊢
      ∀ id : w64, ⌜id ≠ W64 0⌝ -∗ (∃ σ, gsHas γc id σ) -∗ monoListAuthOwn γc.ids (1 : Qp).half ([] : List w64)
        ={⊤}=∗ (monoListAuthOwn γc.ids (1 : Qp).half [id] ∗ monoListLbOwn γc.ids [id] ∗ ⌜id ≠ W64 0⌝) ∗
          writeAuD γk P (.put (putWireOf (opPutModel zK go!"v" [withLeaseM id]))) L₀ (psAtLeast γc 1) := by
  iintro ⟨#Hinv, #Hp0⟩ %id %hid ⟨%σ, Hg⟩ HR
  iunfold gsHas at Hg
  icases Hg with ⟨%gs, #Hgs, %hgs⟩
  imod (cell_fix γk γc [] id [] hid (by simp) (by simp) ⊤ (by simp)) $$ [HR] with ⟨HR', #Hlb⟩
  · iframe HR; iframe #
  imodintro
  ihave #Hlb1 : monoListLbOwn γc.ids [id] $$ []
  · iExactEq Hlb; simp
  isplitl [HR']
  · isplitl [HR']
    · iExactEq HR'; simp
    iframe Hlb1
    ipureintro; exact hid
  iunfold writeAuD
  simp only [leasePut_wire]
  ihave #Hpz := cell_putZAu γk γc id gs hgs (opGrantD γk P (.put (leasePutOp zK id)) L₀) $$ [Hlb1]
  · iframe #
  iexact Hpz

/-- **u's grant fixed, then its put of `a/lease`** (`grantPut.spec`'s step for `grantPut(ucli, aKey)`):
the id recorded second (`cell_fix`), the put's update recording the second attachment (`cell_putAAu`), its
premise `Lu ≠ Lz` from `uPutA_neqD`. -/
theorem fixAD (γk : KVNames) (γc : CellNames) (γz : GName) (hs : List auth.AuthState) (Lset : List EntryModel)
    (r : Nat) (hadm : admStates γk srvAuthSt0 Lset = hs) (hst : srvAuthAtLog γk srvAuthSt0 Lset = etcd_auth.setupSt r)
    (Lz : w64) (hLz : Lz ≠ W64 0) (ps1 : List Nat) (h1 : 1 ≤ ps1.length) :
    cellInv (GF := GF) γk γc ∗ monoListLbOwn γc.ps ps1 ∗ authHistFrozen γk γz hs ⊢
      ∀ id : w64, ⌜id ≠ W64 0⌝ -∗ (∃ σ, gsHas γc id σ) -∗ monoListAuthOwn γc.ids (1 : Qp).half [Lz]
        ={⊤}=∗ (monoListAuthOwn γc.ids (1 : Qp).half [Lz, id] ∗ monoListLbOwn γc.ids [Lz, id] ∗
            ⌜id ≠ W64 0⌝) ∗
          writeAuD γk (some go!"u") (.put (putWireOf (opPutModel aK go!"v" [withLeaseM id]))) Lset
            (psAtLeast γc 2) := by
  iintro ⟨#Hinv, #Hps1, #Hz⟩ %id %hid ⟨%σ, Hg⟩ HR
  iunfold gsHas at Hg
  icases Hg with ⟨%gs, #Hgs, %hgs⟩
  imod (cell_fix γk γc [Lz] id ps1 hid (by simp) (by simp; omega) ⊤ (by simp)) $$ [HR] with ⟨HR', #Hlb⟩
  · iframe HR; iframe #
  imodintro
  ihave #Hlb1 : monoListLbOwn γc.ids [Lz, id] $$ []
  · iExactEq Hlb; simp
  isplitl [HR']
  · isplitl [HR']
    · iExactEq HR'; simp
    iframe Hlb1
    ipureintro; exact hid
  iunfold writeAuD
  simp only [leasePut_wire]
  ihave #Hne := uPutA_neqD γk γz hs Lset r hadm hst Lz id hLz $$ Hz
  ihave #Hpa := cell_putAAu γk γc Lz id gs ps1 hgs h1 (opGrantD γk (some go!"u") (.put (leasePutOp aK id)) Lset)
    $$ [Hlb1]
  · iframe #
  iexact Hpa

end lemmas

end etcd_dist_client
end EtcdGrove
end Perennial

/-
**The dist authLease workload's refusals and cell facts** (F7 stage S5; what `RunAuthLease.wp_proof` hands
its checks): the dist ports of authlease's `akGrantedL_of_writeGrantG`, `refused_update` and `revokeLu_update`
(`Proof/.../examples/etcd/authlease/{Cell,Refusals}.lean`) over the view's grant `opGrantD` (the principal by
name, `userOk`) and the frozen set-up (`authHistFrozen` at `Lset`, its state `setupSt r`) in place of the
single-process `akAuthFixed`/`akTokSeen`; the set-up puts' offers at the view (`cell_setupAuD`); the cell read
now (`cell_seen_now`) and what a state the cell saw satisfies (`seenD_z`, `seenD_gone`, copied from
authlease's `run.lean`); the members' addresses from `leaseMember`. Lean-first (no Rocq counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.AuthCell
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.LeaseDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.AddrPlain
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.authlease.Refusals

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic Iris.Std Net go_etcd_io.etcd.server.v3.etcdserver client
open etcd_dist etcd_dist.authd etcd_authlease

section cell
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **A write granted at the view after the frozen set-up is granted at `setupSt`** (the dist
`akGrantedL_of_writeGrantG`): the grant's prefix `L ⊒ L₀ ⊒ Lset` has the frozen history (`authHistFrozen_prefix`),
so its auth state is `Lset`'s; the principal `some who` binds the header's user to `who` or the empty one. -/
theorem akGrantedL_of_writeGrantGD (γk : KVNames) (γz : GName) (hs : List auth.AuthState)
    (Lset L₀ : List EntryModel) (r : Nat) (who : GoString) (rq : apply.IRRModel) (σ : KVState)
    (Em : CoPset) (hE : ↑authHistN ⊆ Em) (hpre : Lset <+: L₀)
    (hadm : admStates γk srvAuthSt0 Lset = hs) (hst : srvAuthAtLog γk srvAuthSt0 Lset = etcd_auth.setupSt r)
    (hwho : who = go!"u" ∨ who = go!"v") :
    authHistFrozen (GF := GF) γk γz hs ⊢
      writeGrantG γk srvAuthSt0 (fun hm => iprop(⌜userOk (some who) hm.username⌝)) rq L₀ σ ={Em}=∗
        ⌜akGrantedL who σ rq⌝ := by
  iintro #Hz Hw
  ihave Hw := writeGrantG_granted γk srvAuthSt0 _ rq L₀ σ $$ Hw
  icases Hw with ⟨%hm, %L, %Hu, #Hlb, %Hp⟩
  obtain ⟨hL, hgr⟩ := Hp
  imod (authHistFrozen_prefix γk γz hs _ Em hE) $$ Hz Hlb with %Hpf
  imodintro
  ipureintro
  have h1 := admStates_prefix γk srvAuthSt0 _ _ (hpre.trans hL)
  rw [hadm] at h1
  have heq : hs = admStates γk srvAuthSt0 L :=
    h1.eq_of_length (Nat.le_antisymm h1.length_le Hpf.length_le)
  have hr : srvAuthAtLog γk srvAuthSt0 L = etcd_auth.setupSt r :=
    (srvAuthAtLog_of_admStates γk srvAuthSt0 Lset L (hadm.trans heq)).symm.trans hst
  refine ⟨r, hm, by rw [← hr]; exact hgr, ?_⟩
  unfold etcd_auth.akUser
  unfold userOk at Hu
  rcases Hu with h | h
  · exact Or.inl h
  · exact Or.inr ⟨(Option.some.inj h).symm, hwho⟩

/-- **An operation's view grant checks the lease `L`** (the dist `opChecksLease`). -/
def opChecksLeaseD (γk : KVNames) (who : GoString) (op : KVOp) (L : w64) : Prop :=
  ∀ L₀ σ, opGrantD (GF := GF) γk (some who) op L₀ σ ⊢
    ∃ rq : apply.IRRModel, ⌜∀ r (hm : apply.HeaderModel),
        leaseGrantedM (etcd_auth.setupSt r) (mvcc.leaseItemsOf σ.kvs) (apply.withHeader rq hm) →
          leaseOk (etcd_auth.setupSt r) ⟨hm.username, hm.authRevision⟩ (mvcc.leaseItemsOf σ.kvs) L⌝ ∗
      writeGrantG γk srvAuthSt0 (fun hm => iprop(⌜userOk (some who) hm.username⌝)) rq L₀ σ

theorem opChecksLeaseD_put (γk : KVNames) (who : GoString) (o : OpFull) :
    opChecksLeaseD (GF := GF) γk who (.put o) o.leaseID := by
  intro L₀ σ
  iintro H
  iexists irrPut o
  isplitl []
  · ipureintro; exact fun r hm h => leaseGranted_put r _ o hm h
  iunfold opGrantD at H
  iexact H

theorem opChecksLeaseD_revoke (γk : KVNames) (who : GoString) (id : w64) :
    opChecksLeaseD (GF := GF) γk who (.leaseRevoke id) id := by
  intro L₀ σ
  iintro H
  iexists irrLeaseRevoke id
  isplitl []
  · ipureintro; exact fun r hm h => leaseGranted_revoke r _ id hm h
  iunfold opGrantD at H
  iexact H

theorem opChecksLeaseD_txn (γk : KVNames) (who : GoString) (k : GoString) (L : w64) :
    opChecksLeaseD (GF := GF) γk who (.txn (txnWireOf (leaseTxn k L))) L := by
  intro L₀ σ
  iintro H
  iunfold opGrantD at H
  icases H with ⟨%tw, %htw, H⟩
  iexists irrTxn tw
  isplitl []
  · ipureintro; exact fun r hm h => leaseGranted_txn r _ tw k L htw hm h
  iexact H

/-- **A write of `who`'s refused at every state the cell holds** (the dist `refused_update`): its grant
checks the lease `L`, held on `k` at those states, which `who` may not write. -/
theorem refused_updateD (γk : KVNames) (γc : CellNames) (γz : GName) (hs : List auth.AuthState)
    (Lset L₀ : List EntryModel) (r : Nat) (who : GoString) (op : KVOp) (k : GoString) (L : w64)
    (pre : List w64) (ps0 : List Nat) (Q : KVState → IProp GF)
    (hpre : Lset <+: L₀) (hadm : admStates γk srvAuthSt0 Lset = hs)
    (hst : srvAuthAtLog γk srvAuthSt0 Lset = etcd_auth.setupSt r)
    (hop : opChecksLeaseD (GF := GF) γk who op L)
    (hcell : ∀ σ ids ps gs d, CellOk σ ids ps gs d → pre <+: ids → ps0.length ≤ ps.length →
      leaseOf k σ.kvs = some L ∧ L ≠ W64 0)
    (hwho : who = go!"v" ∨ (who = go!"u" ∧ ¬ etcd_auth.inRangeK k)) :
    cellInv γk γc ∗ monoListLbOwn γc.ids pre ∗ monoListLbOwn γc.ps ps0 ∗ authHistFrozen γk γz hs ⊢
      writeAuD γk (some who) op L₀ Q := by
  have hw1 : who = go!"u" ∨ who = go!"v" := by
    rcases hwho with h | ⟨h, -⟩
    · exact Or.inr h
    · exact Or.inl h
  have hw2 : who = go!"anon" ∨ who = go!"bad" ∨ who = go!"v" ∨ (who = go!"u" ∧ ¬ etcd_auth.inRangeK k) := by
    rcases hwho with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  iintro ⟨#Hinv, #Hi0, #Hp0, #Hz⟩
  ihave #Hau := cell_refusedAu γk γc op (opGrantD γk (some who) op L₀) Q $$ []
  · isplitl []
    · iexact Hinv
    iintro !> %σ %ids %ps %gs %d %HS Hids Ha HG
    ihave %Hpre := ids_of_lb γc ids pre $$ Hids Hi0
    iunfold cellAuth at Ha
    icases Ha with ⟨Hp, -, -, -⟩
    ihave %Hps := len_of_lb γc ps ps0 $$ Hp Hp0
    obtain ⟨hk, hL⟩ := hcell σ ids ps gs d HS Hpre Hps
    ihave HG := hop L₀ σ $$ HG
    icases HG with ⟨%rq, %hrq, HG⟩
    imod (akGrantedL_of_writeGrantGD γk γz hs Lset L₀ r who rq σ cellM authHistN_cellM hpre hadm hst hw1)
      $$ Hz HG with %Hg
    exact absurd Hg (not_akGrantedL_lease who σ rq k L hk hL hw2 hrq)
  iunfold writeAuD
  imodintro
  iexact Hau

/-- **v's revocation of `Lu` under the cell** (the dist `revokeLu_update`): refuted while `a/lease` holds
`Lu`, a no-op after u's revocation; it tells `revoked`. -/
theorem revokeLu_updateD (γk : KVNames) (γc : CellNames) (γz : GName) (hs : List auth.AuthState)
    (Lset L₀ : List EntryModel) (r : Nat) (Lz Lu : w64) (ps0 : List Nat) (h3 : 3 ≤ ps0.length)
    (hLu : Lu ≠ W64 0) (hpre : Lset <+: L₀) (hadm : admStates γk srvAuthSt0 Lset = hs)
    (hst : srvAuthAtLog γk srvAuthSt0 Lset = etcd_auth.setupSt r) :
    cellInv γk γc ∗ monoListLbOwn γc.ids [Lz, Lu] ∗ monoListLbOwn γc.ps ps0 ∗ authHistFrozen γk γz hs ⊢
      writeAuD (GF := GF) γk (some go!"v") (.leaseRevoke Lu) L₀ (revoked γc) := by
  iintro ⟨#Hinv, #Hi0, #Hp0, #Hz⟩
  ihave #Hau := cell_revokeLuAu γk γc Lz Lu ps0 h3 (opGrantD γk (some go!"v") (.leaseRevoke Lu) L₀) $$ []
  · iframe Hinv Hi0 Hp0
    iintro !> %σ %ha HG
    iunfold opGrantD at HG
    imod (akGrantedL_of_writeGrantGD γk γz hs Lset L₀ r go!"v" (irrLeaseRevoke Lu) σ cellM authHistN_cellM
      hpre hadm hst (Or.inr rfl)) $$ Hz HG with %Hg
    exact absurd Hg (not_akGrantedL_lease _ σ _ aK Lu ha hLu (Or.inr (Or.inr (Or.inl rfl)))
      (fun r hm h => leaseGranted_revoke r _ Lu hm h))
  iunfold writeAuD
  imodintro
  iexact Hau

/-- **The set-up puts' offers at the view** (`cell_setupAu` with the view's grant). -/
theorem cell_setupAuD (γk : KVNames) (γc : CellNames) (L₀ : List EntryModel) :
    cellInv (GF := GF) γk γc ⊢ □ ∀ k : GoString, ⌜k ∈ etcd_auth.setupKeys⌝ -∗
      writeAuD γk none (.put (putWireOf (opPutModel k go!"setup" []))) L₀ (fun _ => iprop(True)) := by
  iintro #Hinv
  imodintro
  iintro %k %hk
  obtain ⟨hx, hz, ha, ht⟩ := setupKeys_other k hk
  rw [show putWireOf (opPutModel k go!"setup" []) = client.putKeyOp k go!"setup" from rfl]
  ihave #Hau := cell_writeAu γk γc (.put (client.putKeyOp k go!"setup"))
    (opGrantD γk none (.put (client.putKeyOp k go!"setup")) L₀) (fun _ => iprop(True)) $$ [Hinv]
  · isplitl []
    · iexact Hinv
    iintro !> %σ %ids %ps %gs %d %HS Hids Ha -
    imodintro
    iexists ps, gs, d
    iframe Hids Ha
    ipureintro; exact cellOk_put0 HS k go!"setup" hx hz ha ht
  iunfold writeAuD
  imodintro
  iexact Hau

/-- **The cell read now**: a state it holds, seen past the reader's `ps1`. -/
theorem cell_seen_now (γk : KVNames) (γc : CellNames) (ps1 : List Nat) (E : CoPset) (hE : ↑cellN ⊆ E) :
    cellInv (GF := GF) γk γc ∗ monoListLbOwn γc.ps ps1 ={E}=∗ ∃ σ : KVState, cellSeen γc ps1 0 σ := by
  iintro ⟨#Hinv, #Hp1⟩
  iunfold cellInv at Hinv
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%σ, %ids, %ps, %gs, %d, Hσ, Hids, Ha, Hv, Hal, %HS⟩
  iunfold cellAuth at Ha
  icases Ha with ⟨Hp, Hg, Hd, Hdo⟩
  ihave #Hidl := monoListLbOwn_get γc.ids _ ids $$ Hids
  ihave #Hpl := monoListLbOwn_get γc.ps 1 ps $$ Hp
  ihave %Hpp := mono_list_auth_lb_valid γc.ps 1 ps ps1 $$ Hp Hp1
  ihave #Hgl := monoListLbOwn_get γc.gs 1 gs $$ Hg
  ihave #Hdl := monoNatLbOwn_get γc.d 1 d $$ Hd
  ihave #Hvl := monoNatLbOwn_get γc.v 1 σ.rev $$ Hv
  imod Hclose $$ [Hσ Hids Hp Hg Hd Hdo Hv Hal] with -
  · inext; iexists σ, ids, ps, gs, d; iframe Hσ Hids Hv Hal
    isplitl [Hp Hg Hd Hdo]
    · iunfold cellAuth; iframe Hp Hg Hd Hdo
    · ipureintro; exact HS
  imodintro
  iexists σ
  iunfold cellSeen
  iexists ids, ps, gs, d
  iframe Hidl Hpl Hgl Hdl Hvl
  ipureintro; exact ⟨HS, Hpp.2, Nat.zero_le _⟩

/-- **A state the cell saw after root's attachment has `z/lease` on `Lz`** (authlease's `seen_z`). -/
theorem seenD_z (γc : CellNames) (ps1 : List Nat) (d1 : Nat) (σ : KVState) (lz : w64) (h1 : 1 ≤ ps1.length) :
    cellSeen (GF := GF) γc ps1 d1 σ ∗ monoListLbOwn γc.ids [lz] ⊢ ⌜leaseOf zK σ.kvs = some lz⌝ := by
  iintro ⟨H, #Hl⟩
  iunfold cellSeen at H
  icases H with ⟨%ids, %ps, %gs, %d, %h, #Hil, -⟩
  ihave %Hc := mono_list_lb_valid γc.ids ids [lz] $$ Hil Hl
  ipureintro
  obtain ⟨hok, hps, -⟩ := h
  have hp1 : 1 ≤ ps.length := Nat.le_trans h1 hps.length_le
  have hz := hok.1.z_at hp1
  have hi1 := hok.1.ps_ids.2.1 hp1
  have hl : lzOf ids = lz := by
    rcases Hc with ⟨t, ht⟩ | ⟨t, ht⟩
    · cases ids with
      | nil => simp at hi1
      | cons a r => simp at ht; simp [lzOf, ht.1]
    · subst ht; simp [lzOf]
  rw [hz, hl]

/-- **A state the cell saw after u's revocation has neither `a/lease` nor `a/txn`** (authlease's
`seen_gone`). -/
theorem seenD_gone (γc : CellNames) (ps1 : List Nat) (σ : KVState) :
    cellSeen (GF := GF) γc ps1 1 σ ⊢ ⌜mvcc.findKey aK σ.kvs = none ∧ mvcc.findKey tK σ.kvs = none⌝ := by
  iintro H
  iunfold cellSeen at H
  icases H with ⟨%ids, %ps, %gs, %d, %h, -⟩
  ipureintro
  obtain ⟨hok, -, hd⟩ := h
  exact hok.1.gone (by have := hok.1.d_le; omega)

end cell

section members
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- The endpoints of lease members are members of the view. -/
theorem membersAt_of_leaseMembers [π : NetProtoGS] (Γ : DistView) (addrs : List GoString) :
    ([∗list] a ∈ addrs, leaseMember (Gg := hG.goose_globalGS) Γ a) ⊢
      membersAt (Gg := hG.goose_globalGS) addrs Γ := by
  iintro H
  iunfold membersAt
  iapply (BigSepL.bigSepL_mono (fun {_ a} _ => by
    iintro H
    iunfold leaseMember at H
    icases H with ⟨-, %mid, Ha, -⟩
    iexists mid
    iexact Ha))
  iexact H

/-- The endpoints of lease members are valid addresses. -/
theorem addrOk_of_leaseMembers [π : NetProtoGS] (Γ : DistView) :
    ∀ addrs : List GoString, ([∗list] a ∈ addrs, leaseMember (Gg := hG.goose_globalGS) Γ a) ⊢
      ⌜∀ a ∈ addrs, Net.addrOk a = true⌝
  | [] => by iintro -; ipureintro; simp
  | a :: L => by
    iintro H
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨Ha, H⟩
    iunfold leaseMember at Ha
    icases Ha with ⟨%h1, -⟩
    ihave %h2 := addrOk_of_leaseMembers Γ L $$ H
    ipureintro
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h1
    · exact h2 x hx

end members

end etcd_dist_client
end EtcdGrove
end Perennial

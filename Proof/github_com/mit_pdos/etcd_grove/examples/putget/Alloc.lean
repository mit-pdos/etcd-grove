/-
**The ghost state `Main` allocates before `NewServer`** (item 9, stage 2, 2026-10-18). Lean-first
(no Rocq counterpart).

`putget_alloc`: for the one-member cluster `{id}` and its bootstrap log (`BootFacts`), at the
leases-off workload `putgetWorkload` (D19q), everything `NewServer.spec` takes of the ghost state:
raft's cluster ghost state for a new cluster with the server's continuation
(`srvRaftBoot_alloc`: the read names, the KV invariant at the bootstrap log, raft's commit
invariant, the committed bootstrap log, this node's ghost state, raft's read credits), the term
budget (`budget_alloc_boot`), and the names chosen before the call (`newServerNames_alloc`: the id
generator's, the store's index names, its certificate map, the revisions' map), with the request
names `ρ` and the stand-in apply environment `E₀` carrying them; and the client's `etcdKV` at the
bootstrap log's model, for the client's invariant (`putGetInv_alloc_log`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.putget.Defs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.NewServerAlloc

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace putget

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section alloc
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The stand-in apply environment** (`NewServer.spec`'s `E₀`): the store's index names, its
certificate map and the revisions' map; `envAgree` reads nothing else. -/
def env₀ (idx : mvcc.IdxNames) (cok rev : GName) : apply.AEnv GF :=
  { s := null,
    γ := { idx := idx, bucket := 0, clog := 0, leases := 0, revs := 0, hook := 0, hookFn := 0,
           kb := none, cmeta := 0, fin := 0, sch := ⟨0, 0⟩, cok := cok, watchQ := false },
    P := iprop(True), f := #(), RD := iprop(True), γrev := rev, authOn := false,
    FS := iprop(True), ciC := fun _ => True }

/-- **What `NewServer` takes of the ghost state, for `Main`'s cluster** (see the file header). -/
theorem putget_alloc (id : w64) (bootLog : List EntryM) (Hbf : BootFacts id bootLog)
    (Hrb : receiptBound GF ≤ 2 ^ 64 - 2) :
    ⊢ |={⊤}=> ∃ (γ : RaftNames) (bud : BudgetNames) (ρ : ReqNames) (E₀ : apply.AEnv GF),
      ⌜γ.reCfg = GMap.listToSet [id] ∧ γ.reDyn = none ∧ γ.reCCOk = ccOk id ∧
        γ.reBoot = bootLog ∧ γ.reTracked = some (GMap.listToSet [id]) ∧ ρ.rd.raft = ⟨γ, [], W64 0⟩ ∧ srvCCPolicy ρ.rd.raft ∧
        ρ.rd.kv.c0 = W64 0 ∧ ρ.rd.kv.ch0 = apply.alarmChain false false false ∧
        ρ.rd.kv.log0 = [[], []] ∧ ρ.rd.kv.cok = E₀.γ.cok ∧ ρ.rd.kv.wl = putgetWorkload⌝ ∗
      ownRaftGhost γ id (bootPState bootLog) ∗ isCommitted γ bootLog ∗ raftCommitInv γ ∗
      inv budgetN (budgetInv bud) ∗ termLB bud (W64 1) ∗
      ghostMapAuth γ.reFresh 1 (∅ : GMap (List w8) Unit) ∗
      ghostMapAuth γ.reRdFresh 1 (∅ : GMap (List w8) Unit) ∗ rdCred γ (2 ^ 64 - 2) ∗
      idNamesFresh ρ.ids ∗ mvcc.idxFresh E₀.γ.idx ∗
      ghostMapAuth E₀.γ.cok 1 (∅ : GMap w64 mvcc.Log) ∗
      ghostMapAuth E₀.γrev 1 (∅ : GMap w64 Unit) ∗
      srvReadNamesFreshNK ρ.rd ∗ kvInv ρ.rd.raft ρ.rd.kv ∗
      etcdKV ρ.rd.kv (kvStateOf (kvModel ρ.rd.kv (bootEntries bootLog))) := by
  istart
  imod newServerNames_alloc (GF := GF) with ⟨%ids, %idx, %cok, %rev, Hids, Hidx, Hcok, Hrev⟩
  have Hin : id ∈ GMap.listToSet [id] := by
    rw [GMap.elem_of_list_to_set]; exact List.mem_singleton_self id
  have Hid0 : id ≠ W64 0 := by
    intro h; apply Hbf.idLow; rw [h]; decide
  imod (srvRaftBoot_alloc (GF := GF) ⊤ (GMap.listToSet [id]) (GMap.listToSet [id]) (ccOk id)
      [id] bootLog ids cok putgetWorkload
      (fun h => GMap.not_elem_of_empty id (h ▸ Hin))
      (by rw [GMap.elem_of_list_to_set]; simpa using Hid0.symm)
      rfl Hbf.boot (fun ty d h => h))
    with ⟨%γ, %Hγ, #Hcinv, #Hcomm, Hghosts, Hout, HrdC, -⟩
  imod budget_alloc_boot (GF := GF) Hrb ⊤ with ⟨%bud, #Hbinv, #Hlb⟩
  iunfold srvBootOut at Hout
  icases Hout with ⟨%γr, %Hr, #Hkv, Hetcd, Hnk, Hf, Hrf⟩
  obtain ⟨hraft, hc0, hch, hlog, hcok, hids, hwl⟩ := Hr
  obtain ⟨hcfg, hdyn, hcc, hboot, htr⟩ := Hγ
  subst hids hcok
  -- this node's ghost state, out of the map over the cluster `{id}`
  ihave Hghost : ownRaftGhost γ id (bootPState bootLog) $$ [Hghosts]
  · rw [show toMap (GMap.listToSet [id]) = GMap.insert id () (∅ : GMap w64 Unit) from rfl]
    ihave ⟨H1, -⟩ := (BigSepM.bigSepM_insert
      (Φ := fun k (_ : Unit) => ownRaftGhost (GF := GF) γ k (bootPState bootLog))
      (m := (∅ : GMap w64 Unit)) (i := id) (x := ()) (GMap.lookup_empty id)).1 $$ Hghosts
    iexact H1
  imodintro
  iexists γ, bud, ⟨γr.kv.cok, γr⟩, env₀ idx γr.kv.cok rev
  simp only [env₀]
  iframe Hghost Hcomm Hcinv Hbinv Hlb Hf Hrf HrdC Hids Hidx Hcok Hrev Hnk Hkv Hetcd
  ipureintro
  refine ⟨hcfg, hdyn, hcc, hboot, htr, hraft, ?_, hc0, hch, hlog, trivial, hwl⟩
  intro ty d h
  simp only [hraft] at h ⊢
  rw [hcc] at h
  rw [hcfg]
  exact h

end alloc

end putget
end EtcdGrove
end Perennial

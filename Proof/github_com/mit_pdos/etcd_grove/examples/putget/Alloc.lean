/-
**The ghost state `Main` allocates before `NewServer`** (item 9, stage 2, 2026-10-18; the
cluster's and the member's apart, stage M4 of D21, 2026-10-19). Lean-first (no Rocq counterpart).

`putget_alloc`: for the one-member cluster `{id}` and its bootstrap log (`BootFacts`), at the
leases-off workload `putgetWorkload` (D19q), everything `NewServer.spec` takes of the ghost state:
the member's names chosen before the call (`newServerNames_alloc`: the store's index names, its
certificate map, the revisions' map), with the stand-in apply environment `E₀` carrying them and
the claimers' facts at the member's prefix the server's (`srvFloorFact E₀`); the cluster's
resources (`srvClusterBoot_alloc`: raft's commit invariant, the committed bootstrap log, the
nodes' ghost states, the KV invariant at the bootstrap log, the claims with the reserved id `0`,
the proposals' mint, the read contexts, each member's share; its pure premise, the members' ids'
16 low bits distinct and not `0`, is `BootFacts`' `idLow` for one member), the term budget
(`budget_alloc_boot`), and the member's names and share (`srvMemberBoot_alloc`: the request names
`ρ`, its read names' fresh rows, its slots); and the client's `etcdKV` at the bootstrap log's
model, for the client's invariant (`putGetInv_alloc_log`).
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
    ⊢ |={⊤}=> ∃ (γ : RaftNames) (bud : BudgetNames) (ρ : ReqNames) (E₀ : apply.AEnv GF)
        (Φs : w64 → w64 → List w8 → GName → IProp GF),
      ⌜γ.reCfg = GMap.listToSet [id] ∧ γ.reDyn = none ∧ γ.reCCOk = ccOk id ∧
        γ.reBoot = bootLog ∧ γ.reNoSnap = true ∧ γ.reWit = W64 0 ∧ ρ.rd.raft = ⟨γ, [], W64 0⟩ ∧ srvCCPolicy ρ.rd.raft ∧
        ρ.rd.kv.c0 = W64 0 ∧ ρ.rd.kv.ch0 = apply.alarmChain false false false ∧
        ρ.rd.kv.log0 = [[], []] ∧ ρ.rd.kv.cok = E₀.γ.cok ∧ ρ.rd.kv.wl = putgetWorkload ∧
        ρ.ids.pfx = idPfxOf (W16 (uint.Z id)) ∧ Φs ρ.ids.pfx = srvFloorFact E₀⌝ ∗
      ownRaftGhost γ id (bootPState bootLog) ∗ isCommitted γ bootLog ∗ raftCommitInv γ ∗
      inv budgetN (budgetInv bud) ∗ termLB bud (W64 1) ∗
      idClusterInv ρ.ids.issued ρ.ids.cnt Φs ∗ idNoZero ρ.ids ∗
      srvPropMint ρ.rd.raft ρ.ids ∗ srvRdCtxInv ρ.rd.raft ρ.ids.issued ∗
      idShare ρ.ids ∗ rdCred γ (2 ^ 48) ∗
      mvcc.idxFresh E₀.γ.idx ∗
      ghostMapAuth E₀.γ.cok 1 (∅ : GMap w64 mvcc.Log) ∗
      ghostMapAuth E₀.γrev 1 (∅ : GMap w64 Unit) ∗
      srvReadNamesFreshNK ρ.rd ∗ kvInv ρ.rd.raft ρ.rd.kv ∗
      etcdKV ρ.rd.kv (kvStateOf (kvModel ρ.rd.kv (bootEntries bootLog))) := by
  istart
  imod newServerNames_alloc (GF := GF) with ⟨%idx, %cok, %rev, Hidx, Hcok, Hrev⟩
  have Hin : id ∈ GMap.listToSet [id] := by
    rw [GMap.elem_of_list_to_set]; exact List.mem_singleton_self id
  have Hid0 : id ≠ W64 0 := by
    intro h; apply Hbf.idLow; rw [h]; decide
  let Φs : w64 → w64 → List w8 → GName → IProp GF := fun _ => srvFloorFact (env₀ idx cok rev)
  imod (srvClusterBoot_alloc (GF := GF) (GMap.listToSet [id]) (GMap.listToSet [id]) (ccOk id)
      [id] bootLog putgetWorkload Φs
      (fun h => GMap.not_elem_of_empty id (h ▸ Hin))
      (by rw [GMap.elem_of_list_to_set]; simpa using Hid0.symm)
      rfl Hbf.boot (fun ty d h => h) (by simp) (by simpa using Hbf.idLow))
    with ⟨%γ, %issued, %cnt, %γk, %Hγ, #Hcinv, #Hcomm, -, Hghosts, #Hkv, Hetcd, #Hcl, #H0,
      #Hpm, #Hrc, Hms⟩
  obtain ⟨hcfg, hdyn, hcc, hboot, htr, hnw, hc0, hch, hlog, hiss, hwl⟩ := Hγ
  icases BigSepL.bigSepL_cons.1 $$ Hms with ⟨⟨Hp, HrdC⟩, -⟩
  imod budget_alloc_boot (GF := GF) Hrb ⊤ with ⟨%bud, #Hbinv, #Hlb⟩
  imod (srvMemberBoot_alloc (GF := GF) γ cnt γk id cok) $$ Hkv Hp
    with ⟨%ρ, %Hρ, #Hkvρ, Hsh, Hnk⟩
  obtain ⟨hraft, hst, hc0', hch', hlog', hwl', hcok, hiss', hcnt, hpfx⟩ := Hρ
  -- this node's ghost state, out of the map over the cluster `{id}`
  ihave Hghost : ownRaftGhost γ id (bootPState bootLog) $$ [Hghosts]
  · rw [show toMap (GMap.listToSet [id]) = GMap.insert id () (∅ : GMap w64 Unit) from rfl]
    ihave ⟨H1, -⟩ := (BigSepM.bigSepM_insert
      (Φ := fun k (_ : Unit) => ownRaftGhost (GF := GF) γ k (bootPState bootLog))
      (m := (∅ : GMap w64 Unit)) (i := id) (x := ()) (GMap.lookup_empty id)).1 $$ Hghosts
    iexact H1
  imodintro
  iexists γ, bud, ρ, env₀ idx cok rev, Φs
  simp only [env₀]
  rw [hiss', hcnt, hraft, hiss]
  rw [← srvPropMint_congr _ γk.ids ρ.ids (by rw [hiss', hiss])]
  rw [etcdKV_congr ρ.rd.kv γk hst,
    show kvModel ρ.rd.kv (bootEntries bootLog) = kvModel γk (bootEntries bootLog) by
      unfold kvModel; rw [hc0', hch', hlog']]
  iframe Hghost Hcomm Hcinv Hbinv Hlb Hcl Hpm Hrc Hsh HrdC Hidx Hcok Hrev Hnk Hkvρ Hetcd
  isplitr
  · ipureintro
    refine ⟨hcfg, hdyn, hcc, hboot, htr, hnw, rfl, ?_, by rw [hc0', hc0], by rw [hch', hch],
      by rw [hlog', hlog], hcok, by rw [hwl', hwl], hpfx, rfl⟩
    intro ty d h
    simp only at h ⊢
    rw [hcc] at h
    rw [hcfg]
    exact h
  iunfold idNoZero
  rw [hiss', hiss]
  iexact H0

end alloc

end putget
end EtcdGrove
end Perennial

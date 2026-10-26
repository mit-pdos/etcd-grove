/-
**The ghost state a one-member example's `Main` allocates before its member** (2026-10-22, D33).
Lean-first (no Rocq counterpart). What putget's `putget_alloc` and watchkv's `watchkv_alloc` were,
once, at a peer-URL directory `dir`, with the raft network's allocation (each `Main`'s
`netNames_alloc`) inside.

`alloc1`: for the one-member cluster `{id}` and its bootstrap log (`BootLogOk` under `ccOk [id]`,
the id's 16 low bits not `0`), everything the member's `NewServer` takes of the ghost state
(`memberBoot`): the member's names chosen before the call (`newServerNames_alloc`: the store's
index names, its certificate map, the revisions' map), with the stand-in apply environment `env₀`
carrying them and the claimers' facts at the member's prefix the server's (`srvFloorFact`); the
cluster's resources (`srvClusterBoot_alloc`), the term budget (`budget_alloc_boot`), the member's
names and share (`srvMemberBoot_alloc`); the raft network with the member's slot and the directory
`dir` (`netNames_alloc`); and the client's `etcdKV` at the bootstrap log's model.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.common.Defs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.NewServerAlloc

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace common

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section alloc
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **What a one-member `Main` takes of the ghost state, for its member** (see the file header). -/
theorem alloc1 (id : w64) (bootLog : List EntryM)
    (Hlow : uint.Z id % 2 ^ 16 ≠ 0) (Hboot : BootLogOk (ccOk [id]) [id] bootLog)
    (dir : w64 → List GoString) (Hone : ∀ f, dir f ≠ [] → f = id)
    (Hrb : receiptBound GF ≤ 2 ^ 64 - 2) :
    ⊢ |={⊤}=> ∃ (γ : RaftNames) (bud : BudgetNames) (ρ : ReqNames) (E₀ : apply.AEnv GF)
        (Φs : w64 → w64 → List w8 → GName → IProp GF) (γn : NetNames GF),
      ⌜γ.reCfg = GMap.listToSet [id] ∧ γ.reDyn = none ∧ γ.reCCOk = ccOk [id] ∧
        γ.reBoot = bootLog ∧ γ.reNoSnap = true ∧ γ.reNoXfer = true ∧
        γn.N = srvNet γ bud ∧ γn.dir = dir ∧ ρ.rd.kv.log0 = [[], []]⌝ ∗
      memberBoot γ bud bootLog ρ E₀ Φs id ∗ netHttpOk γn id ∗
      etcdKV ρ.rd.kv (kvStateOf (kvModel ρ.rd.kv (bootEntries bootLog))) := by
  istart
  imod newServerNames_alloc (GF := GF) with ⟨%idx, %cok, %rev, Hidx, Hcok, Hrev⟩
  have Hin : id ∈ GMap.listToSet [id] := by
    rw [GMap.elem_of_list_to_set]; exact List.mem_singleton_self id
  have Hid0 : id ≠ W64 0 := by
    intro h; apply Hlow; rw [h]; decide
  let Φs : w64 → w64 → List w8 → GName → IProp GF := fun _ => srvFloorFact (env₀ idx cok rev)
  imod (srvClusterBoot_alloc (GF := GF) (GMap.listToSet [id]) (GMap.listToSet [id]) (ccOk [id])
      [id] bootLog Φs
      (fun h => GMap.not_elem_of_empty id (h ▸ Hin))
      (by rw [GMap.elem_of_list_to_set]; simpa using Hid0.symm)
      rfl Hboot (fun ty d h => h) (by simp) (by simpa using Hlow))
    with ⟨%γ, %issued, %cnt, %γk, %Hγ, #Hcinv, #Hcomm, -, Hghosts, #Hkv, Hetcd, #Hcl, #H0,
      #Hpm, #Hrc, Hms, Hwns⟩
  obtain ⟨hcfg, hdyn, hcc, hboot, htr, htx, hc0, hch, hlog, hiss⟩ := Hγ
  icases BigSepL.bigSepL_cons.1 $$ Hms with ⟨⟨Hp, HrdC, Hsd⟩, -⟩
  icases BigSepL.bigSepL_cons.1 $$ Hwns with ⟨Hwn, -⟩
  imod budget_alloc_boot (GF := GF) Hrb ⊤ with ⟨%bud, #Hbinv, #Hlb⟩
  imod (srvMemberBoot_alloc (GF := GF) γ cnt γk id cok) $$ Hkv Hp Hwn
    with ⟨%ρ, %Hρ, #Hkvρ, Hsh, Hnk, Hwt⟩
  obtain ⟨hraft, hst, hc0', hch', hlog', hcok, hiss', hcnt, hpfx⟩ := Hρ
  -- this node's ghost state, out of the map over the cluster `{id}`
  ihave Hghost : ownRaftGhost γ id (bootPState bootLog) $$ [Hghosts]
  · rw [show toMap (GMap.listToSet [id]) = GMap.insert id () (∅ : GMap w64 Unit) from rfl]
    ihave ⟨H1, -⟩ := (BigSepM.bigSepM_insert
      (Φ := fun k (_ : Unit) => ownRaftGhost (GF := GF) γ k (bootPState bootLog))
      (m := (∅ : GMap w64 Unit)) (i := id) (x := ()) (GMap.lookup_empty id)).1 $$ Hghosts
    iexact H1
  -- the raft network; (2026-10-24, rafthttp stage 6d) one member: no other member's hosts to
  -- register (until then the member's slot)
  imod (netNames_alloc (srvNet γ bud) dir (∅ : GMap w64 Unit) ⊤) with ⟨%γn, %Hγn, -, #HregN⟩
  ihave #Hnet := netHttpOk_single γn id
    (fun f hf => Hone f (by rw [Hγn.2] at hf; exact hf)) $$ HregN
  imodintro
  iexists γ, bud, ρ, env₀ idx cok rev, Φs, γn
  iframe Hnet
  isplitr
  · ipureintro
    exact ⟨hcfg, hdyn, hcc, hboot, htr, htx, Hγn.1, Hγn.2, by rw [hlog', hlog]⟩
  iunfold memberBoot
  simp only [env₀]
  rw [hiss', hcnt, hraft, hiss]
  rw [← srvPropMint_congr _ γk.ids ρ.ids (by rw [hiss', hiss])]
  rw [etcdKV_congr ρ.rd.kv γk hst,
    show kvModel ρ.rd.kv (bootEntries bootLog) = kvModel γk (bootEntries bootLog) by
      unfold kvModel; rw [hc0', hch', hlog']]
  iframe Hghost Hcomm Hcinv Hbinv Hlb Hcl Hpm Hrc Hsh HrdC Hidx Hcok Hrev Hnk Hkvρ Hwt Hetcd Hsd
  isplitr
  · ipureintro
    refine ⟨rfl, ?_, by rw [hc0', hc0], by rw [hch', hch], by rw [hlog', hlog], hcok,
      hpfx, rfl⟩
    intro ty d h
    simp only at h ⊢
    rw [hcc] at h
    rw [hcfg]
    exact h
  iunfold idNoZero
  rw [hiss', hiss]
  iexact H0

end alloc

end common
end EtcdGrove
end Perennial

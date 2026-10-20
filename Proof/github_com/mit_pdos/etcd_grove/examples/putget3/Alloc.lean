/-
**The ghost state `Main` allocates before the members** (D21 stage M5, 2026-10-19). Lean-first (no
Rocq counterpart). putget's `putget_alloc` (`putget/Alloc.lean`) for three members.

`putget3_alloc`: for the three-member cluster `[id₁, id₂, id₃]` and its bootstrap log
(`BootFacts`), at the leases-off workload `putgetWorkload`: each member's names chosen before its
`NewServer` (`newServerNames_alloc`), the claimers' facts at each member's prefix that member's
(`srvFloorFact` of its stand-in environment; the prefixes are distinct, D21e (A)); the cluster's
resources once (`srvClusterBoot_alloc`), the term budget once (`budget_alloc_boot`), each member's
names and share (`srvMemberBoot_alloc`); the raft network with a slot per member and the directory
`dir3` (`netNames_alloc`); and the client's `etcdKV` at the bootstrap log's model, at the first
member's names. What one member's `NewServer` takes is `memberBoot`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.putget3.Defs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.NewServerAlloc

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace putget3

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section alloc
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The stand-in apply environment** (`NewServer.spec`'s `E₀`; putget's `env₀`). -/
def env₀ (idx : mvcc.IdxNames) (cok rev : GName) : apply.AEnv GF :=
  { s := null,
    γ := { idx := idx, bucket := 0, clog := 0, leases := 0, revs := 0, hook := 0, hookFn := 0,
           kb := none, cmeta := 0, fin := 0, sch := ⟨0, 0⟩, cok := cok, watchQ := false },
    P := iprop(True), f := #(), RD := iprop(True), γrev := rev, authOn := false,
    FS := iprop(True), ciC := fun _ => True }

/-- **What member `id`'s `NewServer` takes of the ghost state** (its pure facts, the cluster's
resources at its names, its share): `NewServer.spec`'s precondition but the network's and the
premises'. -/
def memberBoot (γ : RaftNames) (bud : BudgetNames) (bootLog : List EntryM) (ρ : ReqNames)
    (E₀ : apply.AEnv GF) (Φs : w64 → w64 → List w8 → GName → IProp GF) (id : w64) : IProp GF :=
  iprop(⌜ρ.rd.raft = ⟨γ, [], W64 0⟩ ∧ srvCCPolicy ρ.rd.raft ∧
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
    srvReadNamesFreshNK ρ.rd ∗ kvInv ρ.rd.raft ρ.rd.kv)

/-- The three prefixes are distinct. -/
theorem pfx_ne (id₁ id₂ id₃ : w64) (bootLog : List EntryM) (Hbf : BootFacts id₁ id₂ id₃ bootLog) :
    idPfxOf (W16 (uint.Z id₁)) ≠ idPfxOf (W16 (uint.Z id₂)) ∧
    idPfxOf (W16 (uint.Z id₁)) ≠ idPfxOf (W16 (uint.Z id₃)) ∧
    idPfxOf (W16 (uint.Z id₂)) ≠ idPfxOf (W16 (uint.Z id₃)) := by
  have h := (idPfxsOf_ok [id₁, id₂, id₃] Hbf.idLow Hbf.idLow0).1
  simp only [idPfxsOf, List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, or_false] at h
  refine ⟨fun e => h.1 (Or.inl e), fun e => h.1 (Or.inr e), fun e => h.2.1 e⟩

/-- The three ids are distinct. -/
theorem id_ne (id₁ id₂ id₃ : w64) (bootLog : List EntryM) (Hbf : BootFacts id₁ id₂ id₃ bootLog) :
    id₁ ≠ id₂ ∧ id₁ ≠ id₃ ∧ id₂ ≠ id₃ := by
  obtain ⟨h1, h2, h3⟩ := pfx_ne id₁ id₂ id₃ bootLog Hbf
  exact ⟨fun e => h1 (by rw [e]), fun e => h2 (by rw [e]), fun e => h3 (by rw [e])⟩

/-- No id is `0`. -/
theorem id_nz (id₁ id₂ id₃ : w64) (bootLog : List EntryM) (Hbf : BootFacts id₁ id₂ id₃ bootLog) :
    ∀ id ∈ [id₁, id₂, id₃], id ≠ W64 0 := by
  intro id hid e
  apply Hbf.idLow0 id hid
  rw [e]; decide

/-- **`memberBoot` from the allocations**, for one member (the common step of `putget3_alloc`). -/
theorem memberBoot_of (γ : RaftNames) (bud : BudgetNames) (bootLog : List EntryM)
    (issued cnt : GName) (γk : KVNames) (Φs : w64 → w64 → List w8 → GName → IProp GF)
    (id : w64) (idx : mvcc.IdxNames) (cok rev : GName)
    (Hiss : γk.ids.issued = issued) (Hc0 : γk.c0 = W64 0)
    (Hch : γk.ch0 = apply.alarmChain false false false) (Hlog : γk.log0 = [[], []])
    (Hwl : γk.wl = putgetWorkload)
    (Hpol : srvCCPolicy ⟨γ, [], W64 0⟩)
    (HΦ : Φs (idPfxOf (W16 (uint.Z id))) = srvFloorFact (env₀ (GF := GF) idx cok rev)) :
    ⊢ ownRaftGhost γ id (bootPState bootLog) -∗ isCommitted γ bootLog -∗ raftCommitInv γ -∗
      inv budgetN (budgetInv bud) -∗ termLB bud (W64 1) -∗
      idClusterInv issued cnt Φs -∗ (W64 0) ↪[issued]□ (none : Option (List w8 × GName)) -∗
      srvPropMint ⟨γ, [], W64 0⟩ γk.ids -∗ srvRdCtxInv ⟨γ, [], W64 0⟩ issued -∗
      kvInv ⟨γ, [], W64 0⟩ γk -∗
      (idPfxOf (W16 (uint.Z id)) ↪[cnt] ([] : List w64) ∗ rdCred γ (2 ^ 48)) -∗
      mvcc.idxFresh idx -∗ ghostMapAuth cok 1 (∅ : GMap w64 mvcc.Log) -∗
      ghostMapAuth rev 1 (∅ : GMap w64 Unit) ==∗
      ∃ ρ : ReqNames, ⌜ρ.rd.kv.st = γk.st ∧ ρ.rd.kv.c0 = γk.c0 ∧ ρ.rd.kv.ch0 = γk.ch0 ∧
        ρ.rd.kv.log0 = γk.log0⌝ ∗
        memberBoot γ bud bootLog ρ (env₀ idx cok rev) Φs id := by
  iintro Hghost #Hcomm #Hcinv #Hbinv #Hlb #Hcl #H0 #Hpm #Hrc #Hkv ⟨Hp, HrdC⟩ Hidx Hcok Hrev
  imod (srvMemberBoot_alloc (GF := GF) γ cnt γk id cok) $$ Hkv Hp
    with ⟨%ρ, %Hρ, #Hkvρ, Hsh, Hnk⟩
  obtain ⟨hraft, hst, hc0', hch', hlog', hwl', hcok, hiss', hcnt, hpfx⟩ := Hρ
  imodintro
  iexists ρ
  isplitr
  · ipureintro; exact ⟨hst, hc0', hch', hlog'⟩
  iunfold memberBoot
  simp only [env₀]
  rw [hiss', hcnt, hraft, Hiss]
  rw [← srvPropMint_congr _ γk.ids ρ.ids (by rw [hiss', Hiss])]
  iframe Hghost Hcomm Hcinv Hbinv Hlb Hcl Hpm Hrc Hsh HrdC Hidx Hcok Hrev Hnk Hkvρ
  isplitr
  · ipureintro
    refine ⟨rfl, Hpol, by rw [hc0', Hc0], by rw [hch', Hch], by rw [hlog', Hlog], hcok,
      by rw [hwl', Hwl], hpfx, ?_⟩
    rw [hpfx]; exact HΦ
  iunfold idNoZero
  rw [hiss', Hiss]
  iexact H0

/-- **What `Main` takes of the ghost state, for its cluster** (see the file header). -/
theorem putget3_alloc (id₁ id₂ id₃ : w64) (bootLog : List EntryM)
    (Hbf : BootFacts id₁ id₂ id₃ bootLog) (Hrb : receiptBound GF ≤ 2 ^ 64 - 2) :
    ⊢ |={⊤}=> ∃ (γ : RaftNames) (bud : BudgetNames) (ρ₁ ρ₂ ρ₃ : ReqNames)
        (E₁ E₂ E₃ : apply.AEnv GF) (Φs : w64 → w64 → List w8 → GName → IProp GF)
        (γn : NetNames GF),
      ⌜γ.reCfg = GMap.listToSet [id₁, id₂, id₃] ∧ γ.reDyn = none ∧
        γ.reCCOk = ccOk [id₁, id₂, id₃] ∧ γ.reBoot = bootLog ∧ γ.reNoSnap = true ∧
        γ.reWit = W64 0 ∧ γn.N = srvNet γ bud ∧ γn.dir = dir3 id₁ id₂ id₃⌝ ∗
      memberBoot γ bud bootLog ρ₁ E₁ Φs id₁ ∗ netSlot γn id₁ ∗
      memberBoot γ bud bootLog ρ₂ E₂ Φs id₂ ∗ netSlot γn id₂ ∗
      memberBoot γ bud bootLog ρ₃ E₃ Φs id₃ ∗ netSlot γn id₃ ∗
      etcdKV ρ₁.rd.kv (kvStateOf (kvModel ρ₁.rd.kv (bootEntries bootLog))) := by
  obtain ⟨hn12, hn13, hn23⟩ := id_ne id₁ id₂ id₃ bootLog Hbf
  obtain ⟨hp12, hp13, hp23⟩ := pfx_ne id₁ id₂ id₃ bootLog Hbf
  have Hnz := id_nz id₁ id₂ id₃ bootLog Hbf
  istart
  imod newServerNames_alloc (GF := GF) with ⟨%idx₁, %cok₁, %rev₁, Hidx₁, Hcok₁, Hrev₁⟩
  imod newServerNames_alloc (GF := GF) with ⟨%idx₂, %cok₂, %rev₂, Hidx₂, Hcok₂, Hrev₂⟩
  imod newServerNames_alloc (GF := GF) with ⟨%idx₃, %cok₃, %rev₃, Hidx₃, Hcok₃, Hrev₃⟩
  let Φs : w64 → w64 → List w8 → GName → IProp GF := fun p =>
    if p = idPfxOf (W16 (uint.Z id₁)) then srvFloorFact (env₀ idx₁ cok₁ rev₁)
    else if p = idPfxOf (W16 (uint.Z id₂)) then srvFloorFact (env₀ idx₂ cok₂ rev₂)
    else srvFloorFact (env₀ idx₃ cok₃ rev₃)
  have HΦ₁ : Φs (idPfxOf (W16 (uint.Z id₁))) = srvFloorFact (env₀ (GF := GF) idx₁ cok₁ rev₁) := by
    simp only [Φs, if_true]
  have HΦ₂ : Φs (idPfxOf (W16 (uint.Z id₂))) = srvFloorFact (env₀ (GF := GF) idx₂ cok₂ rev₂) := by
    simp only [Φs, Ne.symm hp12, if_false, if_true]
  have HΦ₃ : Φs (idPfxOf (W16 (uint.Z id₃))) = srvFloorFact (env₀ (GF := GF) idx₃ cok₃ rev₃) := by
    simp only [Φs, Ne.symm hp13, Ne.symm hp23, if_false]
  have Hpol : ∀ ty d, ccOk [id₁, id₂, id₃] ty d → ty = W32 1 ∧ isConfChangeEncoding d ∧
      ccIdOf d = W64 0 ∧ ccBootOk (GMap.listToSet [id₁, id₂, id₃]) d := fun ty d h => h
  have Hin₁ : id₁ ∈ GMap.listToSet [id₁, id₂, id₃] := by
    rw [GMap.elem_of_list_to_set]; simp
  imod (srvClusterBoot_alloc (GF := GF) (GMap.listToSet [id₁, id₂, id₃])
      (GMap.listToSet [id₁, id₂, id₃]) (ccOk [id₁, id₂, id₃]) [id₁, id₂, id₃] bootLog
      putgetWorkload Φs
      (fun h => GMap.not_elem_of_empty id₁ (h ▸ Hin₁))
      (by
        rw [GMap.elem_of_list_to_set]
        intro h
        exact Hnz _ h rfl)
      rfl Hbf.boot Hpol Hbf.idLow Hbf.idLow0)
    with ⟨%γ, %issued, %cnt, %γk, %Hγ, #Hcinv, #Hcomm, -, Hghosts, #Hkv, Hetcd, #Hcl, #H0,
      #Hpm, #Hrc, Hms⟩
  obtain ⟨hcfg, hdyn, hcc, hboot, htr, hnw, hc0, hch, hlog, hiss, hwl⟩ := Hγ
  have Hpol' : srvCCPolicy ⟨γ, [], W64 0⟩ := by
    intro ty d h
    simp only at h ⊢
    rw [hcc] at h
    rw [hcfg]
    exact h
  icases Hms with ⟨Hm₁, Hm₂, Hm₃, -⟩
  imod budget_alloc_boot (GF := GF) Hrb ⊤ with ⟨%bud, #Hbinv, #Hlb⟩
  -- the nodes' ghost states, out of the map over the cluster
  rw [show toMap (GMap.listToSet [id₁, id₂, id₃]) =
      GMap.insert id₁ () (GMap.insert id₂ () (GMap.insert id₃ () (∅ : GMap w64 Unit))) from rfl]
  ihave ⟨Hg₁, Hgs⟩ := (BigSepM.bigSepM_insert
    (Φ := fun k (_ : Unit) => ownRaftGhost (GF := GF) γ k (bootPState bootLog))
    (by rw [gmap_get?_eq, GMap.lookup_insert_ne _ _ (Ne.symm hn12),
      GMap.lookup_insert_ne _ _ (Ne.symm hn13)]; exact GMap.lookup_empty _)).1 $$ Hghosts
  ihave ⟨Hg₂, Hgs⟩ := (BigSepM.bigSepM_insert
    (Φ := fun k (_ : Unit) => ownRaftGhost (GF := GF) γ k (bootPState bootLog))
    (by rw [gmap_get?_eq, GMap.lookup_insert_ne _ _ (Ne.symm hn23)]; exact GMap.lookup_empty _)).1 $$ Hgs
  ihave ⟨Hg₃, -⟩ := (BigSepM.bigSepM_insert
    (Φ := fun k (_ : Unit) => ownRaftGhost (GF := GF) γ k (bootPState bootLog))
    (GMap.lookup_empty _)).1 $$ Hgs
  imod (memberBoot_of γ bud bootLog issued cnt γk Φs id₁ idx₁ cok₁ rev₁ hiss hc0 hch hlog hwl
      Hpol' HΦ₁) $$ Hg₁ Hcomm Hcinv Hbinv Hlb Hcl H0 Hpm Hrc Hkv Hm₁ Hidx₁ Hcok₁ Hrev₁
    with ⟨%ρ₁, %Hρ₁, Hb₁⟩
  imod (memberBoot_of γ bud bootLog issued cnt γk Φs id₂ idx₂ cok₂ rev₂ hiss hc0 hch hlog hwl
      Hpol' HΦ₂) $$ Hg₂ Hcomm Hcinv Hbinv Hlb Hcl H0 Hpm Hrc Hkv Hm₂ Hidx₂ Hcok₂ Hrev₂
    with ⟨%ρ₂, -, Hb₂⟩
  imod (memberBoot_of γ bud bootLog issued cnt γk Φs id₃ idx₃ cok₃ rev₃ hiss hc0 hch hlog hwl
      Hpol' HΦ₃) $$ Hg₃ Hcomm Hcinv Hbinv Hlb Hcl H0 Hpm Hrc Hkv Hm₃ Hidx₃ Hcok₃ Hrev₃
    with ⟨%ρ₃, -, Hb₃⟩
  -- the raft network: a slot per member
  imod (netNames_alloc (srvNet γ bud) (dir3 id₁ id₂ id₃)
      (GMap.insert id₁ () (GMap.insert id₂ () (GMap.insert id₃ () (∅ : GMap w64 Unit)))))
    with ⟨%γn, %Hγn, Hslots⟩
  ihave ⟨Hs₁, Hslots⟩ := (BigSepM.bigSepM_insert
    (Φ := fun k (_ : Unit) => netSlot (GF := GF) γn k)
    (by rw [gmap_get?_eq, GMap.lookup_insert_ne _ _ (Ne.symm hn12),
      GMap.lookup_insert_ne _ _ (Ne.symm hn13)]; exact GMap.lookup_empty _)).1 $$ Hslots
  ihave ⟨Hs₂, Hslots⟩ := (BigSepM.bigSepM_insert
    (Φ := fun k (_ : Unit) => netSlot (GF := GF) γn k)
    (by rw [gmap_get?_eq, GMap.lookup_insert_ne _ _ (Ne.symm hn23)]; exact GMap.lookup_empty _)).1 $$ Hslots
  ihave ⟨Hs₃, -⟩ := (BigSepM.bigSepM_insert
    (Φ := fun k (_ : Unit) => netSlot (GF := GF) γn k)
    (GMap.lookup_empty _)).1 $$ Hslots
  obtain ⟨hst₁, hc0₁, hch₁, hlog₁⟩ := Hρ₁
  imodintro
  iexists γ, bud, ρ₁, ρ₂, ρ₃, env₀ idx₁ cok₁ rev₁, env₀ idx₂ cok₂ rev₂, env₀ idx₃ cok₃ rev₃, Φs, γn
  iframe Hb₁ Hb₂ Hb₃ Hs₁ Hs₂ Hs₃
  isplitr
  · ipureintro; exact ⟨hcfg, hdyn, hcc, hboot, htr, hnw, Hγn.1, Hγn.2⟩
  rw [etcdKV_congr ρ₁.rd.kv γk hst₁,
    show kvModel ρ₁.rd.kv (bootEntries bootLog) = kvModel γk (bootEntries bootLog) by
      unfold kvModel; rw [hc0₁, hch₁, hlog₁]]
  iexact Hetcd

end alloc

end putget3
end EtcdGrove
end Perennial

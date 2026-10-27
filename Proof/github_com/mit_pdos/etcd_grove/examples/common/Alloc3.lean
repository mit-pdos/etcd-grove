/-
**The ghost state a three-member example's `Main` allocates before its members** (2026-10-22, D33).
Lean-first (no Rocq counterpart). What putget3's `putget3_alloc`, linkv3's and linkv3p's
`cluster3_alloc` were, once, at a peer-URL directory `dir`.

`alloc3`: for the three-member cluster `[id₁, id₂, id₃]` (in `bootstrap`'s order) and its bootstrap
log (`BootLogOk` under `ccOk`; the ids' 16 low bits distinct and not `0`, D21e (A)): each member's
names chosen before its `NewServer` (`newServerNames_alloc`), the claimers' facts at each member's
prefix that member's (`srvFloorFact` of its stand-in environment; the prefixes are distinct); the
cluster's resources once (`srvClusterBoot_alloc`), the term budget once (`budget_alloc_boot`), each
member's names and share (`srvMemberBoot_alloc`, `memberBoot_of`); the raft network with the
directory `dir` (`netNames_alloc`), its HTTP side ready for each member (2026-10-24, rafthttp stage
6d; until then a slot per member: `netHttp_reserve3`, each peer address reserved for the raft
protocol from the program start's right); and the client's `etcdKV` at the bootstrap log's
model, at the first member's names, the others' KV names agreeing with them in state variable,
and their KV models one (the cluster's `etcdKV`, D21 M4: an invariant over it allocated
at one member's names is every member's).
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- The three prefixes are distinct. -/
theorem pfx_ne (id₁ id₂ id₃ : w64) (Hlow : ([id₁, id₂, id₃].map (fun id => uint.Z id % 2 ^ 16)).Nodup)
    (Hlow0 : ∀ id ∈ [id₁, id₂, id₃], uint.Z id % 2 ^ 16 ≠ 0) :
    idPfxOf (W16 (uint.Z id₁)) ≠ idPfxOf (W16 (uint.Z id₂)) ∧
    idPfxOf (W16 (uint.Z id₁)) ≠ idPfxOf (W16 (uint.Z id₃)) ∧
    idPfxOf (W16 (uint.Z id₂)) ≠ idPfxOf (W16 (uint.Z id₃)) := by
  have h := (idPfxsOf_ok [id₁, id₂, id₃] Hlow Hlow0).1
  simp only [idPfxsOf, List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, or_false] at h
  refine ⟨fun e => h.1 (Or.inl e), fun e => h.1 (Or.inr e), fun e => h.2.1 e⟩

/-- The three ids are distinct. -/
theorem id_ne (id₁ id₂ id₃ : w64) (Hlow : ([id₁, id₂, id₃].map (fun id => uint.Z id % 2 ^ 16)).Nodup)
    (Hlow0 : ∀ id ∈ [id₁, id₂, id₃], uint.Z id % 2 ^ 16 ≠ 0) :
    id₁ ≠ id₂ ∧ id₁ ≠ id₃ ∧ id₂ ≠ id₃ := by
  obtain ⟨h1, h2, h3⟩ := pfx_ne id₁ id₂ id₃ Hlow Hlow0
  exact ⟨fun e => h1 (by rw [e]), fun e => h2 (by rw [e]), fun e => h3 (by rw [e])⟩

/-- No id is `0`. -/
theorem id_nz (id₁ id₂ id₃ : w64) (Hlow : ([id₁, id₂, id₃].map (fun id => uint.Z id % 2 ^ 16)).Nodup)
    (Hlow0 : ∀ id ∈ [id₁, id₂, id₃], uint.Z id % 2 ^ 16 ≠ 0) :
    ∀ id ∈ [id₁, id₂, id₃], id ≠ W64 0 := by
  intro id hid e
  apply Hlow0 id hid
  rw [e]; decide

/-- **`memberBoot` from the allocations**, for one member (the common step of `alloc3`). -/
theorem memberBoot_of (γ : RaftNames) (bud : BudgetNames) (bootLog : List EntryM)
    (issued cnt : GName) (γk : KVNames) (Φs : w64 → w64 → List w8 → GName → IProp GF)
    (id : w64) (idx : mvcc.IdxNames) (cok rev : GName)
    (Hiss : γk.ids.issued = issued) (Hc0 : γk.c0 = W64 0)
    (Hch : γk.ch0 = apply.alarmChain false false false) (Hlog : γk.log0 = [[], []])
    (Hpol : srvCCPolicy ⟨γ, [], W64 0⟩)
    (HΦ : Φs (idPfxOf (W16 (uint.Z id))) = srvFloorFact (env₀ (GF := GF) idx cok rev)) :
    ⊢ ownRaftGhost γ id (bootPState bootLog) -∗ isCommitted γ bootLog -∗ raftCommitInv γ -∗
      inv budgetN (budgetInv bud) -∗ termLB bud (W64 1) -∗
      idClusterInv issued cnt Φs -∗ (W64 0) ↪[issued]□ (none : Option (List w8 × GName)) -∗
      srvPropMint ⟨γ, [], W64 0⟩ γk.ids -∗ srvRdCtxInv ⟨γ, [], W64 0⟩ issued -∗
      kvInv ⟨γ, [], W64 0⟩ γk -∗
      (idPfxOf (W16 (uint.Z id)) ↪[cnt] ([] : List w64) ∗ rdCred γ (2 ^ 48) ∗
        ∃ γd : GName, ⌜γ.reSnapLoc id = some γd⌝ ∗ ghostMapAuth γd 1 (∅ : GMap w64 Unit)) -∗
      idWaitTokAt γk.ids.wn (idPfxOf (W16 (uint.Z id))) -∗
      mvcc.idxFresh idx -∗ ghostMapAuth cok 1 (∅ : GMap w64 mvcc.Log) -∗
      ghostMapAuth rev 1 (∅ : GMap w64 Unit) ==∗
      ∃ ρ : ReqNames, ⌜ρ.rd.kv.st = γk.st ∧ ρ.rd.kv.c0 = γk.c0 ∧ ρ.rd.kv.ch0 = γk.ch0 ∧
        ρ.rd.kv.log0 = γk.log0⌝ ∗
        memberBoot γ bud bootLog ρ (env₀ idx cok rev) Φs id := by
  iintro Hghost #Hcomm #Hcinv #Hbinv #Hlb #Hcl #H0 #Hpm #Hrc #Hkv ⟨Hp, HrdC, Hsd⟩ Hwn Hidx Hcok Hrev
  imod (srvMemberBoot_alloc (GF := GF) γ cnt γk id cok) $$ Hkv Hp Hwn
    with ⟨%ρ, %Hρ, #Hkvρ, Hsh, Hnk, Hwt⟩
  obtain ⟨hraft, hst, hc0', hch', hlog', hcok, hiss', hcnt, hpfx⟩ := Hρ
  imodintro
  iexists ρ
  isplitr
  · ipureintro; exact ⟨hst, hc0', hch', hlog'⟩
  iunfold memberBoot
  simp only [env₀]
  rw [hiss', hcnt, hraft, Hiss]
  rw [← srvPropMint_congr _ γk.ids ρ.ids (by rw [hiss', Hiss])]
  iframe Hghost Hcomm Hcinv Hbinv Hlb Hcl Hpm Hrc Hsh HrdC Hidx Hcok Hrev Hnk Hkvρ Hwt Hsd
  isplitr
  · ipureintro
    refine ⟨rfl, Hpol, by rw [hc0', Hc0], by rw [hch', Hch], by rw [hlog', Hlog], hcok,
      hpfx, ?_⟩
    rw [hpfx]; exact HΦ
  iunfold idNoZero
  rw [hiss', Hiss]
  iexact H0

/-- **What `Main` takes of the ghost state, for its cluster** (see the file header). -/
theorem alloc3 (id₁ id₂ id₃ : w64) (bootLog : List EntryM)
    (Hlow : ([id₁, id₂, id₃].map (fun id => uint.Z id % 2 ^ 16)).Nodup)
    (Hlow0 : ∀ id ∈ [id₁, id₂, id₃], uint.Z id % 2 ^ 16 ≠ 0)
    (Hboot : BootLogOk (ccOk [id₁, id₂, id₃]) [id₁, id₂, id₃] bootLog) (dir : w64 → List GoString)
    -- (2026-10-24, rafthttp stage 6d) the directory's hosts the three peer addresses, no member `0`
    (a₁ a₂ a₃ : GoString) (Hd0 : dir 0 = [])
    (Hhost : ∀ (i : w64) (h : GoString), go!"http://" ++ h ∈ dir i → h = a₁ ∨ h = a₂ ∨ h = a₃)
    (Hrb : receiptBound GF ≤ 2 ^ 64 - 2) :
    -- (2026-10-24, rafthttp stage 6d) the program start's HTTP rights of the peer addresses
    ⊢ httpProtoFree (GF := GF) a₁ -∗ httpProtoFree (GF := GF) a₂ -∗ httpProtoFree (GF := GF) a₃ ={⊤}=∗
      ∃ (γ : RaftNames) (bud : BudgetNames) (ρ₁ ρ₂ ρ₃ : ReqNames)
        (E₁ E₂ E₃ : apply.AEnv GF) (Φs : w64 → w64 → List w8 → GName → IProp GF)
        (γn : NetNames GF),
      ⌜γ.reCfg = GMap.listToSet [id₁, id₂, id₃] ∧ γ.reDyn = none ∧
        γ.reCCOk = ccOk [id₁, id₂, id₃] ∧ γ.reBoot = bootLog ∧ γ.reNoSnap = true ∧
        γ.reNoXfer = true ∧ γn.N = srvNet γ bud ∧ γn.dir = dir ∧ ρ₁.rd.kv.log0 = [[], []] ∧
        ρ₂.rd.kv.st = ρ₁.rd.kv.st ∧ ρ₃.rd.kv.st = ρ₁.rd.kv.st ∧
        kvModel ρ₂.rd.kv = kvModel ρ₁.rd.kv ∧ kvModel ρ₃.rd.kv = kvModel ρ₁.rd.kv ∧
        ρ₂.rd.kv.log0 = [[], []] ∧ ρ₃.rd.kv.log0 = [[], []]⌝ ∗
      memberBoot γ bud bootLog ρ₁ E₁ Φs id₁ ∗
      (netHttpOk γn id₁ ∗ http.httpProtoOwn a₁ (raftProto (netRh γn))) ∗
      memberBoot γ bud bootLog ρ₂ E₂ Φs id₂ ∗
      (netHttpOk γn id₂ ∗ http.httpProtoOwn a₂ (raftProto (netRh γn))) ∗
      memberBoot γ bud bootLog ρ₃ E₃ Φs id₃ ∗
      (netHttpOk γn id₃ ∗ http.httpProtoOwn a₃ (raftProto (netRh γn))) ∗
      etcdKV ρ₁.rd.kv (kvModelSt ρ₁.rd.kv (bootEntries bootLog)) := by
  obtain ⟨hn12, hn13, hn23⟩ := id_ne id₁ id₂ id₃ Hlow Hlow0
  obtain ⟨hp12, hp13, hp23⟩ := pfx_ne id₁ id₂ id₃ Hlow Hlow0
  have Hnz := id_nz id₁ id₂ id₃ Hlow Hlow0
  iintro Hf₁ Hf₂ Hf₃
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
      Φs
      (fun h => GMap.not_elem_of_empty id₁ (h ▸ Hin₁))
      (by
        rw [GMap.elem_of_list_to_set]
        intro h
        exact Hnz _ h rfl)
      rfl Hboot Hpol Hlow Hlow0)
    with ⟨%γ, %issued, %cnt, %γk, %Hγ, #Hcinv, #Hcomm, -, Hghosts, #Hkv, Hetcd, #Hcl, #H0,
      #Hpm, #Hrc, Hms, Hwns⟩
  obtain ⟨hcfg, hdyn, hcc, hboot, htr, htx, hc0, hch, hlog, hiss⟩ := Hγ
  have Hpol' : srvCCPolicy ⟨γ, [], W64 0⟩ := by
    intro ty d h
    simp only at h ⊢
    rw [hcc] at h
    refine ⟨h.1, h.2.1, h.2.2.1, ccPolOk_of_boot _ _ ?_⟩
    rw [hcfg]
    exact h.2.2.2
  icases Hms with ⟨Hm₁, Hm₂, Hm₃, -⟩
  icases Hwns with ⟨Hw₁, Hw₂, Hw₃, -⟩
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
  imod (memberBoot_of γ bud bootLog issued cnt γk Φs id₁ idx₁ cok₁ rev₁ hiss hc0 hch hlog
      Hpol' HΦ₁) $$ Hg₁ Hcomm Hcinv Hbinv Hlb Hcl H0 Hpm Hrc Hkv Hm₁ Hw₁ Hidx₁ Hcok₁ Hrev₁
    with ⟨%ρ₁, %Hρ₁, Hb₁⟩
  imod (memberBoot_of γ bud bootLog issued cnt γk Φs id₂ idx₂ cok₂ rev₂ hiss hc0 hch hlog
      Hpol' HΦ₂) $$ Hg₂ Hcomm Hcinv Hbinv Hlb Hcl H0 Hpm Hrc Hkv Hm₂ Hw₂ Hidx₂ Hcok₂ Hrev₂
    with ⟨%ρ₂, %Hρ₂, Hb₂⟩
  imod (memberBoot_of γ bud bootLog issued cnt γk Φs id₃ idx₃ cok₃ rev₃ hiss hc0 hch hlog
      Hpol' HΦ₃) $$ Hg₃ Hcomm Hcinv Hbinv Hlb Hcl H0 Hpm Hrc Hkv Hm₃ Hw₃ Hidx₃ Hcok₃ Hrev₃
    with ⟨%ρ₃, %Hρ₃, Hb₃⟩
  -- the raft network (rafthttp stage 6d; until then a slot per member): each peer address
  -- reserved for the raft protocol, so every member's transport may post to the others'
  imod (netNames_alloc (srvNet γ bud) dir (∅ : GMap w64 Unit) ⊤) with ⟨%γn, %Hγn, -, #Hreg⟩
  have Hd0' : γn.dir 0 = [] := by rw [Hγn.2]; exact Hd0
  imod (netHttp_reserve3 γn a₁ a₂ a₃ Hd0' (fun i h hm => Hhost i h (by rw [← Hγn.2]; exact hm)))
    $$ Hreg Hf₁ Hf₂ Hf₃ with ⟨#Hnet, Ho₁, Ho₂, Ho₃⟩
  ihave #Hs₁ := Hnet $$ %id₁
  ihave #Hs₂ := Hnet $$ %id₂
  ihave #Hs₃ := Hnet $$ %id₃
  obtain ⟨hst₁, hc0₁, hch₁, hlog₁⟩ := Hρ₁
  obtain ⟨hst₂, hc0₂, hch₂, hlog₂⟩ := Hρ₂
  obtain ⟨hst₃, hc0₃, hch₃, hlog₃⟩ := Hρ₃
  imodintro
  iexists γ, bud, ρ₁, ρ₂, ρ₃, env₀ idx₁ cok₁ rev₁, env₀ idx₂ cok₂ rev₂, env₀ idx₃ cok₃ rev₃, Φs, γn
  iframe Hb₁ Hb₂ Hb₃ Hs₁ Hs₂ Hs₃ Ho₁ Ho₂ Ho₃
  isplitr
  · ipureintro
    exact ⟨hcfg, hdyn, hcc, hboot, htr, htx, Hγn.1, Hγn.2, by rw [hlog₁, hlog],
      by rw [hst₂, hst₁], by rw [hst₃, hst₁],
      by funext B; unfold kvModel; rw [hc0₂, hch₂, hlog₂, hc0₁, hch₁, hlog₁],
      by funext B; unfold kvModel; rw [hc0₃, hch₃, hlog₃, hc0₁, hch₁, hlog₁],
      by rw [hlog₂, hlog], by rw [hlog₃, hlog]⟩
  rw [etcdKV_congr ρ₁.rd.kv γk hst₁,
    show kvModelSt ρ₁.rd.kv (bootEntries bootLog) = kvModelSt γk (bootEntries bootLog) by
      unfold kvModelSt kvLeases kvModel; rw [hc0₁, hch₁, hlog₁]]
  iexact Hetcd

end alloc

end common
end EtcdGrove
end Perennial

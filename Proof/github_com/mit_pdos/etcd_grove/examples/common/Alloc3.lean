/-
**The ghost state a three-member example's `Main` allocates before its members** (2026-10-22, D33).
Lean-first (no Rocq counterpart). What putget3's `putget3_alloc`, linkv3's and linkv3p's
`cluster3_alloc` were, once, at a peer-URL directory `dir`.

`alloc3`: for the three-member cluster `[id₁, id₂, id₃]` (in `bootstrap`'s order) and its bootstrap
log (the node API's `BootLog` at the contexts `ctxs`, `bootCCOk`; the ids' 16 low bits distinct and
not `0`, D21e (A)): each member's names chosen before its `NewServer` (`newServerNames_alloc`) and
its storage registry (2026-10-27, the server port: the server's `SrvRaft` names one registry, so each
member's names are the cluster's with its own registry, `{γ with reg}`), the claimers' facts at each member's
prefix that member's (`srvFloorFact` of its stand-in environment; the prefixes are distinct); the
cluster's resources once (`srvClusterBoot_alloc`, from `proto.Marshal`'s contract `bootMarshal`), each
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

/-! The cluster's invariants do not read the storage registry's name (2026-10-27, the server
port): at `{γ with reg}` they are those at `γ`. -/

theorem srvRaftLogInv_reg (γ : SrvRaft) (r : GName) :
    srvRaftLogInv (GF := GF) (⟨γ, [], W64 0⟩ : ServerRaftNames) ⊢
      srvRaftLogInv ⟨{ γ with reg := r }, [], W64 0⟩ := BI.entails_refl

theorem kvInv_reg (γ : SrvRaft) (r : GName) (γk : KVNames) :
    kvInv (GF := GF) (⟨γ, [], W64 0⟩ : ServerRaftNames) γk ⊢
      kvInv ⟨{ γ with reg := r }, [], W64 0⟩ γk := BI.entails_refl

theorem srvPropMint_reg (γ : SrvRaft) (r : GName) (ids : IdNames) :
    srvPropMint (GF := GF) (⟨γ, [], W64 0⟩ : ServerRaftNames) ids ⊢
      srvPropMint ⟨{ γ with reg := r }, [], W64 0⟩ ids := BI.entails_refl

theorem srvRdCtxInv_reg (γ : SrvRaft) (r : GName) (issued : GName) :
    srvRdCtxInv (GF := GF) (⟨γ, [], W64 0⟩ : ServerRaftNames) issued ⊢
      srvRdCtxInv ⟨{ γ with reg := r }, [], W64 0⟩ issued := BI.entails_refl

/-- **`memberBoot` from the allocations**, for one member (the common step of `alloc3`), at the
cluster's names `γ` with the member's own storage registry `reg` (2026-10-27, the server port: the
server's `SrvRaft` names one registry, and each member's `bootstrap` joins its own; the cluster's
invariants do not read it, so they hold at `{γ with reg}` as at `γ`). -/
theorem memberBoot_of (γ : SrvRaft) (ps : List w64) (ctxs : List (List w8)) (reg : GName)
    (issued cnt : GName) (γk : KVNames) (Φs : w64 → w64 → List w8 → GName → IProp GF)
    (id : w64) (idx : mvcc.IdxNames) (cok rev : GName)
    (Hiss : γk.ids.issued = issued) (Hc0 : γk.c0 = W64 0)
    (Hch : γk.ch0 = apply.alarmChain false false false) (Hlog : γk.log0 = [[], []])
    (Hdyn : γ.dyn = false) (Hvs : γ.vs = ps)
    (HΦ : Φs (idPfxOf (W16 (uint.Z id))) = srvFloorFact (env₀ (GF := GF) idx cok rev)) :
    ⊢ srvRaftLogInv (⟨γ, [], W64 0⟩ : ServerRaftNames) -∗
      idClusterInv issued cnt Φs -∗ (W64 0) ↪[issued]□ (none : Option (List w8 × GName)) -∗
      srvPropMint ⟨γ, [], W64 0⟩ γk.ids -∗ srvRdCtxInv ⟨γ, [], W64 0⟩ issued -∗
      kvInv ⟨γ, [], W64 0⟩ γk -∗
      (idPfxOf (W16 (uint.Z id)) ↪[cnt] ([] : List w64) ∗ Draft.readCredits γ.cl (2 ^ 48) ∗
        Draft.nodeBoot γ.cl srvClusterN ps ctxs id ∗
        ∃ γd : GName, ⌜γ.snapLoc id = some γd⌝ ∗ ghostMapAuth γd 1 (∅ : GMap w64 Unit)) -∗
      idWaitTokAt γk.ids.wn (idPfxOf (W16 (uint.Z id))) -∗
      ghostMapAuth reg 1 (∅ : GMap Loc MemStorNamesRec) -∗
      mvcc.idxFresh idx -∗ ghostMapAuth cok 1 (∅ : GMap w64 mvcc.Log) -∗
      ghostMapAuth rev 1 (∅ : GMap w64 Unit) ==∗
      ∃ ρ : ReqNames, ⌜ρ.rd.kv.st = γk.st ∧ ρ.rd.kv.c0 = γk.c0 ∧ ρ.rd.kv.ch0 = γk.ch0 ∧
        ρ.rd.kv.log0 = γk.log0⌝ ∗
        memberBoot { γ with reg := reg } ctxs ρ (env₀ idx cok rev) Φs id := by
  iintro #Hsrl #Hcl #H0 #Hpm #Hrc #Hkv ⟨Hp, HrdC, Hnb, Hsd⟩ Hwn Hreg Hidx Hcok Hrev
  ihave #Hkv' := kvInv_reg γ reg γk $$ Hkv
  imod (srvMemberBoot_alloc (GF := GF) { γ with reg := reg } cnt γk id cok) $$ Hkv' Hp Hwn
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
  ihave #Hsrl' := srvRaftLogInv_reg γ reg $$ Hsrl
  ihave #Hpm' := srvPropMint_reg γ reg γk.ids $$ Hpm
  ihave #Hrc' := srvRdCtxInv_reg γ reg issued $$ Hrc
  ihave Hnb' : Draft.nodeBoot γ.cl srvClusterN γ.vs ctxs id $$ [Hnb]
  · rw [Hvs]; iexact Hnb
  iframe Hnb' Hsrl' Hcl Hpm' Hrc'  Hsh HrdC Hidx Hcok Hrev Hnk Hkvρ Hwt Hsd Hreg
  isplitr
  · ipureintro
    refine ⟨rfl, Hdyn, by rw [hc0', Hc0], by rw [hch', Hch], by rw [hlog', Hlog], hcok,
      hpfx, ?_⟩
    rw [hpfx]; exact HΦ
  iunfold idNoZero
  rw [hiss', Hiss]
  iexact H0

/-- **What `Main` takes of the ghost state, for its cluster** (see the file header). -/
theorem alloc3 (id₁ id₂ id₃ : w64) (ctxs : List (List w8)) (boot : List Draft.LogEntry)
    (Hlow : ([id₁, id₂, id₃].map (fun id => uint.Z id % 2 ^ 16)).Nodup)
    (Hlow0 : ∀ id ∈ [id₁, id₂, id₃], uint.Z id % 2 ^ 16 ≠ 0)
    (HB : Draft.BootLog [id₁, id₂, id₃] ctxs boot)
    (Hcc : bootCCOk [id₁, id₂, id₃] (Draft.LogEntry.toEntries boot 0))
    (dir : w64 → List GoString)
    -- (2026-10-24, rafthttp stage 6d) the directory's hosts the three peer addresses, no member `0`
    (a₁ a₂ a₃ : GoString) (Hd0 : dir 0 = [])
    (Hhost : ∀ (i : w64) (h : GoString), go!"http://" ++ h ∈ dir i → h = a₁ ∨ h = a₂ ∨ h = a₃)
    (Hrb : receiptBound GF ≤ 2 ^ 64 - 2) (Hrb2 : receiptBound GF + boot.length ≤ 2 ^ 61) :
    -- (2026-10-24, rafthttp stage 6d) the program start's HTTP rights of the peer addresses
    ⊢ bootMarshal (GF := GF) [id₁, id₂, id₃] ctxs (Draft.LogEntry.toEntries boot 0) -∗
      httpProtoFree (GF := GF) a₁ -∗ httpProtoFree (GF := GF) a₂ -∗ httpProtoFree (GF := GF) a₃ ={⊤}=∗
      ∃ (γ₁ γ₂ γ₃ : SrvRaft) (ρ₁ ρ₂ ρ₃ : ReqNames)
        (E₁ E₂ E₃ : apply.AEnv GF) (Φs : w64 → w64 → List w8 → GName → IProp GF)
        (γn : NetNames GF),
      ⌜(∀ γ ∈ [γ₁, γ₂, γ₃], γ.vs = [id₁, id₂, id₃] ∧ γ.dyn = false ∧
          γ.boot = Draft.LogEntry.toEntries boot 0 ∧ γn.N = srvNet γ) ∧
        γn.dir = dir ∧ ρ₁.rd.kv.log0 = [[], []] ∧
        ρ₂.rd.kv.st = ρ₁.rd.kv.st ∧ ρ₃.rd.kv.st = ρ₁.rd.kv.st ∧
        kvModel ρ₂.rd.kv = kvModel ρ₁.rd.kv ∧ kvModel ρ₃.rd.kv = kvModel ρ₁.rd.kv ∧
        ρ₂.rd.kv.log0 = [[], []] ∧ ρ₃.rd.kv.log0 = [[], []]⌝ ∗
      memberBoot γ₁ ctxs ρ₁ E₁ Φs id₁ ∗
      (netHttpOk γn id₁ ∗ http.httpProtoOwn a₁ (raftProto (netRh γn))) ∗
      memberBoot γ₂ ctxs ρ₂ E₂ Φs id₂ ∗
      (netHttpOk γn id₂ ∗ http.httpProtoOwn a₂ (raftProto (netRh γn))) ∗
      memberBoot γ₃ ctxs ρ₃ E₃ Φs id₃ ∗
      (netHttpOk γn id₃ ∗ http.httpProtoOwn a₃ (raftProto (netRh γn))) ∗
      etcdKV ρ₁.rd.kv (kvModelSt ρ₁.rd.kv (bootEntries (Draft.LogEntry.toEntries boot 0))) := by
  obtain ⟨hn12, hn13, hn23⟩ := id_ne id₁ id₂ id₃ Hlow Hlow0
  obtain ⟨hp12, hp13, hp23⟩ := pfx_ne id₁ id₂ id₃ Hlow Hlow0
  have Hnz := id_nz id₁ id₂ id₃ Hlow Hlow0
  iintro #Hmarsh Hf₁ Hf₂ Hf₃
  imod newServerNames_alloc (GF := GF) with ⟨%idx₁, %cok₁, %rev₁, Hidx₁, Hcok₁, Hrev₁⟩
  imod newServerNames_alloc (GF := GF) with ⟨%idx₂, %cok₂, %rev₂, Hidx₂, Hcok₂, Hrev₂⟩
  imod newServerNames_alloc (GF := GF) with ⟨%idx₃, %cok₃, %rev₃, Hidx₃, Hcok₃, Hrev₃⟩
  -- each member's storage registry, its `bootstrap`'s to join
  imod ghost_map_alloc_empty (GF := GF) (K := Loc) (V := MemStorNamesRec) with ⟨%reg₁, Hreg₁⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Loc) (V := MemStorNamesRec) with ⟨%reg₂, Hreg₂⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Loc) (V := MemStorNamesRec) with ⟨%reg₃, Hreg₃⟩
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
  imod (srvClusterBoot_alloc (GF := GF) [id₁, id₂, id₃] ctxs boot Φs reg₁ Hrb Hrb2 HB
      (by simp [hn12, hn13, hn23]) (by simp)
      (by intro h; exact Hnz _ h rfl) Hcc Hlow Hlow0) $$ Hmarsh
    with ⟨%γ, %issued, %cnt, %γk, %Hγ, #Hsrl, #Hkv, Hetcd, #Hcl, #H0, #Hpm, #Hrc, Hms, Hwns⟩
  obtain ⟨hvs, hdyn, hboot, hreg, hc0, hch, hlog, hiss⟩ := Hγ
  icases Hms with ⟨Hm₁, Hm₂, Hm₃, -⟩
  icases Hwns with ⟨Hw₁, Hw₂, Hw₃, -⟩
  imod (memberBoot_of γ [id₁, id₂, id₃] ctxs reg₁ issued cnt γk Φs id₁ idx₁ cok₁ rev₁ hiss hc0 hch hlog
      hdyn hvs HΦ₁) $$ Hsrl Hcl H0 Hpm Hrc Hkv Hm₁ Hw₁ Hreg₁ Hidx₁ Hcok₁ Hrev₁
    with ⟨%ρ₁, %Hρ₁, Hb₁⟩
  imod (memberBoot_of γ [id₁, id₂, id₃] ctxs reg₂ issued cnt γk Φs id₂ idx₂ cok₂ rev₂ hiss hc0 hch hlog
      hdyn hvs HΦ₂) $$ Hsrl Hcl H0 Hpm Hrc Hkv Hm₂ Hw₂ Hreg₂ Hidx₂ Hcok₂ Hrev₂
    with ⟨%ρ₂, %Hρ₂, Hb₂⟩
  imod (memberBoot_of γ [id₁, id₂, id₃] ctxs reg₃ issued cnt γk Φs id₃ idx₃ cok₃ rev₃ hiss hc0 hch hlog
      hdyn hvs HΦ₃) $$ Hsrl Hcl H0 Hpm Hrc Hkv Hm₃ Hw₃ Hreg₃ Hidx₃ Hcok₃ Hrev₃
    with ⟨%ρ₃, %Hρ₃, Hb₃⟩
  -- the raft network (rafthttp stage 6d; until then a slot per member): each peer address
  -- reserved for the raft protocol, so every member's transport may post to the others'
  imod (netNames_alloc (srvNet γ) dir (∅ : GMap w64 Unit) ⊤) with ⟨%γn, %Hγn, -, #Hreg⟩
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
  iexists { γ with reg := reg₁ }, { γ with reg := reg₂ }, { γ with reg := reg₃ }, ρ₁, ρ₂, ρ₃,
    env₀ idx₁ cok₁ rev₁, env₀ idx₂ cok₂ rev₂, env₀ idx₃ cok₃ rev₃, Φs, γn
  iframe Hb₁ Hb₂ Hb₃ Hs₁ Hs₂ Hs₃ Ho₁ Ho₂ Ho₃
  isplitr
  · ipureintro
    refine ⟨?_, Hγn.2, by rw [hlog₁, hlog],
      by rw [hst₂, hst₁], by rw [hst₃, hst₁],
      by funext B; unfold kvModel; rw [hc0₂, hch₂, hlog₂, hc0₁, hch₁, hlog₁],
      by funext B; unfold kvModel; rw [hc0₃, hch₃, hlog₃, hc0₁, hch₁, hlog₁],
      by rw [hlog₂, hlog], by rw [hlog₃, hlog]⟩
    intro γ' hγ'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hγ'
    rcases hγ' with h | h | h <;> subst h <;> exact ⟨hvs, hdyn, hboot, by rw [Hγn.1]; rfl⟩
  rw [← hboot]
  rw [etcdKV_congr ρ₁.rd.kv γk hst₁,
    show kvModelSt ρ₁.rd.kv (bootEntries γ.boot) = kvModelSt γk (bootEntries γ.boot) by
      unfold kvModelSt kvLeases kvModel; rw [hc0₁, hch₁, hlog₁]]
  iexact Hetcd

end alloc

end common
end EtcdGrove
end Perennial

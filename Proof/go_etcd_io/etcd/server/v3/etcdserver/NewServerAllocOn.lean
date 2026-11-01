/-
**The ghost allocations `NewServer.specM true` takes** (the auth plan's E2z, 2026-10-26;
`notes/decisions.md`, "E2z of the auth plan"): `NewServerAlloc.lean`'s, with the mode-`on` KV
invariant (`kvInvOn`, E2q) at the start chain with auth on, so a caller of `server_new_auth_on`
can build its precondition: the cluster's resources (`srvClusterBootOn_alloc`: the KV invariant
allocated at the bootstrap log by `kvInvOn_alloc_boot`) and a member's names
(`srvMemberBootOn_alloc`), each the mode-off one's with `kvInv` replaced by
`kvInvOn _ _ srvAuthSt0` and the start chain `alarmChain true false false`. (2026-10-27: over raft's
node API; raft's allocation continuation and its standing update for raft's own entries are gone:
the server's log holds the requested entries only.)

**Additive.** Nothing in `NewServerAlloc.lean` changes; the examples keep allocating with it.

Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.NewServerAlloc
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ServerOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ProposeOn

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section alloc
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **A new cluster's resources, for the servers, in the mode `on`** (`srvClusterBoot_alloc`'s: the
same, with the mode-`on` KV invariant from `srvAuthSt0` and the start chain with auth on; 2026-10-27:
over raft's node API): a static cluster of the peers `ps` from the bootstrap log `boot`
(`cluster_alloc` with leader transfer off and no snapshot's data vouched for), the server's raft
names over it (`srvLogInv_alloc`, at the `MemoryStorage` registry `reg` and the members' snapshot
directories) with the server's raft invariant (`srvRaftLogInv`: the cluster's kind, its allocation
`readyFits`, started from the bootstrap log), the KV
invariant at the bootstrap log (`kvInv_alloc_boot`) with the client's view of the auth history
(`authHistView`, at the start's state: the auth-mode merge's 5b), the cluster's claims at the claimers' facts
`Φs` (the caller's: a member's at its prefix), with the reserved id `0`, the proposals' mint, the
read contexts, and each member's share: its prefix's entry of the claims, `2 ^ 48` of the
cluster's read credits, its boot token and its snapshot directory. The pure premises (D21e (A),
`issues/etcd-request-id-member-prefix.md`): the members' ids' 16 low bits are distinct and not
`0`; every bootstrap conf change of id `0`, one `applyConfChange` takes (`ccBootOk`). -/
theorem srvClusterBootOn_alloc (ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (Φs : w64 → w64 → List w8 → GName → IProp GF) (reg : GName)
    (Hrb : receiptBound GF ≤ 2 ^ 64 - 2) (Hrb2 : receiptBound GF + boot.length ≤ 2 ^ 61)
    (HB : BootLog ps ctxs boot) (Hnd : ps.Nodup) (Hne : ps ≠ []) (Hnz : W64 0 ∉ ps)
    (hcc : ∀ e ∈ LogEntry.toEntries boot 0,
      ccIdOf e.Data' = W64 0 ∧ ccBootOk (GMap.listToSet ps) e.Data')
    (Hpd : (ps.map (fun id => uint.Z id % 2 ^ 16)).Nodup)
    (Hp0 : ∀ id ∈ ps, uint.Z id % 2 ^ 16 ≠ 0) :
    ⊢ bootMarshal (GF := GF) ps ctxs (LogEntry.toEntries boot 0) ={⊤}=∗
      ∃ (γ : SrvRaft) (issued cnt : GName) (γk : KVNames),
        ⌜γ.vs = ps ∧ γ.rule = srvRule (W64 0) (LogEntry.toEntries boot 0) ∧ γ.boot = LogEntry.toEntries boot 0 ∧ γ.reg = reg ∧
          γk.c0 = W64 0 ∧ γk.ch0 = apply.alarmChain true false false ∧ γk.log0 = [[], []] ∧
          γk.ids.issued = issued⌝ ∗
        srvRaftLogInv (⟨γ, [], W64 0⟩ : ServerRaftNames) ∗
        kvInvOn ⟨γ, [], W64 0⟩ γk srvAuthSt0 ∗
        etcdKV γk (kvStateOf (kvModelOn γk srvAuthSt0 (bootEntries γ.boot))) ∗
        -- (5b) the client's view of the auth history, at the start
        authHistView γk [srvAuthSt0] ∗
        idClusterInv issued cnt Φs ∗ (W64 0) ↪[issued]□ (none : Option (List w8 × GName)) ∗
        srvPropMint ⟨γ, [], W64 0⟩ γk.ids ∗ srvRdCtxInv ⟨γ, [], W64 0⟩ issued ∗
        ([∗list] id ∈ ps, (idPfxOf (W16 (uint.Z id)) ↪[cnt] ([] : List w64) ∗
          nodeBoot γ.cl srvClusterN ps ctxs id ∗
          -- (2026-10-26, D22 J2) and its snapshot directory, empty (`SrvRaft.snapLoc`)
          ∃ γd : GName, ⌜γ.snapLoc id = some γd⌝ ∗ ghostMapAuth γd 1 (∅ : GMap w64 Unit))) ∗
        -- (linkv-txn stage B1, 2026-10-20) each member's entry of the registries' map
        [∗list] id ∈ ps, idWaitTokAt γk.ids.wn (idPfxOf (W16 (uint.Z id))) := by
  -- PORT(durability stage II): a definition or statement it uses changed (durability stage I-2..I-8)
  sorry

/-- **The mode-`on` KV invariant reads only the cluster's KV names** (`kvInv_congr`'s). -/
theorem kvInvOn_congr (γs : ServerRaftNames) (γk γk' : KVNames) (st₀ : auth.AuthState)
    (h : γk.st = γk'.st ∧ γk.c0 = γk'.c0 ∧ γk.ch0 = γk'.ch0 ∧ γk.log0 = γk'.log0 ∧
      γk.ids.issued = γk'.ids.issued ∧ γk.ids.wn = γk'.ids.wn ∧ γk.hist = γk'.hist) :
    kvInvOn (GF := GF) γs γk st₀ = kvInvOn γs γk' st₀ := by
  obtain ⟨h1, h2, h3, h4, h6, h7, h8⟩ := h
  unfold kvInvOn kvWorkOn entryClaim idClaim kvModelOn idRegd idWaitIs admStates
  rw [h1, h2, h3, h4, h6, h7, h8]

/-- **A member's names and share in the mode `on`** (`srvMemberBoot_alloc`'s): the mode-`on` KV
invariant at its names, as `NewServer.specM true`'s `kvInvM true`. -/
theorem srvMemberBootOn_alloc (γ : SrvRaft) (cnt : GName) (γk : KVNames) (id : w64)
    (cok : GName) :
    ⊢ kvInvOn (GF := GF) ⟨γ, [], W64 0⟩ γk srvAuthSt0 -∗
      idPfxOf (W16 (uint.Z id)) ↪[cnt] ([] : List w64) -∗
      idWaitTokAt γk.ids.wn (idPfxOf (W16 (uint.Z id))) ==∗
      ∃ ρ : ReqNames,
        ⌜ρ.rd.raft = ⟨γ, [], W64 0⟩ ∧ ρ.rd.kv.st = γk.st ∧ ρ.rd.kv.c0 = γk.c0 ∧
          ρ.rd.kv.ch0 = γk.ch0 ∧ ρ.rd.kv.log0 = γk.log0 ∧
          ρ.rd.kv.cok = cok ∧ ρ.ids.issued = γk.ids.issued ∧ ρ.ids.cnt = cnt ∧
          ρ.ids.pfx = idPfxOf (W16 (uint.Z id)) ∧ ρ.rd.kv.hist = γk.hist⌝ ∗
        kvInvM true ⟨γ, [], W64 0⟩ ρ.rd.kv srvAuthSt0 ∗ idShare ρ.ids ∗
        srvReadNamesFreshNK ρ.rd ∗ idWaitTok ρ.ids := by
  iintro #Hkv Hp Hwt
  imod ghost_map_alloc_empty (GF := GF) (K := w64) (V := Unit) with ⟨%γsl, Hsl⟩
  imod mono_nat_own_alloc (GF := GF) 0 with ⟨%γa, Ha, -⟩
  imod mono_nat_own_alloc (GF := GF) 0 with ⟨%γc, Hc, -⟩
  imod ghostVar_alloc (GF := GF) ((null, ⟨γa, γa⟩) : Loc × NeedNames) with ⟨%γn, Hn⟩
  imod ghost_map_alloc_empty (GF := GF) (K := w64) (V := mvcc.Log) with ⟨%γl, Hl⟩
  imod ghostVar_alloc (GF := GF) false with ⟨%γp, Hpd⟩
  imod ghostVar_alloc (GF := GF) γk.log0.length with ⟨%γhi, Hhi⟩
  imodintro
  iexists ⟨0, ⟨γa, γc, γn, γl, γp, ⟨γ, [], W64 0⟩,
    ⟨γk.st, γk.c0, γk.ch0, γk.log0, cok, γhi,
      ⟨γk.ids.issued, cnt, γsl, idPfxOf (W16 (uint.Z id)), γk.ids.wn⟩, γk.hist⟩⟩⟩
  isplitr
  · ipureintro
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  isplitr
  · dsimp only
    rw [kvInvM_true, kvInvOn_congr _ ⟨γk.st, γk.c0, γk.ch0, γk.log0, cok, γhi,
      ⟨γk.ids.issued, cnt, γsl, idPfxOf (W16 (uint.Z id)), γk.ids.wn⟩, γk.hist⟩ γk srvAuthSt0
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩]
    iexact Hkv
  isplitl [Hp Hsl]
  · iunfold idShare
    iframe Hp Hsl
  isplitr [Hwt]
  · iunfold srvReadNamesFreshNK
    iframe Ha Hc Hl Hpd Hhi
    iexists _
    iexact Hn
  iexact Hwt

end alloc

end EtcdGrove
end Perennial

#print axioms Perennial.EtcdGrove.srvClusterBootOn_alloc
#print axioms Perennial.EtcdGrove.srvMemberBootOn_alloc

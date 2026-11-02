/-
**The ghost allocations `NewServer.spec` takes** (item 9, point 7, 2026-10-18; the cluster's and
the members', stage M4 of D21, 2026-10-19): what the adequacy example's `Main` allocates before
calling `NewServer`. Lean-first (no Rocq counterpart).

**The cluster's, once** (D21e (A), stage M4: until then one server owned them):
* `srvBootClient` / `srvRaftBoot_alloc`: **a new cluster's raft ghost state, for the servers**:
  `ownRaftGhost_alloc_boot` with the servers' continuation, which allocates the KV state's
  variable and the KV invariant at the bootstrap log (`kvInv_alloc_boot`, from the client's half of
  raft's committed log `rLog γ bootLog`) inside the continuation, at the cluster's KV names (no
  member's read names: a member's are its own, `srvMemberBoot_alloc`), and builds raft's standing
  update `noopAu` from it (`kv_noop_au`, `srvNoopAu_to_noopAu_of`). Its output (`srvBootOut`):
  `kvInv`, the client's `etcdKV` at the bootstrap log's model and the fresh-token authorities.
* `srvClusterBoot_alloc`: that, with the cluster's claims (`idCluster_alloc`, under the pure
  premise that the members' ids' 16 low bits are distinct and not `0`: D21e (A),
  `issues/etcd-request-id-member-prefix.md`), the proposals' mint (`srvPropMint`), the read
  contexts (`srvRdCtxInv`), and each member's share: its prefix's entry of the claims and `2 ^ 48`
  of raft's read credits (fewer than `2 ^ 16` members, from the premise).

**A member's** (`srvMemberBoot_alloc`): its read names at the cluster's KV names (the KV invariant
reads only those, `kvInv_congr`), its wait slots (`idShare`), and the names chosen before the
call (`newServerNames_alloc`: the store's index names, its certificate map, the revisions' map).

**`NewServer.spec`'s premises** (D19g (a), 2026-10-18): `NewServer.spec` takes `kvInv ρ.rd.raft
ρ.rd.kv` and `srvReadNamesFreshNK ρ.rd` (`InvBuild.lean`); until then it took `rLog γ bootLog`
owned and allocated `kvInv` itself, which no caller could meet: raft's allocation needs `noopAu`
from its continuation, which only an invariant holding `rLog` gives.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BuildAlloc
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVLemmas

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

/-- **The fresh names chosen before `NewServer`** (D13a) but raft's, the read names and (since
stage M4) the id generator's: the store's index names, its certificate map and the revisions'
map. -/
theorem newServerNames_alloc :
    ⊢ |==> ∃ (idx : mvcc.IdxNames) (cok rev : GName),
      mvcc.idxFresh (GF := GF) idx ∗
      ghostMapAuth cok 1 (∅ : GMap w64 mvcc.Log) ∗ ghostMapAuth rev 1 (∅ : GMap w64 Unit) := by
  istart
  imod mvcc.idxFresh_alloc (GF := GF) with ⟨%idx, Hidx⟩
  imod ghost_map_alloc_empty (GF := GF) (K := w64) (V := mvcc.Log) with ⟨%cok, Hcok⟩
  imod ghost_map_alloc_empty (GF := GF) (K := w64) (V := Unit) with ⟨%rev, Hrev⟩
  imodintro
  iexists idx, cok, rev
  iframe

/-- **The KV invariant reads only the cluster's KV names** (stage M4): the state's variable, the
start values and the claims' map; not a member's certificate map, its applied
height or its slots and prefix. -/
theorem kvInv_congr (γs : ServerRaftNames) (γk γk' : KVNames)
    (h : γk.st = γk'.st ∧ γk.c0 = γk'.c0 ∧ γk.ch0 = γk'.ch0 ∧ γk.log0 = γk'.log0 ∧
      γk.ids.issued = γk'.ids.issued ∧ γk.ids.wn = γk'.ids.wn ∧ γk.cmp = γk'.cmp ∧
      γk.rlog = γk'.rlog ∧ γk.cret = γk'.cret) :
    kvInv (GF := GF) γs γk = kvInv γs γk' := by
  obtain ⟨h1, h2, h3, h4, h6, h7, h8, h9, h10⟩ := h
  unfold kvInv kvWork entryClaim kvModelSt kvLeases kvModel idRegdAt idWaitIs cmpLogOk
    cmpEntryOk kvModel
  rw [h1, h2, h3, h4, h6, h7, h8, h9, h10]

/-- The client's `etcdKV` reads only the state's variable. -/
theorem etcdKV_congr (γk γk' : KVNames) (h : γk.st = γk'.st) (σ : KVState) :
    etcdKV (GF := GF) γk σ = etcdKV γk' σ := by
  unfold etcdKV; rw [h]

/-- The proposals' mint reads only the claims' map. -/
theorem srvPropMint_congr (γs : ServerRaftNames) (γi γi' : IdNames) (h : γi.issued = γi'.issued) :
    srvPropMint (GF := GF) γs γi = srvPropMint γs γi' := by
  unfold srvPropMint idClaimAny; rw [h]

/-- A list whose image is without repeats is without repeats. -/
theorem nodup_of_map {α β : Type} (f : α → β) : ∀ {l : List α}, (l.map f).Nodup → l.Nodup
  | [], _ => List.nodup_nil
  | a :: l, h => by
    rw [List.map_cons, List.nodup_cons] at h
    exact List.nodup_cons.2 ⟨fun ha => h.1 (List.mem_map_of_mem ha), nodup_of_map f h.2⟩

/-- (2026-10-26, D22 J2, R-loc) **The members' snapshot directories, allocated empty**, before
the server's raft names (which name them, `SrvRaft.snapLoc`; raft's `reSnapLoc` until 2026-10-27):
one ghost map `index ↦ ()` per member of `ps` (distinct), each member's authority (what
`NewServer`'s `snapDir_init` takes). -/
theorem snapDirs_alloc : ∀ (ps : List w64), ps.Nodup →
    ⊢ |==> ∃ sl : w64 → Option GName,
      [∗list] id ∈ ps, ∃ γd : GName, ⌜sl id = some γd⌝ ∗
        ghostMapAuth (GF := GF) γd 1 (∅ : GMap w64 Unit)
  | [], _ => by
    istart
    imodintro
    iexists (fun _ => none)
    iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
    itrivial
  | a :: ps, hnd => by
    have hna : a ∉ ps := (List.nodup_cons.1 hnd).1
    istart
    imod (snapDirs_alloc ps (List.nodup_cons.1 hnd).2) with ⟨%sl, Hs⟩
    imod ghost_map_alloc_empty (GF := GF) (K := w64) (V := Unit) with ⟨%γa, Ha⟩
    imodintro
    iexists (fun x => if x = a then some γa else sl x)
    iapply BigSepL.bigSepL_cons.2
    isplitl [Ha]
    · iexists γa
      iframe Ha
      ipureintro; simp
    iapply (BigSepL.bigSepL_mono (PROP := IProp GF) (fun {k x} hk => ?_)) $$ Hs
    have hx : x ≠ a := fun h => hna (h ▸ List.mem_of_getElem? hk)
    iintro ⟨%γd, %h, H⟩
    iexists γd
    iframe H
    ipureintro; simp [hx, h]

/- (2026-10-30, the repair) `readCredits_members` is gone with raft's read credits. -/
/-- The node API's bootstrap log, as the server's entries, is the node API's log. -/
theorem bootEntries_toLE (boot : List LogEntry) :
    (bootEntries (LogEntry.toEntries boot 0)).map EntryModel.toLE = boot := by
  apply List.ext_getElem?
  intro n
  unfold bootEntries LogEntry.toEntries
  simp only [List.map_map, List.getElem?_map, List.getElem?_mapIdx]
  cases boot[n]? <;> rfl

/-- **A new cluster's resources, for the servers** (D21e (A), stage M4; 2026-10-27: over raft's
node API; see the file header): a static cluster of the peers `ps` from the bootstrap log `boot`
(`cluster_alloc` with leader transfer off and no snapshot's data vouched for), the server's raft
names over it (`srvLogInv_alloc`, at the `MemoryStorage` registry `reg` and the members' snapshot
directories) with the server's raft invariant (`srvRaftLogInv`: the cluster's kind, its allocation
`readyFits`, started from the bootstrap log), the KV
invariant at the bootstrap log (`kvInv_alloc_boot`), the cluster's claims at the claimers' facts
`Φs` (the caller's: a member's at its prefix), with the reserved id `0`, the proposals' mint, the
read contexts, and each member's share: its prefix's entry of the claims (2026-10-30: no read credits), the
its boot token and its snapshot directory. The pure premises (D21e (A),
`issues/etcd-request-id-member-prefix.md`): the members' ids' 16 low bits are distinct and not
`0`; every bootstrap conf change of id `0`, one `applyConfChange` takes (`ccBootOk`). -/
theorem srvClusterBoot_alloc (ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (xs : w64 → mvcc.IdxNames) (reg : GName)
    (Hrb : receiptBound GF ≤ 2 ^ 64 - 2) (Hrb2 : receiptBound GF + boot.length ≤ 2 ^ 61)
    (HB : BootLog ps ctxs boot) (Hnd : ps.Nodup) (Hne : ps ≠ []) (Hnz : W64 0 ∉ ps)
    (hcc : ∀ e ∈ LogEntry.toEntries boot 0,
      ccIdOf e.Data' = W64 0 ∧ ccBootOk (GMap.listToSet ps) e.Data')
    (Hpd : (ps.map (fun id => uint.Z id % 2 ^ 16)).Nodup)
    (Hp0 : ∀ id ∈ ps, uint.Z id % 2 ^ 16 ≠ 0) (cmp : Bool) (cret : Nat := 0) :
    ⊢ bootMarshal (GF := GF) ps ctxs (LogEntry.toEntries boot 0) ={⊤}=∗
      ∃ (γ : SrvRaft) (issued cnt wn fs : GName) (γk : KVNames),
        ⌜γ.vs = ps ∧ γ.rule = srvRule (W64 0) (LogEntry.toEntries boot 0) ∧ γ.boot = LogEntry.toEntries boot 0 ∧ γ.reg = reg ∧
          γk.c0 = W64 0 ∧ γk.ch0 = apply.alarmChain false false false ∧ γk.log0 = [[], []] ∧
          γk.ids.issued = issued ∧ γk.ids.cnt = cnt ∧ γk.ids.wn = wn ∧ γk.ids.fs = fs ∧
          γk.cmp = cmp ∧ γk.cret = cret ∧ γk.lg = false⌝ ∗
        srvRaftLogInv (⟨γ, [], W64 0⟩ : ServerRaftNames) ∗
        kvInv ⟨γ, [], W64 0⟩ γk ∗ etcdKV γk (kvModelSt γk (bootEntries γ.boot)) ∗
        idClusterInv issued cnt wn fs srvFloorFacts ∗ (W64 0) ↪[issued]□ (none : Option IdClaimV) ∗
        srvPropMint ⟨γ, [], W64 0⟩ γk.ids ∗ srvRdCtxInv ⟨γ, [], W64 0⟩ issued ∗
        ([∗list] id ∈ ps, ((idPfxOf (W16 (uint.Z id)), 0) ↪[cnt] ([] : List w64) ∗
          idKeyFactAt fs (idPfxOf (W16 (uint.Z id)), 0) (xs (idPfxOf (W16 (uint.Z id)))) ∗
          -- (2026-11-01, durability layer 4) with its durable state at `RaftState.init` and its
          -- vacant id (`cluster_alloc`'s, `StartNode`'s premises)
          (nodeBoot γ.cl srvClusterN ps ctxs id ∗ raftState γ.cl id RaftState.init ∗
            nodeVacant γ.cl id) ∗
          -- (2026-10-26, D22 J2) and its snapshot directory, empty (`SrvRaft.snapLoc`)
          ∃ γd : GName, ⌜γ.snapLoc id = some γd⌝ ∗ ghostMapAuth γd 1 (∅ : GMap w64 Unit))) ∗
        -- (linkv-txn stage B1, 2026-10-20) each member's entry of the registries' map
        [∗list] id ∈ ps, idWaitTokAt wn (idPfxOf (W16 (uint.Z id)), 0) := by
  letI := srvAnyStor (GF := GF)
  obtain ⟨Hpnd, Hok, Hlen⟩ := idPfxsOf_ok ps Hpd Hp0
  have hboot := srvBootLogOk_of_BootLog ps ctxs boot HB
  obtain ⟨hidx, hty⟩ := bootEntries_ok ps _ hboot
  have hbne : boot ≠ [] := by
    intro h
    have := HB.1
    rw [h] at this
    exact Hne (List.length_eq_zero_iff.1 this.symm)
  have hnf : ∀ m ∈ bootEntries (LogEntry.toEntries boot 0),
      ¬ m.toLE.isFiller ∧ ¬ m.toLE.isEmptyV2 := by
    intro m hm
    refine ⟨fun hf => ?_, fun hf => ?_⟩
    · obtain ⟨-, h⟩ := hf
      simp only [EntryModel.toLE] at h
      rw [hty m hm] at h
      exact absurd h (by word)
    · obtain ⟨-, h⟩ := hf
      simp only [EntryModel.toLE] at h
      rw [hty m hm] at h
      exact absurd h (by word)
  have hnn : ∀ m ∈ bootEntries (LogEntry.toEntries boot 0), m.typ ≠ W32 0 := by
    intro m hm
    rw [hty m hm]
    decide
  have hccL : ∀ m ∈ bootEntries (LogEntry.toEntries boot 0), m.typ = W32 1 →
      ccBootOk (GMap.listToSet ps) m.data := by
    intro m hm _
    unfold bootEntries at hm
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hm
    exact (hcc e he).2
  have hcne : GMap.listToSet ps ≠ ∅ := by
    intro h
    obtain ⟨p, ps', rfl⟩ := List.exists_cons_of_ne_nil Hne
    have : p ∈ GMap.listToSet (p :: ps') :=
      (GMap.elem_of_list_to_set p _).2 (List.mem_cons_self ..)
    rw [h] at this
    exact (GMap.not_elem_of_empty p) this
  have hnz' : W64 0 ∉ GMap.listToSet ps := fun h => Hnz ((GMap.elem_of_list_to_set _ _).1 h)
  have hsz : GMap.size (GMap.listToSet ps) < 2 ^ 62 := by
    rw [GMap.size_list_to_set ps Hnd]; omega
  have hval := Membership.simple_valid _ hcne hnz' hsz
  iintro #Hmarsh
  imod (idCluster_alloc (GF := GF) (idPfxsOf ps) srvFloorFacts xs ⊤ Hpnd Hok)
    with ⟨%issued, %cnt, %wn, %fs, #Hcl, #H0, Hps⟩
  -- (R2c) each member's first key: its list, its registry cell, its facts' parameter
  ihave ⟨Hps, Hrest⟩ := (BigSepL.bigSepL_sep_eqv (PROP := IProp GF)).1 $$ Hps
  ihave ⟨Hwns, Hfs⟩ := (BigSepL.bigSepL_sep_eqv (PROP := IProp GF)).1 $$ Hrest
  imod (snapDirs_alloc (GF := GF) ps Hnd) with ⟨%sl, Hsd⟩
  -- the node API's cluster from the bootstrap log, proposals not duplicated
  imod (cluster_alloc (GF := GF) srvClusterN ps ctxs boot false sl ⊤ Hrb Hne Hnd Hnz
      (by omega) (fun _ => HB)) $$ [Hmarsh]
    with ⟨%cl, ⟨%Hdup, %Hcsl, %Hbl⟩, Hops, Hctxs, #Hst, Hdec, #Hca0, Hsm, Hslots, Hboots⟩
  · rw [if_neg hbne]; iexact Hmarsh
  isimp only [hbne, ↓reduceIte] at Hboots
  icases Hboots with ⟨#Hbl0c, Hboots⟩
  imod confPolicy_alloc cl srvConfN (srvRule (W64 0) (LogEntry.toEntries boot 0)) ⊤ $$ Hdec
    with #Hpol
  imod (inv_alloc srvSnapsN ⊤ iprop(∃ S, ownSnapsMade (GF := GF) cl S)) $$ [Hsm] with #Hsinv
  · inext; iexists []; iexact Hsm
  -- the server's raft names over it, its log of requested entries at the bootstrap log
  imod (srvLogInv_alloc (GF := GF) cl ps (srvRule (W64 0) (LogEntry.toEntries boot 0))
      (LogEntry.toEntries boot 0) reg sl (bootEntries (LogEntry.toEntries boot 0)) ⊤
      hidx hnf hnn hccL) $$ [Hops]
    with ⟨%γ, %Hγ, #Hli, HL, #Hlb0, Hfresh, Hrdf⟩
  · rw [bootEntries_toLE]; iexact Hops
  obtain ⟨hcl, hvs, hrule, hbt, hreg, hsl⟩ := Hγ
  ihave #Hfits : iprop(letI := srvStor (GF := GF) γ; readyFits (GF := GF) cl srvClusterN) $$ []
  · iapply readyFits_intro
    rw [Hbl]; exact Hrb2
  ihave #Hcok : srvClusterOk (⟨γ, [], W64 0⟩ : ServerRaftNames) $$ []
  · iunfold srvClusterOk
    simp only [hcl, hvs, hrule, SrvRaft.cfg]
    iframe Hst Hpol Hca0 Hfits Hsinv
    ipureintro
    exact ⟨Hdup, srvRule_keeps _ _ _ hval, by rw [Hcsl, hsl], by rw [Hbl, hbt]; simp [LogEntry.toEntries]⟩
  ihave #Hsrl : srvRaftLogInv (⟨γ, [], W64 0⟩ : ServerRaftNames) $$ []
  · iunfold srvRaftLogInv
    iframe Hli Hcok Hlb0
    isplitr
    · ipureintro; rfl
    isplitr
    · ipureintro; rfl
    -- (2026-10-31, S5) the bootstrap log committed first
    isplitr
    · iunfold srvRLogLb
      isplitl
      · have he : srvLE (⟨γ, [], W64 0⟩ : ServerRaftNames) (γ.boot.map EntryModel.ofM) = boot := by
          simp only [srvLE, List.nil_append]; rw [hbt]; exact bootEntries_toLE boot
        rw [he]; simp only [hcl]; iexact Hbl0c
      · ipureintro; rw [hbt]; exact hidx
    ipureintro; exact ⟨ps, Hne, by rw [hbt]; exact hboot⟩
  -- the KV invariant at the bootstrap log
  let γk0 : KVNames := ⟨0, W64 0, apply.alarmChain false false false, [[], []], 0, 0,
    ⟨issued, cnt, 0, 0, wn, 0, fs⟩, 0, cmp, γ.log, cret, false⟩
  imod ghostVar_alloc (GF := GF) (kvModelSt γk0 (bootEntries γ.boot)) with ⟨%γst, Hstv⟩
  let γk : KVNames := { γk0 with st := γst }
  have hm : kvModelSt γk (bootEntries γ.boot) = kvModelSt γk0 (bootEntries γ.boot) := rfl
  imod (kvInv_alloc_boot (GF := GF) ⟨γ, [], W64 0⟩ γk ps ⊤ rfl rfl
      (by show srvBootLogOk ps γ.boot; rw [hbt]; exact hboot)
      (fun e he => by
        show ccIdOf e.Data' = W64 0 ∧ ccBootOk γ.cfg e.Data'
        unfold SrvRaft.cfg
        rw [hvs]
        exact hcc e (by rw [← hbt]; exact he))
      rfl rfl (by simp [γk, γk0]) (mvcc.LogPutsLe.empties _) rfl)
    $$ [HL] [Hstv] with ⟨#Hkv, Hetcd⟩
  · simp only [hbt]; iexact HL
  · rw [hm]; iexact Hstv
  -- the mints
  imod (srvPropMint_alloc ⟨γ, [], W64 0⟩ γk.ids ⊤) $$ Hfresh with #Hpm
  imod (srvRdCtxInv_alloc ⟨γ, [], W64 0⟩ issued ⊤) $$ Hrdf [Hctxs] with #Hrc
  · simp only [hcl]; iexact Hctxs
  imodintro
  iexists γ, issued, cnt, wn, fs, γk
  iframe Hsrl Hkv Hetcd Hcl H0 Hpm Hrc
  isplitr
  · ipureintro
    exact ⟨hvs, hrule, hbt, hreg, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  isplitl [Hps Hfs Hsd Hboots Hslots]
  · iapply (BigSepL.bigSepL_sep_eqv (PROP := IProp GF)).2
    ihave Hbc : iprop([∗list] id ∈ ps, ((nodeBoot γ.cl srvClusterN ps ctxs id ∗
        raftState γ.cl id RaftState.init ∗ nodeVacant γ.cl id) ∗
        ∃ γd : GName, ⌜γ.snapLoc id = some γd⌝ ∗ ghostMapAuth (GF := GF) γd 1 (∅ : GMap w64 Unit)))
      $$ [Hsd Hboots Hslots]
    · iapply (BigSepL.bigSepL_sep_eqv (PROP := IProp GF)).2
      rw [hcl, hsl]
      isplitl [Hboots Hslots]
      · iapply (BigSepL.bigSepL_sep_eqv (PROP := IProp GF)).2
        iframe Hboots Hslots
      iexact Hsd
    have hm : ([∗list] p ∈ idPfxsOf ps, (p, 0) ↪[cnt] ([] : List w64)) =
        ([∗list] id ∈ ps, ((idPfxOf (W16 (uint.Z id)), 0) ↪[cnt] ([] : List w64) : IProp GF)) := by
      unfold idPfxsOf; rw [BigSepL.bigSepL_map]
    rw [← hm]
    iframe Hps
    iapply (BigSepL.bigSepL_sep_eqv (PROP := IProp GF)).2
    iframe Hbc
    have hf : ([∗list] p ∈ idPfxsOf ps, idKeyFactAt (GF := GF) fs (p, 0) (xs p)) =
        ([∗list] id ∈ ps, idKeyFactAt (GF := GF) fs (idPfxOf (W16 (uint.Z id)), 0)
          (xs (idPfxOf (W16 (uint.Z id))))) := by
      unfold idPfxsOf; rw [BigSepL.bigSepL_map]
    rw [← hf]
    iexact Hfs
  have hm : ([∗list] p ∈ idPfxsOf ps, idWaitTokAt (GF := GF) wn (p, 0)) =
      ([∗list] id ∈ ps, idWaitTokAt (GF := GF) wn (idPfxOf (W16 (uint.Z id)), 0)) := by
    unfold idPfxsOf; rw [BigSepL.bigSepL_map]
  rw [← hm]
  iexact Hwns

/-- **A member's names and share** (D21e (A), stage M4; see the file header): for the member
`id` of a cluster allocated by `srvClusterBoot_alloc` (its KV names `γk`, its claims' names), the
request names `ρ`: its read names at the cluster's KV names but for its own applied height and the
certificate map `cok` (the member's store's), its id names (the cluster's claims, its slots, its
prefix); with its read names' fresh rows (`srvReadNamesFreshNK`), the KV invariant at its names
(`kvInv_congr`) and its share of the claims (`idShare`, from its prefix's entry). -/
theorem srvMemberBoot_alloc (γ : SrvRaft) (cnt : GName) (γk : KVNames) (id : w64)
    (cok : GName) :
    ⊢ kvInv (GF := GF) ⟨γ, [], W64 0⟩ γk -∗
      (idPfxOf (W16 (uint.Z id)), 0) ↪[cnt] ([] : List w64) -∗
      idWaitTokAt γk.ids.wn (idPfxOf (W16 (uint.Z id)), 0) ==∗
      ∃ ρ : ReqNames,
        ⌜ρ.rd.raft = ⟨γ, [], W64 0⟩ ∧ ρ.rd.kv.st = γk.st ∧ ρ.rd.kv.c0 = γk.c0 ∧
          ρ.rd.kv.ch0 = γk.ch0 ∧ ρ.rd.kv.log0 = γk.log0 ∧
          ρ.rd.kv.cok = cok ∧ ρ.ids.issued = γk.ids.issued ∧ ρ.ids.cnt = cnt ∧
          ρ.ids.pfx = idPfxOf (W16 (uint.Z id)) ∧ ρ.rd.kv.cmp = γk.cmp ∧ ρ.rd.kv.rlog = γk.rlog ∧
          ρ.rd.kv.cret = γk.cret ∧ ρ.rd.kv.lg = γk.lg ∧ ρ.ids.wn = γk.ids.wn ∧ ρ.ids.fs = γk.ids.fs ∧ ρ.ids.inc = 0⌝ ∗
        kvInv ⟨γ, [], W64 0⟩ ρ.rd.kv ∗ idShare ρ.ids ∗ srvReadNamesFreshNK ρ.rd ∗
        idWaitTok ρ.ids := by
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
      ⟨γk.ids.issued, cnt, γsl, idPfxOf (W16 (uint.Z id)), γk.ids.wn, 0, γk.ids.fs⟩, γk.hist, γk.cmp, γk.rlog,
      γk.cret, γk.lg⟩⟩⟩
  isplitr
  · ipureintro
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  isplitr
  · dsimp only
    rw [kvInv_congr _ ⟨γk.st, γk.c0, γk.ch0, γk.log0, cok, γhi,
      ⟨γk.ids.issued, cnt, γsl, idPfxOf (W16 (uint.Z id)), γk.ids.wn, 0, γk.ids.fs⟩, γk.hist, γk.cmp, γk.rlog,
      γk.cret, γk.lg⟩ γk
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩]
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

#print axioms Perennial.EtcdGrove.newServerNames_alloc
#print axioms Perennial.EtcdGrove.srvClusterBoot_alloc
#print axioms Perennial.EtcdGrove.srvMemberBoot_alloc

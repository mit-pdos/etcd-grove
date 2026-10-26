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
      γk.ids.issued = γk'.ids.issued ∧ γk.ids.wn = γk'.ids.wn) :
    kvInv (GF := GF) γs γk = kvInv γs γk' := by
  obtain ⟨h1, h2, h3, h4, h6, h7⟩ := h
  unfold kvInv kvWork entryClaim idClaim kvModelSt kvLeases kvModel idRegd idWaitIs
  rw [h1, h2, h3, h4, h6, h7]

/-- The client's `etcdKV` reads only the state's variable. -/
theorem etcdKV_congr (γk γk' : KVNames) (h : γk.st = γk'.st) (σ : KVState) :
    etcdKV (GF := GF) γk σ = etcdKV γk' σ := by
  unfold etcdKV; rw [h]

/-- The proposals' mint reads only the claims' map. -/
theorem srvPropMint_congr (γs : ServerRaftNames) (γi γi' : IdNames) (h : γi.issued = γi'.issued) :
    srvPropMint (GF := GF) γs γi = srvPropMint γs γi' := by
  unfold srvPropMint idClaim; rw [h]

/-- **The standing update, as raft's**, from the pure facts of `srvRaftLogInv` only (as
`srvNoopAu_to_noopAu`, whose proof uses no more): usable inside raft's allocation continuation,
before raft's commit invariant exists. -/
theorem srvNoopAu_to_noopAu_of (γ : ServerRaftNames) (Hai0 : uint.Z γ.ai0 = γ.pre.length)
    (Hcc : srvCCPolicy γ) :
    ⊢ srvNoopAu (GF := GF) γ -∗ noopAu γ.raft := by
  iintro #Hau
  unfold noopAu
  iintro !>
  iauintro
  unfold atomic_acc
  iunfold srvNoopAu at Hau
  ihave Hacc := aupd_aacc $$ Hau
  unfold atomic_acc
  imod Hacc with Hacc
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at Hacc
  icases Hacc with ⟨%L, HL, Hcl⟩
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  imodintro
  iexists srvLogOf γ L
  iunfold srvRLog at HL
  iframe HL
  isplit
  · iintro HL
    icases Hcl with ⟨Habort, -⟩
    imod Habort $$ [HL] with -
    · iunfold srvRLog; iexact HL
    imodintro
    itrivial
  · iintro %e ⟨HL, #He, %Hidx⟩
    icases Hcl with ⟨-, Hcommit⟩
    ihave He := entDataIs_prop _ e none $$ He
    iunfold propDataIs at He
    icases He with (%Hn | %Hc)
    · imod Hcommit $$ %(EntryModel.ofM e) [HL] with -
      · isplitr
        · ipureintro
          refine ⟨Or.inl ?_, srvLogOf_index γ L e Hai0 Hidx⟩
          simp only [EntryModel.ofM]; exact Hn
        iunfold srvRLog
        rw [srvLogOf_snoc, EntryModel.toM_ofM]
        iexact HL
      imodintro
      itrivial
    · imod Hcommit $$ %(EntryModel.ofM e) [HL] with -
      · isplitr
        · ipureintro
          refine ⟨Or.inr ?_, srvLogOf_index γ L e Hai0 Hidx⟩
          simp only [EntryModel.ofM]; exact Hcc _ _ Hc.2.2
        iunfold srvRLog
        rw [srvLogOf_snoc, EntryModel.toM_ofM]
        iexact HL
      imodintro
      itrivial

/-- **What the servers' continuation of raft's allocation returns** (see the file header): the
cluster's KV names `γk` (the start values of a new cluster; the claims' names `ids`, the cluster's, D21e (A)), the KV invariant at raft's names
`⟨γ, [], 0⟩`, the client's `etcdKV` at the bootstrap log's model and raft's fresh-token
authorities. (Until stage M4 one server's read names, with its other rows.) -/
def srvBootOut (ids : IdNames) (bootLog : List EntryM) (γ : RaftNames) :
    IProp GF :=
  iprop(∃ γk : KVNames,
    ⌜γk.c0 = W64 0 ∧ γk.ch0 = apply.alarmChain false false false ∧ γk.log0 = [[], []] ∧
      γk.ids = ids⌝ ∗
    kvInv ⟨γ, [], W64 0⟩ γk ∗ etcdKV γk (kvModelSt γk (bootEntries bootLog)) ∗
    ghostMapAuth γ.reFresh 1 (∅ : GMap (List w8) Unit) ∗
    ghostMapAuth γ.reRdFresh 1 (∅ : GMap (List w8) Unit))

/-- **The servers' continuation of raft's allocation** (see the file header), for a bootstrap
log the conf-change policy `ccOk` admits, every admitted conf change of id `0` in the server's
form, one `applyConfChange` takes (`srvCCPolicy`'s; audit phase B3, 2026-10-18). -/
theorem srvBootClient (E : CoPset) (cfg : GSet w64) (ccOk : w32 → List w8 → Prop)
    (ps : List w64) (bootLog : List EntryM) (ids : IdNames)
    (hboot : BootLogOk ccOk ps bootLog)
    (hpol : ∀ ty d, ccOk ty d →
      ty = W32 1 ∧ isConfChangeEncoding d ∧ ccIdOf d = W64 0 ∧ ccBootOk cfg d) :
    ⊢ allocClientBoot (GF := GF) E cfg ccOk bootLog (srvBootOut ids bootLog) := by
  unfold allocClientBoot
  iintro %γ %Hγ #Hc HL Hf Hrf
  let γk0 : KVNames := ⟨0, W64 0, apply.alarmChain false false false, [[], []], 0, 0, ids⟩
  imod ghostVar_alloc (GF := GF) (kvModelSt γk0 (bootEntries bootLog)) with ⟨%γst, Hst⟩
  let γk : KVNames := { γk0 with st := γst }
  have hm : kvModelSt γk (bootEntries bootLog) = kvModelSt γk0 (bootEntries bootLog) := rfl
  let γs : ServerRaftNames := ⟨γ, [], W64 0⟩
  imod (kvInv_alloc_boot (GF := GF) γs γk ccOk ps bootLog E rfl rfl hboot
      (fun ty d h => ⟨(hpol ty d h).2.2.1, by rw [Hγ.1]; exact (hpol ty d h).2.2.2⟩)
      rfl rfl (by simp [γk, γk0]))
    $$ [HL] [Hst] with ⟨#Hkv, Hetcd⟩
  · iexact HL
  · rw [hm]; iexact Hst
  ihave #Hsn := kv_noop_au γs γk $$ Hkv
  ihave #Hnoop := srvNoopAu_to_noopAu_of γs rfl
    (by
      intro ty d h
      simp only [γs] at h
      rw [Hγ.2.2.1] at h
      have := hpol ty d h
      refine ⟨this.1, this.2.1, this.2.2.1, ?_⟩
      simp only [γs]; rw [Hγ.1]; exact this.2.2.2) $$ Hsn
  imodintro
  isplitl []
  · iexact Hnoop
  unfold srvBootOut
  iexists γk
  iframe Hkv Hetcd Hf Hrf
  ipureintro
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- **A new cluster's raft ghost state, for the servers** (`ownRaftGhost_alloc_boot` at
`srvBootClient`): raft's names `γ` with the commit invariant, the committed bootstrap log, each
node's ghost state at the bootstrap log's state, the servers' continuation's output
(`srvBootOut`) and raft's read credits. -/
theorem srvRaftBoot_alloc (E : CoPset) (cfg nodes : GSet w64) (ccOk : w32 → List w8 → Prop)
    (ps : List w64) (bootLog : List EntryM) (ids : IdNames)
    -- (2026-10-26, D22 J2) the members' snapshot directories (`RaftNames.reSnapLoc`)
    (sl : w64 → Option GName)
    (Hcne : cfg ≠ ∅) (Hnz : W64 0 ∉ nodes) (Hcfg : cfg = GMap.listToSet ps)
    (hboot : BootLogOk ccOk ps bootLog)
    (hpol : ∀ ty d, ccOk ty d →
      ty = W32 1 ∧ isConfChangeEncoding d ∧ ccIdOf d = W64 0 ∧ ccBootOk cfg d) :
    ⊢ |={E}=> ∃ γ : RaftNames,
        ⌜γ.reCfg = cfg ∧ γ.reDyn = none ∧ γ.reCCOk = ccOk ∧ γ.reBoot = bootLog ∧
          γ.reTracked = some cfg ∧ γ.reNoSnap = true ∧ γ.reNoXfer = true ∧ γ.reSnapLoc = sl⌝ ∗
        raftCommitInv (GF := GF) γ ∗ isCommitted γ bootLog ∗
        ([∗map] id ↦ _u ∈ toMap nodes, ownRaftGhost γ id (bootPState bootLog)) ∗
        srvBootOut ids bootLog γ ∗
        (rdCred γ (2 ^ 64 - 2) ∗ rdCredInv γ) := by
  -- (2026-10-19, D21 M3) in raft's no-snapshot mode; (D22 S-a) and its no-transfer mode
  iapply (ownRaftGhost_alloc_boot E cfg nodes ccOk ps bootLog (srvBootOut ids bootLog) true true
    sl Hcne Hnz Hcfg hboot)
  iapply srvBootClient E cfg ccOk ps bootLog ids hboot hpol

/-- A list whose image is without repeats is without repeats. -/
theorem nodup_of_map {α β : Type} (f : α → β) : ∀ {l : List α}, (l.map f).Nodup → l.Nodup
  | [], _ => List.nodup_nil
  | a :: l, h => by
    rw [List.map_cons, List.nodup_cons] at h
    exact List.nodup_cons.2 ⟨fun ha => h.1 (List.mem_map_of_mem ha), nodup_of_map f h.2⟩

/-- (2026-10-26, D22 J2, R-loc) **The members' snapshot directories, allocated empty**, before
raft's names (which name them, `RaftNames.reSnapLoc`): one ghost map `index ↦ ()` per member of
`ps` (distinct), each member's authority (what `NewServer`'s `snapDir_init` takes). -/
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

/-- `c` of raft's read credits for each member of `ps`, out of `n` (D21e (A): `c = 2 ^ 48`). -/
theorem rdCred_members (γ : RaftNames) (c : Nat) :
    ∀ (ps : List w64) (n : Nat), ps.length * c ≤ n →
      rdCred (GF := GF) γ n ⊢ [∗list] _id ∈ ps, rdCred γ c
  | [], _, _ => by
    iintro -
    iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
    itrivial
  | _ :: ps, n, h => by
    rw [List.length_cons, Nat.succ_mul] at h
    iintro H
    ihave H' : iprop(rdCred γ (c + (n - c))) $$ [H]
    · rw [show c + (n - c) = n by omega]
      iexact H
    icases (rdCred_split γ _ _).1 $$ H' with ⟨H1, H2⟩
    iapply BigSepL.bigSepL_cons.2
    iframe H1
    iapply (rdCred_members γ c ps (n - c) (by omega)) $$ H2

/-- **A new cluster's resources, for the servers** (D21e (A), stage M4; see the file header):
raft's ghost state (`srvRaftBoot_alloc`), the cluster's claims at the claimers' facts `Φs` (the
caller's: a member's at its prefix), with the reserved id `0`, the proposals' mint, the read
contexts, and each member's share: its prefix's entry of the claims and `2 ^ 48` of raft's read
credits. The pure premise (D21e (A), `issues/etcd-request-id-member-prefix.md`): the members' ids'
16 low bits are distinct and not `0`. -/
theorem srvClusterBoot_alloc (cfg nodes : GSet w64) (ccOk : w32 → List w8 → Prop)
    (ps : List w64) (bootLog : List EntryM)
    (Φs : w64 → w64 → List w8 → GName → IProp GF)
    (Hcne : cfg ≠ ∅) (Hnz : W64 0 ∉ nodes) (Hcfg : cfg = GMap.listToSet ps)
    (hboot : BootLogOk ccOk ps bootLog)
    (hpol : ∀ ty d, ccOk ty d →
      ty = W32 1 ∧ isConfChangeEncoding d ∧ ccIdOf d = W64 0 ∧ ccBootOk cfg d)
    (Hpd : (ps.map (fun id => uint.Z id % 2 ^ 16)).Nodup)
    (Hp0 : ∀ id ∈ ps, uint.Z id % 2 ^ 16 ≠ 0) :
    ⊢ |={⊤}=> ∃ (γ : RaftNames) (issued cnt : GName) (γk : KVNames),
        ⌜γ.reCfg = cfg ∧ γ.reDyn = none ∧ γ.reCCOk = ccOk ∧ γ.reBoot = bootLog ∧
          γ.reNoSnap = true ∧ γ.reNoXfer = true ∧
          γk.c0 = W64 0 ∧ γk.ch0 = apply.alarmChain false false false ∧ γk.log0 = [[], []] ∧
          γk.ids.issued = issued⌝ ∗
        raftCommitInv (GF := GF) γ ∗ isCommitted γ bootLog ∗ rdCredInv γ ∗
        ([∗map] id ↦ _u ∈ toMap nodes, ownRaftGhost γ id (bootPState bootLog)) ∗
        kvInv ⟨γ, [], W64 0⟩ γk ∗ etcdKV γk (kvModelSt γk (bootEntries bootLog)) ∗
        idClusterInv issued cnt Φs ∗ (W64 0) ↪[issued]□ (none : Option (List w8 × GName)) ∗
        srvPropMint ⟨γ, [], W64 0⟩ γk.ids ∗ srvRdCtxInv ⟨γ, [], W64 0⟩ issued ∗
        ([∗list] id ∈ ps, (idPfxOf (W16 (uint.Z id)) ↪[cnt] ([] : List w64) ∗
          rdCred γ (2 ^ 48) ∗
          -- (2026-10-26, D22 J2) and its snapshot directory, empty (`RaftNames.reSnapLoc`)
          ∃ γd : GName, ⌜γ.reSnapLoc id = some γd⌝ ∗ ghostMapAuth γd 1 (∅ : GMap w64 Unit))) ∗
        -- (linkv-txn stage B1, 2026-10-20) each member's entry of the registries' map
        [∗list] id ∈ ps, idWaitTokAt γk.ids.wn (idPfxOf (W16 (uint.Z id))) := by
  obtain ⟨Hnd, Hok, Hlen⟩ := idPfxsOf_ok ps Hpd Hp0
  istart
  imod (idCluster_alloc (GF := GF) (idPfxsOf ps) Φs ⊤ Hnd Hok) with ⟨%issued, %cnt, #Hcl, #H0, Hps⟩
  imod (idWait_alloc_list (GF := GF) (idPfxsOf ps) Hnd) with ⟨%wn, Hwns⟩
  imod (snapDirs_alloc (GF := GF) ps (nodup_of_map _ Hpd)) with ⟨%sl, Hsd⟩
  imod (srvRaftBoot_alloc (GF := GF) ⊤ cfg nodes ccOk ps bootLog ⟨issued, cnt, 0, 0, wn⟩ sl
      Hcne Hnz Hcfg hboot hpol)
    with ⟨%γ, %Hγ, #Hcinv, #Hcomm, Hghosts, Hout, HrdC, #HrdI⟩
  iunfold srvBootOut at Hout
  icases Hout with ⟨%γk, %Hk, #Hkv, Hetcd, Hf, Hrf⟩
  obtain ⟨hc0, hch, hlog, hids⟩ := Hk
  imod (srvPropMint_alloc ⟨γ, [], W64 0⟩ γk.ids ⊤) $$ Hf with #Hpm
  imod (srvRdCtxInv_alloc ⟨γ, [], W64 0⟩ issued ⊤) $$ Hrf with #Hrc
  ihave Hcr := rdCred_members γ (2 ^ 48) ps (2 ^ 64 - 2) (by
    have := Nat.mul_le_mul_right (2 ^ 48) Hlen
    omega) $$ HrdC
  imodintro
  iexists γ, issued, cnt, γk
  iframe Hcinv Hcomm HrdI Hghosts Hkv Hetcd Hcl H0 Hpm Hrc
  isplitr
  · ipureintro
    obtain ⟨h1, h2, h3, h4, -, h5, h6, -⟩ := Hγ
    exact ⟨h1, h2, h3, h4, h5, h6, hc0, hch, hlog, by rw [hids]⟩
  isplitl [Hps Hcr Hsd]
  · iapply (BigSepL.bigSepL_sep_eqv (PROP := IProp GF)).2
    ihave Hbc : iprop([∗list] id ∈ ps, (rdCred γ (2 ^ 48) ∗
        ∃ γd : GName, ⌜γ.reSnapLoc id = some γd⌝ ∗ ghostMapAuth (GF := GF) γd 1 (∅ : GMap w64 Unit)))
      $$ [Hcr Hsd]
    · iapply (BigSepL.bigSepL_sep_eqv (PROP := IProp GF)).2
      iframe Hcr
      rw [Hγ.2.2.2.2.2.2.2]
      iexact Hsd
    iframe Hbc
    have hm : ([∗list] p ∈ idPfxsOf ps, p ↪[cnt] ([] : List w64)) =
        ([∗list] id ∈ ps, (idPfxOf (W16 (uint.Z id)) ↪[cnt] ([] : List w64) : IProp GF)) := by
      unfold idPfxsOf; rw [BigSepL.bigSepL_map]
    rw [← hm]
    iexact Hps
  have hw : γk.ids.wn = wn := by rw [hids]
  rw [hw]
  have hm : ([∗list] p ∈ idPfxsOf ps, idWaitTokAt (GF := GF) wn p) =
      ([∗list] id ∈ ps, idWaitTokAt (GF := GF) wn (idPfxOf (W16 (uint.Z id)))) := by
    unfold idPfxsOf; rw [BigSepL.bigSepL_map]
  rw [← hm]
  iexact Hwns

/-- **A member's names and share** (D21e (A), stage M4; see the file header): for the member
`id` of a cluster allocated by `srvClusterBoot_alloc` (its KV names `γk`, its claims' names), the
request names `ρ`: its read names at the cluster's KV names but for its own applied height and the
certificate map `cok` (the member's store's), its id names (the cluster's claims, its slots, its
prefix); with its read names' fresh rows (`srvReadNamesFreshNK`), the KV invariant at its names
(`kvInv_congr`) and its share of the claims (`idShare`, from its prefix's entry). -/
theorem srvMemberBoot_alloc (γ : RaftNames) (cnt : GName) (γk : KVNames) (id : w64)
    (cok : GName) :
    ⊢ kvInv (GF := GF) ⟨γ, [], W64 0⟩ γk -∗
      idPfxOf (W16 (uint.Z id)) ↪[cnt] ([] : List w64) -∗
      idWaitTokAt γk.ids.wn (idPfxOf (W16 (uint.Z id))) ==∗
      ∃ ρ : ReqNames,
        ⌜ρ.rd.raft = ⟨γ, [], W64 0⟩ ∧ ρ.rd.kv.st = γk.st ∧ ρ.rd.kv.c0 = γk.c0 ∧
          ρ.rd.kv.ch0 = γk.ch0 ∧ ρ.rd.kv.log0 = γk.log0 ∧
          ρ.rd.kv.cok = cok ∧ ρ.ids.issued = γk.ids.issued ∧ ρ.ids.cnt = cnt ∧
          ρ.ids.pfx = idPfxOf (W16 (uint.Z id))⌝ ∗
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
      ⟨γk.ids.issued, cnt, γsl, idPfxOf (W16 (uint.Z id)), γk.ids.wn⟩⟩⟩⟩
  isplitr
  · ipureintro
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  isplitr
  · dsimp only
    rw [kvInv_congr _ ⟨γk.st, γk.c0, γk.ch0, γk.log0, cok, γhi,
      ⟨γk.ids.issued, cnt, γsl, idPfxOf (W16 (uint.Z id)), γk.ids.wn⟩⟩ γk
      ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩]
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
#print axioms Perennial.EtcdGrove.srvRaftBoot_alloc
#print axioms Perennial.EtcdGrove.srvClusterBoot_alloc
#print axioms Perennial.EtcdGrove.srvMemberBoot_alloc

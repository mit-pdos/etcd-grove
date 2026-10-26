/-
**The ghost allocations `NewServer.specM true` takes** (the auth plan's E2z, 2026-10-26;
`notes/decisions.md`, "E2z of the auth plan"): `NewServerAlloc.lean`'s, with the mode-`on` KV
invariant (`kvInvOn`, E2q) at the start chain with auth on, so a caller of `server_new_auth_on`
can build its precondition. The cluster's raft ghost state with the servers' continuation
(`srvBootClientOn`, `srvRaftBootOn_alloc`: the KV invariant allocated at the bootstrap log by
`kvInvOn_alloc_boot`, raft's standing update from it by `kv_noop_au_on`), the cluster's resources
(`srvClusterBootOn_alloc`) and a member's names (`srvMemberBootOn_alloc`), each the mode-off one's
with `kvInv` replaced by `kvInvOn _ _ srvAuthSt0` and the start chain `alarmChain true false false`.

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

section pure
variable [ext : FfiSyntax]

/-- **Raft's own entries keep the mode-`on` model's state** (an empty normal entry or a conf
change: neither is a normal entry with data, so neither is decoded). -/
theorem kvEntryOn_noop (cfg : GSet w64) (c₀ : w64) (ch : apply.Chain)
    (s : auth.AuthState × mvcc.Log) (e : EntryModel) (h : srvNoopEntry cfg e) :
    kvEntryOn c₀ ch s e = s := by
  have hk : kvEntry c₀ ch s.2 e = s.2 := by
    apply kvEntry_nonwrite
    rcases h with ⟨-, hd⟩ | ⟨ht, -⟩
    · left; exact hd
    · right; left; rw [ht]; decide
  have hn : ¬ (e.typ = W32 0 ∧ e.data ≠ []) := by
    rintro ⟨ht, hd⟩
    rcases h with ⟨-, hd'⟩ | ⟨ht', -⟩
    · exact hd hd'
    · rw [ht'] at ht; exact absurd ht (by decide)
  unfold kvEntryOn
  simp only [hn, ↓reduceIte, hk]

/-- **Raft's own entries meet the committer's obligation** in the mode `on`, vacuously: both
`plainEntryOn` and `entryDetOn` ask of normal entries with data only. -/
theorem commitOkOn_noop (cfg : GSet w64) (c₀ : w64) (ch : apply.Chain)
    (s₀ : auth.AuthState × mvcc.Log) (L : List EntryModel) (e : EntryModel)
    (h : srvNoopEntry cfg e) : commitOkOn c₀ ch s₀ L e := by
  have hn : e.typ = W32 0 → e.data ≠ [] → False := by
    intro ht hd
    rcases h with ⟨-, hd'⟩ | ⟨ht', -⟩
    · exact hd hd'
    · rw [ht'] at ht; exact absurd ht (by decide)
  exact ⟨fun ht hd => absurd (hn ht hd) id, fun ht hd => absurd (hn ht hd) id⟩

end pure

section alloc
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The standing update for raft's own entries, from the mode-`on` KV invariant** (`kv_noop_au`'s
counterpart): an empty entry or a conf change keeps the mode-`on` model's state
(`kvEntryOn_noop`) and meets the committer's obligation (`commitOkOn_noop`). -/
theorem kv_noop_au_on (γ : ServerRaftNames) (γk : KVNames) (st₀ : auth.AuthState) :
    ⊢ kvInvOn (GF := GF) γ γk st₀ -∗ srvNoopAu γ := by
  have Hdisj := kvN_raftN
  iintro #Hinv
  unfold srvNoopAu
  iintro !>
  iauintro
  unfold atomic_acc
  iunfold kvInvOn at Hinv
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%L, HL, Hσ, %Hok, #Hw⟩
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
  iintro Hmask
  iexists L
  iframe HL
  isplit
  · iintro HL
    imod Hmask with -
    imod Hclose $$ [HL Hσ] with -
    · inext; iexists L; iframe HL Hσ Hw; ipureintro; exact Hok
    imodintro
    itrivial
  · iintro %e ⟨%He, HL⟩
    imod Hmask with -
    obtain ⟨He, hidx⟩ := He
    have hidx' : srvIdxOkW γ.ai0 (L ++ [e]) := by
      refine srvIdxOkW_snoc γ.ai0 L e Hok.2.2.1 hidx ?_
      rcases He with h | h
      · left; exact h.1
      · right; exact ⟨h.1, h.2.1⟩
    have hent : kvModelOn γk st₀ (L ++ [e]) = kvModelOn γk st₀ L := by
      rw [kvModelOn_snoc, kvEntryOn_noop γ.raft.reCfg _ _ _ e He]
      rfl
    ihave #Hnc := noop_claim (GF := GF) γk.ids γ.raft.reCfg e He
    ihave #Hw' := kvWorkOn_snoc γ.raft.reCfg γk L e
      (entryShapeOn_of_entryShape e (noop_shape γ.raft.reCfg e He))
      (noop_cc γ.raft.reCfg e He) $$ Hw Hnc
    imod Hclose $$ [HL Hσ] with -
    · inext
      iexists L ++ [e]
      rw [hent]
      iframe HL Hσ Hw'
      ipureintro
      exact kvInvOn_facts_snoc γ γk st₀ L e Hok hidx'
        (commitOkOn_noop γ.raft.reCfg _ _ _ L e He)
    imodintro
    itrivial

/-- **What the servers' continuation of raft's allocation returns in the mode `on`**
(`srvBootOut`'s): the cluster's KV names with the start chain with auth on, the mode-`on` KV
invariant from `srvAuthSt0` and the client's `etcdKV` at the bootstrap log's mode-`on` model. -/
def srvBootOutOn (ids : IdNames) (bootLog : List EntryM) (γ : RaftNames) :
    IProp GF :=
  iprop(∃ γk : KVNames,
    ⌜γk.c0 = W64 0 ∧ γk.ch0 = apply.alarmChain true false false ∧ γk.log0 = [[], []] ∧
      γk.ids = ids⌝ ∗
    kvInvOn ⟨γ, [], W64 0⟩ γk srvAuthSt0 ∗
    etcdKV γk (kvStateOf (kvModelOn γk srvAuthSt0 (bootEntries bootLog))) ∗
    ghostMapAuth γ.reFresh 1 (∅ : GMap (List w8) Unit) ∗
    ghostMapAuth γ.reRdFresh 1 (∅ : GMap (List w8) Unit))

/-- **The servers' continuation of raft's allocation in the mode `on`** (`srvBootClient`'s). -/
theorem srvBootClientOn (E : CoPset) (cfg : GSet w64) (ccOk : w32 → List w8 → Prop)
    (ps : List w64) (bootLog : List EntryM) (ids : IdNames)
    (hboot : BootLogOk ccOk ps bootLog)
    (hpol : ∀ ty d, ccOk ty d →
      ty = W32 1 ∧ isConfChangeEncoding d ∧ ccIdOf d = W64 0 ∧ ccBootOk cfg d) :
    ⊢ allocClientBoot (GF := GF) E cfg ccOk bootLog (srvBootOutOn ids bootLog) := by
  unfold allocClientBoot
  iintro %γ %Hγ #Hc HL Hf Hrf
  let γk0 : KVNames := ⟨0, W64 0, apply.alarmChain true false false, [[], []], 0, 0, ids⟩
  imod ghostVar_alloc (GF := GF) (kvStateOf (kvModelOn γk0 srvAuthSt0 (bootEntries bootLog)))
    with ⟨%γst, Hst⟩
  let γk : KVNames := { γk0 with st := γst }
  have hm : kvModelOn γk srvAuthSt0 (bootEntries bootLog) =
      kvModelOn γk0 srvAuthSt0 (bootEntries bootLog) := rfl
  let γs : ServerRaftNames := ⟨γ, [], W64 0⟩
  imod (kvInvOn_alloc_boot (GF := GF) γs γk srvAuthSt0 ccOk ps bootLog E rfl rfl hboot
      (fun ty d h => ⟨(hpol ty d h).2.2.1, by rw [Hγ.1]; exact (hpol ty d h).2.2.2⟩)
      rfl rfl (by simp [γk, γk0]))
    $$ [HL] [Hst] with ⟨#Hkv, Hetcd⟩
  · iexact HL
  · rw [hm]; iexact Hst
  ihave #Hsn := kv_noop_au_on γs γk srvAuthSt0 $$ Hkv
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
  unfold srvBootOutOn
  iexists γk
  iframe Hkv Hetcd Hf Hrf
  ipureintro
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- **A new cluster's raft ghost state, for the servers, in the mode `on`**
(`srvRaftBoot_alloc`'s). -/
theorem srvRaftBootOn_alloc (E : CoPset) (cfg nodes : GSet w64) (ccOk : w32 → List w8 → Prop)
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
        srvBootOutOn ids bootLog γ ∗
        (rdCred γ (2 ^ 64 - 2) ∗ rdCredInv γ) := by
  iapply (ownRaftGhost_alloc_boot E cfg nodes ccOk ps bootLog (srvBootOutOn ids bootLog) true true
    sl Hcne Hnz Hcfg hboot)
  iapply srvBootClientOn E cfg ccOk ps bootLog ids hboot hpol

/-- **A new cluster's resources, for the servers, in the mode `on`** (`srvClusterBoot_alloc`'s:
the same, with the mode-`on` KV invariant from `srvAuthSt0` and the start chain with auth on). -/
theorem srvClusterBootOn_alloc (cfg nodes : GSet w64) (ccOk : w32 → List w8 → Prop)
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
          γk.c0 = W64 0 ∧ γk.ch0 = apply.alarmChain true false false ∧ γk.log0 = [[], []] ∧
          γk.ids.issued = issued⌝ ∗
        raftCommitInv (GF := GF) γ ∗ isCommitted γ bootLog ∗ rdCredInv γ ∗
        ([∗map] id ↦ _u ∈ toMap nodes, ownRaftGhost γ id (bootPState bootLog)) ∗
        kvInvOn ⟨γ, [], W64 0⟩ γk srvAuthSt0 ∗
        etcdKV γk (kvStateOf (kvModelOn γk srvAuthSt0 (bootEntries bootLog))) ∗
        idClusterInv issued cnt Φs ∗ (W64 0) ↪[issued]□ (none : Option (List w8 × GName)) ∗
        srvPropMint ⟨γ, [], W64 0⟩ γk.ids ∗ srvRdCtxInv ⟨γ, [], W64 0⟩ issued ∗
        ([∗list] id ∈ ps, (idPfxOf (W16 (uint.Z id)) ↪[cnt] ([] : List w64) ∗
          rdCred γ (2 ^ 48) ∗
          -- (2026-10-26, D22 J2) and its snapshot directory, empty (`RaftNames.reSnapLoc`)
          ∃ γd : GName, ⌜γ.reSnapLoc id = some γd⌝ ∗ ghostMapAuth γd 1 (∅ : GMap w64 Unit))) ∗
        [∗list] id ∈ ps, idWaitTokAt γk.ids.wn (idPfxOf (W16 (uint.Z id))) := by
  obtain ⟨Hnd, Hok, Hlen⟩ := idPfxsOf_ok ps Hpd Hp0
  istart
  imod (idCluster_alloc (GF := GF) (idPfxsOf ps) Φs ⊤ Hnd Hok) with ⟨%issued, %cnt, #Hcl, #H0, Hps⟩
  imod (idWait_alloc_list (GF := GF) (idPfxsOf ps) Hnd) with ⟨%wn, Hwns⟩
  imod (snapDirs_alloc (GF := GF) ps (nodup_of_map _ Hpd)) with ⟨%sl, Hsd⟩
  imod (srvRaftBootOn_alloc (GF := GF) ⊤ cfg nodes ccOk ps bootLog ⟨issued, cnt, 0, 0, wn⟩ sl
      Hcne Hnz Hcfg hboot hpol)
    with ⟨%γ, %Hγ, #Hcinv, #Hcomm, Hghosts, Hout, HrdC, #HrdI⟩
  iunfold srvBootOutOn at Hout
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

/-- **The mode-`on` KV invariant reads only the cluster's KV names** (`kvInv_congr`'s). -/
theorem kvInvOn_congr (γs : ServerRaftNames) (γk γk' : KVNames) (st₀ : auth.AuthState)
    (h : γk.st = γk'.st ∧ γk.c0 = γk'.c0 ∧ γk.ch0 = γk'.ch0 ∧ γk.log0 = γk'.log0 ∧
      γk.ids.issued = γk'.ids.issued ∧ γk.ids.wn = γk'.ids.wn) :
    kvInvOn (GF := GF) γs γk st₀ = kvInvOn γs γk' st₀ := by
  obtain ⟨h1, h2, h3, h4, h6, h7⟩ := h
  unfold kvInvOn kvWorkOn entryClaim idClaim kvModelOn idRegd idWaitIs
  rw [h1, h2, h3, h4, h6, h7]

/-- **A member's names and share in the mode `on`** (`srvMemberBoot_alloc`'s): the mode-`on` KV
invariant at its names, as `NewServer.specM true`'s `kvInvM true`. -/
theorem srvMemberBootOn_alloc (γ : RaftNames) (cnt : GName) (γk : KVNames) (id : w64)
    (cok : GName) :
    ⊢ kvInvOn (GF := GF) ⟨γ, [], W64 0⟩ γk srvAuthSt0 -∗
      idPfxOf (W16 (uint.Z id)) ↪[cnt] ([] : List w64) -∗
      idWaitTokAt γk.ids.wn (idPfxOf (W16 (uint.Z id))) ==∗
      ∃ ρ : ReqNames,
        ⌜ρ.rd.raft = ⟨γ, [], W64 0⟩ ∧ ρ.rd.kv.st = γk.st ∧ ρ.rd.kv.c0 = γk.c0 ∧
          ρ.rd.kv.ch0 = γk.ch0 ∧ ρ.rd.kv.log0 = γk.log0 ∧
          ρ.rd.kv.cok = cok ∧ ρ.ids.issued = γk.ids.issued ∧ ρ.ids.cnt = cnt ∧
          ρ.ids.pfx = idPfxOf (W16 (uint.Z id))⌝ ∗
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
      ⟨γk.ids.issued, cnt, γsl, idPfxOf (W16 (uint.Z id)), γk.ids.wn⟩⟩⟩⟩
  isplitr
  · ipureintro
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  isplitr
  · dsimp only
    rw [kvInvM_true, kvInvOn_congr _ ⟨γk.st, γk.c0, γk.ch0, γk.log0, cok, γhi,
      ⟨γk.ids.issued, cnt, γsl, idPfxOf (W16 (uint.Z id)), γk.ids.wn⟩⟩ γk srvAuthSt0
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

#print axioms Perennial.EtcdGrove.kv_noop_au_on
#print axioms Perennial.EtcdGrove.srvClusterBootOn_alloc
#print axioms Perennial.EtcdGrove.srvMemberBootOn_alloc

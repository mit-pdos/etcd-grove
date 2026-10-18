/-
**The ghost allocations `NewServer.spec` takes** (item 9, point 7, 2026-10-18): what the
adequacy example's `Main` allocates before calling `NewServer`. Lean-first (no Rocq counterpart).

* `newServerNames_alloc`: the names chosen before the call (D13a) other than raft's and the read
  names: the id generator's (`idNamesFresh`), the store's index names (`mvcc.idxFresh`), its
  certificate map and the revisions' map, all fresh.
* `srvBootClient` / `srvRaftBoot_alloc`: **a new cluster's raft ghost state, for the server**:
  `ownRaftGhost_alloc_boot` with the server's continuation, which allocates the read names
  (`srvReadNamesFresh_alloc`, at the raft names `⟨γ, [], 0⟩`) and the KV invariant at the
  bootstrap log (`kvInv_alloc_boot`, from the client's half of raft's committed log `rLog γ
  bootLog`) inside the continuation, and builds raft's standing update `noopAu` from it
  (`kv_noop_au`, `srvNoopAu_to_noopAu_of`). Its output (`srvBootOut`): the read names' other
  rows (`srvReadNamesFreshNK`), `kvInv`, the client's `etcdKV` at the bootstrap log's model and
  the fresh-token authorities.

**Not yet `NewServer.spec`'s premises** (`notes/STATUS.md`, "Item 9, point 7"; `notes/decisions.md`,
D19g): `NewServer.spec` takes `rLog γ bootLog` owned and allocates `kvInv` itself, but raft's
allocation needs `noopAu γ` from its continuation, which only an invariant holding `rLog` (the
KV invariant) gives: no caller can meet both. The allocation here is the achievable one;
`NewServer.spec` is to take `kvInv ρ.rd.raft ρ.rd.kv` and `srvReadNamesFreshNK ρ.rd` in place of
`rLog γ bootLog` and `srvReadNamesFresh`, its post no longer the client's `etcdKV` (which this
allocation gives).
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The fresh names chosen before `NewServer`** (D13a) but raft's and the read names: the id
generator's, the store's index names, its certificate map and the revisions' map. -/
theorem newServerNames_alloc :
    ⊢ |==> ∃ (ids : IdNames) (idx : mvcc.IdxNames) (cok rev : GName),
      idNamesFresh (GF := GF) ids ∗ mvcc.idxFresh idx ∗
      ghostMapAuth cok 1 (∅ : GMap w64 mvcc.Log) ∗ ghostMapAuth rev 1 (∅ : GMap w64 Unit) := by
  istart
  imod idNamesFresh_alloc (GF := GF) with ⟨%ids, Hids⟩
  imod mvcc.idxFresh_alloc (GF := GF) with ⟨%idx, Hidx⟩
  imod ghost_map_alloc_empty (GF := GF) (K := w64) (V := mvcc.Log) with ⟨%cok, Hcok⟩
  imod ghost_map_alloc_empty (GF := GF) (K := w64) (V := Unit) with ⟨%rev, Hrev⟩
  imodintro
  iexists ids, idx, cok, rev
  iframe

/-- The read names' fresh rows but the KV state's variable (which the KV invariant takes). -/
def srvReadNamesFreshNK (γr : ReadNames) : IProp GF :=
  iprop(monoNatAuthOwn γr.applied 1 0 ∗ monoNatAuthOwn γr.committed 1 0 ∗
    (∃ x : Loc × NeedNames, ghostVar γr.notifier 1 x) ∗
    ghostMapAuth γr.logs 1 (∅ : GMap w64 mvcc.Log) ∗ ghostVar γr.pend 1 false ∗
    ghostVar γr.kv.hi 1 γr.kv.log0.length)

theorem srvReadNamesFresh_split (γr : ReadNames) (σ : KVState) :
    srvReadNamesFresh (GF := GF) γr σ ⊢ srvReadNamesFreshNK γr ∗ ghostVar γr.kv.st 1 σ := by
  unfold srvReadNamesFresh srvReadNamesFreshNK
  iintro ⟨Ha, Hc, Hn, Hl, Hp, Hs, Hh⟩
  iframe

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
    iunfold entDataIs at He
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

/-- **What the server's continuation of raft's allocation returns** (see the file header): read
names at the raft names `⟨γ, [], 0⟩` and the KV start values of a new cluster, the KV invariant,
the client's `etcdKV` at the bootstrap log's model, the read names' other rows and raft's
fresh-token authorities. -/
def srvBootOut (ids : IdNames) (cok : GName) (bootLog : List EntryM) (γ : RaftNames) : IProp GF :=
  iprop(∃ γr : ReadNames,
    ⌜γr.raft = ⟨γ, [], W64 0⟩ ∧ γr.kv.c0 = W64 0 ∧
      γr.kv.ch0 = apply.alarmChain false false false ∧ γr.kv.log0 = [[], []] ∧
      γr.kv.cok = cok ∧ γr.kv.ids = ids⌝ ∗
    kvInv γr.raft γr.kv ∗ etcdKV γr.kv (kvStateOf (kvModel γr.kv (bootEntries bootLog))) ∗
    srvReadNamesFreshNK γr ∗
    ghostMapAuth γ.reFresh 1 (∅ : GMap (List w8) Unit) ∗
    ghostMapAuth γ.reRdFresh 1 (∅ : GMap (List w8) Unit))

/-- **The server's continuation of raft's allocation** (see the file header), for a bootstrap
log the conf-change policy `ccOk` admits, every admitted conf change of id `0` in the server's
form (`srvCCPolicy`'s). -/
theorem srvBootClient (E : CoPset) (cfg : GSet w64) (ccOk : w32 → List w8 → Prop)
    (ps : List w64) (bootLog : List EntryM) (ids : IdNames) (cok : GName)
    (hboot : BootLogOk ccOk ps bootLog)
    (hpol : ∀ ty d, ccOk ty d → ty = W32 1 ∧ isConfChangeEncoding d ∧ ccIdOf d = W64 0) :
    ⊢ allocClientBoot (GF := GF) E cfg ccOk bootLog (srvBootOut ids cok bootLog) := by
  unfold allocClientBoot
  iintro %γ %Hγ #Hc HL Hf Hrf
  imod (srvReadNamesFresh_alloc (GF := GF) ⟨γ, [], W64 0⟩ (W64 0)
      (apply.alarmChain false false false) [[], []] cok ids
      (kvStateOf (kvRaftOf (W64 0) (apply.alarmChain false false false) [[], []]
        (bootEntries bootLog)))) with ⟨%γr, %Hr, Hrd⟩
  obtain ⟨hraft, hc0, hch, hlog, hcok, hids⟩ := Hr
  icases srvReadNamesFresh_split γr _ $$ Hrd with ⟨Hnk, Hst⟩
  have hm : kvModel γr.kv (bootEntries bootLog) =
      kvRaftOf (W64 0) (apply.alarmChain false false false) [[], []] (bootEntries bootLog) := by
    unfold kvModel; rw [hc0, hch, hlog]
  imod (kvInv_alloc_boot (GF := GF) γr.raft γr.kv ccOk ps bootLog E (by rw [hraft])
      (by rw [hraft]) hboot (fun ty d h => (hpol ty d h).2.2) hc0 hch (by rw [hlog]; simp))
    $$ [HL] [Hst] with ⟨#Hkv, Hetcd⟩
  · rw [hraft]; iexact HL
  · rw [hm]; iexact Hst
  ihave #Hsn := kv_noop_au γr.raft γr.kv $$ Hkv
  ihave #Hnoop := srvNoopAu_to_noopAu_of γr.raft (by rw [hraft]; rfl)
    (by
      intro ty d h
      rw [hraft] at h
      simp only at h
      rw [Hγ.2.2.1] at h
      exact hpol ty d h) $$ Hsn
  imodintro
  isplitl []
  · rw [hraft]; iexact Hnoop
  unfold srvBootOut
  iexists γr
  iframe Hkv Hetcd Hnk Hf Hrf
  ipureintro
  exact ⟨hraft, hc0, hch, hlog, hcok, hids⟩

/-- **A new cluster's raft ghost state, for the server** (`ownRaftGhost_alloc_boot` at
`srvBootClient`): raft's names `γ` with the commit invariant, the committed bootstrap log, each
node's ghost state at the bootstrap log's state, the server's continuation's output
(`srvBootOut`) and raft's read credits. -/
theorem srvRaftBoot_alloc (E : CoPset) (cfg nodes : GSet w64) (ccOk : w32 → List w8 → Prop)
    (ps : List w64) (bootLog : List EntryM) (ids : IdNames) (cok : GName)
    (Hcne : cfg ≠ ∅) (Hnz : W64 0 ∉ nodes) (Hcfg : cfg = GMap.listToSet ps)
    (hboot : BootLogOk ccOk ps bootLog)
    (hpol : ∀ ty d, ccOk ty d → ty = W32 1 ∧ isConfChangeEncoding d ∧ ccIdOf d = W64 0) :
    ⊢ |={E}=> ∃ γ : RaftNames,
        ⌜γ.reCfg = cfg ∧ γ.reDyn = none ∧ γ.reCCOk = ccOk ∧ γ.reBoot = bootLog⌝ ∗
        raftCommitInv (GF := GF) γ ∗ isCommitted γ bootLog ∗
        ([∗map] id ↦ _u ∈ toMap nodes, ownRaftGhost γ id (bootPState bootLog)) ∗
        srvBootOut ids cok bootLog γ ∗
        (rdCred γ (2 ^ 64 - 2) ∗ rdCredInv γ) := by
  iapply (ownRaftGhost_alloc_boot E cfg nodes ccOk ps bootLog (srvBootOut ids cok bootLog)
    Hcne Hnz Hcfg hboot)
  iapply srvBootClient E cfg ccOk ps bootLog ids cok hboot hpol

end alloc

end EtcdGrove
end Perennial

#print axioms Perennial.EtcdGrove.newServerNames_alloc
#print axioms Perennial.EtcdGrove.srvRaftBoot_alloc

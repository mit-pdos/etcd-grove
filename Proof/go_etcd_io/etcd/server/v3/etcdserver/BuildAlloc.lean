/-
**The server's construction: the ghost allocations** (unit N2 of the server-construction unit;
statements placed at stage N0, 2026-10-16; D13 and D13a-d, `notes/decisions.md`). Lean-first (no
Rocq counterpart). The statements are the interface `NewServer`'s proof (unit N1) uses; their
proofs are unit N2's.

* `srvReadNamesFresh_alloc`: the read names, fresh (`InvBuild.lean`), chosen before
  `newRaftNode` (D13a), at the given raft names and KV start values.
* `kvInv_alloc_boot`: the KV invariant at the bootstrap log, from the client's half of raft's
  committed log (`allocClientBoot`'s continuation output `rLog γ bootLog`), and the client's
  `etcdKV` at the bootstrap log's model.
* `kvCertInv_alloc`: the certificates' invariant, from the store's certificate authority (which
  `mvcc.New` returns, D13a) and the certified length's half.
* `srvIndices_alloc`: the applied and committed indices' invariants and the term's, at index `0`.
* `srvMintInv_alloc`: the mints, from `allocClientBoot`'s fresh-token authorities and raft's read
  credits.
* `consInv_alloc` (in `InvApply.lean` since D22 receiver epochs S7f, 2026-10-23): the apply
  protocol's invariant over a fresh consistent index (for whoever discharges `bootstrap`'s contract,
  `InvBoot.lean`: the backend's batch lock's resource names the protocol's names, so they exist
  before the backend does).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvBuild

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

/-- A ghost variable's whole as its two halves. -/
theorem buildGhostVarHalves {A : Type} [Pos.Countable A] (γ : GName) (a : A) :
    ghostVar (GF := GF) γ 1 a ⊢ ghostVar γ (1 : Qp).half a ∗ ghostVar γ (1 : Qp).half a := by
  have h := ghostVar_split (GF := GF) γ a (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at h
  exact wand_entails h

/-- A mono nat's whole authority as its two halves. -/
theorem buildMonoNatHalves (γ : GName) (n : Nat) :
    monoNatAuthOwn (GF := GF) γ 1 n ⊢
      monoNatAuthOwn γ (1 : Qp).half n ∗ monoNatAuthOwn γ (1 : Qp).half n := by
  have hf := (monoNatAuthOwn_fractional (GF := GF) γ n).fractional (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at hf
  exact hf.1

/-- Conf-change entries claim nothing (D19c). -/
theorem entryClaims_conf (γi : IdNames) :
    ∀ l : List EntryModel, (∀ m ∈ l, m.typ ≠ W32 0) →
      ⊢ [∗list] m ∈ l, entryClaim (GF := GF) γi m
  | [], _ => by
    iapply BigSepL.bigSepL_nil.2
    itrivial
  | m :: l, h => by
    iapply BigSepL.bigSepL_cons.2
    isplitr
    · iunfold entryClaim
      ileft; ipureintro; left; exact h m (by simp)
    · iapply entryClaims_conf γi l (fun m' hm => h m' (by simp [hm]))

/-- **The bootstrap log's entries, as the server's** (2026-10-27): consecutive from index `1`,
conf changes. -/
theorem bootEntries_ok (ps : List w64) (bootLog : List EntryM) (hboot : srvBootLogOk ps bootLog) :
    srvIdxOkW (W64 0) (bootEntries bootLog) ∧ ∀ m ∈ bootEntries bootLog, m.typ = W32 1 := by
  obtain ⟨-, -, hk⟩ := hboot
  have hent : ∀ (n : Nat) (m : EntryModel), (bootEntries bootLog)[n]? = some m →
      uint.Z m.index = (n : Int) + 1 ∧ m.typ = W32 1 ∧ isConfChangeEncoding m.data := by
    intro n m hm
    unfold bootEntries at hm
    rw [List.getElem?_map] at hm
    cases he : bootLog[n]? with
    | none => rw [he] at hm; simp at hm
    | some e =>
      rw [he] at hm
      simp only [Option.map_some, Option.some.injEq] at hm
      subst hm
      obtain ⟨-, hi, ht, ⟨cm, hd, -⟩⟩ := hk n e he
      refine ⟨hi, ht, ?_⟩
      unfold isConfChangeEncoding
      show (ccDecodeV1 e.Data').isSome = true
      rw [hd]; rfl
  refine ⟨fun n m hm => ?_, fun m hm => ?_⟩
  · obtain ⟨hi, ht, hc⟩ := hent n m hm
    refine ⟨?_, Or.inr ⟨ht, hc⟩⟩
    rw [hi]; word
  · obtain ⟨n, hn⟩ := List.getElem?_of_mem hm
    exact (hent n m hn).2.1

/-- **The KV invariant at the bootstrap log** (a new cluster: the server's start log empty, its
start index `0`, the consistent index `0`, the base chain, a non-empty start log): from the
server's log of requested entries at the cluster's bootstrap log (`srvLogInv_alloc`'s; 2026-10-27,
until then the client's half of raft's committed log), each a conf change of id `0` that
`applyConfChange` takes (`hcc`), and the KV state's variable at the bootstrap log's model, the
invariant and the client's `etcdKV`. -/
theorem kvInv_alloc_boot (γs : ServerRaftNames) (γk : KVNames) (ps : List w64) (E : CoPset)
    (hpre : γs.pre = []) (hai : γs.ai0 = W64 0) (hboot : srvBootLogOk ps γs.raft.boot)
    (hcc : ∀ e ∈ γs.raft.boot, ccIdOf e.Data' = W64 0 ∧ ccBootOk γs.raft.cfg e.Data')
    (hc0 : γk.c0 = W64 0) (hch : γk.ch0 = apply.alarmChain false false false)
    (hlog : γk.log0 ≠ []) (hlk : mvcc.LogPutsLe etcdKeyMax γk.log0) :
    ⊢ srvRLog (GF := GF) γs (bootEntries γs.raft.boot) -∗
      ghostVar γk.st 1 (kvModelSt γk (bootEntries γs.raft.boot)) ={E}=∗
      kvInv γs γk ∗ etcdKV γk (kvModelSt γk (bootEntries γs.raft.boot)) := by
  generalize hbl : γs.raft.boot = bootLog at hboot hcc ⊢
  iintro HL Hv
  icases buildGhostVarHalves γk.st _ $$ Hv with ⟨Hv1, Hv2⟩
  have hent : ∀ (n : Nat) (m : EntryModel), (bootEntries bootLog)[n]? = some m →
      uint.Z m.index = (n : Int) + 1 ∧ m.typ = W32 1 ∧ isConfChangeEncoding m.data ∧
        ccIdOf m.data = W64 0 := by
    obtain ⟨-, -, hk⟩ := hboot
    intro n m hm
    unfold bootEntries at hm
    rw [List.getElem?_map] at hm
    cases he : bootLog[n]? with
    | none => rw [he] at hm; simp at hm
    | some e =>
      rw [he] at hm
      simp only [Option.map_some, Option.some.injEq] at hm
      subst hm
      obtain ⟨-, hi, ht, ⟨cm, hd, -⟩⟩ := hk n e he
      refine ⟨hi, ht, ?_, (hcc e (List.mem_of_getElem? he)).1⟩
      unfold isConfChangeEncoding
      show (ccDecodeV1 e.Data').isSome = true
      rw [hd]; rfl
  have hent' := hent
  have hok : plainLog (bootEntries bootLog) ∧ srvIdxOkW γs.ai0 (bootEntries bootLog) ∧
      uint.Z γk.c0 ≤ uint.Z γs.ai0 ∧
      γk.ch0 = apply.alarmChain false false false ∧ γk.log0 ≠ [] := by
    refine ⟨?_, ?_, ?_, hch, hlog⟩
    · intro m hm
      obtain ⟨n, hn⟩ := List.getElem?_of_mem hm
      obtain ⟨-, ht, -⟩ := hent n m hn
      intro h0
      rw [ht] at h0
      exact absurd h0 (by decide)
    · intro n m hm
      obtain ⟨hi, ht, hc, -⟩ := hent n m hm
      refine ⟨?_, Or.inr ⟨ht, hc⟩⟩
      rw [hai, hi]; word
    · rw [hc0, hai]; word
  -- the workload facts of the boot log (D19c): conf changes of id `0`, nothing claimed
  have hshape : logShape (bootEntries bootLog) := by
    intro m hm
    obtain ⟨n, hn⟩ := List.getElem?_of_mem hm
    obtain ⟨-, ht, -, hid⟩ := hent' n m hn
    refine ⟨fun h0 => ?_, fun _ => hid⟩
    rw [ht] at h0; exact absurd h0 (by decide)
  -- (audit phase B3) every conf change of the boot log is one `applyConfChange` takes
  have hccl : ccLogOk γs.raft (bootEntries bootLog) := by
    intro m hm _
    obtain ⟨n, hn⟩ := List.getElem?_of_mem hm
    obtain ⟨-, -, hk⟩ := hboot
    unfold bootEntries at hn
    rw [List.getElem?_map] at hn
    cases he : bootLog[n]? with
    | none => rw [he] at hn; simp at hn
    | some e =>
      rw [he] at hn
      simp only [Option.map_some, Option.some.injEq] at hn
      subst hn
      exact ccPolOk_of_boot _ _ (hcc e (List.mem_of_getElem? he)).2
  ihave #Hcl := entryClaims_conf (GF := GF) γk.ids (bootEntries bootLog) (fun m hm => by
    obtain ⟨n, hn⟩ := List.getElem?_of_mem hm
    obtain ⟨-, ht, -, -⟩ := hent' n m hn
    rw [ht]; decide)
  iunfold kvInv
  imod inv_alloc kvN E (iprop(∃ L : List EntryModel,
      srvRLog γs L ∗ ghostVar γk.st (1 : Qp).half (kvModelSt γk L) ∗
      ⌜plainLogM γk.cmp L ∧ srvIdxOkW γs.ai0 L ∧ uint.Z γk.c0 ≤ uint.Z γs.ai0 ∧
        γk.ch0 = apply.alarmChain false false false ∧ γk.log0 ≠ [] ∧ cmpLogOk γk γk.cmp L⌝ ∗
        kvWork γs.raft γk L))
    $$ [HL Hv1] with #Hinv
  · inext
    iexists bootEntries bootLog
    iframe Hv1
    isplitl [HL]
    · iexact HL
    isplitr
    · ipureintro
      exact ⟨plainLogM_of _ _ hok.1, hok.2.1, hok.2.2.1, hok.2.2.2.1, hok.2.2.2.2,
        cmpLogOk_plain _ _ _ hok.1⟩
    iunfold kvWork
    iframe Hcl
    ipureintro
    refine ⟨hshape, hccl, fun m hm => entryPutsOk_conf m ?_, hlk⟩
    obtain ⟨n, hn⟩ := List.getElem?_of_mem hm
    obtain ⟨-, ht, -, -⟩ := hent' n m hn
    rw [ht]; decide
  imodintro
  iframe Hinv
  iunfold etcdKV; iexact Hv2

/-- **The certificates' invariant**: from the store's certificate authority (empty), the
certified length's half at the start log's length, and the empty log committed. -/
theorem kvCertInv_alloc (γs : ServerRaftNames) (γk : KVNames) (E : CoPset)
    (h2 : 2 ≤ γk.log0.length) :
    ⊢ ghostMapAuth (GF := GF) γk.cok 1 (∅ : GMap w64 mvcc.Log) -∗
      ghostVar γk.hi (1 : Qp).half γk.log0.length -∗ srvRLogLb γs [] ={E}=∗
      kvCertInv γs γk := by
  iintro HC Hhi #HL
  iunfold kvCertInv
  iapply inv_alloc kvcN E
  inext
  iexists ∅, γk.log0.length, []
  iframe HC Hhi HL
  ipureintro
  refine ⟨?_, h2⟩
  intro n l hn
  simp at hn

/-- **The indices' invariants at index `0`** (the server's start index `0`): from the three
atomics at `0` (the zero fields of the `EtcdServer` literal), the indices' fresh authorities, the
applied logs' empty map, the pending flag, the store's certificate of the start log and the empty
log committed: the applied index's invariant with the apply thread's half and the start log
applied at `0`; the committed index's with the writer's half; the term's. -/
theorem srvIndices_alloc (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) (Ec : CoPset)
    (hai : γr.raft.ai0 = W64 0) :
    ⊢ sync.atomic.ownUint64 (srvAppliedIndexAddr s) (DFrac.own 1) (W64 0) -∗
      sync.atomic.ownUint64 (srvCommittedIndexAddr s) (DFrac.own 1) (W64 0) -∗
      sync.atomic.ownUint64 (srvTermAddr s) (DFrac.own 1) (W64 0) -∗
      monoNatAuthOwn γr.applied 1 0 -∗ monoNatAuthOwn γr.committed 1 0 -∗
      ghostMapAuth γr.logs 1 (∅ : GMap w64 mvcc.Log) -∗ ghostVar γr.pend 1 false -∗
      mvcc.idxCert E.γ.idx γr.kv.log0 -∗ srvRLogLb γr.raft [] ={Ec}=∗
      srvAppliedInv s E γr ∗ srvAppliedOwn γr (W64 0) ∗ appliedLogAt γr (W64 0) γr.kv.log0 ∗
      srvCommittedInv s γr ∗ srvCommittedOwn γr (W64 0) ∗
      inv srvN (∃ t : w64, sync.atomic.ownUint64 (srvTermAddr s) (DFrac.own 1) t) := by
  iintro Hai Hci Hti Hap Hcm Hlogs Hpend #Hcert #HL
  have h0 : uint.nat (W64 0) = 0 := rfl
  icases buildMonoNatHalves γr.applied 0 $$ Hap with ⟨Hap1, Hap2⟩
  icases buildMonoNatHalves γr.committed 0 $$ Hcm with ⟨Hcm1, Hcm2⟩
  icases buildGhostVarHalves γr.pend false $$ Hpend with ⟨Hp1, Hp2⟩
  imod ghost_map_insert_persist (W64 0) γr.kv.log0 (GMap.lookup_empty _) $$ Hlogs with ⟨Hlogs, #Hlog0⟩
  imod inv_alloc srvN Ec (iprop(∃ t : w64,
      sync.atomic.ownUint64 (srvTermAddr s) (DFrac.own 1) t)) $$ [Hti] with #Hterm
  · inext; iexists W64 0; iexact Hti
  imod inv_alloc srvN Ec (iprop(∃ v : w64,
      sync.atomic.ownUint64 (srvCommittedIndexAddr s) (DFrac.own 1) v ∗
      monoNatAuthOwn γr.committed (1 : Qp).half (uint.nat v) ∗
      (∃ L : List EntryModel, srvRLogLb γr.raft L ∗ ⌜uint.Z v ≤ uint.Z γr.raft.ai0 + L.length⌝)))
    $$ [Hci Hcm1] with #Hcinv
  · inext
    iexists W64 0
    rw [h0]
    iframe Hci Hcm1
    iexists []
    iframe HL
    ipureintro; rw [hai]; simp
  imod inv_alloc srvN Ec (srvAppliedBody s E γr)
    $$ [Hai Hap1 Hlogs Hp1] with #Hainv
  · inext
    iunfold srvAppliedBody
    iexists W64 0, W64 0, γr.kv.log0, (∅ : GMap w64 mvcc.Log).insert (W64 0) γr.kv.log0, false
    rw [h0]
    iframe Hai Hap1 Hlogs Hp1 Hcert
    isplitr
    · ipureintro
      refine ⟨Int.le_refl _, ?_⟩
      constructor
      · intro k L' hk
        rw [GMap.lookup_insert_Some] at hk
        rcases hk with ⟨rfl, -⟩ | ⟨-, hk⟩
        · left; exact Int.le_refl _
        · simp at hk
      · intro k k' L1 L2 h1 h2 _
        rw [GMap.lookup_insert_Some] at h1 h2
        rcases h1 with ⟨-, rfl⟩ | ⟨-, h1⟩
        · rcases h2 with ⟨-, rfl⟩ | ⟨-, h2⟩
          · exact List.prefix_refl _
          · simp at h2
        · simp at h1
    isplitr
    · iunfold appliedLogAt; iexact Hlog0
    iunfold kvLogsOk
    iexists []
    iframe HL
    ipureintro
    intro k L' hk
    rw [GMap.lookup_insert_Some] at hk
    rcases hk with ⟨rfl, rfl⟩ | ⟨-, hk⟩
    · refine ⟨[], List.prefix_refl _, ?_, rfl⟩
      rw [hai]; simp
    · simp at hk
  imodintro
  unfold srvAppliedInv srvCommittedInv srvAppliedOwn srvCommittedOwn
  iframe Hainv Hcinv Hterm
  rw [h0]
  iframe Hap2 Hp2 Hcm2
  iunfold appliedLogAt; iexact Hlog0

/-- **The proposals' mint, allocated** (`srvPropMint`; the cluster's since stage M4, 2026-10-19):
from raft's fresh-data authority (empty; `allocClientBoot`'s continuation output). -/
theorem srvPropMint_alloc (γ : ServerRaftNames) (γi : IdNames) (E : CoPset) :
    ⊢ ghostMapAuth (GF := GF) γ.raft.fresh 1 (∅ : GMap (List w8) Unit) ={E}=∗
      srvPropMint γ γi := by
  iintro HF
  iunfold srvPropMint
  iapply inv_alloc srvMintN E
  inext
  iexists ∅
  iframe HF
  iapply (BigSepM.bigSepM_empty (PROP := IProp GF)).2
  itrivial

/-- **The mints** (`srvMintInv`): the cluster's proposals' mint and read contexts (stage M4,
2026-10-19: allocated once for the cluster, `srvClusterBoot_alloc`). (2026-10-30, the repair: no
read credits; until then also the member's share of the cluster's, `2 ^ 48`. Until M4 from raft's
fresh-data and fresh read-context authorities and its whole read budget.) -/
theorem srvMintInv_alloc (ρ : ReqNames) (E : CoPset) :
    ⊢ srvPropMint (GF := GF) ρ.raft ρ.ids -∗ srvRdCtxInv ρ.raft ρ.ids.issued ={E}=∗
      srvMintInv ρ := by
  iintro #HP #HR
  imod srvRdFreshInv_alloc ρ.raft ρ.ids E $$ HR with #Hrd
  iunfold srvMintInv
  iframe HP Hrd

end alloc

end EtcdGrove
end Perennial

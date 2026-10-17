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
* `consInv_alloc`: the apply protocol's invariant over a fresh consistent index (for whoever
  discharges `bootstrap`'s contract, `InvBoot.lean`: the backend's batch lock's resource names the
  protocol's names, so they exist before the backend does).
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- A ghost variable's whole as its two halves. -/
private theorem buildGhostVarHalves {A : Type} [Pos.Countable A] (γ : GName) (a : A) :
    ghostVar (GF := GF) γ 1 a ⊢ ghostVar γ (1 : Qp).half a ∗ ghostVar γ (1 : Qp).half a := by
  have h := ghostVar_split (GF := GF) γ a (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at h
  exact wand_entails h

/-- A mono nat's whole authority as its two halves. -/
private theorem buildMonoNatHalves (γ : GName) (n : Nat) :
    monoNatAuthOwn (GF := GF) γ 1 n ⊢
      monoNatAuthOwn γ (1 : Qp).half n ∗ monoNatAuthOwn γ (1 : Qp).half n := by
  have hf := (monoNatAuthOwn_fractional (GF := GF) γ n).fractional (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at hf
  exact hf.1

/-- **The read names, fresh**, at the raft names `raft` and the KV start values (`c0`, `ch0`,
`log0`), the KV names' certificate map `cok` (the store's, chosen before `mvcc.New`), and the KV
state's variable at `σ`. -/
theorem srvReadNamesFresh_alloc (raft : ServerRaftNames) (c0 : w64) (ch0 : apply.Chain)
    (log0 : mvcc.Log) (cok : GName) (σ : KVState) :
    ⊢ |==> ∃ γr : ReadNames,
      ⌜γr.raft = raft ∧ γr.kv.c0 = c0 ∧ γr.kv.ch0 = ch0 ∧ γr.kv.log0 = log0 ∧ γr.kv.cok = cok⌝ ∗
      srvReadNamesFresh (GF := GF) γr σ := by
  imod mono_nat_own_alloc (GF := GF) 0 with ⟨%γa, Ha, -⟩
  imod mono_nat_own_alloc (GF := GF) 0 with ⟨%γc, Hc, -⟩
  imod ghostVar_alloc (GF := GF) ((null, ⟨γa, γa⟩) : Loc × NeedNames) with ⟨%γn, Hn⟩
  imod ghost_map_alloc_empty (GF := GF) (K := w64) (V := mvcc.Log) with ⟨%γl, Hl⟩
  imod ghostVar_alloc (GF := GF) false with ⟨%γp, Hp⟩
  imod ghostVar_alloc (GF := GF) σ with ⟨%γst, Hst⟩
  imod ghostVar_alloc (GF := GF) log0.length with ⟨%γhi, Hhi⟩
  imodintro
  iexists ⟨γa, γc, γn, γl, γp, raft, ⟨γst, c0, ch0, log0, cok, γhi⟩⟩
  isplitr
  · ipureintro; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  unfold srvReadNamesFresh
  iframe Ha Hc Hl Hp Hst Hhi
  iexists _
  iexact Hn

/-- **The KV invariant at the bootstrap log** (a new cluster: the server's start log empty, its
start index `0`, the consistent index `0`, the base chain, a non-empty start log): from the
client's half of raft's committed log at `bootLog` and the KV state's variable at the bootstrap
log's model, the invariant and the client's `etcdKV`. -/
theorem kvInv_alloc_boot (γs : ServerRaftNames) (γk : KVNames) (ccOk : w32 → List w8 → Prop)
    (ps : List w64) (bootLog : List EntryM) (E : CoPset)
    (hpre : γs.pre = []) (hai : γs.ai0 = W64 0) (hboot : BootLogOk ccOk ps bootLog)
    (hc0 : γk.c0 = W64 0) (hch : γk.ch0 = apply.alarmChain false false false)
    (hlog : γk.log0 ≠ []) :
    ⊢ rLog (GF := GF) γs.raft bootLog -∗
      ghostVar γk.st 1 (kvStateOf (kvModel γk (bootEntries bootLog))) ={E}=∗
      kvInv γs γk ∗ etcdKV γk (kvStateOf (kvModel γk (bootEntries bootLog))) := by
  iintro HL Hv
  icases buildGhostVarHalves γk.st _ $$ Hv with ⟨Hv1, Hv2⟩
  have hsl : srvLogOf γs (bootEntries bootLog) = bootLog := by
    unfold srvLogOf bootEntries; rw [hpre, List.nil_append, EntryModel.map_toM_ofM]
  have hok : plainLog (bootEntries bootLog) ∧ srvIdxOkW γs.ai0 (bootEntries bootLog) ∧
      uint.Z γk.c0 ≤ uint.Z γs.ai0 + (bootEntries bootLog).length ∧
      γk.ch0 = apply.alarmChain false false false ∧ γk.log0 ≠ [] := by
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
        obtain ⟨-, hi, ht, ⟨cm, hd, -⟩, -⟩ := hk n e he
        refine ⟨hi, ht, ?_⟩
        unfold isConfChangeEncoding
        show (ccDecodeV1 e.Data').isSome = true
        rw [hd]; rfl
    refine ⟨?_, ?_, ?_, hch, hlog⟩
    · intro m hm
      obtain ⟨n, hn⟩ := List.getElem?_of_mem hm
      obtain ⟨-, ht, -⟩ := hent n m hn
      intro h0
      rw [ht] at h0
      exact absurd h0 (by decide)
    · intro n m hm
      obtain ⟨hi, ht, hc⟩ := hent n m hm
      refine ⟨?_, Or.inr ⟨ht, hc⟩⟩
      rw [hai, hi]; word
    · rw [hc0, hai]; word
  iunfold kvInv
  imod inv_alloc kvN E (iprop(∃ L : List EntryModel,
      srvRLog γs L ∗ ghostVar γk.st (1 : Qp).half (kvStateOf (kvModel γk L)) ∗
      ⌜plainLog L ∧ srvIdxOkW γs.ai0 L ∧ uint.Z γk.c0 ≤ uint.Z γs.ai0 + L.length ∧
        γk.ch0 = apply.alarmChain false false false ∧ γk.log0 ≠ []⌝)) $$ [HL Hv1] with #Hinv
  · inext
    iexists bootEntries bootLog
    iframe Hv1
    isplitl [HL]
    · iunfold srvRLog; rw [hsl]; iexact HL
    ipureintro; exact hok
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
  imod inv_alloc srvN Ec (iprop(∃ (v : w64) (L : mvcc.Log) (M : GMap w64 mvcc.Log) (p : Bool),
      sync.atomic.ownUint64 (srvAppliedIndexAddr s) (DFrac.own 1) v ∗
      monoNatAuthOwn γr.applied (1 : Qp).half (uint.nat v) ∗
      ghostMapAuth γr.logs 1 M ∗ ghostVar γr.pend (1 : Qp).half p ∗
      ⌜appliedKeysOk M v p ∧ appliedMonoMap M⌝ ∗
      appliedLogAt γr v L ∗ mvcc.idxCert E.γ.idx L ∗ kvLogsOk γr M))
    $$ [Hai Hap1 Hlogs Hp1] with #Hainv
  · inext
    iexists W64 0, γr.kv.log0, (∅ : GMap w64 mvcc.Log).insert (W64 0) γr.kv.log0, false
    rw [h0]
    iframe Hai Hap1 Hlogs Hp1 Hcert
    isplitr
    · ipureintro
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

/-- **The mints** (`srvMintInv`): from raft's fresh-data and fresh read-context authorities
(empty) and its whole read budget (`allocClientBoot`'s continuation outputs and
`ownRaftGhost_alloc_boot`'s credits). -/
theorem srvMintInv_alloc (ρ : ReqNames) (E : CoPset) :
    ⊢ ghostMapAuth (GF := GF) ρ.raft.raft.reFresh 1 (∅ : GMap (List w8) Unit) -∗
      ghostMapAuth ρ.raft.raft.reRdFresh 1 (∅ : GMap (List w8) Unit) -∗
      rdCred ρ.raft.raft (2 ^ 64 - 2) ={E}=∗ srvMintInv ρ := by
  iintro HF HR Hc
  imod srvRdFreshInv_alloc ρ.raft ρ.ids E $$ HR Hc with #Hrd
  iunfold srvMintInv
  iframe Hrd
  iapply inv_alloc srvMintN E
  inext
  iexists ∅
  iframe HF
  iapply (BigSepM.bigSepM_empty (PROP := IProp GF)).2
  itrivial

/-- **The apply protocol's invariant** over a fresh consistent index (its client half at `0`),
with the backend's initial meta keys `m0`: the protocol's names, its invariant, the apply
thread's half at nothing processed beyond `m0`'s index, the batch lock's half of the stored
index's mirror and its token. -/
theorem consInv_alloc (γci : CINames) (m0 : MetaCI) (E : CoPset) :
    ⊢ ciIdx (GF := GF) γci (W64 0) ={E}=∗ ∃ γA : ApplyNames, ⌜γA.ci = γci ∧ γA.m0 = m0⌝ ∗
      inv applyN (consInv γA) ∗ applyThread γA ⟨W64 0, m0.1, m0.1, false⟩ ∗
      ghostVar γA.mt (1 : Qp).half m0.1 ∗ token γA.pend := by
  iintro Hk
  imod ghostVar_alloc (GF := GF) (⟨W64 0, m0.1, m0.1, false⟩ : ApplyState) with ⟨%γst, Hst⟩
  imod ghostVar_alloc (GF := GF) m0.1 with ⟨%γmt, Hmt⟩
  imod ghostVar_alloc (GF := GF) false with ⟨%γwr, Hwr⟩
  imod token_alloc (GF := GF) with ⟨%γpend, Htok⟩
  icases buildGhostVarHalves γst _ $$ Hst with ⟨Hst1, Hst2⟩
  icases buildGhostVarHalves γmt _ $$ Hmt with ⟨Hmt1, Hmt2⟩
  imod inv_alloc applyN E (consInv (⟨γci, γst, γmt, γwr, γpend, m0⟩ : ApplyNames))
    $$ [Hk Hst1 Hmt1 Hwr] with #Hinv
  · inext
    iunfold consInv
    iexists ⟨W64 0, m0.1, m0.1, false⟩, m0.1, false
    iframe Hk Hst1 Hmt1 Hwr
    iunfold flightInv
    ipureintro
    refine ⟨fun h => absurd rfl h, fun _ => rfl, fun _ => rfl, ?_⟩
    unfold stOk ciEff
    simp
  imodintro
  iexists ⟨γci, γst, γmt, γwr, γpend, m0⟩
  iframe Hinv Hmt2 Htok
  isplitr
  · ipureintro; exact ⟨rfl, rfl⟩
  iunfold applyThread; iexact Hst2

end alloc

end EtcdGrove
end Perennial

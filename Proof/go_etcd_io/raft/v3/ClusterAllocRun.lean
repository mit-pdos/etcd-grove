/-
Lean-first (no Rocq counterpart). (#33 parity B1) **A cluster for a client that writes its own
bootstrap log**: the antithesis harness's `RunCluster` (mit-pdos/etcd-grove#33), whose bootstrapped
run's `node.start` writes one normal entry `{Term: 1, Index: 1, Data: d}` and the hard state
`{Term: 1}` into each node's storage before `NewRawNode` (their `BootInit`), instead of raft's
`Bootstrap` (one `AddNode` per voter, `BootLog`, which `cluster_alloc_boot_impl` takes).

- `ownDurGhost_boot`: a node's durable half moves from `RaftState.init` to the state that write
  leaves (`bootDurState`: term `1`, no vote, the bootstrap log from `base0`, commit `0`), given the
  bootstrap log's records. Nothing of the entered maps changes; their histories over the empty log
  are of no entry, so they hold of any log.
- `cluster_alloc_normBoot`: `cluster_alloc_boot_implG_tr` (untraced, snapshots on, the caller's
  `dup`: the harness's driver duplicates deliveries, forwarded `MsgProp`s too) at a bootstrap log
  of normal entries (`NormBoot`) instead of `BootLog`, for every id of `ids` (the voters `vs` among
  them; non-voters too, since a cluster with a bootstrap log has no join authority), each at
  `bootDurState` (`ownDurGhost_boot`), with the bootstrap log's records and its commitment.
-/
module

public import Proof.go_etcd_io.raft.v3.RawNodeStartSpec
import Proof.go_etcd_io.raft.v3.InvApiBoot
import all Proof.go_etcd_io.raft.v3.InvNode
import all Proof.go_etcd_io.raft.v3.InvNodeRule
import all Proof.go_etcd_io.raft.v3.Protocol.Enter
import all Proof.go_etcd_io.raft.v3.RawNodeStartSpec

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-- **The durable state a client's bootstrap write leaves**: term `1`, no vote, the bootstrap log
`L` from `base0`, commit `0`. -/
def bootDurState [GooseExts] (L : List EntryM) : RaftState := ⟨W64 1, W64 0, base0, L, W64 0, W64 0⟩

section dur
variable [GooseExts]
variable {GF : BundledGFunctors} [AllG GF] [ReceiptGS GF] [InvGS GF] [CrashGS GF]

/-- A history over the empty log is of no entry: it holds of any log, at any larger bound. -/
theorem hist_nil_any (γ : RaftNames) (F0 F : List EntryM) (t i : w64) (B B' : Int) :
    F0 = [] → B ≤ B' → ⊢ hist (GF := GF) γ F0 t i B -∗ hist γ F t i B' := by
  intro HF0 HB
  subst HF0
  unfold hist
  iintro #H %j %Hj
  ihave H' := H $$ %j %Hj
  icases H' with (⟨%X, -, %HXj⟩ | ⟨%j', %X1, %X2, %Hj', #H1, #H2, %Hd⟩)
  · exfalso
    obtain ⟨Hs, He⟩ := HXj
    rw [He] at Hs
    obtain ⟨t', Ht'⟩ := Option.isSome_iff_exists.mp Hs
    have h2 := (plogTermAt_some_range _ _ _ _ Ht').2
    have h3 := Hj.1
    unfold plogLastIndexZ at h2; rw [base0_index] at h2
    rw [List.length_nil] at h2
    omega
  · iright
    iexists j', X1, X2
    isplitr; · ipureintro; exact Hj'
    isplitr; · iapply okL_mono γ t B B' j' X1 HB $$ H1
    isplitr; · iapply okL_mono γ t B B' j' X2 HB $$ H2
    ipureintro; exact Hd

/-- **A node's durable half at the bootstrap write** (see the file header): from `RaftState.init`
to `bootDurState γ.reBoot`, given the bootstrap log's records, its entries normal, of term `1`,
from index `1`. -/
theorem ownDurGhost_boot (γ : RaftNames) (id : w64) :
    PlogWf base0 γ.reBoot → (∀ e ∈ γ.reBoot, e.Term' = W64 1) →
    (∀ e ∈ γ.reBoot, ¬ IsConfEnt e) →
    ⊢ logRecs (GF := GF) γ base0 γ.reBoot -∗ ownDurGhost γ id RaftState.init -∗
      ownDurGhost γ id (bootDurState γ.reBoot) := by
  intro Hwf Hones Hnc
  iintro #Hrecs Hd
  unfold ownDurGhost
  icases Hd with ⟨%E, Hsh, #Hp, #Hsi, -⟩
  iexists E
  iframe Hsh Hsi
  have Hb : RaftState.init.base = base0 := rfl
  have Hc : RaftState.init.commit = W64 0 := rfl
  have He : RaftState.init.ents = [] := rfl
  have Ht : RaftState.init.term = W64 0 := rfl
  have Hv : RaftState.init.vote = W64 0 := rfl
  unfold durPers
  rw [Hb, He, Hc, Ht]
  icases Hp with ⟨%kd, %fp, %Hpure, -, #Hbase, #Hfp, #Hvl, #Hacks, -, #Hag, -, #Hcm, #Hci, #Hfr⟩
  obtain ⟨⟨Hv1, -⟩, Hak, Hcp, Hevs, Hfull, -, -, -, -⟩ := Hpure
  rw [Ht] at Hv1
  have Hfp0 : fp = [] := List.eq_nil_of_length_eq_zero (by
    have := Hfull.1; rw [base0_index] at this; omega)
  subst Hfp0
  have h0 : uint.Z (W64 0) = 0 := rfl
  have h1 : uint.Z (W64 1) = 1 := rfl
  isplitr
  · unfold bootDurState
    iexists none, []
    isplitr
    · ipureintro
      refine ⟨⟨fun t ht => by have := Hv1 t ht; simp only [h0, h1] at this ⊢; omega, ?_⟩,
        fun k hk => by have := Hak k hk; simp only [h0, h1] at this ⊢; omega,
        fun T hT => by have := Hcp T hT; simp only [h0, h1] at this ⊢; omega,
        EvsOk_mono _ _ E (by simp only [h0, h1]; omega) Hevs, FullOk_base0, Hwf, ?_,
        by rw [base0_index, h0]; omega, by unfold plogLastIndexZ; rw [base0_index, h0]; omega⟩
      · rw [if_pos rfl]
        cases hv : E.voted !! W64 1 with
        | none => rfl
        | some x =>
          have := Hv1 (W64 1) (by rw [hv]; rfl)
          rw [h0, h1] at this; omega
      · intro j x Hx
        rw [List.nil_append] at Hx
        by_cases hj : uint.Z j = 0
        · have Hj : j = base0.index' := uint_Z_inj.mp (by rw [base0_index]; exact hj)
          subst Hj
          rw [plogTermAt_base] at Hx; cases Hx
          show (0 : Int) ≤ 1; omega
        · have Hr := plogTermAt_some_range _ _ _ _ Hx
          obtain ⟨e, Hek, -, Het⟩ := plogTermAt_some_entry _ _ _ _ (PlogWf_wfR _ _ Hwf) Hx
            (by rw [base0_index]; have := uint_Z_nonneg j; omega)
          rw [← Het, Hones e (List.mem_of_getElem? Hek), h1]; omega
    isplitr; · iexact Hrecs
    isplitr; · iexact Hbase
    isplitr; · iexact Hfp
    isplitr
    · iapply BigSepM.bigSepM_impl $$ Hvl
      imodintro
      iintro %k %x %_ ⟨%Hx, #Hin⟩
      iframe Hin
      ipureintro; rw [h0] at Hx; rw [h1]; omega
    isplitr
    · iapply BigSepM.bigSepM_impl $$ Hacks
      imodintro
      iintro %k %u %_ #Hh
      ihave #Hh2 := hist_nil_any γ ([] ++ []) ([] ++ γ.reBoot) k.1 k.2 (bndD RaftState.init kd)
        (uint.Z (W64 1)) rfl
        (by cases kd <;> unfold bndD <;> dsimp only [bootDurState, RaftState.init] <;> rw [h1] <;>
              (try rw [h0]) <;> omega) $$ Hh
      iExactEq Hh2; rfl
    isplitr; · unfold klOkD; itrivial
    isplitr
    · iapply BigSepM.bigSepM_impl $$ Hag
      imodintro
      iintro %k %u %Hk - %Hk1
      exfalso
      have := Hak k (by rw [show (E.acks !! k) = some u from Hk]; rfl)
      rw [Hk1.1, h0] at this
      exact absurd this (by show ¬ (uint.Z (W64 1) ≤ 0); rw [h1]; omega)
    isplitr
    · unfold commitIn
      isplitr
      · unfold commitJ; ileft; ipureintro
        refine ⟨by rw [h0]; omega, ?_⟩
        rw [List.nil_append]
      · unfold dynOn
        iright; unfold witsB; iintro %k %Hk %_; exfalso
        have := Hk.2
        rw [h0] at this; simp at this
    iframe Hci
    isplitr
    · iExactEq Hcm
      simp only [List.nil_append, h0]
      rfl
    · iexact Hfr
  · unfold durI1 bootDurState
    iintro !> %fp %Hfp -
    ipureintro; intro _
    have : fp = [] := List.eq_nil_of_length_eq_zero (by
      have := Hfp.1; rw [base0_index] at this; omega)
    subst this
    intro k1 k2 e1 e2 _ H1 _ Hc1 _
    rw [List.nil_append] at H1
    exact absurd Hc1 (Hnc e1 (List.mem_of_getElem? H1))

end dur

section normBoot
variable [GooseExts]

/-- **A bootstrap log a client writes itself** (see the file header): none, or one normal entry of
term `1` with data (not a filler). -/
def NormBoot (boot : List LogEntry) : Prop :=
  boot = [] ∨ ∃ d : List w8, d ≠ [] ∧ boot = [⟨W64 1, W32 0, d⟩]

theorem NormBoot.ops {boot : List LogEntry} (H : NormBoot boot) : opsOf boot = boot := by
  rcases H with rfl | ⟨d, hd, rfl⟩
  · rfl
  · apply ApiImpl.opsOf_eq_self
    intro e he
    simp only [List.mem_singleton] at he
    subst he
    refine ⟨fun h => hd h.1, fun h => ?_⟩
    have h2 : (W32 0 : w32) = W32 2 := h.2
    revert h2; word

theorem NormBoot.idx {boot : List LogEntry} (H : NormBoot boot) :
    ApiImpl.IdxOk (LogEntry.toEntries boot 0) := by
  rcases H with rfl | ⟨d, hd, rfl⟩
  · intro k e h; simp [LogEntry.toEntries] at h
  · intro k e h
    rw [ApiImpl.toEntries_getElem?] at h
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.map_some, Option.some.injEq] at h
      subst h; rfl
    | succ k => simp at h

theorem NormBoot.ents {boot : List LogEntry} (H : NormBoot boot) :
    ∀ e ∈ LogEntry.toEntries boot 0, e.Type' = W32 0 ∧ e.Term' = W64 1 ∧ e.Data' ≠ [] := by
  rcases H with rfl | ⟨d, hd, rfl⟩
  · intro e he; simp [LogEntry.toEntries] at he
  · intro e he
    simp only [LogEntry.toEntries, List.mapIdx_cons, List.mapIdx_nil, List.mem_singleton] at he
    subst he
    exact ⟨rfl, rfl, hd⟩

theorem NormBoot.len {boot : List LogEntry} (H : NormBoot boot) : boot.length ≤ 1 := by
  rcases H with rfl | ⟨d, hd, rfl⟩ <;> simp

theorem NormBoot.wf {boot : List LogEntry} (H : NormBoot boot) :
    BootWf (LogEntry.toEntries boot 0) := by
  have Hl := H.len
  have Hi := H.idx
  have He := H.ents
  refine ⟨by rw [ApiImpl.toEntries_length]; omega, fun k e hk => ?_, ?_⟩
  · obtain ⟨Hty, Ht, Hd⟩ := He e (List.mem_of_getElem? hk)
    refine ⟨Ht, Hi k e hk, fun hf => Hd hf.1, ?_⟩
    rw [Hty]; exact CCDecodes_normal _
  · rcases H with rfl | ⟨d, hd, rfl⟩
    · exact List.nodup_nil
    · simp [LogEntry.toEntries]

theorem NormBoot.plogWf {boot : List LogEntry} (H : NormBoot boot) :
    PlogWf base0 (LogEntry.toEntries boot 0) := H.wf.wf

theorem NormBoot.noConf {boot : List LogEntry} (H : NormBoot boot) :
    ∀ e ∈ LogEntry.toEntries boot 0, ¬ IsConfEnt e := by
  intro e he hc
  have := (H.ents e he).1
  rcases hc with h | h <;> rw [this] at h <;> revert h <;> word

end normBoot

namespace ApiImpl

section alloc
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [AllG GF] [ReceiptGS GF] [InvGS GF]

/-- The committed facts of a log of normal entries: they decode, and none is an empty
`ConfChangeV2`. -/
private theorem cmtFacts_normal (γ : Cluster) (L : List EntryM) (H : ∀ e ∈ L, e.Type' = W32 0) :
    ⊢ cmtFacts (GF := GF) γ L := by
  unfold cmtFacts
  isplitr
  · ipureintro; intro e he
    rw [H e he]; exact CCDecodes_normal _
  imodintro
  iintro %k %e %hk
  unfold ev2At
  iintro %Hc
  exfalso
  have := Hc.2.2.2
  rw [H e (List.mem_of_getElem? hk)] at this
  revert this; word

/-- `api_alloc_client` at a client-written bootstrap log (`NormBoot`) instead of `BootLog`. -/
private theorem api_alloc_client_norm (N : Namespace) (E : CoPset) (cfg : GSet w64)
    (boot : List LogEntry) (bud : BudgetNames) (md : RNMode)
    (tab : GName) (dyn : Option ((e : GooseExts) → @DynCfg e))
    (HB : NormBoot boot) :
    ⊢ allocClientGen (GF := GF) E cfg dyn (fun _ _ => True) (LogEntry.toEntries boot 0)
        (allocOut N boot bud md tab) (N .@ "raft") := by
  unfold allocClientGen
  iintro %γr %Hγr #Hc HrL Hfa Hrfa ⟨%γT, #HspT, #Hpis⟩
  obtain ⟨-, -, -, HbL, HNs⟩ := Hγr
  have Hblen : (boot.length : Int) < (receiptBound GF : Int) + γr.reBoot.length := by
    have := receiptBound_pos (GF := GF)
    rw [HbL, toEntries_length]; omega
  have Hty : ∀ e ∈ LogEntry.toEntries boot 0, e.Type' = W32 0 := fun e he => (HB.ents e he).1
  imod mono_list_own_alloc (GF := GF) boot with ⟨%γf, Hf, #Hflb⟩
  imod mono_list_own_alloc (GF := GF) boot with ⟨%γo, Ho, #Holb⟩
  imod ghost_map_alloc_empty (GF := GF) (K := List w8) (V := GName × List LogEntry) with ⟨%γc, Hca⟩
  icases ((monoListAuthOwn_fractional (GF := GF) γo
      boot).fractional (1 : Qp).half (1 : Qp).half).1
    $$ [Ho] with ⟨Ho1, Ho2⟩
  · rw [Qp.half_add_half]; iexact Ho
  let γ : Cluster := ⟨γr, γf, γo, γc, bud, γT, md.all, tab⟩
  imod inv_alloc (apiN N) E (apiInvBody (GF := GF) γ) $$ [HrL Hf Ho1 Hfa Hrfa] with #Hinv
  · inext
    unfold apiInvBody
    iexists LogEntry.toEntries boot 0, bootFresh (LogEntry.toEntries boot 0), ∅
    rw [strip_toEntries, HB.ops]
    iframe HrL Hf Ho1 Hfa Hrfa
    isplitr
    · ipureintro; refine ⟨HB.idx, ?_⟩; rw [toEntries_length]; exact Hblen
    isplitr
    · unfold freshOk
      imodintro
      iintro %k %Hk
      unfold bootFresh at Hk
      rcases bootFreshFrom_lookup ∅ _ k Hk with h | ⟨e, he, hek⟩
      · exact absurd h (by simp [GMap.lookup_empty])
      · obtain ⟨j, hj⟩ := List.getElem?_of_mem he
        subst hek
        iapply (BigSepL.bigSepL_lookup (Φ := fun _ (e : EntryM) =>
          propIsAt (GF := GF) γr (entKey e.Type' e.Data') γT) hj) $$ Hpis
    isplitr
    · iapply cmtFacts_normal γ _ Hty
    isplitr
    · unfold rdKeys
      imodintro
      iintro %c %Hc
      exact absurd Hc (by simp [GMap.lookup_empty])
    · unfold rdFreshOk
      imodintro
      iintro %c %Hc
      exact absurd Hc (by simp [GMap.lookup_empty])
  ihave #Hinv' : apiInv (GF := GF) γ N $$ []
  · unfold apiInv; iexact Hinv
  ihave #Hnoop := api_noopAu γ N HNs $$ Hinv'
  imodintro
  iframe Hnoop
  unfold allocOut
  iexists γ
  isplitr; · ipureintro; exact ⟨rfl, rfl, rfl, rfl⟩
  iframe Hinv' HspT
  ihave #Hblb : isCommittedLogLb (GF := GF) γ boot $$ []
  · unfold isCommittedLogLb
    rw [HB.ops]
    iright; iframe Hflb Holb
    isplitr; · ipureintro; exact Hblen
    unfold cmtFactsS
    iexists LogEntry.toEntries boot 0
    isplitr; · ipureintro; exact strip_toEntries boot 0
    iapply cmtFacts_normal γ _ Hty
  iframe Hblb
  isplitl [Ho2]
  · unfold ownCommittedOps
    iframe Ho2
    iexists boot
    rw [HB.ops]
    iframe Hblb
    ipureintro; rfl
  · unfold ownReadCtxs
    iexists ∅
    iframe Hca
    ipureintro
    intro c
    constructor <;> intro h <;> exact absurd h (by simp [Membership.mem, GMap.lookup_empty])

end alloc

section allocRun
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [AllG GF] [ReceiptGS GF] [InvGS GF] [CrashGS GF]

/-- **A cluster with a client-written bootstrap log** (see the file header): of the voters `vs`,
with every id of `ids` (non-voters too) at the durable state the client's write leaves
(`bootDurState`; `RaftState.init` without a bootstrap log), untraced, snapshots on, no data bound,
duplicated proposals as the caller chooses (`dup`), with the bootstrap log's records and its
commitment. -/
private theorem cluster_alloc_normBoot (N : Namespace) (vs ids : List w64) (boot : List LogEntry)
    (dup : Bool) (E : CoPset) (HE : (↑(N .@ "raft") : CoPset) ⊆ E) :
    receiptBound GF ≤ 2 ^ 64 - 2 → vs ≠ [] → vs.Nodup → W64 0 ∉ vs → (vs.length : Int) < 2 ^ 62 →
    ids.Nodup → W64 0 ∉ ids → NormBoot boot →
    ⊢ |={E}=> ∃ γ : Cluster,
        ⌜γ.raft.dup = dup ∧ γ.raft.reBoot = LogEntry.toEntries boot 0 ∧ γ.raft.reTrace = none ∧
          γ.raft.maxData = none ∧ γ.raft.reNoSnap = false ∧ γ.raft.reCfg = GMap.listToSet vs ∧
          γ.raft.reNs = N .@ "raft"⌝ ∗
        ownCommittedOps (GF := GF) γ boot ∗ isClusterU γ N ∗
        confAtU γ 0 (Membership.simple (GMap.listToSet vs)) ∗
        isCommitted γ.raft γ.raft.reBoot ∗ logRecs γ.raft base0 γ.raft.reBoot ∗
        [∗list] id ∈ ids, raftStateU γ id
          (if boot = [] then RaftState.init else bootDurState γ.raft.reBoot) ∗ nodeVacantU γ id := by
  intro Hrb Hne Hnd Hnz Hlen Hind Hinz HB
  imod budget_alloc_boot (GF := GF) Hrb E with ⟨%bud, #Hbinv, #Htlb⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Loc) (V := CfgNames) with ⟨%tab, Htab⟩
  imod mono_list_own_alloc (GF := GF) ([] : List (w64 × List w8)) with ⟨%g, Hreg, -⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := Option ConfChangeIM) with ⟨%gd, Hdm⟩
  have Hwf := HB.wf
  have Hcne := listToSet_ne_empty vs Hne
  have Hnz' : W64 0 ∉ GMap.listToSet vs := fun h => Hnz ((GMap.elem_of_list_to_set _ _).1 h)
  have Hinz' : W64 0 ∉ GMap.listToSet ids := fun h => Hinz ((GMap.elem_of_list_to_set _ _).1 h)
  have Hsz : GMap.size (GMap.listToSet vs) < 2 ^ 62 := by
    rw [GMap.size_list_to_set vs Hnd]; omega
  have Hv := memValid_simple (GMap.listToSet vs) Hcne Hsz
  let c0 := Membership.simple (GMap.listToSet vs)
  let md : RNMode := .dyn noDec (stOf c0) Hv.1 Hv.2
  let dc := DynCfg.ofFold noDec (stOf c0) Hv.1
  ihave Hcl := api_alloc_client_norm (GF := GF) N E (GMap.listToSet vs) boot bud md tab
    (some (DynCfg.all dc)) HB
  imod ownRaftGhost_alloc_core_reg_tr E (GMap.listToSet vs) (GMap.listToSet ids)
    (some (DynCfg.all dc))
    (fun _ _ => True) (LogEntry.toEntries boot 0) (W64 1) (allocOut N boot bud md tab) none
    (fun _ h => by cases h)
    false (fun h => by cases h) false (fun h => by cases h) (fun _ _ => True) (fun _ => none)
    (N .@ "raft") N (some g) (some gd) dup none none (fun _ h => by cases h)
    (fun _ h => by cases h)
    Hcne Hinz' Hwf
    (fun _ => by rw [show uint.Z (W64 1) = 1 from rfl]; exact Int.le_refl _)
    $$ Hcl with ⟨%γr, %Hγ, #Hcinv, #Hc0, Hnodes, Hout, Hcr, -⟩
  obtain ⟨Hcfg, Hdyn, -, HbootL, -, Hns, Hnx, Hsok, Hsl, HNs, Hcert, Hrg, Hrd, Hdup, Htr0, Hmxd'⟩ := Hγ
  iunfold allocOut at Hout
  icases Hout with ⟨%γ, %Hγr, #HspT, #Hinv, Hops, -, -⟩
  obtain ⟨Hγr, Hγb, Hγm, Hγt⟩ := Hγr
  subst Hγr
  have Hrn : DecNames γ c0 gd := by
    refine ⟨Hv.1, Hv, ?_, ?_, ?_, Hrd⟩
    · unfold RaftNames.dyn; rw [Hdyn]; simp [DynCfg.all_self, dc]
    · intro L d; rw [Hsok]; trivial
    · rw [Hrg]; simp
  have Hr0 : W64 0 ∉ c0.ids ∧ ∀ k, k ∈ c0.learnersNext → k ∉ c0.voters := by
    refine ⟨fun h' => ?_, fun _ h' => absurd h' (GMap.not_elem_of_empty _)⟩
    simp only [c0, Membership.ids, Membership.simple, GMap.elem_of_union] at h'
    rcases h' with ((h' | h') | h') | h'
    · exact Hnz' h'
    all_goals exact GMap.not_elem_of_empty _ h'
  have Hmr : ModeDec γ c0 gd := ⟨Hrn, ⟨Hv.1, Hv.2, Hγm⟩, Hr0⟩
  imod receipt_zero (GF := GF) with H0
  imod inv_alloc (N .@ "rdpool") E
    iprop(∃ (k c : Nat), ⧗ k ∗ rdCred γ.raft c ∗ ⌜2 ^ 64 - 2 ≤ k + c⌝) $$ [Hcr H0] with #Hpool
  · inext
    iexists 0, 2 ^ 64 - 2
    iframe H0 Hcr
    ipureintro; omega
  ihave #Hdc : isClusterU (GF := GF) γ N $$ []
  · unfold isClusterU rdPool
    isplitr
    · ipureintro
      refine ⟨⟨c0, gd, Hmr⟩, Hcert, ?_⟩
      rw [HbootL]
      intro x hx h
      have := (HB.ents x hx).1
      unfold IsEmptyV2 at h
      rw [this] at h
      have h2 := h.2
      revert h2; word
    isplitr
    · unfold clusterInv
      iframe Hcinv Hinv HspT
      isplitr
      · ipureintro; exact HNs
      ipureintro; intro b hb
      rw [Hmxd'] at hb; cases hb
    iframe Hpool
    ipureintro; exact Hrb
  have HrE : (↑(raftN γ.raft) : CoPset) ⊆ E := by unfold raftN; rw [HNs]; exact HE
  imod boot_facts E γ.raft HrE $$ Hcinv with ⟨#Hcb, #Hrecs, %Hbf⟩
  imodintro
  iexists γ
  iframe Hops Hdc Hcb Hrecs
  isplitr
  · ipureintro; exact ⟨Hdup, HbootL, Htr0, Hmxd', Hns, Hcfg, HNs⟩
  isplitr
  · unfold confAtU
    iexists [], ∅
    isplitr; · iapply isCommittedLogLb_nil_impl
    isplitr; · iapply decLb_empty
    ipureintro
    exact ⟨Nat.le_refl _, c0, gd, Hmr, rfl⟩
  ihave #Htlb0 : termLB (GF := GF) bud (W64 0) $$ []
  · iapply termLB_le bud (W64 1) (W64 0) (by decide) $$ Htlb
  iapply bigSepM_listToSet _ ids Hind
  iapply BigSepM.bigSepM_impl $$ Hnodes
  imodintro
  iintro %id %u %Hid ⟨Hg, Ht⟩
  unfold raftStateU nodeVacantU
  rw [Hγb]
  iframe Ht Hbinv
  by_cases hb : boot = []
  · rw [if_pos hb, show RaftState.init.term = W64 0 from rfl]
    iframe Hg Htlb0
  · rw [if_neg hb]
    ihave Hg' := ownDurGhost_boot γ.raft id Hbf.1 Hbf.2
      (by rw [HbootL]; exact HB.noConf) $$ Hrecs Hg
    iframe Hg'
    rw [show (bootDurState γ.raft.reBoot).term = W64 1 from rfl]
    iexact Htlb

end allocRun

end ApiImpl

section allocRunApi
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [AllG GF] [ReceiptGS GF] [InvGS GF] [CrashGS GF]

/-- **`cluster_alloc_normBoot` over the node API's names** (`cluster_alloc_names`' form): the
cluster's facts (duplicated proposals as `dup` says, the bootstrap log's length, no data bound, snapshots on,
untraced) and its raft names' (the voters, the bootstrap log, raft's namespace `N.@"raft"`); the
committed operations at the bootstrap log, the cluster, the configuration of no entry; the bootstrap
log committed with its records; every id of `ids` at its durable state with its vacant slot. -/
theorem cluster_alloc_run (N : Namespace) (vs ids : List w64) (boot : List LogEntry) (dup : Bool)
    (E : CoPset)
    (HE : (↑(N .@ "raft") : CoPset) ⊆ E) :
    receiptBound GF ≤ 2 ^ 64 - 2 → vs ≠ [] → vs.Nodup → W64 0 ∉ vs → (vs.length : Int) < 2 ^ 62 →
    ids.Nodup → W64 0 ∉ ids → NormBoot boot →
    ⊢ |={E}=> ∃ γ : Cluster,
      ⌜γ.dup = dup ∧ γ.bootLen = boot.length ∧ γ.maxData = none ∧ ¬ clusterNoSnap γ ∧
        Cluster.trace γ = none⌝ ∗
      ⌜γ.raftNames.reCfg = GMap.listToSet vs ∧ γ.raftNames.reBoot = LogEntry.toEntries boot 0 ∧
        γ.raftNames.reNs = N.@"raft" ∧ γ.raftNames.reTrace = none ∧ γ.raftNames.maxData = none⌝ ∗
      ownCommittedOps (GF := GF) γ boot ∗ isCluster γ N ∗
      confAt γ 0 (Membership.simple (GMap.listToSet vs)) ∗
      isCommitted γ.raftNames γ.raftNames.reBoot ∗ logRecs γ.raftNames base0 γ.raftNames.reBoot ∗
      [∗list] id ∈ ids, raftState γ id
        (if boot = [] then RaftState.init else bootDurState γ.raftNames.reBoot) ∗ nodeVacant γ id := by
  intro Hrb Hne Hnd Hnz Hlen Hind Hinz HB
  unfold ownCommittedOps isCluster confAt Cluster.dup Cluster.bootLen Cluster.trace Cluster.maxData
    raftState nodeVacant clusterNoSnap Cluster.raftNames
  imod ApiImpl.cluster_alloc_normBoot (GF := GF) N vs ids boot dup E HE Hrb Hne Hnd Hnz Hlen Hind Hinz HB
    with ⟨%γ, %Hd, Hops, #Hcl, #Hca, #Hcb, #Hrecs, Hfs⟩
  imodintro
  iexists γ
  iframe Hops Hcl Hca Hcb Hrecs Hfs
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := Hd
  isplitr
  · ipureintro
    exact ⟨h1, by rw [h2, ApiImpl.toEntries_length], h4, by rw [h5]; decide, h3⟩
  ipureintro; exact ⟨h6, h2, h7, h3, h4⟩

end allocRunApi

end EtcdGrove
end Perennial

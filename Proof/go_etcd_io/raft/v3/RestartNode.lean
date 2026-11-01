/- Lean-first (no Rocq counterpart). -/
module

public import Spec.go_etcd_io.raft.v3.RestartNode
public import Spec.go_etcd_io.raft.v3.newNode
public import Spec.go_etcd_io.raft.v3.node__run
public import Proof.go_etcd_io.raft.v3.InvNodeRun
public import Proof.go_etcd_io.raft.v3.InvAdvance
import all Proof.go_etcd_io.raft.v3.InvNodeChan
public import Proof.go_etcd_io.raft.v3.InvRawnodeReady
public import Proof.go_etcd_io.raft.v3.InvApplyConf
public import Proof.go_etcd_io.raft.v3.InvBoot
public import Spec.go_etcd_io.raft.v3.RawNode__ProposeConfChange
public import Spec.go_etcd_io.raft.v3.NewRawNode
public import Proof.go_etcd_io.raft.v3.ApiVocab
import all Proof.go_etcd_io.raft.v3.InvNode
import Proof.go_etcd_io.raft.v3.InvApi
import Proof.go_etcd_io.raft.v3.InvApiView
import Proof.go_etcd_io.raft.v3.InvApiDec
import Proof.go_etcd_io.raft.v3.InvApiJoin
import all Proof.go_etcd_io.raft.v3.InvNodeRule
import Proof.go_etcd_io.raft.v3.SnapValidCert
import Proof.go_etcd_io.raft.v3.StepGhostMode
import Proof.go_etcd_io.raft.v3.InvStorageRead
import Proof.go_etcd_io.raft.v3.ConfchangeApiImpl
import Proof.go_etcd_io.raft.v3.ConfchangeApi

@[expose] public section

noncomputable section


namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-! ## The raw triple (internal: private to this file)

What the proof over raft's internals shows, from which the wrapper (below) derives the spec. Its documentation, as when it was the spec (until 2026-10-28):
-/

/-! Lean-first (no Rocq counterpart).

## `RestartNode(c)` (node.go:281)

`NewRawNode(c)` (its premises: a node of a new cluster, `Spec/NewRawNode.lean`) in a
`node` whose goroutine `run` it starts, for the cluster's term budget `bud`
(`budget_alloc`, `InvNode.lean`). It returns the node (`isNodeChan`, persistent: what
`Propose`, `Step`, `Tick` and `Ready` take) and the driver's token (`nodeDriverChan`, at
the empty committed log: what `node_ready_receive` and `Advance` take). Since 2026-10-10
also the cluster's proposed slices (`propDataInv`, allocated once with the raft ghost
state), which `isNodeChan` keeps with the commit invariant. Since 2026-10-15 (stage N) in either
mode (`md`, `NewRawNode`'s `rnInit`: statically `ownRaftGhost` at the initial state, dynamically
B5's `ownRaftGhostR` at `rinit c0`), and with the driver's view of the configuration
(`nodeCfg`, at index `0` and the initial configuration) for `ApplyConfChange` and `Advance`.

raft v3.7 (2026-10-16, stage R5): `NewRawNode`'s premises as they are now (the storage's
`InitialState` in `newRaft`'s D7 shape, the conf state's record `csm`; 2026-10-16, stage R6b: the
conf state's `AutoLeave` cell set or not, `csPts cs □ csm al`); **no proposed slices'
invariant** (D6: an entry's data is its bytes; until then `inv propDataN (propDataInv γ)`, which
`isNodeChan` kept).
-/

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- See the file header. (raft-final phase 1, 2026-10-29: over `NewRawNode`'s boot bundle, raft's
storage names `sn` and frame `R`/`R'`; until then raft's view of an empty storage with an
`InitialState` closure, and `NodeNames.snapIn`, deleted.) -/
private abbrev RestartNode.specRaw : Prop :=
  ∀ (γ : RaftNames) (md : RNMode) (bud : BudgetNames) (c : Loc) (cv : Config)
    (lok si : GoInterfaceOk) (sn : StorNames)
    -- (raft-final phase 2) the node's configuration names, allocated by the caller, so that the
    -- node's table entry (`nodeTabOk`) exists before the storage's contract is read
    (gdlm gcap gccq gcam glive : GName)
    (σ : StorState)
    (hs : HardStateM) (csm : ConfStateM) (R R' : IProp GF) (cs' : CCState),
  -- `NewRawNode`'s premises
  ConfigValid cv →
  cv.Logger' = interface.ok lok →
  cv.Storage' = interface.ok si →
  sint.Z cv.MaxInflightMsgs' < 2 ^ 62 →
  cv.DisableProposalForwarding' = false →
  -- `ReadOnlySafe` (2026-10-12)
  cv.ReadOnlyOption' = W64 0 →
  -- conf-change validation on (2026-10-13; `newRaft`'s premise)
  cv.DisableConfChangeValidation' = false →
  (cv.MaxCommittedSizePerReady' ≠ W64 0 ∨ cv.MaxSizePerMsg' ≠ W64 0) →
  cv.AsyncStorageWrites' = false →
  -- (2026-10-25, T-M M2b: pre-vote either way; 2026-10-17 to 2026-10-25 off in the dynamic mode,
  -- which did not model pre-candidates; until then off in either mode)
  -- (2026-11-01, durability stage I-6: a restart from a storage holding a log, `NewRawNode`'s
  -- premises as they are now: raft's view from the base, the attach record, the hard state
  -- restored, `Applied` within the committed part, any conf state `Restore` accepts. Until then an
  -- empty storage, an empty hard state, nothing applied, voters only.
  -- PORT(durability stage II): the ghost-state premises and the post below are still the empty
  -- start's (`rnInit`, `isCommitted γ []`, the configuration names at `0`, the driver at `[]`);
  -- stage II (d) restates them with `raft_restart` (`restartP`) and the wrapper.)
  LogIndicesOk σ.prev σ.ents → σ.pend = [] → σ.fr = uint.nat σ.prev.index' →
  uint.Z σ.fl ≤ uint.Z σ.prev.index' → σ.sg ≤ uint.nat σ.prev.index' →
  (∀ k t, σ.dt !! k = some t → k ≤ uint.nat σ.prev.index') →
  uint.Z σ.prev.index' + (σ.ents.length : Int) + 1 < 2 ^ 64 →
  AttachRec sn σ.prev σ.ents (uint.nat (committedAfter σ.prev hs))
    (max (uint.nat σ.prev.index') (uint.nat cv.Applied')) →
  (HsEmpty hs ∨ uint.Z σ.prev.index' ≤ uint.Z hs.Commit' ∧
    uint.Z hs.Commit' ≤ uint.Z σ.prev.index' + (σ.ents.length : Int)) →
  (cv.Applied' = W64 0 ∨ uint.Z σ.prev.index' ≤ uint.Z cv.Applied' ∧
    uint.Z cv.Applied' ≤ uint.Z (committedAfter σ.prev hs)) →
  -- (2026-10-16, stage R5) the conf state's record `csm`, as `NewRawNode`'s
  restoreM csm.VotersOutgoing' csm.Voters' csm.Learners' csm.LearnersNext' csm.AutoLeave' =
    some cs' →
  csm.Voters'.length + csm.VotersOutgoing'.length + csm.Learners'.length +
    csm.LearnersNext'.length ≤ 2 ^ 62 →
  -- (2026-10-29, stage U4: only in the static mode; a dynamic node, a newcomer, need not be one of
  -- the conf state's voters)
  (md = .static → γ.reCfg = GMap.listToSet csm.Voters') →
  (md = .static → cv.ID' ∈ csm.Voters') →
  -- (2026-10-25, T-M M2c: `StepDownOnRemoval` either way; 2026-10-15 to 2026-10-25 on in the dynamic
  -- mode)
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ c ↦ cv ∗ isLogger lok ∗ R ∗
      -- (raft-final phase 1) `NewRawNode`'s boot bundle (durability stage I-6: at the view's base
      -- and last index; raft's view made without the attach record, `sn.unrec`)
      (□ {{ R }} (App (Val #(methods si.ty go!"FirstIndex" si.v)) (Val #()))
         {{ RET (PairV #(W64 (uint.nat σ.prev.index' + 1)) #interface.nil); R }}) ∗
      (□ {{ R }} (App (Val #(methods si.ty go!"LastIndex" si.v)) (Val #()))
         {{ RET (PairV #(W64 (uint.nat σ.prev.index' + σ.ents.length)) #interface.nil); R }}) ∗
      (□ {{ R }} (App (Val #(methods si.ty go!"InitialState" si.v)) (Val #()))
         {{ (hp cs : Loc) (al : Bool), RET (PairV (PairV #hp #cs) #interface.nil);
            hsOpt hp hs ∗ csPts cs DFrac.discard csm al ∗
            |={⊤}=> isStorageD sn (interface.ok si) ∗ ownStorage sn.unrec (interface.ok si) σ ∗
              R' }}) ∗
      -- (2026-10-15, stage N) the ghost state in the mode `md` (`NewRawNode`'s `rnInit`; until
      -- then `ownRaftGhost γ cv.ID' initPState`, the static mode's)
      rnInit γ md cv.ID' (GMap.listToSet csm.Voters') ∗ isCommitted γ [] ∗
      -- the cluster's term budget
      inv budgetN (budgetInv bud) ∗ termLB bud (W64 0) ∗
      -- (D22 S-b′3, 2026-10-20) the storage's certificate link (`certLink`; raft-final phase 1: of
      -- the storage names, U8 v2)
      certLink γ sn ∗
      -- (raft-final phase 2) the configuration names' initial states
      monoListAuthOwn gdlm 1 ([] : List EntryM) ∗ monoListLbOwn gdlm ([] : List EntryM) ∗
      dghostVar gcap (DFrac.own 1) ((0 : Nat), cfgState (GMap.listToSet csm.Voters') ∅) ∗
      dghostVar gccq (DFrac.own 1) ((0 : Nat), cfgState (GMap.listToSet csm.Voters') ∅) ∗
      monoNatAuthOwn gcam 1 0 ∗ monoNatLbOwn gcam 0 ∗ dghostVar glive (DFrac.own 1) false }}
    (App (Val #(functions RestartNode [])) (Val #c))
  {{ (nd : GoInterface), RET #nd;
      ∃ (γn : NodeNames) (n : Loc),
        ⌜γn.raft = γ ∧ γn.bud = bud ∧ γn.stor = interface.ok si ∧ γn.mode = md ∧ γn.sn = sn ∧
         nd = interface.mkOk (go.GoType.PointerType node.ty) #n ∧
         γn.dlm = gdlm ∧ γn.cap = gcap ∧ γn.ccq = gccq ∧ γn.cam = gcam ∧ γn.live = glive⌝ ∗
        -- (raft-final phase 1) the frame `InitialState` gave back
        R' ∗
        isNodeChan γn cv.ID' n ∗ nodeDriverChan γn cv.ID' n [] hsZero ∗
        -- (2026-10-29, stage U9a) the client's half of `live`, for `Stop`
        nodeLiveRaw γn 1 ∗
        -- (2026-10-15, stage N) the driver's view of the configuration: the initial one
        nodeCfg γn 0 (cfgState (GMap.listToSet csm.Voters') ∅) }}

end spec

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `NewRawNode` (its result the node open, `rawNodeFresh`, closed here with the ghost state in
the mode `md`: 2026-10-16, stage R8b; until then `NewRawNode` closed it), `newNode`, then the
node's ghost state: the channels' hand-shakes (with `P := False` on those nobody sends on), the
tick channel's invariant (no credit yet), `dlv` and `rof`; `run` takes its halves. (Raft v3.7,
stage R5: `NewRawNode`'s premises over the conf state's record `csm` and D7's `InitialState`; no
proposed slices' invariant (D6).) -/
private theorem RestartNode.wp_raw
    (wp_NewRawNode : NewRawNode.spec (GF := GF) (hG := hG))
    (wp_newNode : newNode.spec (GF := GF) (hG := hG))
    (wp_node_run : node.run.spec (GF := GF) (hG := hG)) :
    RestartNode.specRaw (GF := GF) (hG := hG) := by
  -- PORT(durability stage II): `NewRawNode.spec` generalized (I-6: `rawNodeAt`); the raw triple to restate for a restart (I-2, I-6)
  sorry

end proof

/-! ## The spec, from the raw triple -/

namespace ApiImpl

section wrap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- Raft's log namespace is in the cluster's. -/
private theorem raftLogN_sub (γ : Cluster) (N : Namespace) (E : CoPset) (HE : ↑N ⊆ E)
    (HNs : γ.raft.reNs = N .@ "raft") : (↑(raftLogN γ.raft) : CoPset) ⊆ E := by
  intro p hp
  unfold raftLogN raftN at hp; rw [HNs] at hp
  exact HE p (nclose_subseteq N "raft" p (nclose_subseteq (N .@ "raft") "log" p hp))

/-- **A valid snapshot's certificates** (the API's `snapshotValid` read back at raft's level). -/
private theorem snapValid_raftCert (γ : Cluster) (N : Namespace) (E : CoPset) (HE : ↑N ⊆ E)
    (_HU : UniNames γ N) (sv : SnapshotM) :
    ⊢ clusterInv (GF := GF) γ N -∗ EtcdGrove.snapshotValid (GF := GF) γ sv ={E}=∗
      raftSnapCertD γ.raft (snapTrip sv sv.Metadata'.ConfState'.lists) := by
  iintro #Hci Hv
  unfold EtcdGrove.snapshotValid EtcdGrove.isCommittedLogLb EtcdGrove.confAt EtcdGrove.snapMade
  icases Hv with ⟨%l, %m, #Hlb, #Ha, #Hm, %Hp⟩
  obtain ⟨Hlen, -, Hlast, Hcs, H61, Hsz⟩ := Hp
  ihave %Hval := confAt_valid_impl γ l.length m $$ Ha
  ihave %Hres := confAtU_restorable γ l.length m $$ Ha
  iunfold confAtU at Ha
  icases Ha with ⟨%l2, %M, #Hlb2, #HM, %P2⟩
  obtain ⟨hk, c0, g, hm, hf⟩ := P2
  icases isCommittedLogLb_agree_impl γ l l2 $$ [Hlb Hlb2] with %Hcm
  · iframe Hlb Hlb2
  have Hfold : decFold M c0 l = some m := by
    rw [← List.take_length (l := l), take_eq_of_cmp l l2 l.length Hcm (Nat.le_refl _) hk]
    exact hf
  iunfold snapMadeU at Hm
  icases Hm with ⟨%gr, %K, %key, %Hk, #HK, -⟩
  obtain ⟨Hreg, HkK, Hmat⟩ := Hk
  have hm' := hm
  obtain ⟨⟨h0, -, hd, -, Hsok, -, -⟩, -⟩ := hm'
  ihave #Hci' := Hci
  iunfold clusterInv at Hci'
  icases Hci' with ⟨%HNs, #Hcinv, -, -⟩
  imod api_lb_committed γ N E HE l $$ Hci Hlb with ⟨%L, %HL, #HLc⟩
  have HD : (DynCfg.ofFold noDec (stOf c0) h0).fold M L = some (cfgOf m) := by
    rw [hm.fold _ hd M L, HL, Hfold]; rfl
  have HLlen : L.length = uint.nat sv.Metadata'.Index' := by rw [← Hlen, ← HL, strip_length]
  have HLlast : L.getLast?.map EntryM.Term' = some sv.Metadata'.Term' := by
    rw [← Hlast, ← HL]; unfold strip; rw [List.getLast?_map, Option.map_map]; rfl
  obtain ⟨hcv, hco, hcl, hcn, hal⟩ := Hcs
  unfold EtcdGrove.Membership.Valid memValid at Hval
  obtain ⟨Hz, Hni⟩ := Hres
  iapply raftSnapCertD_snapTrip γ.raft E L sv (cfgOf m) _ M gr K key
    (raftLogN_sub γ N E HE HNs) hd Hreg Hsok HLlen (by rw [HLlen, ← Hlen]; exact H61) HLlast
    hcv hco hcl hcn hal Hval.1
    (fun x hx h0x => Hz (by
      subst h0x
      simp only [Membership.ids, GMap.elem_of_union]
      rcases hx with h | h | h | h
      · exact .inl (.inl (.inl h))
      · exact .inl (.inl (.inr h))
      · exact .inl (.inr h)
      · exact .inr h))
    (fun x hx => Hni x hx) Hsz HD HkK (by rw [HLlen, ← Hlen]; exact Hmat.1) Hmat.2
    $$ Hcinv HLc HM HK

/-- Raft's reading of the contract's `Bnd`: compacting up to it is safe, of the storage's key's
names. (2026-11-01, durability stage I-4: keyed by the storage's key.) -/
private theorem storBnd_raftBnd (γ : Cluster) (K : GName) (sn : StorNames) (c : Nat) :
    ⊢ storKeyNames (GF := GF) K sn -∗ monoNatLbOwn sn.ga 0 -∗ EtcdGrove.storBnd γ K c -∗
      raftBnd sn c := by
  -- PORT(durability stage II): restated (I-4: keyed by `K`, `snapGiven` merged)
  sorry

/-- Raft's reading of the contract's `DL` for a valid snapshot: the node on the storage committed
up to its index, so raft certified the term there (or handed out a snapshot past it). (2026-11-01,
durability stage I-4: `nodeCommitLb`, keyed by the storage's key.) -/
private theorem storDL_raftDL (γ : Cluster) (K : GName) (sn : StorNames) (sv : SnapshotM) :
    ⊢ storKeyNames (GF := GF) K sn -∗ EtcdGrove.snapshotValid γ sv -∗
      EtcdGrove.nodeCommitLb γ K (uint.nat sv.Metadata'.Index') -∗
      raftDL sn (uint.nat sv.Metadata'.Index') sv.Metadata'.Term' := by
  -- PORT(durability stage II): restated (I-4: `nodeCommitLb` keyed by `K`)
  sorry

/-- **The certificate link of fresh storage names** (`certLink`): their `SV` pin the API's
`snapshotValid`, their snapshot pin raft's certificate. -/
private theorem certLink_make (γ : Cluster) (N : Namespace) (HU : UniNames γ N) (sn : StorNames) :
    ⊢ clusterInv (GF := GF) γ N -∗
      savedPredOwn sn.gsv DFrac.discard (EtcdGrove.snapshotValid (GF := GF) γ) -∗
      savedPredOwn sn.gk DFrac.discard (raftSnapCertD (GF := GF) γ.raft) -∗ certLink γ.raft sn := by
  iintro #Hci #Hsv #Hgk
  have HcN : raftCertN γ.raft = N := HU.2.2.1
  unfold certLink storCertOk
  isplitr
  · iintro !> %sv %E %HE Hc
    rw [HcN] at HE
    unfold svCert
    icases Hc with ⟨%SV, #Hp, #HSV⟩
    ihave #Heq := saved_pred_agree sn.gsv DFrac.discard DFrac.discard SV
      (EtcdGrove.snapshotValid (GF := GF) γ) sv $$ Hp Hsv
    ihave Hv : ▷ EtcdGrove.snapshotValid (GF := GF) γ sv $$ []
    · inext
      ihave Hiff := internalEq_iff _ _ $$ Heq
      icases Hiff with ⟨Hiff, -⟩
      iapply Hiff $$ HSV
    have : Timeless (EtcdGrove.snapshotValid (GF := GF) γ sv) := by
      have : ∀ s, Timeless (snapMadeU (GF := GF) γ s) := fun s => by
        unfold snapMadeU; infer_instance
      have : ∀ l, Timeless (isCommittedLogLb (GF := GF) γ l) := fun l => by
        unfold isCommittedLogLb; infer_instance
      unfold EtcdGrove.snapshotValid EtcdGrove.isCommittedLogLb EtcdGrove.confAt EtcdGrove.snapMade
      infer_instance
    icases Hv with >Hv
    iapply snapValid_raftCert γ N E HE HU sv $$ Hci Hv
  isplitr
  · iintro !> %k %E %HE Hc
    unfold ksnCert
    icases Hc with ⟨%P, #Hp, #HP⟩
    ihave #Heq := saved_pred_agree sn.gk DFrac.discard DFrac.discard P
      (raftSnapCertD (GF := GF) γ.raft) k $$ Hp Hgk
    ihave Hv : ▷ raftSnapCertD (GF := GF) γ.raft k $$ []
    · inext
      ihave Hiff := internalEq_iff _ _ $$ Heq
      icases Hiff with ⟨Hiff, -⟩
      iapply Hiff $$ HP
    icases Hv with >#Hv
    imodintro; iexact Hv
  · iintro !> %k %E %HE #Hc
    unfold ksnCert
    imodintro
    iexists raftSnapCertD γ.raft
    iframe Hgk
    imodintro; iexact Hc

/-- `RestartNode.spec` from the raw triple (2026-10-28, stage U4a): the node in the cluster's
dynamic mode (of the client's decisions, since the decision switch; until then the rule's), taking `MsgSnap`s (`snapIn`), its ghost state the dynamic one at the
initial state (`ownRaftGhostR_rinit`), its table entry inserted (`nodeTabOk`), its view at the
voters' membership. -/
private theorem wp_RestartNode_impl
    (hS : EtcdGrove.RestartNode.specRaw (GF := GF) (hG := hG)) :
    EtcdGrove.RestartNode.spec (GF := GF) (hG := hG) := by
  -- PORT(durability stage II): the spec restated (durability I-2/I-4/I-6/I-7: `nodeVacant`, the update over `raftState`, `restartStorage`)
  sorry

end wrap

end ApiImpl

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem RestartNode.wp_proof
    (wp_NewRawNode : NewRawNode.spec (GF := GF) (hG := hG))
    (wp_newNode : newNode.spec (GF := GF) (hG := hG))
    (wp_node_run : node.run.spec (GF := GF) (hG := hG)) :
    RestartNode.spec (GF := GF) (hG := hG) :=
  ApiImpl.wp_RestartNode_impl (RestartNode.wp_raw wp_NewRawNode wp_newNode wp_node_run)

end proof

end EtcdGrove
end Perennial

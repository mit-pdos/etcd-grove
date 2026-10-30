/- Lean-first (no Rocq counterpart), 2026-10-13; 2026-10-15 (stage N): the dynamic mode. -/
module

public import Spec.go_etcd_io.raft.v3.node__ApplyConfChange
public import Spec.go_etcd_io.raft.v3.raftpb.ConfChange__AsV2
public import Spec.go_etcd_io.raft.v3.raftpb.ConfChangeV2__AsV2
public import Proof.go_etcd_io.raft.v3.LemmasNodeR
public import Proof.go_etcd_io.raft.v3.FrameH
import all Proof.go_etcd_io.raft.v3.InvNodeChan
public import Proof.go_etcd_io.raft.v3.InvRawnodeReady
public import Proof.go_etcd_io.raft.v3.InvApplyConf
public import Proof.go_etcd_io.raft.v3.InvBoot
public import Spec.go_etcd_io.raft.v3.RawNode__ProposeConfChange
public import Spec.go_etcd_io.raft.v3.NewRawNode
import all Proof.go_etcd_io.raft.v3.InvNode
import Proof.go_etcd_io.raft.v3.InvApi
import Proof.go_etcd_io.raft.v3.InvApiView
import Proof.go_etcd_io.raft.v3.InvApiDec
import all Proof.go_etcd_io.raft.v3.InvNodeRule

@[expose] public section

noncomputable section


namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-! ## The raw triple (internal: private to this file)

What the proof over raft's internals shows, from which the wrapper (below) derives the spec. Its documentation, as when it was the spec (until 2026-10-28):
-/

/-! Lean-first (no Rocq counterpart).

## `node.ApplyConfChange(cc)` (node.go:556), 2026-10-13 (reconfiguration stage D)

From any goroutine: `cc.AsV2()` onto `confc` (`confcP`: its changes, read-only, keep the
voters and only drop learners -- `CCShrink`; until 2026-10-13 an unchanged configuration), which `run` applies (`raft.applyConfChange`, the ghost step inside,
`wp_rn_raft_applyConfChange`) and answers with the `ConfState` on `confstatec`
(`confstateP`), which this returns, by pointer. `n.done` never fires.

**Scope**, as `RawNode.ApplyConfChange`'s: a change whose model answer keeps the voters and
some of the learners (`CCShrink` of `ccV2Of o`), e.g. a `ConfChange` with `NodeId = 0`, or a
`RemoveNode` of a learner. The change is held read-only (`DFrac.discard`): `run` reads its `Changes`
on its own goroutine.

**Order with `Advance`** (`issues/raft-advance-before-applyconfchange.md`): an application
must apply a `Ready`'s conf-change entries before it calls `Advance` for that `Ready`, which
node.go's documentation does not say (it allows `Advance` while applying). For the changes
covered here the order does not matter (the configuration in use does not change), so no
premise; a configuration-changing `ApplyConfChange` will need one.

**The dynamic mode (2026-10-15, stage N).** In a node of the dynamic mode (`γ.mode`, from
`RestartNode`), any change the driver applies in order: the change of the next conf-change
entry `e` of the committed log `ds` it was handed (`dlvLb`), at position `k` past its
configuration index `ca` (`DynCCPreOp`: the decoder's change, which applies to its
configuration `cfg` with no `confchange` error and is no auto-leave joint configuration). The
driver's view `nodeCfg γ ca cfg` goes along with the change on `confc` (`confcP`) and comes back
on `confstatec` at `(k + 1, cs')` (`confstateP`, recognized by the answer slot `ccq`); the run
loop checks the premises against its `RawNode` (`runCfg_confc`) and applies the change there
(`StepR.applyConf`, a removed leader stepping down). The answer is the new configuration's
`ConfState` (`confstateOk`). A1 at `Advance` (`node.Advance.spec`) is what makes the order
matter.

**raft v3.7 (2026-10-16, stage R5).** `cc.AsV2()` is a `*pb.ConfChangeV2` (for a
`*ConfChangeV2`, `cc` itself), sent on `confc` read-only (`confcP`: `ownConfChangeV2 v □`, hence
`ownConfChangeI c □`); the answer is the `*pb.ConfState` `run`'s `applyConfChange` returned, owned
(`csPts csp 1 cs true`), its lists the record's (`confstateS`/`confstateOk` pure). Go returns
`nil` if `done` fires (2026-10-29, stage U9a: the node stopped, `nodeStoppedRaw`; until then it never
did).
-/

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- See the file header. -/
private abbrev node.ApplyConfChange.specRaw : Prop :=
  ∀ (γ : NodeNames) (id : w64) (n : Loc) (c : GoInterface) (o : ConfChangeIM)
    -- (2026-10-15, stage N) the dynamic mode's: the committed log the driver was handed (a
    -- lower bound of `run`'s), its view of the configuration, the conf entry applied (at
    -- position `k`) and the configuration it gives
    (ds : List EntryM) (ca : Nat) (cfg : CCState) (k : Nat) (e : EntryM)
    (cs' : CCState) (M : DecMap),
  -- the static mode (the voters fixed): a change that keeps the voters, drops learners
  (γ.mode = .static → CCShrink γ.raft.reCfg (ccV2Of o).1 (ccV2Of o).2) →
  -- the dynamic mode: the next committed conf entry's decoded change, which applies; (2026-10-28,
  -- the decision switch) over decisions recorded (`M`, `decLb`)
  (∀ dec c0 h0 h1, γ.mode = .dyn dec c0 h0 h1 →
    DynCCPreOp (effDec dec M) ds ca cfg (ccV2Of o) k e cs') →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNodeChan γ id n ∗
      ownConfChangeI c DFrac.discard (some o) ∗
      (⌜γ.mode = .static⌝ ∨ nodeCfg γ ca cfg ∗ dlvLb γ ds ∗ decLb γ.raft M) }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"ApplyConfChange")) (Val #c))
  {{ (csp : Loc) (cs : ConfStateM), RET #csp;
      -- (2026-10-16, stage R5) `applyConfChange`'s fresh `*pb.ConfState`, owned (`confstateP`;
      -- until then `csp ↦ cs` with the slices in `confstateS`/`confstateOk`)
      (csPts csp (DFrac.own 1) cs true ∗
        ((⌜γ.mode = .static⌝ ∗ ⌜confstateS γ cs⌝) ∨
         (⌜γ.mode.isDyn = true⌝ ∗ nodeCfg γ (k + 1) cs' ∗ ⌜confstateOk cs cs'.cfg⌝))) ∨
      -- (2026-10-29, stage U9a) or the node stopped (`done` fired): `nil`
      (⌜csp = null⌝ ∗ nodeStoppedRaw γ) }}

end spec

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

set_option hygiene false in
/-- (2026-10-29, stage U9a) The second `select` of `ApplyConfChange`: the `*ConfState` from
`confstatec` (`confstateP`, recognized by the answer slot's half the driver kept, `Hkeep`), or
`done`: the node stopped, `nil`. Reached after the send on `confc` or after `done` fired instead. -/
local macro "apply_cc_recv" : tactic => `(tactic| (
  wp_auto_lc 2
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists Loc, inferInstance, inferInstance, inferInstance, inferInstance,
      nv.confstatec', γ.confstatec
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply isHandshake_isChan $$ Hconfstatec
    iapply handshake_receive_au γ.confstatec nv.confstatec' (confstateP γ) iprop(True) _
      $$ [$(frameH `Hlc1) $(frameH `Hlc2)] Hconfstatec []
    · itrivial
    inext
    iintro %csv Hcs
    wp_auto
    iunfold confstateP at Hcs
    icases Hcs with ⟨%csm, Hcs, (%Hs | ⟨%Hd, %w, Hcap, Hq, #Hlb, %Hok⟩)⟩
    · icases Hkeep with (%Hs' | ⟨%Hd', -⟩)
      · iapply HΦ $$ %csv %csm
        ileft
        iframe Hcs
        ileft
        ipureintro; exact Hs
      · rw [Hs.1] at Hd'; cases Hd'
    · icases Hkeep with (%Hs' | ⟨%Hd', Hq'⟩)
      · rw [Hs'] at Hd; cases Hd
      ihave %Heq := dghostVar_agree _ _ _ _ _ $$ Hq Hq'
      subst Heq
      iapply HΦ $$ %csv %csm
      ileft
      iframe Hcs
      iright
      isplitr
      · ipureintro; exact Hd
      isplitl
      rotate_left
      · ipureintro; exact Hok
      unfold nodeCfg
      iframe Hcap Hlb
      iexists (k + 1, cs')
      iframe Hq Hq'
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, nv.done', γ.done
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply ownBroadcastChan_is_chan _ _ _ _ $$ Hdone
    -- (2026-10-29, stage U9a) the node stopped: `cs` is still `nil`
    iapply node_done_recv_au γ nv.done' _ $$ Hdone
    iintro #Hst
    wp_auto
    iapply HΦ $$ %null %(ConfStateM.mk [] [] [] [] false)
    iright
    iframe Hst
    ipureintro; rfl
  iapply BigAndL.bigAndL_nil.2
  itrivial
  ))

set_option hygiene false in
/-- The rest of `ApplyConfChange` once `AsV2` gave the `ConfChangeV2` `v2` (`#Hch`), in both
arms (`ConfChange`, `ConfChangeV2`): the payload by the mode, the send on `confc`, the receive
on `confstatec` (`apply_cc_recv`). -/
local macro "apply_cc_send" : tactic => `(tactic| (
    ihave Hpay : iprop(|==> (confcP γ v2 ∗ (⌜γ.mode = .static⌝ ∨ (⌜γ.mode.isDyn = true⌝ ∗
        dghostVar γ.ccq (DFrac.own (1 : Qp).half) (k + 1, cs'))))) $$ [HR]
    · rcases Hmode with hm | ⟨dec, c0, h0, h1, hm⟩
      · imodintro
        isplitl []
        · unfold confcP
          iexists _
          iframe Hch
          ileft
          ipureintro
          exact ⟨hm, Hshr hm⟩
        ileft; ipureintro; exact hm
      · icases HR with (%Hs | ⟨Hcfg, #Hdlb, #HdM⟩)
        · rw [hm] at Hs; cases Hs
        unfold nodeCfg
        icases Hcfg with ⟨Hcap, ⟨%x, Hq1, Hq2⟩, #Hcamlb⟩
        imod dghostVar_update_halves (k + 1, cs') γ.ccq x x $$ Hq1 Hq2 with ⟨Hq1, Hq2⟩
        imodintro
        isplitl [Hcap Hq1]
        · unfold confcP
          iexists _
          iframe Hch
          iright
          iexists ds, ca, cfg, k, e, cs', M
          iunfold dlvLb at Hdlb
          icases Hdlb with ⟨#Hdlb, -⟩
          iframe Hdlb Hcap Hq1 HdM
          ipureintro
          refine ⟨by rw [hm]; rfl, fun dec' c0' h0' h1' hm' => ?_⟩
          exact Hdyn dec' c0' h0' h1' hm'
        iright
        iframe Hq2
        ipureintro; rw [hm]; rfl
    imod Hpay with ⟨HP, Hkeep⟩
    wp_auto_lc 3
    wp_apply_core chan.wp_select_blocking
    iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.blockingClausePre]
      iexists Loc, inferInstance, inferInstance, inferInstance, inferInstance,
        nv.confc', γ.confc, _
      isplitr
      · ipureintro; exact ⟨rfl, rfl⟩
      isplitr
      · iapply isHandshake_isChan $$ Hconfc
      iapply handshake_send_au γ.confc nv.confc' _ (confcP γ) iprop(True)
        $$ [$(frameH `Hlc1) $(frameH `Hlc2) $(frameH `Hlc3)] Hconfc HP
      inext
      iintro -
      apply_cc_recv
    iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.blockingClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, nv.done', γ.done
      isplitr
      · ipureintro; rfl
      isplitr
      · iapply ownBroadcastChan_is_chan _ _ _ _ $$ Hdone
      -- (2026-10-29, stage U9a) the node stopped before the send: on to the second `select`
      iapply node_done_recv_au γ nv.done' _ $$ Hdone
      iintro -
      iclear Hlc1 Hlc2 Hlc3 HP
      apply_cc_recv
    iapply BigAndL.bigAndL_nil.2
    itrivial
  ))

/-- `cc.AsV2()` on `confc` (`confcP`, by the mode; the driver keeps the answer slot's other
half), then the `*ConfState` from `confstatec` (`confstateP`), or `nil` once `n.done` fired. (Raft v3.7,
stage R5: `confc` carries `AsV2`'s pointer: a `ConfChange`'s fresh `ConfChangeV2`
(`m.asV2`), frozen (`ownConfChangeV2_persist`), or a `ConfChangeV2` itself, read-only already; the
answer a `*pb.ConfState` owned, `csPts csp 1 cs true`.) -/
private theorem node.ApplyConfChange.wp_raw
    (wp_ConfChange_AsV2 : raftpb.ConfChange.AsV2.spec (GF := GF) (hG := hG))
    (wp_ConfChangeV2_AsV2 : raftpb.ConfChangeV2.AsV2.spec (GF := GF) (hG := hG)) :
    node.ApplyConfChange.specRaw (GF := GF) (hG := hG) := by
  intro γ id n c o ds ca cfg k e cs' M Hshr Hdyn
  wp_start as ⟨#Hnode, Hc, HR⟩
  ihave #Hnode' := Hnode
  open_node Hnode'
  have Hmode : γ.mode = .static ∨ ∃ dec c0 h0 h1, γ.mode = .dyn dec c0 h0 h1 := by
    cases h : γ.mode with
    | static => exact .inl rfl
    | dyn dec c0 h0 h1 => exact .inr ⟨dec, c0, h0, h1, rfl⟩
  rcases o with m | m
  · simp only [ownConfChangeI]
    icases Hc with ⟨%p, %Hcv, Hc⟩
    subst Hcv
    wp_auto
    wp_apply +noauto wp_ConfChange_AsV2 p DFrac.discard m $$ [Hc] as %v2 ⟨-, Hch⟩
    · iexact Hc
    imod ownConfChangeV2_persist $$ Hch with #Hch
    -- the payload, by the mode; the driver keeps the answer slot's other half
    apply_cc_send
  · simp only [ownConfChangeI]
    icases Hc with ⟨%v2, %Hcv, #Hch⟩
    subst Hcv
    wp_auto
    wp_apply +noauto wp_ConfChangeV2_AsV2
    -- the payload, by the mode; the driver keeps the answer slot's other half
    apply_cc_send

end proof

/-! ## The spec, from the raw triple -/

namespace ApiImpl

section wrap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- (2026-10-30, stage R3) The configuration after the applied entry: past the skipped ones, then
the decision at `k`. -/
private theorem confAt_applied (γ : Cluster) (l : List LogEntry) (k : Nat) (e : LogEntry)
    (v : ConfigView) (o' : ConfChangeIM) (m' : Membership) :
    v.applied ≤ k → l[k]? = some e → Membership.applyChange o' v.membership = some m' →
    ⊢ EtcdGrove.isCommittedLogLb (GF := GF) γ l -∗ confAt γ v.applied v.membership -∗
      skippedIn γ l v.applied k -∗ confDecided γ k (.apply o') -∗ confAt γ (k + 1) m' := by
  intro hk he hap
  have hkl : k < l.length := (List.getElem?_eq_some_iff.mp he).1
  iintro Hl Hc Hs Hd
  ihave Hck : confAt (GF := GF) γ k v.membership $$ [Hl Hc Hs]
  · iapply confAt_skipped γ l v.applied k v.membership hk (by omega)
    iframe Hl Hc Hs
  ihave Hx : (∃ m'', ⌜(ConfDecision.apply o').step v.membership = some m''⌝ ∗ confAt (GF := GF) γ (k + 1) m'') $$ [Hck Hd]
  · iapply confAt_decided γ k v.membership (.apply o')
    iframe Hck Hd
  icases Hx with ⟨%m'', %Hm, Hc'⟩
  simp only [ConfDecision.step] at Hm
  rw [hap] at Hm
  cases Hm
  iexact Hc'

/-- `node.ApplyConfChange.spec` from the raw triple (2026-10-28, stage U4a; the conf-change
decision switch): the cluster's decoder decides nothing, so the node's decisions are the recorded
ones: the decision at `k` to apply `o'` (`confDecidedU`'s element) and the skips of the conf entries
between the view and `k` (`skippedIn`), joined into one lower bound of the map (`decLb`) at which the
node's decoder gives the change at `k` and rejects the entries before it (`DynCCPreOp`). -/
private theorem node.wp_ApplyConfChange_impl
    (hA : EtcdGrove.node.ApplyConfChange.specRaw (GF := GF) (hG := hG)) :
    EtcdGrove.node.ApplyConfChange.spec (GF := GF) (hG := hG) := by
  unfold EtcdGrove.node.ApplyConfChange.spec EtcdGrove.Cluster EtcdGrove.Membership.applyChange
    EtcdGrove.deliveredLogLb EtcdGrove.isCluster EtcdGrove.confDecided EtcdGrove.isNode
    EtcdGrove.nodeConfig EtcdGrove.nodeStopped
  intro n γ N id c o o' l k e v m' Hk He Hcc Hap' Hap
  haveI := skippedIn_persistent (GF := GF) γ l v.applied k
  haveI := ApiImpl.confAtU_persistent (GF := GF) γ v.applied v.membership
  iintro %Φ ⟨#Hinit, -, #Hcl, #Hdec, Hcc0, ⟨Hcfg, #Hca⟩, #Hdl, #Hsk⟩ HΦ
  -- (2026-10-30, stage R3) the configuration after the entry
  ihave Hlc0 : EtcdGrove.isCommittedLogLb (GF := GF) γ l $$ []
  · unfold EtcdGrove.isCommittedLogLb
    iunfold ApiImpl.deliveredLogLb at Hdl
    icases Hdl with ⟨-, #Hlc⟩
    iexact Hlc
  ihave Hca1 : EtcdGrove.confAt (GF := GF) γ v.applied v.membership $$ []
  · unfold EtcdGrove.confAt; iexact Hca
  ihave Hdec1 : EtcdGrove.confDecided (GF := GF) γ k (.apply o') $$ []
  · unfold EtcdGrove.confDecided; iexact Hdec
  ihave Hca' := confAt_applied γ l k e v o' m' Hk He Hap' $$ Hlc0 Hca1 Hsk Hdec1
  iunfold isClusterU at Hcl
  icases Hcl with ⟨%Hu, -⟩
  obtain ⟨⟨c0, gd, Hmd0⟩, -, -⟩ := Hu
  -- the decisions: the one at `k`, the skips before it
  iunfold confDecidedU at Hdec
  icases Hdec with ⟨%ld, %ed, %md, %md', -, #Hel, -⟩
  ihave #HS := decElem_decLb γ k _ $$ Hel
  iunfold EtcdGrove.skippedIn at Hsk
  simp only [EtcdGrove.confDecided]
  icases skipped_range_decLb γ l v.applied k $$ Hsk with ⟨%Mk, #HMk, %PMk⟩
  icases decLb_compat γ.raft Mk (GMap.singleton k (ConfDecision.apply o').toOpt) $$ [HMk HS] with %Hcp
  · iframe HMk HS
  ihave #HU := decLb_union γ.raft Mk (GMap.singleton k (ConfDecision.apply o').toOpt) $$ [HMk HS]
  · iframe HMk HS
  iunfold nodeConfig at Hcfg
  icases Hcfg with ⟨%γn, %id1, %Hf, #Hn1, #Htab1, Hcf⟩
  obtain ⟨Hnok, Hdy, Hgood⟩ := Hf
  iunfold deliveredLogLb at Hdl
  icases Hdl with ⟨⟨%γn2, %id2, %ds, %Hf2, #Hn2, #Htab2, #Hlb⟩, #Hlc⟩
  obtain ⟨Hnok2, Hds⟩ := Hf2
  icases isNode_id_agree γn γn2 id1 id2 n $$ Hn1 Hn2 with %Hid
  subst Hid
  obtain ⟨h0, h1, Hmd1⟩ := Hmd0.mode
  have Hmd : γn.mode = .dyn noDec (stOf c0) h0 h1 := by rw [Hnok.2.2.2, Hmd1]
  have Hdy2 : γn2.mode.isDyn = true := by rw [Hnok2.2.2.2, Hmd1]; rfl
  icases Htab2 with (%Hc | #Htab2)
  · rw [Hdy2] at Hc; cases Hc
  icases nodeTabOk_agree γ id1 γn γn2 $$ Htab1 Htab2 with %Hnm
  ihave #Hlb' := dlvLb_names γn2 γn Hnm.symm ds $$ Hlb
  -- the entry, as raft has it
  have He' : (strip ds)[k]? = some e := by rw [Hds]; exact He
  unfold strip at He'
  rw [List.getElem?_map] at He'
  obtain ⟨eM, HeM, HeMe⟩ : ∃ eM, ds[k]? = some eM ∧ LogEntry.ofEntryM eM = e := by
    cases h : ds[k]? with
    | none => rw [h] at He'; cases He'
    | some eM => rw [h] at He'; exact ⟨eM, rfl, Option.some.inj He'⟩
  obtain ⟨Hs', Hg'⟩ := memApply_some Hgood Hap'
  obtain ⟨Hs, -⟩ := memApply_some Hgood Hap
  let U : DecMap := Mk ∪ GMap.singleton k (ConfDecision.apply o').toOpt
  have HUk : U.lookup k = some (some o') := by
    apply DecCompat.sub_right Hcp
    show (GMap.singleton k (ConfDecision.apply o').toOpt : DecMap) !! k = some (some o')
    simp [GMap.singleton, GMap.lookup_insert_eq_iff, ConfDecision.toOpt]
  have Hpre : DynCCPreOp (effDec noDec U) ds v.applied (stOf v.membership) (ccV2Of o) k eM
      (stOf m') := by
    refine ⟨Hk, (List.getElem?_eq_some_iff.mp HeM).1, HeM, ?_, ?_, ⟨ccV2Of o', ?_, Hs'⟩, Hs⟩
    · rw [← HeMe] at Hcc; exact Hcc
    · intro k' e' h1 h2 he hc
      have hl' : l[k']? = some (LogEntry.ofEntryM e') := by
        rw [← Hds]; unfold strip; rw [List.getElem?_map, he]; rfl
      have hk' : U.lookup k' = some none :=
        DecCompat.sub_left Mk _ k' none (PMk k' (LogEntry.ofEntryM e') h1 h2 hl' hc)
      have hlen : (ds.take k').length = k' := by
        have := (List.getElem?_eq_some_iff.mp he).1
        rw [List.length_take]; omega
      show (U.lookup (ds.take k').length).map ccDecOf = some .reject
      rw [hlen, hk']; rfl
    · have hlen : (ds.take k).length = k := by
        have := (List.getElem?_eq_some_iff.mp HeM).1
        rw [List.length_take]; omega
      show (U.lookup (ds.take k).length).map ccDecOf = some (.apply (ccV2Of o'))
      rw [hlen, HUk]; rfl
  iapply (hA γn id1 n c o ds v.applied (stOf v.membership) k eM (stOf m') U
    (fun h => by rw [Hmd] at h; cases h)
    (fun dec c0' h0' h1' h => by rw [Hmd] at h; cases h; exact Hpre)) $$ [Hcc0 Hcf]
  · iframe Hinit Hn1 Hcc0
    iright; iframe Hcf Hlb'
    rw [Hnok.1]; iexact HU
  iintro !> %csp %cs Hpost
  icases Hpost with (⟨Hcs, Hor⟩ | ⟨%Hnull, #Hst⟩)
  rotate_left
  · -- (2026-10-29, stage U9a) the node stopped
    iapply HΦ $$ %csp %cs
    iright
    isplitr
    · ipureintro; exact Hnull
    unfold nodeStopped
    iexists γn, id1
    iframe Hn1 Hst Htab1
    ipureintro; exact Hnok
  icases Hor with (⟨%Hst', -⟩ | ⟨-, Hcf', %Hok⟩)
  · exfalso; rw [Hmd] at Hst'; cases Hst'
  iapply HΦ
  ileft
  iframe Hcs
  isplitl [Hcf' Hca']
  · isplitl [Hcf']
    · unfold nodeConfig
      iexists γn, id1
      iframe Hn1 Htab1 Hcf'
      ipureintro; exact ⟨Hnok, Hdy, Hg'⟩
    iunfold EtcdGrove.confAt at Hca'
    iexact Hca'
  ipureintro
  have := confStateIs_of_ok cs _ Hok
  rw [stOf_cfg, memOf_cfgOf] at this
  exact this

end wrap

end ApiImpl

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem node.ApplyConfChange.wp_proof
    (wp_ConfChange_AsV2 : raftpb.ConfChange.AsV2.spec (GF := GF) (hG := hG))
    (wp_ConfChangeV2_AsV2 : raftpb.ConfChangeV2.AsV2.spec (GF := GF) (hG := hG)) :
    node.ApplyConfChange.spec (GF := GF) (hG := hG) :=
  ApiImpl.node.wp_ApplyConfChange_impl
    (node.ApplyConfChange.wp_raw wp_ConfChange_AsV2 wp_ConfChangeV2_AsV2)

end proof

end EtcdGrove
end Perennial

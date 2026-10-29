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
import Proof.go_etcd_io.raft.v3.InvApiDyn
import Proof.go_etcd_io.raft.v3.InvApiRule
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
`nil` if `done` fires first, which it never does.
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
      csPts csp (DFrac.own 1) cs true ∗
      ((⌜γ.mode = .static⌝ ∗ ⌜confstateS γ cs⌝) ∨
       (⌜γ.mode.isDyn = true⌝ ∗ nodeCfg γ (k + 1) cs' ∗ ⌜confstateOk cs cs'.cfg⌝)) }}

end spec

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

set_option hygiene false in
/-- The rest of `ApplyConfChange` once `AsV2` gave the `ConfChangeV2` `v2` (`#Hch`), in both
arms (`ConfChange`, `ConfChangeV2`): the payload by the mode, the send on `confc`, the receive
on `confstatec`. -/
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
          unfold dlvLb
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
            iframe Hcs
            ileft
            ipureintro; exact Hs
          · rw [Hs.1] at Hd'; cases Hd'
        · icases Hkeep with (%Hs' | ⟨%Hd', Hq'⟩)
          · rw [Hs'] at Hd; cases Hd
          ihave %Heq := dghostVar_agree _ _ _ _ _ $$ Hq Hq'
          subst Heq
          iapply HΦ $$ %csv %csm
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
        · iapply isHandshake_isChan $$ Hdone
        iapply handshake_false_recv_au γ.done nv.done' $$ [$(frameH `Hlc1) $(frameH `Hlc2)] Hdone
      iapply BigAndL.bigAndL_nil.2
      itrivial
    iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.blockingClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, nv.done', γ.done
      isplitr
      · ipureintro; rfl
      isplitr
      · iapply isHandshake_isChan $$ Hdone
      iapply handshake_false_recv_au γ.done nv.done' $$ [$(frameH `Hlc1) $(frameH `Hlc2)] Hdone
    iapply BigAndL.bigAndL_nil.2
    itrivial
  ))

/-- `cc.AsV2()` on `confc` (`confcP`, by the mode; the driver keeps the answer slot's other
half), then the `*ConfState` from `confstatec` (`confstateP`); `n.done` never fires. (Raft v3.7,
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

/-- `node.ApplyConfChange.spec` from the raw triple (`node`'s names hidden behind the API's). -/
private theorem node.wp_ApplyConfChange_impl
    (hA : EtcdGrove.node.ApplyConfChange.specRaw (GF := GF) (hG := hG)) :
    EtcdGrove.node.ApplyConfChange.spec (GF := GF) (hG := hG) := by
  unfold EtcdGrove.node.ApplyConfChange.spec EtcdGrove.Cluster EtcdGrove.isNode EtcdGrove.isStaticCluster
  intro n γ N id vs so c o Hsh
  iintro %Φ ⟨#Hinit, #Hnode, #Hst, Hcc⟩ HΦ
  iunfold isStaticCluster at Hst
  icases Hst with ⟨%Hsn, -⟩
  obtain ⟨Hcfg, -, -, -, Hγm, -, -, -, -, -, Hnd, -⟩ := Hsn
  iunfold isNode at Hnode
  icases Hnode with ⟨%γn, %Hnok, #Hrn, -⟩
  obtain ⟨Hγr, -, -, Hmd, -⟩ := Hnok
  rw [Hγm, RNMode.all_self] at Hmd
  iapply (hA γn id n c o [] 0 (cfgState ∅ ∅) 0 ⟨W64 0, W64 0, W32 0, []⟩ (cfgState ∅ ∅) ∅
    (fun _ => by rw [Hγr, Hcfg]; exact Hsh) (fun dec c0 h0 h1 h => by rw [Hmd] at h; cases h))
    $$ [Hcc]
  · iframe Hinit Hrn Hcc
    ileft; ipureintro; exact Hmd
  iintro !> %csp %cs ⟨Hcs, Hor⟩
  icases Hor with (⟨-, %Hs⟩ | ⟨%Hd, -⟩)
  · iapply HΦ
    iframe Hcs
    ipureintro
    obtain ⟨h1, h2, h3, h4, h5⟩ := Hs
    rw [Hγr, Hcfg] at h1 h2
    exact ⟨h1.trans (perm_elements_listToSet' vs Hnd).symm,
      fun k hk h => h2 k hk ((GMap.elem_of_list_to_set _ _).2 h), h3, h4, h5⟩
  · exfalso; rw [Hmd] at Hd; cases Hd

/-- `node.ApplyConfChange.dynamicSpec` from the raw triple (`node`'s names hidden behind the API's). -/
private theorem node.wp_ApplyConfChange_dynamic_impl
    (hA : EtcdGrove.node.ApplyConfChange.specRaw (GF := GF) (hG := hG)) :
    EtcdGrove.node.ApplyConfChange.dynamicSpec (GF := GF) (hG := hG) := by
  unfold EtcdGrove.node.ApplyConfChange.dynamicSpec EtcdGrove.Cluster EtcdGrove.Membership.applyChange EtcdGrove.deliveredLogLb EtcdGrove.isDynamicCluster EtcdGrove.isNode EtcdGrove.nodeConfig
  intro n γ N id c0 decode c o o' l k e v m' Hk He Hcc Hno Hdec Hap' Hap Hal
  iintro %Φ ⟨#Hinit, -, #Hdc, Hcc0, Hcfg, #Hdl⟩ HΦ
  iunfold isDynamicCluster at Hdc
  icases Hdc with ⟨%Hdn, -⟩
  iunfold nodeConfig at Hcfg
  icases Hcfg with ⟨%γn, %id1, %Hf, #Hn1, #Htab1, Hcf⟩
  obtain ⟨Hnok, Hdy, Hgood⟩ := Hf
  iunfold deliveredLogLb at Hdl
  icases Hdl with ⟨⟨%γn2, %id2, %ds, %Hf2, #Hn2, #Htab2, #Hlb⟩, -⟩
  obtain ⟨Hnok2, Hds⟩ := Hf2
  icases isNode_id_agree γn γn2 id1 id2 n $$ Hn1 Hn2 with %Hid
  subst Hid
  have Hdy2 := Hdn.isDyn Hnok2
  icases Htab2 with (%Hc | #Htab2)
  · rw [Hdy2] at Hc; cases Hc
  icases nodeTabOk_agree γ id1 γn γn2 $$ Htab1 Htab2 with %Hnm
  ihave #Hlb' := dlvLb_names γn2 γn Hnm.symm ds $$ Hlb
  obtain ⟨h0, h1, Hmd⟩ := Hdn.node Hnok
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
  have Hpre : DynCCPreOp (decOf decode) ds v.applied (stOf v.membership) (ccV2Of o) k eM
      (stOf m') := by
    refine ⟨Hk, (List.getElem?_eq_some_iff.mp HeM).1, HeM, ?_, ?_, ⟨ccV2Of o', ?_, Hs'⟩, Hs, Hal⟩
    · rw [← HeMe] at Hcc; exact Hcc
    · refine NoConfIn.noUndec ?_
      intro k' e' h1 h2 he hc
      apply Hno k' (LogEntry.ofEntryM e') h1 h2
      · rw [← Hds]; unfold strip; rw [List.getElem?_map, he]; rfl
      · exact hc
    · unfold decOf
      have : strip (ds.take k) = l.take k := by
        rw [← Hds]; unfold strip; rw [List.map_take]
      rw [this, HeMe, Hdec]; rfl
  iapply (hA γn id1 n c o ds v.applied (stOf v.membership) k eM (stOf m') ∅
    (fun h => by rw [Hmd] at h; cases h)
    (fun dec c0' h0' h1' h => by rw [Hmd] at h; cases h; rw [effDec_empty]; exact Hpre)) $$ [Hcc0 Hcf]
  · iframe Hinit Hn1 Hcc0
    iright; iframe Hcf Hlb'
    iapply decLb_empty
  iintro !> %csp %cs ⟨Hcs, Hor⟩
  icases Hor with (⟨%Hst, -⟩ | ⟨-, Hcf', %Hok⟩)
  · exfalso; rw [Hmd] at Hst; cases Hst
  iapply HΦ
  iframe Hcs
  isplitl [Hcf']
  · unfold nodeConfig
    iexists γn, id1
    iframe Hn1 Htab1 Hcf'
    ipureintro; exact ⟨Hnok, Hdy, Hg'⟩
  ipureintro
  have := confStateIs_of_ok cs _ Hok
  rw [stOf_cfg, memOf_cfgOf] at this
  exact this

/-- `node.ApplyConfChange.unifiedSpec` from the raw triple (2026-10-28, stage U4a): the recorded
decision is the rule's at the committed prefix (`confDecidedU`), so the node's decoder (the rule's,
`ConfRule.toDec`) gives the decided change there (`DynCCPreOp`). -/
private theorem node.wp_ApplyConfChange_unified_impl
    (hA : EtcdGrove.node.ApplyConfChange.specRaw (GF := GF) (hG := hG)) :
    EtcdGrove.node.ApplyConfChange.unifiedSpec (GF := GF) (hG := hG) := by
  unfold EtcdGrove.node.ApplyConfChange.unifiedSpec EtcdGrove.Cluster EtcdGrove.Membership.applyChange
    EtcdGrove.deliveredLogLb EtcdGrove.isCluster EtcdGrove.confDecided EtcdGrove.isNode
    EtcdGrove.nodeConfig
  intro n γ N id c o o' l k e v m' Hk He Hcc Hno Hap' Hap Hal
  iintro %Φ ⟨#Hinit, -, -, #Hdec, Hcc0, Hcfg, #Hdl⟩ HΦ
  iunfold confDecidedU at Hdec
  icases Hdec with ⟨%ld, #Hld, %Pd⟩
  obtain ⟨ed, Hed, -, r, c0, Hmr, md, -, Hfd, -, Hdm⟩ := Pd
  iunfold nodeConfig at Hcfg
  icases Hcfg with ⟨%γn, %id1, %Hf, #Hn1, #Htab1, Hcf⟩
  obtain ⟨Hnok, Hdy, Hgood⟩ := Hf
  iunfold deliveredLogLb at Hdl
  icases Hdl with ⟨⟨%γn2, %id2, %ds, %Hf2, #Hn2, #Htab2, #Hlb⟩, #Hlc⟩
  obtain ⟨Hnok2, Hds⟩ := Hf2
  icases isNode_id_agree γn γn2 id1 id2 n $$ Hn1 Hn2 with %Hid
  subst Hid
  obtain ⟨h0, h1, Hmd0⟩ := Hmr.mode
  have Hmd : γn.mode = .dyn (r.toDec c0) (stOf c0) h0 h1 := by rw [Hnok.2.2.2.1, Hmd0]
  have Hdy2 : γn2.mode.isDyn = true := by rw [Hnok2.2.2.2.1, Hmd0]; rfl
  icases Htab2 with (%Hc | #Htab2)
  · rw [Hdy2] at Hc; cases Hc
  icases nodeTabOk_agree γ id1 γn γn2 $$ Htab1 Htab2 with %Hnm
  ihave #Hlb' := dlvLb_names γn2 γn Hnm.symm ds $$ Hlb
  icases isCommittedLogLb_agree_impl γ l ld $$ [Hlc Hld] with %Hcmp
  · iframe Hlc Hld
  have hkl : k < l.length := (List.getElem?_eq_some_iff.mp He).1
  have hkd : k < ld.length := (List.getElem?_eq_some_iff.mp Hed).1
  have Htk : l.take k = ld.take k := take_eq_of_cmp l ld k Hcmp (by omega) (by omega)
  have Hee : e = ed := by
    have := getElem?_eq_of_cmp l ld k Hcmp hkl hkd
    rw [He, Hed] at this; exact Option.some.inj this
  subst Hee
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
  -- the decision: the rule's at the committed prefix
  have Hst : strip (ds.take k) = ld.take k := by
    rw [← Htk, ← Hds]; unfold strip; rw [List.map_take]
  have Hdecd : (r.toDec c0) (ds.take k) eM = some (.apply (ccV2Of o')) := by
    rw [ConfRule.toDec_at r c0 md (ds.take k) eM (by rw [Hst]; exact Hfd), Hst, HeMe]
    cases hr : r (ld.take k) md e with
    | none => rw [hr] at Hdm; exact (Hdm : False).elim
    | some o1 =>
      rw [hr] at Hdm
      show some (CCDecision.apply (ccV2Of o1)) = _
      rw [show ccV2Of o1 = ccV2Of o' from Hdm]
  have Hpre : DynCCPreOp (r.toDec c0) ds v.applied (stOf v.membership) (ccV2Of o) k eM
      (stOf m') := by
    refine ⟨Hk, (List.getElem?_eq_some_iff.mp HeM).1, HeM, ?_, ?_, ⟨ccV2Of o', Hdecd, Hs'⟩, Hs, Hal⟩
    · rw [← HeMe] at Hcc; exact Hcc
    · refine NoConfIn.noUndec ?_
      intro k' e' h1 h2 he hc
      apply Hno k' (LogEntry.ofEntryM e') h1 h2
      · rw [← Hds]; unfold strip; rw [List.getElem?_map, he]; rfl
      · exact hc
  iapply (hA γn id1 n c o ds v.applied (stOf v.membership) k eM (stOf m') ∅
    (fun h => by rw [Hmd] at h; cases h)
    (fun dec c0' h0' h1' h => by rw [Hmd] at h; cases h; rw [effDec_empty]; exact Hpre)) $$ [Hcc0 Hcf]
  · iframe Hinit Hn1 Hcc0
    iright; iframe Hcf Hlb'
    iapply decLb_empty
  iintro !> %csp %cs ⟨Hcs, Hor⟩
  icases Hor with (⟨%Hst', -⟩ | ⟨-, Hcf', %Hok⟩)
  · exfalso; rw [Hmd] at Hst'; cases Hst'
  iapply HΦ
  iframe Hcs
  isplitl [Hcf']
  · unfold nodeConfig
    iexists γn, id1
    iframe Hn1 Htab1 Hcf'
    ipureintro; exact ⟨Hnok, Hdy, Hg'⟩
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
  ApiImpl.node.wp_ApplyConfChange_impl (node.ApplyConfChange.wp_raw wp_ConfChange_AsV2 wp_ConfChangeV2_AsV2)

theorem node.ApplyConfChange.wp_proof_dynamic
    (wp_ConfChange_AsV2 : raftpb.ConfChange.AsV2.spec (GF := GF) (hG := hG))
    (wp_ConfChangeV2_AsV2 : raftpb.ConfChangeV2.AsV2.spec (GF := GF) (hG := hG)) :
    node.ApplyConfChange.dynamicSpec (GF := GF) (hG := hG) :=
  ApiImpl.node.wp_ApplyConfChange_dynamic_impl (node.ApplyConfChange.wp_raw wp_ConfChange_AsV2 wp_ConfChangeV2_AsV2)

theorem node.ApplyConfChange.wp_proof_unified
    (wp_ConfChange_AsV2 : raftpb.ConfChange.AsV2.spec (GF := GF) (hG := hG))
    (wp_ConfChangeV2_AsV2 : raftpb.ConfChangeV2.AsV2.spec (GF := GF) (hG := hG)) :
    node.ApplyConfChange.unifiedSpec (GF := GF) (hG := hG) :=
  ApiImpl.node.wp_ApplyConfChange_unified_impl
    (node.ApplyConfChange.wp_raw wp_ConfChange_AsV2 wp_ConfChangeV2_AsV2)

end proof

end EtcdGrove
end Perennial

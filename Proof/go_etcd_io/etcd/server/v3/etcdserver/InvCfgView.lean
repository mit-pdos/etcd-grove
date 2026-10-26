/-
**The driver's configuration view at the server** (D43 M3, 2026-10-25; `notes/membership-plan.md`,
M3). In raft's dynamic mode the application owns its view of raft's configuration (`nodeCfg`:
the index of the last applied conf entry and the configuration) and applies every conf entry of
the committed log handed out, in order, before `Advance` (A1). At the server the view is the raft
loop's while it drives raft and the apply thread's while it applies a batch with a conf entry
(`raftNode.start` hands it over with the `toApply`; the second `notifyc` send gives it back,
`NotifyC.lean`).

- `srvDec`: the server's decoder (raft's `dec`), a `ConfChange` entry's bytes as
  `pbutil.MustUnmarshal` reads them (`ccDecodeV1`), as `AsV2` makes them.
- `srvCfgView γn pre L`: the view after the committed log `pre ++ L`, every conf entry of it
  applied, the configuration the voters' simple one (no change in M3's scope changes it).
- `raftApplyCCDyn γn n`: raft's `node.ApplyConfChange` in the dynamic mode, as the server calls
  it (`applyConfChange`, its axiom); `srvRaftNodeDyn s γn` the server's node meeting it.
- `ccStepB_of_raftOk`: a change `ccRaftOk` admits (an `AddNode` of a voter, or of `0`) leaves the
  voters' simple configuration as it is, within raft's size bound (moved here from
  `NodeBridge.lean`, with `ccShrink_of_raftOk`).
Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRequest
public import Proof.go_etcd_io.raft.v3.InvNode
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.NotifyC

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- **The server's conf-change decoder** (raft's dynamic mode's `dec`): a `ConfChange` entry's
change, `AsV2`'s; none for any other entry (the server's policy commits no `ConfChangeV2`,
`srvCCPolicy`). -/
def srvDec : CCDec := fun _ e =>
  if e.Type' = W32 1 then (ccDecodeV1 e.Data').map (fun m => ccV2Of (.v1 m)) else none

/-- **A change `ccRaftOk` admits leaves the voters as they are** (`CCShrink`, the static mode's
premise of `node.ApplyConfChange`; audit phase B3, 2026-10-18): an `AddNode` of a voter
(`makeVoter` of a voter), or of the node `0` (skipped), on a non-empty configuration. -/
theorem ccShrink_of_raftOk (cfg : GSet w64) (cm : CCV1M) (h : ccRaftOk cfg cm) :
    CCShrink cfg (ccV2Of (.v1 cm)).1 (ccV2Of (.v1 cm)).2 := by
  obtain ⟨ht, k, hk, hid⟩ := h
  have hne : cfg ≠ ∅ := by
    intro he
    rw [he] at hk
    have := (GMap.elem_of_gset _ _).1 hk
    simp at this
  rcases hid with hid | hid0
  · by_cases h0 : cm.nodeId = W64 0
    · exact CCNoop.shrink (ccApplyM_v1_noop cfg cm h0 hne)
    · intro lrn Hd
      refine ⟨lrn, GMap.subseteq_refl _, ?_⟩
      have hin : cm.nodeId ∈ cfg := by rw [hid]; exact hk
      have hL : cm.nodeId ∉ lrn := fun h' => Hd _ h' hin
      have hc : ({ Type' := cm.type, NodeId' := cm.nodeId } : ConfChangeSingleM) =
          addNodeCC cm.nodeId := by rw [ht]
      show ccApplyM (W32 0) [{ Type' := cm.type, NodeId' := cm.nodeId }] (cfgState cfg lrn) =
        some (cfgState cfg lrn)
      apply ccApplyM_single
      rw [hc]
      have := simpleM_cfgState_addNode cfg lrn cm.nodeId h0 hL Hd
      rw [GMap.insert_id _ _ _ ((GMap.elem_of_gset _ _).1 hin)] at this
      exact this
  · exact CCNoop.shrink (ccApplyM_v1_noop cfg cm hid0 hne)

/-- **A change `ccRaftOk` admits is a no-op step** (`ccStepB`) on the voters' simple
configuration, within raft's bound on the tracked ids. -/
theorem ccStepB_of_raftOk (V : GSet w64) (cm : CCV1M) (h : ccRaftOk V cm)
    (hsz : GMap.size (cfgState V ∅).cfg.ids < 2 ^ 62) :
    ccStepB (ccV2Of (.v1 cm)) (cfgState V ∅) = some (cfgState V ∅) := by
  obtain ⟨lrn', hsub, happ⟩ := ccShrink_of_raftOk V cm h ∅
    (fun k hk => absurd hk (by rw [GMap.elem_of_empty]; exact id))
  have hl : lrn' = ∅ := GMap.set_eq fun x => by
    rw [GMap.elem_of_empty]
    exact ⟨fun hx => by have := (GMap.elem_of_subseteq _ _).1 hsub x hx; rwa [GMap.elem_of_empty] at this,
      False.elim⟩
  subst hl
  unfold ccStepB
  rw [happ, Option.bind_some, ite_eq_left hsz]

/-- The pure part of the view: after the log `D`, the configuration index `ca` past every conf
entry of it, the configuration the voters' simple one, within raft's bounds. -/
def srvCfgOk (V : GSet w64) (D : List EntryM) (ca : Nat) (cfg : CCState) : Prop :=
  ca ≤ D.length ∧ NoConfIn D ca D.length ∧ cfg = cfgState V ∅ ∧ CfgOk cfg

/-- The view at the start: nothing handed out, the voters' configuration. -/
theorem srvCfgOk_nil (V : GSet w64) (h : CfgOk (cfgState V ∅)) :
    srvCfgOk V [] 0 (cfgState V ∅) :=
  ⟨Nat.le_refl _, fun _ _ _ h2 _ => absurd h2 (by simp), rfl, h⟩

/-- An entry that is no conf entry keeps the view. -/
theorem srvCfgOk_snoc_noConf {V : GSet w64} {D : List EntryM} {ca : Nat} {cfg : CCState}
    (h : srvCfgOk V D ca cfg) (m : EntryM) (hm : ¬ IsConfEnt m) :
    srvCfgOk V (D ++ [m]) ca cfg := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨by simp; omega, ?_, h3, h4⟩
  intro k e hk1 hk2 he
  rw [List.length_append, List.length_singleton] at hk2
  by_cases hk : k < D.length
  · rw [List.getElem?_append_left hk] at he
    exact h2 k e hk1 hk he
  · have hk' : k = D.length := by omega
    subst hk'
    rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self] at he
    simp only [List.getElem?_cons_zero, Option.some.injEq] at he
    subst he
    exact hm

/-- **A conf entry of the server's, applied**: the entry `m` after `D`, a `ConfChange` whose bytes
decode to a change `applyConfChange` takes (`ccApplyOk`), is the next conf entry of any log
extending `D ++ [m]`, and both changes etcd may hand raft for it (the entry's, or with `NodeId`
`0`) meet raft's premise at the server's decoder (`DynCCPreOp`, leaving the configuration); the
view after it is at `(|D| + 1, cfg)`. -/
theorem srvCfgOk_cc {V : GSet w64} {D : List EntryM} {ca : Nat} {cfg : CCState}
    (h : srvCfgOk V D ca cfg) (m : EntryM) (rest : List EntryM) (cm : CCV1M)
    (Hty : m.Type' = W32 1) (Hdec : ccDecodeV1 m.Data' = some cm) (Hcm : ccApplyOk V cm) :
    (DynCCPreOp srvDec (D ++ m :: rest) ca cfg (ccV2Of (.v1 cm)) D.length m cfg ∧
      DynCCPreOp srvDec (D ++ m :: rest) ca cfg (ccV2Of (.v1 { cm with nodeId := W64 0 }))
        D.length m cfg) ∧
    srvCfgOk V (D ++ [m]) (D.length + 1) cfg := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨ht, hin, -⟩ := Hcm
  have hsz : GMap.size (cfgState V ∅).cfg.ids < 2 ^ 62 := by rw [← h3]; exact h4.2.2
  have hs1 : ccStepB (ccV2Of (.v1 cm)) cfg = some cfg := by
    rw [h3]; exact ccStepB_of_raftOk V cm ⟨ht, cm.nodeId, hin, .inl rfl⟩ hsz
  have hs0 : ccStepB (ccV2Of (.v1 { cm with nodeId := W64 0 })) cfg = some cfg := by
    rw [h3]; exact ccStepB_of_raftOk V _ ⟨ht, cm.nodeId, hin, .inr rfl⟩ hsz
  have hal : cfg.cfg.autoLeave = false := by rw [h3]; rfl
  have hk : (D ++ m :: rest)[D.length]? = some m := by
    rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]; rfl
  have hnc : NoConfIn (D ++ m :: rest) ca D.length :=
    NoConfIn_prefix ⟨m :: rest, rfl⟩ (Nat.le_refl _) h2
  have hdec : srvDec ((D ++ m :: rest).take D.length) m = some (ccV2Of (.v1 cm)) := by
    unfold srvDec
    rw [ite_eq_left Hty, Hdec]; rfl
  have hlt : D.length < (D ++ m :: rest).length := by simp
  refine ⟨⟨⟨h1, hlt, hk, .inl Hty, hnc, ⟨_, hdec, hs1⟩, hs1, hal⟩,
    ⟨h1, hlt, hk, .inl Hty, hnc, ⟨_, hdec, hs1⟩, hs0, hal⟩⟩, ?_⟩
  refine ⟨by simp, fun _ _ h1 h2 _ => absurd h2 (by simp at h1 ⊢; omega), h3, h4⟩

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The driver's view after the committed log `pre ++ L`** (raft's dynamic mode; see the file
header): raft's `nodeCfg` at `(ca, cfg)` with `srvCfgOk` at raft's voters. -/
def srvCfgView (γn : NodeNames) (pre L : List EntryModel) : IProp GF :=
  iprop(∃ (ca : Nat) (cfg : CCState), nodeCfg γn ca cfg ∗
    ⌜srvCfgOk γn.raft.reCfg ((pre ++ L).map EntryModel.toM) ca cfg⌝)

/-- **Raft's `ApplyConfChange` in the dynamic mode, as the server calls it** (persistent; the
dynamic case of `node.ApplyConfChange.spec`): of a v1 change, read-only, the next conf entry's
at position `k` of the committed log `ds` handed out (`DynCCPreOp`, at the node's decoder), with
the driver's view, it returns the new `*ConfState`, owned, and the view at `(k + 1, cs')`. -/
def raftApplyCCDyn (γn : NodeNames) (n : GoInterface) : IProp GF :=
  iprop(∃ ni : GoInterfaceOk, ⌜n = GoInterface.ok ni⌝ ∗ ⌜γn.mode.isDyn = true⌝ ∗
    □ (∀ (c : GoInterface) (cm : CCV1M) (ds : List EntryM) (ca : Nat) (cfg : CCState) (k : Nat)
        (e : EntryM) (cs' : CCState),
      ⌜∀ dec c0 h0 h1, γn.mode = .dyn dec c0 h0 h1 →
        DynCCPreOp dec ds ca cfg (ccV2Of (.v1 cm)) k e cs'⌝ -∗
      {{ ownCCI c DFrac.discard (some (.v1 cm)) ∗ nodeCfg γn ca cfg ∗ dlvLb γn ds }}
        (App (Val #(methods ni.ty go!"ApplyConfChange" ni.v)) (Val #c))
      {{ (csp : Loc), RET #csp; (∃ cs : ConfStateM, csPts csp (DFrac.own 1) cs true) ∗
          nodeCfg γn (k + 1) cs' }}))

instance raftApplyCCDyn_persistent (γn : NodeNames) (n : GoInterface) :
    Persistent (raftApplyCCDyn (GF := GF) γn n) := by
  unfold raftApplyCCDyn; infer_instance

end defs

section addr
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The server `s`'s raft node in the dynamic mode** (persistent): `s.r`'s `Node` meets
`raftApplyCCDyn`. -/
def srvRaftNodeDyn (s : Loc) (γn : NodeNames) : IProp GF :=
  iprop(∃ n : GoInterface, srvNodeAddr s ↦□ n ∗ raftApplyCCDyn γn n)

instance srvRaftNodeDyn_persistent (s : Loc) (γn : NodeNames) :
    Persistent (srvRaftNodeDyn (GF := GF) s γn) := by
  unfold srvRaftNodeDyn; infer_instance

end addr

section apply
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The apply thread's view, optional** (`apply`, `applyEntries`, `applyAll`): `none` (raft's
static mode, or a batch with no conf entry: the raft loop keeps the view), or the view after the
log `L` the apply thread has applied, at the node's names. -/
def dvView (γs : ServerRaftNames) (dv : Option NodeNames) (L : List EntryModel) : IProp GF :=
  match dv with
  | none => iprop(True)
  | some γn => srvCfgView γn γs.pre L

/-- What the apply thread holds of the node for a batch with a view (persistent): the dynamic
contract and the committed log handed out through the batch `L`. -/
def dvRes (s : Loc) (γs : ServerRaftNames) (dv : Option NodeNames) (L : List EntryModel) :
    IProp GF :=
  match dv with
  | none => iprop(True)
  | some γn => iprop(srvRaftNodeDyn s γn ∗ dlvLb γn (srvLogOf γs L))

instance dvRes_persistent (s : Loc) (γs : ServerRaftNames) (dv : Option NodeNames)
    (L : List EntryModel) : Persistent (dvRes (GF := GF) s γs dv L) := by
  unfold dvRes; split <;> infer_instance

/-- **The premise on a batch's view**: without one, raft's static mode or no conf entry; with
one, no entry at or below the consistent index `c` (no replay: Go hands a replayed conf change to
no one), the node raft's and in the dynamic mode at the server's decoder. -/
def dvOk (γs : ServerRaftNames) (dv : Option NodeNames) (c f0 : w64) (ms : List EntryModel) :
    Prop :=
  (dv = none → γs.raft.reDyn = none ∨ ∀ m, m ∈ ms → m.typ ≠ W32 1) ∧
  ∀ γn, dv = some γn → uint.Z c < uint.Z f0 ∧ γn.raft = γs.raft ∧
    ∃ c0 h0 h1, γn.mode = .dyn srvDec c0 h0 h1

/-- The axiom `applyConfChange`'s dynamic resources (its precondition's): with a view, the node's
dynamic contract, the driver's `nodeCfg γn ca cfg` and the committed log `ds` handed out. -/
def dvCCPre (s : Loc) (dv : Option NodeNames) (ca : Nat) (cfg : CCState) (ds : List EntryM) :
    IProp GF :=
  match dv with
  | none => iprop(True)
  | some γn => iprop(srvRaftNodeDyn s γn ∗ nodeCfg γn ca cfg ∗ dlvLb γn ds)

/-- The axiom's dynamic answer: with a view, `nodeCfg γn (k + 1) cs'`. -/
def dvCCPost (dv : Option NodeNames) (k : Nat) (cs' : CCState) : IProp GF :=
  match dv with
  | none => iprop(True)
  | some γn => nodeCfg γn (k + 1) cs'

/-- A normal entry keeps the view. -/
theorem dvView_normal (γs : ServerRaftNames) (dv : Option NodeNames) (L : List EntryModel)
    (m : EntryModel) (hm : m.typ = W32 0) :
    dvView (GF := GF) γs dv L ⊢ dvView γs dv (L ++ [m]) := by
  unfold dvView
  rcases dv with _ | γn
  · exact .rfl
  · unfold srvCfgView
    iintro ⟨%ca, %cfg, Hc, %Hok⟩
    iexists ca, cfg
    iframe Hc
    ipureintro
    rw [← List.append_assoc, List.map_append]
    refine srvCfgOk_snoc_noConf Hok _ ?_
    unfold IsConfEnt
    simp only [EntryModel.toM, hm]
    intro h
    rcases h with h | h <;> simp at h

/-- **A conf entry, at the view** (`applyConfChange`'s call): the view and the node's give the
axiom's dynamic resources at `(ca, cfg)`, its premise (both changes Go may hand raft, at the entry's
position `|srvLogOf γs L|` of the committed log handed out), and back from its answer the view
after the entry. -/
theorem dvView_cc (s : Loc) (γs : ServerRaftNames) (dv : Option NodeNames)
    (L rest : List EntryModel) (m : EntryModel) (cm : CCV1M)
    (Hty : m.typ = W32 1) (Hdec : ccDecodeV1 m.data = some cm)
    (Hcm : ccApplyOk γs.raft.reCfg cm) (Hraft : ∀ γn, dv = some γn → γn.raft = γs.raft) :
    dvView (GF := GF) γs dv L ∗ dvRes s γs dv (L ++ m :: rest) ⊢
      ∃ (ca : Nat) (cfg : CCState), dvCCPre s dv ca cfg (srvLogOf γs (L ++ m :: rest)) ∗
        ⌜∀ γn, dv = some γn →
          DynCCPreOp srvDec (srvLogOf γs (L ++ m :: rest)) ca cfg (ccV2Of (.v1 cm))
            (srvLogOf γs L).length m.toM cfg ∧
          DynCCPreOp srvDec (srvLogOf γs (L ++ m :: rest)) ca cfg
            (ccV2Of (.v1 { cm with nodeId := W64 0 })) (srvLogOf γs L).length m.toM cfg⌝ ∗
        (dvCCPost dv (srvLogOf γs L).length cfg -∗ dvView γs dv (L ++ [m])) := by
  unfold dvView dvRes dvCCPre dvCCPost
  rcases dv with _ | γn
  · iintro -
    iexists 0, cfgState ∅ ∅
    isplitr
    · itrivial
    isplitr
    · ipureintro; intro γn h; cases h
    iintro -
    itrivial
  · unfold srvCfgView
    iintro ⟨⟨%ca, %cfg, Hc, %Hok⟩, #Hn, #Hd⟩
    have Hr := Hraft γn rfl
    have Hcm' : ccApplyOk γn.raft.reCfg cm := by rw [Hr]; exact Hcm
    have hlog : srvLogOf γs (L ++ m :: rest) =
        (γs.pre ++ L).map EntryModel.toM ++ m.toM :: rest.map EntryModel.toM := by
      simp [srvLogOf]
    have hlen : (srvLogOf γs L).length = ((γs.pre ++ L).map EntryModel.toM).length := rfl
    obtain ⟨⟨H1, H0⟩, Hpost⟩ := srvCfgOk_cc Hok m.toM (rest.map EntryModel.toM) cm Hty Hdec Hcm'
    iexists ca, cfg
    dsimp only
    iframe Hn Hc Hd
    isplitr
    · ipureintro
      intro γn' h
      cases h
      rw [hlog, hlen]
      exact ⟨H1, H0⟩
    iintro Hc'
    iexists (srvLogOf γs L).length + 1, cfg
    iframe Hc'
    ipureintro
    rw [hlen, ← List.append_assoc, List.map_append]
    exact Hpost

end apply

end EtcdGrove
end Perennial

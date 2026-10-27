/-
**The driver's configuration view at the server** (D43 M3, 2026-10-25; `notes/membership-plan.md`,
M3). In raft's dynamic mode the application owns its view of raft's configuration (`nodeCfg`:
the index of the last applied conf entry and the configuration) and applies every conf entry of
the committed log handed out, in order, before `Advance` (A1). At the server the view is the raft
loop's while it drives raft and the apply thread's while it applies a batch with a conf entry
(`raftNode.start` hands it over with the `toApply`; the second `notifyc` send gives it back,
`NotifyC.lean`).

- `srvDec c0 boot`: the server's decoder (raft's `dec`), a `ConfChange` entry's bytes as
  `pbutil.MustUnmarshal` reads them (`ccDecodeV1`), the change as `applyConfChange` hands it to
  raft after the log before it (D43 M5d: `ccRaftEff`, `NodeId` `0` when it does not validate),
  as `AsV2` makes it.
- `srvCfgView γn pre L`: the view after the committed log `pre ++ L`, every conf entry of it
  applied, the configuration a simple one of raft's voters less the members a `RemoveNode` of
  the log removed (D43 M5d; until then the voters themselves).
- `raftApplyCCDyn γn n`: raft's `node.ApplyConfChange` in the dynamic mode, as the server calls
  it (`applyConfChange`, its axiom); `srvRaftNodeDyn s γn` the server's node meeting it.
- `ccStepB_of_raftOk`: a change `ccRaftOk` admits (an `AddNode` of a voter, or of `0`) leaves the
  voters' simple configuration as it is, within raft's size bound (moved here from
  `NodeBridge.lean`, with `ccShrink_of_raftOk`).
Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRequest
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRest
public import Proof.go_etcd_io.raft.v3.InvNode
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.NotifyC

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section pure
variable [FfiSyntax]

/-- **The server's conf-change decoder** (raft's dynamic mode's `dec`; D43 M5d, 2026-10-26: aware
of the log before the entry): a `ConfChange` entry's change as `applyConfChange` hands it to raft,
`AsV2`'s: the change if it validates against the member buckets the log before it leaves
(`restModel` from the start's consistent index `c0` and the boot log `boot`), else with `NodeId`
`0` (`ccRaftEff`); none for any other entry (the server's policy commits no `ConfChangeV2`,
`srvCCPolicy`). Until M5d the change itself (every change the policy admitted left raft's
configuration as it was). -/
def srvDec (c0 : w64) (boot : List EntryM) : CCDec := fun pre e =>
  if e.Type' = W32 1 then
    (ccDecodeV1 e.Data').map (fun m =>
      ccV2Of (.v1 (membership.ccRaftEff (restModel c0 boot (pre.map EntryModel.ofM)).bk m)))
  else none

/-- The log `D` has a `RemoveNode` of `x` (a `ConfChange` entry). -/
def RemovedIn (D : List EntryM) (x : w64) : Prop :=
  ∃ (p : Nat) (e : EntryM) (cc : CCV1M), D[p]? = some e ∧ e.Type' = W32 1 ∧
    ccDecodeV1 e.Data' = some cc ∧ cc.type = W32 1 ∧ cc.nodeId = x

theorem RemovedIn_snoc {D : List EntryM} {x : w64} (h : RemovedIn D x) (m : EntryM) :
    RemovedIn (D ++ [m]) x := by
  obtain ⟨p, e, cc, hp, h1, h2, h3, h4⟩ := h
  exact ⟨p, e, cc, by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hp).1]; exact hp,
    h1, h2, h3, h4⟩

/-- **The dynamic mode's positional policy on a log `D`** (D43 M5d, the user's decision; the pure
part of `srvDynLog`): every conf entry decodes to an `AddNode` at a position below the boot log's
length `nb` (the boot entries) or a `RemoveNode` at or after it, never of the local member
`lid`. -/
def srvDynPol (nb : Nat) (lid : w64) (D : List EntryM) : Prop :=
  ∀ (p : Nat) (e : EntryM) (cc : CCV1M), D[p]? = some e → e.Type' ≠ W32 0 →
    ccDecodeV1 e.Data' = some cc →
    (cc.type = W32 0 → p < nb) ∧ (cc.type = W32 1 → nb ≤ p ∧ cc.nodeId ≠ lid)

/-- One conf change applied keeps `CfgOk`. -/
theorem ccStepB_cfgOk {op : CCOp} {s s' : CCState} (h : ccStepB op s = some s') (hs : CfgOk s) :
    CfgOk s' := by
  unfold ccStepB at h
  cases ha : ccApplyM op.1 op.2 s with
  | none => rw [ha] at h; cases h
  | some s1 =>
    rw [ha, Option.bind_some] at h
    split at h
    · rename_i hb; cases h; exact (ccApplyM_overlap ha hs hb).2
    · cases h

/-- A v1 change of the node `0` is a no-op on a non-empty voters' configuration. -/
theorem ccStepB_noop0 (W : GSet w64) (m : CCV1M) (h0 : m.nodeId = W64 0) (hne : W ≠ ∅)
    (hsz : GMap.size (cfgState W ∅).cfg.ids < 2 ^ 62) :
    ccStepB (ccV2Of (.v1 m)) (cfgState W ∅) = some (cfgState W ∅) := by
  unfold ccStepB
  rw [ccApplyM_v1_noop W m h0 hne ∅ (fun k hk => absurd hk (GMap.not_elem_of_empty _)),
    Option.bind_some, ite_eq_left hsz]

theorem gset_elem_delete (W : GSet w64) (y x : w64) :
    x ∈ (GMap.delete y W : GSet w64) ↔ x ≠ y ∧ x ∈ W := by
  rw [GMap.elem_of_gset, GMap.elem_of_gset]
  by_cases h : y = x
  · subst h; rw [GMap.lookup_delete]; simp
  · rw [GMap.lookup_delete_ne _ h]
    exact ⟨fun h' => ⟨fun e => h e.symm, h'⟩, fun h' => h'.2⟩

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
entry of it, the configuration a voters' simple one, within raft's bounds (D43 M5d, 2026-10-26:
voters `W` of `V`, each voter of `V` out of `W` removed by a `RemoveNode` of `D`; until then `V`
itself). -/
def srvCfgOk (V : GSet w64) (D : List EntryM) (ca : Nat) (cfg : CCState) : Prop :=
  ca ≤ D.length ∧ NoConfIn D ca D.length ∧
  (∃ W : GSet w64, cfg = cfgState W ∅ ∧ (∀ x, x ∈ W → x ∈ V) ∧
    ∀ x, x ∈ V → x ∉ W → RemovedIn D x) ∧ CfgOk cfg

/-- The view at the start: nothing handed out, the voters' configuration. -/
theorem srvCfgOk_nil (V : GSet w64) (h : CfgOk (cfgState V ∅)) :
    srvCfgOk V [] 0 (cfgState V ∅) :=
  ⟨Nat.le_refl _, fun _ _ _ h2 _ => absurd h2 (by simp),
    ⟨V, rfl, fun _ h => h, fun _ h1 h2 => absurd h1 h2⟩, h⟩

/-- An entry that is no conf entry keeps the view. -/
theorem srvCfgOk_snoc_noConf {V : GSet w64} {D : List EntryM} {ca : Nat} {cfg : CCState}
    (h : srvCfgOk V D ca cfg) (m : EntryM) (hm : ¬ IsConfEnt m) :
    srvCfgOk V (D ++ [m]) ca cfg := by
  obtain ⟨h1, h2, ⟨W, h3, h3a, h3b⟩, h4⟩ := h
  refine ⟨by simp; omega, ?_, ⟨W, h3, h3a, fun x hx hw => RemovedIn_snoc (h3b x hx hw) m⟩, h4⟩
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

/-- **A conf entry of the server's, applied** (D43 M5d, 2026-10-26: with `RemoveNode`): the entry
`m` after `D`, a `ConfChange` whose bytes decode to a change `applyConfChange` takes (an `AddNode`
of `ccApplyOk`, or a `RemoveNode` of a member of `V`), under the dynamic mode's positional policy
(`srvDynPol`, the local member `lid` a member of `V`), is the next conf entry of any log extending
`D ++ [m]`, and the change etcd hands raft for it (`ccRaftEff` at the member buckets after `D`,
the server's decoder's) meets raft's premise (`DynCCPreOp`); the view after it is at
`(|D| + 1, cs')`. -/
theorem srvCfgOk_cc {V : GSet w64} {D : List EntryM} {ca : Nat} {cfg : CCState}
    (h : srvCfgOk V D ca cfg) (c0 : w64) (boot : List EntryM) (m : EntryM) (rest : List EntryM)
    (cm : CCV1M) (Hty : m.Type' = W32 1) (Hdec : ccDecodeV1 m.Data' = some cm)
    (nb : Nat) (lid : w64) (hpol : srvDynPol nb lid (D ++ [m])) (hlid : lid ∈ V)
    (Hcm : ccApplyOk V cm ∨ (cm.type = W32 1 ∧ cm.nodeId ∈ V)) :
    ∃ cs' : CCState,
      DynCCPreOp (srvDec c0 boot) (D ++ m :: rest) ca cfg
        (ccV2Of (.v1 (membership.ccRaftEff (restModel c0 boot (D.map EntryModel.ofM)).bk cm)))
        D.length m cs' ∧
      srvCfgOk V (D ++ [m]) (D.length + 1) cs' := by
  obtain ⟨h1, h2, ⟨W, hcfg, hWV, hrem⟩, hok⟩ := h
  have hmD : (D ++ [m])[D.length]? = some m := by simp
  have hpm := hpol D.length m cm hmD (by rw [Hty]; simp) Hdec
  have hpD : ∀ p e cc, D[p]? = some e → e.Type' ≠ W32 0 → ccDecodeV1 e.Data' = some cc →
      (cc.type = W32 0 → p < nb) ∧ (cc.type = W32 1 → nb ≤ p ∧ cc.nodeId ≠ lid) :=
    fun p e cc hp => hpol p e cc (by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hp).1]; exact hp)
  -- the local member stays a voter: no `RemoveNode` of it
  have hlW : lid ∈ W := by
    refine Classical.byContradiction fun hl => ?_
    obtain ⟨p, e, cc, hp, het, hd, hct, hcn⟩ := hrem lid hlid hl
    exact ((hpD p e cc hp (by rw [het]; simp) hd).2 hct).2 hcn
  have hne : W ≠ ∅ := fun he => by rw [he] at hlW; exact GMap.not_elem_of_empty _ hlW
  have hsz : GMap.size (cfgState W ∅).cfg.ids < 2 ^ 62 := by rw [← hcfg]; exact hok.2.2
  have hszW : GMap.size W < 2 ^ 62 := by rw [cfgState_empty_ids] at hsz; exact hsz
  generalize heff : membership.ccRaftEff (restModel c0 boot (D.map EntryModel.ofM)).bk cm = eff
  have hEff : eff = cm ∨ eff = { cm with nodeId := W64 0 } := by
    rw [← heff]; unfold membership.ccRaftEff; split
    · exact .inl rfl
    · exact .inr rfl
  -- the step: the voters `W'`
  have hstep : ∃ W' : GSet w64, ccStepB (ccV2Of (.v1 eff)) (cfgState W ∅) = some (cfgState W' ∅) ∧
      (∀ x, x ∈ W' → x ∈ W) ∧ (∀ x, x ∈ W → x ∉ W' → cm.type = W32 1 ∧ cm.nodeId = x) := by
    by_cases h0 : eff.nodeId = W64 0
    · exact ⟨W, ccStepB_noop0 W eff h0 hne hsz, fun _ h => h, fun _ h1 h2 => absurd h1 h2⟩
    have hec : eff = cm := by
      rcases hEff with h | h
      · exact h
      · rw [h] at h0; exact absurd rfl h0
    subst hec
    rcases Hcm with ⟨ht, hin, -⟩ | ⟨ht, hin⟩
    · -- an `AddNode`, among the boot entries: no `RemoveNode` before it, so `W = V`
      have hlt := hpm.1 ht
      have hinW : eff.nodeId ∈ W := by
        refine Classical.byContradiction fun hn => ?_
        obtain ⟨p, e, cc, hp, het, hd, hct, -⟩ := hrem _ hin hn
        have := ((hpD p e cc hp (by rw [het]; simp) hd).2 hct).1
        have := (List.getElem?_eq_some_iff.1 hp).1
        omega
      exact ⟨W, ccStepB_of_raftOk W eff ⟨ht, _, hinW, .inl rfl⟩ hsz, fun _ h => h,
        fun _ h1 h2 => absurd h1 h2⟩
    · -- a `RemoveNode` of another member than the local one
      have hnl : eff.nodeId ≠ lid := (hpm.2 ht).2
      by_cases hx : eff.nodeId ∈ W
      · refine ⟨GMap.delete eff.nodeId W, ccStepB_removeVoter W eff ht h0 hx ?_ hszW,
          fun x h => ((gset_elem_delete W _ x).1 h).2, fun x h1 h2 => ⟨ht, ?_⟩⟩
        · intro he
          have : lid ∈ (GMap.delete eff.nodeId W : GSet w64) :=
            (gset_elem_delete W _ lid).2 ⟨fun e => hnl e.symm, hlW⟩
          rw [he] at this; exact GMap.not_elem_of_empty _ this
        · refine Classical.byContradiction fun hne' => h2 ?_
          exact (gset_elem_delete W _ x).2 ⟨fun e => hne' e.symm, h1⟩
      · exact ⟨W, ccStepB_removeAbsent W eff ht h0 hx hne hszW, fun _ h => h,
          fun _ h1 h2 => absurd h1 h2⟩
  obtain ⟨W', hs, hW'W, hW'r⟩ := hstep
  rw [← hcfg] at hs
  have hk : (D ++ m :: rest)[D.length]? = some m := by
    rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]; rfl
  have hnc : NoConfIn (D ++ m :: rest) ca D.length :=
    NoConfIn_prefix ⟨m :: rest, rfl⟩ (Nat.le_refl _) h2
  have hdec : srvDec c0 boot ((D ++ m :: rest).take D.length) m = some (ccV2Of (.v1 eff)) := by
    unfold srvDec
    rw [List.take_left' rfl, ite_eq_left Hty, Hdec, ← heff]; rfl
  have hlt : D.length < (D ++ m :: rest).length := by simp
  refine ⟨cfgState W' ∅, ⟨h1, hlt, hk, .inl Hty, hnc, ⟨_, hdec, hs⟩, hs, rfl⟩, ?_⟩
  refine ⟨by simp, fun _ _ h1 h2 _ => absurd h2 (by simp at h1 ⊢; omega),
    ⟨W', rfl, fun x hx => hWV x (hW'W x hx), fun x hx hw => ?_⟩, ccStepB_cfgOk hs hok⟩
  by_cases hxW : x ∈ W
  · obtain ⟨ht, hn⟩ := hW'r x hxW hw
    exact ⟨D.length, m, cm, hmD, Hty, Hdec, ht, hn⟩
  · exact RemovedIn_snoc (hrem x hx hxW) m

end pure

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
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
no one), the node raft's, raft's names in the dynamic mode, and the node at the server's decoder
(from the start's consistent index `kc0` and the boot log, D43 M5d). -/
def dvOk (γs : ServerRaftNames) (kc0 : w64) (dv : Option NodeNames) (c f0 : w64)
    (ms : List EntryModel) : Prop :=
  (dv = none → γs.raft.reDyn = none ∨ ∀ m, m ∈ ms → m.typ ≠ W32 1) ∧
  ∀ γn, dv = some γn → uint.Z c < uint.Z f0 ∧ γn.raft = γs.raft ∧ γs.raft.reDyn.isSome = true ∧
    ∃ c0 h0 h1, γn.mode = .dyn (srvDec kc0 γs.raft.reBoot) c0 h0 h1

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
dynamic resources of `applyConfChange`'s spec at `(ca, cfg)`, its premise (the change etcd hands
raft, `ccRaftEff` at the member buckets after `L` from `kc0`, at the entry's position
`|srvLogOf γs L|` of the committed log handed out; D43 M5d: with a `RemoveNode`, under the dynamic
mode's positional policy), and back from its answer the view after the entry. -/
theorem dvView_cc (s : Loc) (γs : ServerRaftNames) (dv : Option NodeNames) (kc0 lid : w64)
    (L rest : List EntryModel) (m : EntryModel) (cm : CCV1M)
    (Hty : m.typ = W32 1) (Hdec : ccDecodeV1 m.data = some cm)
    (Hraft : ∀ γn, dv = some γn → γn.raft = γs.raft)
    (Hdyn : ∀ γn, dv = some γn → ccApplyOkR γs.raft cm ∧
      srvDynPol γs.raft.reBoot.length lid (srvLogOf γs (L ++ [m])) ∧ lid ∈ γs.raft.reCfg) :
    dvView (GF := GF) γs dv L ∗ dvRes s γs dv (L ++ m :: rest) ⊢
      ∃ (ca : Nat) (cfg cs' : CCState), dvCCPre s dv ca cfg (srvLogOf γs (L ++ m :: rest)) ∗
        ⌜∀ γn, dv = some γn →
          DynCCPreOp (srvDec kc0 γs.raft.reBoot) (srvLogOf γs (L ++ m :: rest)) ca cfg
            (ccV2Of (.v1 (membership.ccRaftEff
              (restModel kc0 γs.raft.reBoot (γs.pre ++ L)).bk cm)))
            (srvLogOf γs L).length m.toM cs'⌝ ∗
        (dvCCPost dv (srvLogOf γs L).length cs' -∗ dvView γs dv (L ++ [m])) := by
  unfold dvView dvRes dvCCPre dvCCPost
  rcases dv with _ | γn
  · iintro -
    iexists 0, cfgState ∅ ∅, cfgState ∅ ∅
    isplitr
    · itrivial
    isplitr
    · ipureintro; intro γn h; cases h
    iintro -
    itrivial
  · unfold srvCfgView
    iintro ⟨⟨%ca, %cfg, Hc, %Hok⟩, #Hn, #Hd⟩
    have Hr := Hraft γn rfl
    obtain ⟨Hcm, Hpol, Hlid⟩ := Hdyn γn rfl
    have hlog : srvLogOf γs (L ++ m :: rest) =
        (γs.pre ++ L).map EntryModel.toM ++ m.toM :: rest.map EntryModel.toM := by
      simp [srvLogOf]
    have hlog1 : srvLogOf γs (L ++ [m]) = (γs.pre ++ L).map EntryModel.toM ++ [m.toM] := by
      simp [srvLogOf]
    have hlen : (srvLogOf γs L).length = ((γs.pre ++ L).map EntryModel.toM).length := rfl
    have Hcm' : ccApplyOk γn.raft.reCfg cm ∨ (cm.type = W32 1 ∧ cm.nodeId ∈ γn.raft.reCfg) := by
      rw [Hr]
      rcases Hcm with h | ⟨-, h⟩
      · exact .inl h
      · exact .inr h
    rw [hlog1] at Hpol
    obtain ⟨cs', Hpre, Hpost⟩ := srvCfgOk_cc Hok kc0 γs.raft.reBoot m.toM
      (rest.map EntryModel.toM) cm Hty Hdec _ lid Hpol (by rw [Hr]; exact Hlid) Hcm'
    rw [EntryModel.map_ofM_toM] at Hpre
    iexists ca, cfg, cs'
    dsimp only
    iframe Hn Hc Hd
    isplitr
    · ipureintro
      intro γn' h
      cases h
      rw [hlog, hlen]
      exact Hpre
    iintro Hc'
    iexists (srvLogOf γs L).length + 1, cs'
    iframe Hc'
    ipureintro
    rw [hlen, ← List.append_assoc, List.map_append]
    exact Hpost

end apply

end EtcdGrove
end Perennial

/-
**The driver's configuration view at the server** (D43 M3, 2026-10-25; `notes/membership-plan.md`,
M3; 2026-10-27, branch `server-port`: over raft's node API, `nodeConfig`; 2026-10-30, the repair:
raft's one mode, the old dynamic one, its conf entries decided by the server's rule `srvRule`
through the cluster's `confPolicy`, D3: the membership static after boot). The application owns its
view of the configuration (`nodeConfig n γ N v`: the
position past the last applied conf entry and the membership) and applies every conf entry of the
committed log handed out, in order, before `Advance` (`node.Advance.spec`). At the server
the view is the raft loop's while it drives raft and the apply thread's while it applies a batch
with a conf entry (`raftNode.start` hands it over with the `toApply`; the second `notifyc` send
gives it back, `NotifyC.lean`).

- `srvRule c0 boot`: the server's rule (the cluster's `ConfRule`, `confPolicy`; until the repair
  the dynamic mode's decoder `srvDec`), a `ConfChange`
  entry's bytes as `pbutil.MustUnmarshal` reads them (`ccDecodeV1`), the change as
  `applyConfChange` hands it to raft after the log before it (D43 M5d: `ccRaftEff`, `NodeId` `0`
  when it does not validate).
- `srvCfgView γs n pre L`: the view after the committed log `pre ++ L`, every conf entry of it
  applied, the membership a simple one of the cluster's voters less the members a `RemoveNode` of
  the log removed (D43 M5d).
- `raftApplyCC γs n nd`: the node API's `node.ApplyConfChange.spec`, as the server calls
  it (`applyConfChange`); `srvRaftNodeCC s γs n` the server's node meeting it.
Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRequest
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRest
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.NotifyC

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section pure
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]

/-- A committed log from index `1`, as the server's records: each entry at its position. -/
def withIdx (l : List LogEntry) : List EntryModel :=
  l.mapIdx fun i x => ⟨x.term, W64 ((i : Int) + 1), x.type, x.data⟩

/-- A log consecutive from index `1` is its entries at their positions. -/
theorem withIdx_toLE (D : List EntryModel) (h : srvIdxOkW (W64 0) D) :
    withIdx (D.map EntryModel.toLE) = D := by
  apply List.ext_getElem?
  intro n
  unfold withIdx
  rw [List.getElem?_mapIdx, List.getElem?_map]
  cases hD : D[n]? with
  | none => rfl
  | some m =>
    simp only [Option.map_some]
    have hi := (h n m hD).1
    have hn : n < D.length := (List.getElem?_eq_some_iff.1 hD).1
    have : m.index = W64 ((n : Int) + 1) := by
      simp at hi
      word
    cases m
    simp only [EntryModel.toLE] at this ⊢
    rw [this]

/-- **The server's conf-change rule** (the cluster's `confPolicy` rule; D43 M5d: aware of the log
before the entry; 2026-10-30, the repair: raft's `ConfRule`, until then the dynamic mode's decoder
`srvDec`, the same function, the membership unread): a `ConfChange` entry's change as
`applyConfChange` hands it to raft: the change if it validates against the member buckets the log
before it leaves (`restModel` from the start's consistent index `c0` and the boot log `boot`), else
with `NodeId` `0` (`ccRaftEff`); skipped (`none`) for any other entry (the server proposes no
`ConfChangeV2`; raft's own, an empty one to leave a joint configuration, never comes:
`srv_committed_noV2`). -/
def srvRule (c0 : w64) (boot : List EntryM) : ConfRule := fun pre _m e =>
  if e.type = W32 1 then
    (ccDecodeV1 e.data).map (fun m =>
      .v1 (membership.ccRaftEff (restModel c0 boot (withIdx pre)).bk m))
  else none

/-- (2026-10-30, the repair; D3) **The server's rule keeps the voters' membership** (`srvClusterOk`'s
`srvRuleKeeps`): an `AddNode` of a voter, or with `NodeId` `0`, leaves a valid simple membership as
it is (`Membership.applyChange_addVoter`/`_nodeZero`). -/
theorem srvRule_keeps (c0 : w64) (boot : List EntryM) (cfg : GSet w64)
    (hv : (Membership.simple cfg).Valid) : srvRuleKeeps (srvRule c0 boot) cfg := by
  intro pre e
  refine ⟨fun ht hok o ho => ?_, fun ht => by unfold srvRule; simp only [ht, ↓reduceIte]⟩
  unfold srvRule at ho
  simp only [ht, ↓reduceIte] at ho
  cases hd : ccDecodeV1 e.data with
  | none => rw [hd] at ho; cases ho
  | some m =>
    rw [hd] at ho
    simp only [Option.map_some, Option.some.injEq] at ho
    subst ho
    obtain ⟨hty, hin, -⟩ := hok m hd
    unfold membership.ccRaftEff
    split
    · exact Membership.applyChange_addVoter cfg m hty hin hv
    · exact Membership.applyChange_nodeZero cfg _ rfl hv

/-- The log `D` has a `RemoveNode` of `x` (a `ConfChange` entry). -/
def RemovedIn (D : List EntryModel) (x : w64) : Prop :=
  ∃ (p : Nat) (e : EntryModel) (cc : ConfChangeM), D[p]? = some e ∧ e.typ = W32 1 ∧
    ccDecodeV1 e.data = some cc ∧ cc.type = W32 1 ∧ cc.nodeId = x

theorem RemovedIn_snoc {D : List EntryModel} {x : w64} (h : RemovedIn D x) (m : EntryModel) :
    RemovedIn (D ++ [m]) x := by
  obtain ⟨p, e, cc, hp, h1, h2, h3, h4⟩ := h
  exact ⟨p, e, cc, by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hp).1]; exact hp,
    h1, h2, h3, h4⟩

/-- **The dynamic mode's positional policy on a log `D`** (D43 M5d, the user's decision): every
conf entry decodes to an `AddNode` at a position below the boot log's length `nb` (the boot
entries) or a `RemoveNode` at or after it, never of the local member `lid`. -/
def srvDynPol (nb : Nat) (lid : w64) (D : List EntryModel) : Prop :=
  ∀ (p : Nat) (e : EntryModel) (cc : ConfChangeM), D[p]? = some e → e.typ ≠ W32 0 →
    ccDecodeV1 e.data = some cc →
    (cc.type = W32 0 → p < nb) ∧ (cc.type = W32 1 → nb ≤ p ∧ cc.nodeId ≠ lid)

theorem gset_elem_delete (W : GSet w64) (y x : w64) :
    x ∈ (GMap.delete y W : GSet w64) ↔ x ≠ y ∧ x ∈ W := by
  rw [GMap.elem_of_gset, GMap.elem_of_gset]
  by_cases h : y = x
  · subst h; rw [GMap.lookup_delete]; simp
  · rw [GMap.lookup_delete_ne _ h]
    exact ⟨fun h' => ⟨fun e => h e.symm, h'⟩, fun h' => h'.2⟩

theorem gset_size_delete_le (W : GSet w64) (y : w64) :
    GMap.size (GMap.delete y W : GSet w64) ≤ GMap.size W := by
  rw [GMap.map_size_delete]; split <;> omega

/-- **The node API's `ApplyConfChange`'s premise, at the rule `r`** (2026-10-30, the repair:
`node.ApplyConfChange.spec`'s, the decision `apply o'` the rule's, `confPolicy_decide`; until then
the dynamic spec's at a decoder, `srvDynCCPre`): the change of the next conf entry `e` at position
`k` of the committed log `l` past the view (no conf entry between: `skippedIn_noConf`), as the rule
decides it at the log before it and the view's membership, or `o`, its effect on the view's
membership `m'`. -/
def srvCCPre (r : ConfRule) (l : List LogEntry) (v : ConfigView)
    (o : ConfChangeIM) (k : Nat) (e : LogEntry) (m' : Membership) : Prop :=
  v.applied ≤ k ∧ l[k]? = some e ∧ e.isConfChange ∧ NoConfChangeIn l v.applied k ∧
  ∃ o', r (l.take k) v.membership e = some o' ∧ Membership.applyChange o' v.membership = some m' ∧
    Membership.applyChange o v.membership = some m' ∧ m'.autoLeave = false

/-- The pure part of the view: after the log `D`, the configuration index past every conf entry
of it, the membership a simple one of voters `W` of `V`, each voter of `V` out of `W` removed by a
`RemoveNode` of `D`, `W` within raft's bounds. -/
def srvCfgOk (V : GSet w64) (D : List EntryModel) (v : ConfigView) : Prop :=
  v.applied ≤ D.length ∧ NoConfChangeIn (D.map EntryModel.toLE) v.applied D.length ∧
  ∃ W : GSet w64, v.membership = Membership.simple W ∧ (∀ x, x ∈ W → x ∈ V) ∧
    (∀ x, x ∈ V → x ∉ W → RemovedIn D x) ∧ W64 0 ∉ W ∧ GMap.size W < 2 ^ 62

/-- The view at the start: nothing handed out, the voters' membership. -/
theorem srvCfgOk_nil (V : GSet w64) (h0 : W64 0 ∉ V) (hs : GMap.size V < 2 ^ 62) :
    srvCfgOk V [] ⟨0, Membership.simple V⟩ :=
  ⟨Nat.le_refl _, fun _ _ _ h2 _ => absurd h2 (by simp),
    ⟨V, rfl, fun _ h => h, fun _ h1 h2 => absurd h1 h2, h0, hs⟩⟩

/-- An entry that is no conf entry keeps the view. -/
theorem srvCfgOk_snoc_noConf {V : GSet w64} {D : List EntryModel} {v : ConfigView}
    (h : srvCfgOk V D v) (m : EntryModel) (hm : ¬ m.toLE.isConfChange) :
    srvCfgOk V (D ++ [m]) v := by
  obtain ⟨h1, h2, ⟨W, h3, h3a, h3b, h3c⟩⟩ := h
  refine ⟨by simp; omega, ?_, ⟨W, h3, h3a, fun x hx hw => RemovedIn_snoc (h3b x hx hw) m, h3c⟩⟩
  intro k e hk1 hk2 he
  rw [List.length_append, List.length_singleton] at hk2
  rw [List.map_append] at he
  by_cases hk : k < D.length
  · rw [List.getElem?_append_left (by simpa using hk)] at he
    exact h2 k e hk1 hk he
  · have hk' : k = D.length := by omega
    subst hk'
    rw [List.getElem?_append_right (by simp), List.length_map, Nat.sub_self] at he
    simp only [List.map_cons, List.map_nil, List.getElem?_cons_zero, Option.some.injEq] at he
    subst he
    exact hm

/-- **A conf entry of the server's, applied** (D43 M5d: with `RemoveNode`): the entry `m` after
`D` (consecutive from index `1`), a `ConfChange` whose bytes decode to a change `applyConfChange`
takes (an `AddNode` of `ccApplyOk`, or a `RemoveNode` of a member of `V`), under the dynamic mode's
positional policy (`srvDynPol`, the local member `lid` a member of `V`), meets the node API's
premise for the change etcd hands raft (`ccRaftEff` at the member buckets after `D`, the server's
decoder's), and the view after it is at `⟨|D| + 1, m'⟩`. -/
theorem srvCfgOk_cc {V : GSet w64} {D : List EntryModel} {v : ConfigView}
    (h : srvCfgOk V D v) (c0 : w64) (boot : List EntryM) (m : EntryModel) (rest : List EntryModel)
    (cm : ConfChangeM) (Hty : m.typ = W32 1) (Hdec : ccDecodeV1 m.data = some cm)
    (nb : Nat) (lid : w64) (hpol : srvDynPol nb lid (D ++ [m])) (hlid : lid ∈ V)
    (Hcm : ccApplyOk V cm ∨ (cm.type = W32 1 ∧ cm.nodeId ∈ V))
    (Hwi : withIdx (D.map EntryModel.toLE) = D) :
    ∃ m' : Membership,
      srvCCPre (srvRule c0 boot) ((D ++ m :: rest).map EntryModel.toLE) v
        (.v1 (membership.ccRaftEff (restModel c0 boot D).bk cm)) D.length m.toLE m' ∧
      srvCfgOk V (D ++ [m]) ⟨D.length + 1, m'⟩ := by
  obtain ⟨h1, h2, ⟨W, hcfg, hWV, hrem, hW0, hsz⟩⟩ := h
  have hmD : (D ++ [m])[D.length]? = some m := by simp
  have hpm := hpol D.length m cm hmD (by rw [Hty]; decide) Hdec
  have hpD : ∀ p e cc, D[p]? = some e → e.typ ≠ W32 0 → ccDecodeV1 e.data = some cc →
      (cc.type = W32 0 → p < nb) ∧ (cc.type = W32 1 → nb ≤ p ∧ cc.nodeId ≠ lid) :=
    fun p e cc hp => hpol p e cc (by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hp).1]; exact hp)
  -- the local member stays a voter: no `RemoveNode` of it
  have hlW : lid ∈ W := by
    refine Classical.byContradiction fun hl => ?_
    obtain ⟨p, e, cc, hp, het, hd, hct, hcn⟩ := hrem lid hlid hl
    exact ((hpD p e cc hp (by rw [het]; decide) hd).2 hct).2 hcn
  have hne : W ≠ ∅ := fun he => by rw [he] at hlW; exact GMap.not_elem_of_empty _ hlW
  have hval : (Membership.simple W).Valid := Membership.simple_valid W hne hW0 hsz
  generalize heff : membership.ccRaftEff (restModel c0 boot D).bk cm = eff
  have hEff : eff = cm ∨ eff = { cm with nodeId := W64 0 } := by
    rw [← heff]; unfold membership.ccRaftEff; split
    · exact .inl rfl
    · exact .inr rfl
  -- the step: the voters `W'`
  have hstep : ∃ W' : GSet w64,
      Membership.applyChange (.v1 eff) (Membership.simple W) =
        some (Membership.simple W') ∧
      (∀ x, x ∈ W' → x ∈ W) ∧ (∀ x, x ∈ W → x ∉ W' → cm.type = W32 1 ∧ cm.nodeId = x) ∧
      GMap.size W' < 2 ^ 62 := by
    by_cases h0 : eff.nodeId = W64 0
    · exact ⟨W, Membership.applyChange_nodeZero W eff h0 hval, fun _ h => h,
        fun _ h1 h2 => absurd h1 h2, hsz⟩
    have hec : eff = cm := by
      rcases hEff with h | h
      · exact h
      · rw [h] at h0; exact absurd rfl h0
    subst hec
    rcases Hcm with ⟨ht, hin, -⟩ | ⟨ht, hin⟩
    · -- an `AddNode`, among the boot entries: no `RemoveNode` before it, so its node is in `W`
      have hinW : eff.nodeId ∈ W := by
        refine Classical.byContradiction fun hn => ?_
        obtain ⟨p, e, cc, hp, het, hd, hct, -⟩ := hrem _ hin hn
        have := ((hpD p e cc hp (by rw [het]; decide) hd).2 hct).1
        have := (List.getElem?_eq_some_iff.1 hp).1
        have := hpm.1 ht
        omega
      exact ⟨W, Membership.applyChange_addVoter W eff ht hinW hval, fun _ h => h,
        fun _ h1 h2 => absurd h1 h2, hsz⟩
    · -- a `RemoveNode` of another member than the local one
      have hnl : eff.nodeId ≠ lid := (hpm.2 ht).2
      by_cases hx : eff.nodeId ∈ W
      · have hdne : (GMap.delete eff.nodeId W : GSet w64) ≠ ∅ := by
          intro he
          have : lid ∈ (GMap.delete eff.nodeId W : GSet w64) :=
            (gset_elem_delete W _ lid).2 ⟨fun e => hnl e.symm, hlW⟩
          rw [he] at this; exact GMap.not_elem_of_empty _ this
        refine ⟨GMap.delete eff.nodeId W,
          Membership.applyChange_removeVoter W eff ht h0 hx hdne hval,
          fun x h => ((gset_elem_delete W _ x).1 h).2, fun x h1 h2 => ⟨ht, ?_⟩,
          Nat.lt_of_le_of_lt (gset_size_delete_le W _) hsz⟩
        refine Classical.byContradiction fun hne' => h2 ?_
        exact (gset_elem_delete W _ x).2 ⟨fun e => hne' e.symm, h1⟩
      · exact ⟨W, Membership.applyChange_removeAbsent W eff ht h0 hx hval, fun _ h => h,
          fun _ h1 h2 => absurd h1 h2, hsz⟩
  obtain ⟨W', hs, hW'W, hW'r, hsz'⟩ := hstep
  rw [← hcfg] at hs
  have hk : ((D ++ m :: rest).map EntryModel.toLE)[D.length]? = some m.toLE := by
    rw [List.map_append, List.getElem?_append_right (by simp), List.length_map, Nat.sub_self]; rfl
  have hnc : NoConfChangeIn ((D ++ m :: rest).map EntryModel.toLE) v.applied D.length := by
    intro k e hk1 hk2 he
    rw [List.map_append, List.getElem?_append_left (by simpa using hk2)] at he
    exact h2 k e hk1 hk2 he
  have htake : ((D ++ m :: rest).map EntryModel.toLE).take D.length = D.map EntryModel.toLE := by
    rw [List.map_append, List.take_left' (by simp)]
  have hdec : srvRule c0 boot (((D ++ m :: rest).map EntryModel.toLE).take D.length)
      v.membership m.toLE = some (.v1 eff) := by
    rw [htake]
    unfold srvRule
    simp only [EntryModel.toLE, Hty, ↓reduceIte, Hdec, Option.map_some, Hwi, heff]
  refine ⟨Membership.simple W', ⟨h1, hk, .inl Hty, hnc, ⟨_, hdec, hs, hs, rfl⟩⟩, ?_⟩
  refine ⟨by simp, fun _ _ h1 h2 _ => absurd h2 (by simp at h1 ⊢; omega),
    ⟨W', rfl, fun x hx => hWV x (hW'W x hx), fun x hx hw => ?_,
      fun h0 => hW0 (hW'W _ h0), hsz'⟩⟩
  by_cases hxW : x ∈ W
  · obtain ⟨ht, hn⟩ := hW'r x hxW hw
    exact ⟨D.length, m, cm, hmD, Hty, Hdec, ht, hn⟩
  · exact RemovedIn_snoc (hrem x hx hxW) m

/-- (2026-10-30, the repair; D3) **A conf entry of the server's, applied, in a static cluster**: the
entry `m` after `D` (consecutive from index `1`, no `RemoveNode` in it), a `ConfChange` whose bytes
decode to an `AddNode` of a voter (`ccApplyOk`), meets the node API's premise for the change etcd
hands raft (`ccRaftEff`: the change or it at the node `0`), which keeps the view's membership. -/
theorem srvCfgOk_ccS {V : GSet w64} {D : List EntryModel} {v : ConfigView}
    (h : srvCfgOk V D v) (c0 : w64) (boot : List EntryM) (m : EntryModel) (rest : List EntryModel)
    (cm : ConfChangeM) (Hty : m.typ = W32 1) (Hdec : ccDecodeV1 m.data = some cm)
    (Hnr : ∀ x, ¬ RemovedIn D x) (Hcm : ccApplyOk V cm)
    (Hwi : withIdx (D.map EntryModel.toLE) = D) :
    ∃ m' : Membership,
      srvCCPre (srvRule c0 boot) ((D ++ m :: rest).map EntryModel.toLE) v
        (.v1 (membership.ccRaftEff (restModel c0 boot D).bk cm)) D.length m.toLE m' ∧
      srvCfgOk V (D ++ [m]) ⟨D.length + 1, m'⟩ := by
  obtain ⟨h1, h2, ⟨W, hcfg, hWV, hrem, hW0, hsz⟩⟩ := h
  have hVW : ∀ x, x ∈ V → x ∈ W := fun x hx =>
    Classical.byContradiction fun hn => Hnr x (hrem x hx hn)
  obtain ⟨hct, hcin, -⟩ := Hcm
  have hne : W ≠ ∅ := fun he => by
    have := hVW _ hcin; rw [he] at this; exact GMap.not_elem_of_empty _ this
  have hval : (Membership.simple W).Valid := Membership.simple_valid W hne hW0 hsz
  generalize heff : membership.ccRaftEff (restModel c0 boot D).bk cm = eff
  have hs : Membership.applyChange (.v1 eff) (Membership.simple W) = some (Membership.simple W) := by
    rw [← heff]; unfold membership.ccRaftEff; split
    · exact Membership.applyChange_addVoter W cm hct (hVW _ hcin) hval
    · exact Membership.applyChange_nodeZero W _ rfl hval
  rw [← hcfg] at hs
  have hk : ((D ++ m :: rest).map EntryModel.toLE)[D.length]? = some m.toLE := by
    rw [List.map_append, List.getElem?_append_right (by simp), List.length_map, Nat.sub_self]; rfl
  have hnc : NoConfChangeIn ((D ++ m :: rest).map EntryModel.toLE) v.applied D.length := by
    intro k e hk1 hk2 he
    rw [List.map_append, List.getElem?_append_left (by simpa using hk2)] at he
    exact h2 k e hk1 hk2 he
  have htake : ((D ++ m :: rest).map EntryModel.toLE).take D.length = D.map EntryModel.toLE := by
    rw [List.map_append, List.take_left' (by simp)]
  have hdec : srvRule c0 boot (((D ++ m :: rest).map EntryModel.toLE).take D.length)
      v.membership m.toLE = some (.v1 eff) := by
    rw [htake]
    unfold srvRule
    simp only [EntryModel.toLE, Hty, ↓reduceIte, Hdec, Option.map_some, Hwi, heff]
  refine ⟨v.membership, ⟨h1, hk, .inl Hty, hnc, ⟨_, hdec, hs, hs, by rw [hcfg]; rfl⟩⟩, ?_⟩
  refine ⟨by simp, fun _ _ h1 h2 _ => absurd h2 (by simp at h1 ⊢; omega),
    ⟨W, hcfg, hWV, fun x hx hw => absurd (hVW x hx) hw, hW0, hsz⟩⟩

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- **The driver's view after the committed log `pre ++ L`** (see the file
header): the node API's `nodeConfig` of the node `n` with `srvCfgOk` at the cluster's voters. -/
def srvCfgView (γs : ServerRaftNames) (n : Loc) (pre L : List EntryModel) : IProp GF :=
  letI := srvStor (GF := GF) γs.raft
  iprop(∃ v : ConfigView, nodeConfig n γs.raft.cl srvClusterN v ∗
    ⌜srvCfgOk γs.raft.cfg (pre ++ L) v⌝)

/-- **The node API's `ApplyConfChange`, as the server calls it** (persistent; `node.ApplyConfChange.spec`
of the node `n`; 2026-10-30, the repair: raft's one mode, the decision the cluster's rule's,
`confPolicy_decide`, and the conf entries between the view and `k` skipped, `skippedIn_noConf`;
until then the dynamic mode's `raftApplyCCDyn`): of a v1 change, read-only, the next conf entry's
at position `k` of the committed log `l` delivered (`srvCCPre`, at the cluster's rule), with the
driver's view and a share of the node's running token (the apply side's half, `dvRun`, which
refutes raft's stopped answer, `nodeRunning_stopped`: etcd stops raft only after the scheduler is
drained), it returns the new `*ConfState`, owned, of the membership `m'`, and the view at
`⟨k + 1, m'⟩`. -/
def raftApplyCC (γs : ServerRaftNames) (n : Loc) (nd : GoInterface) : IProp GF :=
  letI := srvStor (GF := GF) γs.raft
  iprop(∃ ni : GoInterfaceOk, ⌜nd = GoInterface.ok ni⌝ ∗
    □ (∀ (c : GoInterface) (cm : ConfChangeM) (l : List LogEntry) (v : ConfigView)
        (k : Nat) (e : LogEntry) (m' : Membership) (q : Qp),
      ⌜srvCCPre γs.raft.rule l v (.v1 cm) k e m'⌝ -∗
      {{ ownConfChangeI c DFrac.discard (some (.v1 cm)) ∗
          nodeConfig n γs.raft.cl srvClusterN v ∗
          deliveredLogLb n γs.raft.cl srvClusterN l ∗ nodeRunning n γs.raft.cl srvClusterN q }}
        (App (Val #(methods ni.ty go!"ApplyConfChange" ni.v)) (Val #c))
      {{ (csp : Loc), RET #csp; (∃ cs : ConfStateM, csPts csp (DFrac.own 1) cs true ∗
            ⌜confStateIs cs m'⌝) ∗
          nodeConfig n γs.raft.cl srvClusterN ⟨k + 1, m'⟩ ∗
          nodeRunning n γs.raft.cl srvClusterN q }}))

instance raftApplyCC_persistent (γs : ServerRaftNames) (n : Loc) (nd : GoInterface) :
    Persistent (raftApplyCC (GF := GF) γs n nd) := by
  unfold raftApplyCC; infer_instance

end defs

section addr
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- **The server `s`'s raft node, for its conf changes** (persistent; 2026-10-30, the repair: until
then `srvRaftNodeDyn`, in a dynamic cluster): `s.r`'s `Node` (the node `n`) meets `raftApplyCC`. -/
def srvRaftNodeCC (s : Loc) (γs : ServerRaftNames) (n : Loc) : IProp GF :=
  iprop(∃ nd : GoInterface, srvNodeAddr s ↦□ nd ∗ raftApplyCC γs n nd)

instance srvRaftNodeCC_persistent (s : Loc) (γs : ServerRaftNames) (n : Loc) :
    Persistent (srvRaftNodeCC (GF := GF) s γs n) := by
  unfold srvRaftNodeCC; infer_instance

/-- The contract reads only the cluster. -/
theorem srvRaftNodeCC_congr (s : Loc) (γ1 γ2 : ServerRaftNames) (n : Loc) (h : γ1.raft = γ2.raft) :
    srvRaftNodeCC (GF := GF) s γ1 n = srvRaftNodeCC s γ2 n := by
  unfold srvRaftNodeCC raftApplyCC; rw [h]

end addr

section apply
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- **The apply thread's view, optional** (`apply`, `applyEntries`, `applyAll`): `none` (a batch
with no conf entry: the raft loop keeps the view; until the repair also a static cluster), or the
view after the log
`L` the apply thread has applied, of the node `n`. -/
def dvView (γs : ServerRaftNames) (dv : Option Loc) (L : List EntryModel) : IProp GF :=
  match dv with
  | none => iprop(True)
  | some n => srvCfgView γs n γs.pre L

/-- What the apply thread holds of the node for a batch with a view (persistent): the conf-change
contract and the committed log delivered through the batch `L`. -/
def dvRes (s : Loc) (γs : ServerRaftNames) (dv : Option Loc) (L : List EntryModel) :
    IProp GF :=
  match dv with
  | none => iprop(True)
  | some n => letI := srvStor (GF := GF) γs.raft; iprop(srvRaftNodeCC s γs n ∗
      deliveredLogLb n γs.raft.cl srvClusterN (srvLE γs L))

instance dvRes_persistent (s : Loc) (γs : ServerRaftNames) (dv : Option Loc)
    (L : List EntryModel) : Persistent (dvRes (GF := GF) s γs dv L) := by
  unfold dvRes; split <;> infer_instance

/-- **The premise on a batch's view**: without one, no conf entry (2026-10-30, the repair: one mode;
until then also a static cluster); with one, no entry at or below the consistent index `c` (no
replay: Go hands a replayed conf change to no one), the cluster at the server's rule (from the
start's consistent index `kc0` and the boot log, D43 M5d), started at index `0` with nothing
before. -/
def dvOk (γs : ServerRaftNames) (kc0 : w64) (dv : Option Loc) (c f0 : w64)
    (ms : List EntryModel) : Prop :=
  (dv = none → ∀ m, m ∈ ms → m.typ ≠ W32 1) ∧
  ∀ n, dv = some n → uint.Z c < uint.Z f0 ∧
    γs.raft.rule = srvRule kc0 γs.raft.boot ∧ γs.pre = [] ∧ γs.ai0 = W64 0

/-- The node resources of `applyConfChange` (its precondition's): with a view, the node's
conf-change contract, the driver's `nodeConfig` at `v` and the committed log `l` delivered, and
(2026-10-30, the repair) the apply side's half of the running token (`dvRun`). -/
def dvCCPre (s : Loc) (γs : ServerRaftNames) (dv : Option Loc) (v : ConfigView)
    (l : List LogEntry) : IProp GF :=
  match dv with
  | none => iprop(True)
  | some n => letI := srvStor (GF := GF) γs.raft; iprop(srvRaftNodeCC s γs n ∗ nodeConfig n γs.raft.cl srvClusterN v ∗
      deliveredLogLb n γs.raft.cl srvClusterN l ∗ nodeRunning n γs.raft.cl srvClusterN (1 : Qp).half)

/-- `applyConfChange`'s node answer: with a view, `nodeConfig` at `⟨k + 1, m'⟩`, and (2026-10-30)
the running token's half back. -/
def dvCCPost (γs : ServerRaftNames) (dv : Option Loc) (k : Nat) (m' : Membership) :
    IProp GF :=
  match dv with
  | none => iprop(True)
  | some n => letI := srvStor (GF := GF) γs.raft
      iprop(nodeConfig n γs.raft.cl srvClusterN ⟨k + 1, m'⟩ ∗ nodeRunning n γs.raft.cl srvClusterN (1 : Qp).half)

/-- A normal entry keeps the view. -/
theorem dvView_normal (γs : ServerRaftNames) (dv : Option Loc) (L : List EntryModel)
    (m : EntryModel) (hm : m.typ = W32 0) :
    dvView (GF := GF) γs dv L ⊢ dvView γs dv (L ++ [m]) := by
  unfold dvView
  rcases dv with _ | n
  · exact .rfl
  · unfold srvCfgView
    iintro ⟨%v, Hc, %Hok⟩
    iexists v
    iframe Hc
    ipureintro
    rw [← List.append_assoc]
    refine srvCfgOk_snoc_noConf Hok _ ?_
    unfold LogEntry.isConfChange
    simp only [EntryModel.toLE, hm]
    intro h
    rcases h with h | h <;> simp at h

/-- (2026-10-30, the repair; D3) **No committed log has a `RemoveNode`**: its v1 conf entries are
the server's (`srv_committed_ccBoot`), `AddNode`s (`ccApplyOk`). What `dvView_cc`'s premise asks of
the log before the entry. -/
theorem srv_noRemovedIn (γ : ServerRaftNames) (L : List EntryModel) (E : CoPset)
    (hL : ↑srvLogN ⊆ E) :
    srvRaftLogInv (GF := GF) γ ∗ isCommittedLogLb γ.raft.cl (srvLE γ L) ⊢
      |={E}=> ⌜∀ x, ¬ RemovedIn (γ.pre ++ L) x⌝ := by
  iintro ⟨#Hinv, #Hl⟩
  imod srv_committed_ccBoot γ (srvLE γ L) E hL $$ [$Hinv $Hl] with %Hall
  imodintro
  ipureintro
  rintro x ⟨p, e, cc, hp, h1, h2, h3, -⟩
  have he : e.toLE ∈ srvLE γ L := by
    unfold srvLE; exact List.mem_map_of_mem (List.mem_of_getElem? hp)
  have := (Hall _ he h1 cc h2).1
  rw [h3] at this
  simp at this

/-- **A conf entry, at the view** (`applyConfChange`'s call): the view and the node's give the
node resources of `applyConfChange`'s spec at `v`, its premise (the change etcd hands raft,
`ccRaftEff` at the member buckets after `L` from `kc0`, at the entry's position `|pre ++ L|` of the
committed log delivered; D43 M5d: with a `RemoveNode`, under the dynamic mode's positional policy),
and back from its answer the view after the entry. -/
theorem dvView_cc (s : Loc) (γs : ServerRaftNames) (dv : Option Loc) (kc0 lid : w64)
    (L rest : List EntryModel) (m : EntryModel) (cm : ConfChangeM)
    (Hty : m.typ = W32 1) (Hdec : ccDecodeV1 m.data = some cm)
    (Hdyn : ∀ n, dv = some n → ccApplyOkR γs.raft cm ∧ lid ∈ γs.raft.cfg ∧
      withIdx ((γs.pre ++ L).map EntryModel.toLE) = γs.pre ++ L ∧
      (∀ x, ¬ RemovedIn (γs.pre ++ L) x)) :
    dvView (GF := GF) γs dv L ∗ dvRes s γs dv (L ++ m :: rest) ∗ (match dv with | none => iprop(True) | some n => (letI := srvStor (GF := GF) γs.raft; nodeRunning n γs.raft.cl srvClusterN (1 : Qp).half)) ⊢
      ∃ (v : ConfigView) (m' : Membership),
        dvCCPre s γs dv v (srvLE γs (L ++ m :: rest)) ∗
        ⌜∀ n, dv = some n →
          srvCCPre (srvRule kc0 γs.raft.boot) (srvLE γs (L ++ m :: rest)) v
            (.v1 (membership.ccRaftEff (restModel kc0 γs.raft.boot (γs.pre ++ L)).bk cm))
            (γs.pre ++ L).length m.toLE m'⌝ ∗
        (dvCCPost γs dv (γs.pre ++ L).length m' -∗ dvView γs dv (L ++ [m]) ∗ (match dv with | none => iprop(True) | some n => (letI := srvStor (GF := GF) γs.raft; nodeRunning n γs.raft.cl srvClusterN (1 : Qp).half))) := by
  unfold dvView dvRes dvCCPre dvCCPost
  rcases dv with _ | n
  · iintro -
    iexists ⟨0, Membership.simple ∅⟩, Membership.simple ∅
    isplitr
    · itrivial
    isplitr
    · ipureintro; intro n h; cases h
    iintro -
    itrivial
  · unfold srvCfgView
    iintro ⟨⟨%v, Hc, %Hok⟩, ⟨#Hn, #Hd⟩, Hrun⟩
    obtain ⟨Hcm, -, Hwi, Hnr⟩ := Hdyn n rfl
    have hlog : srvLE γs (L ++ m :: rest) = ((γs.pre ++ L) ++ m :: rest).map EntryModel.toLE := by
      simp [srvLE]
    obtain ⟨m', Hpre, Hpost⟩ := srvCfgOk_ccS Hok kc0 γs.raft.boot m rest cm Hty Hdec Hnr Hcm Hwi
    iexists v, m'
    dsimp only
    iframe Hn Hc Hrun
    isplitr
    · rw [hlog]; iexact Hd
    isplitr
    · ipureintro
      intro n' h
      cases h
      rw [hlog]
      exact Hpre
    iintro ⟨Hc', Hrun'⟩
    iframe Hrun'
    iexists ⟨(γs.pre ++ L).length + 1, m'⟩
    iframe Hc'
    ipureintro
    rw [← List.append_assoc]
    exact Hpost

end apply

end EtcdGrove
end Perennial

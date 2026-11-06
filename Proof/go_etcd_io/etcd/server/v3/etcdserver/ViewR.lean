/-
**The driver's view at a restart, over the ghost log** (R2d' probe, step 5, 2026-11-06; DRAFT:
nothing here is frozen, `notes/restart-plan.md`, "R2d' Scope (approved 2026-11-06)", finding 1 and
the probe). Lean-first (no Rocq counterpart).

At the etcd pin `673da07c8`, a restarted member's raft node starts (`raft.RestartNode`,
`bootstrap.go:597`, its `raft.Config` with no `Applied`, `bootstrap.go:580-591`) with a view `⟨a, m⟩`,
`a ∈ [σ.b, σ.commit]`, which the proof takes at the backend's consistent index `i` (finding 1: Go
skips every conf entry in `(σ.b, i]`), while Go's applied log `G` restarts at the WAL snapshot's index
`σ.b ≤ i`.
Go hands a replayed conf change to no one (`applyConfChange` calls `s.r.ApplyConfChange` only `if
shouldApplyV3`, `server.go:2053-2058`), yet the raft loop hands the apply thread the view along with
every batch holding a conf entry and waits for it back on `notifyc` (`confChanged`,
`raft.go:294-300` and `raft.go:317-326`; the apply side's receive, `server.go:995`). Over Go's log the view's `srvCfgOk` (its applied index at most the log's
length) is false while `|G| < i`; over the ghost log `ghostOf rp G` it holds, and a replayed batch
leaves the ghost log, hence the view, unchanged.

* `rnCfgAtR`: `rnCfgAt` over the ghost log (DRAFT; today's at a first start, `rnCfgAtR_first`);
* `rnApGiveR`/`rnApRR`: what goes along with a batch and comes back, over it (`rnApGive`/`rnApR`'s
  restart forms; today's at a first start);
* the bridges to the apply side's `dvView`/`dvRes` with the apply side's `pre = []` (Go's log the
  raft loop's `pre ++ F`): `rnApGiveR_dv`, `rnApRR_dv` (no `γ.pre = γs.pre`, which a restart breaks);
* the round trip of a replayed batch: the view given is the view returned (`rnCfgR_replay`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRaftLoop
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.RestReplay

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section view
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The driver's view after the committed log `L`, over the ghost log** (DRAFT; `rnCfgAt`'s
restart form, finding 1): the view after `ghostOf rp (pre ++ L)`, the raft loop's handed log
`pre ++ L` completed by the backend's entries past it (`A₀`, the restart point's). -/
def rnCfgAtR (γ : RNNames) (rp : RestartPt) (L : List EntryModel) : IProp GF :=
  srvCfgView γ.srv γ.nl [] (ghostOf rp (γ.pre ++ L))

/-- A first start's is the driver's view over Go's log (`rnCfgAt`'s at `γ.a0 = []`, `rnView_first`;
R2d'a A6: `rnCfgAt` itself is over the ghost log since). -/
theorem rnCfgAtR_first (γ : RNNames) (L : List EntryModel) :
    rnCfgAtR (GF := GF) γ RestartPt.first L = srvCfgView γ.srv γ.nl γ.pre L := by
  unfold rnCfgAtR srvCfgView
  rw [ghostOf_first, List.nil_append]

/-- **What comes back with a batch** (DRAFT; `rnApR`'s restart form). -/
def rnApRR (γ : RNNames) (rp : RestartPt) (F ce : List EntryModel) : IProp GF :=
  if rnHands γ ce then rnCfgAtR γ rp (F ++ ce) else iprop(True)

/-- **What goes along with a batch** (DRAFT; `rnApGive`'s restart form): the view over the ghost
log, the committed log delivered through the batch over Go's (raft's own log). -/
def rnApGiveR (γ : RNNames) (rp : RestartPt) (F ce : List EntryModel) : IProp GF :=
  letI := srvStor (GF := GF) γ.node
  if rnHands γ ce then
    iprop(rnCfgAtR γ rp F ∗ deliveredLogLb γ.nl γ.node.cl srvClusterN (srvLE γ.srv (F ++ ce)))
  else iprop(True)

theorem rnApRR_first (γ : RNNames) (ha : γ.a0 = []) (F ce : List EntryModel) :
    rnApRR (GF := GF) γ RestartPt.first F ce = rnApR γ F ce := by
  rw [(rnView_first γ ha).2.1]; unfold rnApRR; rw [rnCfgAtR_first]

theorem rnApGiveR_first (γ : RNNames) (ha : γ.a0 = []) (F ce : List EntryModel) :
    rnApGiveR (GF := GF) γ RestartPt.first F ce = rnApGive γ F ce := by
  rw [(rnView_first γ ha).2.2]; unfold rnApGiveR; rw [rnCfgAtR_first]

/-- **What comes back, as the apply side states it** (the apply side's `pre = []`, its log Go's
`γ.pre ++ F`; the view over the ghost log). -/
theorem rnApRR_dv (γ : RNNames) (γs : ServerRaftNames) (rp : RestartPt) (hpre : γs.pre = [])
    (hraft : γs.raft = γ.node) (F ce : List EntryModel) :
    rnApRR (GF := GF) γ rp F ce = dvView γs (rnDv γ ce) (ghostOf rp (γ.pre ++ F ++ ce)) := by
  unfold rnApRR rnDv dvView
  by_cases h : rnHands γ ce
  · rw [ite_eq_left h, ite_eq_left h]
    unfold rnCfgAtR srvCfgView
    rw [hraft, hpre, List.append_assoc]
  · rw [ite_eq_right h, ite_eq_right h]

/-- **What goes along, as the apply side states it**: the view over the ghost log of Go's log before
the batch, the delivered log over Go's log through it. -/
theorem rnApGiveR_dv (s : Loc) (γ : RNNames) (γs : ServerRaftNames) (rp : RestartPt)
    (hpre : γs.pre = []) (hraft : γs.raft = γ.node) (F ce : List EntryModel) :
    srvRaftNodeCC (GF := GF) s γ.srv γ.nl ∗ rnApGiveR γ rp F ce ⊢
      dvView γs (rnDv γ ce) (ghostOf rp (γ.pre ++ F)) ∗
        dvRes s γs (rnDv γ ce) (γ.pre ++ F ++ ce) := by
  unfold rnApGiveR rnDv dvView dvRes
  by_cases h : rnHands γ ce
  · rw [ite_eq_left h, ite_eq_left h]
    simp only
    rw [srvRaftNodeCC_congr s γs γ.srv γ.nl hraft]
    unfold rnCfgAtR srvCfgView srvLE
    rw [hraft, hpre]
    simp only [RNNames.srv, List.nil_append, List.append_assoc]
    iintro ⟨#Hn, Hv, #Hd⟩
    iframe Hv Hn Hd
  · rw [ite_eq_right h, ite_eq_right h]
    simp only
    iintro -
    isplitr
    · ipureintro; trivial
    ipureintro; trivial

/-- **A batch inside the window leaves the ghost log unchanged**: Go's log through it a prefix of
the backend's, the ghost log is the backend's before and after. -/
theorem ghostOf_replay (rp : RestartPt) (G ce : List EntryModel) (hin : G ++ ce <+: rp.A₀) :
    ghostOf rp (G ++ ce) = ghostOf rp G := by
  rw [ghostOf_in rp _ hin, ghostOf_in rp G (List.prefix_append G ce |>.trans hin)]

/-- **The view's round trip over a replayed batch** (R2d' probe, step 5): the raft loop gives the
view with a batch inside the window (a replayed conf entry: `rnHands`); the apply thread's replay
leaves its view where it was (the ghost log unchanged, `ghostOf_replay`; `applyConfChange` at
`shouldApplyV3` false calls no `ApplyConfChange`, `server.go:2053-2058`), and what it hands back on
`notifyc` is what the loop waits for (`rnApRR`), the view after the batch (`rnCfgAtR`). -/
theorem rnCfgR_replay (s : Loc) (γ : RNNames) (γs : ServerRaftNames) (rp : RestartPt)
    (hpre : γs.pre = []) (hraft : γs.raft = γ.node) (F ce : List EntryModel)
    (hin : γ.pre ++ F ++ ce <+: rp.A₀) :
    srvRaftNodeCC (GF := GF) s γ.srv γ.nl ∗ rnApGiveR γ rp F ce ⊢
      dvRes s γs (rnDv γ ce) (γ.pre ++ F ++ ce) ∗ rnApRR γ rp F ce := by
  iintro H
  icases rnApGiveR_dv s γ γs rp hpre hraft F ce $$ H with ⟨Hv, #Hd⟩
  iframe Hd
  rw [rnApRR_dv γ γs rp hpre hraft F ce, ghostOf_replay rp _ ce hin]
  iexact Hv

/-- **The loop's view after the batch**: with a conf entry in the batch, what came back
(`rnCfgAt_back_true`'s restart form). -/
theorem rnCfgAtR_back_true (γ : RNNames) (rp : RestartPt) (L ce : List EntryModel)
    (hcc : ccIn ce = true) :
    (if rnHands γ ce then iprop(True) else rnCfgAtR (GF := GF) γ rp L) ∗ rnApRR γ rp L ce ⊢
      rnCfgAtR γ rp (L ++ ce) := by
  have hh : rnHands γ ce = true := hcc
  unfold rnApRR
  rw [ite_eq_left hh, ite_eq_left hh]
  iintro ⟨-, H⟩
  iexact H

/-- A normal entry keeps a view over any log (`dvView_normal`'s, at `pre = []`). -/
theorem srvCfgView_normal1 (γs : ServerRaftNames) (n : Loc) (X : List EntryModel) (m : EntryModel)
    (hm : m.typ = W32 0) :
    srvCfgView (GF := GF) γs n [] X ⊢ srvCfgView γs n [] (X ++ [m]) := by
  unfold srvCfgView
  iintro ⟨%v, Hc, %Hok⟩
  iexists v
  iframe Hc
  ipureintro
  rw [List.nil_append] at Hok ⊢
  refine srvCfgOk_snoc_noConf Hok _ ?_
  unfold LogEntry.isConfChange
  simp only [EntryModel.toLE, hm]
  intro h
  rcases h with h | h <;> simp at h

/-- Normal entries keep a view over any log. -/
theorem srvCfgView_normal (γs : ServerRaftNames) (n : Loc) (d : List EntryModel)
    (h : ∀ m, m ∈ d → m.typ = W32 0) :
    ∀ X, srvCfgView (GF := GF) γs n [] X ⊢ srvCfgView γs n [] (X ++ d) := by
  induction d with
  | nil => intro X; rw [List.append_nil]
  | cons m d IH =>
    intro X
    refine (srvCfgView_normal1 γs n X m (h m List.mem_cons_self)).trans ?_
    rw [show X ++ m :: d = (X ++ [m]) ++ d by simp]
    exact IH (fun m' hm' => h m' (List.mem_cons_of_mem _ hm')) _

/-- **The ghost log after a batch extends the one before by a suffix of the batch** (R2d'a A6,
DRAFT): when Go's log through the batch and the backend's agree (one a prefix of the other, as two
committed logs, `srvRLogLb_prefix`). Inside the window nothing is added; across or past it, the
batch's entries past the backend's log. -/
theorem ghostOf_batch (rp : RestartPt) (G ce : List EntryModel)
    (hc : G ++ ce <+: rp.A₀ ∨ rp.A₀ <+: G ++ ce) :
    ∃ d, ghostOf rp (G ++ ce) = ghostOf rp G ++ d ∧ ∀ m, m ∈ d → m ∈ ce := by
  rcases hc with hin | hpast
  · exact ⟨[], by rw [ghostOf_replay rp G ce hin, List.append_nil], fun _ h => absurd h (by simp)⟩
  · have hg' : ghostOf rp (G ++ ce) = G ++ ce :=
      ghostOf_past rp _ hpast.length_le
    by_cases hG : rp.A₀.length ≤ G.length
    · refine ⟨ce, by rw [hg', ghostOf_past rp G hG], fun _ h => h⟩
    · -- straddling: the ghost log before is the backend's, a prefix of Go's through the batch
      have hGA : G <+: rp.A₀ :=
        List.prefix_of_prefix_length_le (List.prefix_append G ce) hpast (by omega)
      rw [ghostOf_in rp G hGA]
      obtain ⟨u, hu⟩ := hGA
      obtain ⟨t, ht⟩ := hpast
      have hut : u ++ t = ce := by
        rw [← hu, List.append_assoc] at ht; exact List.append_cancel_left ht
      refine ⟨t, by rw [hg', ← ht], fun m hm => ?_⟩
      rw [← hut]; exact List.mem_append_right _ hm

/-- **A batch of normal entries keeps the loop's view over the ghost log** (R2d'a A6, DRAFT;
`rnCfgAt_normal`'s restart form, finding (h)): the raft loop's handed log through the batch and the
backend's log agree (`hc`). -/
theorem rnCfgAtR_normal (γ : RNNames) (rp : RestartPt) (L ce : List EntryModel)
    (h : ∀ m, m ∈ ce → m.typ = W32 0)
    (hc : γ.pre ++ L ++ ce <+: rp.A₀ ∨ rp.A₀ <+: γ.pre ++ L ++ ce) :
    rnCfgAtR (GF := GF) γ rp L ⊢ rnCfgAtR γ rp (L ++ ce) := by
  unfold rnCfgAtR
  obtain ⟨d, hd, hdm⟩ := ghostOf_batch rp (γ.pre ++ L) ce hc
  rw [← List.append_assoc, hd]
  exact srvCfgView_normal γ.srv γ.nl d (fun m hm => h m (hdm m hm)) _

/-- **The loop's view after a batch with no `ConfChange` entry** (R2d'a A6, DRAFT;
`rnCfgAt_back_false`'s restart form). -/
theorem rnCfgAtR_back_false (γ : RNNames) (rp : RestartPt) (ai₀ : w64) (L ce : List EntryModel)
    (hidx : srvIdxOkW ai₀ (L ++ ce)) (hcc : ccIn ce = false)
    (hc : γ.pre ++ L ++ ce <+: rp.A₀ ∨ rp.A₀ <+: γ.pre ++ L ++ ce) :
    (if rnHands γ ce then iprop(True) else rnCfgAtR (GF := GF) γ rp L) ⊢ rnCfgAtR γ rp (L ++ ce) := by
  have hh : rnHands γ ce = false := by unfold rnHands; simp [hcc]
  rw [ite_eq_right (by rw [hh]; decide)]
  exact rnCfgAtR_normal γ rp L ce (ccIn_false_normal ai₀ L ce hidx hcc) hc

end view

end EtcdGrove
end Perennial

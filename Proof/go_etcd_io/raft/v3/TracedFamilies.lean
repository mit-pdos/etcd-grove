/-
Lean-first (no Rocq counterpart). **The traced families and the share's re-ordering** (2026-11-10,
trace-check Q8 stage 1 slice 15, `notes/decisions.md`, "Q8 stage 1 (slice 15)").

Since slice 14 the resources `raft.Step` threads through its gates are families indexed by raft's abstract
outbox (`StepG`'s `G0`, `G1`, `GE`, `Gp2`, `Gc`: `List Msg → IProp`), and a campaign's family must ignore
the order (`PermInv`). A traced caller's family is the capability with its share's pending list the
outbox's traced messages, **up to order** (`PhaseAt Φs o`: the server in phase `Φs`, the share's list
a permutation of `pendAbs C o`); `trFam` is that capability (`PermInv` by `trFam_permInv`).

The idle phase asks the list **exactly** (`SimIdle`'s `P = pendAbs C (toPState s).outbox`), so a closing
wand needs to re-order the share: **`trCapB_perm`**, the share's list replaced by a permutation of it,
inside the simulation's invariant. Sound because `simInv` reads the shares' lists only as a bag (the
pending bag's counts, `BagRep … (C.flatMap …) ++ phP`) and by membership (every pending message's
source): checked against `simInv`'s definition (`TraceSimGhost.lean`) in this slice; the other readers
of a share's list are the laws, which take whatever list the share holds (`trCap_fire_ready` hands
the list out as tokens in its order, which nothing relies on).

Also: `trCapB_monoΛ` (the node's last-event predicate weakened), `trCapB_pin` (the share named, so a
phase can state a line's exact result).
-/
module

public import Proof.go_etcd_io.raft.v3.TracedRaftStep
public import Proof.go_etcd_io.raft.v3.TracedHooksGlobal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 TraceSim

section pure
variable [GooseExts]

/-! ## The outbox's traced messages -/

/-- A message of an untraced type has no specification counterpart. -/
theorem msgAbs_untraced (C : List w64) (bl : Nat) (m : Msg) (h : m.ty.traced = false) :
    TraceSim.msgAbs C bl m = none := by
  unfold TraceSim.msgAbs
  cases hty : m.ty <;> simp_all [MsgType.traced]

theorem pendAbs_append (C : List w64) (o o' : List Msg) :
    pendAbs C (o ++ o') = pendAbs C o ++ pendAbs C o' := by
  unfold pendAbs; exact List.filterMap_append

theorem pendAbs_perm (C : List w64) {o o' : List Msg} (h : o.Perm o') :
    (pendAbs C o).Perm (pendAbs C o') := by
  unfold pendAbs; exact h.filterMap _

/-- Messages of untraced types add nothing to the traced messages. -/
theorem pendAbs_untraced (C : List w64) (o out : List Msg) (h : ∀ x ∈ out, x.ty.traced = false) :
    pendAbs C (o ++ out) = pendAbs C o := by
  rw [pendAbs_append]
  suffices hn : pendAbs C out = [] by rw [hn, List.append_nil]
  unfold pendAbs
  rw [List.filterMap_eq_nil_iff]
  intro x hx
  exact msgAbs_untraced C C.length x (h x hx)

/-! ## The idle relation, the server's part -/

/-- **`SimIdle` without the pending list**: the server's part of the idle relation (`SimIdle C s c P`
is `SimIdleS C s c ∧ P = pendAbs C s.outbox`, `simIdle_iff`). It does not read the outbox
(`simIdleS_outbox`). -/
def SimIdleS (C : List w64) (s : NState) (c : ServerC) : Prop :=
  ∃ a : Etcdraft.Server, toC (confAbs C) a = c ∧ SimServerR C C.length (toPState s) a ∧
    LogShapeOk C.length (toPState s) ∧
    uint.Z s.term < 2 ^ 63 ∧ uint.Z s.logst.committed < 2 ^ 63 ∧ uint.Z (plastIndex (toPState s)) < 2 ^ 63

theorem simIdle_iff (C : List w64) (s : NState) (c : ServerC) (P : List Etcdraft.Msg) :
    SimIdle C s c P ↔ SimIdleS C s c ∧ P = pendAbs C s.outbox := by
  unfold SimIdle SimIdleS
  constructor
  · rintro ⟨a, h1, h2, h3, h4, h5, h6, h7⟩; exact ⟨⟨a, h1, h2, h3, h5, h6, h7⟩, h4⟩
  · rintro ⟨⟨a, h1, h2, h3, h5, h6, h7⟩, h4⟩; exact ⟨a, h1, h2, h3, h4, h5, h6, h7⟩

/-- The server's part of the idle relation does not read the outbox. -/
theorem simIdleS_outbox (C : List w64) (s : NState) (o : List Msg) :
    SimIdleS C { s with outbox := o } = SimIdleS C s := rfl

theorem simIdleS_sendMsgs (C : List w64) (s : NState) (ms : List Msg) :
    SimIdleS C (sendMsgs s ms) = SimIdleS C s := rfl

/-! ## The traced families -/

/-- **A phase at an outbox, up to order**: the server in phase `Φs`, the share's pending list a
permutation of the outbox's traced messages. -/
def PhaseAt (Φs : List w64 → ServerC → Prop) (o : List Msg) :
    List w64 → ServerC → List Etcdraft.Msg → Prop :=
  fun C cs P => Φs C cs ∧ P.Perm (pendAbs C o)

theorem phaseAt_permInv (Φs : List w64 → ServerC → Prop) : PermInv (PhaseAt Φs) := by
  intro o o' h
  funext C cs P
  unfold PhaseAt
  apply propext
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, h2.trans (pendAbs_perm C h)⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, h2.trans (pendAbs_perm C h).symm⟩

/-- The phase at an outbox extended by untraced messages is the phase at the outbox. -/
theorem phaseAt_untraced (Φs : List w64 → ServerC → Prop) (o out : List Msg)
    (h : ∀ x ∈ out, x.ty.traced = false) : PhaseAt Φs (o ++ out) = PhaseAt Φs o := by
  funext C cs P
  unfold PhaseAt
  rw [pendAbs_untraced C o out h]

/-- The idle phase at `s` is the idle server's phase at its outbox. -/
theorem simIdle_phaseAt (C : List w64) (s : NState) (cs : ServerC) (P : List Etcdraft.Msg)
    (h : SimIdle C s cs P) : PhaseAt (fun C => SimIdleS C s) s.outbox C cs P := by
  obtain ⟨h1, h2⟩ := (simIdle_iff C s cs P).1 h
  exact ⟨h1, h2 ▸ List.Perm.refl _⟩

/-! ## The shares' lists, re-ordered (the invariant's pure clauses) -/

theorem flatMap_perm_one {K V : Type} [DecidableEq K] (C : List K) (f g : K → List V) (i : K)
    (hg : (g i).Perm (f i)) (ho : ∀ j, j ≠ i → g j = f j) : (C.flatMap g).Perm (C.flatMap f) := by
  induction C with
  | nil => exact List.Perm.refl _
  | cons c C ih =>
    simp only [List.flatMap_cons]
    by_cases hc : c = i
    · subst hc; exact hg.append ih
    · rw [ho c hc]; exact (List.Perm.refl _).append ih

/-- **The simulation invariant's pure clauses after node `id`'s share `(cs, P)` is re-ordered to
`(cs, P')`**: the state unchanged, the pending bag the same. -/
theorem sharePerm_pure (C : List w64) (σ : Etcdraft.State)
    (A : GMap w64 (ServerC × List Etcdraft.Msg)) (phP : List Etcdraft.Msg) (id : w64)
    (cs : ServerC) (P P' : List Etcdraft.Msg) (hperm : P'.Perm P)
    (hA : ∀ i ∈ C, ∃ Q, A !! i = some (toC σ.server (σ.s (idAbs i)), Q)) (hAid : A !! id = some (cs, P))
    (hAn : ∀ i, i ∉ C → A !! i = none)
    (hsrcA : ∀ i ∈ C, ∀ x ∈ ((A !! i).map Prod.snd).getD [], x.source = idAbs i)
    (hP : BagRep σ.pendingMessages ((C.flatMap (fun i => ((A !! i).map Prod.snd).getD [])) ++ phP)) :
    let A' := A.insert id (cs, P')
    (∀ i ∈ C, ∃ Q, A' !! i = some (toC σ.server (σ.s (idAbs i)), Q)) ∧ (∀ i, i ∉ C → A' !! i = none) ∧
      BagRep σ.pendingMessages ((C.flatMap (fun i => ((A' !! i).map Prod.snd).getD [])) ++ phP) ∧
      (∀ i ∈ C, ∀ x ∈ ((A' !! i).map Prod.snd).getD [], x.source = idAbs i) := by
  intro A'
  have hl : A' !! id = some (cs, P') := GMap.lookup_insert _ _ _
  have hne : ∀ j, j ≠ id → A' !! j = A !! j := fun j hj => GMap.lookup_insert_ne _ _ (Ne.symm hj)
  have hC : id ∈ C := by
    by_cases h : id ∈ C
    · exact h
    · rw [hAn id h] at hAid; cases hAid
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    by_cases h : i = id
    · subst h
      obtain ⟨Q, hQ⟩ := hA i hi
      rw [hAid] at hQ
      simp only [Option.some.injEq, Prod.mk.injEq] at hQ
      exact ⟨P', by rw [hl, hQ.1]⟩
    · rw [hne i h]; exact hA i hi
  · intro i hi
    have : i ≠ id := fun e => hi (e ▸ hC)
    rw [hne i this]; exact hAn i hi
  · apply bagRep_perm _ _ _ hP
    refine List.Perm.append_right phP ?_
    refine (flatMap_perm_one C _ _ id ?_ ?_).symm
    · rw [hl, hAid]; exact hperm
    · intro j hj; rw [hne j hj]
  · intro i hi x hx
    by_cases h : i = id
    · subst h
      rw [hl] at hx
      simp only [Option.map_some, Option.getD_some] at hx
      exact hsrcA _ hi x (by rw [hAid]; simpa using hperm.mem_iff.1 hx)
    · rw [hne i h] at hx; exact hsrcA i hi x hx

end pure

section law
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **The share re-ordering law**: the capability's share's pending list replaced by a permutation of
it (the phase `Φ'` of the server and the permuted list), inside the simulation's invariant, which reads
the list only as a bag and by membership (`sharePerm_pure`). Untraced, nothing. -/
theorem trCapB_perm (tr : Option GName) (γ : RaftNames) (r : Loc) (id : w64) (c : CfgM) (b : Bool)
    (Φ Φ' : List w64 → ServerC → List Etcdraft.Msg → Prop) (Λ : Option TraceEv → Prop)
    (h : ∀ C cs P, Φ C cs P → ∃ P', P'.Perm P ∧ Φ' C cs P') :
    trCapB (GF := GF) tr γ r id c b Φ Λ ⊢ |={⊤}=> trCapB tr γ r id c b Φ' Λ := by
  cases tr with
  | none => simp only [trCapB]; iintro H; imodintro; iexact H
  | some γd =>
    iintro H
    iunfold trCapB at H
    icases H with ⟨%tn, %C, %tl, %cs, %P, #Hdir, %Hpf, #Htl, #Hlg, %Hnn, #Hinv, #Hrinv, Hnode, Hbt, %HΦ⟩
    obtain ⟨P', hperm, hΦ'⟩ := h C cs P HΦ
    iinv Hinv with >Hi Hclose
    iunfold simInv at Hi
    icases Hi with ⟨%L, %σ, %A, %B, %phP, %phM, %Bt, HL, HA, HB, HBt, #Hfσ, %Hp⟩
    iunfold simNode at Hnode
    icases ghost_map_lookup $$ HA Hnode with %HAid
    obtain ⟨hrun, hsrv, hA, hAn, hPb, hMb, hpv, hcq, hsrcA, hbtC, hasc⟩ := Hp
    obtain ⟨hA', hAn', hPb', hsrc'⟩ := sharePerm_pure C σ A phP id cs P P' hperm hA HAid hAn hsrcA hPb
    imod ghost_map_update (cs, P') $$ HA Hnode with ⟨HA, Hnode⟩
    imod Hclose $$ [HL HA HB HBt] with -
    · inext; iunfold simInv
      iexists L, σ, A.insert id (cs, P'), B, phP, phM, Bt
      iframe HL HA HB HBt Hfσ
      ipureintro
      exact ⟨hrun, hsrv, hA', hAn', hPb', hMb, hpv, hcq, hsrc', hbtC, hasc⟩
    imodintro
    iunfold trCapB
    iexists tn, C, tl, cs, P'
    iunfold simNode
    iframe Hdir Htl Hlg Hinv Hrinv Hnode Hbt
    isplitr; · ipureintro; exact Hpf
    isplitr; · ipureintro; exact Hnn
    ipureintro; exact hΦ'

/-- The capability's last-event predicate weakened. -/
theorem trCapB_monoΛ (tr : Option GName) (γ : RaftNames) (r : Loc) (id : w64) (c : CfgM) (b : Bool)
    (Φ : List w64 → ServerC → List Etcdraft.Msg → Prop) (Λ Λ' : Option TraceEv → Prop)
    (h : ∀ o, Λ o → Λ' o) :
    trCapB (GF := GF) tr γ r id c b Φ Λ ⊢ trCapB tr γ r id c b Φ Λ' := by
  cases tr with
  | none => exact .rfl
  | some γd =>
    iintro H
    iunfold trCapB at H
    icases H with ⟨%tn, %C, %tl, %cs, %P, #Hdir, %Hpf, #Htl, #Hlg, %Hnn, #Hinv, #Hrinv, Hnode, ⟨%o, Hbt, %HΛ⟩, %HΦ⟩
    iunfold trCapB
    iexists tn, C, tl, cs, P
    iframe Hdir Htl Hlg Hinv Hrinv Hnode
    isplitr; · ipureintro; exact Hpf
    isplitr; · ipureintro; exact Hnn
    isplitl [Hbt]; · iexists o; iframe Hbt; ipureintro; exact h o HΛ
    ipureintro; exact HΦ

/-- **The capability's share, pinned**: its voters, server and pending list named, so that a later
phase can state the line's exact result on them (a node-event line's facts, `FxPres`, are asked of
every result the phase admits: pinning the share pins the result up to `toC`). -/
theorem trCapB_pin (γd : GName) (γ : RaftNames) (r : Loc) (id : w64) (c : CfgM) (b : Bool)
    (Φ : List w64 → ServerC → List Etcdraft.Msg → Prop) (Λ : Option TraceEv → Prop) :
    trCapB (GF := GF) (some γd) γ r id c b Φ Λ ⊢
      ∃ (C0 : List w64) (cs0 : ServerC) (P0 : List Etcdraft.Msg), ⌜Φ C0 cs0 P0⌝ ∗
        trCapB (some γd) γ r id c b (fun C cs P => C = C0 ∧ cs = cs0 ∧ P = P0 ∧ Φ C cs P) Λ := by
  iintro H
  iunfold trCapB at H
  icases H with ⟨%tn, %C, %tl, %cs, %P, #Hdir, %Hpf, #Htl, #Hlg, %Hnn, #Hinv, #Hrinv, Hnode, Hbt, %HΦ⟩
  iexists C, cs, P
  isplitr; · ipureintro; exact HΦ
  iunfold trCapB
  iexists tn, C, tl, cs, P
  iframe Hdir Htl Hlg Hinv Hrinv Hnode Hbt
  isplitr; · ipureintro; exact Hpf
  isplitr; · ipureintro; exact Hnn
  ipureintro; exact ⟨rfl, rfl, rfl, HΦ⟩

/-- `trCapB_pin` with the node among the pinned voters (review a2-r5's 1: `fxPres_heartbeat_pin`'s
`id ∈ C0` from the capability, not by unfolding it). -/
theorem trCapB_pinMem (γd : GName) (γ : RaftNames) (r : Loc) (id : w64) (c : CfgM) (b : Bool)
    (Φ : List w64 → ServerC → List Etcdraft.Msg → Prop) (Λ : Option TraceEv → Prop) :
    trCapB (GF := GF) (some γd) γ r id c b Φ Λ ⊢
      ∃ (C0 : List w64) (cs0 : ServerC) (P0 : List Etcdraft.Msg), ⌜Φ C0 cs0 P0 ∧ id ∈ C0⌝ ∗
        trCapB (some γd) γ r id c b (fun C cs P => C = C0 ∧ cs = cs0 ∧ P = P0 ∧ Φ C cs P) Λ := by
  iintro H
  iunfold trCapB at H
  icases H with ⟨%tn, %C, %tl, %cs, %P, #Hdir, %Hpf, #Htl, #Hlg, %Hnn, #Hinv, #Hrinv, Hnode, Hbt, %HΦ⟩
  iexists C, cs, P
  isplitr; · ipureintro; exact ⟨HΦ, Hpf.2.2.2.1⟩
  iunfold trCapB
  iexists tn, C, tl, cs, P
  iframe Hdir Htl Hlg Hinv Hrinv Hnode Hbt
  isplitr; · ipureintro; exact Hpf
  isplitr; · ipureintro; exact Hnn
  ipureintro; exact ⟨rfl, rfl, rfl, HΦ⟩

/-- (Amendment A6, Q23) **A pinned capability's voters are its configuration's** (up to order): a peer
raft sends to is one of them. -/
theorem trCapB_pinPerm (γd : GName) (γ : RaftNames) (r : Loc) (id : w64) (c : CfgM) (b : Bool)
    (Φ : List w64 → ServerC → List Etcdraft.Msg → Prop) (Λ : Option TraceEv → Prop) (C0 : List w64)
    (hΦ : ∀ C cs P, Φ C cs P → C = C0) :
    trCapB (GF := GF) (some γd) γ r id c b Φ Λ ⊢
      ⌜(elements c.incoming).Perm C0⌝ ∗ trCapB (some γd) γ r id c b Φ Λ := by
  iintro H
  iunfold trCapB at H
  icases H with ⟨%tn, %C, %tl, %cs, %P, #Hdir, %Hpf, #Htl, #Hlg, %Hnn, #Hinv, #Hrinv, Hnode, Hbt, %HΦ⟩
  isplitr
  · ipureintro; rw [← hΦ C cs P HΦ]; exact Hpf.2.1
  iunfold trCapB
  iexists tn, C, tl, cs, P
  iframe Hdir Htl Hlg Hinv Hrinv Hnode Hbt
  isplitr; · ipureintro; exact Hpf
  isplitr; · ipureintro; exact Hnn
  ipureintro; exact HΦ

/-- (Amendment A6, Q24) **The capability's voters fit the bootstrap log**, into its phase (the
capability's clause `C.length ≤ γ.reBoot.length`): what `stepBundle_traced.on_of_onRB` asks. -/
theorem trCapB_bootFit (tr : Option GName) (γ : RaftNames) (r : Loc) (id : w64) (c : CfgM) (b : Bool)
    (Φ : List w64 → ServerC → List Etcdraft.Msg → Prop) (Λ : Option TraceEv → Prop) :
    trCapB (GF := GF) tr γ r id c b Φ Λ ⊢
      trCapB tr γ r id c b (fun C cs P => Φ C cs P ∧ C.length ≤ γ.reBoot.length) Λ := by
  cases tr with
  | none => simp only [trCapB]; exact .rfl
  | some γd =>
    iintro H
    iunfold trCapB at H
    icases H with ⟨%tn, %C, %tl, %cs, %P, #Hdir, %Hpf, #Htl, #Hlg, %Hnn, #Hinv, #Hrinv, Hnode, Hbt, %HΦ⟩
    iunfold trCapB
    iexists tn, C, tl, cs, P
    iframe Hdir Htl Hlg Hinv Hrinv Hnode Hbt
    isplitr; · ipureintro; exact Hpf
    isplitr; · ipureintro; exact Hnn
    ipureintro; exact ⟨HΦ, Hpf.2.2.2.2⟩

/-- **The traced family**: the capability (booted `b`) in the phase `Φs` of the server, its share's
pending list the outbox's traced messages up to order (`PhaseAt`). -/
def trFam (tr : Option GName) (γ : RaftNames) (r : Loc) (id : w64) (c : CfgM) (b : Bool)
    (Φs : List w64 → ServerC → Prop) (Λ : Option TraceEv → Prop) : List Msg → IProp GF :=
  fun o => trCapB tr γ r id c b (PhaseAt Φs o) Λ

theorem trFam_permInv (tr : Option GName) (γ : RaftNames) (r : Loc) (id : w64) (c : CfgM) (b : Bool)
    (Φs : List w64 → ServerC → Prop) (Λ : Option TraceEv → Prop) :
    PermInv (trFam (GF := GF) tr γ r id c b Φs Λ) := by
  intro o o' h
  unfold trFam
  rw [phaseAt_permInv Φs o o' h]

/-- The family at an outbox extended by untraced messages. -/
theorem trFam_untraced (tr : Option GName) (γ : RaftNames) (r : Loc) (id : w64) (c : CfgM) (b : Bool)
    (Φs : List w64 → ServerC → Prop) (Λ : Option TraceEv → Prop) (o out : List Msg)
    (h : ∀ x ∈ out, x.ty.traced = false) :
    trFam (GF := GF) tr γ r id c b Φs Λ (o ++ out) = trFam tr γ r id c b Φs Λ o := by
  unfold trFam
  rw [phaseAt_untraced Φs o out h]

/-- **The idle capability from the idle server's family**: at the outbox of `s'`, a state whose
server part is `s`'s (`SimIdleS C s = SimIdleS C s'`), the share re-ordered (`trCapB_perm`). -/
theorem trFam_idle (tr : Option GName) (γ : RaftNames) (r : Loc) (id : w64) (c : CfgM) (b : Bool)
    (s s' : NState) (Λ : Option TraceEv → Prop) (hS : ∀ C, SimIdleS C s = SimIdleS C s') :
    trFam (GF := GF) tr γ r id c b (fun C => SimIdleS C s) Λ s'.outbox ⊢
      |={⊤}=> trCapB tr γ r id c b (fun C => SimIdle C s') Λ := by
  unfold trFam
  apply trCapB_perm
  rintro C cs P ⟨h1, h2⟩
  refine ⟨pendAbs C s'.outbox, h2.symm, ?_⟩
  rw [simIdle_iff]
  exact ⟨hS C ▸ h1, rfl⟩

end law

end EtcdGrove
end Perennial

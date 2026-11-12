/-
Lean-first (no Rocq counterpart). Trace-check's layer D, S7 (part 2) (2026-11-11; `notes/decisions.md`,
"S7 (part 2)"): **the ghost state `RunConcurrent` allocates** before its `StartNode`s, and what each
voter's `StartNode` takes of it.

The order (amendment A4's): the recorder's trace `γt` (`syncRecorder_alloc`, with the simulation's half
`traceFrag γt []`), then the simulation's names (`traceNames_alloc`: the shares' map at the bootstrap
servers, the empty bag, the voters' flags unset, no voter's bootstrap complete, the directory `γd`
naming them, persistent), then the
traced cluster (`cluster_alloc_traced` with `γd`), then the shared invariant from a voter's `nodeBoot`
(`Cluster.traceSim_alloc`); together `harness_alloc`. Each voter's part (`voterStart`): its `nodeBoot`,
durable state and vacant slot, its share and its flag, which with the recorder as its trace logger and
the configuration's premises make `startTraceC` (`startTraceC_intro`).
-/
module

public import Proof.go_etcd_io.raft.v3.TracedNodeApi

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace TraceCheck

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 TraceSim

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **A ghost map of the distinct keys `vs`**, each at `f`: the authority over a map holding exactly
them, and each key's element. -/
theorem ghostMap_alloc_list {V : Type} [Pos.Countable V] (f : w64 → V) (vs : List w64)
    (Hnd : vs.Nodup) :
    ⊢ |==> ∃ (γ : GName) (A : GMap w64 V), ghostMapAuth (GF := GF) γ 1 A ∗
      ⌜(∀ i ∈ vs, A !! i = some (f i)) ∧ ∀ i, i ∉ vs → A !! i = none⌝ ∗
      [∗list] i ∈ vs, i ↪[γ] f i := by
  imod ghost_map_alloc_empty (GF := GF) (K := w64) (V := V) with ⟨%γ, Ha⟩
  suffices H : ∀ (ws : List w64), ws.Nodup → ⊢ (ghostMapAuth (GF := GF) γ 1 (∅ : GMap w64 V)) ==∗
      ∃ A : GMap w64 V, ghostMapAuth γ 1 A ∗
        ⌜(∀ i ∈ ws, A !! i = some (f i)) ∧ ∀ i, i ∉ ws → A !! i = none⌝ ∗
        [∗list] i ∈ ws, i ↪[γ] f i by
    imod H vs Hnd $$ Ha with ⟨%A, Ha, %HA, Hs⟩
    imodintro
    iexists γ, A
    iframe Ha Hs
    ipureintro; exact HA
  intro ws
  induction ws with
  | nil =>
    intro _
    iintro Ha
    imodintro
    iexists ∅
    iframe Ha
    isplitr
    · ipureintro
      exact ⟨fun _ h => absurd h (List.not_mem_nil), fun _ _ => GMap.lookup_empty _⟩
    iapply (BigSepL.bigSepL_nil (Φ := fun _ i => iprop(i ↪[γ] f i : IProp GF))).2
    iempintro
  | cons w ws ih =>
    intro Hnd'
    rw [List.nodup_cons] at Hnd'
    iintro Ha
    imod ih Hnd'.2 $$ Ha with ⟨%A, Ha, %HA, Hs⟩
    have Hw : A.lookup w = none := HA.2 w Hnd'.1
    imod ghost_map_insert (GF := GF) w (f w) Hw $$ Ha with ⟨Ha, Hw'⟩
    imodintro
    iexists A.insert w (f w)
    iframe Ha
    isplitr
    · ipureintro
      refine ⟨fun i hi => ?_, fun i hi => ?_⟩
      · by_cases h : i = w
        · subst h; exact GMap.lookup_insert A i (f i)
        · rw [GMap.lookup_insert_ne A (f w) (Ne.symm h)]
          exact HA.1 i ((List.mem_cons.1 hi).resolve_left h)
      · have h : i ≠ w := fun h => hi (h ▸ List.mem_cons_self)
        rw [GMap.lookup_insert_ne A (f w) (Ne.symm h)]
        exact HA.2 i (fun h' => hi (List.mem_cons_of_mem _ h'))
    iapply (BigSepL.bigSepL_cons (Φ := fun _ i => iprop(i ↪[γ] f i : IProp GF))).2
    iframe Hw' Hs

/-- A voter's bootstrap share (`startTraceC`'s): its server at the bootstrap state, nothing pending. -/
abbrev bootShare (vs : List w64) (i : w64) : ServerC × List Etcdraft.Msg :=
  (toC (confAbs vs) ((simInit vs).s (idAbs i)), [])

/-- **The simulation's names**, for the voters `vs` and the recorder's trace `γt`: the shares' map at
the bootstrap servers, the empty bag, the flags unset, the empty list of completed voters (amendment
A8) (their authorities for
`Cluster.traceSim_alloc`, their elements for the voters' `StartNode`s), and the directory `γd` naming
them (persistent), before the traced cluster (whose trace mode is `γd`). -/
theorem traceNames_alloc (γt : GName) (vs : List w64) (Hnd : vs.Nodup) :
    ⊢ |==> ∃ (γd : GName) (tn : TraceNames) (A : GMap w64 (ServerC × List Etcdraft.Msg))
        (Bt : GMap w64 (Bool × Option TraceEv)),
      ⌜tn.tr = γt ∧ tn.voters = vs ∧
        (∀ i ∈ vs, A !! i = some (toC (confAbs vs) ((simInit vs).s (idAbs i)), [])) ∧
        (∀ i, i ∉ vs → A !! i = none) ∧ (∀ i ∈ vs, Bt !! i = some (false, none))⌝ ∗
      traceDir (GF := GF) γd tn ∗ ghostMapAuth tn.st 1 A ∗
      ghostMapAuth tn.bag 1 (∅ : GMap Nat Etcdraft.Msg) ∗ ghostMapAuth tn.bt 1 Bt ∗
      monoListAuthOwn tn.dn 1 ([] : List w64) ∗
      [∗list] i ∈ vs, simNode tn i (toC (confAbs vs) ((simInit vs).s (idAbs i))) [] ∗
        simBoot tn i false none := by
  imod ghostMap_alloc_list (GF := GF) (bootShare vs) vs Hnd with ⟨%st, %A, HA, %HAp, HAs⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := Etcdraft.Msg) with ⟨%bag, HB⟩
  imod ghostMap_alloc_list (GF := GF) (fun _ => ((false, none) : Bool × Option TraceEv)) vs Hnd
    with ⟨%bt, %Bt, HBt, %HBtp, HBts⟩
  imod mono_list_own_alloc (GF := GF) ([] : List w64) with ⟨%dn, HDn, -⟩
  let tn : TraceNames := ⟨γt, st, bag, vs, bt, dn⟩
  imod dghostVar_alloc (GF := GF) tn with ⟨%γd, Hd⟩
  imod dghostVar_persist (GF := GF) γd 1 tn $$ Hd with #Hd
  imodintro
  iexists γd, tn, A, Bt
  isplitr
  · ipureintro
    exact ⟨rfl, rfl, HAp.1, HAp.2, HBtp.1⟩
  iframe HA HB HBt HDn
  isplitr
  · unfold traceDir; iexact Hd
  iapply (BigSepL.bigSepL_sep_eqv (Φ := fun _ i => simNode (GF := GF) tn i
      (toC (confAbs vs) ((simInit vs).s (idAbs i))) [])
    (Ψ := fun _ i => simBoot (GF := GF) tn i false none)).2
  unfold simNode simBoot
  isplitl [HAs]
  · iexact HAs
  · iexact HBts

/-- **A voter's part of the harness's allocation**: what its `StartNode` takes besides the logger and
the configuration (`nodeBoot`, its durable state at `RaftState.init`, its vacant slot), and its share
and flag of the simulation (`startTraceC`'s). -/
def voterStart (γ : Cluster) (N : Namespace) (vs : List w64) (ctxs : List (List w8))
    (tn : TraceNames) (i : w64) : IProp GF :=
  iprop(nodeBoot γ N vs ctxs i ∗ (raftState γ i RaftState.init ∗ nodeVacant γ i) ∗
    simNode tn i (toC (confAbs vs) ((simInit vs).s (idAbs i))) [] ∗ simBoot tn i false none)

/-- **The harness's allocation** (see the file header): from the bootstrap log's marshalling and the
recorder's half of its trace `γt`, a traced cluster `γ` of the voters `vs` (in the caller's namespace
`N`, with no snapshot directory and no duplicated proposal) whose trace mode names the simulation's
names `tn` (`tn.tr = γt`), the simulation's invariant, the cluster's client resources, and each voter's
part. -/
theorem harness_alloc (N : Namespace) (vs : List w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (γt : GName) (E : CoPset) (hE : ↑N ⊆ E)
    (Hrb : receiptBound GF ≤ 2 ^ 64 - 2) (Hne : vs ≠ []) (Hnd : vs.Nodup) (Hnz : W64 0 ∉ vs)
    (Hlen : (vs.length : Int) < 2 ^ 62) (HB : BootLog vs ctxs boot) :
    ⊢ bootMarshal (GF := GF) vs ctxs (LogEntry.toEntries boot 0) -∗ traceFrag γt [] ={E}=∗
      ∃ (γ : Cluster) (γd : GName) (tn : TraceNames),
        ⌜Cluster.trace γ = some γd ∧ tn.tr = γt ∧ tn.voters = vs ∧ γ.dup = false ∧
          γ.snapLoc = (fun _ => none) ∧ γ.bootLen = boot.length⌝ ∗
        traceDir γd tn ∗ Cluster.traceSim γ vs tn ∗
        ownCommittedOps γ boot ∗ ownReadCtxs γ ∅ ∗ isCluster γ N ∗ ownConfDecisions γ ∅ ∗
        confAt γ 0 (Membership.simple (GMap.listToSet vs)) ∗ ownSnapsMade γ [] ∗
        isCommittedLogLb γ boot ∗
        [∗list] i ∈ vs, voterStart γ N vs ctxs tn i := by
  iintro #Hm Hfr
  imod traceNames_alloc (GF := GF) γt vs Hnd
    with ⟨%γd, %tn, %A, %Bt, %Htn, #Hdir, HA, HB0, HBt, HDn, Hsh⟩
  obtain ⟨Htr, Hvs, HA1, HA2, HBt1⟩ := Htn
  subst Htr
  imod cluster_alloc_traced (GF := GF) N vs ctxs boot false (fun _ => none) γd E Hrb Hne Hnd Hnz Hlen
    HB $$ Hm with ⟨%γ, %Hγ, %Hgt, Hops, Hctx, #Hcl, Hdec, #Hca, Hsm, Hrs, #Hlb, #Hbs⟩
  obtain ⟨v0, vs', rfl⟩ : ∃ v0 vs', vs = v0 :: vs' := List.exists_cons_of_ne_nil Hne
  ihave #Hb0 : nodeBoot γ N (v0 :: vs') ctxs v0 $$ []
  · icases (BigSepL.bigSepL_cons (Φ := fun _ i => nodeBoot (GF := GF) γ N (v0 :: vs') ctxs i)).1
      $$ Hbs with ⟨#H, -⟩
    iexact H
  imod Cluster.traceSim_alloc (GF := GF) γ N (v0 :: vs') ctxs v0 tn A Bt E hE HA1 HA2 HBt1
    $$ [Hfr HA HB0 HBt HDn] with #Hinv
  · iframe Hb0 Hfr HA HB0 HBt HDn
  imodintro
  iexists γ, γd, tn
  isplitr
  · ipureintro; exact ⟨Hgt, rfl, Hvs, Hγ.1, Hγ.2.1, Hγ.2.2⟩
  iframe Hdir Hinv Hops Hctx Hcl Hdec Hca Hsm Hlb
  unfold voterStart
  iapply (BigSepL.bigSepL_sep_eqv (Φ := fun _ i => nodeBoot (GF := GF) γ N (v0 :: vs') ctxs i)
    (Ψ := fun _ i => iprop((raftState (GF := GF) γ i RaftState.init ∗ nodeVacant γ i) ∗
      simNode tn i (toC (confAbs (v0 :: vs')) ((simInit (v0 :: vs')).s (idAbs i))) [] ∗
      simBoot tn i false none))).2
  iframe Hbs
  iapply (BigSepL.bigSepL_sep_eqv (Φ := fun _ i => iprop(raftState (GF := GF) γ i RaftState.init ∗
      nodeVacant γ i))
    (Ψ := fun _ i => iprop(simNode (GF := GF) tn i
      (toC (confAbs (v0 :: vs')) ((simInit (v0 :: vs')).s (idAbs i))) [] ∗
      simBoot tn i false none))).2
  iframe Hrs Hsh

/-- **A voter's `startTraceC`**: in the traced cluster `γ` of the directory `γd`, its share and flag,
the simulation's invariant and directory, a trace logger of the names' trace that is not nil, and the
configuration's premises (pre-vote and check-quorum off, fewer than `2^40` voters), and (2026-11-12,
trace-check step 5) the receipts' fit with the ceiling's headroom (`traceFits`). -/
theorem startTraceC_intro (γ : Cluster) (γd : GName) (tn : TraceNames) (vs : List w64) (cv : Config)
    (Htr : Cluster.trace γ = some γd) (Hvs : tn.voters = vs) (Hpv : cv.PreVote' = false)
    (Hcq : cv.CheckQuorum' = false) (Hlen : vs.length < 2 ^ 40)
    (Hnil : cv.TraceLogger' ≠ interface.nil) (N : Namespace)
    (Hfit : receiptBound GF + max γ.bootLen 2 ≤ 2 ^ 61) :
    ⊢ traceDir (GF := GF) γd tn -∗ Cluster.traceSim γ vs tn -∗ isTraceLogger tn.tr cv.TraceLogger' -∗
      simNode tn cv.ID' (toC (confAbs vs) ((simInit vs).s (idAbs cv.ID'))) [] -∗
      simBoot tn cv.ID' false none -∗ startTraceC γ N vs cv := by
  iintro #Hdir #Hinv #Hlog Hsh Hbt
  ihave #Hf := traceFits_intro (GF := GF) γ N Hfit
  unfold startTraceC
  rw [Htr]
  iexists tn
  iframe Hdir Hinv Hlog Hsh Hbt Hf
  ipureintro
  exact ⟨⟨Hpv, Hcq⟩, Hvs, Hlen, Hnil⟩

end ghost

end TraceCheck
end EtcdGrove
end Perennial

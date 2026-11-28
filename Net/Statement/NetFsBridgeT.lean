/-
**The crash bridge with the thread bound and the protocol registry** (hraft_robust R7; coordinator-E's
decision (f)): `robust_of_netFsBoot_addrs` (`NetFsBridge.lean`) over Perennial's
`goose_dist_mixed_crash_adequacy_below` (`DistAdequacy.lean`), whose executions are `Robust`'s,
`DistCrashNstepsBelow` with the thread bound `threads`, in place of `goose_dist_mixed_crash_adequacy`
(whose thread bound is of every execution of `n` steps, `n + 2`):

- every machine's obligation gets its generation's thread bound, `threadBound ≤ threads`
  (`CrashBootWpT`, `StableBootWpT`: `CrashBootWp`, `StableBootWp` under that premise), independent of the
  step bound; a program whose specs need a small thread bound (net/rpc's server: `2 ^ 31`) is covered
  for every execution of fewer than `bound` steps;
- the start obligation gets the network protocols' registry (`regCtx`, allocated here by
  `netProto_alloc`, as dsv-epaxos's `robust_of_distProtoLisRBTT`) with the deployment's addresses unset.

The first generation of a crashing machine and the stable machines' shares are as in
`robust_of_netFsBoot`. The deployment's premises are `Robust`'s and the address facts (distinct and
valid). General: names no program. Untrusted, proved.
-/
module

public import Net.Statement.NetFsBridge

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

namespace Net

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Robustness NetFs

attribute [local instance] kvraftExts kvraftExtsSemantics kvraftExtsInterp kvraftExtsCrashInterp
  kvraftExts_hasNet kvraftExts_hasFs GooseGlobalGS.gooseInvGS

section bridgeT
variable [GoGlobalContext] {GF : BundledGFunctors} [hPre : GooseGpreS GF]

/-- **`StableBootWp` with the machine's thread bound at most `T`**: under every local ghost state `L`
whose Go context is `lctx` and whose thread bound is at most `T`, from `P`, its files' start
resources, no package initialized and its main thread's token, the boot program `e` returns `#()`
and is not stuck. -/
def StableBootWpT [lctx : GoLocalContext] [G : GooseGlobalGS .hasLC GF] (T : Nat) (e : Expr)
    (σ : state) (P : IProp GF) : Prop :=
  ∀ L : GooseLocalGS GF, L.goose_go_local_context = lctx →
    @ThreadGS.threadBound GF L.goose_threadGS ≤ T →
    letI : HeapGS .hasLC GF := ⟨G, L⟩
    P ⊢ fsStartRes L (extLocal Fs.fsExt σ.world) -∗ ownGoState (hG := L.goose_go_stateGS) ∅ -∗
      threadTok ={⊤}=∗ WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜v = #()⌝ }}

/-- **`CrashBootWp` with every generation's thread bound at most `T`**: under every local ghost
state `L` whose Go context is `lctx` and whose thread bound is at most `T`, from `P L` and its main
thread's token, the boot program `e` returns `#()` and is not stuck, and after a crash `P` holds of
the next generation `L'` (from `L`'s `crashed`, `L'`'s invariant of the mapped cells, the file
system's crash rest for some new history `V'`, `L'`'s empty package state and a later credit). -/
def CrashBootWpT [lctx : GoLocalContext] [G : GooseGlobalGS .hasLC GF] (T : Nat) (e : Expr)
    (P : GooseLocalGS GF → IProp GF) : Prop :=
  ∀ L : GooseLocalGS GF, L.goose_go_local_context = lctx →
    @ThreadGS.threadBound GF L.goose_threadGS ≤ T →
    letI : HeapGS .hasLC GF := ⟨G, L⟩
    P L ⊢ threadTok ={⊤}=∗ WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜v = #()⌝ }} ∗
      ∀ (L' : GooseLocalGS GF) (V' : Fs.Hist), crashed (hC := L.goose_crashGS) -∗
        Fs.osInv (L := L') -∗
        Fs.crashRest (fun _ _ => True) (Fs.gooseOsGS (L := L)) (Fs.gooseOsGS (L := L')) [] false
          V' -∗
        ownGoState (hG := L'.goose_go_stateGS) ∅ -∗ £ 1 ={⊤}=∗ P L'

/-- `CrashBootWp` gives `CrashBootWpT` at any bound. -/
theorem CrashBootWpT.of_crashBootWp [lctx : GoLocalContext] [GooseGlobalGS .hasLC GF]
    (T : Nat) (e : Expr) (P : GooseLocalGS GF → IProp GF) (H : CrashBootWp e P) :
    CrashBootWpT T e P := fun L hL _ => H L hL

/-- `StableBootWp` gives `StableBootWpT` at any bound. -/
theorem StableBootWpT.of_stableBootWp [lctx : GoLocalContext] [GooseGlobalGS .hasLC GF]
    (T : Nat) (e : Expr) (σ : state) (P : IProp GF) (H : StableBootWp e σ P) :
    StableBootWpT T e σ P := fun L hL _ => H L hL

/-- `crashPre` with `CrashBootWpT`. -/
def crashPreT [lctx : GoLocalContext] [G : GooseGlobalGS .hasLC GF] (T : Nat)
    (crashing : List (Expr × state)) (i : Nat) (L : GooseLocalGS GF) : IProp GF :=
  iprop(∃ Q : GooseLocalGS GF → IProp GF,
    ⌜∀ m : Expr × state, crashing[i]? = some m → CrashBootWpT T m.1 Q⌝ ∗ Q L)

/-- A stable machine's obligation (`nodeWp`, at the thread bound `T`), from `StableBootWpT T`. -/
theorem nodeWp_of_stableBootT [lctx : GoLocalContext] [G : GooseGlobalGS .hasLC GF] (T : Nat)
    (e : Expr) (σ : state) (P : IProp GF) (hf : Fresh lctx σ)
    (hfs : Fs.FsInit (extLocal Fs.fsExt σ.world)) (H : StableBootWpT T e σ P) :
    P ⊢ nodeWp T e σ (fun v => v = #()) := by
  unfold nodeWp
  iintro HP %L
  unfold nodeWpBody
  rw [hf.2.1]
  iintro %hTb %hL Hls Hgs Htok
  imod fsStartRes_of_localStart L σ.world hfs $$ Hls with Hr
  iapply H L (hL.trans hf.1) (Nat.le_of_eq hTb) $$ HP Hr Hgs Htok

/-- A crashing machine's first start (`nodeStart`), with `Q` safe in every generation under the
thread bound `T`. -/
theorem nodeStart_of_crashBootT [lctx : GoLocalContext] [G : GooseGlobalGS .hasLC GF] (T T' : Nat)
    (crashing : List (Expr × state)) (i : Nat) (m : Expr × state) (hm : crashing[i]? = some m)
    (hf : Fresh lctx m.2) (hfs : Fs.FsInit (extLocal Fs.fsExt m.2.world))
    (Q : GooseLocalGS GF → IProp GF) (HQ : CrashBootWpT T m.1 Q) :
    (∀ L : GooseLocalGS GF, ⌜L.goose_go_local_context = lctx⌝ -∗
        fsStartRes L (extLocal Fs.fsExt m.2.world) -∗ ownGoState (hG := L.goose_go_stateGS) ∅
        ={⊤}=∗ Q L) ⊢
      nodeStart T' m.2 (crashPreT T crashing i) := by
  unfold nodeStart
  rw [hf.2.1]
  iintro H %L %_ %hL Hls Hgs
  imod fsStartRes_of_localStart L m.2.world hfs $$ Hls with Hr
  imod H $$ %L %(hL.trans hf.1) Hr Hgs with HQL
  imodintro
  unfold crashPreT
  iexists Q
  iframe HQL
  ipureintro
  intro m' hm'
  rw [hm] at hm'
  cases hm'
  exact HQ

/-- **The bridge, with the thread bound and the registry** (see the file header): from the addresses
`addrs` distinct and valid, and an update from the protocols' registry and every address unset to
- for each crashing machine `i`, a precondition `Pc i` of its generations, with its boot program
  safe in every generation whose thread bound is at most `threads` (`CrashBootWpT`), and its first
  generation's `Pc i L` from that generation's file start resources and empty package state, and
- for each stable machine `j`, a share `Ps j`, with its boot program safe from it under the thread
  bound `threads` (`StableBootWpT`),

`Robust crashing stable g threads bound`; the update is given `receiptBound GF ≤ bound`. -/
theorem robust_of_netFsBootT [lctx : GoLocalContext] (addrs : List GoString)
    (crashing stable : List (Expr × state)) (g : GlobalState) (threads bound : Nat)
    (Hnd : addrs.Nodup) (Hok : ∀ a ∈ addrs, addrOk a = true)
    (Hstart : ∀ [GooseGlobalGS .hasLC GF] [NetProtoGS], receiptBound GF ≤ bound →
      ⊢ regCtx -∗ ([∗list] a ∈ addrs, addrUnset a) ={⊤}=∗
        ∃ (Pc : Nat → GooseLocalGS GF → IProp GF) (Ps : Nat → IProp GF),
          ⌜∀ (i : Nat) (m : Expr × state), crashing[i]? = some m →
            CrashBootWpT threads m.1 (Pc i)⌝ ∗
          ⌜∀ (j : Nat) (m : Expr × state), stable[j]? = some m →
            StableBootWpT threads m.1 m.2 (Ps j)⌝ ∗
          ([∗list] i ↦ m ∈ crashing, ∀ L : GooseLocalGS GF,
            ⌜L.goose_go_local_context = lctx⌝ -∗ fsStartRes L (extLocal Fs.fsExt m.2.world) -∗
            ownGoState (hG := L.goose_go_stateGS) ∅ ={⊤}=∗ Pc i L) ∗
          [∗list] j ↦ _m ∈ stable, Ps j) :
    Robust crashing stable g threads bound := by
  intro hfresh hig hil n κs c hsteps hn i tp σ hi e he
  have hfs : ∀ m ∈ crashing ++ stable, Fs.FsInit (extLocal Fs.fsExt m.2.world) :=
    fun m hm => (hil m hm).2.1
  have hfc : ∀ (k : Nat) (m : Expr × state), crashing[k]? = some m → m ∈ crashing ++ stable :=
    fun _ m hm => List.mem_append_left _ (List.mem_of_getElem? hm)
  have hfst : ∀ (k : Nat) (m : Expr × state), stable[k]? = some m → m ∈ crashing ++ stable :=
    fun _ m hm => List.mem_append_right _ (List.mem_of_getElem? hm)
  have H := goose_dist_mixed_crash_adequacy_below (GF := GF) (n + 1) threads crashing stable g
    (fun _ v => v = #()) (fun _ p h => intoVal_ne_PanicV () p h.symm) ⟨hig.1, trivial, trivial⟩
    (fun m hm => ⟨trivial, hfs m hm, trivial⟩) (fun i L => crashPreT threads crashing i L) ?_ ?_
    n κs c hsteps (Nat.lt_succ_self n) (fun m hm => (hfresh m hm).2.2) i tp σ hi
  · exact ⟨H.2.1 e he, H.2.2 e he⟩
  · -- the global setup: the registry, the addresses, then the client's start
    intro G HN
    iintro Hg
    ihave Hnet := kvraft_net_globalStart g.globalWorld $$ Hg
    ihave Hs := addrs_start (Gg := G) (extGlobal netExt g.globalWorld) addrs Hnd Hok $$ Hnet
    imod netProto_alloc (Gg := G) ⊤ with ⟨%π, #Hreg⟩
    imod (@Hstart G π (by omega)) $$ Hreg Hs with ⟨%Pc, %Ps, %HPc, %HPs, Hc, Hst⟩
    imodintro
    isplitl [Hc]
    · iapply BigSepL.bigSepL_mono ?_ $$ Hc
      intro k m hm
      exact nodeStart_of_crashBootT threads threads crashing k m hm (hfresh m (hfc k m hm))
        (hfs m (hfc k m hm)) (Pc k) (HPc k m hm)
    · iapply BigSepL.bigSepL_mono ?_ $$ Hst
      intro k m hm
      exact nodeWp_of_stableBootT threads m.1 m.2 (Ps k) (hfresh m (hfst k m hm))
        (hfs m (hfst k m hm)) (HPs k m hm)
  · -- every generation of a crashing machine: its WP, and its next precondition
    intro hG _ hT k e' σ' Hes Hlctx
    obtain ⟨G, L⟩ := hG
    have hL : L.goose_go_local_context = lctx :=
      Hlctx.trans (hfresh (e', σ') (hfc k _ Hes)).1
    unfold crashPreT
    iintro ⟨%Q, %HQ, HQL⟩ Htok
    imod HQ (e', σ') Hes L hL (Nat.le_of_eq hT) $$ HQL Htok with ⟨Hwp, Hcr⟩
    imodintro
    iframe Hwp
    iintro %L' Hcrd Hcs Hgs Hlc
    icases kvraft_fs_crashStart L L' $$ Hcs with Hcs
    unfold Fs.osCrashStart
    icases Hcs with ⟨Hv, %V', Hr⟩
    imod Fs.osInv_alloc (L := L') ⊤ $$ Hv with #Hinv
    imod Hcr $$ %L' %V' Hcrd Hinv Hr Hgs Hlc with HQL'
    imodintro
    iexists Q
    iframe HQL'
    ipureintro
    exact HQ

end bridgeT

end Net
end Perennial

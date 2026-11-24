/-
**The all-stable bridge over any list of extensions that has the net extension** (proved; 2026-11-23,
`notes/putget-dist-plan.md` section 5): a distributed deployment whose machines never crash is robust
(`Robust []`, `Robustness/Statement.lean`) under its start (`DistDeploy`) when each machine's boot program
is safe from its share of an update from the deployment's addresses unset.

`DistBridge.lean`'s theorems are this one at the net extension alone (`netExts`); `putget_safe`'s is at
`[idIssueExt, fsExt, netExt]`. What a list of extensions has to give, beyond `HasExt netExt`:

- a `GooseGpreS GF` for its ghost-state bundle;
- the adequacy theorem's conditions on the initial states (`extsInitgP`, `extsInitP`) from `Robust`'s own
  premises (`extsInitGlobal`, `extsInitLocal`) and whatever the deployment's statement adds
  (`robust_of_distBootI`); with `GooseInitCompat` (each interpretation accepts every initial state of its
  semantics) nothing is added (`robust_of_distBootE`). `etcdFsSem` (`Fs.fsSemWithS`) keeps `ExtSemantics`'s
  default `initLocal` (any state), so a statement over it adds `FsInit` per machine;
- nothing else: the net extension's start resources are taken out of the list's by its position
  (`hasExt_globalStart`), whatever the other extensions are.

**`Robust`'s thread bound** (`robust_of_distBootILT`, over Perennial's `goose_dist_adequacy_below`): the
logic's thread bound is the statement's `threads`, and the receipt bound ranges up to `bound` alone
(`DistBootWpSLT`). The bridges before it (`robust_of_distBootIL` and the ones built on it) tie the thread
bound to the receipts (`threadBound GF = receiptBound GF + 1`), so a thread cap also caps the steps.
-/
module

public import Perennial.GooseLang.DistAdequacy
public import Perennial.GooseLang.InitAdequacy
public import Perennial.Golang.Defn
public import GooseLang.Ext.Net.Adequacy
public import GooseLang.Ext.Net.Proto
public import Net.Statement.DistDeploy
public import Robustness.Statement

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

namespace Net

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Robustness

/-! ## An extension's start resources, out of the list's

Facts of Perennial's definitions (`Exts.globalStart`, `ExtIn`), proved here until they move to Perennial
(`notes/perennial-changes.md`, 2026-11-23). -/

/-- The global start resources of a list of extensions hold those of the extension at position `m`. -/
theorem extIn_globalStart_get {GF : BundledGFunctors} {E : GooseExt} :
    {l : List GooseExt} → (m : ExtIn E l) → (Is : ExtTuple ExtInterp l) →
    (gs : Exts.GlobalGS l Is GF) → (w : ExtsGlobalState l) →
    Exts.globalStart l Is gs w ⊢ (m.get Is).globalStart (m.globalGS gs) (m.get w)
  | _ :: _, .here, _, _, _ => sep_elim_left
  | _ :: _, .there m, Is, gs, w => sep_elim_right.trans (extIn_globalStart_get m Is.2 gs.2 w.2)

theorem ExtInterp.globalStart_cast {GF : BundledGFunctors} {X : GooseExt} {J K : ExtInterp X}
    (h : J = K) (x : J.GlobalGS GF) (g : X.GlobalState) :
    J.globalStart x g =
      K.globalStart (cast (congrArg (fun J : ExtInterp X => J.GlobalGS GF) h) x) g := by
  subst h; rfl

/-- **The global start resources of the extension `X`** of the program's list (`HasExt X`). -/
theorem hasExt_globalStart [GooseExts] [GooseSemantics] [GooseInterp] {X : GooseExt}
    [ExtSemantics X] [I : ExtInterp X] [hX : HasExt X] {hlc : HasLC} {GF : BundledGFunctors}
    [G : GooseGlobalGS hlc GF] (w : ExtsGlobalState exts) :
    extsGlobalStart (GF := GF) w ⊢ I.globalStart (extGlobalGS X) (extGlobal X w) := by
  have H := extIn_globalStart_get hX.mem GooseInterp.interps G.gooseExtsGlobalGS w
  rw [ExtInterp.globalStart_cast hX.interp_eq'] at H
  exact H

/-! ## The bridge -/

/-- With no boot program, an execution has no crash: it is a plain distributed execution. -/
theorem distNsteps_of_crash_nil [GooseExts] [GooseSemantics] [GoGlobalContext] {n : Nat}
    {c c' : DistCfg} {κs : List Observation} (h : DistCrashNsteps [] n c κs c') :
    DistNsteps n c κs c' := by
  induction h with
  | refl c => exact .refl c
  | cons hs _ ih =>
    cases hs with
    | step hs => exact .cons hs ih
    | crash _ hb _ => simp at hb

attribute [local instance] GooseGlobalGS.gooseInvGS

section bridge
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hPre : GooseGpreS GF]

/-- A machine's boot program `e` is safe from `P`: under every ghost state `hG` over the global one
`G` whose Go context is `lctx` (the statement's, `Robust`'s `Fresh`), from no package initialized, it
returns `#()` (a Go `main`'s result) and is not stuck. (A proof destructs `hG` and substitutes the
context, so that the program's instances over `lctx`, `[go.Semantics]` and its packages'
`Assumptions`, apply.) -/
def DistBootWpE [lctx : GoLocalContext] [G : GooseGlobalGS .hasLC GF] (e : Expr) (P : IProp GF) :
    Prop :=
  ∀ hG : HeapGS .hasLC GF, hG.goose_globalGS = G →
    hG.goose_localGS.goose_go_local_context = lctx →
    P ⊢ ownGoState (hG := hG.goose_localGS.goose_go_stateGS) ∅ -∗
      WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜v = #()⌝ }}

omit [HasExt netExt] hPre in
/-- A machine's obligation in `goose_dist_adequacy` (`nodeWp`) from `DistBootWpE`. -/
theorem nodeWp_of_distBootE [lctx : GoLocalContext] [G : GooseGlobalGS .hasLC GF] (T : Nat)
    (e : Expr) (σ : state) (P : IProp GF) (hf : Fresh lctx σ) (H : DistBootWpE e P) :
    P ⊢ nodeWp T e σ (fun v => v = #()) := by
  unfold nodeWp
  iintro HP %L
  unfold nodeWpBody
  iintro %_ %hL Hls Hgs -
  rw [hf.2.1]
  imodintro
  iapply H ⟨G, L⟩ rfl (hL.trans hf.1) $$ HP Hgs

/-- **A machine's boot program `e` is safe from `P`, from its whole start** (the obligation
`goose_dist_adequacy` gives a machine, `nodeWpBody`, under any ghost state over the global one `G` whose Go
context is `lctx`): from its extensions' local start resources (`extsLocalStart`: its files, its
listeners), no package initialized, the main thread's token, and the bounds of the logic (the receipts'
`receiptBound GF ≤ bound`, the threads' `threadBound GF = receiptBound GF + 1`: the adequacy theorem's
choices for an execution of fewer than `bound` steps), it returns `#()` and is not stuck. -/
def DistBootWpS [lctx : GoLocalContext] [G : GooseGlobalGS .hasLC GF] (bound : Nat) (e : Expr)
    (σ : state) (P : IProp GF) : Prop :=
  ∀ hG : HeapGS .hasLC GF, hG.goose_globalGS = G →
    hG.goose_localGS.goose_go_local_context = lctx →
    receiptBound GF ≤ bound → threadBound GF = receiptBound GF + 1 →
    letI : HeapGS .hasLC GF := hG
    P ⊢ extsLocalStart (L := hG.goose_localGS) σ.world -∗
      ownGoState (hG := hG.goose_localGS.goose_go_stateGS) ∅ -∗ threadTok ={⊤}=∗
      WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜v = #()⌝ }}

omit [HasExt netExt] in
/-- `DistBootWpE` gives `DistBootWpS` (the start resources and the token dropped). -/
theorem distBootWpS_of_E [lctx : GoLocalContext] [G : GooseGlobalGS .hasLC GF] (bound : Nat)
    (e : Expr) (σ : state) (P : IProp GF) (H : DistBootWpE e P) : DistBootWpS bound e σ P := by
  intro hG hGG hL _ _
  iintro HP - Hgs -
  imodintro
  iapply H hG hGG hL $$ HP Hgs

omit [HasExt netExt] in
/-- A machine's obligation in `goose_dist_adequacy` (`nodeWp`, at `T = N + 1` threads and `N` receipts)
from `DistBootWpS`. -/
theorem nodeWp_of_distBootS [lctx : GoLocalContext] [G : GooseGlobalGS .hasLC GF] (bound N : Nat)
    (hN : receiptBound GF = N) (hb : N ≤ bound) (e : Expr) (σ : state) (P : IProp GF)
    (hf : Fresh lctx σ) (H : DistBootWpS bound e σ P) :
    P ⊢ nodeWp (N + 1) e σ (fun v => v = #()) := by
  unfold nodeWp
  iintro HP %L
  unfold nodeWpBody
  iintro %hT %hL Hls Hgs Htok
  rw [hf.2.1]
  iapply H ⟨G, L⟩ rfl (hL.trans hf.1) (by omega) (by omega) $$ HP Hls Hgs Htok

/-- **`DistBootWpS` with a floor on the receipts** (`lo ≤ receiptBound GF`): a machine's boot program safe
from its share and its whole start at every receipt bound from `lo` to `bound` (`robust_of_distBootIL` picks
`max (n + 1) lo` receipts for an execution of `n` steps). A program whose specs need a few levels of a thread
token from its first step (etcd's served member, `srvLevels`: `srvLevelK ≤ threadBound GF`) takes them from
the floor. `DistBootWpS bound` is the floor `0` (`distBootWpSL_of_S`). -/
def DistBootWpSL [lctx : GoLocalContext] [G : GooseGlobalGS .hasLC GF] (lo bound : Nat) (e : Expr)
    (σ : state) (P : IProp GF) : Prop :=
  ∀ hG : HeapGS .hasLC GF, hG.goose_globalGS = G →
    hG.goose_localGS.goose_go_local_context = lctx →
    lo ≤ receiptBound GF → receiptBound GF ≤ bound → threadBound GF = receiptBound GF + 1 →
    letI : HeapGS .hasLC GF := hG
    P ⊢ extsLocalStart (L := hG.goose_localGS) σ.world -∗
      ownGoState (hG := hG.goose_localGS.goose_go_stateGS) ∅ -∗ threadTok ={⊤}=∗
      WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜v = #()⌝ }}

omit [HasExt netExt] in
/-- `DistBootWpS` gives `DistBootWpSL` at any floor. -/
theorem distBootWpSL_of_S [lctx : GoLocalContext] [G : GooseGlobalGS .hasLC GF] (lo bound : Nat)
    (e : Expr) (σ : state) (P : IProp GF) (H : DistBootWpS bound e σ P) :
    DistBootWpSL lo bound e σ P :=
  fun hG hGG hL _ hb hT => H hG hGG hL hb hT

omit [HasExt netExt] in
/-- A machine's obligation in `goose_dist_adequacy` (`nodeWp`, at `T = N + 1` threads and `N` receipts,
`lo ≤ N ≤ bound`) from `DistBootWpSL`. -/
theorem nodeWp_of_distBootSL [lctx : GoLocalContext] [G : GooseGlobalGS .hasLC GF] (lo bound N : Nat)
    (hN : receiptBound GF = N) (hlo : lo ≤ N) (hb : N ≤ bound) (e : Expr) (σ : state) (P : IProp GF)
    (hf : Fresh lctx σ) (H : DistBootWpSL lo bound e σ P) :
    P ⊢ nodeWp (N + 1) e σ (fun v => v = #()) := by
  unfold nodeWp
  iintro HP %L
  unfold nodeWpBody
  iintro %hT %hL Hls Hgs Htok
  rw [hf.2.1]
  iapply H ⟨G, L⟩ rfl (hL.trans hf.1) (by omega) (by omega) (by omega) $$ HP Hls Hgs Htok

/-- **The bridge with a floor on the receipts** (`robust_of_distBootI` at `DistBootWpSL lo`, `lo ≤ bound`):
an execution of `n` steps is run at `max (n + 1) lo` receipts and one more thread (`goose_dist_adequacy`'s
thread premise holds at any bound from `n + 2`). -/
theorem robust_of_distBootIL [lctx : GoLocalContext] (addrs : List GoString)
    (nodes : List (Expr × state)) (g : GlobalState) (threads bound lo : Nat) (hlo : lo ≤ bound)
    (HI : extsInitGlobal g → (∀ m, m ∈ nodes → extsInitLocal m.2 g) →
      extsInitgP g.globalWorld ∧ ∀ m, m ∈ nodes → extsInitP m.2.world g.globalWorld)
    (Hstart : ∀ [GooseGlobalGS .hasLC GF], lo ≤ receiptBound GF → receiptBound GF ≤ bound →
      ⊢ ([∗list] a ∈ addrs, addrUnset a) ={⊤}=∗
        ∃ Ps : Nat → IProp GF,
          ⌜∀ (i : Nat) (m : Expr × state), nodes[i]? = some m →
            DistBootWpSL lo bound m.1 m.2 (Ps i)⌝ ∗
          [∗list] i ↦ _m ∈ nodes, Ps i) :
    DistDeploy addrs nodes g → Robust [] nodes g threads bound := by
  rintro ⟨Hnd, Hok, -, -⟩ hfresh hg hl n κs c hsteps hn i tp σ hi e he
  simp only [List.map_nil, List.nil_append] at hfresh hl hsteps
  have Hlive : DistThreadsBelow (max (n + 1) lo + 1) n (distInit nodes g) := by
    intro k κs' c' hk h j tp' σ' hj
    have := DistThreadsBelow.of_single (n := n) (c := distInit nodes g) ?_ k κs' c' hk h j tp' σ' hj
    · omega
    · intro j tp' σ' hj
      simp only [distInit, List.getElem?_map] at hj
      obtain ⟨x, hx, hx'⟩ := Option.map_eq_some_iff.mp hj
      simp only [Prod.mk.injEq] at hx'
      obtain ⟨-, rfl⟩ := hx'
      exact (hfresh x (List.mem_of_getElem? hx)).2.2
  have H := goose_dist_adequacy (GF := GF) (max (n + 1) lo) (max (n + 1) lo + 1) nodes g
    (fun _ v => v = #()) (fun _ p h => intoVal_ne_PanicV () p h.symm) (HI hg hl).1 (HI hg hl).2
    ?_ n κs c (distNsteps_of_crash_nil hsteps.nsteps) (by omega)
    (fun m hm => (hfresh m hm).2.2) Hlive i tp σ hi
  · exact ⟨H.2.1 e he, H.2.2 e he⟩
  · intro G HN
    iintro Hg
    ihave Hnet := hasExt_globalStart (X := netExt) g.globalWorld $$ Hg
    ihave Hs := addrs_start (Gg := G) (extGlobal netExt g.globalWorld) addrs Hnd Hok $$ Hnet
    imod Hstart (by omega) (by omega) $$ Hs with ⟨%Ps, %HP, HPs⟩
    imodintro
    iapply BigSepL.bigSepL_mono ?_ $$ HPs
    intro j m hm
    exact nodeWp_of_distBootSL lo bound (max (n + 1) lo) HN (by omega) (by omega) m.1 m.2 (Ps j)
      (hfresh m (List.mem_of_getElem? hm)) (HP j m hm)

/-- **`DistBootWpSL` with the thread bound fixed** (`threadBound GF = T`, `Robust`'s separate thread bound): a
machine's boot program safe from its share and its whole start at the thread bound `T` and every receipt bound
from `lo` to `bound`. A program's thread facts (a pool of `n` slots, `threadBound GF ≤ n + 1`; the levels of a
thread token, `srvLevels`) come from `T`, its lifetime counters' caps from `bound`. -/
def DistBootWpSLT [lctx : GoLocalContext] [G : GooseGlobalGS .hasLC GF] (T lo bound : Nat) (e : Expr)
    (σ : state) (P : IProp GF) : Prop :=
  ∀ hG : HeapGS .hasLC GF, hG.goose_globalGS = G →
    hG.goose_localGS.goose_go_local_context = lctx →
    lo ≤ receiptBound GF → receiptBound GF ≤ bound → threadBound GF = T →
    letI : HeapGS .hasLC GF := hG
    P ⊢ extsLocalStart (L := hG.goose_localGS) σ.world -∗
      ownGoState (hG := hG.goose_localGS.goose_go_stateGS) ∅ -∗ threadTok ={⊤}=∗
      WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜v = #()⌝ }}

omit [HasExt netExt] in
/-- A machine's obligation in `goose_dist_adequacy_below` (`nodeWp`, at `T` threads and `N` receipts,
`lo ≤ N ≤ bound`) from `DistBootWpSLT`. -/
theorem nodeWp_of_distBootSLT [lctx : GoLocalContext] [G : GooseGlobalGS .hasLC GF] (T lo bound N : Nat)
    (hN : receiptBound GF = N) (hlo : lo ≤ N) (hb : N ≤ bound) (e : Expr) (σ : state) (P : IProp GF)
    (hf : Fresh lctx σ) (H : DistBootWpSLT T lo bound e σ P) :
    P ⊢ nodeWp T e σ (fun v => v = #()) := by
  unfold nodeWp
  iintro HP %L
  unfold nodeWpBody
  iintro %hT %hL Hls Hgs Htok
  rw [hf.2.1]
  iapply H ⟨G, L⟩ rfl (hL.trans hf.1) (by omega) (by omega) hT $$ HP Hls Hgs Htok

/-- **The bridge with `Robust`'s thread bound** (over Perennial's `goose_dist_adequacy_below`): an execution
of `n` steps along which every machine keeps fewer than `threads` threads is run at `max (n + 1) lo`
receipts and the thread bound `threads`, so each machine's boot program is safe at `threadBound GF =
threads` and any receipt bound from `lo` to `bound` (`DistBootWpSLT`; `lo ≤ bound`). -/
theorem robust_of_distBootILT [lctx : GoLocalContext] (addrs : List GoString)
    (nodes : List (Expr × state)) (g : GlobalState) (threads bound lo : Nat) (hlo : lo ≤ bound)
    (HI : extsInitGlobal g → (∀ m, m ∈ nodes → extsInitLocal m.2 g) →
      extsInitgP g.globalWorld ∧ ∀ m, m ∈ nodes → extsInitP m.2.world g.globalWorld)
    (Hstart : ∀ [GooseGlobalGS .hasLC GF], lo ≤ receiptBound GF → receiptBound GF ≤ bound →
      ⊢ ([∗list] a ∈ addrs, addrUnset a) ={⊤}=∗
        ∃ Ps : Nat → IProp GF,
          ⌜∀ (i : Nat) (m : Expr × state), nodes[i]? = some m →
            DistBootWpSLT threads lo bound m.1 m.2 (Ps i)⌝ ∗
          [∗list] i ↦ _m ∈ nodes, Ps i) :
    DistDeploy addrs nodes g → Robust [] nodes g threads bound := by
  rintro ⟨Hnd, Hok, -, -⟩ hfresh hg hl n κs c hsteps hn i tp σ hi e he
  simp only [List.map_nil, List.nil_append] at hfresh hl hsteps
  have H := goose_dist_adequacy_below (GF := GF) (max (n + 1) lo) threads nodes g
    (fun _ v => v = #()) (fun _ p h => intoVal_ne_PanicV () p h.symm) (HI hg hl).1 (HI hg hl).2
    ?_ n κs c hsteps (by omega) (fun m hm => (hfresh m hm).2.2) i tp σ hi
  · exact ⟨H.2.1 e he, H.2.2 e he⟩
  · intro G HN
    iintro Hg
    ihave Hnet := hasExt_globalStart (X := netExt) g.globalWorld $$ Hg
    ihave Hs := addrs_start (Gg := G) (extGlobal netExt g.globalWorld) addrs Hnd Hok $$ Hnet
    imod Hstart (by omega) (by omega) $$ Hs with ⟨%Ps, %HP, HPs⟩
    imodintro
    iapply BigSepL.bigSepL_mono ?_ $$ HPs
    intro j m hm
    exact nodeWp_of_distBootSLT threads lo bound (max (n + 1) lo) HN (by omega) (by omega) m.1 m.2
      (Ps j) (hfresh m (List.mem_of_getElem? hm)) (HP j m hm)

/-- **The bridge, over any list of extensions with the net extension** (see the file header), with the
interpretations' conditions on the initial states (`extsInitgP`, `extsInitP`) given from `Robust`'s
(`HI`; `robust_of_distBootE` when the interpretations accept every initial state): under the
deployment's start, an update from the extension's start resources (every address of the deployment
unset) to a share `Ps i` for each machine `i`, each machine's boot program safe from its share and its
whole start (`DistBootWpS`), give `Robust` with no crashing machine, for any thread bound
(`robust_of_distBootIL` at the floor `0`). -/
theorem robust_of_distBootI [lctx : GoLocalContext] (addrs : List GoString)
    (nodes : List (Expr × state)) (g : GlobalState) (threads bound : Nat)
    (HI : extsInitGlobal g → (∀ m, m ∈ nodes → extsInitLocal m.2 g) →
      extsInitgP g.globalWorld ∧ ∀ m, m ∈ nodes → extsInitP m.2.world g.globalWorld)
    (Hstart : ∀ [GooseGlobalGS .hasLC GF], receiptBound GF ≤ bound →
      ⊢ ([∗list] a ∈ addrs, addrUnset a) ={⊤}=∗
        ∃ Ps : Nat → IProp GF,
          ⌜∀ (i : Nat) (m : Expr × state), nodes[i]? = some m → DistBootWpS bound m.1 m.2 (Ps i)⌝ ∗
          [∗list] i ↦ _m ∈ nodes, Ps i) :
    DistDeploy addrs nodes g → Robust [] nodes g threads bound :=
  robust_of_distBootIL (GF := GF) addrs nodes g threads bound 0 (Nat.zero_le _) HI
    (fun _ hb => by
      iintro Hs
      imod Hstart hb $$ Hs with ⟨%Ps, %HP, HPs⟩
      imodintro
      iexists Ps
      iframe HPs
      ipureintro
      exact fun i m hm => distBootWpSL_of_S 0 bound m.1 m.2 (Ps i) (HP i m hm))

/-- `robust_of_distBootI` when every extension's interpretation accepts its semantics' initial states
(`GooseInitCompat`). -/
theorem robust_of_distBootE (Hc : GooseInitCompat) [lctx : GoLocalContext] (addrs : List GoString)
    (nodes : List (Expr × state)) (g : GlobalState) (threads bound : Nat)
    (Hstart : ∀ [GooseGlobalGS .hasLC GF], receiptBound GF ≤ bound →
      ⊢ ([∗list] a ∈ addrs, addrUnset a) ={⊤}=∗
        ∃ Ps : Nat → IProp GF,
          ⌜∀ (i : Nat) (m : Expr × state), nodes[i]? = some m → DistBootWpE m.1 (Ps i)⌝ ∗
          [∗list] i ↦ _m ∈ nodes, Ps i) :
    DistDeploy addrs nodes g → Robust [] nodes g threads bound :=
  robust_of_distBootI (GF := GF) addrs nodes g threads bound
    (fun hg hl => ⟨extsInitgP_of_init Hc hg, fun m hm => extsInitP_of_init Hc (hl m hm)⟩)
    (fun hb => by
      iintro Hs
      imod Hstart hb $$ Hs with ⟨%Ps, %HP, HPs⟩
      imodintro
      iexists Ps
      iframe HPs
      ipureintro
      exact fun i m hm => distBootWpS_of_E bound m.1 m.2 (Ps i) (HP i m hm))

end bridge

end Net
end Perennial

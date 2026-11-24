/-
**The crash bridge over any list of extensions with the net and Linux file extensions** (etcd-dist
stage D4c, `notes/etcd-dist-plan.md` §12; proved, untrusted): `NetFsBridge.lean`'s
`robust_of_netFsBoot{,_addrs}` (hard-wired to `[netExt, fsExt]` at `fs_semantics`) for a bundle of
extensions given by its instances, so that it applies to etcd's `[idIssueExt, fsExt at etcdFsSem,
netExt]` (`etcdstart/NetExtsCrash.lean`) as to kvnet's (`NetFsBridgeGKvnet.lean` re-derives
`robust_of_netFsBoot_addrs`).

Two layers:

1. `robust_of_crashBootIL`: any list of extensions with the net extension and a crash interpretation
   (`GooseCrashInterp`). A crashing machine's generation is safe from its precondition, and gives it
   back for the next generation from the extensions' raw crash resources (`CrashBootWpE`:
   `extsCrashStart L L'`); its first generation's precondition comes from the raw start resources
   (`extsLocalStart`); a stable machine's obligation is `DistBootWpSL` (`DistBridgeExts.lean`). The
   step and thread bounds as `robust_of_distBootIL`: an execution of `n` steps is run at `max (n + 1) lo`
   receipts and one thread more.
2. `robust_of_netFsBootG`: the list also has the Linux file extension, at any semantics with
   `FsSemOk` (`fs_semantics`, `etcdFsSem := fsSemWithS etcdSQ (fun _ _ => True)`, ...), and its crash
   resources split (`HC`) into the file extension's at some crash premise `Q` (`osCrashStart Q`: the
   crash interpretation `fs_crash_interp` has `Q := True`, `fs_crash_interpS SQ Q` has `Q`) and the rest
   `X L L'` (the other extensions'). A crashing machine's generation then gets, after a crash, the
   cells' invariant of the new generation, the file system's crash rest (`crashRest Q`) and `X`
   (`CrashBootWpG Q X`), and its first generation the file start resources (`fsStartResG`, from
   `FsInit`).

What the list must give, beyond the instances (`HasExt netExt`, `HasExt fsExt`, `GooseCrashInterp`,
`GooseGpreS GF`): `HC`, and the interpretations' conditions on the initial states with every crashing
machine's `FsInit` (`HI`), from `Robust`'s own premises (`extsInitGlobal`, `extsInitLocal`). Where the
file semantics states `FsInit` as its `initLocal` (`fs_semantics`) it follows from them; where it does
not (`fsSemWithS`, until D4a) the deployment's statement adds it.
-/
module

public import Perennial.GooseLang.DistAdequacy
public import Perennial.GooseLang.InitAdequacy
public import Perennial.Golang.Defn
public import GooseLang.Ext.Fs.Adequacy
public import Net.Statement.DistBridgeExts

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

namespace Net

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Robustness

/-! ## An extension's local start resources, out of the list's

As `hasExt_globalStart` (`DistBridgeExts.lean`), for the local ones. -/

/-- The local start resources of a list of extensions hold those of the extension at position `m`. -/
theorem extIn_localStart_get {GF : BundledGFunctors} {E : GooseExt} :
    {l : List GooseExt} → (m : ExtIn E l) → (Is : ExtTuple ExtInterp l) →
    (gs : Exts.LocalGS l Is GF) → (w : ExtsLocalState l) →
    Exts.localStart l Is gs w ⊢ (m.get Is).localStart (m.localGS gs) (m.get w)
  | _ :: _, .here, _, _, _ => sep_elim_left
  | _ :: _, .there m, Is, gs, w => sep_elim_right.trans (extIn_localStart_get m Is.2 gs.2 w.2)

theorem ExtInterp.localStart_cast {GF : BundledGFunctors} {X : GooseExt} {J K : ExtInterp X}
    (h : J = K) (x : J.LocalGS GF) (σ : X.LocalState) :
    J.localStart x σ =
      K.localStart (cast (congrArg (fun J : ExtInterp X => J.LocalGS GF) h) x) σ := by
  subst h; rfl

/-- **The local start resources of the extension `X`** of the program's list (`HasExt X`). -/
theorem hasExt_localStart [GooseExts] [GooseSemantics] [GooseInterp] {X : GooseExt}
    [ExtSemantics X] [I : ExtInterp X] [hX : HasExt X] {GF : BundledGFunctors}
    [L : GooseLocalGS GF] (w : ExtsLocalState exts) :
    extsLocalStart (GF := GF) w ⊢ I.localStart (extLocalGS X) (extLocal X w) := by
  have H := extIn_localStart_get hX.mem GooseInterp.interps L.gooseExtsLocalGS w
  rw [ExtInterp.localStart_cast hX.interp_eq'] at H
  exact H

attribute [local instance] GooseGlobalGS.gooseInvGS

/-! ## Layer 1: any list of extensions with the net extension and a crash interpretation -/

section bridgeE
variable [GooseExts] [GooseSemantics] [GooseInterp] [GooseCrashInterp] [HasExt netExt]
  [GoGlobalContext]
variable {GF : BundledGFunctors} [hPre : GooseGpreS GF]

/-- **A crashing machine's boot program `e` is safe from `P`, in every generation, from the
extensions' raw crash resources**: under every local ghost state `L` whose Go context is `lctx` (the
statement's, `Robust`'s `Fresh`), with the bounds of the logic (`lo ≤ receiptBound GF ≤ bound`, the
thread bound one more), from `P L` and its main thread's token, it returns `#()` and is not stuck, and
after a crash of its machine `P` holds again of the next generation `L'`, from `L`'s `crashed`, the
extensions' crash resources (`extsCrashStart L L'`), `L'`'s empty package state and a later credit. -/
def CrashBootWpE [lctx : GoLocalContext] [G : GooseGlobalGS .hasLC GF] (lo bound : Nat) (e : Expr)
    (P : GooseLocalGS GF → IProp GF) : Prop :=
  ∀ L : GooseLocalGS GF, L.goose_go_local_context = lctx →
    lo ≤ receiptBound GF → receiptBound GF ≤ bound →
    @ThreadGS.threadBound GF L.goose_threadGS = receiptBound GF + 1 →
    letI : HeapGS .hasLC GF := ⟨G, L⟩
    P L ⊢ threadTok ={⊤}=∗ WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜v = #()⌝ }} ∗
      ∀ L' : GooseLocalGS GF, crashed (hC := L.goose_crashGS) -∗ extsCrashStart L L' -∗
        ownGoState (hG := L'.goose_go_stateGS) ∅ -∗ £ 1 ={⊤}=∗ P L'

/-- The precondition, in `goose_dist_mixed_crash_adequacy`, of crashing machine `i` in the generation
`L`: some `Q` for which its boot program is safe in every generation (`CrashBootWpE`), and `Q L`
(`NetFsBridge.lean`'s `crashPre`: `Q` is chosen in the start update). -/
def crashPreE [lctx : GoLocalContext] [G : GooseGlobalGS .hasLC GF] (lo bound : Nat)
    (crashing : List (Expr × state)) (i : Nat) (L : GooseLocalGS GF) : IProp GF :=
  iprop(∃ Q : GooseLocalGS GF → IProp GF,
    ⌜∀ m : Expr × state, crashing[i]? = some m → CrashBootWpE lo bound m.1 Q⌝ ∗ Q L)

/-- A crashing machine's first start in `goose_dist_mixed_crash_adequacy` (`nodeStart`, at `N + 1`
threads and `N` receipts): from the client's start of `Q` (every `L` of the statement's Go context, its
thread bound, from the extensions' local start resources and the empty package state), with `Q` safe in
every generation. -/
theorem nodeStart_of_crashBootE [lctx : GoLocalContext] [G : GooseGlobalGS .hasLC GF]
    (lo bound N : Nat) (hN : receiptBound GF = N) (crashing : List (Expr × state)) (i : Nat)
    (m : Expr × state) (hm : crashing[i]? = some m) (hf : Fresh lctx m.2)
    (Q : GooseLocalGS GF → IProp GF) (HQ : CrashBootWpE lo bound m.1 Q) :
    (∀ L : GooseLocalGS GF, ⌜L.goose_go_local_context = lctx⌝ -∗
        ⌜@ThreadGS.threadBound GF L.goose_threadGS = receiptBound GF + 1⌝ -∗
        extsLocalStart (L := L) m.2.world -∗ ownGoState (hG := L.goose_go_stateGS) ∅
        ={⊤}=∗ Q L) ⊢
      nodeStart (N + 1) m.2 (crashPreE lo bound crashing i) := by
  sorry

/-- **The bridge, layer 1** (see the file header): over any list of extensions with the net extension
and a crash interpretation, with the interpretations' conditions on the initial states given from
`Robust`'s (`HI`), the deployment's addresses distinct and valid, and an update from the network's start
resources (every address unset) to
- for each crashing machine `i`, a precondition `Pc i` of its generations, with its boot program safe in
  every generation (`CrashBootWpE`) and its first generation's `Pc i L` from that generation's local
  start resources and empty package state, and
- for each stable machine `j`, a share `Ps j`, with its boot program safe from it and its whole start
  (`DistBootWpSL`),

gives `Robust crashing stable g threads bound`, for any thread bound; the update and the obligations get
`lo ≤ receiptBound GF ≤ bound`. -/
theorem robust_of_crashBootIL [lctx : GoLocalContext] (addrs : List GoString)
    (crashing stable : List (Expr × state)) (g : GlobalState) (threads bound lo : Nat)
    (hlo : lo ≤ bound) (Hnd : addrs.Nodup) (Hok : ∀ a ∈ addrs, addrOk a = true)
    (HI : extsInitGlobal g → (∀ m, m ∈ crashing ++ stable → extsInitLocal m.2 g) →
      extsInitgP g.globalWorld ∧ ∀ m, m ∈ crashing ++ stable → extsInitP m.2.world g.globalWorld)
    (Hstart : ∀ [GooseGlobalGS .hasLC GF], lo ≤ receiptBound GF → receiptBound GF ≤ bound →
      ⊢ ([∗list] a ∈ addrs, addrUnset a) ={⊤}=∗
        ∃ (Pc : Nat → GooseLocalGS GF → IProp GF) (Ps : Nat → IProp GF),
          ⌜∀ (i : Nat) (m : Expr × state), crashing[i]? = some m →
            CrashBootWpE lo bound m.1 (Pc i)⌝ ∗
          ⌜∀ (j : Nat) (m : Expr × state), stable[j]? = some m →
            DistBootWpSL lo bound m.1 m.2 (Ps j)⌝ ∗
          ([∗list] i ↦ m ∈ crashing, ∀ L : GooseLocalGS GF,
            ⌜L.goose_go_local_context = lctx⌝ -∗
            ⌜@ThreadGS.threadBound GF L.goose_threadGS = receiptBound GF + 1⌝ -∗
            extsLocalStart (L := L) m.2.world -∗
            ownGoState (hG := L.goose_go_stateGS) ∅ ={⊤}=∗ Pc i L) ∗
          [∗list] j ↦ _m ∈ stable, Ps j) :
    Robust crashing stable g threads bound := by
  sorry

end bridgeE

/-! ## Layer 2: the list also has the Linux file extension -/

section bridgeFs
variable [GooseExts] [GooseSemantics] [GooseInterp] [GooseCrashInterp] [HasExt netExt]
  [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hPre : GooseGpreS GF]

/-- The file extension's resources of a generation that starts from the file system `st` with every
file as on disk (a machine's first start), under the local ghost state `L` (`NetFsBridge.lean`'s
`fsStartRes`, for any list with the file extension): the invariant of the mapped cells, every file
whole (each byte durable) and the tree's shared view (`osShared`), with nothing logged. -/
def fsStartResG [G : GooseGlobalGS .hasLC GF] (L : GooseLocalGS GF) (st : Fs.OsState) : IProp GF :=
  iprop(Fs.osInv (L := L) ∗
    ([∗map] i ↦ f ∈ st.fs.files, Fs.osFileStart (L := L) i f) ∗
    Fs.osShared (L := L) st.fs.roots (st.fs.treeDur, []))

/-- The local start resources of the list give `fsStartResG`, for files as on disk (`FsInit`). -/
theorem fsStartResG_of_localStart [G : GooseGlobalGS .hasLC GF] (L : GooseLocalGS GF)
    (w : ExtsLocalState exts) (h : Fs.FsInit (extLocal Fs.fsExt w)) :
    ⊢ extsLocalStart (GF := GF) (L := L) w ={⊤}=∗ fsStartResG L (extLocal Fs.fsExt w) := by
  sorry

/-- **A crashing machine's boot program `e` is safe from `P`, in every generation**, with the file
extension's crash resources at the crash premise `Q` and the other extensions' `X`: as `CrashBootWpE`,
with, after a crash, in place of the raw crash resources, `L'`'s invariant of the mapped cells, the file
system's crash rest (the restart's files and tree, `Fs.crashRest Q`, for some new history `V'`) and
`X L L'` (`NetFsBridge.lean`'s `CrashBootWp` is `Q := True`, `X` dropped, no bounds). -/
def CrashBootWpG [lctx : GoLocalContext] [G : GooseGlobalGS .hasLC GF]
    (Q : Fs.OsState → Fs.OsState → Prop) (X : GooseLocalGS GF → GooseLocalGS GF → IProp GF)
    (lo bound : Nat) (e : Expr) (P : GooseLocalGS GF → IProp GF) : Prop :=
  ∀ L : GooseLocalGS GF, L.goose_go_local_context = lctx →
    lo ≤ receiptBound GF → receiptBound GF ≤ bound →
    @ThreadGS.threadBound GF L.goose_threadGS = receiptBound GF + 1 →
    letI : HeapGS .hasLC GF := ⟨G, L⟩
    P L ⊢ threadTok ={⊤}=∗ WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜v = #()⌝ }} ∗
      ∀ (L' : GooseLocalGS GF) (V' : Fs.Hist), crashed (hC := L.goose_crashGS) -∗
        Fs.osInv (L := L') -∗
        Fs.crashRest Q (Fs.gooseOsGS (L := L)) (Fs.gooseOsGS (L := L')) [] false V' -∗
        X L L' -∗ ownGoState (hG := L'.goose_go_stateGS) ∅ -∗ £ 1 ={⊤}=∗ P L'

/-- `CrashBootWpG` gives `CrashBootWpE` when the crash resources split as `HC` says. -/
theorem crashBootWpE_of_G [lctx : GoLocalContext] [G : GooseGlobalGS .hasLC GF]
    (Q : Fs.OsState → Fs.OsState → Prop) (X : GooseLocalGS GF → GooseLocalGS GF → IProp GF)
    (HC : ∀ L L' : GooseLocalGS GF, extsCrashStart L L' ⊢
      Fs.osCrashStart Q (Fs.gooseOsGS (L := L)) (Fs.gooseOsGS (L := L')) ∗ X L L')
    (lo bound : Nat) (e : Expr) (P : GooseLocalGS GF → IProp GF)
    (H : CrashBootWpG Q X lo bound e P) : CrashBootWpE lo bound e P := by
  sorry

/-- **A stable machine's boot program `e`, from the local state `σ`, is safe from `P`**, from the file
start resources (`fsStartResG`), no package initialized and its main thread's token, with the bounds of
the logic (`NetFsBridge.lean`'s `StableBootWp`, with bounds). -/
def StableBootWpG [lctx : GoLocalContext] [G : GooseGlobalGS .hasLC GF] (lo bound : Nat) (e : Expr)
    (σ : state) (P : IProp GF) : Prop :=
  ∀ L : GooseLocalGS GF, L.goose_go_local_context = lctx →
    lo ≤ receiptBound GF → receiptBound GF ≤ bound →
    @ThreadGS.threadBound GF L.goose_threadGS = receiptBound GF + 1 →
    letI : HeapGS .hasLC GF := ⟨G, L⟩
    P ⊢ fsStartResG L (extLocal Fs.fsExt σ.world) -∗ ownGoState (hG := L.goose_go_stateGS) ∅ -∗
      threadTok ={⊤}=∗ WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜v = #()⌝ }}

/-- `StableBootWpG` gives `DistBootWpSL`, for files as on disk. -/
theorem distBootWpSL_of_stableBootG [lctx : GoLocalContext] [G : GooseGlobalGS .hasLC GF]
    (lo bound : Nat) (e : Expr) (σ : state) (P : IProp GF)
    (hfs : Fs.FsInit (extLocal Fs.fsExt σ.world)) (H : StableBootWpG lo bound e σ P) :
    DistBootWpSL lo bound e σ P := by
  sorry

/-- **The bridge, layer 2** (see the file header): over any list of extensions with the net and file
extensions whose crash resources split as `HC` says, with the interpretations' conditions on the
initial states and every crashing machine's files as on disk given from `Robust`'s (`HI`), the
deployment's addresses distinct and valid, and an update from the network's start resources (every
address unset) to
- for each crashing machine `i`, a precondition `Pc i` of its generations, with its boot program safe in
  every generation (`CrashBootWpG Q X`) and its first generation's `Pc i L` from the file start resources
  (`fsStartResG`) and the empty package state, and
- for each stable machine `j`, a share `Ps j`, with its boot program safe from it and its whole start
  (`DistBootWpSL`; from `StableBootWpG` by `distBootWpSL_of_stableBootG`),

gives `Robust crashing stable g threads bound`, for any thread bound. -/
theorem robust_of_netFsBootG [lctx : GoLocalContext] (Q : Fs.OsState → Fs.OsState → Prop)
    (X : GooseLocalGS GF → GooseLocalGS GF → IProp GF)
    (HC : ∀ L L' : GooseLocalGS GF, extsCrashStart L L' ⊢
      Fs.osCrashStart Q (Fs.gooseOsGS (L := L)) (Fs.gooseOsGS (L := L')) ∗ X L L')
    (addrs : List GoString) (crashing stable : List (Expr × state)) (g : GlobalState)
    (threads bound lo : Nat) (hlo : lo ≤ bound)
    (Hnd : addrs.Nodup) (Hok : ∀ a ∈ addrs, addrOk a = true)
    (HI : extsInitGlobal g → (∀ m, m ∈ crashing ++ stable → extsInitLocal m.2 g) →
      extsInitgP g.globalWorld ∧
      (∀ m, m ∈ crashing ++ stable → extsInitP m.2.world g.globalWorld) ∧
      ∀ m, m ∈ crashing → Fs.FsInit (extLocal Fs.fsExt m.2.world))
    (Hstart : ∀ [GooseGlobalGS .hasLC GF], lo ≤ receiptBound GF → receiptBound GF ≤ bound →
      ⊢ ([∗list] a ∈ addrs, addrUnset a) ={⊤}=∗
        ∃ (Pc : Nat → GooseLocalGS GF → IProp GF) (Ps : Nat → IProp GF),
          ⌜∀ (i : Nat) (m : Expr × state), crashing[i]? = some m →
            CrashBootWpG Q X lo bound m.1 (Pc i)⌝ ∗
          ⌜∀ (j : Nat) (m : Expr × state), stable[j]? = some m →
            DistBootWpSL lo bound m.1 m.2 (Ps j)⌝ ∗
          ([∗list] i ↦ m ∈ crashing, ∀ L : GooseLocalGS GF,
            ⌜L.goose_go_local_context = lctx⌝ -∗
            ⌜@ThreadGS.threadBound GF L.goose_threadGS = receiptBound GF + 1⌝ -∗
            fsStartResG L (extLocal Fs.fsExt m.2.world) -∗
            ownGoState (hG := L.goose_go_stateGS) ∅ ={⊤}=∗ Pc i L) ∗
          [∗list] j ↦ _m ∈ stable, Ps j) :
    Robust crashing stable g threads bound := by
  sorry

end bridgeFs

end Net
end Perennial

/-
**From per-machine boot WPs to a robustness statement with crashing and stable machines, over the
network and Linux files** (etcd-dist stage D3, `notes/dist-crash-bridge.md`): the bridge from
Perennial's `goose_dist_mixed_crash_adequacy` (`DistAdequacy.lean`: machines with boot programs, which
crash and restart, and machines without, which never crash) to `Robust crashing stable g threads
bound` (`Robustness/Statement.lean`), for machines over `[netExt, fsExt]` (`kvnetExts`,
`GooseLang/Ext/NetFs/Adequacy.lean`), under `NetFsDeploy` (`NetFsDeploy.lean`). It is to crashes
what `robust_of_distBootRB` (`DistBridge.lean`) is to deployments whose machines never crash.

What a machine's proof is given:
- every machine, at its first start: the file extension's start resources of its files (`fsStartRes`:
  the invariant of the mapped cells, every file whole and durable, the tree's shared view with nothing
  logged, `osShared`), its
  empty package state and its main thread's token; its net resources are the global ones, which the
  start obligation `Hstart` gets for the deployment's addresses (each unset, `addrUnset`);
- a crashing machine, after each crash (`CrashBootWp`'s frame): a fresh local ghost state `L'` (a
  new generation: no heap, no thread, no listener), its empty package state, the cells' invariant
  `osInv` of `L'`, the file system's crash rest (`crashRest`, the restart's files and tree for
  some new history `V'`, related to what the crashed generation knew) and a later credit, from which it
  re-establishes its own precondition for `L'` (the next generation's `osShared` from `crashRest_treeS'`
  and the crashed generation's persistent `osSharedInv`). The network is global state: its ghost state survives the crash, so
  the protocols and invariants of `Hstart` hold in every generation.

The file system's resources are its one shared view (`osShared`, `fs_crash_adequacy`'s resources,
`notes/fs-interp-state-determined.md`): they need no access to the extension's local interpretation,
so Perennial's distributed theorem gives them as it is.

The step and thread bounds: as `robust_of_distBootRB`, the adequacy theorem is used at the step
bound `n + 1` and thread bound `n + 2` of an execution of `n < bound` steps, so the WPs get
`receiptBound GF ≤ bound` (in `Hstart`, where the obligations are proved). Untrusted.
-/
module

public import Perennial.GooseLang.DistAdequacy
public import Perennial.Golang.Defn
public import GooseLang.Ext.NetFs.Adequacy
public import GooseLang.Ext.Net.Proto
public import Net.Statement.NetFsDeploy
public import Robustness.Statement

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

namespace Net

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Robustness NetFs

attribute [local instance] kvnetExts kvnetExtsSemantics kvnetExtsInterp kvnetExtsCrashInterp
  kvnetExts_hasNet kvnetExts_hasFs GooseGlobalGS.gooseInvGS

section bridge
variable [GoGlobalContext] {GF : BundledGFunctors} [hPre : GooseGpreS GF]

/-- The file extension's resources of a generation that starts from the file system `st` with
every file as on disk (a machine's first start), under the local ghost state `L`: the invariant of
the mapped cells, every file whole (each byte durable) and the tree's shared view (`osShared`), with
nothing logged. -/
def fsStartRes [G : GooseGlobalGS .hasLC GF] (L : GooseLocalGS GF) (st : Fs.OsState) : IProp GF :=
  iprop(Fs.osInv (L := L) ∗
    ([∗map] i ↦ f ∈ st.fs.files, Fs.osFileStart (L := L) i f) ∗
    Fs.osShared (L := L) st.fs.roots (st.fs.treeDur, []))

/-- The file extension's start resources of `[netExt, fsExt]` give `fsStartRes`
(`Fs.fs_start` for `[fsExt]`). -/
theorem fsStartRes_of_localStart [G : GooseGlobalGS .hasLC GF] (L : GooseLocalGS GF)
    (w : ExtsLocalState exts) (h : Fs.FsInit (extLocal Fs.fsExt w)) :
    ⊢ extsLocalStart (GF := GF) (L := L) w ={⊤}=∗ fsStartRes L (extLocal Fs.fsExt w) := by
  have hdisk : ∀ i f, (extLocal Fs.fsExt w).fs.files !! i = some f →
      ∃ img sz, f = Fs.OsFile.ofDisk img sz := fun i f hf =>
    let ⟨img, sz, _, e⟩ := (h.2.2.2.2.2.2.1 i f hf).2; ⟨img, sz, e⟩
  iintro Hs
  icases kvnet_fs_localStart (L := L) w $$ Hs with Hs
  unfold Fs.osStart Fs.osStartF Fs.treeStart Fs.bytesMap Fs.metaMap
  icases Hs with ⟨⟨Hb, Hm, Hv⟩, Hd⟩
  ihave Hfs := Fs.start_files (Fs.gooseOsGS (L := L)) hdisk $$ [Hb Hm]
  · iframe
  imod Fs.osInv_alloc (L := L) ⊤ $$ Hv with #Hinv
  imod Fs.osSwitchKit_open (L := L) _ _ ⊤ $$ Hd with Hsh
  imodintro
  unfold fsStartRes
  iframe Hinv Hsh
  iapply BigSepM.bigSepM_mono (fun {i f} _ =>
    (Fs.fileStart_eq (L := L) i f).1) $$ Hfs

/-- **A stable machine's boot program `e`, from the local state `σ`, is safe from `P`**: under every
local ghost state `L` whose Go context is `lctx` (the statement's, `Robust`'s `Fresh`), from `P`, its
files' start resources (`fsStartRes`), no package initialized and its main thread's token, it returns
`#()` (a Go `main`'s result) and is not stuck. (A proof substitutes `lctx` by `L`'s context, so that
the program's instances over `lctx`, `[go.Semantics]` and its packages' `Assumptions`, apply.) -/
def StableBootWp [lctx : GoLocalContext] [G : GooseGlobalGS .hasLC GF] (e : Expr) (σ : state)
    (P : IProp GF) : Prop :=
  ∀ L : GooseLocalGS GF, L.goose_go_local_context = lctx →
    letI : HeapGS .hasLC GF := ⟨G, L⟩
    P ⊢ fsStartRes L (extLocal Fs.fsExt σ.world) -∗ ownGoState (hG := L.goose_go_stateGS) ∅ -∗
      threadTok ={⊤}=∗ WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜v = #()⌝ }}

/-- **A crashing machine's boot program `e` is safe from `P`, in every generation**: under every
local ghost state `L` whose Go context is `lctx`, from `P L` and its main thread's token, it returns
`#()` and is not stuck, and after a crash of its machine `P` holds again of the next generation `L'`,
from `L`'s `crashed`, `L'`'s invariant of the mapped cells, the file system's crash rest (the
restart's files and tree, `Fs.crashRest`, for some new history `V'`), `L'`'s empty package state and a
later credit. -/
def CrashBootWp [lctx : GoLocalContext] [G : GooseGlobalGS .hasLC GF] (e : Expr)
    (P : GooseLocalGS GF → IProp GF) : Prop :=
  ∀ L : GooseLocalGS GF, L.goose_go_local_context = lctx →
    letI : HeapGS .hasLC GF := ⟨G, L⟩
    P L ⊢ threadTok ={⊤}=∗ WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜v = #()⌝ }} ∗
      ∀ (L' : GooseLocalGS GF) (V' : Fs.Hist), crashed (hC := L.goose_crashGS) -∗
        Fs.osInv (L := L') -∗
        Fs.crashRest (fun _ _ => True) (Fs.gooseOsGS (L := L)) (Fs.gooseOsGS (L := L')) [] false
          V' -∗
        ownGoState (hG := L'.goose_go_stateGS) ∅ -∗ £ 1 ={⊤}=∗ P L'

/-- The precondition, in `goose_dist_mixed_crash_adequacy`, of crashing machine `i` in the generation
`L`: some predicate `Q` for which its boot program is safe in every generation (`CrashBootWp`), and
`Q L`. (The adequacy theorem fixes the preconditions before the start obligation allocates the
protocols they name; `Q` is chosen there.) -/
def crashPre [lctx : GoLocalContext] [G : GooseGlobalGS .hasLC GF]
    (crashing : List (Expr × state)) (i : Nat) (L : GooseLocalGS GF) : IProp GF :=
  iprop(∃ Q : GooseLocalGS GF → IProp GF,
    ⌜∀ m : Expr × state, crashing[i]? = some m → CrashBootWp m.1 Q⌝ ∗ Q L)

/-- A stable machine's obligation in `goose_dist_mixed_crash_adequacy` (`nodeWp`), from
`StableBootWp`. -/
theorem nodeWp_of_stableBoot [lctx : GoLocalContext] [G : GooseGlobalGS .hasLC GF] (T : Nat)
    (e : Expr) (σ : state) (P : IProp GF) (hf : Fresh lctx σ)
    (hfs : Fs.FsInit (extLocal Fs.fsExt σ.world)) (H : StableBootWp e σ P) :
    P ⊢ nodeWp T e σ (fun v => v = #()) := by
  unfold nodeWp
  iintro HP %L
  unfold nodeWpBody
  rw [hf.2.1]
  iintro %_ %hL Hls Hgs Htok
  imod fsStartRes_of_localStart L σ.world hfs $$ Hls with Hr
  iapply H L (hL.trans hf.1) $$ HP Hr Hgs Htok

/-- A crashing machine's first start in `goose_dist_mixed_crash_adequacy` (`nodeStart`): from the
client's start of `Q` (every `L` of the statement's Go context, from the files' start resources and
the empty package state), with `Q` safe in every generation. -/
theorem nodeStart_of_crashBoot [lctx : GoLocalContext] [G : GooseGlobalGS .hasLC GF] (T : Nat)
    (crashing : List (Expr × state)) (i : Nat) (m : Expr × state) (hm : crashing[i]? = some m)
    (hf : Fresh lctx m.2) (hfs : Fs.FsInit (extLocal Fs.fsExt m.2.world))
    (Q : GooseLocalGS GF → IProp GF) (HQ : CrashBootWp m.1 Q) :
    (∀ L : GooseLocalGS GF, ⌜L.goose_go_local_context = lctx⌝ -∗
        fsStartRes L (extLocal Fs.fsExt m.2.world) -∗ ownGoState (hG := L.goose_go_stateGS) ∅
        ={⊤}=∗ Q L) ⊢
      nodeStart T m.2 (crashPre crashing i) := by
  unfold nodeStart
  rw [hf.2.1]
  iintro H %L %_ %hL Hls Hgs
  imod fsStartRes_of_localStart L m.2.world hfs $$ Hls with Hr
  imod H $$ %L %(hL.trans hf.1) Hr Hgs with HQL
  imodintro
  unfold crashPre
  iexists Q
  iframe HQL
  ipureintro
  intro m' hm'
  rw [hm] at hm'
  cases hm'
  exact HQ

/-- **The bridge** (see the file header): under the deployment `NetFsDeploy`, an update from the
network's start resources (every address of the deployment unset) to
- for each crashing machine `i`, a precondition `Pc i` of its generations, with its boot program
  safe in every generation (`CrashBootWp`) and its first generation's `Pc i L` from that
  generation's file start resources and empty package state, and
- for each stable machine `j`, a share `Ps j`, with its boot program safe from it (`StableBootWp`),

gives `Robust crashing stable g threads bound`, for any thread bound and step bound; the update is
given `receiptBound GF ≤ bound`. -/
theorem robust_of_netFsBoot [lctx : GoLocalContext] (addrs : List GoString)
    (crashing stable : List (Expr × state)) (g : GlobalState) (threads bound : Nat)
    (Hstart : ∀ [GooseGlobalGS .hasLC GF], receiptBound GF ≤ bound →
      ⊢ ([∗list] a ∈ addrs, addrUnset a) ={⊤}=∗
        ∃ (Pc : Nat → GooseLocalGS GF → IProp GF) (Ps : Nat → IProp GF),
          ⌜∀ (i : Nat) (m : Expr × state), crashing[i]? = some m → CrashBootWp m.1 (Pc i)⌝ ∗
          ⌜∀ (j : Nat) (m : Expr × state), stable[j]? = some m → StableBootWp m.1 m.2 (Ps j)⌝ ∗
          ([∗list] i ↦ m ∈ crashing, ∀ L : GooseLocalGS GF,
            ⌜L.goose_go_local_context = lctx⌝ -∗ fsStartRes L (extLocal Fs.fsExt m.2.world) -∗
            ownGoState (hG := L.goose_go_stateGS) ∅ ={⊤}=∗ Pc i L) ∗
          [∗list] j ↦ _m ∈ stable, Ps j) :
    NetFsDeploy addrs crashing stable g → Robust crashing stable g threads bound := by
  rintro ⟨⟨Hnd, Hok, Hconns, -⟩, Hfs⟩ hfresh _ _ n κs c hsteps hn i tp σ hi e he
  have hfc : ∀ (k : Nat) (m : Expr × state), crashing[k]? = some m → m ∈ crashing ++ stable :=
    fun _ m hm => List.mem_append_left _ (List.mem_of_getElem? hm)
  have hfst : ∀ (k : Nat) (m : Expr × state), stable[k]? = some m → m ∈ crashing ++ stable :=
    fun _ m hm => List.mem_append_right _ (List.mem_of_getElem? hm)
  have H := goose_dist_mixed_crash_adequacy (GF := GF) (n + 1) (n + 2) crashing stable g
    (fun _ v => v = #()) (fun _ p h => intoVal_ne_PanicV () p h.symm) ⟨Hconns, trivial, trivial⟩
    (fun m hm => ⟨trivial, Hfs m hm, trivial⟩) (fun i L => crashPre crashing i L) ?_ ?_
    n κs c hsteps.nsteps (Nat.lt_succ_self n) (fun m hm => (hfresh m hm).2.2)
    (DistCrashThreadsBelow.of_single (distInit_threads hfresh)) i tp σ hi
  · exact ⟨H.2.1 e he, H.2.2 e he⟩
  · -- the global setup, every crashing machine's first generation, every stable machine's WP
    intro G HN
    iintro Hg
    ihave Hnet := kvnet_net_globalStart g.globalWorld $$ Hg
    ihave Hs := addrs_start (Gg := G) (extGlobal netExt g.globalWorld) addrs Hnd Hok $$ Hnet
    imod Hstart (by omega) $$ Hs with ⟨%Pc, %Ps, %HPc, %HPs, Hc, Hst⟩
    imodintro
    isplitl [Hc]
    · iapply BigSepL.bigSepL_mono ?_ $$ Hc
      intro k m hm
      exact nodeStart_of_crashBoot (n + 2) crashing k m hm (hfresh m (hfc k m hm))
        (Hfs m (hfc k m hm)) (Pc k) (HPc k m hm)
    · iapply BigSepL.bigSepL_mono ?_ $$ Hst
      intro k m hm
      exact nodeWp_of_stableBoot (n + 2) m.1 m.2 (Ps k) (hfresh m (hfst k m hm))
        (Hfs m (hfst k m hm)) (HPs k m hm)
  · -- every generation of a crashing machine: its WP, and its next precondition
    intro hG _ _ k e' σ' Hes Hlctx
    obtain ⟨G, L⟩ := hG
    have hL : L.goose_go_local_context = lctx :=
      Hlctx.trans (hfresh (e', σ') (hfc k _ Hes)).1
    unfold crashPre
    iintro ⟨%Q, %HQ, HQL⟩ Htok
    imod HQ (e', σ') Hes L hL $$ HQL Htok with ⟨Hwp, Hcr⟩
    imodintro
    iframe Hwp
    iintro %L' Hcrd Hcs Hgs Hlc
    icases kvnet_fs_crashStart L L' $$ Hcs with Hcs
    unfold Fs.osCrashStart
    icases Hcs with ⟨Hv, %V', Hr⟩
    imod Fs.osInv_alloc (L := L') ⊤ $$ Hv with #Hinv
    imod Hcr $$ %L' %V' Hcrd Hinv Hr Hgs Hlc with HQL'
    imodintro
    iexists Q
    iframe HQL'
    ipureintro
    exact HQ

/-- **The bridge, from `Robust`'s own premises**: since the extensions state their initial states
(2026-11-22: the net extension's no listener and no connection, `net_semantics`; the file
extension's files as on disk, `fs_semantics`), `NetFsDeploy` follows from `Robust`'s premises and the
address facts alone: `robust_of_netFsBoot` with only the addresses distinct and valid. -/
theorem robust_of_netFsBoot_addrs [lctx : GoLocalContext] (addrs : List GoString)
    (crashing stable : List (Expr × state)) (g : GlobalState) (threads bound : Nat)
    (Hnd : addrs.Nodup) (Hok : ∀ a ∈ addrs, addrOk a = true)
    (Hstart : ∀ [GooseGlobalGS .hasLC GF], receiptBound GF ≤ bound →
      ⊢ ([∗list] a ∈ addrs, addrUnset a) ={⊤}=∗
        ∃ (Pc : Nat → GooseLocalGS GF → IProp GF) (Ps : Nat → IProp GF),
          ⌜∀ (i : Nat) (m : Expr × state), crashing[i]? = some m → CrashBootWp m.1 (Pc i)⌝ ∗
          ⌜∀ (j : Nat) (m : Expr × state), stable[j]? = some m → StableBootWp m.1 m.2 (Ps j)⌝ ∗
          ([∗list] i ↦ m ∈ crashing, ∀ L : GooseLocalGS GF,
            ⌜L.goose_go_local_context = lctx⌝ -∗ fsStartRes L (extLocal Fs.fsExt m.2.world) -∗
            ownGoState (hG := L.goose_go_stateGS) ∅ ={⊤}=∗ Pc i L) ∗
          [∗list] j ↦ _m ∈ stable, Ps j) :
    Robust crashing stable g threads bound := by
  intro hfresh hig hil
  exact robust_of_netFsBoot (GF := GF) addrs crashing stable g threads bound Hstart
    ⟨⟨Hnd, Hok, hig.1, fun m hm => (hil m hm).1⟩, fun m hm => (hil m hm).2.1⟩ hfresh hig hil

end bridge

end Net
end Perennial

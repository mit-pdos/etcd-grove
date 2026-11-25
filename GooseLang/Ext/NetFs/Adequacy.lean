/-
The closed list of extensions of a networked program with Linux files: the net extension and the
Linux file extension, `[Net.netExt, Fs.fsExt]` (`kvraftExts`), with its semantics, ghost state,
crash interpretation, the `HasExt` instances of both, ghost state `kvraftGF` for it, and the
projections of its start and crash resources onto each extension's; what kvraft's top-level theorem
(`notes/kvraft-robust-goal.md`) fixes as its extensions, and what its distributed crash adequacy
(`kvraft_dist_crash_adequacy`, Perennial's `goose_dist_crash_adequacy` at `kvraftGF`) is about.

Each extension's semantics, interpretation and crash interpretation are its own (`Net.net_semantics`,
`Net.net_interp`, `Net.net_crash_interp`; `Fs.fs_semantics`, `Fs.fs_interp`, `Fs.fs_crash_interp`):
Perennial's `ExtTuple` composes them, an extension's specs see only their own part (`HasExt`), so a
proof over `kvraftExts` uses both extensions' specs unchanged. The initial states: the network has no
connection and no machine a listener (`Net.NetGlobal.init`, `Net.NetLocal.init`: the net semantics'
`initGlobal`/`initLocal`), and every machine's files are as on disk (`Fs.FsInit`, the file semantics'
`initLocal`); the interpretations accept them (`kvraftInitCompat`).
-/
module

public import GooseLang.Ext.Net.Adequacy
public import GooseLang.Ext.Fs.Adequacy
public import Perennial.GooseLang.InitAdequacy
public import Iris.Instances.Lib.NaInvariants

@[expose] public section

noncomputable section

namespace Perennial
namespace NetFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

/-- The extensions of a networked program with Linux files: the net extension, then the Linux file
extension. -/
@[reducible] def kvraftExts : GooseExts := ⟨[Net.netExt, Fs.fsExt]⟩

attribute [local instance] kvraftExts

@[reducible] def kvraftExtsSemantics : GooseSemantics := ⟨(Net.net_semantics, (Fs.fs_semantics, ⟨⟩))⟩

@[reducible] def kvraftExtsInterp : GooseInterp := ⟨(Net.net_interp, (Fs.fs_interp, ⟨⟩))⟩

attribute [local instance] kvraftExtsSemantics kvraftExtsInterp

@[reducible] def kvraftExtsCrashInterp : GooseCrashInterp :=
  ⟨(Net.net_crash_interp, (Fs.fs_crash_interp, ⟨⟩))⟩

attribute [local instance] kvraftExtsCrashInterp

set_option linter.defProp false in
@[reducible] def kvraftExts_hasNet : HasExt Net.netExt where
  registered := rfl
  sem_eq := rfl
  interp_eq := rfl

set_option linter.defProp false in
@[reducible] def kvraftExts_hasFs : HasExt Fs.fsExt where
  registered := rfl
  sem_eq := rfl
  interp_eq := rfl

attribute [local instance] kvraftExts_hasNet kvraftExts_hasFs

/-- The interpretations of `[netExt, fsExt]` accept every initial state of the semantics
(`Net.net_init_compat`, `Fs.fs_init_compat`): Perennial's `*_adequacy_init` theorems apply. -/
theorem kvraftInitCompat : GooseInitCompat := ⟨Net.net_init_compat, Fs.fs_init_compat, trivial⟩

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- Ghost state for a networked program with Linux files: one slot for each camera `GooseGpreS`
needs for `[netExt, fsExt]` (both extensions need only the universal camera, `AllG`, at slot 0), and
iris-lean's camera of non-atomic invariants at slot 8 (`NaInvG`: lintest's linked results, which kvraft's
checking client runs, take it). -/
noncomputable def kvraftGF : BundledGFunctors := fun
  | 0 => ⟨AllURF, inferInstance⟩
  | 1 => ⟨InvMapF, inferInstance⟩
  | 2 => ⟨constOF CoPsetDisjL, inferInstance⟩
  | 3 => ⟨constOF (DisjointLeibnizSet PosSet), inferInstance⟩
  | 4 => ⟨Auth.AuthURF (constOF Credit), inferInstance⟩
  | 5 => ⟨constOF (NaHeapUR Loc val), inferInstance⟩
  | 6 => ⟨constOF (HeapView proph_id (Agree (DiscreteO (List val))) (GMap proph_id)), inferInstance⟩
  | 7 => ⟨GhostVarF (GMap GoString Bool), inferInstance⟩
  | 8 => ⟨NaInvF, inferInstance⟩
  | _ => ⟨constOF Unit, inferInstance⟩

/-- iris-lean's camera of non-atomic invariants, at slot 8. -/
instance kvraftGF_naInvG : NaInvG kvraftGF := ⟨⟨8, rfl⟩⟩

noncomputable instance kvraftGpreS : GooseGpreS kvraftGF where
  goose_preG_iris := ⟨⟨⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩⟩, ⟨⟨4, rfl⟩⟩⟩
  goose_preG_heap := ⟨⟨5, rfl⟩⟩
  goose_preG_proph := ⟨⟨⟨6, rfl⟩⟩⟩
  goosePreGExts := (⟨allGOfSlot 0 rfl⟩, (⟨allGOfSlot 0 rfl⟩, PUnit.unit))
  goose_preG_go_state := ⟨@GhostVarG.mk _ _ ⟨7, rfl⟩⟩
  goosePreGAllG := allGOfSlot 0 rfl

section start
variable [GoGlobalContext] {GF : BundledGFunctors}

/-- The global start resources of `[netExt, fsExt]`: the network's (every valid address's
pending set and listening token). -/
theorem kvraft_net_globalStart [G : GooseGlobalGS .hasLC GF] (g : ExtsGlobalState exts) :
    extsGlobalStart (GF := GF) g ⊢
      Net.netStart (extGlobalGS Net.netExt) (extGlobal Net.netExt g) :=
  sep_elim_left

/-- The local start resources of `[netExt, fsExt]` for a node: its listeners. -/
theorem kvraft_net_localStart [L : GooseLocalGS GF] (σ : ExtsLocalState exts) :
    extsLocalStart (GF := GF) σ ⊢
      Net.lisStart (extLocalGS Net.netExt (L := L)) (extLocal Net.netExt σ) :=
  sep_elim_left

/-- The local start resources of `[netExt, fsExt]` for a node: its files and tree. -/
theorem kvraft_fs_localStart [L : GooseLocalGS GF] (σ : ExtsLocalState exts) :
    extsLocalStart (GF := GF) σ ⊢
      Fs.osStart (extLocalGS Fs.fsExt (L := L)) (extLocal Fs.fsExt σ) :=
  sep_elim_right.trans sep_elim_left

/-- The crash resources of `[netExt, fsExt]`: the file extension's (the net extension's are
`emp`). -/
theorem kvraft_fs_crashStart (L L' : GooseLocalGS GF) :
    extsCrashStart (GF := GF) L L' ⊢
      Fs.osCrashStart (fun _ _ => True) (extLocalGS Fs.fsExt (L := L))
        (extLocalGS Fs.fsExt (L := L')) :=
  sep_elim_right.trans sep_elim_left

end start

section adequacy
variable [GoGlobalContext]

/-- **Distributed crash adequacy for `[netExt, fsExt]`**: Perennial's `goose_dist_crash_adequacy`
at the ghost state `kvraftGF`, its initial-state conditions discharged from the network's having no
connection and every node's files being as on disk. -/
theorem kvraft_dist_crash_adequacy (N T : Nat)
    (es : List (Expr × state)) (g : GlobalState) (φ : Nat → val → Prop)
    (hφ : ∀ i p, ¬ φ i (PanicV p))
    (Hconns : (extGlobal Net.netExt g.globalWorld).init)
    (Hfs : ∀ n, n ∈ es → Fs.FsInit (extLocal Fs.fsExt n.2.world))
    (P : ∀ [GooseGlobalGS .hasLC kvraftGF], Nat → GooseLocalGS kvraftGF → IProp kvraftGF)
    (Hstart : ∀ [GooseGlobalGS .hasLC kvraftGF],
      receiptBound kvraftGF = N →
      ⊢ extsGlobalStart (GF := kvraftGF) g.globalWorld ={⊤}=∗
        [∗list] i ↦ n ∈ es, nodeStart T n.2 (P i))
    (Hwp : ∀ [hG : HeapGS .hasLC kvraftGF],
      receiptBound kvraftGF = N →
      threadBound kvraftGF = T →
      ∀ (i : Nat) (e : Expr) (σ : state), es[i]? = some (e, σ) →
      hG.goose_localGS.goose_go_local_context = σ.goState.goLctx →
      ⊢ P i hG.goose_localGS -∗ threadTok ={⊤}=∗
        WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ i v⌝ }} ∗
        ∀ L' : GooseLocalGS kvraftGF, crashed (hC := hG.goose_localGS.goose_crashGS) -∗
          extsCrashStart hG.goose_localGS L' -∗
          ownGoState (hG := L'.goose_go_stateGS) ∅ ={⊤}=∗ P i L')
    (n : Nat) (κs : List Observation) (c : DistCfg)
    (Hsteps : DistCrashNsteps (es.map Prod.fst) n (distInit es g) κs c)
    (Hbound : n < N) (Hthreads : ∀ n, n ∈ es → n.2.threads = 1)
    (Hlive : DistCrashThreadsBelow (es.map Prod.fst) T n (distInit es g)) :
    ∀ i tp σ, c.nodes[i]? = some (tp, σ) →
      (∀ v tp', tp = Val v :: tp' → φ i v) ∧
      (∀ e, e ∈ tp → RealNotStuck e (σ, c.global)) ∧
      (∀ e, e ∈ tp → ¬ UnrecoveredPanic e) :=
  goose_dist_crash_adequacy (GF := kvraftGF) N T es g φ hφ ⟨Hconns, trivial, trivial⟩
    (fun m hm => ⟨trivial, Hfs m hm, trivial⟩) P Hstart
    (by
      -- the crash obligation's later credit is not needed
      intro hG HN HT i e σ Hes Hlctx
      iintro HP Htok
      imod Hwp HN HT i e σ Hes Hlctx $$ HP Htok with ⟨Hwp, Hcrash⟩
      imodintro
      iframe Hwp
      iintro %L' Hcr Hcs Hgs _
      iapply Hcrash $$ %L' Hcr Hcs Hgs)
    n κs c Hsteps Hbound Hthreads Hlive

end adequacy

end NetFs
end Perennial

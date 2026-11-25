/-
The closed list of extensions of a networked program with Linux files and UDP: the net extension,
the Linux file extension and the UDP extension, `[Net.netExt, Fs.fsExt, Udp.udpExt]` (`kvraftUdpExts`),
with its semantics, ghost state, crash interpretation, the `HasExt` instances of the three, ghost state
`kvraftUdpGF` for it, and the projections of its start resources onto each extension's: what kvraft-udp's
top-level theorem (`KvRaft/Spec/.../kvraft/cmd/kvraft_udp/TopLevelRobustness.lean`) fixes as its extensions.
As `GooseLang/Ext/NetFs/Adequacy.lean` (kvraft's `[netExt, fsExt]`), with the UDP extension last: each
extension's semantics, interpretation and crash interpretation are its own (`Udp.udp_semantics`,
`Udp.udp_interp`, `Udp.udp_crash_interp`), Perennial's `ExtTuple` composes them, and an extension's
specs see only their own part (`HasExt`). The UDP extension's initial state: no datagram sent
(`Udp.UdpGlobal.init`), and its interpretation accepts it (`Udp.udp_init_compat`).
-/
module

public import GooseLang.Ext.NetFs.Adequacy
public import GooseLang.Ext.Udp.Adequacy

@[expose] public section

noncomputable section

namespace Perennial
namespace NetFsUdp

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

/-- The extensions of a networked program with Linux files and UDP. -/
@[reducible] def kvraftUdpExts : GooseExts := ⟨[Net.netExt, Fs.fsExt, Udp.udpExt]⟩

attribute [local instance] kvraftUdpExts

@[reducible] def kvraftUdpExtsSemantics : GooseSemantics :=
  ⟨(Net.net_semantics, (Fs.fs_semantics, (Udp.udp_semantics, ⟨⟩)))⟩

@[reducible] def kvraftUdpExtsInterp : GooseInterp :=
  ⟨(Net.net_interp, (Fs.fs_interp, (Udp.udp_interp, ⟨⟩)))⟩

attribute [local instance] kvraftUdpExtsSemantics kvraftUdpExtsInterp

@[reducible] def kvraftUdpExtsCrashInterp : GooseCrashInterp :=
  ⟨(Net.net_crash_interp, (Fs.fs_crash_interp, (Udp.udp_crash_interp, ⟨⟩)))⟩

attribute [local instance] kvraftUdpExtsCrashInterp

set_option linter.defProp false in
@[reducible] def kvraftUdpExts_hasNet : HasExt Net.netExt where
  registered := rfl
  sem_eq := rfl
  interp_eq := rfl

set_option linter.defProp false in
@[reducible] def kvraftUdpExts_hasFs : HasExt Fs.fsExt where
  registered := rfl
  sem_eq := rfl
  interp_eq := rfl

set_option linter.defProp false in
@[reducible] def kvraftUdpExts_hasUdp : HasExt Udp.udpExt where
  registered := rfl
  sem_eq := rfl
  interp_eq := rfl

attribute [local instance] kvraftUdpExts_hasNet kvraftUdpExts_hasFs kvraftUdpExts_hasUdp

/-- The interpretations of `[netExt, fsExt, udpExt]` accept every initial state of the semantics. -/
theorem kvraftUdpInitCompat : GooseInitCompat :=
  ⟨Net.net_init_compat, Fs.fs_init_compat, Udp.udp_init_compat, trivial⟩

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- Ghost state for kvraft-udp: `NetFs.kvraftGF`'s slots (the three extensions need only the universal
camera, `AllG`, at slot 0). -/
noncomputable def kvraftUdpGF : BundledGFunctors := fun
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
instance kvraftUdpGF_naInvG : NaInvG kvraftUdpGF := ⟨⟨8, rfl⟩⟩

noncomputable instance kvraftUdpGpreS : GooseGpreS kvraftUdpGF where
  goose_preG_iris := ⟨⟨⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩⟩, ⟨⟨4, rfl⟩⟩⟩
  goose_preG_heap := ⟨⟨5, rfl⟩⟩
  goose_preG_proph := ⟨⟨⟨6, rfl⟩⟩⟩
  goosePreGExts := (⟨allGOfSlot 0 rfl⟩, (⟨allGOfSlot 0 rfl⟩, (⟨allGOfSlot 0 rfl⟩, PUnit.unit)))
  goose_preG_go_state := ⟨@GhostVarG.mk _ _ ⟨7, rfl⟩⟩
  goosePreGAllG := allGOfSlot 0 rfl

section start
variable [GoGlobalContext] {GF : BundledGFunctors}

/-- The global start resources of `[netExt, fsExt, udpExt]`: the network's. -/
theorem kvraft_udp_net_globalStart [G : GooseGlobalGS .hasLC GF] (g : ExtsGlobalState exts) :
    extsGlobalStart (GF := GF) g ⊢
      Net.netStart (extGlobalGS Net.netExt) (extGlobal Net.netExt g) :=
  sep_elim_left

/-- The global start resources of `[netExt, fsExt, udpExt]`: every valid address's datagrams. -/
theorem kvraft_udp_udp_globalStart [G : GooseGlobalGS .hasLC GF] (g : ExtsGlobalState exts) :
    extsGlobalStart (GF := GF) g ⊢
      Udp.udpStart (extGlobalGS Udp.udpExt) (extGlobal Udp.udpExt g) :=
  sep_elim_right.trans (sep_elim_right.trans sep_elim_left)

/-- The global start resources of `[netExt, fsExt, udpExt]`: the network's and every valid address's
datagrams, together. -/
theorem kvraft_udp_netUdp_globalStart [G : GooseGlobalGS .hasLC GF] (g : ExtsGlobalState exts) :
    extsGlobalStart (GF := GF) g ⊢
      Net.netStart (extGlobalGS Net.netExt) (extGlobal Net.netExt g) ∗
        Udp.udpStart (extGlobalGS Udp.udpExt) (extGlobal Udp.udpExt g) :=
  sep_mono_right (sep_elim_right.trans sep_elim_left)

/-- The local start resources of `[netExt, fsExt, udpExt]` for a node: its listeners. -/
theorem kvraft_udp_net_localStart [L : GooseLocalGS GF] (σ : ExtsLocalState exts) :
    extsLocalStart (GF := GF) σ ⊢
      Net.lisStart (extLocalGS Net.netExt (L := L)) (extLocal Net.netExt σ) :=
  sep_elim_left

/-- The local start resources of `[netExt, fsExt, udpExt]` for a node: its files and tree. -/
theorem kvraft_udp_fs_localStart [L : GooseLocalGS GF] (σ : ExtsLocalState exts) :
    extsLocalStart (GF := GF) σ ⊢
      Fs.osStart (extLocalGS Fs.fsExt (L := L)) (extLocal Fs.fsExt σ) :=
  sep_elim_right.trans sep_elim_left

/-- The crash resources of `[netExt, fsExt, udpExt]`: the file extension's. -/
theorem kvraft_udp_fs_crashStart (L L' : GooseLocalGS GF) :
    extsCrashStart (GF := GF) L L' ⊢
      Fs.osCrashStart (fun _ _ => True) (extLocalGS Fs.fsExt (L := L))
        (extLocalGS Fs.fsExt (L := L')) :=
  sep_elim_right.trans sep_elim_left

end start

section adequacy
variable [GoGlobalContext]

/-- **Distributed crash adequacy for `[netExt, fsExt, udpExt]`**: Perennial's
`goose_dist_crash_adequacy` at `kvraftUdpGF`, as `NetFs.kvraft_dist_crash_adequacy`, its initial-state
conditions discharged from the network's having no connection, no datagram sent, and every node's
files being as on disk (a node's sockets need nothing: the UDP extension's `initP` is `True`). -/
theorem kvraft_udp_dist_crash_adequacy (N T : Nat)
    (es : List (Expr × state)) (g : GlobalState) (φ : Nat → val → Prop)
    (hφ : ∀ i p, ¬ φ i (PanicV p))
    (Hconns : (extGlobal Net.netExt g.globalWorld).init)
    (Hudp : (extGlobal Udp.udpExt g.globalWorld).init)
    (Hfs : ∀ n, n ∈ es → Fs.FsInit (extLocal Fs.fsExt n.2.world))
    (P : ∀ [GooseGlobalGS .hasLC kvraftUdpGF], Nat → GooseLocalGS kvraftUdpGF → IProp kvraftUdpGF)
    (Hstart : ∀ [GooseGlobalGS .hasLC kvraftUdpGF],
      receiptBound kvraftUdpGF = N →
      ⊢ extsGlobalStart (GF := kvraftUdpGF) g.globalWorld ={⊤}=∗
        [∗list] i ↦ n ∈ es, nodeStart T n.2 (P i))
    (Hwp : ∀ [hG : HeapGS .hasLC kvraftUdpGF],
      receiptBound kvraftUdpGF = N →
      threadBound kvraftUdpGF = T →
      ∀ (i : Nat) (e : Expr) (σ : state), es[i]? = some (e, σ) →
      hG.goose_localGS.goose_go_local_context = σ.goState.goLctx →
      ⊢ P i hG.goose_localGS -∗ threadTok ={⊤}=∗
        WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ i v⌝ }} ∗
        ∀ L' : GooseLocalGS kvraftUdpGF, crashed (hC := hG.goose_localGS.goose_crashGS) -∗
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
  goose_dist_crash_adequacy (GF := kvraftUdpGF) N T es g φ hφ ⟨Hconns, trivial, Hudp, trivial⟩
    (fun m hm => ⟨trivial, Hfs m hm, trivial, trivial⟩) P Hstart
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

end NetFsUdp
end Perennial

/-
The closed list of extensions of a networked program with Linux files and UDP: the net extension,
the Linux file extension and the UDP extension, `[Net.netExt, Fs.fsExt, Udp.udpExt]` (`kvudpExts`),
with its semantics, ghost state, crash interpretation, the `HasExt` instances of the three, ghost state
`kvudpGF` for it, and the projections of its start resources onto each extension's: what kvudp's
top-level theorem (`KvNet/Spec/.../kvnet/cmd/kvudp/TopLevelRobustness.lean`) fixes as its extensions.
As `GooseLang/Ext/NetFs/Adequacy.lean` (kvnet's `[netExt, fsExt]`), with the UDP extension last: each
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
@[reducible] def kvudpExts : GooseExts := ⟨[Net.netExt, Fs.fsExt, Udp.udpExt]⟩

attribute [local instance] kvudpExts

@[reducible] def kvudpExtsSemantics : GooseSemantics :=
  ⟨(Net.net_semantics, (Fs.fs_semantics, (Udp.udp_semantics, ⟨⟩)))⟩

@[reducible] def kvudpExtsInterp : GooseInterp :=
  ⟨(Net.net_interp, (Fs.fs_interp, (Udp.udp_interp, ⟨⟩)))⟩

attribute [local instance] kvudpExtsSemantics kvudpExtsInterp

@[reducible] def kvudpExtsCrashInterp : GooseCrashInterp :=
  ⟨(Net.net_crash_interp, (Fs.fs_crash_interp, (Udp.udp_crash_interp, ⟨⟩)))⟩

attribute [local instance] kvudpExtsCrashInterp

set_option linter.defProp false in
@[reducible] def kvudpExts_hasNet : HasExt Net.netExt where
  registered := rfl
  sem_eq := rfl
  interp_eq := rfl

set_option linter.defProp false in
@[reducible] def kvudpExts_hasFs : HasExt Fs.fsExt where
  registered := rfl
  sem_eq := rfl
  interp_eq := rfl

set_option linter.defProp false in
@[reducible] def kvudpExts_hasUdp : HasExt Udp.udpExt where
  registered := rfl
  sem_eq := rfl
  interp_eq := rfl

attribute [local instance] kvudpExts_hasNet kvudpExts_hasFs kvudpExts_hasUdp

/-- The interpretations of `[netExt, fsExt, udpExt]` accept every initial state of the semantics. -/
theorem kvudpInitCompat : GooseInitCompat :=
  ⟨Net.net_init_compat, Fs.fs_init_compat, Udp.udp_init_compat, trivial⟩

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- Ghost state for kvudp: `NetFs.kvnetGF`'s slots (the three extensions need only the universal
camera, `AllG`, at slot 0). -/
noncomputable def kvudpGF : BundledGFunctors := NetFs.kvnetGF

/-- iris-lean's camera of non-atomic invariants, at slot 8. -/
instance kvudpGF_naInvG : NaInvG kvudpGF := ⟨⟨8, rfl⟩⟩

noncomputable instance kvudpGpreS : GooseGpreS kvudpGF where
  goose_preG_iris := ⟨⟨⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩⟩, ⟨⟨4, rfl⟩⟩⟩
  goose_preG_heap := ⟨⟨5, rfl⟩⟩
  goose_preG_proph := ⟨⟨⟨6, rfl⟩⟩⟩
  goosePreGExts := (⟨allGOfSlot 0 rfl⟩, (⟨allGOfSlot 0 rfl⟩, (⟨allGOfSlot 0 rfl⟩, PUnit.unit)))
  goose_preG_go_state := ⟨@GhostVarG.mk _ _ ⟨7, rfl⟩⟩
  goosePreGAllG := allGOfSlot 0 rfl

section start
variable [GoGlobalContext] {GF : BundledGFunctors}

/-- The global start resources of `[netExt, fsExt, udpExt]`: the network's. -/
theorem kvudp_net_globalStart [G : GooseGlobalGS .hasLC GF] (g : ExtsGlobalState exts) :
    extsGlobalStart (GF := GF) g ⊢
      Net.netStart (extGlobalGS Net.netExt) (extGlobal Net.netExt g) :=
  sep_elim_left

/-- The global start resources of `[netExt, fsExt, udpExt]`: every valid address's datagrams. -/
theorem kvudp_udp_globalStart [G : GooseGlobalGS .hasLC GF] (g : ExtsGlobalState exts) :
    extsGlobalStart (GF := GF) g ⊢
      Udp.udpStart (extGlobalGS Udp.udpExt) (extGlobal Udp.udpExt g) :=
  sep_elim_right.trans (sep_elim_right.trans sep_elim_left)

/-- The local start resources of `[netExt, fsExt, udpExt]` for a node: its listeners. -/
theorem kvudp_net_localStart [L : GooseLocalGS GF] (σ : ExtsLocalState exts) :
    extsLocalStart (GF := GF) σ ⊢
      Net.lisStart (extLocalGS Net.netExt (L := L)) (extLocal Net.netExt σ) :=
  sep_elim_left

/-- The local start resources of `[netExt, fsExt, udpExt]` for a node: its files and tree. -/
theorem kvudp_fs_localStart [L : GooseLocalGS GF] (σ : ExtsLocalState exts) :
    extsLocalStart (GF := GF) σ ⊢
      Fs.osStart (extLocalGS Fs.fsExt (L := L)) (extLocal Fs.fsExt σ) :=
  sep_elim_right.trans sep_elim_left

/-- The crash resources of `[netExt, fsExt, udpExt]`: the file extension's. -/
theorem kvudp_fs_crashStart (L L' : GooseLocalGS GF) :
    extsCrashStart (GF := GF) L L' ⊢
      Fs.osCrashStart (fun _ _ => True) (extLocalGS Fs.fsExt (L := L))
        (extLocalGS Fs.fsExt (L := L')) :=
  sep_elim_right.trans sep_elim_left

end start

section adequacy
variable [GoGlobalContext]

/-- **Distributed crash adequacy for `[netExt, fsExt, udpExt]`**: Perennial's
`goose_dist_crash_adequacy` at `kvudpGF`, as `NetFs.kvnet_dist_crash_adequacy`, its initial-state
conditions discharged from the network's having no connection, no datagram sent, and every node's
files being as on disk. (Phase 2: the instantiation, `kvnet_dist_crash_adequacy`'s with the UDP
extension's conditions.) -/
theorem kvudp_dist_crash_adequacy (N T : Nat)
    (es : List (Expr × state)) (g : GlobalState) (φ : Nat → val → Prop)
    (hφ : ∀ i p, ¬ φ i (PanicV p))
    (Hconns : (extGlobal Net.netExt g.globalWorld).init)
    (Hudp : (extGlobal Udp.udpExt g.globalWorld).init)
    (Hfs : ∀ n, n ∈ es → Fs.FsInit (extLocal Fs.fsExt n.2.world))
    (P : ∀ [GooseGlobalGS .hasLC kvudpGF], Nat → GooseLocalGS kvudpGF → IProp kvudpGF)
    (Hstart : ∀ [GooseGlobalGS .hasLC kvudpGF],
      receiptBound kvudpGF = N →
      ⊢ extsGlobalStart (GF := kvudpGF) g.globalWorld ={⊤}=∗
        [∗list] i ↦ n ∈ es, nodeStart T n.2 (P i))
    (Hwp : ∀ [hG : HeapGS .hasLC kvudpGF],
      receiptBound kvudpGF = N →
      threadBound kvudpGF = T →
      ∀ (i : Nat) (e : Expr) (σ : state), es[i]? = some (e, σ) →
      hG.goose_localGS.goose_go_local_context = σ.goState.goLctx →
      ⊢ P i hG.goose_localGS -∗ threadTok ={⊤}=∗
        WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ i v⌝ }} ∗
        ∀ L' : GooseLocalGS kvudpGF, crashed (hC := hG.goose_localGS.goose_crashGS) -∗
          extsCrashStart hG.goose_localGS L' -∗
          ownGoState (hG := L'.goose_go_stateGS) ∅ ={⊤}=∗ P i L')
    (n : Nat) (κs : List Observation) (c : DistCfg)
    (Hsteps : DistCrashNsteps (es.map Prod.fst) n (distInit es g) κs c)
    (Hbound : n < N) (Hthreads : ∀ n, n ∈ es → n.2.threads = 1)
    (Hlive : DistCrashThreadsBelow (es.map Prod.fst) T n (distInit es g)) :
    ∀ i tp σ, c.nodes[i]? = some (tp, σ) →
      (∀ v tp', tp = Val v :: tp' → φ i v) ∧
      (∀ e, e ∈ tp → RealNotStuck e (σ, c.global)) ∧
      (∀ e, e ∈ tp → ¬ UnrecoveredPanic e) := by
  sorry

end adequacy

end NetFsUdp
end Perennial

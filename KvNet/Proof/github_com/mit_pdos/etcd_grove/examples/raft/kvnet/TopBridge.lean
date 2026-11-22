/-
# kvnet's top level: the bridge it needs, in the shape of Perennial's proposed change (2026-11-22)

`Net.robust_of_netFsBoot_addrs` (`Net/Statement/NetFsBridge.lean`) over Perennial's
`goose_dist_mixed_crash_adequacy` gives a crashing machine's generation only `P i L -∗ threadTok ={⊤}=∗
WP ∗ crashFrame`: no access to the extensions' local interpretation before the WP, and no later
credit in the crash obligation (`notes/kvnet-part.md`, the blocker; `notes/perennial-changes.md`,
"Extension state access at generation start, distributed"). The change is being made in Perennial
(branch `crash-genstart`, not landed): (1) each generation's obligation gets the node's extensions'
local interpretation before its WP; (2) the crash obligation gets `£ 1`.

This file states, as a `Prop` (no proof: it is a hypothesis of `raft_kvnet_robust_of_errors` until the
change lands, then the bridge's own theorem), what `robust_of_netFsBoot_addrs` becomes on top of it:

* `CrashBootWpG e P`: a crashing machine's generation, from `P L` and its main thread's token, gets
  the file extension's local interpretation (`fs_interp.localCtx … σ`, the Linux file extension's
  component of the generation's `extsLocalCtx`, through `HasExt.localCtx_acc`), and gives it back
  with its WP and its crash obligation, which gets one later credit;
* `RobustOfNetFsBootG`: `robust_of_netFsBoot_addrs` with `CrashBootWpG` in place of `CrashBootWp`.

Only the shapes are guessed (the exact ones come with the Perennial PR); kvnet's proofs use
`TopBoot.lean`'s `kvGen_boot` (at the interpretation) and `kvGen_crash` (with the credit), so moving to
the exact shapes is mechanical.
-/
module

public import Net.Statement.NetFsBridge

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI Iris.ProgramLogic Iris.Std Robustness NetFs Net

attribute [local instance] kvnetExts kvnetExtsSemantics kvnetExtsInterp kvnetExtsCrashInterp
  kvnetExts_hasNet kvnetExts_hasFs GooseGlobalGS.gooseInvGS

section bridge
variable [GoGlobalContext] {GF : BundledGFunctors} [hPre : GooseGpreS GF]

/-- **A crashing machine's boot program `e` is safe from `P`, in every generation, booting at the
file extension's interpretation** (see the file header): `Net.CrashBootWp`, where the generation's
obligation also gets the file extension's local interpretation (kept) before its WP, and the crash
obligation one later credit. -/
def CrashBootWpG [lctx : GoLocalContext] [G : GooseGlobalGS .hasLC GF] (e : Expr)
    (P : GooseLocalGS GF → IProp GF) : Prop :=
  ∀ L : GooseLocalGS GF, L.goose_go_local_context = lctx →
    letI : HeapGS .hasLC GF := ⟨G, L⟩
    P L ⊢ threadTok ={⊤}=∗ ∀ σ : Fs.OsState,
      Fs.fs_interp.localCtx (extLocalGS Fs.fsExt) σ ={⊤}=∗
      Fs.fs_interp.localCtx (extLocalGS Fs.fsExt) σ ∗
      (WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜v = #()⌝ }} ∗
        ∀ (L' : GooseLocalGS GF) (V' : Fs.Hist), £ 1 -∗ crashed (hC := L.goose_crashGS) -∗
          Fs.osInv (L := L') -∗
          Fs.crashRest (fun _ _ => True) (Fs.gooseOsGS (L := L)) (Fs.gooseOsGS (L := L')) [] false
            V' -∗
          ownGoState (hG := L'.goose_go_stateGS) ∅ ={⊤}=∗ P L')

end bridge

/-- **The bridge on top of Perennial's proposed change** (see the file header):
`Net.robust_of_netFsBoot_addrs` with `CrashBootWpG` for the crashing machines. -/
def RobustOfNetFsBootG : Prop :=
  ∀ [GoGlobalContext] (GF : BundledGFunctors) [GooseGpreS GF] [lctx : GoLocalContext]
    (addrs : List GoString) (crashing stable : List (Expr × state)) (g : GlobalState)
    (threads bound : Nat),
    addrs.Nodup → (∀ a ∈ addrs, addrOk a = true) →
    (∀ [GooseGlobalGS .hasLC GF], receiptBound GF ≤ bound →
      ⊢ ([∗list] a ∈ addrs, addrUnset a) ={⊤}=∗
        ∃ (Pc : Nat → GooseLocalGS GF → IProp GF) (Ps : Nat → IProp GF),
          ⌜∀ (i : Nat) (m : Expr × state), crashing[i]? = some m → CrashBootWpG m.1 (Pc i)⌝ ∗
          ⌜∀ (j : Nat) (m : Expr × state), stable[j]? = some m → StableBootWp m.1 m.2 (Ps j)⌝ ∗
          ([∗list] i ↦ m ∈ crashing, ∀ L : GooseLocalGS GF,
            ⌜L.goose_go_local_context = lctx⌝ -∗ fsStartRes L (extLocal Fs.fsExt m.2.world) -∗
            ownGoState (hG := L.goose_go_stateGS) ∅ ={⊤}=∗ Pc i L) ∗
          [∗list] j ↦ _m ∈ stable, Ps j) →
    Robust crashing stable g threads bound

end raft_kvnet
end EtcdGrove
end Perennial

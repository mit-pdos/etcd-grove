/-
**The deployment of machines over the network and Linux files** [Trusted definition!]: the premise of
a robustness statement whose machines run over `[netExt, fsExt]`, some of which crash and restart
(etcd-dist stage D3, `Net/Statement/NetFsBridge.lean`):

    NetFsDeploy addrs crashing stable g → Robust crashing stable g threads bound

It is the distributed deployment's start (`DistDeploy`, `DistDeploy.lean`) of all the machines, crashing and stable:
the addresses `addrs` are distinct and valid, the network has no connection, and no machine has a
listener; and, on every machine, its files are as on disk (`Fs.FsInit`, the Linux file extension's
initial state, `GooseLang/Ext/Fs/Impl.lean`: no process state, nothing logged, every file named and
on disk), which is what a fresh process on a real machine sees (the extension's environment
assumptions). Nothing is said of a crashing machine's state after a crash: that is the extensions'
crash relations' (`Robust`'s executions). What `Robust` states itself (each machine a fresh Go
process, the extensions' `initLocal`/`initGlobal`) is not repeated.

Two things a reader must know (independent review, 2026-11-22, `notes/dist-crash-bridge.md`):
- **The start conditions are also `Robust`'s now.** Since 2026-11-22 the net extension's and the
  file extension's semantics state their initial states (`Net.net_semantics`'s `initLocal`/
  `initGlobal`: no listener, no connection; `Fs.fs_semantics`'s `initLocal`: `FsInit`), which `Robust`
  assumes of every machine and of the network; so "no listener, no connection" and "files as on disk"
  here repeat `Robust`'s premises, and this definition can shrink to the address facts
  (`robust_of_netFsBoot_addrs`, `NetFsBridge.lean`, takes only those).
- **Each machine's files are its own.** The model gives each machine its own file system, and the
  file extension assumes that no other process changes its trees: that must count the other machines'
  programs. A deployment where two machines share a root (e.g. two replicas in one mount namespace
  using the same directory) is outside what this premise describes.
-/
module

public import Net.Statement.DistDeploy
public import GooseLang.Ext.Fs.Ghost

@[expose] public section

noncomputable section

namespace Perennial
namespace Net

/-- **The deployment of machines over the network and Linux files**: the distributed deployment's start of every
machine (`DistDeploy`), and every machine's files as on disk (`Fs.FsInit`). -/
def NetFsDeploy [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext] [HasExt netExt]
    [HasExt Fs.fsExt] (addrs : List GoString) (crashing stable : List (Expr × state))
    (g : GlobalState) : Prop :=
  DistDeploy addrs (crashing ++ stable) g ∧
  ∀ m ∈ crashing ++ stable, Fs.FsInit (extLocal Fs.fsExt m.2.world)

end Net
end Perennial

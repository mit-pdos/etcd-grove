/-
**The deployment of machines over the network and Linux files** [Trusted definition!]: the premise of
a robustness statement whose machines run over `[netExt, fsExt]`, some of which crash and restart
(etcd-dist stage D3, `Net/Statement/NetFsBridge.lean`):

    NetFsDeploy addrs crashing stable g → Robust crashing stable g threads bound

It is the kits' deployment (`KitDeploy`, `KitDeploy.lean`) of all the machines, crashing and stable:
the addresses `addrs` are distinct and valid, the network has no connection, and no machine has a
listener; and, on every machine, its files are as on disk (`Fs.FsInit`, the Linux file extension's
initial state, `GooseLang/Ext/Fs/Impl.lean`: no process state, nothing logged, every file named and
on disk), which is what a fresh process on a real machine sees (the extension's environment
assumptions). Nothing is said of a crashing machine's state after a crash: that is the extensions'
crash relations' (`Robust`'s executions). What `Robust` states itself (each machine a fresh Go
process, the extensions' `initLocal`/`initGlobal`) is not repeated.
-/
module

public import Net.Statement.KitDeploy
public import GooseLang.Ext.Fs.Ghost

@[expose] public section

noncomputable section

namespace Perennial
namespace Net

/-- **The deployment of machines over the network and Linux files**: the kits' deployment of every
machine (`KitDeploy`), and every machine's files as on disk (`Fs.FsInit`). -/
def NetFsDeploy [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext] [HasExt netExt]
    [HasExt Fs.fsExt] (addrs : List GoString) (crashing stable : List (Expr × state))
    (g : GlobalState) : Prop :=
  KitDeploy addrs (crashing ++ stable) g ∧
  ∀ m ∈ crashing ++ stable, Fs.FsInit (extLocal Fs.fsExt m.2.world)

end Net
end Perennial

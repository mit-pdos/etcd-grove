/-
**A distributed deployment's start** [Trusted definition!]: the premise of every top-level theorem
about machines over the network that never crash (`notes/dsverify-net-port-plan.md`, phase 4).

Such a theorem is the repository's robustness statement (`Robustness.Robust`,
`Robustness/Statement.lean`) of its machines, none of which crashes (the plan's Q4: no restart, a
process's death is a cut for its peers, D10, D11), under this premise:

    DistDeploy addrs nodes g → Robust [] nodes g threads bound

`DistDeploy addrs nodes g` is data about the deployment's addresses, the network's start `g` and the
machines' initial local states (`nodes`, each a program and its local state): the addresses
`addrs` (the ones the deployment's programs listen at and dial) are distinct and valid (`addrOk`, D20,
decidable), the network has no connection (`NetGlobal.init`), and every machine has no listener
(`NetLocal.init`). Which machine listens where is not a premise (v3.4: the network has no plan and
no hosts; the deployment's proof shows it). What `Robust` states itself (each machine a fresh Go process,
`Fresh`) is not repeated. Over any list of extensions that has the net extension
(`[HasExt Net.netExt]`).

It names no program: the part `Net/` is exported (phase 3).
-/
module

public import GooseLang.Ext.Net.Deploy
public import Perennial.GooseLang.DistLang
public import GooseLang.Ext.Net.Ghost

@[expose] public section

noncomputable section

namespace Perennial
namespace Net

/-- **A distributed deployment's start**: the addresses `addrs` are distinct and valid, the network has no
connection, and every machine of `nodes` has no listener. -/
def DistDeploy [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext] [HasExt netExt]
    (addrs : List GoString) (nodes : List (Expr × state)) (g : GlobalState) : Prop :=
  addrs.Nodup ∧ (∀ a ∈ addrs, addrOk a = true) ∧
  (extGlobal netExt g.globalWorld).init ∧
  ∀ m ∈ nodes, (extLocal netExt m.2.world).init

end Net
end Perennial

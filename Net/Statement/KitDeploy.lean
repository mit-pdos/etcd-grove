/-
**The deployment of a network kit** [Trusted definition!]: the premise of every kit's top-level
theorem (`notes/dsverify-net-port-plan.md`, phase 4).

A kit's theorem is the repository's robustness statement (`Robustness.Robust`,
`Robustness/Statement.lean`) of its machines, none of which crashes (the plan's Q4: no restart, a
process's death is a cut for its peers, D10, D11), under this premise:

    KitDeploy addrs nodes g → Robust [] nodes g bound

`KitDeploy addrs nodes g` is data about the kit's addresses, the network's start `g` and the
machines' initial local states (`nodes`, each a program and its local state): the addresses
`addrs` (the ones the kit's programs listen at and dial) are distinct and valid (`addrOk`, D20,
decidable), the network has no connection (`NetGlobal.init`), and every machine has no listener
(`NetLocal.init`). Which machine listens where is not a premise (v3.4: the network has no plan and
no hosts; the kit's proof shows it). What `Robust` states itself (each machine a fresh Go process,
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

/-- **A kit's deployment**: the addresses `addrs` are distinct and valid, the network has no
connection, and every machine of `nodes` has no listener. -/
def KitDeploy [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext] [HasExt netExt]
    (addrs : List GoString) (nodes : List (Expr × state)) (g : GlobalState) : Prop :=
  addrs.Nodup ∧ (∀ a ∈ addrs, addrOk a = true) ∧
  (extGlobal netExt g.globalWorld).init ∧
  ∀ m ∈ nodes, (extLocal netExt m.2.world).init

end Net
end Perennial

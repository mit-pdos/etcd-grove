/-
**The deployment of a network kit** [Trusted definition!]: the premise of every kit's top-level
theorem (`notes/dsverify-net-port-plan.md`, phase 4).

A kit's theorem is the repository's robustness statement (`Robustness.Robust`,
`Robustness/Statement.lean`) of its machines, none of which crashes (the plan's Q4: no restart, a
process's death is a cut for its peers, D10, D11), under this premise:

    KitDeploy plan hosts nodes g → Robust [] nodes g bound

`KitDeploy plan hosts nodes g` is data about the network's start `g` and the machines' initial
local states (`nodes`, each a program and its local state): the plan `plan` (address, host)
pairs is well formed (`PlanWellFormed`, D20, decidable) and is the network's plan, the network has
no connection, and machine `i` is on the host `hosts[i]` (its local state of the net extension)
with no listener. What `Robust` states itself (each machine a fresh Go process, `Fresh`) is not
repeated. Over any list of extensions that has the net extension (`[HasExt Net.netExt]`).

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

/-- **A kit's deployment**: the plan `plan` is well formed and is the network's plan, the network
has no connection, and machine `i` of `nodes` is on the host `hosts[i]`, with no listener. -/
def KitDeploy [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext] [HasExt netExt]
    (plan : List (GoString × GoString)) (hosts : List GoString)
    (nodes : List (Expr × state)) (g : GlobalState) : Prop :=
  PlanWellFormed plan ∧
  (extGlobal netExt g.globalWorld).plan = GMap.ofList plan ∧
  (extGlobal netExt g.globalWorld).conns = ∅ ∧
  hosts.length = nodes.length ∧
  ∀ (i : Nat) (h : GoString) (m : Expr × state), hosts[i]? = some h → nodes[i]? = some m →
    (extLocal netExt m.2.world).host = h ∧ (extLocal netExt m.2.world).lis = ∅

end Net
end Perennial

/-
Ported from dsverify-lab examples/paxos/proof/Paxos/Proof/Deploy.lean (lab master 7a84fb35; notes/dsv-paxos.md).

The deployment's API (`netcluster.go`; stage 1 interface, frozen at `stage1-frozen`): what the
kit's adapter (`examples/paxosnet`) and the start need of `RunServer`, `NewNetCluster` and
`NetCluster.Propose`, for the kit's configuration (3 acceptors, 2 learners, 4 clients over the
nine addresses `addrs`: here each client is a machine of its own, at its own address, where the
lab's four clients shared one client node).

* `allProtos Γ`: every configured address's protocols are the wire's over `msgOK Γ` (set at the
  start, persistent).
* `clientTok Γ c`: client `c`'s tokens (register once, propose once, take the receipt once).
* `is_cluster Γ c cl` (persistent): `NewNetCluster`'s result on client `c`'s node; its lock holds
  `c`'s tokens until `c` has proposed.
* `Propose(c, v, waitMs)`: the client's update `opAU Γ v Q` goes in; `(w, true)` gives the
  commit's receipt `Q w`; `(_, false)` gives nothing back (the update may be committed later, by
  the acceptor step that first chooses `v`: helping).
-/
module

public import Dsverify.Proof.github_com.xiang90.paxos.Agents
public import Perennial.Proof.sync

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

namespace github_com.xiang90.paxos

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The deployment's node addresses (`paxosnet.PaxosAddrs()`): acceptors 1..3, learners 2001,
2002, then client `c`'s, `c = 0..3`. -/
def addrs : List GoString :=
  [go!"127.0.0.1:7401", go!"127.0.0.1:7402", go!"127.0.0.1:7403", go!"127.0.0.1:7404",
   go!"127.0.0.1:7405", go!"127.0.0.1:7406", go!"127.0.0.1:7407", go!"127.0.0.1:7408",
   go!"127.0.0.1:7409"]

/-- Client `c`'s node's agents, in `NewNetCluster`'s order: proposer `1001 + c`, box `3001 + c`. -/
def clientIds (c : w64) : List w64 := [W64 1001 + c, W64 3001 + c]

/-- `agentAddrs(addrs, 3, 2, 4)`: every agent's node address. -/
def agentMap : GMap w64 GoString :=
  <[W64 1 := addrs.getD 0 []]> (<[W64 2 := addrs.getD 1 []]> (<[W64 3 := addrs.getD 2 []]>
  (<[W64 2001 := addrs.getD 3 []]> (<[W64 2002 := addrs.getD 4 []]>
  (<[W64 1001 := addrs.getD 5 []]> (<[W64 3001 := addrs.getD 5 []]>
  (<[W64 1002 := addrs.getD 6 []]> (<[W64 3002 := addrs.getD 6 []]>
  (<[W64 1003 := addrs.getD 7 []]> (<[W64 3003 := addrs.getD 7 []]>
  (<[W64 1004 := addrs.getD 8 []]> (<[W64 3004 := addrs.getD 8 []]> ∅))))))))))))

section gdefs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] 
variable {GF : BundledGFunctors} [G : GooseGlobalGS HasLC.hasLC GF] [π : NetProtoGS]

/-- Every configured address's protocols (persistent). -/
def allProtos (Γ : Names) : IProp GF :=
  iprop([∗list] a ∈ addrs, addrProto a (wireProto (msgOK Γ)) noProto)

/-- Client `c`'s tokens. -/
def clientTok (Γ : Names) (c : w64) : IProp GF :=
  iprop(rtok Γ c ∗ ptok Γ (W64 1001 + c) ∗ dtok Γ c)

end gdefs

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [π : NetProtoGS]

/-- Client `c`'s node's lock invariant: which clients have proposed, and `c`'s tokens until it has. -/
def clusterLock (Γ : Names) (c : w64) (usl : GoSlice) : IProp GF :=
  iprop(∃ used : List Bool, usl ↦* used ∗ ⌜used.length = 4⌝ ∗
    if used[uint.nat c]? = some false then clientTok Γ c else True)

/-- Client `c`'s node of the deployment (persistent; the deployment module's slot). -/
def is_cluster (Γ : Names) (c : w64) (cl : Loc) : IProp GF :=
  iprop(∃ (nd : Loc) (asl : GoSlice) (mu : Loc) (usl : GoSlice),
    cl.[NetCluster, go!"node"] ↦□ nd ∗ cl.[NetCluster, go!"acceptors"] ↦□ asl ∗
    cl.[NetCluster, go!"mu"] ↦□ mu ∗ cl.[NetCluster, go!"used"] ↦□ usl ∗
    asl ↦*□ accIds ∗ isPaxos Γ ∗ is_node nd (msgOK Γ) agentMap (clientIds c) ∗
    sync.isMutex mu (clusterLock Γ c usl))

instance is_cluster_persistent (Γ : Names) (c : w64) (cl : Loc) :
    Persistent (is_cluster (GF := GF) Γ c cl) := by
  unfold is_cluster isPaxos; infer_instance

end defs

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [π : NetProtoGS]
variable [package_sem : paxos.Assumptions] [field_sem : net.FieldAssumptions]
  [sync.Assumptions]

local notation "pkg" => pkg_id.github_com.xiang90.paxos

/-- `RunServer(addrs, me, 3, 2, 4)` on server node `me` (1..5): never returns. -/
abbrev RunServer.spec : Prop :=
  ∀ (Γ : Names) (sl : GoSlice) (me : w64), 1 ≤ uint.nat me ∧ uint.nat me ≤ 5 →
  {{ isPkgInit (PROP := IProp GF) pkg ∗ isPaxos Γ ∗ sl ↦*□ addrs ∗ allProtos Γ ∗
      (if uint.nat me ≤ 3 then stOwn Γ me AccState.init else True) }}
    (App (App (App (App (App (Val (@! RunServer)) (Val #sl)) (Val #me)) (Val #(W64 3)))
      (Val #(W64 2))) (Val #(W64 4)))
  {{ RET #(); False }}

/-- `NewNetCluster(addrs, c, 3, 2, 4)` on client `c`'s node. -/
abbrev NewNetCluster.spec : Prop :=
  ∀ (Γ : Names) (sl : GoSlice) (c : w64), uint.nat c < 4 →
  {{ isPkgInit (PROP := IProp GF) pkg ∗ isPaxos Γ ∗ sl ↦*□ addrs ∗ allProtos Γ ∗
      clientTok Γ c }}
    (App (App (App (App (App (Val (@! NewNetCluster)) (Val #sl)) (Val #c)) (Val #(W64 3)))
      (Val #(W64 2))) (Val #(W64 4)))
  {{ (cl : Loc), RET #cl; is_cluster Γ c cl }}

/-- `cl.Propose(c, v, waitMs)` on client `c`'s node: the client's update goes in; an answer
`(w, true)` gives its receipt for `w`, `(_, false)` (an unknown outcome) nothing. -/
abbrev NetCluster.Propose.spec : Prop :=
  ∀ (Γ : Names) (clp : Loc) (c waitMs : w64) (v : GoString) (Q : GoString → IProp GF),
  uint.nat c < 4 → (v.length : Int) < 2 ^ 48 →
  ⊢ isPkgInit (PROP := IProp GF) pkg -∗ is_cluster Γ c clp -∗ opAU Γ v Q -∗
    WP (App (App (App (Val (clp @!! go.GoType.PointerType NetCluster.ty @!! go!"Propose"))
        (Val #c)) (Val #v)) (Val #waitMs))
      {{ r, (∃ w : GoString, ⌜r = PairV #w #true⌝ ∗ Q w) ∨
            ⌜∃ x : GoString, r = PairV #x #false⌝ }}

end specs

end github_com.xiang90.paxos

end Perennial

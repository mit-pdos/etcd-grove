/-
Ported from dsverify-lab examples/paxos/proof/Paxos/Proof/Deploy.lean (lab master 7a84fb35; notes/dsv-paxos.md).

The deployment's API (`netcluster.go`; stage 1 interface, frozen at `stage1-frozen`): what the
kit's adapter (`examples/paxosnet`) and the start need of `RunServer`, `NewNetCluster` and
`NetCluster.Propose`, for the lab's configuration (3 acceptors, 2 learners, 4 clients over the
six addresses `addrs`).

* `allProtos Γ`: every configured address's protocols are the wire's over `msgOK Γ` (set at the
  start, persistent).
* `clientToks Γ`: the client node's per-client tokens (register once, propose once, take the
  receipt once).
* `is_cluster Γ cl` (persistent): `NewNetCluster`'s result; its lock holds the tokens of the
  clients that have not proposed yet.
* `Propose(c, v, waitMs)`: logically atomic in the B form: the client's update `opAU Γ v Q`
  goes in; `(w, true)` gives the commit's receipt `Q σ σ' w`; `(_, false)` gives nothing back
  (the update may be committed later, by the acceptor step that first chooses `v`: helping).
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

/-- The client node's agents, in `NewNetCluster`'s order: proposer `1001 + c`, box `3001 + c`. -/
def clientIds : List w64 :=
  [W64 1001, W64 3001, W64 1002, W64 3002, W64 1003, W64 3003, W64 1004, W64 3004]

/-- `agentAddrs(addrs, 3, 2, 4)`: every agent's node address. -/
def agentMap : GMap w64 GoString :=
  <[W64 1 := addrs.getD 1 []]> (<[W64 2 := addrs.getD 2 []]> (<[W64 3 := addrs.getD 3 []]>
  (<[W64 2001 := addrs.getD 4 []]> (<[W64 2002 := addrs.getD 5 []]>
  (<[W64 1001 := addrs.getD 0 []]> (<[W64 3001 := addrs.getD 0 []]>
  (<[W64 1002 := addrs.getD 0 []]> (<[W64 3002 := addrs.getD 0 []]>
  (<[W64 1003 := addrs.getD 0 []]> (<[W64 3003 := addrs.getD 0 []]>
  (<[W64 1004 := addrs.getD 0 []]> (<[W64 3004 := addrs.getD 0 []]> ∅))))))))))))

section gdefs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] 
variable {GF : BundledGFunctors} [G : GooseGlobalGS HasLC.hasLC GF]

/-- Every configured address's protocols (persistent). -/
def allProtos (Γ : Names) : IProp GF :=
  iprop([∗list] a ∈ addrs, addrProto a (wireProto (msgOK Γ)) noProto)

/-- Client `c`'s tokens. -/
def clientTok (Γ : Names) (c : w64) : IProp GF :=
  iprop(rtok Γ c ∗ ptok Γ (W64 1001 + c) ∗ dtok Γ c)

/-- The client node's tokens. -/
def clientToks (Γ : Names) : IProp GF :=
  iprop([∗list] c ∈ [W64 0, W64 1, W64 2, W64 3], clientTok Γ c)

end gdefs

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [π : NetProtoGS]

/-- `NetCluster`'s lock invariant: which clients have proposed, and the tokens of the others. -/
def clusterLock (Γ : Names) (usl : GoSlice) : IProp GF :=
  iprop(∃ used : List Bool, usl ↦* used ∗ ⌜used.length = 4⌝ ∗
    [∗list] c ↦ u ∈ used, if u then True else clientTok Γ (W64 c))

/-- The client node's deployment (persistent; the deployment module's slot). -/
def is_cluster (Γ : Names) (cl : Loc) : IProp GF :=
  iprop(∃ (nd : Loc) (asl : GoSlice) (mu : Loc) (usl : GoSlice),
    cl.[NetCluster, go!"node"] ↦□ nd ∗ cl.[NetCluster, go!"acceptors"] ↦□ asl ∗
    cl.[NetCluster, go!"mu"] ↦□ mu ∗ cl.[NetCluster, go!"used"] ↦□ usl ∗
    asl ↦*□ accIds ∗ isPaxos Γ ∗ is_node nd (msgOK Γ) agentMap clientIds ∗
    sync.isMutex mu (clusterLock Γ usl))

instance is_cluster_persistent (Γ : Names) (cl : Loc) :
    Persistent (is_cluster (GF := GF) Γ cl) := by
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
  {{ isPkgInit (PROP := IProp GF) pkg ∗ isPaxos Γ ∗ sl ↦*□ addrs ∗
      addrTok (GF := GF) (addrs.getD (uint.nat me) []) ∗ allProtos Γ ∗
      (if uint.nat me ≤ 3 then stOwn Γ me AccState.init else True) }}
    (App (App (App (App (App (Val (@! RunServer)) (Val #sl)) (Val #me)) (Val #(W64 3)))
      (Val #(W64 2))) (Val #(W64 4)))
  {{ RET #(); False }}

/-- `NewNetCluster(addrs, 3, 2, 4)` on the client node. -/
abbrev NewNetCluster.spec : Prop :=
  ∀ (Γ : Names) (sl : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg ∗ isPaxos Γ ∗ sl ↦*□ addrs ∗
      addrTok (GF := GF) (addrs.getD 0 []) ∗ allProtos Γ ∗ clientToks Γ }}
    (App (App (App (App (Val (@! NewNetCluster)) (Val #sl)) (Val #(W64 3))) (Val #(W64 2)))
      (Val #(W64 4)))
  {{ (cl : Loc), RET #cl; is_cluster Γ cl }}

/-- `cl.Propose(c, v, waitMs)`: logically atomic with a maybe-committed unknown outcome. -/
abbrev NetCluster.Propose.spec : Prop :=
  ∀ (Γ : Names) (clp : Loc) (c waitMs : w64) (v : GoString)
    (Q : Option GoString → Option GoString → GoString → IProp GF),
  uint.nat c < 4 → (v.length : Int) < 2 ^ 48 →
  ⊢ isPkgInit (PROP := IProp GF) pkg -∗ is_cluster Γ clp -∗ opAU Γ v Q -∗
    WP (App (App (App (Val (clp @!! go.GoType.PointerType NetCluster.ty @!! go!"Propose"))
        (Val #c)) (Val #v)) (Val #waitMs))
      {{ r, (∃ w : GoString, ⌜r = PairV #w #true⌝ ∗ ∃ σ σ', Q σ σ' w) ∨
            ⌜∃ x : GoString, r = PairV #x #false⌝ }}

end specs

end github_com.xiang90.paxos

end Perennial

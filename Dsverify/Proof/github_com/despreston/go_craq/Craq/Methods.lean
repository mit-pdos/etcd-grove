/-
The address-level method specs of go-craq's RPC services (stage 1 interface): what a caller
deposits for each method of a node or of the coordinator, and what it gets back, over the wire
values (`Wire.lean`) and the protocol (`Protocol.lean`). They are the `RpcWorld`'s service
specs (`net.rpc.MethodSpec`, `Net/Proof/net/rpc/Proto.lean`): a client's `Call` gets `Φ reply msg`
of exactly one run for a nil or `ServerError` result; the server's receiver meets them
(`rcvrOk`).

Every method answers an error with an empty reply and a non-empty message (`errOk`), but the
coordinator's `RemoveNode` (stage 2: any caller, any address; its caller uses no result, so its
spec asks `Φ` of every outcome). Methods no caller uses (`ClientWrite`, `ReadAll`) have the spec
`False`: no run of them happens.
-/
module

public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Protocol
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Wire
public import Net.Proof.net.rpc.Proto

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

namespace github_com.despreston.go_craq

/-- Node.Read's error for a key with no committed version (the kit's adapter's not-found). -/
def notFoundMsg : GoString := go!"key doesn't exist"

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable {GF : BundledGFunctors} [G : GooseGlobalGS HasLC.hasLC GF]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- Every error answer (a non-empty message, no reply) is allowed. -/
def errOk (Φ : List w8 → GoString → IProp GF) : IProp GF :=
  iprop(∀ msg : GoString, ⌜msg ≠ []⌝ -∗ Φ [] msg)

/-- A propagation response's items are versions (persistent). -/
def respItems (γ : CraqNames) (resp : GMap GoString (List (GoString × w64))) : IProp GF :=
  iprop([∗map] k ↦ vvs ∈ resp, [∗list] e ∈ vvs, valsElem γ e.2 k e.1)

/-- ... and committed ones. -/
def respCommitted (γ : CraqNames) (resp : GMap GoString (List (GoString × w64))) : IProp GF :=
  iprop([∗map] k ↦ vvs ∈ resp, [∗list] e ∈ vvs, cvLb γ k e.2)

/-- A back propagation covers the log `L` its requester knows node `a`'s committed versions
cover (`covers γ a L`, passed with the request): for every key whose version in `L` is newer than
the request's, the response has that version or a newer one. -/
def respCovers (req : GMap GoString w64) (resp : GMap GoString (List (GoString × w64)))
    (L : CLog) : Prop :=
  ∀ k, uint.Z (reqVer req k) < uint.Z (cvOf L k) →
    ∃ x v', (x, v') ∈ (resp.lookup k).getD [] ∧ uint.Z (cvOf L k) ≤ uint.Z v'

/-- The addresses a metadata names are chain addresses (or none). -/
def metaAddrsOk (chain : List GoString) (m : MetaV) : Prop :=
  m.prev ∈ go!"" :: chain ∧ m.next ∈ go!"" :: chain ∧ m.tail ∈ go!"" :: chain

/-- The catch-up source's facts: node `s` covers the tail token's log (no source: nothing
committed). -/
def srcOk (γ : CraqNames) (s : GoString) (L : CLog) : IProp GF :=
  if s = go!"" then iprop(⌜∀ k, cvOf L k = W64 0⌝) else covers γ s L

/-- What an Update deposits besides the role: the tail token when it makes the node the tail
(the node is not, as the coordinator knows: `r.1 = false`), with its catch-up source's facts
(the node's successor if it has one: the removed tail; else its new predecessor: the tail it
joins after). -/
def updDep (γ : CraqNames) (r : Role) (m : MetaV) : IProp GF :=
  if m.isTail ∧ r.1 = false then
    iprop(∃ L : CLog, tailTok γ L ∗ srcOk γ (if r.2 = go!"" then m.prev else r.2) L)
  else iprop(True)

/-- What a successful Update gives back: the role as told, and the tail token when it told the
tail that it is not the tail any more, with its committed versions' cover. -/
def updPost (γ : CraqNames) (a : GoString) (r : Role) (m : MetaV) : IProp GF :=
  iprop(roleHalf γ a (m.isTail, m.next) ∗
    if m.isTail = false ∧ r.1 = true then iprop(∃ L : CLog, tailTok γ L ∗ covers γ a L)
    else iprop(True))

/-- A get's answers through `Read`: the value, or "key doesn't exist", each linearized; any
other non-empty message, nothing. -/
def readCont (γ : CraqNames) (k : GoString) (Q : KvM.Output → IProp GF)
    (Φ : List w8 → GoString → IProp GF) : IProp GF :=
  iprop((∀ (x : GoString) (σ : KvM.State), Q (.got (σ k)) -∗ ⌜σ k = some x⌝ -∗
      Φ (encItem k x) []) ∧
    (∀ σ : KvM.State, Q (.got (σ k)) -∗ ⌜σ k = none⌝ -∗ Φ [] notFoundMsg) ∧
    (∀ msg : GoString, ⌜msg ≠ [] ∧ msg ≠ notFoundMsg⌝ -∗ Φ [] msg))

/-- The methods of the node at address `a`. -/
def nodeSpec (γ : CraqNames) (chain : List GoString) (a : GoString) : net.rpc.MethodSpec GF :=
  fun m args Φ =>
  if m = go!"Ping" then
    iprop(⌜args = encEmptyArgs⌝ ∗ (Φ encEmptyReply [] ∧ errOk Φ))
  else if m = go!"Update" then
    iprop(∃ (md : MetaV) (r : Role), ⌜args = encMeta md ∧ metaAddrsOk chain md⌝ ∗ roleHalf γ a r ∗ updDep γ r md ∗
      ((updPost γ a r md -∗ Φ encEmptyReply []) ∧ errOk Φ))
  else if m = go!"Write" then
    iprop(∃ (k x : GoString) (v : w64), ⌜args = encWriteArgs k x v⌝ ∗ valsElem γ v k x ∗
      ((cvLb γ k v -∗ Φ encEmptyReply []) ∧ errOk Φ))
  else if m = go!"Commit" then
    iprop(∃ (k : GoString) (v : w64), ⌜args = encCommitArgs k v⌝ ∗ cvLb γ k v ∗
      (Φ encEmptyReply [] ∧ errOk Φ))
  else if m = go!"LatestVersion" then
    iprop(∃ (k : GoString) (Q : KvM.Output → IProp GF),
      ⌜args = encString k⌝ ∗ opAU γ (.get k) Q ∗
      ((∀ (v : w64) (σ : KvM.State), Q (.got (σ k)) -∗ readFacts γ k v (σ k) -∗
          Φ (encVersionResp k v) []) ∧ errOk Φ))
  else if m = go!"Read" then
    iprop(∃ (k : GoString) (Q : KvM.Output → IProp GF),
      ⌜args = encString k⌝ ∗ opAU γ (.get k) Q ∗ readCont γ k Q Φ)
  else if m = go!"FwdPropagate" then
    iprop(∃ req : GMap GoString w64, ⌜encPropReq req args⌝ ∗
      ((∀ (resp : GMap GoString (List (GoString × w64))) (rbs : List w8), ⌜encPropResp resp rbs⌝ -∗
          respItems γ resp -∗ Φ rbs []) ∧ errOk Φ))
  else if m = go!"BackPropagate" then
    iprop(∃ (req : GMap GoString w64) (L : CLog), ⌜encPropReq req args⌝ ∗ covers γ a L ∗
      ((∀ (resp : GMap GoString (List (GoString × w64))) (rbs : List w8), ⌜encPropResp resp rbs⌝ -∗
          respItems γ resp -∗ respCommitted γ resp -∗ ⌜respCovers req resp L⌝ -∗ Φ rbs []) ∧
        errOk Φ))
  else iprop(False)

/-- The methods of the coordinator; `chain` are the chain nodes' addresses. -/
def coordSpec (γ : CraqNames) (chain : List GoString) : net.rpc.MethodSpec GF := fun m args Φ =>
  if m = go!"AddNode" then
    iprop(∃ a : GoString, ⌜args = encString a ∧ a ∈ chain⌝ ∗ joinTicket γ a ∗
      ((∀ md : MetaV, Φ (encMeta md) []) ∧ errOk Φ))
  else if m = go!"Write" then
    iprop(∃ (k x : GoString) (Q : KvM.Output → IProp GF),
      ⌜args = encClientWriteArgs k x⌝ ∗ opAU γ (.put k x) Q ∗
      ((putReceipt k x Q -∗ Φ encEmptyReply []) ∧ errOk Φ))
  else if m = go!"RemoveNode" then
    -- any caller, any address (the client nodes' removals, stage 2); the caller learns nothing
    iprop(∃ a : GoString, ⌜args = encString a⌝ ∗ (Φ encEmptyReply [] ∧ ∀ msg : GoString, Φ [] msg))
  else iprop(False)

/-- The run's services: the coordinator at `cAddr`, the chain nodes at `chain`, each as service
`"RPC"`. -/
def craqSS (γ : CraqNames) (cAddr : GoString) (chain : List GoString) :
    GoString → GoString → Option (net.rpc.MethodSpec GF) := fun a svc =>
  if svc = go!"RPC" then
    (if a = cAddr then some (coordSpec γ chain) else if a ∈ chain then some (nodeSpec γ chain a) else none)
  else none

end specs

end github_com.despreston.go_craq

end Perennial

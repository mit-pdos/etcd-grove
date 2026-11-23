/-
The Go-level interfaces between go-craq's packages (stage 1 interface): each Go interface the
code calls through (`store.Storer`, `transport.NodeClient`, `transport.CoordinatorClient`,
`transport.NodeService`, `transport.CoordinatorService`, `transport.NodeClientFactory`) is a
persistent predicate on the interface value bundling the specs of the methods its callers use
(stated on `#(methods e.ty m e.v)`, what a method call on an interface resolves to). The
implementing package proves its values meet it; the calling package uses only the predicate.

* `Cfg`: the run's configuration seen by the code: ghost names `γ`, the rpc world `W`, the
  coordinator's address `cAddr`, the chain's addresses `chain`; `craqCtx` (persistent): the
  protocol's invariant, `W`'s services are the run's (`craqSS`), every address serves net/rpc over HTTP (`httpRpcAddr`: Net's `rpcAddrP`
  behind HTTP's handshake, models-rpc-http).
* The store (`isStore`, `storeOwn`): logically atomic specs over the abstract contents, a map
  from keys to their items `(version, value, committed)` in arrival order (`StoreS`).
* The clients (`isNodeClient`, `isCoordClient`, `freshNodeClient`, `freshCoordClient`): their
  methods are the address-level method specs (`Methods.lean`) over Go values; errors come with
  their `Error()` (`errAny`).
* The services (`isNodeSvc`, `isCoordSvc`): what the rpc bindings call; errors have a non-empty
  message (`errMsg`), which the binding sends.
-/
module

public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Methods
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Store
public import Dsverify.Proof.github_com.despreston.go_craq.transport.netrpc.Base
public import Net.Proof.net.rpc.ClientDefs
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.HttpRpc
public import Net.Proof.models_lab.Errors

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

namespace github_com.despreston.go_craq

section global
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [G : GooseGlobalGS HasLC.hasLC GF] [π : NetProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The run's configuration as the code sees it. -/
structure Cfg (GF : BundledGFunctors) where
  γ : CraqNames
  W : net.rpc.RpcWorld GF
  cAddr : GoString
  chain : List GoString

/-- The run's shared facts (persistent). -/
def craqCtx (cfg : Cfg GF) : IProp GF :=
  iprop(isCraq cfg.γ ∗ ⌜cfg.W.SS = craqSS cfg.γ cfg.cAddr cfg.chain ∧ cfg.chain.Nodup ∧
      cfg.cAddr ∉ cfg.chain ∧ go!"" ∉ cfg.chain⌝ ∗
    [∗list] a ∈ cfg.cAddr :: cfg.chain, httpRpcAddr cfg.W a)

instance craqCtx_persistent (cfg : Cfg GF) : Persistent (craqCtx (G := G) cfg) := by
  unfold craqCtx; infer_instance

/-- Node `a`'s share of the ghost state at the start. -/
def nodeRes (cfg : Cfg GF) (a : GoString) : IProp GF :=
  iprop(roleHalf cfg.γ a ((false, go!"") : Role) ∗ nlogAuth cfg.γ a [])

/-- The coordinator's share of the ghost state at the start. -/
def coordRes (cfg : Cfg GF) : IProp GF :=
  iprop(tailTok cfg.γ [] ∗ nextHalf cfg.γ (W64 0) ∗
    [∗list] a ∈ cfg.chain, roleHalf cfg.γ a ((false, go!"") : Role))

end global

section ifaces
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [net.rpc.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]
variable [store.Assumptions] [transport.Assumptions] [transport.netrpc.Assumptions]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-! ## Wire values in the heap -/

/-- `ptr` (a `*transport.NodeMeta`) holds `m`. -/
def metaPtr (ptr : Loc) (dq : DFrac) (m : MetaV) : IProp GF :=
  iprop(ptr ↦{dq} (transport.NodeMeta.mk m.isHead m.isTail m.prev m.next m.tail))

/-- `ptr` (a `*transport.PropagateRequest`) holds the map `req`. -/
def reqPtr (ptr : Loc) (dq : DFrac) (req : GMap GoString w64) : IProp GF :=
  iprop(∃ mp : Loc, ptr ↦{dq} mp ∗ ownMap mp dq req)

/-- `ptr` (a `*transport.PropagateResponse`) holds the map `resp` (values and slices owned). -/
def respPtr (ptr : Loc) (resp : GMap GoString (List (GoString × w64))) : IProp GF :=
  iprop(∃ (mp : Loc) (m : GMap GoString GoSlice), ptr ↦ mp ∗ ownMap mp (DFrac.own 1) m ∗
    ⌜∀ k, (m.lookup k).isSome ↔ (resp.lookup k).isSome⌝ ∗
    [∗map] k ↦ sl ∈ m, ∃ (vvs : List transport.ValueVersion),
      sl ↦* vvs ∗ ⌜vvs.map (·.Version') = ((resp.lookup k).getD []).map Prod.snd⌝ ∗
      [∗list] i ↦ vv ∈ vvs, ∃ x, ⌜(((resp.lookup k).getD [])[i]?).map Prod.fst = some x⌝ ∗
        vv.Value' ↦*□ x)

/-! ## The clients -/

/-- `c` is a client of the node at `a` (persistent). -/
def isNodeClient (cfg : Cfg GF) (c : GoInterface) (a : GoString) : IProp GF :=
  iprop(∃ e : GoInterfaceOk, ⌜c = interface.ok e ∧ a ∈ cfg.chain⌝ ∗ □ (
    -- Ping()
    (∀ Φ : val → IProp GF, ▷ (∀ err : GoInterface, (⌜err = interface.nil⌝ ∨ models_lab.errAny err) -∗
        Φ #err) -∗
      WP (App (Val #(methods e.ty go!"Ping" e.v)) (Val #())) {{ Φ }}) ∧
    -- Write(k, val, v)
    (∀ (k : GoString) (sl : GoSlice) (x : GoString) (v : w64) (Φ : val → IProp GF),
      sl ↦*□ x -∗ valsElem cfg.γ v k x -∗
      ▷ (∀ err : GoInterface, (⌜err = interface.nil⌝ ∗ cvLb cfg.γ k v ∨ models_lab.errAny err) -∗
        Φ #err) -∗
      WP (App (App (App (Val #(methods e.ty go!"Write" e.v)) (Val #k)) (Val #sl)) (Val #v))
        {{ Φ }}) ∧
    -- Commit(k, v)
    (∀ (k : GoString) (v : w64) (Φ : val → IProp GF), cvLb cfg.γ k v -∗
      ▷ (∀ err : GoInterface, (⌜err = interface.nil⌝ ∨ models_lab.errAny err) -∗ Φ #err) -∗
      WP (App (App (Val #(methods e.ty go!"Commit" e.v)) (Val #k)) (Val #v)) {{ Φ }}) ∧
    -- LatestVersion(k)
    (∀ (k : GoString) (Q : KvM.Output → IProp GF) (Φ : val → IProp GF),
      opAU cfg.γ (.get k) Q -∗
      ▷ (∀ (k' : GoString) (v : w64) (err : GoInterface),
          (⌜err = interface.nil⌝ ∗ (∃ σ : KvM.State, Q (.got (σ k)) ∗ readFacts cfg.γ k v (σ k)) ∨
            models_lab.errAny err) -∗
          Φ (PairV (PairV #k' #v) #err)) -∗
      WP (App (Val #(methods e.ty go!"LatestVersion" e.v)) (Val #k)) {{ Φ }}) ∧
    -- Read(k)
    (∀ (k : GoString) (Q : KvM.Output → IProp GF) (Φ : val → IProp GF),
      opAU cfg.γ (.get k) Q -∗
      ▷ (∀ (k' : GoString) (sl : GoSlice) (err : GoInterface),
          ((⌜err = interface.nil⌝ ∗ ∃ (x : GoString) (σ : KvM.State), sl ↦* x ∗
              Q (.got (σ k)) ∗ ⌜σ k = some x⌝) ∨
            (⌜err = net.rpc.serverErr notFoundMsg⌝ ∗ ∃ σ : KvM.State, Q (.got (σ k)) ∗
              ⌜σ k = none⌝) ∨
            (⌜err ≠ interface.nil ∧ err ≠ net.rpc.serverErr notFoundMsg ∧
              (net.rpc.notServerErr err ∨ ∃ msg, err = net.rpc.serverErr msg)⌝)) -∗
          Φ (PairV (PairV #k' #sl) #err)) -∗
      WP (App (Val #(methods e.ty go!"Read" e.v)) (Val #k)) {{ Φ }}) ∧
    -- Update(meta)
    (∀ (ptr : Loc) (dq : DFrac) (m : MetaV) (r : Role) (Φ : val → IProp GF),
      ⌜metaAddrsOk cfg.chain m⌝ -∗ metaPtr ptr dq m -∗ roleHalf cfg.γ a r -∗ updDep cfg.γ r m -∗
      ▷ (∀ err : GoInterface,
          (⌜err = interface.nil⌝ ∗ metaPtr ptr dq m ∗ updPost cfg.γ a r m ∨ models_lab.errAny err) -∗
          Φ #err) -∗
      WP (App (Val #(methods e.ty go!"Update" e.v)) (Val #ptr)) {{ Φ }}) ∧
    -- FwdPropagate(req)
    (∀ (ptr : Loc) (dq : DFrac) (req : GMap GoString w64) (Φ : val → IProp GF),
      reqPtr ptr dq req -∗
      ▷ (∀ (rp : Loc) (err : GoInterface),
          (⌜err = interface.nil⌝ ∗ reqPtr ptr dq req ∗ (∃ resp, respPtr rp resp ∗ respItems cfg.γ resp) ∨
            models_lab.errAny err) -∗ Φ (PairV #rp #err)) -∗
      WP (App (Val #(methods e.ty go!"FwdPropagate" e.v)) (Val #ptr)) {{ Φ }}) ∧
    -- BackPropagate(req)
    (∀ (ptr : Loc) (dq : DFrac) (req : GMap GoString w64) (L : CLog) (Φ : val → IProp GF),
      reqPtr ptr dq req -∗ covers cfg.γ a L -∗
      ▷ (∀ (rp : Loc) (err : GoInterface),
          (⌜err = interface.nil⌝ ∗ reqPtr ptr dq req ∗ (∃ resp, respPtr rp resp ∗ respItems cfg.γ resp ∗
              respCommitted cfg.γ resp ∗ ⌜respCovers req resp L⌝) ∨
            models_lab.errAny err) -∗ Φ (PairV #rp #err)) -∗
      WP (App (Val #(methods e.ty go!"BackPropagate" e.v)) (Val #ptr)) {{ Φ }}) ∧
    -- Close()
    (∀ Φ : val → IProp GF, ▷ (∀ err : GoInterface, Φ #err) -∗
      WP (App (Val #(methods e.ty go!"Close" e.v)) (Val #())) {{ Φ }})))

/-- `c` is a client of the coordinator (persistent). -/
def isCoordClient (cfg : Cfg GF) (c : GoInterface) : IProp GF :=
  iprop(∃ e : GoInterfaceOk, ⌜c = interface.ok e⌝ ∗ □ (
    -- AddNode(a)
    (∀ (a : GoString) (Φ : val → IProp GF), ⌜a ∈ cfg.chain⌝ -∗ joinTicket cfg.γ a -∗
      ▷ (∀ (p : Loc) (err : GoInterface), (⌜err = interface.nil⌝ ∨ models_lab.errAny err) -∗
          Φ (PairV #p #err)) -∗
      WP (App (Val #(methods e.ty go!"AddNode" e.v)) (Val #a)) {{ Φ }}) ∧
    -- Write(k, val)
    (∀ (k : GoString) (sl : GoSlice) (dq : DFrac) (x : GoString)
        (Q : KvM.Output → IProp GF) (Φ : val → IProp GF),
      sl ↦*{dq} x -∗ opAU cfg.γ (.put k x) Q -∗
      ▷ (∀ err : GoInterface,
          (⌜err = interface.nil⌝ ∗ sl ↦*{dq} x ∗ putReceipt k x Q ∨ models_lab.errAny err) -∗ Φ #err) -∗
      WP (App (App (Val #(methods e.ty go!"Write" e.v)) (Val #k)) (Val #sl)) {{ Φ }}) ∧
    -- Close()
    (∀ Φ : val → IProp GF, ▷ (∀ err : GoInterface, Φ #err) -∗
      WP (App (Val #(methods e.ty go!"Close" e.v)) (Val #())) {{ Φ }}) ∧
    -- RemoveNode(a), of any address (stage 2: the client nodes' removals)
    (∀ (a : GoString) (Φ : val → IProp GF),
      ▷ (∀ err : GoInterface, (⌜err = interface.nil⌝ ∨ models_lab.errAny err) -∗ Φ #err) -∗
      WP (App (Val #(methods e.ty go!"RemoveNode" e.v)) (Val #a)) {{ Φ }})))

/-- `c` is a new, unconnected node client: `Connect(a)` makes it a client of the node at `a`
(or fails). -/
def freshNodeClient (cfg : Cfg GF) (c : GoInterface) : IProp GF :=
  iprop(∃ e : GoInterfaceOk, ⌜c = interface.ok e⌝ ∗
    ∀ (a : GoString) (Φ : val → IProp GF), ⌜a ∈ cfg.chain⌝ -∗
      ▷ (∀ err : GoInterface, ((⌜err = interface.nil⌝ ∗ isNodeClient cfg c a) ∨
          models_lab.errAny err) -∗ Φ #err) -∗
      WP (App (Val #(methods e.ty go!"Connect" e.v)) (Val #a)) {{ Φ }})

/-- `c` is a new, unconnected coordinator client. -/
def freshCoordClient (cfg : Cfg GF) (c : GoInterface) : IProp GF :=
  iprop(∃ e : GoInterfaceOk, ⌜c = interface.ok e⌝ ∗
    ∀ (Φ : val → IProp GF),
      ▷ (∀ err : GoInterface, ((⌜err = interface.nil⌝ ∗ isCoordClient cfg c) ∨
          models_lab.errAny err) -∗ Φ #err) -∗
      WP (App (Val #(methods e.ty go!"Connect" e.v)) (Val #cfg.cAddr)) {{ Φ }})

/-- `f` (a `transport.NodeClientFactory`) makes new node clients (persistent). -/
def isFactory (cfg : Cfg GF) (f : GoFunc) : IProp GF :=
  iprop(□ ∀ Φ : val → IProp GF, ▷ (∀ c : GoInterface, freshNodeClient cfg c -∗ Φ #c) -∗
    WP (App (Val #f) (Val #())) {{ Φ }})

instance isNodeClient_persistent (cfg : Cfg GF) (c : GoInterface) (a : GoString) :
    Persistent (isNodeClient (hG := hG) cfg c a) := by
  unfold isNodeClient; infer_instance
instance isCoordClient_persistent (cfg : Cfg GF) (c : GoInterface) :
    Persistent (isCoordClient (hG := hG) cfg c) := by
  unfold isCoordClient; infer_instance
instance isFactory_persistent (cfg : Cfg GF) (f : GoFunc) :
    Persistent (isFactory (hG := hG) cfg f) := by
  unfold isFactory; infer_instance

/-! ## The services -/

/-- An error with a non-empty message (persistent). -/
def errNE (err : GoInterface) : IProp GF :=
  iprop(∃ msg : GoString, ⌜msg ≠ []⌝ ∗ net.rpc.errMsg err msg)

/-- `svc` is the node at `a`, as its rpc binding calls it (persistent). -/
def isNodeSvc (cfg : Cfg GF) (svc : GoInterface) (a : GoString) : IProp GF :=
  iprop(∃ e : GoInterfaceOk, ⌜svc = interface.ok e⌝ ∗ □ (
    (∀ Φ : val → IProp GF, ▷ (∀ err : GoInterface, (⌜err = interface.nil⌝ ∨ errNE err) -∗ Φ #err) -∗
      WP (App (Val #(methods e.ty go!"Ping" e.v)) (Val #())) {{ Φ }}) ∧
    (∀ (ptr : Loc) (dq : DFrac) (m : MetaV) (r : Role) (Φ : val → IProp GF),
      ⌜metaAddrsOk cfg.chain m⌝ -∗ metaPtr ptr dq m -∗ roleHalf cfg.γ a r -∗ updDep cfg.γ r m -∗
      ▷ (∀ err : GoInterface, metaPtr ptr dq m -∗
          (⌜err = interface.nil⌝ ∗ updPost cfg.γ a r m ∨ errNE err) -∗ Φ #err) -∗
      WP (App (Val #(methods e.ty go!"Update" e.v)) (Val #ptr)) {{ Φ }}) ∧
    (∀ (k : GoString) (sl : GoSlice) (x : GoString) (v : w64) (Φ : val → IProp GF),
      sl ↦*□ x -∗ valsElem cfg.γ v k x -∗
      ▷ (∀ err : GoInterface, (⌜err = interface.nil⌝ ∗ cvLb cfg.γ k v ∨ errNE err) -∗ Φ #err) -∗
      WP (App (App (App (Val #(methods e.ty go!"Write" e.v)) (Val #k)) (Val #sl)) (Val #v))
        {{ Φ }}) ∧
    (∀ (k : GoString) (v : w64) (Φ : val → IProp GF), cvLb cfg.γ k v -∗
      ▷ (∀ err : GoInterface, (⌜err = interface.nil⌝ ∨ errNE err) -∗ Φ #err) -∗
      WP (App (App (Val #(methods e.ty go!"Commit" e.v)) (Val #k)) (Val #v)) {{ Φ }}) ∧
    (∀ (k : GoString) (Q : KvM.Output → IProp GF) (Φ : val → IProp GF),
      opAU cfg.γ (.get k) Q -∗
      ▷ (∀ (k' : GoString) (v : w64) (err : GoInterface),
          (⌜err = interface.nil ∧ k' = k⌝ ∗ (∃ σ : KvM.State, Q (.got (σ k)) ∗
              readFacts cfg.γ k v (σ k)) ∨ errNE err) -∗
          Φ (PairV (PairV #k' #v) #err)) -∗
      WP (App (Val #(methods e.ty go!"LatestVersion" e.v)) (Val #k)) {{ Φ }}) ∧
    (∀ (k : GoString) (Q : KvM.Output → IProp GF) (Φ : val → IProp GF),
      opAU cfg.γ (.get k) Q -∗
      ▷ (∀ (k' : GoString) (sl : GoSlice) (err : GoInterface),
          ((⌜err = interface.nil ∧ k' = k⌝ ∗ ∃ (x : GoString) (σ : KvM.State), sl ↦*□ x ∗
              Q (.got (σ k)) ∗ ⌜σ k = some x⌝) ∨
            (net.rpc.errMsg err notFoundMsg ∗ ∃ σ : KvM.State, Q (.got (σ k)) ∗
              ⌜σ k = none⌝) ∨
            (∃ msg, ⌜msg ≠ [] ∧ msg ≠ notFoundMsg⌝ ∗ net.rpc.errMsg err msg)) -∗
          Φ (PairV (PairV #k' #sl) #err)) -∗
      WP (App (Val #(methods e.ty go!"Read" e.v)) (Val #k)) {{ Φ }}) ∧
    (∀ (ptr : Loc) (dq : DFrac) (req : GMap GoString w64) (Φ : val → IProp GF),
      reqPtr ptr dq req -∗
      ▷ (∀ (rp : Loc) (err : GoInterface), reqPtr ptr dq req -∗
          (⌜err = interface.nil⌝ ∗ (∃ resp, respPtr rp resp ∗ respItems cfg.γ resp) ∨ errNE err) -∗
          Φ (PairV #rp #err)) -∗
      WP (App (Val #(methods e.ty go!"FwdPropagate" e.v)) (Val #ptr)) {{ Φ }}) ∧
    (∀ (ptr : Loc) (dq : DFrac) (req : GMap GoString w64) (L : CLog) (Φ : val → IProp GF),
      reqPtr ptr dq req -∗ covers cfg.γ a L -∗
      ▷ (∀ (rp : Loc) (err : GoInterface), reqPtr ptr dq req -∗
          (⌜err = interface.nil⌝ ∗ (∃ resp, respPtr rp resp ∗ respItems cfg.γ resp ∗
              respCommitted cfg.γ resp ∗ ⌜respCovers req resp L⌝) ∨ errNE err) -∗
          Φ (PairV #rp #err)) -∗
      WP (App (Val #(methods e.ty go!"BackPropagate" e.v)) (Val #ptr)) {{ Φ }})))

/-- `svc` is the coordinator, as its rpc binding calls it (persistent). -/
def isCoordSvc (cfg : Cfg GF) (svc : GoInterface) : IProp GF :=
  iprop(∃ e : GoInterfaceOk, ⌜svc = interface.ok e⌝ ∗ □ (
    (∀ (a : GoString) (Φ : val → IProp GF), ⌜a ∈ cfg.chain⌝ -∗ joinTicket cfg.γ a -∗
      ▷ (∀ (p : Loc) (err : GoInterface),
          (⌜err = interface.nil⌝ ∗ (∃ m : MetaV, metaPtr p (DFrac.own 1) m) ∨ errNE err) -∗
          Φ (PairV #p #err)) -∗
      WP (App (Val #(methods e.ty go!"AddNode" e.v)) (Val #a)) {{ Φ }}) ∧
    (∀ (k : GoString) (sl : GoSlice) (x : GoString)
        (Q : KvM.Output → IProp GF) (Φ : val → IProp GF),
      sl ↦*□ x -∗ opAU cfg.γ (.put k x) Q -∗
      ▷ (∀ err : GoInterface, (⌜err = interface.nil⌝ ∗ putReceipt k x Q ∨ errNE err) -∗
          Φ #err) -∗
      WP (App (App (Val #(methods e.ty go!"Write" e.v)) (Val #k)) (Val #sl)) {{ Φ }}) ∧
    -- RemoveNode(a), of any address (stage 2: the client nodes' removals over net/rpc)
    (∀ (a : GoString) (Φ : val → IProp GF),
      ▷ (∀ err : GoInterface, (⌜err = interface.nil⌝ ∨ models_lab.errAny err) -∗ Φ #err) -∗
      WP (App (Val #(methods e.ty go!"RemoveNode" e.v)) (Val #a)) {{ Φ }})))

instance isNodeSvc_persistent (cfg : Cfg GF) (svc : GoInterface) (a : GoString) :
    Persistent (isNodeSvc (hG := hG) cfg svc a) := by
  unfold isNodeSvc; infer_instance
instance isCoordSvc_persistent (cfg : Cfg GF) (svc : GoInterface) :
    Persistent (isCoordSvc (hG := hG) cfg svc) := by
  unfold isCoordSvc; infer_instance

end ifaces

end github_com.despreston.go_craq

end Perennial

/-
**The model API server's predicates** (phase 3 of `notes/k8s-daemonset-plan.md`; D50's internal
layer: the specs the informers' and the controller's proofs use instead of stepping through the
model). Lean-first (no Rocq counterpart).

* `apiState γ σ`: the clients' half of the server's state `σ` (`State.lean`), with the history of
  every earlier state (a mono-list, `γ.hist`): the specs are logically atomic over it. `pastSt γ σ`
  (persistent): `σ` is one of the server's states, `St.le`-before every later one
  (`pastSt_le`); a list and a watch event carry one.
* `objAt x dq o`: the Go `runtime.Object` `x` is a pointer to an API object of the type of `o`,
  owned deeply at `dq` with deep value `o` (`Proof/k8s_io/api/Deep.lean`).
* `errIs err e`: `err` is a `*StatusError` of `e`'s reason and code (persistent).
* `isServer s γ cfg`: the server `s` with configuration `cfg`, its lock and its invariant
  (`lockInv`: the physical state, `srvLocked`, of some `σ`, the other half of the history, the
  watchers' stop flags); `podClientAt c γ cfg ns admin`, ...: a typed client of it.
* `evOk`: the `i`-th event of a watch (an SPSC channel's element predicate): an initial object,
  the next change of the log in the namespace (after changes of other namespaces), or a bookmark at
  a version through which the log has nothing more in the namespace; with the watch's cursor
  (`γw.cur`, positions `(log index, version)`) before and after.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.State
public import Proof.k8s_io.client_go.util.consistency.Defs
public import Perennial.Golang.Theory.Chan.Idioms.Spsc
public import Perennial.Proof.sync.Results

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apimodel

open Iris Iris.BI Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8sdaemonset

/-- The ghost names of a server. -/
structure ApiNames where
  /-- the history of states (a mono-list: halves in `apiState` and the lock invariant) -/
  hist : GName
  /-- the registered watchers (a ghost map: watcher to its stop channel's names) -/
  ws : GName

/-- A watch's ghost names. -/
structure WatchNames where
  /-- the result channel (SPSC: the watch's goroutine sends, the caller receives) -/
  ch : SpscNames
  /-- the cursor: the position after each event (log index, version) -/
  cur : GName

/-- A resource's `schema.GroupResource` (`NewServer`'s tables). -/
def grOf [FfiSyntax] : Res → k8s_io.apimachinery.pkg.runtime.schema.GroupResource
  | .pods => ⟨go!"", go!"pods"⟩
  | .nodes => ⟨go!"", go!"nodes"⟩
  | .daemonSets => ⟨go!"apps", go!"daemonsets"⟩
  | .revisions => ⟨go!"apps", go!"controllerrevisions"⟩

/-- An SPSC channel's ghost names as a list of numbers (the watchers' ghost map stores them; an
encoding rather than a `Pos.Countable SpscNames` instance, which another proof, the etcd cache's
`InvDemux.lean`, has for `ChanNames`). -/
def spscCode (g : SpscNames) : List Nat :=
  [g.chanName.stateName, g.chanName.offerLockName, g.chanName.offerParkedPropName,
    g.chanName.offerParkedPredName, g.chanName.offerContinuationName, g.chanName.chanCap.toNat,
    g.spscSentName, g.spscRecvName]

theorem spscCode_inj {g g' : SpscNames} (h : spscCode g = spscCode g') : g = g' := by
  obtain ⟨⟨a, b, c, d, e, f⟩, x, y⟩ := g
  obtain ⟨⟨a', b', c', d', e', f'⟩, x', y'⟩ := g'
  simp only [spscCode, List.cons.injEq, and_true] at h
  obtain ⟨rfl, rfl, rfl, rfl, rfl, hf, rfl, rfl⟩ := h
  have : f = f' := BitVec.eq_of_toNat_eq hf
  subst this
  rfl

instance watchEvent_countable [FfiSyntax] :
    Pos.Countable k8s_io.apimachinery.pkg.watch.Event :=
  .ofInjective (fun e => Pos.Countable.encode (e.Type', e.Object'))
    (by rintro ⟨a, b⟩ ⟨c, d⟩ h; simp only [Pos.encode_eq_iff, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h; rfl)

/-- **The semantics of the packages the model's code calls into** (their `Assumptions`): every
spec of the model quantifies over it, as the examples' specs over the packages they call. -/
class ApiDeps [FfiSyntax] [GoGlobalContext] [GoLocalContext] [GoSemanticsFunctions] : Prop where
  sync_sem : sync.Assumptions
  time_sem : time.Assumptions
  core_sem : k8s_io.api.core.v1.Assumptions
  apps_sem : k8s_io.api.apps.v1.Assumptions
  meta_sem : k8s_io.apimachinery.pkg.apis.«meta».v1.Assumptions
  errors_sem : k8s_io.apimachinery.pkg.api.errors.Assumptions
  schema_sem : k8s_io.apimachinery.pkg.runtime.schema.Assumptions
  types_sem : k8s_io.apimachinery.pkg.types.Assumptions

attribute [instance] ApiDeps.sync_sem ApiDeps.time_sem ApiDeps.core_sem ApiDeps.apps_sem
  ApiDeps.meta_sem ApiDeps.errors_sem ApiDeps.schema_sem ApiDeps.types_sem

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-! ## The state and its history -/

/-- **The API server's state**, the clients' half (logically atomic specs are over it). -/
def apiState (γ : ApiNames) (σ : St) : IProp GF :=
  iprop(∃ H : List St, monoListAuthOwn γ.hist (1 : Qp).half (H ++ [σ]) ∗ ⌜histOk (H ++ [σ])⌝)

/-- **A state the server was in** (persistent): well formed, and before every later one. -/
def pastSt (γ : ApiNames) (σ : St) : IProp GF :=
  iprop(∃ H : List St, monoListLbOwn γ.hist H ∗ ⌜σ ∈ H ∧ σ.wf⌝)

instance pastSt_persistent (γ : ApiNames) (σ : St) : Persistent (pastSt (GF := GF) γ σ) := by
  unfold pastSt; infer_instance

/-! ## Objects -/

/-- A pod in the heap, owned deeply at `dq`, with deep value `d`. -/
def podAt (l : Loc) (dq : DFrac) (d : kd.core.Pod) : IProp GF :=
  iprop(∃ v : k8s_io.api.core.v1.Pod, l ↦{dq} v ∗ kd.core.Pod.own v dq d)

/-- A node in the heap. -/
def nodeAt (l : Loc) (dq : DFrac) (d : kd.core.Node) : IProp GF :=
  iprop(∃ v : k8s_io.api.core.v1.Node, l ↦{dq} v ∗ kd.core.Node.own v dq d)

/-- A daemon set in the heap. -/
def dsAt (l : Loc) (dq : DFrac) (d : kd.apps.DaemonSet) : IProp GF :=
  iprop(∃ v : k8s_io.api.apps.v1.DaemonSet, l ↦{dq} v ∗ kd.apps.DaemonSet.own v dq d)

/-- A controller revision in the heap. -/
def crAt (l : Loc) (dq : DFrac) (d : kd.apps.ControllerRevision) : IProp GF :=
  iprop(∃ v : k8s_io.api.apps.v1.ControllerRevision, l ↦{dq} v ∗
    kd.apps.ControllerRevision.own v dq d)

/-- **An object** (a `runtime.Object`, the model's `object`): a pointer to an API object of
`o`'s type, owned deeply at `dq`, with deep value `o`. -/
def objAt (x : GoInterface) (dq : DFrac) : Obj → IProp GF
  | .pod d => iprop(∃ l : Loc, ⌜x = interface.mkOk (go.GoType.PointerType k8s_io.api.core.v1.Pod.ty)
      #l⌝ ∗ podAt l dq d)
  | .node d => iprop(∃ l : Loc, ⌜x = interface.mkOk
      (go.GoType.PointerType k8s_io.api.core.v1.Node.ty) #l⌝ ∗ nodeAt l dq d)
  | .ds d => iprop(∃ l : Loc, ⌜x = interface.mkOk
      (go.GoType.PointerType k8s_io.api.apps.v1.DaemonSet.ty) #l⌝ ∗ dsAt l dq d)
  | .cr d => iprop(∃ l : Loc, ⌜x = interface.mkOk
      (go.GoType.PointerType k8s_io.api.apps.v1.ControllerRevision.ty) #l⌝ ∗ crAt l dq d)

/-- A pointer to an object of `o`'s type (`*corev1.Pod`, ...) owned with `o`, as the typed
clients return (`nil` for none). -/
def objPtrAt (p : Loc) (dq : DFrac) : Obj → IProp GF
  | .pod d => podAt p dq d
  | .node d => nodeAt p dq d
  | .ds d => dsAt p dq d
  | .cr d => crAt p dq d

/-! ## Errors -/

/-- **An API error of reason `e`** (persistent): a `*StatusError` whose status has `e`'s reason
and HTTP code. -/
def errIs (err : GoInterface) (e : ApiErr) : IProp GF :=
  iprop(∃ (p : Loc) (st : k8s_io.apimachinery.pkg.apis.«meta».v1.Status),
    ⌜err = interface.mkOk (go.GoType.PointerType k8s_io.apimachinery.pkg.api.errors.StatusError.ty)
      #p⌝ ∗ p ↦□ k8s_io.apimachinery.pkg.api.errors.StatusError.mk st ∗
    ⌜st.Reason' = e.reason.1 ∧ st.Code' = e.reason.2⌝)

instance errIs_persistent (err : GoInterface) (e : ApiErr) : Persistent (errIs (GF := GF) err e) := by
  unfold errIs; infer_instance

/-- **What a write returns** for its outcome `oc` (`ok (wrote, o)`: the object stored, written
or not; `error e`: no effect): the object, or, after a write, if ambiguous writes are flagged, a
timeout; the error. `p` is the typed client's result pointer. -/
def writeRet (amb admin : Bool) (oc : Except ApiErr (Bool × Obj)) (p : Loc) (err : GoInterface) :
    IProp GF :=
  match oc with
  | .ok (w, o) => iprop((⌜err = interface.nil⌝ ∗ objPtrAt p (DFrac.own 1) o) ∨
      (⌜w = true ∧ mayHappen amb admin ∧ p = null⌝ ∗ errIs err .timeout))
  | .error e => iprop(⌜p = null⌝ ∗ errIs err e)

/-- **What a delete returns** for its outcome (`ok wrote`; `error e`: no effect). -/
def deleteRet (amb admin : Bool) (oc : Except ApiErr Bool) (err : GoInterface) : IProp GF :=
  match oc with
  | .ok w => iprop(⌜err = interface.nil⌝ ∨ (⌜w = true ∧ mayHappen amb admin⌝ ∗ errIs err .timeout))
  | .error e => errIs err e

/-! ## The server -/

/-- A table's fixed locations. -/
structure Tbl where
  /-- the `*table` -/
  t : Loc
  /-- its `objs` map -/
  objs : GoMap
  /-- its `empty` function -/
  empty : GoFunc

/-- The server's fixed locations. -/
structure SrvLocs where
  cond : Loc
  rvs : GoMap
  tp : Tbl
  tn : Tbl
  td : Tbl
  tc : Tbl

/-- A resource's table locations. -/
def SrvLocs.tbl (L : SrvLocs) : Res → Tbl
  | .pods => L.tp
  | .nodes => L.tn
  | .daemonSets => L.td
  | .revisions => L.tc

/-- The zero object of a resource (`emptyPod()`, ...). -/
def zeroObj : Res → Obj
  | .pods => .pod kd.core.Pod.zero
  | .nodes => .node kd.core.Node.zero
  | .daemonSets => .ds kd.apps.DaemonSet.zero
  | .revisions => .cr kd.apps.ControllerRevision.zero

/-- A table's `empty` function returns a new zero object of the resource. -/
def emptyOk (r : Res) (f : GoFunc) : IProp GF :=
  iprop({{ True }} (App (Val #f) (Val #())) {{ (x : GoInterface), RET #x; objAt x (DFrac.own 1) (zeroObj r) }})

instance emptyOk_persistent (r : Res) (f : GoFunc) : Persistent (emptyOk (GF := GF) r f) := by
  unfold emptyOk; infer_instance

/-- **A table's fixed fields** (persistent): its resource, namespacing, map and `empty`. -/
def tableFixed (r : Res) (T : Tbl) : IProp GF :=
  iprop(T.t.[apimodel.table, go!"resource"] ↦□ grOf r ∗
    T.t.[apimodel.table, go!"namespaced"] ↦□ r.namespaced ∗
    T.t.[apimodel.table, go!"objs"] ↦□ T.objs ∗ T.t.[apimodel.table, go!"empty"] ↦□ T.empty ∗
    emptyOk r T.empty)

instance tableFixed_persistent (r : Res) (T : Tbl) : Persistent (tableFixed (GF := GF) r T) := by
  unfold tableFixed emptyOk; infer_instance

/-- A log entry in the heap: its type, version and object. -/
def changeAt (c : apimodel.change) (e : Change) : IProp GF :=
  iprop(⌜c.typ' = e.typ.str ∧ c.rv' = e.rv⌝ ∗ objAt c.obj' (DFrac.own 1) e.obj)

/-- **A table's state in the heap** (under the server's lock): its map of the stored objects and
its log. -/
def tableLocked (T : Tbl) (tb : Table) : IProp GF :=
  iprop(∃ (M : GMap Key GoInterface) (sl : GoSlice) (cs : List apimodel.change),
    T.objs ↦$ M ∗ ([∗map] _k ↦ x;o ∈ M;tb.objs, objAt x (DFrac.own 1) o) ∗
    T.t.[apimodel.table, go!"log"] ↦ sl ∗ sl ↦* cs ∗ ownSliceCap apimodel.change sl (DFrac.own 1) ∗
    [∗list] c;e ∈ cs;tb.log, changeAt c e)

/-- The four tables' states in the heap. -/
def tablesLocked (L : SrvLocs) (σ : St) : IProp GF :=
  iprop(tableLocked L.tp σ.pods ∗ tableLocked L.tn σ.nodes ∗ tableLocked L.td σ.dss ∗
    tableLocked L.tc σ.crs)

/-- **The server's state in the heap** (under its lock): the last version issued, the issued
versions' map, the UIDs issued, the tables; one receipt per version issued since the first (which
bounds the counter, `isServer`'s `receiptBound`). -/
def srvLocked (s : Loc) (L : SrvLocs) (σ : St) : IProp GF :=
  iprop("Hrev" ∷ s.[apimodel.Server, go!"rev"] ↦ σ.rev ∗
    "Huids" ∷ s.[apimodel.Server, go!"uids"] ↦ σ.uids ∗
    "Hrvsm" ∷ L.rvs ↦$ issuedMap σ.rev.toNat ∗
    "Htbls" ∷ tablesLocked L σ ∗ "Hrc" ∷ ⧗ (σ.rev.toNat - 1) ∗
    "%Huidlt" ∷ ⌜σ.uids.toNat < σ.rev.toNat⌝)

/-- **The registered watchers' stop flags** (under the server's lock): a watcher not stopped
holds its stop channel's sending side (`Stop` closes it once). -/
def watchersLocked (γ : ApiNames) : IProp GF :=
  iprop(∃ W : GMap Loc (List Nat), ghostMapAuth γ.ws (1 : Qp) W ∗
    [∗map] w ↦ c ∈ W, ∃ (g : SpscNames) (b : Bool), ⌜spscCode g = c⌝ ∗
      w.[apimodel.watcher, go!"stopped"] ↦ b ∗
      (if b then iprop(True) else spscProducer (V := Unit) g []))

/-- **The server's lock invariant**: the heap's state of some `σ`, the history's other half
(ending at `σ`), the watchers. -/
def lockInv (s : Loc) (γ : ApiNames) (L : SrvLocs) : IProp GF :=
  iprop(∃ (σ : St) (H : List St), srvLocked s L σ ∗
    monoListAuthOwn γ.hist (1 : Qp).half (H ++ [σ]) ∗ ⌜histOk (H ++ [σ])⌝ ∗ watchersLocked γ)

/-- A `Config`'s fields (persistent; one by one, so that they load without the struct's points-to,
which `wp_load` cannot access at a fraction other than `1`). -/
def cfgAt (l : Loc) (cfg : apimodel.Config) : IProp GF :=
  iprop("#HFailWrites" ∷ l.[apimodel.Config, go!"FailWrites"] ↦□ cfg.FailWrites' ∗
    "#HAmbiguousWrites" ∷ l.[apimodel.Config, go!"AmbiguousWrites"] ↦□ cfg.AmbiguousWrites' ∗
    "#HFailReads" ∷ l.[apimodel.Config, go!"FailReads"] ↦□ cfg.FailReads' ∗
    "#HEndWatches" ∷ l.[apimodel.Config, go!"EndWatches"] ↦□ cfg.EndWatches' ∗
    "#HExpireWatches" ∷ l.[apimodel.Config, go!"ExpireWatches"] ↦□ cfg.ExpireWatches' ∗
    "#HBookmarks" ∷ l.[apimodel.Config, go!"Bookmarks"] ↦□ cfg.Bookmarks' ∗
    "#HFaultPercent" ∷ l.[apimodel.Config, go!"FaultPercent"] ↦□ cfg.FaultPercent')

/-- The `Server` field holding a resource's table. -/
def resField : Res → GoString
  | .pods => go!"pods"
  | .nodes => go!"nodes"
  | .daemonSets => go!"daemonSets"
  | .revisions => go!"revisions"

/-- `t` is the server's table of `r` (persistent). -/
def tableOf (s : Loc) (r : Res) (t : Loc) : IProp GF :=
  iprop(s.[apimodel.Server, resField r] ↦□ t)

instance tableOf_persistent (s : Loc) (r : Res) (t : Loc) : Persistent (tableOf (GF := GF) s r t) := by
  unfold tableOf; infer_instance

/-- **The model API server** `s` with failure configuration `cfg` (persistent): its fixed fields,
its tables', its lock with `lockInv` and its condition variable; the receipts' bound under which
its version counter does not wrap (`receiptBound GF ≤ 2 ^ 63`). -/
def srvFixed (s : Loc) (γ : ApiNames) (L : SrvLocs) (cfg : apimodel.Config) : IProp GF :=
  iprop("#Hchanged" ∷ s.[apimodel.Server, go!"changed"] ↦□ L.cond ∗
    "#Hcfg" ∷ cfgAt (s.[apimodel.Server, go!"cfg"]) cfg ∗
    "#Hrvs" ∷ s.[apimodel.Server, go!"rvs"] ↦□ L.rvs ∗
    "#Htp" ∷ tableOf s .pods L.tp.t ∗ "#Htn" ∷ tableOf s .nodes L.tn.t ∗
    "#Htd" ∷ tableOf s .daemonSets L.td.t ∗ "#Htc" ∷ tableOf s .revisions L.tc.t ∗
    "#Hfp" ∷ tableFixed .pods L.tp ∗ "#Hfn" ∷ tableFixed .nodes L.tn ∗
    "#Hfd" ∷ tableFixed .daemonSets L.td ∗ "#Hfc" ∷ tableFixed .revisions L.tc ∗
    "#Hmu" ∷ sync.isMutex (s.[apimodel.Server, go!"mu"]) (lockInv s γ L) ∗
    "#Hcond" ∷ sync.isCond L.cond (interface.mk (go.GoType.PointerType sync.Mutex.ty)
      #(s.[apimodel.Server, go!"mu"])) ∗
    "%Hbound" ∷ ⌜receiptBound GF ≤ 2 ^ 63⌝)

instance srvFixed_persistent (s : Loc) (γ : ApiNames) (L : SrvLocs) (cfg : apimodel.Config) :
    Persistent (srvFixed (GF := GF) s γ L cfg) := by
  unfold srvFixed tableFixed emptyOk cfgAt tableOf; infer_instance

/-- **The model API server** (persistent): `srvFixed` at its fixed locations. -/
def isServer (s : Loc) (γ : ApiNames) (cfg : apimodel.Config) : IProp GF :=
  iprop(∃ L : SrvLocs, srvFixed s γ L cfg)

instance isServer_persistent (s : Loc) (γ : ApiNames) (cfg : apimodel.Config) :
    Persistent (isServer (GF := GF) s γ cfg) := by
  unfold isServer; infer_instance

/-! ## The functions the operations take -/

/-- **A create strategy** (`preparePod`, ...): it changes the object as `prepareD` does. -/
def prepareOk (r : Res) (f : GoFunc) : IProp GF :=
  iprop(∀ (x : GoInterface) (o : Obj), ⌜o.res = r⌝ -∗
    {{ objAt x (DFrac.own 1) o }} (App (Val #f) (Val #x)) {{ RET #(); objAt x (DFrac.own 1) (prepareD o) }})

/-- **An update's mutation** (`updateDaemonSetStatus`, `replaceRevision`), of the stored object's
copy and the request's: `nil` for nothing to write, or the object to write, as `mutR` allows. -/
def mutateOk (r : Res) (mutR : Obj → Obj → Option Obj → Prop) (f : GoFunc) : IProp GF :=
  iprop(∀ (x y : GoInterface) (st req : Obj), ⌜st.res = r ∧ req.res = r⌝ -∗
    {{ objAt x (DFrac.own 1) st ∗ objAt y (DFrac.own 1) req }}
      (App (App (Val #f) (Val #x)) (Val #y))
    {{ (z : GoInterface), RET #z; (⌜z = interface.nil ∧ mutR st req none⌝) ∨
        (∃ o, ⌜mutR st req (some o) ∧ o.res = r⌝ ∗ objAt z (DFrac.own 1) o) }})

/-- **A delete's grace period** (`podGrace`, `noGrace`): `graceOf`. -/
def graceOk (r : Res) (f : GoFunc) : IProp GF :=
  iprop(∀ (x : GoInterface) (st : Obj) (opts : k8s_io.apimachinery.pkg.apis.«meta».v1.DeleteOptions)
      (dq : DFrac) (dop : kd.meta.DeleteOptions), ⌜st.res = r⌝ -∗
    {{ objAt x (DFrac.own 1) st ∗ kd.meta.DeleteOptions.own opts dq dop }}
      (App (App (Val #f) (Val #x)) (Val #opts))
    {{ RET #(graceOf r st dop.GracePeriodSeconds'); objAt x (DFrac.own 1) st ∗
        kd.meta.DeleteOptions.own opts dq dop }})

instance prepareOk_persistent (r : Res) (f : GoFunc) : Persistent (prepareOk (GF := GF) r f) := by
  unfold prepareOk; infer_instance

instance mutateOk_persistent (r : Res) (mutR : Obj → Obj → Option Obj → Prop) (f : GoFunc) :
    Persistent (mutateOk (GF := GF) r mutR f) := by
  unfold mutateOk; infer_instance

instance graceOk_persistent (r : Res) (f : GoFunc) : Persistent (graceOk (GF := GF) r f) := by
  unfold graceOk; infer_instance

/-! ## What the operations return -/

/-- **What a server write returns** (`create`, `update`: the object, an interface value): as
`writeRet`. -/
def writeRetI (amb admin : Bool) (oc : Except ApiErr (Bool × Obj)) (x err : GoInterface) : IProp GF :=
  match oc with
  | .ok (w, o) => iprop((⌜err = interface.nil⌝ ∗ objAt x (DFrac.own 1) o) ∨
      (⌜w = true ∧ mayHappen amb admin ∧ x = interface.nil⌝ ∗ errIs err .timeout))
  | .error e => iprop(⌜x = interface.nil⌝ ∗ errIs err e)

/-- **What a get returns**, `x` its result: a flagged failure (500), or the object stored at the
key (404 if none). -/
def getRet (failReads admin : Bool) (o : Option Obj) (x err : GoInterface) : IProp GF :=
  iprop((⌜mayHappen failReads admin ∧ x = interface.nil⌝ ∗ errIs err .internal) ∨
    match o with
    | none => iprop(⌜x = interface.nil⌝ ∗ errIs err .notFound)
    | some o => iprop(⌜err = interface.nil⌝ ∗ objAt x (DFrac.own 1) o))

/-- The same for a typed client (its result a pointer). -/
def getRetP (failReads admin : Bool) (o : Option Obj) (p : Loc) (err : GoInterface) : IProp GF :=
  iprop((⌜mayHappen failReads admin ∧ p = null⌝ ∗ errIs err .internal) ∨
    match o with
    | none => iprop(⌜p = null⌝ ∗ errIs err .notFound)
    | some o => iprop(⌜err = interface.nil⌝ ∗ objPtrAt p (DFrac.own 1) o))

/-- **A list's objects**: the slice `sl` of objects owned with `os`, a snapshot of the namespace
at `σ` (`listOk`), at version `rv = rvStr σ.rev`, of a state the server was in. -/
def listedAt (γ : ApiNames) (r : Res) (ns : GoString) (σ : St) (sl : GoSlice) (rv : GoString) :
    IProp GF :=
  iprop(∃ (xs : List GoInterface) (os : List Obj), sl ↦* xs ∗
    ([∗list] x;o ∈ xs;os, objAt x (DFrac.own 1) o) ∗ ⌜listOk r ns σ os ∧ rv = rvStr σ.rev⌝ ∗
    pastSt γ σ)

/-- **A typed list** (`*PodList`, ...) at `q`: its version `rv` and its items, owned deeply with
the objects `os`. -/
def typedListAt (r : Res) (q : Loc) (os : List Obj) (rv : GoString) : IProp GF :=
  match r with
  | .pods => iprop(∃ (lv : k8s_io.api.core.v1.PodList) (vs : List k8s_io.api.core.v1.Pod)
      (ds : List kd.core.Pod), q ↦ lv ∗ ⌜lv.ListMeta'.ResourceVersion' = rv ∧ os = ds.map .pod⌝ ∗
      lv.Items' ↦* vs ∗ [∗list] v;d ∈ vs;ds, kd.core.Pod.own v (DFrac.own 1) d)
  | .nodes => iprop(∃ (lv : k8s_io.api.core.v1.NodeList) (vs : List k8s_io.api.core.v1.Node)
      (ds : List kd.core.Node), q ↦ lv ∗ ⌜lv.ListMeta'.ResourceVersion' = rv ∧ os = ds.map .node⌝ ∗
      lv.Items' ↦* vs ∗ [∗list] v;d ∈ vs;ds, kd.core.Node.own v (DFrac.own 1) d)
  | .daemonSets => iprop(∃ (lv : k8s_io.api.apps.v1.DaemonSetList)
      (vs : List k8s_io.api.apps.v1.DaemonSet) (ds : List kd.apps.DaemonSet), q ↦ lv ∗
      ⌜lv.ListMeta'.ResourceVersion' = rv ∧ os = ds.map .ds⌝ ∗
      lv.Items' ↦* vs ∗ [∗list] v;d ∈ vs;ds, kd.apps.DaemonSet.own v (DFrac.own 1) d)
  | .revisions => iprop(∃ (lv : k8s_io.api.apps.v1.ControllerRevisionList)
      (vs : List k8s_io.api.apps.v1.ControllerRevision) (ds : List kd.apps.ControllerRevision),
      q ↦ lv ∗ ⌜lv.ListMeta'.ResourceVersion' = rv ∧ os = ds.map .cr⌝ ∗
      lv.Items' ↦* vs ∗ [∗list] v;d ∈ vs;ds, kd.apps.ControllerRevision.own v (DFrac.own 1) d)

/-- **What a typed list returns**: as `listRet`, the list a typed list. -/
def typedListRet (γ : ApiNames) (failReads admin : Bool) (r : Res) (ns : GoString)
    (lo : kd.meta.ListOptions) (σ : St) (q : Loc) (err : GoInterface) : IProp GF :=
  if lo.LabelSelector' ≠ go!"" ∨ lo.FieldSelector' ≠ go!"" then
    iprop(⌜q = null⌝ ∗ errIs err .badRequest)
  else iprop((⌜mayHappen failReads admin ∧ q = null⌝ ∗ errIs err .internal) ∨
    (⌜err = interface.nil⌝ ∗ ∃ os : List Obj, typedListAt r q os (rvStr σ.rev) ∗
      ⌜listOk r ns σ os⌝ ∗ pastSt γ σ))

/-- **What a list returns**: a 400 for a selector; else a flagged failure (500) or the list. -/
def listRet (γ : ApiNames) (failReads admin : Bool) (r : Res) (ns : GoString)
    (lo : kd.meta.ListOptions) (σ : St) (sl : GoSlice) (rv : GoString) (err : GoInterface) : IProp GF :=
  if lo.LabelSelector' ≠ go!"" ∨ lo.FieldSelector' ≠ go!"" then errIs err .badRequest
  else iprop((⌜mayHappen failReads admin⌝ ∗ errIs err .internal) ∨
    (⌜err = interface.nil⌝ ∗ listedAt γ r ns σ sl rv))

/-! ## The clients -/

/-- A `*Clientset` of the server (persistent). -/
def clientsetAt (c : Loc) (γ : ApiNames) (cfg : apimodel.Config) (admin : Bool) : IProp GF :=
  iprop(∃ s : Loc, c.[apimodel.Clientset, go!"s"] ↦□ s ∗ c.[apimodel.Clientset, go!"admin"] ↦□ admin ∗ isServer s γ cfg)

/-- A `*coreV1` (persistent). -/
def coreV1At (l : Loc) (γ : ApiNames) (cfg : apimodel.Config) (admin : Bool) : IProp GF :=
  iprop(∃ s : Loc, l.[apimodel.coreV1, go!"s"] ↦□ s ∗ l.[apimodel.coreV1, go!"admin"] ↦□ admin ∗ isServer s γ cfg)

/-- A `*appsV1` (persistent). -/
def appsV1At (l : Loc) (γ : ApiNames) (cfg : apimodel.Config) (admin : Bool) : IProp GF :=
  iprop(∃ s : Loc, l.[apimodel.appsV1, go!"s"] ↦□ s ∗ l.[apimodel.appsV1, go!"admin"] ↦□ admin ∗ isServer s γ cfg)

/-- `CoreV1()`'s client (an interface value, persistent). -/
def isCoreV1 (x : GoInterface) (γ : ApiNames) (cfg : apimodel.Config) (admin : Bool) : IProp GF :=
  iprop(∃ l : Loc, ⌜x = interface.mkOk (go.GoType.PointerType apimodel.coreV1.ty) #l⌝ ∗
    coreV1At l γ cfg admin)

/-- `AppsV1()`'s client. -/
def isAppsV1 (x : GoInterface) (γ : ApiNames) (cfg : apimodel.Config) (admin : Bool) : IProp GF :=
  iprop(∃ l : Loc, ⌜x = interface.mkOk (go.GoType.PointerType apimodel.appsV1.ty) #l⌝ ∗
    appsV1At l γ cfg admin)

/-- A `*podClient` of namespace `ns` (persistent). -/
def podClientAt (c : Loc) (γ : ApiNames) (cfg : apimodel.Config) (ns : GoString) (admin : Bool) :
    IProp GF :=
  iprop(∃ s : Loc, c.[apimodel.podClient, go!"s"] ↦□ s ∗ c.[apimodel.podClient, go!"ns"] ↦□ ns ∗ c.[apimodel.podClient, go!"admin"] ↦□ admin ∗ isServer s γ cfg)

/-- A `*nodeClient` (persistent). -/
def nodeClientAt (c : Loc) (γ : ApiNames) (cfg : apimodel.Config) (admin : Bool) : IProp GF :=
  iprop(∃ s : Loc, c.[apimodel.nodeClient, go!"s"] ↦□ s ∗ c.[apimodel.nodeClient, go!"admin"] ↦□ admin ∗ isServer s γ cfg)

/-- A `*daemonSetClient` of namespace `ns` (persistent). -/
def dsClientAt (c : Loc) (γ : ApiNames) (cfg : apimodel.Config) (ns : GoString) (admin : Bool) :
    IProp GF :=
  iprop(∃ s : Loc, c.[apimodel.daemonSetClient, go!"s"] ↦□ s ∗ c.[apimodel.daemonSetClient, go!"ns"] ↦□ ns ∗ c.[apimodel.daemonSetClient, go!"admin"] ↦□ admin ∗ isServer s γ cfg)

/-- A `*revisionClient` of namespace `ns` (persistent). -/
def crClientAt (c : Loc) (γ : ApiNames) (cfg : apimodel.Config) (ns : GoString) (admin : Bool) :
    IProp GF :=
  iprop(∃ s : Loc, c.[apimodel.revisionClient, go!"s"] ↦□ s ∗ c.[apimodel.revisionClient, go!"ns"] ↦□ ns ∗ c.[apimodel.revisionClient, go!"admin"] ↦□ admin ∗ isServer s γ cfg)

/-- `Pods(ns)`'s client (an interface value). -/
def isPodClient (x : GoInterface) (γ : ApiNames) (cfg : apimodel.Config) (ns : GoString)
    (admin : Bool) : IProp GF :=
  iprop(∃ c : Loc, ⌜x = interface.mkOk (go.GoType.PointerType apimodel.podClient.ty) #c⌝ ∗
    podClientAt c γ cfg ns admin)

/-- `Nodes()`'s client. -/
def isNodeClient (x : GoInterface) (γ : ApiNames) (cfg : apimodel.Config) (admin : Bool) : IProp GF :=
  iprop(∃ c : Loc, ⌜x = interface.mkOk (go.GoType.PointerType apimodel.nodeClient.ty) #c⌝ ∗
    nodeClientAt c γ cfg admin)

/-- `DaemonSets(ns)`'s client. -/
def isDSClient (x : GoInterface) (γ : ApiNames) (cfg : apimodel.Config) (ns : GoString)
    (admin : Bool) : IProp GF :=
  iprop(∃ c : Loc, ⌜x = interface.mkOk (go.GoType.PointerType apimodel.daemonSetClient.ty) #c⌝ ∗
    dsClientAt c γ cfg ns admin)

/-- `ControllerRevisions(ns)`'s client. -/
def isCRClient (x : GoInterface) (γ : ApiNames) (cfg : apimodel.Config) (ns : GoString)
    (admin : Bool) : IProp GF :=
  iprop(∃ c : Loc, ⌜x = interface.mkOk (go.GoType.PointerType apimodel.revisionClient.ty) #c⌝ ∗
    crClientAt c γ cfg ns admin)

/-- `Events(ns)`'s client (no state). -/
def isEventClient (x : GoInterface) : IProp GF :=
  iprop(∃ c : Loc, ⌜x = interface.mkOk (go.GoType.PointerType apimodel.eventClient.ty) #c⌝ ∗
    True)

/-! ## Watches -/

/-- A watch's position (`(log index, version)`): the changes before the index are delivered or of
another namespace; the version is the last delivered (or the start, or a bookmark's). -/
abbrev Pos' : Type := Nat × w64

/-- **One step of a watch's events**, from position `p` to `p'`, for the event of type `typ`:
an initial object (`i < |inits|`, the position kept), or, past the initial objects, the next
change of the log in the namespace (`k'-1`, after changes of other namespaces at `[k, k'-1)`), or a
bookmark (if bookmarks are allowed, `bm`: requested and flagged) at the version `v'` of a state whose log is `k'` long (its changes at `[k, k')` of other
namespaces): every change of the table at `k'` or later is at a version after `v'`
(`pastSt_le`). The object's deep value is `o` (a bookmark's: the resource's zero object at `v'`). -/
def evStep (r : Res) (ns : GoString) (bm : Bool) (inits : List Obj) (σ1 : St) (i : Nat) (p p' : Pos')
    (typ : GoString) (o : Obj) : Prop :=
  (i < inits.length ∧ p' = p ∧ typ = EvTy.added.str ∧ inits[i]? = some o) ∨
  (inits.length ≤ i ∧ ∃ c, (σ1.tbl r).log[p'.1 - 1]? = some c ∧ p.1 < p'.1 ∧
    (∀ j, p.1 ≤ j → j < p'.1 - 1 → ∀ d, (σ1.tbl r).log[j]? = some d → inNs ns d.obj.key = false) ∧
    inNs ns c.obj.key = true ∧ p'.2 = c.rv ∧ typ = c.typ.str ∧ o = c.obj) ∨
  (bm = true ∧ inits.length ≤ i ∧ p.1 ≤ p'.1 ∧ p'.1 = (σ1.tbl r).log.length ∧
    (∀ j, p.1 ≤ j → j < p'.1 → ∀ d, (σ1.tbl r).log[j]? = some d → inNs ns d.obj.key = false) ∧
    p'.2 = σ1.rev ∧ p.2.toNat < p'.2.toNat ∧ typ = go!"BOOKMARK" ∧
    o = (zeroObj r).modMeta (fun m => { m with ResourceVersion' := rvStr σ1.rev }))

/-- **The `i`-th event of a watch** of resource `r` in namespace `ns` (`""`: all) with initial
objects `inits`: its cursor's positions at `i` and `i + 1`, a state the server was in, the step,
and the event's object, owned. -/
def evOk (γ : ApiNames) (γw : WatchNames) (r : Res) (ns : GoString) (bm : Bool) (inits : List Obj)
    (i : Int)
    (ev : k8s_io.apimachinery.pkg.watch.Event) : IProp GF :=
  iprop(∃ (p p' : Pos') (σ1 : St) (o : Obj), monoListIdxOwn γw.cur i.toNat p ∗
    monoListIdxOwn γw.cur (i.toNat + 1) p' ∗ pastSt γ σ1 ∗
    ⌜evStep r ns bm inits σ1 i.toNat p p' ev.Type' o⌝ ∗ objAt ev.Object' (DFrac.own 1) o)

/-- **A started watch** (an interface value, persistent): the `*watcher` `w`, its result channel
(whose elements are `evOk`), registered with the server (so that `Stop` can stop it). -/
def watchAt (x : GoInterface) (γ : ApiNames) (γw : WatchNames) (r : Res) (ns : GoString)
    (bm : Bool) (inits : List Obj) : IProp GF :=
  iprop(∃ (w : Loc) (ch dch : Loc) (s : Loc) (cfg : apimodel.Config) (g : SpscNames),
    ⌜x = interface.mkOk (go.GoType.PointerType apimodel.watcher.ty) #w⌝ ∗
    w.[apimodel.watcher, go!"ch"] ↦□ ch ∗ w.[apimodel.watcher, go!"done"] ↦□ dch ∗
    w.[apimodel.watcher, go!"s"] ↦□ s ∗ isServer s γ cfg ∗
    isSpsc γw.ch ch (evOk γ γw r ns bm inits) (fun _ => iprop(True)) ∗
    isSpsc (V := Unit) g dch (fun _ _ => iprop(False)) (fun _ => iprop(True)) ∗
    w ↪[γ.ws]□ spscCode g)

instance watchAt_persistent (x : GoInterface) (γ : ApiNames) (γw : WatchNames) (r : Res)
    (ns : GoString) (bm : Bool) (inits : List Obj) :
    Persistent (watchAt (GF := GF) x γ γw r ns bm inits) := by
  unfold watchAt; infer_instance

/-- **The watch's consumer side**, after `n` events, at position `p`. -/
def watchCons (γw : WatchNames) (n : Nat) (p : Pos') : IProp GF :=
  iprop(∃ evs : List k8s_io.apimachinery.pkg.watch.Event, spscConsumer γw.ch evs ∗
    ⌜evs.length = n⌝ ∗ monoListIdxOwn γw.cur n p)

/-! ## What a watch returns -/

/-- **A started watch's start** (`lo` its options, `σ` the state it read): for the version `""`
or `"0"`, the namespace's objects as initial events and the current version; else no initial
event and the requested version, an issued one. -/
def watchStartOk (r : Res) (ns : GoString) (lo : kd.meta.ListOptions) (σ : St)
    (inits : List Obj) (n0 : w64) : Prop :=
  if lo.ResourceVersion' = go!"" ∨ lo.ResourceVersion' = go!"0" then
    n0 = σ.rev ∧ listOk r ns σ inits
  else inits = [] ∧ σ.issued lo.ResourceVersion' = some n0

/-- **What a watch returns**: a 400 for a selector or `SendInitialEvents`; else a flagged
failure (500), a 410 for a version not issued (or, if flagged, an old one), or the watch: its
handle, its consumer side at its start position, the state it started from. -/
def watchRet (γ : ApiNames) (cfg : apimodel.Config) (admin : Bool) (r : Res) (ns : GoString)
    (lo : kd.meta.ListOptions) (σ : St) (w err : GoInterface) : IProp GF :=
  if lo.LabelSelector' ≠ go!"" ∨ lo.FieldSelector' ≠ go!"" ∨ lo.SendInitialEvents'.isSome then
    iprop(⌜w = interface.nil⌝ ∗ errIs err .badRequest)
  else iprop((⌜mayHappen cfg.FailReads' admin ∧ w = interface.nil⌝ ∗ errIs err .internal) ∨
    (⌜w = interface.nil ∧ lo.ResourceVersion' ≠ go!"" ∧ lo.ResourceVersion' ≠ go!"0" ∧
      (σ.issued lo.ResourceVersion' = none ∨ ∃ n, σ.issued lo.ResourceVersion' = some n ∧
        n.toNat < σ.rev.toNat ∧ mayHappen cfg.ExpireWatches' admin)⌝ ∗ errIs err .expired) ∨
    (⌜err = interface.nil⌝ ∗ ∃ (γw : WatchNames) (inits : List Obj) (n0 : w64),
      watchAt w γ γw r ns (lo.AllowWatchBookmarks' && cfg.Bookmarks' && !admin) inits ∗
      watchCons γw 0 (logStart (σ.tbl r).log n0, n0) ∗
      pastSt γ σ ∗ ⌜watchStartOk r ns lo σ inits n0⌝))

end defs

end apimodel
end EtcdGrove
end Perennial

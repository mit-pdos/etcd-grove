/-
**The model API server's abstract state and operations** (pure; phase 3 of
`notes/k8s-daemonset-plan.md`, D50's internal layer). Lean-first (no Rocq counterpart).

The model (`examples/k8sdaemonset/apimodel`) is trusted Go code; this is the state its specs are
stated over, for the proofs above it (the informers, the controller) not to step through it.

* `St`: the last resource version issued (`rev`, `1` for the empty server), the number of UIDs
  issued (`uids`), and per resource (`Res`: pods, nodes, daemon sets, controller revisions) a
  `Table`: the stored objects by namespace and name (`objs`; deep values, `Obj`) and the log of
  every change (`log`: type, version, the object after the change, or its last state for a
  deletion). The issued versions are `issued σ s`: the numbers `1..rev`, by their decimal form.
* The operations as functions of the state and the request, in the order of the Go code's checks:
  `createApply`/`createErr` (`server.go`'s `create`, with the resources' create strategies
  `prepare`: `preparePodD`, `prepareDaemonSetD`), `updateApply`/`updateErr`, `deleteApply`/
  `deleteErr`, `listObjs`, `getObj`, and the log scan of a watch (`logAfter`).
* `St.wf`: what every state of the server satisfies (the specs give it with the state): versions
  increase along each log and do not exceed `rev`; a logged object is the table's resource and
  carries its version and an issued UID; the stored objects are the replay of the log (`replay`).
-/
module

public import Proof.k8s_io.api.Deep
public import Proof.k8s_io.client_go.util.consistency.Model
public import Proof.strconv.FormatUintDefs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apimodel

section state
variable [FfiSyntax]

/-- The resources the model serves. -/
inductive Res where
  | pods | nodes | daemonSets | revisions
deriving DecidableEq

/-- Whether a resource is namespaced (nodes are not). -/
def Res.namespaced : Res → Bool
  | .nodes => false
  | _ => true

/-- An object of one of the four API types, as its deep value. -/
inductive Obj where
  | pod (d : kd.core.Pod)
  | node (d : kd.core.Node)
  | ds (d : kd.apps.DaemonSet)
  | cr (d : kd.apps.ControllerRevision)

instance Obj.countable : Pos.Countable Obj :=
  .ofInjective (fun o => match o with
      | .pod d => Pos.Countable.encode ((0 : Nat), Pos.Countable.encode d)
      | .node d => Pos.Countable.encode ((1 : Nat), Pos.Countable.encode d)
      | .ds d => Pos.Countable.encode ((2 : Nat), Pos.Countable.encode d)
      | .cr d => Pos.Countable.encode ((3 : Nat), Pos.Countable.encode d))
    (by
      intro a b h
      cases a <;> cases b <;>
        simp only [Pos.encode_eq_iff, Prod.mk.injEq] at h <;>
        first | omega | (obtain ⟨-, h⟩ := h; rw [h]))

/-- The resource an object's type is. -/
def Obj.res : Obj → Res
  | .pod _ => .pods
  | .node _ => .nodes
  | .ds _ => .daemonSets
  | .cr _ => .revisions

/-- An object's metadata. -/
def Obj.meta : Obj → kd.meta.ObjectMeta
  | .pod d => d.ObjectMeta'
  | .node d => d.ObjectMeta'
  | .ds d => d.ObjectMeta'
  | .cr d => d.ObjectMeta'

/-- The object with its metadata replaced. -/
def Obj.setMeta (o : Obj) (m : kd.meta.ObjectMeta) : Obj :=
  match o with
  | .pod d => .pod { d with ObjectMeta' := m }
  | .node d => .node { d with ObjectMeta' := m }
  | .ds d => .ds { d with ObjectMeta' := m }
  | .cr d => .cr { d with ObjectMeta' := m }

@[simp] theorem Obj.meta_setMeta (o : Obj) (m : kd.meta.ObjectMeta) : (o.setMeta m).meta = m := by
  cases o <;> rfl

@[simp] theorem Obj.res_setMeta (o : Obj) (m : kd.meta.ObjectMeta) : (o.setMeta m).res = o.res := by
  cases o <;> rfl

/-- The object with its metadata changed by `f`. -/
def Obj.modMeta (o : Obj) (f : kd.meta.ObjectMeta → kd.meta.ObjectMeta) : Obj :=
  o.setMeta (f o.meta)

/-- A store key: namespace and name (`types.NamespacedName`; its `DecidableEq` and `Pos.Countable`
are the consistency store's, `consistency.Owner`'s, `Proof/k8s_io/client_go/util/consistency/Model.lean`). -/
abbrev Key : Type := k8s_io.apimachinery.pkg.types.NamespacedName

/-- A key from a namespace and a name. -/
abbrev mkKey (ns name : GoString) : Key := ⟨ns, name⟩

/-- An object's key. -/
def Obj.key (o : Obj) : Key := mkKey o.meta.Namespace' o.meta.Name'

/-- A change's type (`watch.EventType`). -/
inductive EvTy where
  | added | modified | deleted
deriving DecidableEq

instance EvTy.countable : Pos.Countable EvTy :=
  .ofInjective (fun e => match e with
      | .added => Pos.Countable.encode (0 : Nat)
      | .modified => Pos.Countable.encode (1 : Nat)
      | .deleted => Pos.Countable.encode (2 : Nat))
    (by intro a b h; cases a <;> cases b <;> simp_all [Pos.encode_eq_iff])

/-- A change's type as its `watch.EventType` string. -/
def EvTy.str : EvTy → GoString
  | .added => go!"ADDED"
  | .modified => go!"MODIFIED"
  | .deleted => go!"DELETED"

/-- **One entry of a resource's log**: the change's type, its resource version, and the object
after the change (for a deletion, its last state, at the deletion's version). -/
structure Change where
  typ : EvTy
  rv : w64
  obj : Obj

instance Change.countable : Pos.Countable Change :=
  .ofInjective (fun c => Pos.Countable.encode (c.typ, c.rv, c.obj))
    (by rintro ⟨a, b, c⟩ ⟨d, e, f⟩ h; simp only [Pos.encode_eq_iff, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h; rfl)

/-- **One resource's state**: its stored objects, by key, and the log of its changes. -/
structure Table where
  objs : GMap Key Obj
  log : List Change

instance Table.countable : Pos.Countable Table :=
  .ofInjective (fun t => Pos.Countable.encode (t.objs, t.log))
    (by rintro ⟨a, b⟩ ⟨c, d⟩ h; simp only [Pos.encode_eq_iff, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h; rfl)

/-- **The API server's state.** -/
structure St where
  /-- The last resource version issued (`1` for the empty server). -/
  rev : w64
  /-- The number of UIDs issued. -/
  uids : w64
  pods : Table
  nodes : Table
  dss : Table
  crs : Table

instance St.countable : Pos.Countable St :=
  .ofInjective (fun σ => Pos.Countable.encode (σ.rev, σ.uids, σ.pods, σ.nodes, σ.dss, σ.crs))
    (by rintro ⟨a, b, c, d, e, f⟩ ⟨a', b', c', d', e', f'⟩ h
        simp only [Pos.encode_eq_iff, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h; rfl)

/-- A resource's table. -/
def St.tbl (σ : St) : Res → Table
  | .pods => σ.pods
  | .nodes => σ.nodes
  | .daemonSets => σ.dss
  | .revisions => σ.crs

/-- The state with a resource's table replaced. -/
def St.setTbl (σ : St) (r : Res) (t : Table) : St :=
  match r with
  | .pods => { σ with pods := t }
  | .nodes => { σ with nodes := t }
  | .daemonSets => { σ with dss := t }
  | .revisions => { σ with crs := t }

@[simp] theorem St.tbl_setTbl (σ : St) (r : Res) (t : Table) : (σ.setTbl r t).tbl r = t := by
  cases r <;> rfl

theorem St.tbl_setTbl_ne (σ : St) (r r' : Res) (t : Table) (h : r' ≠ r) :
    (σ.setTbl r t).tbl r' = σ.tbl r' := by
  cases r <;> cases r' <;> first | rfl | exact absurd rfl h

@[simp] theorem St.rev_setTbl (σ : St) (r : Res) (t : Table) : (σ.setTbl r t).rev = σ.rev := by
  cases r <;> rfl

@[simp] theorem St.uids_setTbl (σ : St) (r : Res) (t : Table) : (σ.setTbl r t).uids = σ.uids := by
  cases r <;> rfl

/-- The empty server: at version `1`, no UIDs, no objects. -/
def St.empty : St := ⟨W64 1, W64 0, ⟨∅, []⟩, ⟨∅, []⟩, ⟨∅, []⟩, ⟨∅, []⟩⟩

/-- The map of the versions `1..n` by their decimal form (the model's `rvs`). -/
def issuedMap : Nat → GMap GoString w64
  | 0 => ∅
  | n + 1 => <[decStr (W64 (n + 1)) := W64 (n + 1)]> (issuedMap n)

/-- **The issued resource versions**: the number whose decimal form `s` is, if it is one of
`1..rev` (`decStr` is injective, `decStr_inj`). -/
def St.issued (σ : St) (s : GoString) : Option w64 := issuedMap σ.rev.toNat !! s

/-- A resource version's string form (`rvString`). -/
abbrev rvStr (n : w64) : GoString := decStr n

/-! ### Replaying a log -/

/-- One change applied to the stored objects. -/
def applyChange (M : GMap Key Obj) (c : Change) : GMap Key Obj :=
  match c.typ with
  | .deleted => GMap.delete c.obj.key M
  | _ => <[c.obj.key := c.obj]> M

/-- A table with a change applied and logged. -/
def Table.record (T : Table) (c : Change) : Table := ⟨applyChange T.objs c, T.log ++ [c]⟩

/-- **The objects a log leaves.** -/
def replay (l : List Change) : GMap Key Obj := l.foldl applyChange ∅

/-- **Well-formed states**: see the file header. -/
structure St.wf (σ : St) : Prop where
  rev_pos : 1 ≤ σ.rev.toNat
  log_sorted : ∀ r, (σ.tbl r).log.Pairwise (fun a b => a.rv.toNat < b.rv.toNat)
  log_le : ∀ r c, c ∈ (σ.tbl r).log → 2 ≤ c.rv.toNat ∧ c.rv.toNat ≤ σ.rev.toNat
  log_obj : ∀ r c, c ∈ (σ.tbl r).log → c.obj.res = r ∧ c.obj.meta.ResourceVersion' = rvStr c.rv
  objs_replay : ∀ r, (σ.tbl r).objs = replay (σ.tbl r).log
  uids_lt : σ.uids.toNat < σ.rev.toNat
  /-- every logged object's UID is one issued (`uid-<n>`, `n ≤ uids`): a create's is fresh -/
  log_uid : ∀ r c, c ∈ (σ.tbl r).log → ∃ n : w64, 1 ≤ n.toNat ∧ n.toNat ≤ σ.uids.toNat ∧
    c.obj.meta.UID' = go!"uid-" ++ rvStr n

/-! ### The order of states -/

/-- **`b` is a later state than `a`**: versions and UIDs issued do not decrease, each log
extends, and every change after `a`'s log is at a version after `a`'s. -/
def St.le (a b : St) : Prop :=
  a.rev.toNat ≤ b.rev.toNat ∧ a.uids.toNat ≤ b.uids.toNat ∧
  ∀ r, (a.tbl r).log <+: (b.tbl r).log ∧
    ∀ c ∈ (b.tbl r).log.drop (a.tbl r).log.length, a.rev.toNat < c.rv.toNat

theorem St.le_refl (a : St) : St.le a a := by
  refine ⟨Nat.le_refl _, Nat.le_refl _, fun r => ⟨List.prefix_refl _, ?_⟩⟩
  intro c hc
  simp at hc

theorem St.le_trans {a b c : St} (hab : St.le a b) (hbc : St.le b c) : St.le a c := by
  obtain ⟨h1, h2, h3⟩ := hab
  obtain ⟨h1', h2', h3'⟩ := hbc
  refine ⟨Nat.le_trans h1 h1', Nat.le_trans h2 h2', fun r => ⟨(h3 r).1.trans (h3' r).1, ?_⟩⟩
  obtain ⟨⟨tb, htb⟩, hb⟩ := h3 r
  obtain ⟨⟨tc, htc⟩, hc⟩ := h3' r
  intro x hx
  rw [← htc, ← htb, List.append_assoc, List.drop_left] at hx
  rw [← htb, List.drop_left] at hb
  rw [← htc, List.drop_left] at hc
  rcases List.mem_append.mp hx with hx | hx
  · exact hb x hx
  · have := hc x hx
    omega

/-- **A history of states**: each a well-formed state, each later than the one before. -/
def histOk (H : List St) : Prop := (∀ σ ∈ H, σ.wf) ∧ H.Pairwise St.le

/-! ### The create strategies -/

/-- The defaults the model applies to a created pod, and pod's create strategy (`preparePodD`):
`Generation` 1, `Status` `{Phase: Pending}`, and the unset defaults of the termination grace
period (30), restart policy (`Always`), DNS policy (`ClusterFirst`) and scheduler name. -/
def preparePodD (d : kd.core.Pod) : kd.core.Pod :=
  let s := d.Spec'
  { d with
    ObjectMeta' := { d.ObjectMeta' with Generation' := W64 1 }
    Status' := { kd.core.PodStatus.zero with Phase' := go!"Pending" }
    Spec' := { s with
      TerminationGracePeriodSeconds' := some (s.TerminationGracePeriodSeconds'.getD (W64 30))
      RestartPolicy' := if s.RestartPolicy' = go!"" then go!"Always" else s.RestartPolicy'
      DNSPolicy' := if s.DNSPolicy' = go!"" then go!"ClusterFirst" else s.DNSPolicy'
      SchedulerName' := if s.SchedulerName' = go!"" then go!"default-scheduler"
        else s.SchedulerName' } }

/-- The `apps/v1` annotation of the template generation. -/
def dsTemplateGenKey : GoString := go!"deprecated.daemonset.template.generation"

/-- `SetDefaults_DaemonSet` and the DaemonSet create strategy (`prepareDaemonSetD`). -/
def prepareDaemonSetD (d : kd.apps.DaemonSet) : kd.apps.DaemonSet :=
  let st0 := d.Spec'.UpdateStrategy'
  let st1 := if st0.Type' = go!"" then { st0 with Type' := go!"RollingUpdate" } else st0
  let st2 := if st1.Type' = go!"RollingUpdate" then
      let ru := st1.RollingUpdate'.getD kd.apps.RollingUpdateDaemonSet.zero
      { st1 with RollingUpdate' := some { ru with
          MaxUnavailable' := some (),  -- `intstr.FromInt32(1)` when unset (opaque: gap C5)
          MaxSurge' := some () } }     -- `intstr.FromInt32(0)` when unset
    else st1
  let ann0 := d.ObjectMeta'.Annotations'.getD ∅
  let ann := if (ann0 !! dsTemplateGenKey).getD go!"" = go!"" then
      <[dsTemplateGenKey := go!"1"]> ann0 else ann0
  { d with
    Spec' := { d.Spec' with
      UpdateStrategy' := st2
      RevisionHistoryLimit' := some (d.Spec'.RevisionHistoryLimit'.getD (W32 10)) }
    Status' := kd.apps.DaemonSetStatus.zero
    ObjectMeta' := { d.ObjectMeta' with Generation' := W64 1, Annotations' := some ann } }

/-- **A resource's create strategy** (nodes and controller revisions are stored as given). -/
def prepareD (o : Obj) : Obj :=
  match o with
  | .pod d => .pod (preparePodD d)
  | .ds d => .ds (prepareDaemonSetD d)
  | o => o

end state

/-! ### Errors -/

/-- The errors the model returns (`k8s.io/apimachinery/pkg/api/errors`), by reason. -/
inductive ApiErr where
  /-- 500 (`NewInternalError`): a flagged failure. -/
  | internal
  /-- 400 (`NewBadRequest`). -/
  | badRequest
  /-- 409 `AlreadyExists`. -/
  | alreadyExists
  /-- 404 (`NewNotFound`). -/
  | notFound
  /-- 409 `Conflict`. -/
  | conflict
  /-- 504 (`NewTimeoutError`): an ambiguous write, which may have taken effect. -/
  | timeout
  /-- 410 `Expired` (`NewResourceExpired`): a watch from a version not (or no longer) served. -/
  | expired
deriving DecidableEq

/-- The `metav1.StatusReason` and HTTP code of an error. -/
def ApiErr.reason [FfiSyntax] : ApiErr → GoString × w32
  | .internal => (go!"InternalError", W32 500)
  | .badRequest => (go!"BadRequest", W32 400)
  | .alreadyExists => (go!"AlreadyExists", W32 409)
  | .notFound => (go!"NotFound", W32 404)
  | .conflict => (go!"Conflict", W32 409)
  | .timeout => (go!"Timeout", W32 504)
  | .expired => (go!"Expired", W32 410)

section ops
variable [FfiSyntax]

/-- **A flagged nondeterministic choice may happen** (`chance(flag, admin)`): the flag is on and
the client is not an admin client. -/
def mayHappen (flag admin : Bool) : Prop := flag = true ∧ admin = false

/-! ### Create -/

/-- The object with its namespace set as `create` sets it: a namespaced object gets the request's
namespace if it has none; a non-namespaced one gets none. -/
def createNs (r : Res) (ns : GoString) (o : Obj) : Obj :=
  if r.namespaced then
    (if o.meta.Namespace' = go!"" then o.modMeta (fun m => { m with Namespace' := ns }) else o)
  else o.modMeta (fun m => { m with Namespace' := go!"" })

/-- **The error a create returns before the write, if any** (in the order of the checks, after a
flagged failure, which `CreateOut` allows apart): a namespace other than the request's, a set
resource version, neither name nor generated name (400), an existing name (409). -/
def createErr (r : Res) (ns : GoString) (o : Obj) (σ : St) : Option ApiErr :=
  let o1 := createNs r ns o
  if r.namespaced ∧ o.meta.Namespace' ≠ go!"" ∧ o.meta.Namespace' ≠ ns then some .badRequest
  else if o1.meta.ResourceVersion' ≠ go!"" then some .badRequest
  else if o1.meta.Name' = go!"" ∧ o1.meta.GenerateName' = go!"" then some .badRequest
  else
    let name := if o1.meta.Name' = go!"" then o1.meta.GenerateName' ++ rvStr (σ.rev + 1)
      else o1.meta.Name'
    if ((σ.tbl r).objs !! mkKey o1.meta.Namespace' name).isSome then some .alreadyExists
    else none

/-- **A successful create**: the stored object (name generated from `GenerateName` and the next
version, a fresh UID `uid-<n>`, the creation time `t`, the create strategy, the next version) and
the state after (the object stored, an `ADDED` change logged). -/
def createApply (r : Res) (ns : GoString) (o : Obj) (σ : St) (t : k8s_io.apimachinery.pkg.apis.«meta».v1.Time) :
    Obj × St :=
  let o1 := createNs r ns o
  let name := if o1.meta.Name' = go!"" then o1.meta.GenerateName' ++ rvStr (σ.rev + 1)
    else o1.meta.Name'
  let uid := go!"uid-" ++ rvStr (σ.uids + 1)
  let o2 := prepareD (o1.modMeta (fun m =>
    { m with
      Name' := name
      UID' := uid
      CreationTimestamp' := t }))
  let n := σ.rev + 1
  let o3 := o2.modMeta (fun m => { m with ResourceVersion' := rvStr n })
  let T := σ.tbl r
  (o3, { σ.setTbl r ⟨<[o3.key := o3]> T.objs, T.log ++ [⟨.added, n, o3⟩]⟩ with
    rev := n, uids := σ.uids + 1 })

/-- **What a create may do, at its linearization point** (`oc`: `ok (true, o)` for the write of
`o`, `error e` for no effect): a flagged failure before the write, a check's error, or the write
(`createApply` at some time `t`). (What the call returns, the written object or, if ambiguous
writes are flagged, a timeout after the write: `Defs.lean`'s `writeRet`.) -/
def CreateOut (cfgFail admin : Bool) (r : Res) (ns : GoString) (o : Obj) (σ : St)
    (oc : Except ApiErr (Bool × Obj)) (σ' : St) : Prop :=
  (mayHappen cfgFail admin ∧ oc = .error .internal ∧ σ' = σ) ∨
  (∃ e, createErr r ns o σ = some e ∧ oc = .error e ∧ σ' = σ) ∨
  (createErr r ns o σ = none ∧ ∃ t, (createApply r ns o σ t).2 = σ' ∧
    oc = .ok (true, (createApply r ns o σ t).1))

/-! ### Get and list -/

/-- `Get(name)` in namespace `ns`: the stored object, if any. -/
def getObj (r : Res) (ns name : GoString) (σ : St) : Option Obj := (σ.tbl r).objs !! mkKey ns name

/-- `List` in namespace `ns` (`""`: all): the stored objects of the namespace. -/
def inNs (ns : GoString) (k : Key) : Bool := decide (ns = go!"") || decide (k.Namespace' = ns)

/-- **A list's objects**: exactly the stored objects of the namespace, each once, in some order. -/
def listOk (r : Res) (ns : GoString) (σ : St) (os : List Obj) : Prop :=
  List.Perm os (((σ.tbl r).objs.toList.filter (fun kv => inNs ns kv.1)).map Prod.snd)

/-! ### Update -/

/-- The key an update or delete addresses: the request's namespace, `""` for nodes. -/
def reqKey (r : Res) (ns name : GoString) : Key := mkKey (if r.namespaced then ns else go!"") name

/-- **The error an update returns before the write, if any**: a namespace other than the
request's (400), no such object (404), a set resource version other than the stored one (409). -/
def updateErr (r : Res) (ns : GoString) (req : Obj) (σ : St) : Option ApiErr :=
  if r.namespaced ∧ req.meta.Namespace' ≠ go!"" ∧ req.meta.Namespace' ≠ ns then some .badRequest
  else match (σ.tbl r).objs !! reqKey r ns req.meta.Name' with
    | none => some .notFound
    | some st => if req.meta.ResourceVersion' ≠ go!"" ∧ req.meta.ResourceVersion' ≠
        st.meta.ResourceVersion' then some .conflict else none

/-- **An update's write**: the object the mutation made from the stored one, with the stored
identity (name, namespace, UID, creation time) and the next version, stored and logged as
`MODIFIED`. -/
def updateApply (r : Res) (st obj : Obj) (σ : St) : Obj × St :=
  let n := σ.rev + 1
  let o := obj.modMeta (fun m =>
    { m with
      Name' := st.meta.Name'
      Namespace' := st.meta.Namespace'
      UID' := st.meta.UID'
      CreationTimestamp' := st.meta.CreationTimestamp'
      ResourceVersion' := rvStr n })
  let T := σ.tbl r
  (o, { σ.setTbl r ⟨<[o.key := o]> T.objs, T.log ++ [⟨.modified, n, o⟩]⟩ with rev := n })

/-- **What an update may do, at its linearization point**, for a mutation relation
`mutR st req obj?` (the resource's: `none` for a write of nothing): as `CreateOut`; an update that
changes nothing returns the stored object and writes nothing (`ok (false, st)`). -/
def UpdateOut (cfgFail admin : Bool) (r : Res) (ns : GoString) (req : Obj)
    (mutR : Obj → Obj → Option Obj → Prop) (σ : St) (oc : Except ApiErr (Bool × Obj)) (σ' : St) :
    Prop :=
  (mayHappen cfgFail admin ∧ oc = .error .internal ∧ σ' = σ) ∨
  (∃ e, updateErr r ns req σ = some e ∧ oc = .error e ∧ σ' = σ) ∨
  (updateErr r ns req σ = none ∧ ∃ st, (σ.tbl r).objs !! reqKey r ns req.meta.Name' = some st ∧
    ((mutR st req none ∧ oc = .ok (false, st) ∧ σ' = σ) ∨
     (∃ obj, mutR st req (some obj) ∧ (updateApply r st obj σ).2 = σ' ∧
       oc = .ok (true, (updateApply r st obj σ).1))))

/-- The status fields `daemonSetStatusEqual` compares, but for the conditions' transition times:
the counters, the collision count and each condition's type, status, reason and message. -/
def dsStatusEqNoTimes (a b : kd.apps.DaemonSetStatus) : Prop :=
  a.CurrentNumberScheduled' = b.CurrentNumberScheduled' ∧
  a.NumberMisscheduled' = b.NumberMisscheduled' ∧
  a.DesiredNumberScheduled' = b.DesiredNumberScheduled' ∧ a.NumberReady' = b.NumberReady' ∧
  a.ObservedGeneration' = b.ObservedGeneration' ∧
  a.UpdatedNumberScheduled' = b.UpdatedNumberScheduled' ∧
  a.NumberAvailable' = b.NumberAvailable' ∧ a.NumberUnavailable' = b.NumberUnavailable' ∧
  a.CollisionCount' = b.CollisionCount' ∧ a.Conditions'.length = b.Conditions'.length ∧
  ∀ (i : Nat) (x y : kd.apps.DaemonSetCondition), a.Conditions'[i]? = some x → b.Conditions'[i]? = some y →
    x.Type' = y.Type' ∧ x.Status' = y.Status' ∧ x.Reason' = y.Reason' ∧ x.Message' = y.Message'

/-- **`UpdateStatus`'s mutation** (the status strategy, `updateDaemonSetStatus`): the stored
DaemonSet with the request's status, or nothing when the status is unchanged. Unchanged is
`daemonSetStatusEqual`, whose conditions' transition times compare by `time.Time.Equal`, which
Perennial specifies as some `bool` (`Perennial/Spec/time/Time__Equal.lean`): so a write of nothing
needs only `dsStatusEqNoTimes`, and any status may be written. -/
def dsStatusMut (st req : Obj) (res : Option Obj) : Prop :=
  match st, req with
  | .ds s, .ds q =>
    (res = none ∧ dsStatusEqNoTimes s.Status' q.Status') ∨
    res = some (.ds { s with Status' := q.Status' })
  | _, _ => False

/-- **`Update`'s mutation** (controller revisions): the request's object. -/
def replaceMut (_st req : Obj) (res : Option Obj) : Prop := res = some req

/-! ### Delete -/

/-- **The error a delete returns before the write, if any**: no such object (404), a
precondition that does not hold (409). -/
def deleteErr (r : Res) (ns name : GoString) (pre : Option kd.meta.Preconditions) (σ : St) :
    Option ApiErr :=
  match (σ.tbl r).objs !! reqKey r ns name with
  | none => some .notFound
  | some st => match pre with
    | some p => if (∃ u, p.UID' = some u ∧ u ≠ st.meta.UID') ∨
        (∃ v, p.ResourceVersion' = some v ∧ v ≠ st.meta.ResourceVersion') then some .conflict
        else none
    | none => none

/-- **A pod's graceful-deletion period** (pod's `CheckGracefulDelete`, `podGraceD`): the
options', else the pod's termination grace period, else 0; 0 for an unbound or finished pod; 1
for a negative one. -/
def podGraceD (p : kd.core.Pod) (gps : Option w64) : w64 :=
  let period := match gps with
    | some g => g
    | none => p.Spec'.TerminationGracePeriodSeconds'.getD (W64 0)
  let period := if p.Spec'.NodeName' = go!"" ∨ p.Status'.Phase' = go!"Failed" ∨
      p.Status'.Phase' = go!"Succeeded" then W64 0 else period
  if sint.Z period < 0 then W64 1 else period

/-- A resource's graceful-deletion period of a stored object (controller revisions: 0). -/
def graceOf (r : Res) (st : Obj) (gps : Option w64) : w64 :=
  match r, st with
  | .pods, .pod p => podGraceD p gps
  | _, _ => W64 0

/-- **A delete's write** (the object not already being deleted): with a positive grace period or
finalizers the object is kept, with its deletion time `t` and grace period, as `MODIFIED`;
otherwise removed, its last state at the next version logged as `DELETED`. -/
def deleteApply (r : Res) (st : Obj) (gps : Option w64) (σ : St)
    (t : k8s_io.apimachinery.pkg.apis.«meta».v1.Time) : St :=
  let n := σ.rev + 1
  let period := graceOf r st gps
  let o := st.modMeta (fun m => { m with ResourceVersion' := rvStr n })
  let T := σ.tbl r
  if 0 < sint.Z period ∨ o.meta.Finalizers' ≠ [] then
    let o' := o.modMeta (fun m =>
      { m with
        DeletionTimestamp' := some t
        DeletionGracePeriodSeconds' := some period })
    { σ.setTbl r ⟨<[o'.key := o']> T.objs, T.log ++ [⟨.modified, n, o'⟩]⟩ with rev := n }
  else
    { σ.setTbl r ⟨GMap.delete o.key T.objs, T.log ++ [⟨.deleted, n, o⟩]⟩ with rev := n }

/-- **What a delete may do, at its linearization point** (`oc`: `ok true` for a write, `ok false`
for nothing to do, `error e` for no effect): as `CreateOut`; deleting an object already being
deleted changes nothing. -/
def DeleteOut (cfgFail admin : Bool) (r : Res) (ns name : GoString)
    (opts : kd.meta.DeleteOptions) (σ : St) (oc : Except ApiErr Bool) (σ' : St) : Prop :=
  (mayHappen cfgFail admin ∧ oc = .error .internal ∧ σ' = σ) ∨
  (∃ e, deleteErr r ns name opts.Preconditions' σ = some e ∧ oc = .error e ∧ σ' = σ) ∨
  (deleteErr r ns name opts.Preconditions' σ = none ∧
    ∃ st, (σ.tbl r).objs !! reqKey r ns name = some st ∧
    ((st.meta.DeletionTimestamp'.isSome ∧ oc = .ok false ∧ σ' = σ) ∨
     (st.meta.DeletionTimestamp' = none ∧ ∃ t, deleteApply r st opts.GracePeriodSeconds' σ t = σ' ∧
       oc = .ok true)))

/-! ### Watch -/

/-- **The log index a watch from version `n` starts at**: the first change after `n` (the Go
loop's `next`; the log is sorted, `St.wf`). -/
def logStart (l : List Change) (n : w64) : Nat := (l.takeWhile (fun c => c.rv.toNat ≤ n.toNat)).length

end ops

end apimodel
end EtcdGrove
end Perennial

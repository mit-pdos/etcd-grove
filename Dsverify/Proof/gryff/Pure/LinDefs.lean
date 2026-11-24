/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Pure/LinDefs.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Linearization's definitions (stage 2, unit L; split from `Lin.lean` so that unit L's proof modules
(`GryffProof/PureL/`) can import them; the statements are in `Lin.lean`; `notes/stage2-proof.md` §L, `notes/stage2-plan.md` §1, §5).

**Setting.** A run `l = l1 ++ l2` from the initial configuration: `l1` is the real prefix (reality's
history, in its real order), `l2` a continuation to the closure (an interleaving of the predicted
traces' remainders). The Iris invariant fixes the closure once; every operation's *place* is
computed in the whole run, from the replicas' projections only (`place_congr`); the cut `k` (a
number of labels of `l1`) moves along reality.

* **Operations** (`ops`): the client request events of the run, each identified by its position
  (replica `r`, index `j` in `r`'s projection), with its creation order (`g`, its label's index in
  the run), its key `(client id, request id)` and its input (`RegInput w64`).
* **The frontier** after `k` labels (`front`): the median of the three stores' tags (Gryff's
  carstamp order, stage 1's `median3` over `Tag.toP`); its value (`frontVal`): the value of a store
  holding it.
* **Places** (`place`, `Option model.Tag`): a write's chosen tag (its coordinator's `WriteTag`); an RMW's
  execution result tag (its instance is the one its request created, where it is the first command;
  the result at the first replica, in id order, that executed it with a command; `exec_same` makes
  it the replica's choice irrelevant); a read's returned tag (the tag its coordinator returns the value
  with: its first `Read1Reply`, or the short-circuiting write's tag). `none`: not (yet) placed in the
  run: a write that never sent its `Write2`s, an RMW whose instance became a no-op (its re-proposals
  are never a batch's first command, so never executed), or that no replica executed, a read never
  replied to.
* **The order**: by place, then rank (producers before reads at the same tag), then creation order.
* **Outputs** (`opOut`): a read's returned value; `done` for writes and CASes.
* `lin l k`: the operations created within the first `k` labels whose place is at most the frontier
  after `k` labels, sorted.
-/
module

public import Dsverify.Proof.gryff.Pure.Run
public import Dsverify.Proof.gryff.Pure.Agree
public import Dsverify.Proof.gryff.Proto.Model
public import Dsverify.Proof.gryff.Lab.ModelsCas

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pure

open model kahn proto dsverify_lab.harness

/-! ## Operations -/

/-- A client request's key and input: `(client id, request id, input)`. -/
def _root_.Perennial.gryff.model.Ev.clientReq : Ev → Option (w32 × w32 × RegInput w64)
  | .read rid cid _ _ => some (cid, rid, .read)
  | .write rid cid _ v _ => some (cid, rid, .write v)
  | .rmw rid cid _ _ oldV newV => some (cid, rid, .cas oldV newV)
  | _ => none

/-- A client operation of a run. -/
structure Op where
  /-- its creation: the index of its request's label in the run -/
  g : Nat
  /-- its coordinator -/
  r : Fin 3
  /-- its request's index in the coordinator's projection -/
  j : Nat
  cid : w32
  rid : w32
  inp : RegInput w64

/-- The client operations of a run, in creation order. -/
noncomputable def ops (l : List Label) : List Op :=
  (List.range l.length).filterMap fun g =>
    match l[g]? with
    | some (r, e) => e.clientReq.map fun x =>
        { g, r, j := (projR (l.take g) r).length, cid := x.1, rid := x.2.1, inp := x.2.2 }
    | none => none

/-- The coordinators' map key of an operation (`ShiftInts(RequestId, ClientId)`). -/
def Op.key (o : Op) : w64 := shiftInts o.rid o.cid

/-- `rank`: producers (writes, CASes) before reads at the same place. -/
def Op.rank (o : Op) : Nat :=
  match o.inp with
  | .read => 1
  | _ => 0

/-! ## Replies -/

def _root_.Perennial.gryff.model.Ext.key : Ext → w32 × w32
  | .readReply cid rid _ _ => (cid, rid)
  | .writeReply cid rid _ => (cid, rid)
  | .rmwReply cid rid _ => (cid, rid)

/-- A reply's output. -/
def _root_.Perennial.gryff.model.Ext.out : Ext → RegOutput w64
  | .readReply _ _ v _ => .value v
  | _ => .done

/-- A reply's kind is the input's. -/
def _root_.Perennial.gryff.model.Ext.fits : Ext → RegInput w64 → Prop
  | .readReply .., .read => True
  | .writeReply .., .write _ => True
  | .rmwReply .., .cas _ _ => True
  | _, _ => False

/-- Label `n` of `l` replies to operation `o`: after `o`'s creation, at `o`'s coordinator, a reply
with `o`'s key. -/
def RepliesTo (l : List Label) (n : Nat) (o : Op) : Prop :=
  o.g < n ∧ (l[n]?).map Prod.fst = some o.r ∧ ∃ x ∈ extsAt l n, x.key = (o.cid, o.rid)

/-! ## Places -/

/-- A tag as stage 1's `PTag` (signed fields: `Tag.cmp`'s order is `tagLt`). -/
def _root_.Perennial.gryff.model.Tag.toP (t : model.Tag) : PTag := (sint.Z t.ts, sint.Z t.cid, sint.Z t.rmwc)

/-- The first `some` of `f j` for `a ≤ j < n`. -/
def firstFrom {α : Type} (a n : Nat) (f : Nat → Option α) : Option α :=
  ((List.range n).filter (a ≤ ·)).findSome? f

/-- A write's place: the `WriteTag` its coordinator chooses (the first state after its request where
its record has one). -/
noncomputable def writePlace (l : List Label) (o : Op) : Option model.Tag :=
  let es := projR l o.r
  firstFrom o.j es.length fun j' =>
    ((stOf o.r (es.take (j' + 1))).wops.get? o.key).bind WriteOp.writeTag

/-- An RMW's instance: the coordinator's next instance number on its own row when the request is
handled (`handlePropose`), where the request's proposal is the batch's first. -/
noncomputable def rmwInst (l : List Label) (o : Op) : w32 × w32 :=
  (rid32 o.r, (stOf o.r ((projR l o.r).take o.j)).crt (rid32 o.r))

/-- The result tag of replica `r`'s first execution, with a command, of instance `x` in `es`. -/
noncomputable def execTag (r : Fin 3) (es : List Ev) (x : w32 × w32) : Option model.Tag :=
  (List.range es.length).findSome? fun j =>
    match es[j]? with
    | some (Ev.exec q i) => if (q, i) = x then (execRes (outsOf r es j)).map ValTag.t else none
    | _ => none

/-- An RMW's place: its instance's execution result tag at the first replica (in id order) that
executed it with a command. -/
noncomputable def rmwPlace (l : List Label) (o : Op) : Option model.Tag :=
  (List.finRange 3).findSome? fun r => execTag r (projR l r) (rmwInst l o)

/-- The tag a coordinator's step (from state `s`, on event `e`) returns a read's value with, the
read's record key being `rkey`: a `Read1Reply` determines it (the new maximum) unless already
determined; a `Read2Reply` returns the determined one; a short-circuiting write's reply returns the
write's (`Write1Reply`: its maximum; `Write2Reply`: its `WriteTag`). -/
def readTag (s : RState) (rkey : w64) : Ev → Option model.Tag
  | .msg (.read1Reply m) => (s.rops.get? rkey).bind fun rd =>
      if rd.determinedReadVal then rd.readValTag.map ValTag.t
      else some (match rd.maxValTag with
        | none => m.vt.t
        | some mx => if m.vt.t.gt mx.t then m.vt.t else mx.t)
  | .msg (.read2Reply _) => ((s.rops.get? rkey).bind ReadOp.readValTag).map ValTag.t
  | .msg (.write1Reply m) => (s.wops.get? (shiftInts m.requestId m.clientId)).map fun w =>
      if m.vt.t.gt w.maxValTag.t then m.vt.t else w.maxValTag.t
  | .msg (.write2Reply m) => (s.wops.get? (shiftInts m.requestId m.clientId)).bind WriteOp.writeTag
  | _ => none

/-- A read's reply: the index (in its coordinator's projection) of the first event after its request
that replies to its key, with the value returned. -/
noncomputable def readReply (l : List Label) (o : Op) : Option (Nat × w64) :=
  let es := projR l o.r
  firstFrom (o.j + 1) es.length fun j' =>
    (extsIn (outsOf o.r es j')).findSome? fun x => match x with
      | .readReply cid rid v _ => if (cid, rid) = (o.cid, o.rid) then some (j', v) else none
      | _ => none

/-- A read's place: the tag its value is returned with. -/
noncomputable def readPlace (l : List Label) (o : Op) : Option model.Tag :=
  let es := projR l o.r
  (readReply l o).bind fun (j', _) =>
    match es[j']? with
    | some e => readTag (stOf o.r (es.take j')) o.key e
    | none => none

/-- An operation's place in the run. -/
noncomputable def place (l : List Label) (o : Op) : Option model.Tag :=
  match o.inp with
  | .read => readPlace l o
  | .write _ => writePlace l o
  | .cas _ _ => rmwPlace l o

/-- An operation's output in the run: a read's returned value (0 if never replied: such a read
has no place, so is in no `lin`), `done` otherwise. -/
noncomputable def opOut (l : List Label) (o : Op) : RegOutput w64 :=
  match o.inp with
  | .read => .value (((readReply l o).map Prod.snd).getD 0)
  | _ => .done

/-! ## The frontier and the linearization -/

/-- The frontier after the first `k` labels: the median of the three stores' tags. -/
noncomputable def front (l : List Label) (k : Nat) : PTag :=
  median3 (cutSt l k 0).tag.toP (cutSt l k 1).tag.toP (cutSt l k 2).tag.toP

/-- The frontier's value: the value of a store whose tag is the frontier. -/
noncomputable def frontVal (l : List Label) (k : Nat) : w64 :=
  if (cutSt l k 0).tag.toP = front l k then (cutSt l k 0).val
  else if (cutSt l k 1).tag.toP = front l k then (cutSt l k 1).val
  else (cutSt l k 2).val

/-- `o`'s place is at most `f`. -/
noncomputable def placeLe (l : List Label) (o : Op) (f : PTag) : Bool :=
  match place l o with
  | some t => decide (tagLe t.toP f)
  | none => false

/-- The order of `lin`: by place, then rank, then creation (a total order on placed operations). -/
noncomputable def opLe (l : List Label) (a b : Op) : Bool :=
  let ta := ((place l a).map model.Tag.toP).getD proto.tag0
  let tb := ((place l b).map model.Tag.toP).getD proto.tag0
  decide (tagLt ta tb) ||
    (decide (ta = tb) && (decide (a.rank < b.rank) || (decide (a.rank = b.rank) && decide (a.g ≤ b.g))))

/-- **The linearization at cut `k`**: the operations created within the first `k` labels whose place
is at most the frontier after `k` labels, sorted by (place, rank, creation). -/
noncomputable def lin (l : List Label) (k : Nat) : List Op :=
  ((ops l).filter fun o => decide (o.g < k) && placeLe l o (front l k)).mergeSort (opLe l)

/-- Replaying inputs from `s` with the register's step gives each recorded output and ends at
`s'` (stage 1's `replayOk`). -/
def replayOk : w64 → List (RegInput w64 × RegOutput w64) → w64 → Prop
  | s, [], s' => s' = s
  | s, (i, o) :: l, s' => (casApply s i).2 = o ∧ replayOk (casApply s i).1 l s'

/-! ## Well-behaved clients -/

/-- **Well-behaved clients within `l1`**: client requests' keys are unique; two requests with the
same client id are handled at the same replica, the later one after a reply to the earlier one
(so an earlier one never replied to has no later one). -/
def WB (l1 : List Label) : Prop :=
  (∀ o ∈ ops l1, ∀ o' ∈ ops l1, o.cid = o'.cid → o.rid = o'.rid → o.g = o'.g) ∧
  (∀ o ∈ ops l1, ∀ o' ∈ ops l1, o.cid = o'.cid → o.g < o'.g →
    o.r = o'.r ∧ ∃ n, n < o'.g ∧ RepliesTo l1 n o)

end Perennial.gryff.pure

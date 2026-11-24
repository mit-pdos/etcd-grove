/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/jsoncodec/Enc.lean (lab master 915f964;
notes/dsv-vr.md).
-/
/-
The kit's JSON encodings, pure: a small JSON syntax tree `JV` (numbers, strings, objects,
arrays: what the kit's codec writes for go-vsr's types), its compact serialization `ser`
(the generated encoders' bytes), and the trees of the events, payloads and logs
(`evJV`, `payJV`, `logsJV`). `VsrWire.encEvent`, `events.encPayload` and `log.encLogs` are
these (VsrProof/Wire/Basic.lean, Spec/events.lean, Spec/log.lean).
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Model.Basic
public import Net.Proof.models_lab.jsoncodec.Scan.Lits

@[expose] public section

namespace VsrJson

open JsonScan

open Perennial VsrModel

/-- Byte constants. -/
abbrev cQ : w8 := 34#8      -- "
abbrev cColon : w8 := 58#8  -- :
abbrev cComma : w8 := 44#8  -- ,
abbrev cLB : w8 := 123#8    -- {
abbrev cRB : w8 := 125#8    -- }
abbrev cLS : w8 := 91#8     -- [
abbrev cRS : w8 := 93#8     -- ]

mutual
/-- A JSON value as the kit's codec writes it. -/
inductive JV where
  | num : Nat → JV
  | str : List w8 → JV
  | obj : JMs → JV
  | arr : JVs → JV
/-- An object's members. -/
inductive JMs where
  | nil : JMs
  | cons : List w8 → JV → JMs → JMs
/-- An array's elements. -/
inductive JVs where
  | nil : JVs
  | cons : JV → JVs → JVs
end

mutual
/-- The compact serialization. -/
def ser : JV → List w8
  | .num n => decN n
  | .str s => cQ :: s ++ [cQ]
  | .obj ms => cLB :: serMs ms ++ [cRB]
  | .arr vs => cLS :: serVs vs ++ [cRS]
/-- The members, separated by commas. -/
def serMs : JMs → List w8
  | .nil => []
  | .cons k v ms => (cQ :: k ++ [cQ, cColon]) ++ ser v ++ serMsT ms
/-- The members after the first (each after a comma). -/
def serMsT : JMs → List w8
  | .nil => []
  | .cons k v ms => cComma :: ((cQ :: k ++ [cQ, cColon]) ++ ser v ++ serMsT ms)
/-- The elements, separated by commas. -/
def serVs : JVs → List w8
  | .nil => []
  | .cons v vs => ser v ++ serVsT vs
/-- The elements after the first (each after a comma). -/
def serVsT : JVs → List w8
  | .nil => []
  | .cons v vs => cComma :: (ser v ++ serVsT vs)
end

mutual
/-- Every string (and key) of the value is plain. -/
def JV.ok : JV → Prop
  | .num _ => True
  | .str s => ∀ c ∈ s, okB c
  | .obj ms => JMs.ok ms
  | .arr vs => JVs.ok vs
def JMs.ok : JMs → Prop
  | .nil => True
  | .cons k v ms => (∀ c ∈ k, okB c) ∧ JV.ok v ∧ JMs.ok ms
def JVs.ok : JVs → Prop
  | .nil => True
  | .cons v vs => JV.ok v ∧ JVs.ok vs
end

mutual
/-- The nesting depth (containers). -/
def JV.depth : JV → Nat
  | .num _ => 0
  | .str _ => 0
  | .obj ms => JMs.depth ms + 1
  | .arr vs => JVs.depth vs + 1
def JMs.depth : JMs → Nat
  | .nil => 0
  | .cons _ v ms => max (JV.depth v) (JMs.depth ms)
def JVs.depth : JVs → Nat
  | .nil => 0
  | .cons v vs => max (JV.depth v) (JVs.depth vs)
end

/-- An object from a list of members. -/
def mkObj : List (List w8 × JV) → JMs
  | [] => .nil
  | (k, v) :: ms => .cons k v (mkObj ms)

/-- An array from a list of elements. -/
def mkArr : List JV → JVs
  | [] => .nil
  | v :: vs => .cons v (mkArr vs)

/-- A `,string` number field. -/
def qn (n : Nat) : JV := .str (decN n)

/-- A `log.Log`. -/
def logJV (e : Entry) : JV :=
  .obj (mkObj [(go!"data", .str e.op), (go!"client_id", qn e.cid), (go!"request_id", qn e.req)])

/-- A `[]log.Log` (non-nil). -/
def logsJV (es : List Entry) : JV := .arr (mkArr (es.map logJV))

/-- An `events.Request`. -/
def reqJV (id cid : Nat) (op : List w8) : JV :=
  .obj (mkObj [(go!"id", qn id), (go!"client_id", qn cid), (go!"op", .str op)])

/-- The payload of a message (`events.<T>` of its type). -/
def payJV : Msg → JV
  | .request id cid op => reqJV id cid op
  | .reply id cid v res => .obj (mkObj [(go!"id", qn id), (go!"client_id", qn cid),
      (go!"view_num", qn v), (go!"result", .str res)])
  | .prepare v k c e rid => .obj (mkObj [(go!"view_num", qn v), (go!"op_num", qn k),
      (go!"commit_num", qn c), (go!"request", reqJV e.req e.cid e.op), (go!"replica_id", qn rid)])
  | .prepareOK v k rid => .obj (mkObj [(go!"view_num", qn v), (go!"op_num", qn k),
      (go!"replica_id", qn rid)])
  | .commit v c rid => .obj (mkObj [(go!"view_num", qn v), (go!"commit_num", qn c),
      (go!"replica_id", qn rid)])
  | .startViewChange v rid => .obj (mkObj [(go!"view_num", qn v), (go!"replica_id", qn rid)])
  | .doViewChange d => .obj (mkObj [(go!"view_num", qn d.view), (go!"logs", logsJV d.log),
      (go!"last_stable_view_num", qn d.lnv), (go!"op_num", qn d.log.length),
      (go!"commit_num", qn d.commit), (go!"replica_id", qn d.rid)])
  | .startView v k c logs rid => .obj (mkObj [(go!"view_num", qn v), (go!"op_num", qn k),
      (go!"commit_num", qn c), (go!"logs", logsJV logs), (go!"replica_id", qn rid)])
  | .getState v k rid => .obj (mkObj [(go!"view_num", qn v), (go!"op_num", qn k),
      (go!"replica_id", qn rid)])
  | .newState v logs c k rid => .obj (mkObj [(go!"view_num", qn v), (go!"logs", logsJV logs),
      (go!"commit_num", qn c), (go!"op_num", qn k), (go!"replica_id", qn rid)])
  | .heartbeat => .obj .nil

/-- The event type number of a message (`events.typeOf`). -/
def typeN : Msg → Nat
  | .request .. => 1
  | .reply .. => 2
  | .prepare .. => 3
  | .prepareOK .. => 4
  | .commit .. => 5
  | .startViewChange .. => 6
  | .doViewChange .. => 7
  | .startView .. => 8
  | .getState .. => 9
  | .newState .. => 10
  | .heartbeat => 11

/-- An event: its type and payload. -/
def evJV (m : Msg) : JV := .obj (mkObj [(go!"@type", .num (typeN m)), (go!"data", payJV m)])

open Classical in
/-- The encoding of message `m`'s event (`VsrWire.encEvent`): for a message with plain strings,
the codec's bytes; any other message is never sent (`ToWriter` needs `PlainMsg`), and its
"encoding" is a byte that starts no JSON value (so that encodings frame uniquely). -/
noncomputable def encEvent (m : Msg) : List w8 := if PlainMsg m then ser (evJV m) else [255#8]

/-- A payload's encoding (`events.encPayload`). -/
def encPayload (m : Msg) : List w8 := ser (payJV m)

/-- A `[]log.Log`'s encoding (`log.encLogs`). -/
def encLogs (es : List Entry) : List w8 := ser (logsJV es)

end VsrJson

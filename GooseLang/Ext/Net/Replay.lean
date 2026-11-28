/-
The Lean certification of the TCP conformance checker's verdicts
(`examples/net/conform/check/README.md`, "Certification in Lean"; `notes/net-tcp-v3-plan.md`,
E10). The checker (Python) decides whether some execution of the net extension's semantics
(`Impl.lean`) produces a recorded run, and for an ADMITTED run writes a **witness**: that execution,
as a list of steps (the extension's operation, its arguments, its result, and its hidden choices:
the connection a `Dial` makes, a listener's id, a `Read`'s cut), each linked to the traced call it is a step of. `net-replay WITNESS CALLS` (this file's
`main`, `lake exe net-replay`) checks the witness against `Impl.lean`'s definitions themselves,
not against the checker's transcription of them (`model.py`), and against the run's calls (the
tracer's records, as `conform_check.py check --calls-out` writes them, unmapped):

* (a) (until v3.4, 2026-11-20: the plan is well formed; the network has no plan now, and each
  `Listen` and `Dial` checks its address's validity, `listenOk`, `addrOk`, in (b));
* (b) from the initial state (no connection, each node with no listener),
  each step is a step of the model, decided by `Decide.lean`'s deciders on the state the replay
  threads (connections, pending ones and D16's abandoned ones included; listeners per node, which a
  `Crash` step clears): `step`, `replay`, `checkSteps`;
* (c) every traced call is linearized: each call that returned has its steps in the witness (a
  `Write` the steps of net.lean's loop, `model.writeLoop`: their bytes the call's from the count
  written so far, their counts adding up to the traced count, the last the one that ends the loop,
  with the traced error's kind), each step inside its call's interval `[B.t, E.t]`, the steps in `t`
  order, each a step of its process's node while that process is the node's current incarnation
  (crashes between incarnations, after the old one's last record, by the new one's start); a call
  cut short by its process's end may have steps or not;
* (d) each step's result is the traced one, by the mapping of `mapping.py` (here in Lean, over the
  raw error facts: `errKind`, `expect`): bytes read, counts, error kinds, EOF, the sockets the
  `Dial`s, `Accept`s and `Listen`s made (each later operation on a socket is a step on the end, or
  listener, the step that made it returned); every call is in the model's scope.

It prints CERTIFIED, or NOT CERTIFIED with the first failing step (or a call) and why.

**What is proved.** `checkSteps_sound`: if `checkSteps` (part (b), what `main` runs) accepts, the
steps are an execution (`Exec`) of the extension's
step relation (`net_semantics.step`, that is `NetStep`, at each node's local state; or
`net_semantics.crash`) from the initial state, each step's event the operation, argument and result
it gives (`WOp.toEv`; each an outcome rule, `IsNetStep`, never a stutter: a call that waits leaves
no witness step for its stutters, D22). It rests on the deciders' `↔` lemmas (`Decide.lean`) and on the replay's state
standing for the model's (`World.global`, `World.loc`: association lists for `GMap`s). **What is
checked but not proved**: parts (c) and (d), `checkCalls`, a direct program over the witness and the
calls whose correctness is by reading (it states what it checks, step by step). **What stays
trusted**: the tracer (the records are what Go's `net` did, `[B.t, E.t]` contains the call, one
clock), `conform_check.py`'s `calls_json` (it copies the records verbatim), the mapping's rules
(`errKind`, `expect`: a transcription of how net.lean builds Go's values, read backwards; and that a
`SetDeadline`'s time is zero iff the trace's `set` is false: the step's `(wall, ext)` stand for the
time's words), the identification of a node's processes as its incarnations (by name, and by the
drivers' exit events), and Lean's compiler, runtime and `Lean.Json`. The checker itself (its search,
its lazy model, `model.py`) is not trusted: a wrong witness is NOT CERTIFIED.
-/
module

public import GooseLang.Ext.Net.Decide
public import Lean.Data.Json

@[expose] public section

namespace Perennial

namespace Net

namespace Replay

/-! ## Association lists, and the maps they stand for -/

/-- `l` with the key `k` bound to `v` (its other bindings of `k` removed). -/
def alSet {K V : Type} [DecidableEq K] (l : List (K × V)) (k : K) (v : V) : List (K × V) :=
  (k, v) :: l.filter (fun x => !decide (x.1 = k))

theorem alGet_filter_ne {K V : Type} [DecidableEq K] (l : List (K × V)) (k a : K) :
    alGet (l.filter (fun x => !decide (x.1 = k))) a = if k = a then none else alGet l a := by
  induction l with
  | nil => simp
  | cons x l ih =>
    obtain ⟨k', v'⟩ := x
    by_cases h1 : k' = k
    · subst h1
      simp only [List.filter_cons, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, ih,
        alGet_cons]
      by_cases h2 : k' = a <;> simp [h2]
    · simp only [List.filter_cons, h1, decide_false, Bool.not_false, ite_true, alGet_cons, ih]
      by_cases h2 : k' = a
      · subst h2; simp [Ne.symm h1]
      · simp [h2]

theorem alGet_alSet {K V : Type} [DecidableEq K] (l : List (K × V)) (k : K) (v : V) (a : K) :
    alGet (alSet l k v) a = if k = a then some v else alGet l a := by
  unfold alSet; rw [alGet_cons, alGet_filter_ne]
  by_cases h : k = a <;> simp [h]

theorem ofList_alSet {K V : Type} [DecidableEq K] (l : List (K × V)) (k : K) (v : V) :
    GMap.ofList (alSet l k v) = GMap.insert k v (GMap.ofList l) := by
  apply GMap.ext; intro a
  rw [ofList_lookup, alGet_alSet, GMap.lookup_insert_eq_iff, ofList_lookup]

theorem alGet_mem {K V : Type} [DecidableEq K] {l : List (K × V)} {a : K} {v : V}
    (h : alGet l a = some v) : (a, v) ∈ l := by
  unfold alGet at h
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp h
  have hm := List.mem_of_find?_eq_some hx
  have hp := List.find?_some hx
  simp only [decide_eq_true_eq] at hp
  rw [← hp]; exact hm

/-! ## The replay's state

The model's state (`NetGlobal`, and a `NetLocal` per node) is in `GMap`s, which do not compute;
the replay keeps association lists and stands for the state they map to (`World.global`,
`World.loc`). -/

/-- A node's local state, its listeners as an association list. -/
structure CLocal where
  lis : List (w64 × (GoString × Bool))

/-- The node's `NetLocal`. -/
def CLocal.abs (L : CLocal) : NetLocal := ⟨GMap.ofList L.lis⟩

/-- The replay's state: the connections and the nodes' local states, as association lists. -/
structure World where
  conns : List (Nat × NetConn)
  locs : List (String × CLocal)

/-- The network it stands for. -/
def World.global (w : World) : NetGlobal := ⟨GMap.ofList w.conns⟩

/-- The local state of the node named `n`, if there is one. -/
def World.loc (w : World) (n : String) : Option NetLocal := (alGet w.locs n).map CLocal.abs

def World.setConn (w : World) (c : Nat) (cn : NetConn) : World :=
  { w with conns := alSet w.conns c cn }

def World.setLoc (w : World) (n : String) (L : CLocal) : World :=
  { w with locs := alSet w.locs n L }

theorem World.global_setConn (w : World) (c : Nat) (cn : NetConn) :
    (w.setConn c cn).global = w.global.setConn c cn := by
  simp only [World.global, World.setConn, NetGlobal.setConn, ofList_alSet]

theorem World.loc_setLoc (w : World) (n m : String) (L : CLocal) :
    (w.setLoc n L).loc m = if n = m then some L.abs else w.loc m := by
  simp only [World.loc, World.setLoc, alGet_alSet]
  split <;> simp

/-- The initial state of a run: no connection, each node with no listener. -/
def World.init (nodes : List String) : World :=
  ⟨[], nodes.map (fun n => (n, ⟨[]⟩))⟩

/-! ## Executions of the model -/

section exec
variable [GooseExts] [GoGlobalContext]

/-- An event of an execution: a step of the extension by the node named `node` (the operation,
its argument, and the expression it steps to), or that node's crash. -/
inductive Ev where
  | step (node : String) (op : String) (v : val) (e' : Expr)
  | crash (node : String)

/-- One event of the model on the network `g` and the nodes' local states `loc`: the TCP
extension's step (`net_semantics.step`, `NetStep`) at the node's local state, for every heap (it
reads none), or its crash (`net_semantics.crash`); the other nodes' states unchanged. -/
inductive MStep : NetGlobal → (String → Option NetLocal) → Ev → NetGlobal →
    (String → Option NetLocal) → Prop
  | step {g loc n op v e' L L' g' loc'} :
      loc n = some L →
      (∀ tf h, ExtSemantics.step (E := netExt) tf op v h L g e' h L' g') →
      loc' n = some L' → (∀ m, m ≠ n → loc' m = loc m) →
      MStep g loc (.step n op v e') g' loc'
  | crash {g loc n L L' loc'} :
      loc n = some L → ExtSemantics.crash (E := netExt) L L' →
      loc' n = some L' → (∀ m, m ≠ n → loc' m = loc m) →
      MStep g loc (.crash n) g loc'

/-- An execution: the events in order, each a step of the model from the state the earlier ones
reached. -/
inductive Exec : NetGlobal → (String → Option NetLocal) → List Ev → NetGlobal →
    (String → Option NetLocal) → Prop
  | nil {g loc} : Exec g loc [] g loc
  | cons {g loc e es g' loc' g'' loc''} :
      MStep g loc e g' loc' → Exec g' loc' es g'' loc'' → Exec g loc (e :: es) g'' loc''

end exec

/-! ## Witness steps -/

/-- A 64-bit word of a witness's number. -/
abbrev bv (n : Nat) : w64 := BitVec.ofNat 64 n

/-- The value of a hex digit (an ASCII byte). -/
def hexVal (c : UInt8) : Option Nat :=
  if 48 ≤ c ∧ c ≤ 57 then some (c.toNat - 48)
  else if 97 ≤ c ∧ c ≤ 102 then some (c.toNat - 87)
  else if 65 ≤ c ∧ c ≤ 70 then some (c.toNat - 55)
  else none

/-- The bytes `0..i` of the hex `b`, before `acc`. -/
def hexAux (b : ByteArray) : Nat → List w8 → Option (List w8)
  | 0, acc => some acc
  | i + 1, acc =>
    match hexVal b[2 * i]!, hexVal b[2 * i + 1]! with
    | some h, some l => hexAux b i (BitVec.ofNat 8 (16 * h + l) :: acc)
    | _, _ => none

/-- The bytes of a hex string. -/
def hexDecode (s : String) : Option (List w8) :=
  let b := s.toUTF8
  if b.size % 2 = 0 then hexAux b (b.size / 2) [] else none

/-- The bytes of a hex string (none if it is not one: the replay checks it is). -/
def hexBytes (s : String) : List w8 := (hexDecode s).getD []

/-- The failure of a result code (`errCode`'s inverse): `0` none. -/
def errOf : Nat → Option NetErr
  | 0 => none
  | 1 => some .closed
  | 2 => some .timeout
  | _ => some .sys

/-- A read's result, of its code (`0` bytes, `4` EOF, else a failure) and bytes. -/
def readResOf (code : Nat) (bs : List w8) : ReadRes :=
  match code with
  | 0 => .bytes bs
  | 4 => .eof
  | c => .err ((errOf c).getD .sys)

/-- The operation of a witness step, with its arguments and result (README, "The witness"):
numbers as the witness gives them, `side` `true` for the acceptor's end, hex strings for bytes. -/
inductive WOp where
  | listen (a : GoString) (code lis : Nat)
  | accept (lis code conn endv : Nat)
  | lisClose (lis code : Nat)
  /-- `conn`: the connection made (on success), or left (D16, on failure). -/
  | dial (a : GoString) (code : Nat) (conn : Option Nat) (endv : Nat)
  | read (conn : Nat) (side : Bool) (endv n code : Nat) (data : String) (keep : Option Nat)
  /-- `first`: the step is its `Write`'s first (D25: it takes the end's write lock). -/
  | write (conn : Nat) (side : Bool) (endv : Nat) (data : String) (k code : Nat) (first : Bool)
  | close (conn : Nat) (side : Bool) (endv code : Nat)
  | closeWrite (conn : Nat) (side : Bool) (endv code : Nat)
  | setDeadline (conn : Nat) (side : Bool) (endv kind wall ext code : Nat)
  | crash

section ev
variable [GooseExts] [GoGlobalContext]

/-- A result value: the id `id` on success (code `0`), else no id and the failure's code. -/
def idRes (code id : Nat) : val :=
  if code = 0 then PairV (#(bv id)) (#(W64 0)) else PairV (#(W64 0)) (#(errCode (errOf code)))

/-- The event a witness step of the node `node` stands for: the extension's operation, the
argument the trusted model passes it, and the expression it steps to (its result). -/
def WOp.toEv (node : String) : WOp → Ev
  | .listen a code lis => .step node "Listen" (#a) (Val (idRes code lis))
  | .accept lis code _ endv => .step node "Accept" (#(bv lis)) (Val (idRes code endv))
  | .lisClose lis code => .step node "LisClose" (#(bv lis)) (Val (#(errCode (errOf code))))
  | .dial a code _ endv => .step node "Dial" (#a) (Val (idRes code endv))
  | .read _ _ endv n code data _ =>
    .step node "Read" (PairV (#(bv endv)) (#(bv n)))
      (Val (readResOf code (hexBytes data)).toVal)
  | .write _ _ endv data k code first =>
    .step node "Write" (PairV (#(bv endv)) (PairV (#(hexBytes data)) (#first)))
      (Val (PairV (#(bv k)) (#(errCode (errOf code)))))
  | .close _ _ endv code => .step node "Close" (#(bv endv)) (Val (#(errCode (errOf code))))
  | .closeWrite _ _ endv code =>
    .step node "CloseWrite" (#(bv endv)) (Val (#(errCode (errOf code))))
  | .setDeadline _ _ endv kind wall ext code =>
    .step node "SetDeadline" (PairV (#(bv endv)) (PairV (#(bv kind)) (PairV (#(bv wall)) (#(bv ext)))))
      (Val (#(errCode (errOf code))))
  | .crash => .crash node

end ev

/-! ## One step, decided -/

/-- The direction after a read with result `r`, cut first keeping `keep` bytes if the witness
says so (the witness's choice: the decider then checks it). -/
def readAfter (st : NetEnd) (d : NetDir) (n : Nat) (r : ReadRes) (keep : Option Nat) : NetDir :=
  if st.closed ∨ n = 0 then d
  else
    let d0 : NetDir := match keep with
      | none => d
      | some k => ⟨d.bytes.take k, .cut⟩
    match r with
    | .bytes bs => { d0 with bytes := d0.bytes.drop bs.length }
    | _ => d0

/-- The direction after a write step (`WriteOutcome`'s `d'`, as the step's result determines it). -/
def writeAfter (st : NetEnd) (d : NetDir) (rs : List w8) (k : Nat) (res : Option NetErr) : NetDir :=
  if st.closed then d
  else match d.status, res with
    | .open, none => { d with bytes := d.bytes ++ rs.take k }
    | .open, some .sys => { d with status := .cut }
    | _, _ => d

/-- The end after a close (`CloseOutcome`'s `st'`). -/
def closeEndAfter (st : NetEnd) : NetEnd := if st.closed then st else { st with closed := true }

/-- The direction after a close (`CloseOutcome`'s `d'`). -/
def closeDirAfter (st : NetEnd) (d : NetDir) : NetDir := if st.closed then d else d.shut

/-- The direction after a `CloseWrite` with result `res` (`CloseWriteOutcome`'s `d'`). -/
def closeWriteAfter (st : NetEnd) (d : NetDir) (res : Option NetErr) : NetDir :=
  if st.closed ∨ res.isSome then d else d.shut

/-- The end after setting deadlines (`DeadlineOutcome`'s `st'`). -/
def deadlineAfter (st : NetEnd) (kind : w64) (set : Bool) : NetEnd :=
  if st.closed then st
  else { st with rdl := if kind = W64 2 then st.rdl else set,
                 wdl := if kind = W64 1 then st.wdl else set }

/-- A result code a witness step may have (`errCode`'s: 0 to 3). -/
def okCode (c : Nat) : Bool := decide (c ≤ 3)

/-- The connection-end operations: the end's connection, its state, and the checks every one of
them makes (`IsEnd`, the connection exists). -/
def withConn (w : World) (node : String) (conn : Nat) (side : Bool) (endv : Nat)
    (k : NetConn → Except String World) : Except String World :=
  match alGet w.locs node, alGet w.conns conn with
  | none, _ => .error s!"no node {node}"
  | _, none => .error s!"no connection {conn}"
  | some _, some cn =>
    if isEndB (bv endv) conn side then k cn
    else .error s!"end {endv} is not the end {if side then 1 else 0} of connection {conn}"

/-- One witness step of the node `node` from the state `w`: the state after, checked by the
deciders (`Decide.lean`), or why it is not a step of the model. The step's hidden choices are the
witness's (the connection a `Dial` makes, the listener id a `Listen` makes, the cut a `Read`
makes), and the state after is computed from them; the
relation is then decided on that state. -/
def step (w : World) (node : String) : WOp → Except String World
  | .crash =>
    match alGet w.locs node with
    | none => .error s!"no node {node}"
    | some L => .ok (w.setLoc node { L with lis := [] })
  | .listen a code lis =>
    match alGet w.locs node with
    | none => .error s!"no node {node}"
    | some L =>
      if listenOk a then
        if code = 3 then .ok w
        else if code = 0 ∧ bv lis ≠ 0 ∧ alGet L.lis (bv lis) = none ∧
            L.lis.all (fun x => decide (x.2 ≠ (a, true))) then
          .ok (w.setLoc node { L with lis := alSet L.lis (bv lis) (a, true) })
        else .error s!"Listen: code {code} (ListenStep: a new listener id, no open listener at the address; or sys)"
      else .error "Listen: not a valid address or wildcard (listenOk, D6, D20, D21)"
  | .accept lis code conn endv =>
    match alGet w.locs node with
    | none => .error s!"no node {node}"
    | some L =>
      match alGet L.lis (bv lis) with
      | none => .error s!"Accept: no listener {lis} at node {node}"
      | some (a, o) =>
        if code = 0 then
          match alGet w.conns conn with
          | none => .error s!"Accept: no connection {conn}"
          | some cn =>
            if o = true ∧ lisAcceptsB a cn.addr ∧ cn.accepted = false ∧ 2 * conn + 1 < 2 ^ 64 ∧
                bv endv = endId conn true then
              .ok (w.setConn conn { cn with accepted := true })
            else .error s!"Accept of connection {conn}: not open, not at the address, accepted already, or not its end"
        else if (code = 1 ∧ o = false) ∨ (code = 3 ∧ o = true) then .ok w
        else .error s!"Accept: code {code} (AcceptStep: closed iff the listener is closed, else sys)"
  | .lisClose lis code =>
    match alGet w.locs node with
    | none => .error s!"no node {node}"
    | some L =>
      match alGet L.lis (bv lis) with
      | none => .error s!"LisClose: no listener {lis} at node {node}"
      | some (a, o) =>
        if okCode code ∧ lisCloseOutcomeB o (errOf code) false then
          .ok (w.setLoc node { L with lis := alSet L.lis (bv lis) (a, false) })
        else .error s!"LisClose: code {code} (LisCloseOutcome)"
  | .dial a code conn endv =>
    match alGet w.locs node with
    | none => .error s!"no node {node}"
    | some _ =>
      if addrOk a then
        match conn with
        | none => if code = 3 then .ok w else .error s!"Dial: code {code} with no connection"
        | some c =>
          if c ≠ 0 ∧ alGet w.conns c = none ∧ 2 * c + 1 < 2 ^ 64 then
            if code = 0 ∧ bv endv = endId c false then .ok (w.setConn c (NetConn.fresh a))
            else if code = 3 then .ok (w.setConn c (NetConn.abandoned a))
            else .error s!"Dial: code {code}, or not the end of connection {c}"
          else .error s!"Dial: connection {c} is not new (NewConn)"
      else .error "Dial: not a valid address (addrOk, D20)"
  | .read conn side endv n code data keep =>
    withConn w node conn side endv fun cn =>
      match hexDecode data with
      | none => .error "Read: data is not hex"
      | some bs =>
        if code ≤ 4 then
          let st := cn.endSt side
          let d := cn.out (!side)
          let r := readResOf code bs
          let d' := readAfter st d (bv n).toNat r keep
          if readOutcomeB st d (bv n).toNat r d' then .ok (w.setConn conn (cn.setOut (!side) d'))
          else .error s!"Read: not ReadOutcome (code {code}, {bs.length} bytes, cut {keep})"
        else .error s!"Read: code {code}"
  | .write conn side endv data k code first =>
    withConn w node conn side endv fun cn =>
      match hexDecode data with
      | none => .error "Write: data is not hex"
      | some rs =>
        let st := cn.endSt side
        let d := cn.out side
        let d' := writeAfter st d rs k (errOf code)
        if cn.lock side = !first then
          if okCode code ∧ writeOutcomeB st d rs k (errOf code) d' then
            .ok (w.setConn conn ((cn.setOut side d').setLock side (!writeLast rs k (errOf code))))
          else .error s!"Write: not WriteOutcome (k {k}, code {code}, of {rs.length} bytes left)"
        else .error (if first then "Write: the end's write lock is held by another Write (D25)"
          else "Write: a later step of a Write without the end's write lock (D25)")
  | .close conn side endv code =>
    withConn w node conn side endv fun cn =>
      let st := cn.endSt side
      let d := cn.out side
      let st' := closeEndAfter st
      let d' := closeDirAfter st d
      if okCode code ∧ closeOutcomeB st d (errOf code) st' d' then
        .ok (w.setConn conn ((cn.setEnd side st').setOut side d'))
      else .error s!"Close: not CloseOutcome (code {code})"
  | .closeWrite conn side endv code =>
    withConn w node conn side endv fun cn =>
      let st := cn.endSt side
      let d := cn.out side
      let d' := closeWriteAfter st d (errOf code)
      if okCode code ∧ closeWriteOutcomeB st d (errOf code) d' then
        .ok (w.setConn conn (cn.setOut side d'))
      else .error s!"CloseWrite: not CloseWriteOutcome (code {code})"
  | .setDeadline conn side endv kind wall ext code =>
    withConn w node conn side endv fun cn =>
      let st := cn.endSt side
      let set := !timeIsZero (bv wall) (bv ext)
      let st' := deadlineAfter st (bv kind) set
      if okCode code ∧ deadlineOutcomeB st (bv kind) set (errOf code) st' then
        .ok (w.setConn conn (cn.setEnd side st'))
      else .error s!"SetDeadline: not DeadlineOutcome (code {code})"

/-- A witness step: its index, time, node and operation, and what the call checks read (the
traced call it is a step of, `(pid, s)`; whether that call never returned; a `Write` step's number
in its call and whether it is the last; a `Read`'s count `k`; a crash's two processes). -/
structure WStep where
  i : Nat
  t : Nat
  node : String
  op : WOp
  trace : Option (Nat × Nat) := none
  pending : Bool := false
  part : Nat := 0
  last : Bool := false
  rk : Option Nat := none
  between : Option (Nat × Nat) := none

/-- The replay of the steps from `w`: the state after them all, or the first step that is not a
step of the model (its index, and why). -/
def replay (w : World) : List WStep → Except (Option Nat × String) World
  | [] => .ok w
  | s :: ss =>
    match step w s.node s.op with
    | .ok w' => replay w' ss
    | .error e => .error (some s.i, e)

/-! ## Soundness -/

section sound
variable [GooseExts] [GoGlobalContext]

theorem loc_of {w : World} {n : String} {L : CLocal} (h : alGet w.locs n = some L) :
    w.loc n = some L.abs := by
  simp [World.loc, h]

theorem mstep_same {w : World} {n : String} {op : String} {v : val} {e' : Expr} {g' : NetGlobal}
    {L : CLocal} (hL : alGet w.locs n = some L)
    (hs : IsNetStep op v L.abs w.global e' L.abs g') :
    MStep w.global w.loc (.step n op v e') g' w.loc :=
  MStep.step (loc_of hL) (fun _ _ => ⟨rfl, .inr hs⟩) (loc_of hL) (fun _ _ => rfl)

theorem mstep_set {w : World} {n : String} {op : String} {v : val} {e' : Expr} {L L' : CLocal}
    (hL : alGet w.locs n = some L)
    (hs : IsNetStep op v L.abs w.global e' L'.abs w.global) :
    MStep w.global w.loc (.step n op v e') (w.setLoc n L').global (w.setLoc n L').loc :=
  MStep.step (loc_of hL) (fun _ _ => ⟨rfl, .inr hs⟩) (by rw [World.loc_setLoc]; simp)
    (fun m hm => by rw [World.loc_setLoc]; simp [Ne.symm hm])

theorem lookup_conns {w : World} {c : Nat} {cn : NetConn} (h : alGet w.conns c = some cn) :
    w.global.conns !! c = some cn := by
  simp only [World.global]; rw [ofList_lookup]; exact h

theorem hexBytes_of {s : String} {bs : List w8} (h : hexDecode s = some bs) : hexBytes s = bs := by
  simp [hexBytes, h]

theorem withConn_ok {w w' : World} {node : String} {conn : Nat} {side : Bool} {endv : Nat}
    {k : NetConn → Except String World} (h : withConn w node conn side endv k = .ok w') :
    ∃ L cn, alGet w.locs node = some L ∧ alGet w.conns conn = some cn ∧
      IsEnd (bv endv) conn side ∧ k cn = .ok w' := by
  unfold withConn at h
  split at h
  · cases h
  · cases h
  · rename_i L cn hL hc
    split at h
    · exact ⟨L, cn, hL, hc, isEndB_iff.mp (by assumption), h⟩
    · cases h

/-- **One step is sound**: a witness step the replay accepts is a step of the model (`MStep`:
`NetStep` at the node's local state, or its crash) from the state the replay's state stands for
to the one it computes, with the event the step stands for (`WOp.toEv`). -/
theorem step_sound {w w' : World} {node : String} {op : WOp} (h : step w node op = .ok w') :
    MStep w.global w.loc (op.toEv node) w'.global w'.loc := by
  cases op with
  | crash =>
    simp only [step] at h
    split at h
    · cases h
    · rename_i L hL
      cases h
      exact MStep.crash (loc_of hL) rfl (by rw [World.loc_setLoc]; simp; rfl)
        (fun m hm => by rw [World.loc_setLoc]; simp [Ne.symm hm])
  | listen a code lis =>
    simp only [step] at h
    split at h
    · cases h
    rename_i L hL
    split at h
    case isFalse => cases h
    rename_i hla
    split at h
    · cases h
      rename_i hc
      subst hc
      exact mstep_same hL (Or.inl ⟨a, rfl, hla, Or.inl ⟨rfl, rfl⟩, rfl⟩)
    split at h
    case isFalse => cases h
    rename_i hc3 hc
    obtain ⟨rfl, hne, hnone, hall⟩ := hc
    cases h
    refine mstep_set hL (Or.inl ⟨a, rfl, hla, Or.inr ⟨?_, bv lis, hne,
      ?_, rfl, ?_⟩, rfl⟩)
    · intro l hl
      simp only [CLocal.abs] at hl
      rw [ofList_lookup] at hl
      have hm := alGet_mem hl
      have := List.all_eq_true.mp hall _ hm
      simp at this
    · simp only [CLocal.abs]; rw [ofList_lookup]; exact hnone
    · simp only [CLocal.abs, ofList_alSet]
  | accept lis code conn endv =>
    simp only [step] at h
    split at h
    · cases h
    rename_i L hL
    split at h
    · cases h
    rename_i a o hlis
    have hlis' : L.abs.lis !! bv lis = some (a, o) := by
      simp only [CLocal.abs]; rw [ofList_lookup]; exact hlis
    split at h
    · rename_i hc
      subst hc
      split at h
      · cases h
      rename_i cn hcn
      split at h
      case isFalse => cases h
      rename_i hok
      obtain ⟨ho, ha, hacc, hlt, he⟩ := hok
      cases h
      refine mstep_same hL (Or.inl ⟨bv lis, a, o, rfl, hlis', ?_, rfl⟩)
      refine Or.inr (Or.inr ⟨ho, conn, cn, lookup_conns hcn, lisAcceptsB_iff.mp ha, hacc, hlt, ?_,
        ?_⟩)
      · simp [idRes, he]
      · exact World.global_setConn _ _ _
    · split at h
      case isFalse => cases h
      rename_i hc0 hc
      cases h
      refine mstep_same hL (Or.inl ⟨bv lis, a, o, rfl, hlis', ?_, rfl⟩)
      rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨rfl, rfl, rfl⟩
      · exact Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)
  | lisClose lis code =>
    simp only [step] at h
    split at h
    · cases h
    rename_i L hL
    split at h
    · cases h
    rename_i a o hlis
    split at h
    case isFalse => cases h
    rename_i hok
    cases h
    refine mstep_set hL (Or.inl ⟨bv lis, a, o, errOf code, false, rfl, ?_, rfl,
      lisCloseOutcomeB_iff.mp (by simp_all), rfl, ?_⟩)
    · simp only [CLocal.abs]; rw [ofList_lookup]; exact hlis
    · simp only [CLocal.abs, ofList_alSet]
  | dial a code conn endv =>
    simp only [step] at h
    split at h
    · cases h
    rename_i L hL
    split at h
    case isFalse => cases h
    rename_i hplan'
    split at h
    · split at h
      case isFalse => cases h
      rename_i hc
      subst hc
      cases h
      exact mstep_same hL (Or.inl ⟨a, rfl, ⟨hplan', Or.inl ⟨rfl, rfl⟩⟩, rfl⟩)
    · rename_i c
      split at h
      case isFalse => cases h
      rename_i hnew
      obtain ⟨hc0, hnone, hlt⟩ := hnew
      have hnew' : NewConn w.global c := by
        refine ⟨hc0, ?_, hlt⟩
        simp only [World.global]; rw [ofList_lookup]; exact hnone
      split at h
      · rename_i hok
        obtain ⟨rfl, he⟩ := hok
        cases h
        refine mstep_same hL (Or.inl ⟨a, rfl, ⟨hplan', Or.inr (Or.inl ⟨c, hnew', ?_,
          World.global_setConn _ _ _⟩)⟩, rfl⟩)
        simp [idRes, he]
      · split at h
        case isFalse => cases h
        rename_i hc
        subst hc
        cases h
        exact mstep_same hL (Or.inl ⟨a, rfl, ⟨hplan', Or.inr (Or.inr ⟨c, hnew', rfl,
          World.global_setConn _ _ _⟩)⟩, rfl⟩)
  | read conn side endv n code data keep =>
    simp only [step] at h
    obtain ⟨L, cn, hL, hcn, hE, h⟩ := withConn_ok h
    split at h
    · cases h
    rename_i bs hbs
    split at h
    case isFalse => cases h
    split at h
    case isFalse => cases h
    rename_i hcode ho
    cases h
    refine mstep_same hL (Or.inl ⟨bv endv, bv n, conn, side, rfl, hE, ⟨cn, _, _,
      lookup_conns hcn, readOutcomeB_iff.mp ho, ?_, World.global_setConn _ _ _⟩, rfl⟩)
    simp only [hexBytes_of hbs]
  | write conn side endv data k code first =>
    simp only [step] at h
    obtain ⟨L, cn, hL, hcn, hE, h⟩ := withConn_ok h
    split at h
    · cases h
    rename_i rs hrs
    split at h
    case isFalse => cases h
    rename_i hlk
    split at h
    case isFalse => cases h
    rename_i hok
    cases h
    refine mstep_same hL (Or.inl ⟨bv endv, rs, first, conn, side, ?_, hE, ⟨cn, k, errOf code, _,
      lookup_conns hcn, hlk, writeOutcomeB_iff.mp (by simp_all), rfl, World.global_setConn _ _ _⟩,
      rfl⟩)
    simp only [hexBytes_of hrs]
  | close conn side endv code =>
    simp only [step] at h
    obtain ⟨L, cn, hL, hcn, hE, h⟩ := withConn_ok h
    split at h
    case isFalse => cases h
    rename_i hok
    cases h
    exact mstep_same hL (Or.inl ⟨bv endv, conn, side, rfl, hE, ⟨cn, errOf code, _, _,
      lookup_conns hcn, closeOutcomeB_iff.mp (by simp_all), rfl, World.global_setConn _ _ _⟩, rfl⟩)
  | closeWrite conn side endv code =>
    simp only [step] at h
    obtain ⟨L, cn, hL, hcn, hE, h⟩ := withConn_ok h
    split at h
    case isFalse => cases h
    rename_i hok
    cases h
    exact mstep_same hL (Or.inl ⟨bv endv, conn, side, rfl, hE, ⟨cn, errOf code, _,
      lookup_conns hcn, closeWriteOutcomeB_iff.mp (by simp_all), rfl, World.global_setConn _ _ _⟩,
      rfl⟩)
  | setDeadline conn side endv kind wall ext code =>
    simp only [step] at h
    obtain ⟨L, cn, hL, hcn, hE, h⟩ := withConn_ok h
    split at h
    case isFalse => cases h
    rename_i hok
    cases h
    exact mstep_same hL (Or.inl ⟨bv endv, bv kind, bv wall, bv ext, conn, side, rfl, hE,
      ⟨cn, errOf code, _, lookup_conns hcn, deadlineOutcomeB_iff.mp (by simp_all), rfl,
        World.global_setConn _ _ _⟩, rfl⟩)

/-- **The replay is sound**: if it accepts the steps from `w`, they are an execution of the model
(`Exec`) from the state `w` stands for to the one it computes, with the events the steps stand
for. -/
theorem replay_sound {w w' : World} {ss : List WStep} (h : replay w ss = .ok w') :
    Exec w.global w.loc (ss.map (fun s => s.op.toEv s.node)) w'.global w'.loc := by
  induction ss generalizing w with
  | nil => cases h; exact Exec.nil
  | cons s ss ih =>
    simp only [replay] at h
    split at h
    · rename_i w1 h1
      exact Exec.cons (step_sound h1) (ih h)
    · cases h

theorem alGet_map_snd {K V W : Type} [DecidableEq K] (l : List (K × V)) (f : V → W) (a : K) :
    alGet (l.map (fun x => (x.1, f x.2))) a = (alGet l a).map f := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    obtain ⟨k, v⟩ := x
    simp only [List.map_cons, alGet_cons, ih]
    split <;> simp

/-- The initial state's network: no connection. -/
theorem World.init_global (nodes : List String) : (World.init nodes).global = ⟨∅⟩ := rfl

theorem alGet_map_const {V : Type} (nodes : List String) (v : V) (n : String) :
    alGet (nodes.map (fun m => (m, v))) n = if n ∈ nodes then some v else none := by
  induction nodes with
  | nil => rfl
  | cons m l ih =>
    simp only [List.map_cons, alGet_cons, ih, List.mem_cons]
    by_cases h : m = n
    · subst h; simp
    · have : ¬ n = m := fun e => h e.symm
      simp [h, this]

/-- The initial state's nodes: each with no listener. -/
theorem World.init_loc (nodes : List String) :
    (World.init nodes).loc = fun n => if n ∈ nodes then some ⟨∅⟩ else none := by
  funext n
  simp only [World.loc, World.init]
  rw [alGet_map_const nodes (⟨[]⟩ : CLocal)]
  split <;> rfl

end sound

/-- Part (b) of the certification: the steps replay from the initial state (no connection, each
node with no listener). `main` runs exactly this. -/
def checkSteps (nodes : List String) (ss : List WStep) : Except (Option Nat × String) World :=
  replay (World.init nodes) ss

/-- **What CERTIFIED rests on, for the steps.** If `checkSteps` accepts, the witness's steps, in
order, are an execution of the net extension's semantics (`net_semantics.step`, `NetStep`, and
`net_semantics.crash`, with the network and the nodes' local states threaded through) from the
initial state: the network with no connection (`NetGlobal.init`), and each node of the witness
with no listener (`NetLocal.init`); each step's event is the operation, argument and result the
witness step gives (`WOp.toEv`). -/
theorem checkSteps_sound [GooseExts] [GoGlobalContext] {nodes : List String} {ss : List WStep}
    {w' : World} (h : checkSteps nodes ss = .ok w') :
    Exec ⟨∅⟩ (fun n => if n ∈ nodes then some ⟨∅⟩ else none)
      (ss.map (fun s => s.op.toEv s.node)) w'.global w'.loc := by
  unfold checkSteps at h
  have := replay_sound h
  rwa [World.init_global, World.init_loc] at this

/-! ## Reading the witness and the calls (`Lean.Json`) -/

open Lean (Json)

def jField (j : Json) (k : String) : Json := j.getObjValD k

def jHas (j : Json) (k : String) : Bool := (j.getObjVal? k).toBool

def jNat (j : Json) (k : String) : Except String Nat :=
  match (j.getObjValD k).getNat? with
  | .ok n => .ok n
  | .error _ => .error s!"field {k}: not a natural number"

def jNat? (j : Json) (k : String) : Option Nat := ((j.getObjValD k).getNat?).toOption

def jNatD (j : Json) (k : String) (d : Nat) : Nat := (jNat? j k).getD d

def jStr (j : Json) (k : String) : Except String String :=
  match (j.getObjValD k).getStr? with
  | .ok s => .ok s
  | .error _ => .error s!"field {k}: not a string"

def jStr? (j : Json) (k : String) : Option String := ((j.getObjValD k).getStr?).toOption

def jStrD (j : Json) (k : String) : String := (jStr? j k).getD ""

/-- A boolean field, false if absent or not a boolean (Python's falsy `None`). -/
def jBool (j : Json) (k : String) : Bool := ((j.getObjValD k).getBool?).toOption.getD false

def jArr (j : Json) (k : String) : Except String (Array Json) :=
  match (j.getObjValD k).getArr? with
  | .ok a => .ok a
  | .error _ => .error s!"field {k}: not an array"

def jIsNull (j : Json) : Bool := j.isNull

/-- `side` 0 or 1 as the end (`true`: the acceptor's). -/
def jSide (j : Json) : Except String Bool := do
  match ← jNat j "side" with
  | 0 => pure false
  | 1 => pure true
  | s => throw s!"side {s}"

/-- A witness step (README, "The witness"). -/
def parseStep (j : Json) : Except String WStep := do
  let i ← jNat j "i"
  let t ← jNat j "t"
  let node ← jStr j "node"
  let op ← jStr j "op"
  let res := jField j "res"
  let tr := jField j "trace"
  let trace := match jNat? tr "pid", jNat? tr "s" with
    | some p, some s => some (p, s)
    | _, _ => none
  let base : WStep := { i, t, node, op := .crash, trace, pending := jBool j "pending" }
  match op with
  | "Crash" =>
    let b ← jArr j "between"
    match b.toList.map Json.getNat? with
    | [.ok p, .ok q] => pure { base with op := .crash, between := some (p, q) }
    | _ => throw "Crash: between is not [pid, pid]"
  | "Listen" =>
    let code ← jNat res "code"
    let lis ← if code = 0 then jNat res "lis" else pure 0
    let a ← jStr j "addr"
    pure { base with op := .listen (stringToGoString a) code lis }
  | "Accept" =>
    let code ← jNat res "code"
    let conn ← if code = 0 then jNat res "conn" else pure 0
    let endv ← if code = 0 then jNat res "end" else pure 0
    let lis ← jNat j "lis"
    pure { base with op := .accept lis code conn endv }
  | "LisClose" =>
    let lis ← jNat j "lis"
    let code ← jNat res "code"
    pure { base with op := .lisClose lis code }
  | "Dial" =>
    let code ← jNat res "code"
    let conn := if code = 0 then jNat? res "conn" else jNat? res "abandoned"
    let a ← jStr j "addr"
    pure { base with op := .dial (stringToGoString a) code conn (jNatD res "end" 0) }
  | "Read" =>
    let cut := jField j "cut"
    let keep ← if jIsNull cut then pure none else some <$> jNat cut "keep"
    let o := WOp.read (← jNat j "conn") (← jSide j) (← jNat j "end") (← jNat j "n")
      (← jNat res "code") (jStrD res "data") keep
    pure { base with op := o, rk := jNat? res "k" }
  | "Write" =>
    let part ← jNat j "part"
    let o := WOp.write (← jNat j "conn") (← jSide j) (← jNat j "end") (← jStr j "data")
      (← jNat res "k") (← jNat res "code") (part == 0)
    pure { base with op := o, part, last := jBool j "last" }
  | "Close" =>
    let o := WOp.close (← jNat j "conn") (← jSide j) (← jNat j "end") (← jNat res "code")
    pure { base with op := o }
  | "CloseWrite" =>
    let o := WOp.closeWrite (← jNat j "conn") (← jSide j) (← jNat j "end") (← jNat res "code")
    pure { base with op := o }
  | "SetDeadline" =>
    let o := WOp.setDeadline (← jNat j "conn") (← jSide j) (← jNat j "end")
      (← jNat j "kind") (← jNat j "wall") (← jNat j "ext") (← jNat res "code")
    pure { base with op := o }
  | o => throw s!"unknown op {o}"

/-- A witness node: its name, host and processes (pids, in incarnation order). -/
structure WNode where
  name : String
  host : String
  procs : List Nat

/-- A witness (README, "The witness", version 2: v3.4, no plan, and a `Listen` listens at its own
address). -/
structure Witness where
  nodes : List WNode
  steps : Array WStep

def parseWitness (j : Json) : Except String Witness := do
  unless jStrD j "format" == "net-witness" do throw "not a net-witness"
  unless jNatD j "version" 0 == 2 do throw s!"witness version {jNatD j "version" 0}, this replay reads 2"
  let nodes ← (← jArr j "nodes").toList.mapM fun n => do
    pure { name := ← jStr n "node", host := ← jStr n "host",
           procs := ← (← jArr n "procs").toList.mapM Json.getNat? : WNode }
  let steps ← (← jArr j "steps").mapM parseStep
  pure { nodes, steps }

/-- A traced process (the calls file). -/
structure Proc where
  pid : Nat
  node : String
  t0 : Nat
  t1 : Nat
  timens : String
  exit : Option Nat

/-- A traced call: its `B` record and its `E` record (none if it never returned). -/
structure Call where
  pid : Nat
  s : Nat
  op : String
  id : Option String
  b : Json
  e : Option Json
  bt : Nat
  et : Option Nat

def Call.where_ (c : Call) : String := s!"{c.pid}#{c.s} ({c.op})"

/-- The calls file (README, "Certification in Lean"). -/
structure Calls where
  procs : List Proc
  calls : Array Call
  /-- The drivers' time namespaces (their exit events are on their clock). -/
  driverTimens : List String

def parseCalls (j : Json) : Except String Calls := do
  unless jStrD j "format" == "net-calls" do throw "not a net-calls file"
  unless jNatD j "version" 0 == 1 do throw "calls version: this replay reads 1"
  let procs ← (← jArr j "procs").toList.mapM fun p => do
    pure { pid := ← jNat p "pid", node := ← jStr p "node", t0 := jNatD p "t0" 0,
           t1 := jNatD p "t1" 0, timens := jStrD p "timens", exit := jNat? p "exit" : Proc }
  let calls ← (← jArr j "calls").mapM fun c => do
    let b := jField c "b"
    let e := jField c "e"
    let e := if jIsNull e then none else some e
    pure { pid := ← jNat c "pid", s := ← jNat b "s", op := ← jStr b "op", id := jStr? b "id", b,
           e, bt := ← jNat b "t", et := e.bind (jNat? · "t") : Call }
  let drivers ← match jField j "drivers" with
    | .null => pure []
    | d => do (← d.getArr?).toList.mapM fun x => pure (jStrD x "timens")
  pure { procs, calls, driverTimens := drivers }

/-! ## The mapping from traced results to the extension's (`mapping.py`, net.lean)

Trusted: a transcription of how net.lean's trusted models build Go's values from the extension's
results (`model.kindErr`, `model.connErr`, `model.opError`, `model.errFlag`, each model's Op,
Source, Addr and Syscall), read backwards; the same rules as `mapping.py`'s (README, "From traces to
the model"), here over the trace's raw error facts. Any value no extension result explains (a
shape finding) refuses certification. -/

/-- Go's `OpError.Op` of each traced operation. -/
def goOp : String → String
  | "Read" => "read" | "Write" => "write" | "Close" => "close" | "CloseWrite" => "close"
  | "SetDeadline" => "set" | "Accept" => "accept" | "ListenerClose" => "close" | "Dial" => "dial"
  | "DialTimeout" => "dial" | "Listen" => "listen" | _ => ""

/-- The `*os.SyscallError`'s `Syscall` of a `sys` failure, where net.lean fixes it. -/
def goSyscall : String → Option String
  | "Read" => some "read" | "Write" => some "write" | "CloseWrite" => some "shutdown"
  | "Accept" => some "accept4" | "Close" => some "close" | "ListenerClose" => some "close"
  | "SetDeadline" => some "set" | _ => none

/-- The operations whose `OpError.Source` is nil. -/
def sourceNil (op : String) : Bool :=
  op ∈ ["SetDeadline", "Accept", "ListenerClose", "Dial", "DialTimeout", "Listen"]

/-- A non-nil `*net.TCPAddr` (`model.anyTCPAddr`), as the tracer records it. -/
def netAddrOk (a : Json) : Bool :=
  jStrD a "type" == "*net.TCPAddr" && !jBool a "nil" && jHas a "s"

def chk (b : Bool) (msg : String) : Except String Unit := if b then pure () else throw msg

/-- The extension's result code of a traced error (`none` for success; `4` for `io.EOF`), or the
shape finding that no extension result gives this Go value (`mapping.err_kind`). -/
def errKind (op : String) (err : Json) : Except String (Option Nat) := do
  if jIsNull err then return none
  let t := jStrD err "type"
  if jBool err "eof" then
    chk (op == "Read") s!"io.EOF from {op} (net.lean returns io.EOF only from Read)"
    return some 4
  chk (!jBool err "isEOF") "an error wrapping io.EOF (net.lean returns io.EOF itself)"
  chk (t == "*net.OpError") s!"an error of type {t} from {op} (net.lean: *net.OpError)"
  chk (jStrD err "op" == goOp op) s!"OpError.Op {jStrD err "op"} (net.lean's {op}: {goOp op})"
  chk (jStrD err "net" == "tcp") "OpError.Net is not tcp"
  if sourceNil op then chk (jIsNull (jField err "source")) s!"OpError.Source not nil (net.lean's {op})"
  else chk (netAddrOk (jField err "source")) s!"OpError.Source not a non-nil *TCPAddr (net.lean's {op})"
  chk (netAddrOk (jField err "addr")) s!"OpError.Addr not a non-nil *TCPAddr (net.lean's {op})"
  chk (jHas err "timeout" && jHas err "temporary") "no Timeout()/Temporary() recorded for an *OpError"
  let to := jBool err "timeout"
  let tmp := jBool err "temporary"
  match jStrD err "inner" with
  | "poll.errNetClosing" =>
    chk (!to && !tmp) "a closed-end error with Timeout() or Temporary() true (errFlag: false)"
    chk (jBool err "isClosed") "errors.Is(err, net.ErrClosed) false for poll.errNetClosing"
    return some 1
  | "*poll.DeadlineExceededError" =>
    chk (to && tmp) "a deadline error with Timeout() or Temporary() false (errFlag: true)"
    chk (jBool err "isDeadline") "errors.Is(err, os.ErrDeadlineExceeded) false for *poll.DeadlineExceededError"
    return some (if op == "DialTimeout" then 3 else 2)
  | "*net.timeoutError" =>
    chk (op == "DialTimeout") s!"net's errTimeout from {op} (net.lean: only DialTimeout returns it)"
    chk (to && tmp) "errTimeout with Timeout() or Temporary() false (errFlag: true)"
    return some 3
  | "*os.SyscallError" =>
    chk (jNatD err "errno" 0 != 0) "an *os.SyscallError with no nonzero syscall.Errno (sysErr: AnyErrno)"
    match goSyscall op with
    | some sc => chk (jStrD err "syscall" == sc) s!"SyscallError.Syscall {jStrD err "syscall"} (net.lean's {op}: {sc})"
    | none => pure ()
    chk (!jBool err "isClosed" && !jBool err "isDeadline")
      "errors.Is ErrClosed or ErrDeadlineExceeded true for an *os.SyscallError"
    return some 3
  | inner => throw s!"OpError.Err of type {inner} (net.lean: errNetClosing, *DeadlineExceededError, *os.SyscallError, DialTimeout's *timeoutError)"

/-- What a returned call's traced result maps to (`mapping.map_call`): its result code (`0`
success, `1`-`3` a failure's kind, `4` EOF), the count (a Read's or a Write's), a Read's bytes
(hex), and a new socket's id (a Dial's, an Accept's, a Listen's). -/
structure Expect where
  code : Nat
  n : Nat := 0
  data : String := ""
  newId : Option String := none

def expect (c : Call) (e : Json) : Except String Expect := do
  let kind ← errKind c.op (jField e "err")
  let code := kind.getD 0
  match c.op with
  | "Read" =>
    let n := jNatD e "n" 0
    let data := jStrD e "data"
    chk (2 * n == data.utf8ByteSize) s!"Read count {n} with {data.utf8ByteSize / 2} bytes"
    if kind.isSome then chk (n == 0) s!"a Read returned {n} bytes and an error (net.lean: 0 with an error)"
    pure { code, n, data }
  | "Write" => pure { code, n := jNatD e "n" 0 }
  | "Close" | "CloseWrite" | "SetDeadline" | "ListenerClose" => pure { code }
  | "Accept" | "Dial" | "DialTimeout" | "Listen" =>
    if kind.isSome then return { code }
    let nw := jField e "new"
    let want := if c.op == "Listen" then "l" else "c"
    let some id := jStr? nw "id" | throw s!"{c.op} succeeded with no new socket recorded"
    chk (id.startsWith want) s!"{c.op} returned the socket {id}"
    chk (netAddrOk (jField nw "local")) "the new socket's LocalAddr is not a non-nil *TCPAddr"
    if c.op != "Listen" then
      chk (netAddrOk (jField nw "remote")) "the new socket's RemoteAddr is not a non-nil *TCPAddr"
    pure { code, newId := some id }
  | op => throw s!"no mapping for {op}"

/-- The traced operations the model has a step for, and the witness op of each. -/
def stepOp : String → Option String
  | "Dial" => some "Dial" | "DialTimeout" => some "Dial" | "Listen" => some "Listen"
  | "Accept" => some "Accept" | "ListenerClose" => some "LisClose" | "Read" => some "Read"
  | "Write" => some "Write" | "Close" => some "Close" | "CloseWrite" => some "CloseWrite"
  | "SetDeadline" => some "SetDeadline" | _ => none

def addrQuery (op : String) : Bool := op ∈ ["ListenerAddr", "LocalAddr", "RemoteAddr"]

/-- The scope rules (README, "From traces to the model", Scope): a call with no step in the model
refuses certification (a certified run is ADMITTED, never OUT OF SCOPE). -/
def inScope (c : Call) : Except String Unit := do
  chk (c.op != "Unmodeled") s!"{c.where_}: {jStrD c.b "api"} is not in the model (out of scope)"
  chk ((stepOp c.op).isSome || addrQuery c.op) s!"{c.where_}: unknown operation (out of scope)"
  let id := c.id.getD ""
  chk (id != "nil" && !id.startsWith "u")
    s!"{c.where_}: an operation on a nil, zero-value or untraced socket (out of scope)"
  if c.op == "Dial" || c.op == "DialTimeout" || c.op == "Listen" then
    chk (jStrD c.b "net" == "tcp") s!"{c.where_}: network {jStrD c.b "net"} (out of scope)"

/-! ## The call checks: linearization and results (parts (c) and (d)) -/

/-- A hex string `b` equals the hex `a` from the byte offset `off` on. -/
def hexEqFrom (a b : String) (off : Nat) : Bool :=
  a.utf8ByteSize == 2 * off + b.utf8ByteSize &&
    String.Pos.Raw.substrEq a ⟨2 * off⟩ b ⟨0⟩ b.utf8ByteSize

/-- What the walk has seen of a call: its steps, a Write's bytes so far, whether its last step
was seen (a Write's loop ended; one step of any other operation). -/
structure CallSt where
  steps : Nat := 0
  p : Nat := 0
  ended : Bool := false

/-- The walk's state. -/
structure CState where
  lastT : Nat := 0
  cur : Std.HashMap String Nat := {}
  socks : Std.HashMap (Nat × String) (Nat × Bool) := {}
  liss : Std.HashMap (Nat × String) (String × Nat) := {}
  prog : Std.HashMap (Nat × Nat) CallSt := {}

/-- The run's fixed facts for the walk. -/
structure Ctx where
  calls : Std.HashMap (Nat × Nat) Call
  procs : Std.HashMap Nat Proc
  maxRec : Std.HashMap Nat Nat
  nodeOf : Std.HashMap Nat String
  nodes : Std.HashMap String WNode

/-- The latest record time of a process (its calls' `B.t` and `E.t`; its header's `t1` if none). -/
def Ctx.lastRec (x : Ctx) (pid : Nat) : Nat :=
  (x.maxRec.get? pid).getD ((x.procs.get? pid).map (·.t1) |>.getD 0)

/-- When a process ended at the latest: its driver's exit event, else its last record. -/
def Ctx.endOf (x : Ctx) (pid : Nat) : Nat :=
  match (x.procs.get? pid).bind (·.exit) with
  | some t => t
  | none => x.lastRec pid

def kindOfWhich : String → Nat
  | "read" => 1 | "write" => 2 | _ => 0

/-- The socket of a connection operation, as the steps that made it (its Dial's or Accept's)
named it. -/
def sockOf (cs : CState) (c : Call) (conn : Nat) (side : Bool) : Except String Unit := do
  let some id := c.id | throw s!"{c.where_}: no socket"
  match cs.socks.get? (c.pid, id) with
  | none => throw s!"{c.where_}: the socket {id} was made by no earlier step"
  | some (cn, sd) =>
    let msg := s!"{c.where_}: the socket {id} is the end {if sd then 1 else 0} of connection {cn}, the step says {if side then 1 else 0} of {conn}"
    chk (cn == conn && sd == side) msg

/-- One witness step, against the traced call it is a step of. -/
def checkStep (x : Ctx) (cs : CState) (s : WStep) : Except String CState := do
  chk (cs.lastT ≤ s.t) s!"its time {s.t} is before the step before it ({cs.lastT}): not in t order"
  let cs := { cs with lastT := s.t }
  let some wn := x.nodes.get? s.node | throw s!"no node {s.node} in the witness"
  let idx := (cs.cur.get? s.node).getD 0
  if let .crash := s.op then
    let some (p, q) := s.between | throw "a crash with no processes"
    chk (wn.procs[idx]? == some p && wn.procs[idx + 1]? == some q)
      s!"a crash of {s.node} between {p} and {q}: not its incarnations {idx} and {idx + 1}"
    let some qp := x.procs.get? q | throw s!"no process {q}"
    chk (x.lastRec p < s.t && s.t ≤ qp.t0)
      s!"a crash at {s.t}, not after process {p}'s last record ({x.lastRec p}) and by {q}'s start ({qp.t0})"
    return { cs with cur := cs.cur.insert s.node (idx + 1) }
  let some (pid, sq) := s.trace | throw "a step with no traced call"
  let some c := x.calls.get? (pid, sq) | throw s!"no traced call {pid}#{sq}"
  chk (stepOp c.op == some (match s.op with
      | .listen .. => "Listen" | .accept .. => "Accept" | .lisClose .. => "LisClose"
      | .dial .. => "Dial" | .read .. => "Read" | .write .. => "Write" | .close .. => "Close"
      | .closeWrite .. => "CloseWrite" | .setDeadline .. => "SetDeadline" | .crash => "Crash"))
    s!"{c.where_}: a step of another operation"
  chk (x.nodeOf.get? pid == some s.node) s!"{c.where_}: process {pid} is not of node {s.node}"
  chk (wn.procs[idx]? == some pid)
    s!"{c.where_}: process {pid} is not node {s.node}'s current incarnation (a step after its crash, or before its start)"
  chk (c.bt ≤ s.t && c.et.all (s.t ≤ ·))
    s!"{c.where_}: the step's time {s.t} is outside the call's interval [{c.bt}, {c.et.map toString |>.getD "never returned"}]"
  chk (s.pending == c.et.isNone) s!"{c.where_}: pending is {s.pending}, the call {if c.et.isNone then "never returned" else "returned"}"
  let st := (cs.prog.get? (pid, sq)).getD {}
  chk (!st.ended) s!"{c.where_}: a step after the call's last step"
  let ex ← match c.e with
    | some e => some <$> expect c e
    | none => pure none
  let codeOk (code : Nat) : Except String Unit :=
    match ex with
    | some x => chk (code == x.code) s!"{c.where_}: result code {code}, the trace's maps to {x.code}"
    | none => pure ()
  let one (cs : CState) : CState := { cs with prog := cs.prog.insert (pid, sq) { steps := 1, ended := true } }
  match s.op with
  | .listen a code lis =>
    chk (a == stringToGoString (jStrD c.b "addr")) s!"{c.where_}: Listen of another address"
    codeOk code
    let cs := one cs
    match ex.bind (·.newId) with
    | some id => if code = 0 then return { cs with liss := cs.liss.insert (pid, id) (s.node, lis) } else return cs
    | none => return cs
  | .accept lis code conn _ =>
    let some id := c.id | throw s!"{c.where_}: no listener"
    chk (cs.liss.get? (pid, id) == some (s.node, lis))
      s!"{c.where_}: the listener {id} is not listener {lis} of {s.node}"
    codeOk code
    let cs := one cs
    match ex.bind (·.newId) with
    | some nid => if code = 0 then return { cs with socks := cs.socks.insert (pid, nid) (conn, true) } else return cs
    | none => return cs
  | .lisClose lis code =>
    let some id := c.id | throw s!"{c.where_}: no listener"
    chk (cs.liss.get? (pid, id) == some (s.node, lis))
      s!"{c.where_}: the listener {id} is not listener {lis} of {s.node}"
    codeOk code
    return one cs
  | .dial a code conn _ =>
    chk (a == stringToGoString (jStrD c.b "addr")) s!"{c.where_}: Dial of another address"
    codeOk code
    let cs := one cs
    match ex.bind (·.newId), conn with
    | some nid, some cn => if code = 0 then return { cs with socks := cs.socks.insert (pid, nid) (cn, false) } else return cs
    | _, _ => return cs
  | .read conn side _ n code data _ =>
    sockOf cs c conn side
    chk (n == jNatD c.b "n" 0 && n < 2 ^ 64) s!"{c.where_}: Read of {n} bytes, the call's buffer has {jNatD c.b "n" 0}"
    if code == 0 then
      chk (s.rk.all (2 * · == data.utf8ByteSize)) s!"{c.where_}: the step's k is not its bytes' count"
    codeOk code
    if let some x := ex then
      if code == 0 then chk (data == x.data) s!"{c.where_}: the step read other bytes than the call returned"
    return one cs
  | .write conn side _ data k code _ =>
    sockOf cs c conn side
    let full := jStrD c.b "data"
    chk (full.utf8ByteSize % 2 == 0 && jNatD c.b "n" 0 == full.utf8ByteSize / 2) s!"{c.where_}: the call's data is not its n bytes"
    chk (s.part == st.steps) s!"{c.where_}: step part {s.part}, the call's step {st.steps}"
    chk (hexEqFrom full data st.p)
      s!"{c.where_}: the step's bytes are not the call's bytes from {st.p} on (the loop's b[nn:])"
    let p := st.p + k
    let ends := code != 0 || p == full.utf8ByteSize / 2
    chk (s.last == ends) s!"{c.where_}: last is {s.last}, the loop {if ends then "ends" else "goes on"} at this step"
    if ends then
      if let some x := ex then
        chk (p == x.n) s!"{c.where_}: the steps add up to {p} bytes, the call returned {x.n}"
        chk (code == x.code) s!"{c.where_}: the last step's code {code}, the trace's maps to {x.code}"
    return { cs with prog := cs.prog.insert (pid, sq) { steps := st.steps + 1, p, ended := ends } }
  | .close conn side _ code | .closeWrite conn side _ code =>
    sockOf cs c conn side
    codeOk code
    return one cs
  | .setDeadline conn side _ kind wall ext code =>
    sockOf cs c conn side
    chk (kind == kindOfWhich (jStrD c.b "which")) s!"{c.where_}: deadline kind {kind}, the call's {jStrD c.b "which"}"
    chk ((!timeIsZero (bv wall) (bv ext)) == jBool c.b "set")
      s!"{c.where_}: the time's IsZero is not the call's (set {jBool c.b "set"})"
    codeOk code
    return one cs
  | .crash => throw "unreachable"

/-- Parts (c) and (d): every traced call is in scope and has the result shapes net.lean can give;
the processes are the witness's nodes' incarnations; then each step against its call; then every
returned call has all its steps. The first failure: the step's index (or none), and why. -/
def checkCalls (w : Witness) (cl : Calls) : Except (Option Nat × String) Unit := do
  let pre : Except String Ctx := do
    let tns := cl.procs.map (·.timens) ++ cl.driverTimens
    chk (tns.all (· == tns.headD "")) "processes in several time namespaces: their clocks are not comparable"
    let mut calls : Std.HashMap (Nat × Nat) Call := {}
    let mut maxRec : Std.HashMap Nat Nat := {}
    for c in cl.calls do
      inScope c
      if let some e := c.e then
        if addrQuery c.op then
          chk (netAddrOk (jField e "addr")) s!"{c.where_}: returned a nil or non-TCP address (D18)"
        else
          discard <| (expect c e).mapError (fun m => s!"{c.where_}: {m}")
      calls := calls.insert (c.pid, c.s) c
      let t := max c.bt (c.et.getD 0)
      maxRec := maxRec.insert c.pid (max t ((maxRec.get? c.pid).getD 0))
    let mut procs : Std.HashMap Nat Proc := {}
    for p in cl.procs do procs := procs.insert p.pid p
    let mut nodeOf : Std.HashMap Nat String := {}
    let mut nodes : Std.HashMap String WNode := {}
    for n in w.nodes do
      chk (!nodes.contains n.name) s!"node {n.name} twice in the witness"
      nodes := nodes.insert n.name n
      for pid in n.procs do
        chk (!nodeOf.contains pid) s!"process {pid} in two nodes"
        let some p := procs.get? pid | throw s!"node {n.name}'s process {pid} is not traced"
        chk (p.node == n.host) s!"process {pid} is node {p.node}, in a node of host {n.host}"
        nodeOf := nodeOf.insert pid n.name
    for p in cl.procs do
      chk (nodeOf.contains p.pid) s!"process {p.pid} ({p.node}) is in no node of the witness"
    let x : Ctx := { calls, procs, maxRec, nodeOf, nodes }
    for p in cl.procs do
      if let some ex := p.exit then
        chk (x.lastRec p.pid ≤ ex) s!"process {p.pid} has a record after its exit event"
    for n in w.nodes do
      for (p, q) in n.procs.zip n.procs.tail do
        let some qp := procs.get? q | throw s!"no process {q}"
        chk (x.endOf p < qp.t0) s!"node {n.name}: process {p} had not ended when {q} started"
    pure x
  let x ← pre.mapError (fun m => (none, m))
  let mut cs : CState := {}
  for s in w.steps do
    cs ← (checkStep x cs s).mapError (fun m => (some s.i, m))
  for c in cl.calls do
    if c.e.isSome && !addrQuery c.op then
      match cs.prog.get? (c.pid, c.s) with
      | none => throw (none, s!"{c.where_}: the call returned and no step of the witness is of it (not linearized)")
      | some st => if !st.ended then
          throw (none, s!"{c.where_}: the call returned and its steps do not end its loop")
  pure ()


/-! ## The command -/

/-- Run `f` now (for the timings: not floated into its first use). -/
@[noinline] def strictly {α : Type} (f : Unit → α) : IO α := pure (f ())

/-- The first failure of the two parts (the one at the earlier step), or none. -/
def firstFailure (r1 : Except (Option Nat × String) World) (r2 : Except (Option Nat × String) Unit) :
    Option (Option Nat × String) :=
  let e1 : Option (Option Nat × String) := match r1 with
    | .ok _ => none
    | .error (i, m) => some (i, match i with | some _ => s!"not a step of the model: {m}" | none => m)
  let e2 : Option (Option Nat × String) := match r2 with
    | .ok _ => none
    | .error e => some e
  match e1, e2 with
  | some (some i, m), some (some j, m') => if j < i then some (some j, m') else some (some i, m)
  | some e, _ => some e
  | none, e => e

end Replay

end Net

end Perennial

open Perennial Perennial.Net Perennial.Net.Replay in
/-- `net-replay WITNESS CALLS`: certify the witness of a run against its calls (README,
"Certification in Lean"): (a) and (b) by `checkSteps` (`checkSteps_sound`), (c) and (d) by
`checkCalls`. Prints CERTIFIED, or NOT CERTIFIED with the first failing step (or call) and why;
exits 0 or 1 (2 on a usage or file error). -/
def main (args : List String) : IO UInt32 := do
  match args with
  | [wf, cf] =>
    let t0 ← IO.monoMsNow
    let ws ← IO.FS.readFile wf
    let cs ← IO.FS.readFile cf
    let some wj := (Lean.Json.parse ws).toOption | IO.println s!"{wf}: not JSON"; return 2
    let some cj := (Lean.Json.parse cs).toOption | IO.println s!"{cf}: not JSON"; return 2
    let w ← match parseWitness wj with
      | .ok w => pure w
      | .error m => IO.println s!"NOT CERTIFIED: witness: {m}"; return 1
    let cl ← match parseCalls cj with
      | .ok c => pure c
      | .error m => IO.println s!"NOT CERTIFIED: calls: {m}"; return 1
    let t1 ← IO.monoMsNow
    let nodes := w.nodes.map (·.name)
    let r1 ← strictly (fun _ => checkSteps nodes w.steps.toList)
    let t2 ← IO.monoMsNow
    let r2 ← strictly (fun _ => checkCalls w cl)
    let t3 ← IO.monoMsNow
    match firstFailure r1 r2 with
    | none =>
      IO.println (s!"CERTIFIED: {w.steps.size} steps, {cl.calls.size} calls, {w.nodes.length} " ++
        s!"nodes (read {t1 - t0} ms, steps {t2 - t1} ms, calls {t3 - t2} ms)")
      return 0
    | some (i, m) =>
      let at_ := match i with | some i => s!"step {i}: " | none => ""
      IO.println s!"NOT CERTIFIED: {at_}{m}"
      return 1
  | _ =>
    IO.println "usage: net-replay WITNESS.json CALLS.json"
    return 2

/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/Rabia/Ghost.lean`, run `rabia-r1wake-1`.
The client's atomic update at the harness's `clientN` is remote's one-shot update at
`cliE = ⊤ \ rabiaE`, `opAU`; notes/dsv-rabia.md.)

The deployment's shared ghost state (interface, stage 1): the record of facts (`Protocol.lean`'s
`Facts`, a ghost map with persistent elements), the key-value state, and the clients' pending
operations, in one invariant `rabiaInv` allocated by `start` and shared by the six nodes.

* `fact γ k v`: the fact `k = v` is recorded (persistent). Every fact has a writer
  (`FKey.writer`): server `X` writes its proposals, states, votes, decisions, proposal requests and
  its proxy's objects; client `c` registers its requests; a slot's decision (`FKey.dec`) is written
  by the first server to decide it. A writer owns the set of its keys already written
  (`keysOf γ W K`, half; the other half in `rabiaInv`), so it knows a key is free.
* `rabiaInv γ`: the facts `M` (valid: `Valid M`), the writers' key sets, half of the key-value
  state, the commands of the decided slots of `M` (`cmdsAt`) (the other half is the client spec's
  `own_state`), and for each registered request its operation: pending with the caller's atomic
  update (`AU`, its commit postcondition `Q` named by a saved predicate the client keeps), or
  linearized (when its slot was first decided), with `Q` for the client to collect.

Stage 2: the configuration is the first fact (`cfgIs γ c`, recorded by `setCfg`); an object
carries a batch of requests (`objCmds`, `regFacts`), a request is executed on the state before it
(`stateBefore`: the slots before, then the requests before it in its batch); `newObj` records a
batch, `decideSlot` commits a decided batch's operations in order.

The laws a package uses (statements; proved in Prove): `fact_agree`, `facts_valid` (the recorded
facts are part of a valid record, so `Protocol.lean`'s theorems apply), `fact_insert` (a writer
records a fact justified by facts it holds), `register` (a client registers a request and deposits
its operation's atomic update), `decideSlot` (a server records its decision of a slot and, the first
time, the slot's decision, committing the atomic update of its request), `collect` (the client
takes `Q`).
-/
module

public import Dsverify.Proof.rabia.Core.Protocol
public import Perennial.Ghost.GhostMap
public import Perennial.Ghost.GhostVar
public import Perennial.Ghost.SavedProp
public import Perennial.Ghost.Token
public import Iris.ProgramLogic.Atomic
public import Perennial.GooseLang.Lifting

@[expose] public section

noncomputable section

namespace Perennial.rabia

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode model

/-! ## Countable keys and values (for the ghost maps) -/

/-- The writers of facts. -/
inductive Writer where
  | srv (X : Nat)
  | cli (c : Nat)
  /-- node 0, the orchestrator: it records the configuration (stage 3) -/
  | orch
deriving DecidableEq, Inhabited

/-- Each key's writer (`none`: a slot's decision, written by the first server to decide it). -/
def model.FKey.writer : FKey → Option Writer
  | .reg (c, _) => some (.cli c)
  | .cfg => some .orch
  | .pobj (X, _) => some (.srv X)
  | .robj X _ => some (.srv X)
  | .prop X _ => some (.srv X)
  | .st X _ _ => some (.srv X)
  | .vt X _ _ => some (.srv X)
  | .mydec X _ => some (.srv X)
  | .preq X _ => some (.srv X)
  | .dec _ => none

instance : Pos.Countable FKey :=
  countableOfLeftInverse (B := Nat × List Nat)
    (fun
      | .reg (c, n) => (0, [c, n])
      | .pobj (X, q) => (1, [X, q])
      | .robj X (c, n) => (2, [X, c, n])
      | .prop X s => (3, [X, s])
      | .st X s p => (4, [X, s, p])
      | .vt X s p => (5, [X, s, p])
      | .mydec X s => (6, [X, s])
      | .dec s => (7, [s])
      | .preq X s => (8, [X, s])
      | .cfg => (9, []))
    (fun
      | (0, [c, n]) => .reg (c, n)
      | (1, [X, q]) => .pobj (X, q)
      | (2, [X, c, n]) => .robj X (c, n)
      | (3, [X, s]) => .prop X s
      | (4, [X, s, p]) => .st X s p
      | (5, [X, s, p]) => .vt X s p
      | (6, [X, s]) => .mydec X s
      | (7, [s]) => .dec s
      | (8, [X, s]) => .preq X s
      | (9, []) => .cfg
      | _ => default)
    (by intro k; cases k <;> rfl)
instance : Pos.Countable DVal :=
  countableOfLeftInverse (B := Option (Nat × Nat))
    (fun | .null => none | .obj id => some id)
    (fun | none => .null | some id => .obj id)
    (by intro d; cases d <;> rfl)
instance : Pos.Countable FVal :=
  countableOfLeftInverse
    (B := GoString ⊕ (List (Nat × Nat) ⊕ (List Nat ⊕ (Nat × Nat ⊕ (Nat ⊕ DVal)))))
    (fun
      | .cmd c => .inl c
      | .reqs rs => .inr (.inl rs)
      | .cfgv c => .inr (.inr (.inl [c.n, c.f, c.batch, c.bms, c.blocks]))
      | .obj id => .inr (.inr (.inr (.inl id)))
      | .bit b => .inr (.inr (.inr (.inr (.inl b))))
      | .dval d => .inr (.inr (.inr (.inr (.inr d)))))
    (fun
      | .inl c => .cmd c
      | .inr (.inl rs) => .reqs rs
      | .inr (.inr (.inl l)) => match l with
        | [n, f, b, m, k] => .cfgv ⟨n, f, b, m, k⟩
        | _ => .cfgv default
      | .inr (.inr (.inr (.inl id))) => .obj id
      | .inr (.inr (.inr (.inr (.inl b)))) => .bit b
      | .inr (.inr (.inr (.inr (.inr d)))) => .dval d)
    (by intro v; cases v <;> rfl)
instance : Pos.Countable Writer :=
  countableOfLeftInverse (B := Nat ⊕ Option Nat)
    (fun | .srv X => .inl X | .cli c => .inr (some c) | .orch => .inr none)
    (fun | .inl X => .srv X | .inr (some c) => .cli c | .inr none => .orch)
    (by intro w; cases w <;> rfl)
instance : Pos.Countable (KvOutput GoString) :=
  countableOfLeftInverse (B := Option (Option GoString))
    (fun | .got v => some v | .done => none)
    (fun | some v => .got v | none => .done)
    (by intro o; cases o <;> rfl)

/-- The key-value state after a sequence of executed commands. -/
def stateOfCmds (L : List GoString) : (kv GoString GoString).State :=
  L.foldl (fun s c => (execCmd s c).1) (fun _ => none)

/-! ## Names -/

/-- The namespaces of the system's invariants: every invariant the commit of a client's update
is under is below `rabiaR` (remote's `RBase.Eop`, `rabiaE`). -/
def rabiaR : Namespace := ndot nroot "rabia"

/-- The mask of the system's invariants. -/
def rabiaE : CoPset := ↑rabiaR

/-- The mask a client's update is fired at (remote's `lin`: `⊤ \ Eop`); the lab's `clientN`. -/
def cliE : CoPset := ⊤ \ rabiaE

/-- The namespace of `rabiaInv` (below `rabiaR`). -/
def rabiaN : Namespace := ndot rabiaR "inv"

theorem cliE_disj_of_sub {N : Namespace} (h : (↑N : CoPset) ⊆ rabiaE) : cliE ## ↑N := by
  intro x ⟨hx, hN⟩
  unfold cliE at hx
  rw [LawfulSet.mem_diff] at hx
  exact hx.2 (h x hN)

theorem rabiaN_sub : (↑rabiaN : CoPset) ⊆ rabiaE := by
  unfold rabiaN rabiaE; exact nclose_subseteq _ _

theorem cliE_rabiaN : cliE ## ↑rabiaN := cliE_disj_of_sub rabiaN_sub

/-- The shared ghost names (`start` allocates them). -/
structure RabiaNames where
  /-- the facts: a ghost map `FKey ↦ FVal` with persistent elements; authority in `rabiaInv` -/
  facts : GName
  /-- each writer's set of written keys: a ghost map `Writer ↦ List FKey`, halves -/
  keys : GName
  /-- the key-value state: a ghost variable of `kv`'s state; halves (`rabiaInv`, `own_state`) -/
  kvs : GName
  /-- each registered request's saved commit predicate: a ghost map `ReqId ↦ GName` -/
  qs : GName
  /-- each registered request's collection token: a ghost map `ReqId ↦ ()`, exclusive -/
  col : GName
deriving Inhabited

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF]

attribute [local instance] GooseGlobalGS.gooseInvGS GooseGlobalGS.gooseAllG

/-- The fact `k = v` is recorded (persistent). -/
def fact (γ : RabiaNames) (k : FKey) (v : FVal) : IProp GF :=
  ghostMapElem γ.facts k .discard v

/-- Writer `W` has written exactly the keys `K` (half; the other half in `rabiaInv`). -/
def keysOf (γ : RabiaNames) (W : Writer) (K : List FKey) : IProp GF :=
  ghostMapElem γ.keys W (.own (1 : Qp).half) K

/-- The key-value state, as the commands executed so far `L` (half; the client spec's `own_state`
is the other, `∃ L, kvHalf γ L ∗ ⌜σ = stateOfCmds L⌝`). -/
def kvHalf (γ : RabiaNames) (L : List GoString) : IProp GF :=
  ghostVar γ.kvs (1 : Qp).half L

/-- The model's state `σ`, owned (the client spec's `own_state`). -/
def kvState (γ : RabiaNames) (σ : (kv GoString GoString).State) : IProp GF :=
  iprop(∃ L, kvHalf γ L ∗ ⌜σ = stateOfCmds L⌝)

/-- The commit postconditions of operations: a pending operation's `Q`. -/
abbrev OpQ (GF : BundledGFunctors) := (kv GoString GoString).State → (kv GoString GoString).State →
  (kv GoString GoString).Output → IProp GF

/-- `Q`, saved under `γq`: as a predicate of the command lists of the states and the output. -/
def savedQ (γq : GName) (Q : OpQ GF) : IProp GF :=
  savedPredOwn γq .discard
    (fun x : List GoString × List GoString × KvOutput GoString =>
      Q (stateOfCmds x.1) (stateOfCmds x.2.1) x.2.2)

/-- The update of client operation `i` with commit postcondition `Q`: remote's one-shot update
(`remote.lin`, over the key-value state `kvState`, at the mask `cliE` = `⊤ \ Eop`), in the
relational form the lab's atomic update at `clientN` had. -/
def opAU (γ : RabiaNames) (i : KvInput GoString GoString) (Q : OpQ GF) : IProp GF :=
  iprop(|={cliE, ∅}=> ∃ σ, kvState γ σ ∗
    ∀ σ' o, kvState γ σ' ∗ ⌜(kv GoString GoString).step σ i σ' o⌝ -∗ |={∅, cliE}=> Q σ σ' o)

/-- A client input as the workload makes them (`Gen`; the kit's input premise): keys of `keyLen`
bytes, put values not empty (a get's reply cannot tell an empty value from none). -/
def inputOk : KvInput GoString GoString → Prop
  | .put k v => k.length = keyLen ∧ v ≠ []
  | .get k => k.length = keyLen

/-- The command string of a client input (`kit.go`'s `command`). -/
def cmdOf : KvInput GoString GoString → GoString
  | .put k v => putCmd k v
  | .get k => getCmd k

/-- The decided slots of `M`, in order (the prefix of decided slots; `Valid` makes it one). -/
def decLog (M : Facts) : Nat → List DVal
  | 0 => []
  | n + 1 => decLog M n ++ (match M (.dec n) with | some (.dval d) => [d] | _ => [])

/-- The registered command of request `r` (as a list: none if not registered). -/
def regCmd (M : Facts) (r : ReqId) : List GoString :=
  match M (.reg r) with | some (.cmd c) => [c] | _ => []

/-- The commands of object `id`: its requests' registered commands, in the batch's order. -/
def objCmds (M : Facts) (id : ObjId) : List GoString :=
  match M (.pobj id) with
  | some (.reqs rs) => rs.flatMap (regCmd M)
  | _ => []

/-- The commands of the first `n` decided slots, in order. -/
def cmdsAt (M : Facts) (n : Nat) : List GoString :=
  (decLog M n).flatMap fun d => match d with
    | .null => []
    | .obj id => objCmds M id

/-- The store after the first `n` decided slots (each object's commands executed in order). -/
def storeAt (M : Facts) (n : Nat) : KStore := stateOfCmds (cmdsAt M n)

/-- Request `r` is decided at slot `s` (in object `id`'s batch `rs`). -/
def ReqAt (M : Facts) (r : ReqId) (s : Nat) : Prop :=
  ∃ id rs, M (.dec s) = some (.dval (.obj id)) ∧ M (.pobj id) = some (.reqs rs) ∧ r ∈ rs

/-- The commands of the requests before `r` in the batch decided at slot `s`. -/
def cmdsBefore (M : Facts) (r : ReqId) (s : Nat) : List GoString :=
  match M (.dec s) with
  | some (.dval (.obj id)) => match M (.pobj id) with
    | some (.reqs rs) => (rs.take (rs.idxOf r)).flatMap (regCmd M)
    | _ => []
  | _ => []

/-- The state request `r` (decided at slot `s`) is executed on: the slots before `s`, then the
requests before `r` in its batch. -/
def stateBefore (M : Facts) (r : ReqId) (s : Nat) : KStore :=
  stateOfCmds (cmdsAt M s ++ cmdsBefore M r s)

/-- The result string of request `r` decided at slot `s` (`naiveExecuteCmd` on the state it is
executed on). -/
def resAt (M : Facts) (r : ReqId) (s : Nat) : Option GoString :=
  match M (.reg r) with
  | some (.cmd c) => some (execCmd (stateBefore M r s) c).2
  | _ => none


/-- The number of decided slots of `M` (they are `0 .. n-1`). -/
def nDec (M : Facts) (n : Nat) : Prop :=
  (∀ s < n, M (.dec s) ≠ none) ∧ M (.dec n) = none

/-- Request `r`'s operation, in `rabiaInv`: pending (not decided yet) with the caller's atomic
update for input `i` and commit postcondition `Q` (named by the saved predicate `γq`); or decided
at a slot, with `Q` of its commit or (once collected) the client's token (the state after the
commit is named by its commands `L'`, the form `savedQ` speaks of). -/
def opState (γ : RabiaNames) (M : Facts) (r : ReqId) : IProp GF :=
  iprop(∃ (γq : GName) (i : KvInput GoString GoString),
    ghostMapElem γ.qs r .discard γq ∗ ⌜M (.reg r) = some (.cmd (cmdOf i)) ∧ inputOk i⌝ ∗
    ((⌜∀ s, ¬ ReqAt M r s⌝ ∗ ∃ Q : OpQ GF, savedQ γq Q ∗ opAU γ i Q) ∨
     (∃ s σ L' o, ⌜ReqAt M r s ∧ σ = stateBefore M r s ∧
        (kv GoString GoString).step σ i (stateOfCmds L') o⌝ ∗
       ((∃ Q : OpQ GF, savedQ γq Q ∗ Q σ (stateOfCmds L') o) ∨
        ghostMapElem γ.col r (.own 1) ()))))

/-- The requests `rs` are registered with the commands `bc`, in order (persistent). -/
def regFacts (γ : RabiaNames) (rs : List ReqId) (bc : List GoString) : IProp GF :=
  iprop(⌜rs.length = bc.length⌝ ∗
    [∗list] i ↦ r ∈ rs, ∃ cm, ⌜bc[i]? = some cm⌝ ∗ fact γ (.reg r) (.cmd cm))

/-- The facts of the first `s` decided slots and their commands `cmds`, in order (persistent):
what a proxy knows when it executes slot `s`, and a reply carries. -/
def prefixFacts (γ : RabiaNames) : Nat → List GoString → IProp GF
  | 0, cmds => iprop(⌜cmds = []⌝)
  | s + 1, cmds => iprop(∃ cmds0 d, prefixFacts γ s cmds0 ∗ fact γ (.dec s) (.dval d) ∗
      (match d with
       | .null => iprop(⌜cmds = cmds0⌝)
       | .obj id => iprop(∃ rs bc, fact γ (.pobj id) (.reqs rs) ∗ regFacts γ rs bc ∗
           ⌜cmds = cmds0 ++ bc⌝)))

/-- The deployment's configuration is `c` (recorded first, by the orchestrator's `New`;
persistent; two agree: `cfgIs_agree`). -/
def cfgIs (γ : RabiaNames) (c : RCfg) : IProp GF :=
  iprop(fact γ .cfg (.cfgv c) ∗ ⌜c.Ok⌝)

/-- The writers' key sets agree with `M`'s keys. -/
def KeysOk (M : Facts) (KS : GMap Writer (List FKey)) : Prop :=
  ∀ k, Iff (∃ W, k.writer = some W ∧ ∃ K, KS.lookup W = some K ∧ k ∈ K)
    (M k ≠ none ∧ k.writer ≠ none)

/-- A key's operation part of the invariant: a registered request's `opState`. -/
def opsTerm (γ : RabiaNames) (M : Facts) (k : FKey) : IProp GF :=
  match k with | .reg r => opState γ M r | _ => iprop(True)

/-- The shared invariant's body at the record `M` (not including `Valid M`). -/
def rabiaInvAt (γ : RabiaNames) (M : Facts) : IProp GF :=
  iprop(∃ (MG : GMap FKey FVal) (KS : GMap Writer (List FKey)) (n : Nat),
    ghostMapAuth γ.facts 1 MG ∗ ⌜∀ k, MG.lookup k = M k⌝ ∗
    ([∗map] k ↦ v ∈ MG, fact γ k v) ∗
    ghostMapAuth γ.keys 1 KS ∗ ⌜KeysOk M KS⌝ ∗
    ([∗map] W ↦ K ∈ KS, keysOf γ W K) ∗
    ⌜nDec M n⌝ ∗ kvHalf γ (cmdsAt M n) ∗
    (∃ QS : GMap ReqId GName, ghostMapAuth γ.qs 1 QS ∗
      ⌜∀ r, Iff (QS.lookup r ≠ none) (M (.reg r) ≠ none)⌝) ∗
    (∃ CS : GMap ReqId Unit, ghostMapAuth γ.col 1 CS ∗
      ⌜∀ r, Iff (CS.lookup r ≠ none) (M (.reg r) ≠ none)⌝) ∗
    [∗map] k ↦ _v ∈ MG, opsTerm γ M k)

/-- The shared invariant (namespace `rabiaN`): a valid record `M` of facts, the ghost maps
mirroring it (with a copy of each fact), the writers' key sets, half of the key-value state at the
decided prefix, and the registered requests' operations. -/
def rabiaInv (γ : RabiaNames) : IProp GF :=
  iprop(∃ (M : Facts), ⌜Valid M⌝ ∗ rabiaInvAt γ M)

/-- The invariant, allocated. -/
def isRabia (γ : RabiaNames) : IProp GF := inv rabiaN (rabiaInv γ)

instance fact_persistent (γ : RabiaNames) (k : FKey) (v : FVal) : Persistent (fact (GF := GF) γ k v) :=
  by unfold fact; infer_instance

instance savedQ_persistent (γq : GName) (Q : OpQ GF) : Persistent (savedQ γq Q) := by
  unfold savedQ; infer_instance

instance fact_timeless (γ : RabiaNames) (k : FKey) (v : FVal) : Timeless (fact (GF := GF) γ k v) :=
  by unfold fact; infer_instance

instance keysOf_timeless (γ : RabiaNames) (W : Writer) (K : List FKey) :
    Timeless (keysOf (GF := GF) γ W K) := by unfold keysOf; infer_instance

instance kvHalf_timeless (γ : RabiaNames) (L : List GoString) :
    Timeless (kvHalf (GF := GF) γ L) := by unfold kvHalf; infer_instance

instance regFacts_persistent (γ : RabiaNames) (rs : List ReqId) (bc : List GoString) :
    Persistent (regFacts (GF := GF) γ rs bc) := by unfold regFacts; infer_instance

instance regFacts_timeless (γ : RabiaNames) (rs : List ReqId) (bc : List GoString) :
    Timeless (regFacts (GF := GF) γ rs bc) := by unfold regFacts; infer_instance

instance cfgIs_persistent (γ : RabiaNames) (c : RCfg) : Persistent (cfgIs (GF := GF) γ c) := by
  unfold cfgIs; infer_instance

instance cfgIs_timeless (γ : RabiaNames) (c : RCfg) : Timeless (cfgIs (GF := GF) γ c) := by
  unfold cfgIs; infer_instance

theorem prefixFacts_persistent' (γ : RabiaNames) :
    ∀ (s : Nat) (cmds : List GoString), Persistent (prefixFacts (GF := GF) γ s cmds)
  | 0, cmds => by unfold prefixFacts; infer_instance
  | s + 1, cmds => by
    have := prefixFacts_persistent' γ s
    unfold prefixFacts
    refine ⟨?_⟩
    iintro ⟨%cmds0, %d, #H1, #H2, H3⟩
    cases d with
    | null =>
      icases H3 with %h
      imodintro
      iexists cmds0, DVal.null
      iframe H1 H2
      ipureintro; exact h
    | obj id =>
      icases H3 with ⟨%rs, %bc, #H4, #H5, %h⟩
      imodintro
      iexists cmds0, DVal.obj id
      iframe H1 H2
      iexists rs, bc
      iframe H4 H5
      ipureintro; exact h

instance prefixFacts_persistent (γ : RabiaNames) (s : Nat) (cmds : List GoString) :
    Persistent (prefixFacts (GF := GF) γ s cmds) := prefixFacts_persistent' γ s cmds

end defs

/-! ## Pure lemmas (internal) -/

section pure

theorem Facts.set_apply (M : Facts) (k k' : FKey) (v : FVal) :
    M.set k v k' = if k' = k then some v else M k' := rfl

theorem Facts.set_self (M : Facts) (k : FKey) (v : FVal) : M.set k v k = some v := by
  simp [Facts.set_apply]

theorem Facts.set_ne (M : Facts) {k k' : FKey} (v : FVal) (h : k' ≠ k) : M.set k v k' = M k' := by
  simp [Facts.set_apply, h]

/-- A valid record: at its configuration, or empty. -/
theorem valid_cases {M : Facts} (hM : Valid M) :
    (∃ c, CfgOf M c ∧ c.Ok ∧ ValidAt c M) ∨ ∀ k, M k = none := by
  unfold Valid at hM; unfold CfgOf
  split at hM
  · rename_i c h; exact Or.inl ⟨c, h, hM⟩
  · exact Or.inr hM

/-- The decided slots of a valid record are a prefix. -/
theorem valid_dec_prefix {M : Facts} (hM : Valid M) {t : Nat} (ht : M (.dec t) ≠ none) :
    ∀ u ≤ t, M (.dec u) ≠ none := by
  rcases valid_cases hM with ⟨c, -, -, hV⟩ | h0
  · induction t with
    | zero => intro u hu; rw [Nat.le_zero.mp hu]; exact ht
    | succ t ih =>
      intro u hu
      rcases Nat.lt_or_eq_of_le hu with h | h
      · exact ih (hV.2.2.2.1 t ht) u (by omega)
      · rw [h]; exact ht
  · exact absurd (h0 _) ht

theorem majProp_pobj {c : RCfg} {M : Facts} (hV : ValidAt c M) {s : Nat} {id : ObjId}
    (h : MajProp c M s id) : ∃ rs, M (.pobj id) = some (.reqs rs) := by
  obtain ⟨W, -, hW, hp⟩ := h
  cases W with
  | nil => simp [RCfg.maj] at hW
  | cons X W => exact (hV.1 _ _ (hp X List.mem_cons_self)).2.1

theorem bitDec_pobj {c : RCfg} {M : Facts} (hV : ValidAt c M) {s b : Nat} {id : ObjId}
    (h : BitDec c M s b (.obj id)) : ∃ rs, M (.pobj id) = some (.reqs rs) := by
  obtain ⟨hb, h0, h1⟩ := h
  rcases Nat.lt_or_eq_of_le hb with hb | hb
  · have := h0 (by omega); cases this
  · obtain ⟨id', he, hm⟩ := h1 hb
    cases he
    exact majProp_pobj hV hm

/-- A decided object is a recorded object. -/
theorem valid_dec_pobj {M : Facts} (hM : Valid M) {t : Nat} {id : ObjId}
    (h : M (.dec t) = some (.dval (.obj id))) : ∃ rs, M (.pobj id) = some (.reqs rs) := by
  rcases valid_cases hM with ⟨c, -, -, hV⟩ | h0
  · have hj : DecEvidence c M t (.obj id) := hV.1 _ _ h
    rcases hj with ⟨p, b, W, -, -, -, hb⟩ | ⟨p, b, W, -, -, -, -, hb⟩ | ⟨id', W, -, hW, hp, he⟩
    · exact bitDec_pobj hV hb
    · exact bitDec_pobj hV hb
    · cases he
      cases W with
      | nil => simp [RCfg.mpf] at hW
      | cons X W => exact (hV.1 _ _ (hp X List.mem_cons_self)).2.1
  · rw [h0] at h; cases h

/-- A recorded object carries registered requests. -/
theorem valid_pobj_reg {M : Facts} (hM : Valid M) {id : ObjId} {rs : List ReqId} {r : ReqId}
    (h : M (.pobj id) = some (.reqs rs)) (hr : r ∈ rs) : ∃ c, M (.reg r) = some (.cmd c) := by
  rcases valid_cases hM with ⟨c, -, -, hV⟩ | h0
  · exact ((hV.1 _ _ h).2.2.2 r hr).1
  · rw [h0] at h; cases h

theorem regCmd_congr {M M' : Facts} (hreg : ∀ r, M' (.reg r) = M (.reg r)) :
    regCmd M' = regCmd M := by
  funext r; simp [regCmd, hreg]

theorem cmdsBefore_congr {M M' : Facts} {r : ReqId} {s : Nat} (hd : M' (.dec s) = M (.dec s))
    (hp : ∀ id, M (.dec s) = some (.dval (.obj id)) → M' (.pobj id) = M (.pobj id))
    (hreg : ∀ r, M' (.reg r) = M (.reg r)) : cmdsBefore M' r s = cmdsBefore M r s := by
  unfold cmdsBefore
  rw [hd, regCmd_congr hreg]
  cases h : M (.dec s) with
  | none => rfl
  | some v =>
    cases v with
    | dval d =>
      cases d with
      | null => rfl
      | obj id => simp only [hp id h]
    | _ => rfl

theorem valid_pobj_nodup {M : Facts} (hM : Valid M) {id : ObjId} {rs : List ReqId}
    (h : M (.pobj id) = some (.reqs rs)) : rs.Nodup := by
  rcases valid_cases hM with ⟨c, -, -, hV⟩ | h0
  · exact (hV.1 _ _ h).2.1
  · rw [h0] at h; cases h

theorem take_idxOf_nodup (pre l : List ReqId) (r : ReqId) (hnd : (pre ++ r :: l).Nodup) :
    (pre ++ r :: l).take ((pre ++ r :: l).idxOf r) = pre := by
  have hr : r ∉ pre := by
    intro h
    exact (List.nodup_append.mp hnd).2.2 r h r List.mem_cons_self rfl
  rw [List.idxOf_append, if_neg hr, List.idxOf_cons_self, Nat.zero_add, List.take_left']
  rfl

theorem flatMap_regCmd_congr {M M' : Facts} (rs : List ReqId)
    (h : ∀ r ∈ rs, M' (.reg r) = M (.reg r)) : rs.flatMap (regCmd M') = rs.flatMap (regCmd M) := by
  simp only [List.flatMap]
  congr 1
  exact List.map_congr_left (fun r hr => by simp [regCmd, h r hr])

theorem cmdsBefore_congr' {M M' : Facts} {r : ReqId} {s : Nat} (hd : M' (.dec s) = M (.dec s))
    (hp : ∀ id, M (.dec s) = some (.dval (.obj id)) → M' (.pobj id) = M (.pobj id))
    (hreg : ∀ id rs, M (.dec s) = some (.dval (.obj id)) → M (.pobj id) = some (.reqs rs) →
      ∀ r' ∈ rs, M' (.reg r') = M (.reg r')) : cmdsBefore M' r s = cmdsBefore M r s := by
  unfold cmdsBefore
  rw [hd]
  cases h : M (.dec s) with
  | none => rfl
  | some v =>
    cases v with
    | dval d =>
      cases d with
      | null => rfl
      | obj id =>
        simp only [hp id h]
        cases h2 : M (.pobj id) with
        | none => rfl
        | some w =>
          cases w with
          | reqs rs =>
            exact flatMap_regCmd_congr _ (fun r' hr' => hreg id rs h h2 r' (List.mem_of_mem_take hr'))
          | _ => rfl
    | _ => rfl

/-- The record after recording `robj X r = obj id` for the requests `l`. -/
theorem foldr_setRobj_apply (X : Nat) (id : ObjId) (l : List ReqId) (M : Facts) (k : FKey) :
    (l.foldr (fun r M' => M'.set (.robj X r) (.obj id)) M) k =
      if k ∈ l.map (FKey.robj X) then some (.obj id) else M k := by
  induction l with
  | nil => simp
  | cons r l ih =>
    simp only [List.foldr_cons, Facts.set_apply, ih, List.map_cons, List.mem_cons]
    by_cases h : k = .robj X r
    · simp [h]
    · by_cases h2 : k ∈ List.map (FKey.robj X) l <;> simp [h, h2]

theorem foldl_setRobj_apply (X : Nat) (id : ObjId) (l : List ReqId) :
    ∀ (M : Facts) (k : FKey), (l.foldl (fun M' r => M'.set (.robj X r) (.obj id)) M) k =
      if k ∈ l.map (FKey.robj X) then some (.obj id) else M k := by
  induction l with
  | nil => simp
  | cons r l ih =>
    intro M k
    simp only [List.foldl_cons, ih, Facts.set_apply, List.map_cons, List.mem_cons]
    by_cases h : k = .robj X r
    · simp [h]
    · by_cases h2 : k ∈ List.map (FKey.robj X) l <;> simp [h, h2]

theorem foldr_setRobj_eq (X : Nat) (id : ObjId) (l : List ReqId) (M : Facts) :
    l.foldr (fun r M' => M'.set (.robj X r) (.obj id)) M =
      l.foldl (fun M' r => M'.set (.robj X r) (.obj id)) M := by
  funext k
  rw [foldr_setRobj_apply, foldl_setRobj_apply]

/-- The commands of a decided value. -/
def dcmds (M : Facts) : DVal → List GoString
  | .null => []
  | .obj id => objCmds M id

/-- The commands of slot `n`. -/
def slotCmds (M : Facts) (n : Nat) : List GoString :=
  match M (.dec n) with | some (.dval d) => dcmds M d | _ => []

theorem cmdsAt_eq (M : Facts) (n : Nat) : cmdsAt M n = (decLog M n).flatMap (dcmds M) := by
  unfold cmdsAt; congr 1

theorem cmdsAt_zero (M : Facts) : cmdsAt M 0 = [] := rfl

theorem cmdsAt_succ (M : Facts) (n : Nat) : cmdsAt M (n + 1) = cmdsAt M n ++ slotCmds M n := by
  rw [cmdsAt_eq, cmdsAt_eq]
  simp only [decLog, List.flatMap_append, slotCmds]
  congr 1
  split <;> simp

theorem cmdsAt_congr {M M' : Facts} {n : Nat}
    (hd : ∀ t < n, M' (.dec t) = M (.dec t))
    (ho : ∀ t < n, ∀ id, M (.dec t) = some (.dval (.obj id)) → objCmds M' id = objCmds M id) :
    cmdsAt M' n = cmdsAt M n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [cmdsAt_succ, cmdsAt_succ, ih (fun t ht => hd t (by omega))
      (fun t ht => ho t (by omega))]
    congr 1
    simp only [slotCmds, hd n (by omega)]
    cases hn : M (.dec n) with
    | none => rfl
    | some v =>
      cases v with
      | dval d =>
        cases d with
        | null => rfl
        | obj id => simp only [dcmds, ho n (by omega) id hn]
      | _ => rfl

theorem foldl_snoc {α β : Type} (f : β → α → β) (b : β) (L : List α) (c : α) :
    List.foldl f b (L ++ [c]) = f (List.foldl f b L) c := by simp

theorem stateOfCmds_snoc (L : List GoString) (c : GoString) :
    stateOfCmds (L ++ [c]) = (execCmd (stateOfCmds L) c).1 := by
  unfold stateOfCmds
  exact foldl_snoc _ _ _ _

/-- The output of input `i` at state `s`. -/
def outOf (s : (kv GoString GoString).State) : KvInput GoString GoString → KvOutput GoString
  | .put _ _ => .done
  | .get k => .got (s k)

theorem execCmd_step (s : KStore) (i : KvInput GoString GoString) (hi : inputOk i) :
    (kv GoString GoString).step s i (execCmd s (cmdOf i)).1 (outOf s i) := by
  cases i with
  | put k v =>
    obtain ⟨hk, -⟩ := hi
    have h1 : ((putCmd k v).drop 1).take keyLen = k := by
      simp [putCmd, hk]
    have h2 : (putCmd k v).drop (1 + keyLen) = v := by
      simp only [putCmd, keyLen] at hk ⊢
      have e : List.drop 9 ((48#8) :: k ++ v) = List.drop 8 (k ++ v) := rfl
      rw [e, List.drop_left' hk]
    refine ⟨?_, rfl⟩
    simp only [execCmd, cmdOf, h1, h2]
    simp [putCmd]
  | get k =>
    refine ⟨?_, ?_⟩ <;> simp [execCmd, cmdOf, getCmd, outOf]

theorem objCmds_set (M : Facts) (k : FKey) (v : FVal) (id : ObjId) (h1 : ∀ id, k ≠ .pobj id)
    (h2 : ∀ r, k ≠ .reg r) : objCmds (M.set k v) id = objCmds M id := by
  have e1 : ∀ id, FKey.pobj id ≠ k := fun id h => h1 id h.symm
  have e2 : ∀ r, FKey.reg r ≠ k := fun r h => h2 r h.symm
  have hr : regCmd (M.set k v) = regCmd M := by
    funext r; simp [regCmd, Facts.set_apply, e2]
  unfold objCmds; rw [hr, Facts.set_ne _ _ (e1 id)]

theorem reqAt_set (M : Facts) (k : FKey) (v : FVal) (r : ReqId) (s : Nat)
    (h1 : ∀ id, k ≠ .pobj id) (h3 : ∀ s, k ≠ .dec s) : ReqAt (M.set k v) r s ↔ ReqAt M r s := by
  have e1 : ∀ id, FKey.pobj id ≠ k := fun id h => h1 id h.symm
  have e3 : ∀ s, FKey.dec s ≠ k := fun s h => h3 s h.symm
  simp [ReqAt, Facts.set_apply, e1, e3]

theorem dec_lt {M : Facts} (hM : Valid M) {n t : Nat} (hn : nDec M n) (h : M (.dec t) ≠ none) :
    t < n := by
  rcases Nat.lt_or_ge t n with h' | h'
  · exact h'
  · exact absurd hn.2 (valid_dec_prefix hM h n h')

theorem first_undecided {M : Facts} (hM : Valid M) {n s : Nat} (hn : nDec M n)
    (hs : M (.dec s) = none) (hprev : s = 0 ∨ M (.dec (s - 1)) ≠ none) : s = n := by
  rcases Nat.lt_trichotomy s n with h | h | h
  · exact absurd hs (hn.1 s h)
  · exact h
  · rcases hprev with h0 | h1
    · omega
    · have := dec_lt hM hn h1; omega

theorem nDec_setdec {M : Facts} (hM : Valid M) {n : Nat} (hn : nDec M n) (v : FVal) :
    nDec (M.set (.dec n) v) (n + 1) := by
  refine ⟨fun t ht => ?_, ?_⟩
  · by_cases h : t = n
    · subst h; simp [Facts.set_self]
    · rw [Facts.set_ne _ _ (by simp [h])]; exact hn.1 t (by omega)
  · rw [Facts.set_ne _ _ (by simp)]
    cases h : M (.dec (n + 1)) with
    | none => rfl
    | some _ => exact absurd hn.2 ((valid_dec_prefix hM (t := n + 1) (by simp [h])) n (by omega))

theorem cmdsAt_setdec (M : Facts) (n : Nat) (v : FVal) (t : Nat) (ht : t ≤ n) :
    cmdsAt (M.set (.dec n) v) t = cmdsAt M t :=
  cmdsAt_congr (fun t' h => Facts.set_ne _ _ (by simp; omega))
    (fun _ _ id _ => objCmds_set M _ v id (fun _ => by simp) (fun _ => by simp))

/-- `KeysOk` after writer `W` records the free key `k`. -/
theorem keysOk_insert {M : Facts} {KS : GMap Writer (List FKey)} {W : Writer} {K : List FKey}
    {k : FKey} (v : FVal) (hKO : KeysOk M KS) (hW : k.writer = some W) (hK : KS.lookup W = some K) :
    KeysOk (M.set k v) (KS.insert W (k :: K)) := by
  intro k'
  by_cases hk : k' = k
  · subst hk
    simp only [Facts.set_self, ne_eq, reduceCtorEq, not_false_eq_true, hW, true_and, iff_true]
    exact ⟨W, rfl, k' :: K, GMap.lookup_insert _ _ _, List.mem_cons_self⟩
  · rw [Facts.set_ne _ _ hk, ← hKO k']
    constructor
    · rintro ⟨W', hW', K', hK', hm⟩
      refine ⟨W', hW', ?_⟩
      by_cases hWW : W = W'
      · subst hWW
        rw [GMap.lookup_insert] at hK'
        cases hK'
        exact ⟨K, hK, List.mem_of_ne_of_mem hk hm⟩
      · rw [GMap.lookup_insert_ne _ _ hWW] at hK'
        exact ⟨K', hK', hm⟩
    · rintro ⟨W', hW', K', hK', hm⟩
      refine ⟨W', hW', ?_⟩
      by_cases hWW : W = W'
      · subst hWW
        rw [hK] at hK'; cases hK'
        exact ⟨k :: K, GMap.lookup_insert _ _ _, List.mem_cons_of_mem _ hm⟩
      · rw [GMap.lookup_insert_ne _ _ hWW]
        exact ⟨K', hK', hm⟩

/-- `KeysOk` after a writerless key (a slot's decision) is recorded. -/
theorem keysOk_insert_none {M : Facts} {KS : GMap Writer (List FKey)} {k : FKey} (v : FVal)
    (hKO : KeysOk M KS) (hW : k.writer = none) : KeysOk (M.set k v) KS := by
  intro k'
  by_cases hk : k' = k
  · subst hk
    simp only [hW, reduceCtorEq, false_and, exists_const, ne_eq, not_true_eq_false, and_false]
  · rw [Facts.set_ne _ _ hk]; exact hKO k'

/-- A writer's unwritten key is not recorded. -/
theorem keysOk_free {M : Facts} {KS : GMap Writer (List FKey)} {W : Writer} {K : List FKey}
    {k : FKey} (hKO : KeysOk M KS) (hW : k.writer = some W) (hK : KS.lookup W = some K)
    (hk : k ∉ K) : M k = none := by
  cases hMk : M k with
  | none => rfl
  | some v0 =>
  exfalso
  obtain ⟨W', hW', K', hK', hm⟩ := (hKO k).2 ⟨by simp [hMk], by simp [hW]⟩
  rw [hW] at hW'; cases hW'
  rw [hK] at hK'; cases hK'
  exact hk hm

end pure

/-! ## Invariant lemmas (internal) -/

section invlemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF]

attribute [local instance] GooseGlobalGS.gooseInvGS GooseGlobalGS.gooseAllG

/-- Request `r`'s operation is unaffected by going from `M` to `M'`. -/
def OpStable (M M' : Facts) (r : ReqId) : Prop :=
  M' (.reg r) = M (.reg r) ∧ (∀ s, ReqAt M' r s ↔ ReqAt M r s) ∧
  (∀ s, ReqAt M r s → stateBefore M' r s = stateBefore M r s)

theorem opState_stable (γ : RabiaNames) (M M' : Facts) (r : ReqId) (h : OpStable M M' r) :
    opState (GF := GF) γ M r ⊢ opState γ M' r := by
  obtain ⟨hreg, hreq, hst⟩ := h
  unfold opState
  iintro ⟨%γq, %i, #Hq, %Hi, H⟩
  iexists γq, i
  iframe Hq
  isplitr
  · ipureintro; rw [hreg]; exact Hi
  icases H with (⟨%Hp, HQ⟩ | ⟨%s, %σ, %σ', %o, %Hs, HQ⟩)
  · ileft
    isplitr
    · ipureintro; intro s hs; exact Hp s ((hreq s).1 hs)
    · iexact HQ
  · iright
    iexists s, σ, σ', o
    isplitr
    · ipureintro
      obtain ⟨h1, h2, h3⟩ := Hs
      exact ⟨(hreq s).2 h1, by rw [hst s h1]; exact h2, h3⟩
    · iexact HQ

theorem ops_stable (γ : RabiaNames) (M M' : Facts) (MG : GMap FKey FVal)
    (h : ∀ r v, MG.lookup (.reg r) = some v → OpStable M M' r) :
    ([∗map] k ↦ _v ∈ MG, opsTerm (GF := GF) γ M k) ⊢ [∗map] k ↦ _v ∈ MG, opsTerm γ M' k := by
  apply BigSepM.bigSepM_mono
  intro k v hk
  cases k with
  | reg r => exact opState_stable γ M M' r (h r v hk)
  | _ => exact .rfl

theorem opsTerm_nonreg (γ : RabiaNames) (M : Facts) (k : FKey) (hk : ∀ r, k ≠ .reg r) :
    opsTerm (GF := GF) γ M k = iprop(True) := by
  cases k with
  | reg r => exact absurd rfl (hk r)
  | _ => rfl

theorem fact_of_elem (γ : RabiaNames) (k : FKey) (v : FVal) :
    ⊢ ghostMapElem (GF := GF) γ.facts k .discard v -∗ fact γ k v := by
  iintro H; unfold fact; iexact H

theorem keysOf_lookup (γ : RabiaNames) (KS : GMap Writer (List FKey)) (W : Writer)
    (K : List FKey) :
    ⊢ ghostMapAuth (GF := GF) γ.keys 1 KS -∗ keysOf γ W K -∗ ⌜KS.lookup W = some K⌝ := by
  unfold keysOf
  iintro Ha H
  iapply ghost_map_lookup $$ Ha H

theorem keysOf_update (E : CoPset) (γ : RabiaNames) (KS : GMap Writer (List FKey)) (W : Writer)
    (K K' : List FKey) (hK : KS.lookup W = some K) :
    ghostMapAuth (GF := GF) γ.keys 1 KS ∗ ([∗map] W ↦ K ∈ KS, keysOf γ W K) ∗ keysOf γ W K ⊢
      |={E}=> ghostMapAuth γ.keys 1 (KS.insert W K') ∗
        ([∗map] W ↦ K ∈ KS.insert W K', keysOf γ W K) ∗ keysOf γ W K' := by
  iintro ⟨Ha, Hm, H1⟩
  icases (BigSepM.bigSepM_delete (Φ := fun W K => keysOf (GF := GF) γ W K) hK).1 $$ Hm
    with ⟨H2, Hm⟩
  unfold keysOf
  ihave H := (ghostMapElem_halves γ.keys W K).2 $$ [H1 H2]
  · isplitl [H1]
    · iexact H1
    · iexact H2
  imod ghost_map_update K' $$ Ha H with ⟨Ha, H⟩
  icases (ghostMapElem_halves γ.keys W K').1 $$ H with ⟨H1, H2⟩
  imodintro
  iframe Ha H1
  iapply (BigSepM.bigSepM_insert_delete
    (Φ := fun W K => ghostMapElem (GF := GF) γ.keys W (.own (1 : Qp).half) K)).2
  iframe H2
  iexact Hm

theorem cmdsAt_stable {M M' : Facts} (hdec : ∀ t, M' (.dec t) = M (.dec t))
    (hobj : ∀ t id, M (.dec t) = some (.dval (.obj id)) → objCmds M' id = objCmds M id) (n : Nat) :
    cmdsAt M' n = cmdsAt M n :=
  cmdsAt_congr (fun t _ => hdec t) (fun t _ id h => hobj t id h)

/-- Writer `W` records the free, non-request, non-decision key `k` (the invariant's body, under
the later; the operations carried along). -/
theorem invAt_insert (E : CoPset) (γ : RabiaNames) (M : Facts) (k : FKey) (v : FVal)
    (W : Writer) (K : List FKey) (hW : k.writer = some W) (hk : k ∉ K)
    (hreg : ∀ r, k ≠ .reg r) (hdec : ∀ s, k ≠ .dec s)
    (hobj : M k = none → ∀ t id, M (.dec t) = some (.dval (.obj id)) →
      objCmds (M.set k v) id = objCmds M id)
    (hreq : M k = none → ∀ r s, ReqAt (M.set k v) r s ↔ ReqAt M r s) :
    ▷ rabiaInvAt (GF := GF) γ M ∗ keysOf γ W K ⊢
      |={E}=> ⌜M k = none⌝ ∗ ▷ rabiaInvAt γ (M.set k v) ∗ keysOf γ W (k :: K) ∗ fact γ k v := by
  iintro ⟨Hi, HK⟩
  unfold rabiaInvAt
  icases Hi with ⟨%MG, %KS, %n, >Hf, >%HMG, >Hfs, >Hk, >%HKO, >Hkw, >%Hn, >Hkv, >HQS, >HCS, Hops⟩
  ihave %HKl := keysOf_lookup γ KS W K $$ Hk HK
  have hfree : M k = none := keysOk_free HKO hW HKl hk
  have hMG : MG.lookup k = none := by rw [HMG]; exact hfree
  imod keysOf_update E γ KS W K (k :: K) HKl $$ [Hk Hkw HK] with ⟨Hk, Hkw, HK⟩
  · iframe
  imod ghost_map_insert_persist k v hMG $$ Hf with ⟨Hf, #Hfact⟩
  ihave #Hfact := fact_of_elem γ k v $$ Hfact
  have hd : ∀ t, (M.set k v) (.dec t) = M (.dec t) := fun t => Facts.set_ne _ _ (fun h => hdec t h.symm)
  have hr : ∀ r, (M.set k v) (.reg r) = M (.reg r) := fun r => Facts.set_ne _ _ (fun h => hreg r h.symm)
  have hc := cmdsAt_stable hd (hobj hfree)
  imodintro
  iframe HK Hfact
  isplitr
  · ipureintro; exact hfree
  · inext
    iexists MG.insert k v, KS.insert W (k :: K), n
    iframe Hf Hk Hkw
    rw [hc]
    iframe Hkv
    isplitr
    · ipureintro; intro k'
      simp only [GMap.lookup_insert_eq_iff, Facts.set_apply]
      by_cases h : k' = k
      · subst h; simp
      · simp [h, Ne.symm h, HMG]
    isplitl [Hfs]
    · iapply (BigSepM.bigSepM_insert (Φ := fun k v => fact (GF := GF) γ k v) hMG).2
      iframe Hfact
      iexact Hfs
    isplitr
    · ipureintro; exact keysOk_insert v HKO hW HKl
    isplitr
    · ipureintro
      refine ⟨fun t ht => ?_, ?_⟩
      · rw [hd]; exact Hn.1 t ht
      · rw [hd]; exact Hn.2
    isplitl [HQS]
    · icases HQS with ⟨%QS, HQS, %HQ⟩
      iexists QS
      iframe HQS
      ipureintro; intro r; rw [hr]; exact HQ r
    isplitl [HCS]
    · icases HCS with ⟨%CS, HCS, %HC⟩
      iexists CS
      iframe HCS
      ipureintro; intro r; rw [hr]; exact HC r
    · iapply (BigSepM.bigSepM_insert (Φ := fun k' _ => opsTerm (GF := GF) γ (M.set k v) k') hMG).2
      rw [opsTerm_nonreg γ _ k hreg]
      isplitr
      · itrivial
      iapply ops_stable γ M (M.set k v) MG ?_ $$ Hops
      intro r _ _
      refine ⟨hr r, hreq hfree r, fun s hs => ?_⟩
      obtain ⟨id0, rs0, h1, h2, -⟩ := hs
      have hp : ∀ id, M (.dec s) = some (.dval (.obj id)) → (M.set k v) (.pobj id) = M (.pobj id) := by
        intro id hid
        rw [h1] at hid
        cases hid
        refine Facts.set_ne _ _ (fun e => ?_)
        rw [← e, h2] at hfree
        cases hfree
      unfold stateBefore
      rw [hc s, cmdsBefore_congr (hd s) hp hr]

/-- Proxy `X` records, for each request of `l`, that it is in object `id` (the invariant's body,
under the later). -/
theorem invAt_insert_robjs (E : CoPset) (γ : RabiaNames) (X : Nat) (id : ObjId) :
    ∀ (l : List ReqId) (M : Facts) (K : List FKey), l.Nodup → (∀ r ∈ l, FKey.robj X r ∉ K) →
    ▷ rabiaInvAt (GF := GF) γ M ∗ keysOf γ (.srv X) K ⊢
      |={E}=> ⌜∀ r ∈ l, M (.robj X r) = none⌝ ∗
        ▷ rabiaInvAt γ (l.foldr (fun r M' => M'.set (.robj X r) (.obj id)) M) ∗
        keysOf γ (.srv X) (l.map (FKey.robj X) ++ K) ∗ [∗list] r ∈ l, fact γ (.robj X r) (.obj id)
  | [], M, K, _, _ => by
    simp only [List.foldr_nil, List.map_nil, List.nil_append]
    iintro ⟨Hi, HK⟩
    imodintro
    isplitr
    · ipureintro; simp
    iframe Hi HK
    iapply BigSepL.bigSepL_nil.2; iempintro
  | r :: l, M, K, hnd, hK => by
    have hrl : r ∉ l := (List.nodup_cons.mp hnd).1
    have ih := invAt_insert_robjs E γ X id l M K (List.nodup_cons.mp hnd).2
      (fun r' h => hK r' (List.mem_cons_of_mem _ h))
    have hk : FKey.robj X r ∉ l.map (FKey.robj X) ++ K := by
      intro h
      rcases List.mem_append.mp h with h | h
      · obtain ⟨r', hr', e⟩ := List.mem_map.mp h
        cases e
        exact hrl hr'
      · exact hK r List.mem_cons_self h
    have h1 : ∀ id', FKey.robj X r ≠ .pobj id' := by simp
    have h2 : ∀ r', FKey.robj X r ≠ .reg r' := by simp
    have h3 : ∀ t, FKey.robj X r ≠ .dec t := by simp
    simp only [List.foldr_cons, List.map_cons, List.cons_append]
    iintro ⟨Hi, HK⟩
    imod ih $$ [Hi HK] with ⟨%hfree, Hi, HK, Hl⟩
    · iframe
    imod invAt_insert _ γ _ (.robj X r) (.obj id) (.srv X) _ rfl hk h2 h3
      (fun _ _ id' _ => objCmds_set _ _ _ id' h1 h2) (fun _ r' t => reqAt_set _ _ _ r' t h1 h3)
      $$ [Hi HK] with ⟨%hfree1, Hi, HK, #Hf⟩
    · iframe
    imodintro
    isplitr
    · ipureintro
      intro r' hr'
      rcases List.mem_cons.mp hr' with h | h
      · subst h
        rw [foldr_setRobj_apply, ite_eq_right_iff.mpr (fun h => absurd h ?_)] at hfree1
        · exact hfree1
        · intro hm
          obtain ⟨r'', hr'', e⟩ := List.mem_map.mp hm
          cases e
          exact hrl hr''
      · exact hfree r' h
    iframe Hi HK
    iapply BigSepL.bigSepL_cons.2
    iframe Hf Hl

theorem fact_lookup (γ : RabiaNames) (MG : GMap FKey FVal) (k : FKey) (v : FVal) :
    ⊢ ghostMapAuth (GF := GF) γ.facts 1 MG -∗ fact γ k v -∗ ⌜MG.lookup k = some v⌝ := by
  unfold fact
  iintro Ha H
  iapply ghost_map_lookup $$ Ha H

theorem facts_lookup (γ : RabiaNames) (MG : GMap FKey FVal) (S : List (FKey × FVal)) :
    ⊢ ghostMapAuth (GF := GF) γ.facts 1 MG -∗ ([∗list] kv ∈ S, fact γ kv.1 kv.2) -∗
      ⌜∀ kv ∈ S, MG.lookup kv.1 = some kv.2⌝ := by
  induction S with
  | nil => iintro _ _; ipureintro; simp
  | cons a S ih =>
    iintro Ha ⟨Hx, HS⟩
    ihave %h1 := fact_lookup γ MG a.1 a.2 $$ Ha Hx
    ihave %h2 := ih $$ Ha HS
    ipureintro
    intro kv hkv
    rcases List.mem_cons.mp hkv with h | h
    · subst h; exact h1
    · exact h2 kv h

/-- The facts one holds are in the record. -/
theorem invAt_facts (E : CoPset) (γ : RabiaNames) (M : Facts) (S : List (FKey × FVal)) :
    ▷ rabiaInvAt (GF := GF) γ M ∗ □ ([∗list] kv ∈ S, fact γ kv.1 kv.2) ⊢
      |={E}=> ⌜∀ kv ∈ S, M kv.1 = some kv.2⌝ ∗ ▷ rabiaInvAt γ M := by
  iintro ⟨Hi, #HS⟩
  unfold rabiaInvAt
  icases Hi with ⟨%MG, %KS, %n, >Hf, >%HMG, Hrest⟩
  ihave %h := facts_lookup γ MG S $$ Hf HS
  imodintro
  isplitr
  · ipureintro; intro kv hkv; rw [← HMG]; exact h kv hkv
  · inext
    iexists MG, KS, n
    iframe Hf Hrest
    ipureintro; exact HMG

theorem kvHalf_agree (γ : RabiaNames) (L1 L2 : List GoString) :
    ⊢ kvHalf (GF := GF) γ L1 -∗ kvHalf γ L2 -∗ ⌜L1 = L2⌝ := by
  unfold kvHalf
  iintro H1 H2
  iapply ghostVar_agree $$ H1 H2

theorem kvHalf_update (E : CoPset) (γ : RabiaNames) (L1 L2 L : List GoString) :
    kvHalf (GF := GF) γ L1 ∗ kvHalf γ L2 ⊢ |={E}=> kvHalf γ L ∗ kvHalf γ L := by
  unfold kvHalf
  iintro ⟨H1, H2⟩
  imod ghostVar_update_halves L γ.kvs L1 L2 $$ H1 H2 with ⟨H1, H2⟩
  imodintro
  iframe

theorem opsTerm_reg (γ : RabiaNames) (M : Facts) (r : ReqId) :
    opsTerm (GF := GF) γ M (.reg r) = opState γ M r := rfl

theorem lookup_insert_facts (MG : GMap FKey FVal) (M : Facts) (k : FKey) (v : FVal)
    (HMG : ∀ k, MG.lookup k = M k) : ∀ k', (MG.insert k v).lookup k' = M.set k v k' := by
  intro k'
  simp only [GMap.lookup_insert_eq_iff, Facts.set_apply]
  by_cases h : k' = k
  · subst h; simp
  · simp [h, Ne.symm h, HMG]

/-- `Φ` off the keys of the requests `l`. -/
def offReqs (Φ : FKey → IProp GF) (l : List ReqId) (k : FKey) : IProp GF :=
  if k ∈ l.map FKey.reg then iprop(True) else Φ k

theorem bigSepM_offReqs_cons (MG : GMap FKey FVal) (Φ : FKey → IProp GF) (r : ReqId)
    (l : List ReqId) (hr : r ∉ l) (v : FVal) (hv : MG.lookup (.reg r) = some v) :
    ([∗map] k ↦ _x ∈ MG, offReqs Φ l k) ⊣⊢
      Φ (.reg r) ∗ [∗map] k ↦ _x ∈ MG, offReqs Φ (r :: l) k := by
  have e1 : offReqs Φ l (.reg r) = Φ (.reg r) := by
    simp [offReqs, hr]
  have e2 : offReqs Φ (r :: l) (.reg r) = iprop(True) := by
    simp [offReqs]
  have hm : ∀ {k x}, get? (delete MG (FKey.reg r)) k = some x →
      offReqs Φ l k = offReqs Φ (r :: l) k := by
    intro k x hk
    have hne : FKey.reg r ≠ k := ((GMap.lookup_delete_Some MG _ _ _).1 hk).1
    have : k ∉ [FKey.reg r] := by simp [Ne.symm hne]
    simp only [offReqs, List.map_cons]
    by_cases h : k ∈ l.map FKey.reg
    · simp [h]
    · simp only [h, ite_false, List.mem_cons, Ne.symm hne, false_or]
  refine ⟨?_, ?_⟩
  · refine (BigSepM.bigSepM_delete (Φ := fun k (_ : FVal) => offReqs Φ l k) hv).1.trans ?_
    refine BIBase.Entails.trans ?_ (sep_mono .rfl (BigSepM.bigSepM_delete (Φ := fun k (_ : FVal) => offReqs Φ (r :: l) k) hv).2)
    rw [e1, e2, BigSepM.bigSepM_eq hm]
    iintro ⟨H1, H2⟩
    iframe H1 H2
  · refine BIBase.Entails.trans ?_ (BigSepM.bigSepM_delete (Φ := fun k (_ : FVal) => offReqs Φ l k) hv).2
    refine (sep_mono .rfl (BigSepM.bigSepM_delete (Φ := fun k (_ : FVal) => offReqs Φ (r :: l) k) hv).1).trans ?_
    rw [e1, e2, BigSepM.bigSepM_eq hm]
    iintro ⟨H1, -, H2⟩
    iframe H1 H2

theorem bigSepM_split_reqs (MG : GMap FKey FVal) (Φ : FKey → IProp GF) :
    ∀ (l : List ReqId), l.Nodup → (∀ r ∈ l, ∃ v, MG.lookup (.reg r) = some v) →
    (([∗map] k ↦ _x ∈ MG, Φ k) ⊣⊢
      ([∗list] r ∈ l, Φ (.reg r)) ∗ [∗map] k ↦ _x ∈ MG, offReqs Φ l k)
  | [], _, _ => by
    have : ∀ k, offReqs Φ [] k = Φ k := fun k => by simp [offReqs]
    simp only [this]
    refine ⟨?_, ?_⟩
    · iintro H; isplitr
      · iapply BigSepL.bigSepL_nil.2; iempintro
      · iexact H
    · iintro ⟨-, H⟩; iexact H
  | r :: l, hnd, hin => by
    have ih := bigSepM_split_reqs MG Φ l (List.nodup_cons.mp hnd).2
      (fun r' h => hin r' (List.mem_cons_of_mem _ h))
    obtain ⟨v, hv⟩ := hin r List.mem_cons_self
    have hc := bigSepM_offReqs_cons MG Φ r l (List.nodup_cons.mp hnd).1 v hv
    refine ⟨?_, ?_⟩
    · refine ih.1.trans ?_
      iintro ⟨Hl, Hm⟩
      ihave ⟨H1, H2⟩ := hc.1 $$ Hm
      iframe H2
      iapply BigSepL.bigSepL_cons.2
      iframe H1 Hl
    · refine BIBase.Entails.trans ?_ ih.2
      iintro ⟨Hl, Hm⟩
      icases BigSepL.bigSepL_cons.1 $$ Hl with ⟨H1, Hl⟩
      iframe Hl
      iapply hc.2
      iframe H1 Hm

theorem opState_unfold (γ : RabiaNames) (M : Facts) (r : ReqId) :
    opState (GF := GF) γ M r ⊢ iprop(∃ (γq : GName) (i : KvInput GoString GoString),
    ghostMapElem γ.qs r .discard γq ∗ ⌜M (.reg r) = some (.cmd (cmdOf i)) ∧ inputOk i⌝ ∗
    ((⌜∀ s, ¬ ReqAt M r s⌝ ∗ ∃ Q : OpQ GF, savedQ γq Q ∗ opAU γ i Q) ∨
     (∃ s σ L' o, ⌜ReqAt M r s ∧ σ = stateBefore M r s ∧
        (kv GoString GoString).step σ i (stateOfCmds L') o⌝ ∗
       ((∃ Q : OpQ GF, savedQ γq Q ∗ Q σ (stateOfCmds L') o) ∨
        ghostMapElem γ.col r (.own 1) ())))) := .rfl

theorem opState_fold {γ : RabiaNames} {M : Facts} {r : ReqId} :
    iprop(∃ (γq : GName) (i : KvInput GoString GoString),
    ghostMapElem γ.qs r .discard γq ∗ ⌜M (.reg r) = some (.cmd (cmdOf i)) ∧ inputOk i⌝ ∗
    ((⌜∀ s, ¬ ReqAt M r s⌝ ∗ ∃ Q : OpQ GF, savedQ γq Q ∗ opAU γ i Q) ∨
     (∃ s σ L' o, ⌜ReqAt M r s ∧ σ = stateBefore M r s ∧
        (kv GoString GoString).step σ i (stateOfCmds L') o⌝ ∗
       ((∃ Q : OpQ GF, savedQ γq Q ∗ Q σ (stateOfCmds L') o) ∨
        ghostMapElem γ.col r (.own 1) ())))) ⊢ opState (GF := GF) γ M r := .rfl

/-- Committing, in order, the pending operations of the requests `l` of a decided batch `rs`
(`rs = pre ++ l`, the ones of `pre` already committed). -/
theorem commit_batch (E : CoPset) (hcE : cliE ⊆ E)
    (γ : RabiaNames) (M M' : Facts) (s : Nat) (rs : List ReqId) (hnd : rs.Nodup)
    (hreg' : ∀ r, M' (.reg r) = M (.reg r)) (hreq : ∀ r ∈ rs, ReqAt M' r s)
    (hnot : ∀ r ∈ rs, ∀ t, ¬ ReqAt M r t)
    (hst : ∀ r ∈ rs, stateBefore M' r s =
      stateOfCmds (cmdsAt M s ++ (rs.take (rs.idxOf r)).flatMap (regCmd M))) :
    ∀ (l pre : List ReqId), pre ++ l = rs →
      kvHalf (GF := GF) γ (cmdsAt M s ++ pre.flatMap (regCmd M)) ∗ ([∗list] r ∈ l, opState γ M r) ⊢
        |={E}=> kvHalf γ (cmdsAt M s ++ rs.flatMap (regCmd M)) ∗ [∗list] r ∈ l, opState γ M' r := by
  intro l
  induction l with
  | nil =>
    intro pre hpre
    simp only [List.append_nil] at hpre
    subst hpre
    iintro ⟨Hkv, -⟩
    imodintro
    iframe Hkv
    iapply BigSepL.bigSepL_nil.2; iempintro
  | cons r l ih =>
    intro pre hpre
    have hr : r ∈ rs := by rw [← hpre]; simp
    have hidx : rs.take (rs.idxOf r) = pre := by
      subst hpre; exact take_idxOf_nodup pre l r hnd
    iintro ⟨Hkv, Hl⟩
    icases BigSepL.bigSepL_cons.1 $$ Hl with ⟨Hop, Hl⟩
    ihave Hop := opState_unfold γ M r $$ Hop
    icases Hop with ⟨%γq, %i, #Hq, %Hreg, Hop⟩
    icases Hop with (⟨%Hp, %Q, #HsQ, HAU⟩ | ⟨%s', %σ0, %σ1, %o1, %Hs', -⟩)
    rotate_left
    · exact (hnot r hr s' Hs'.1).elim
    have hrc : regCmd M r = [cmdOf i] := by simp [regCmd, Hreg.1]
    unfold opAU
    imod (fupd_mask_subseteq (PROP := IProp GF) hcE) with Hclose
    imod HAU with ⟨%σ, Hσ, Hcommit⟩
    unfold kvState
    icases Hσ with ⟨%L, HL, %HσL⟩
    ihave %HL := kvHalf_agree γ L _ $$ HL Hkv
    subst HL
    imod kvHalf_update _ γ _ _ (cmdsAt M s ++ pre.flatMap (regCmd M) ++ [cmdOf i]) $$ [HL Hkv]
      with ⟨HL, Hkv⟩
    · iframe
    have hstep : (kv GoString GoString).step σ i
        (stateOfCmds (cmdsAt M s ++ pre.flatMap (regCmd M) ++ [cmdOf i])) (outOf σ i) := by
      rw [stateOfCmds_snoc, HσL]; exact execCmd_step _ i Hreg.2
    imod Hcommit $$ %(stateOfCmds (cmdsAt M s ++ pre.flatMap (regCmd M) ++ [cmdOf i]))
        %(outOf σ i) [HL] with HQ
    · isplitl [HL]
      · iexists cmdsAt M s ++ pre.flatMap (regCmd M) ++ [cmdOf i]
        iframe HL
        ipureintro; rfl
      · ipureintro; exact hstep
    imod Hclose
    have hpre' : cmdsAt M s ++ (pre ++ [r]).flatMap (regCmd M) =
        cmdsAt M s ++ pre.flatMap (regCmd M) ++ [cmdOf i] := by
      simp [List.flatMap_append, hrc]
    have ih' := ih (pre ++ [r]) (by rw [← hpre]; simp)
    rw [hpre'] at ih'
    imod ih' $$ [Hkv Hl] with ⟨Hkv, Hl⟩
    · iframe
    imodintro
    iframe Hkv
    iapply BigSepL.bigSepL_cons.2
    isplitr [Hl]
    rotate_left
    · iexact Hl
    iapply opState_fold
    iexists γq, i
    iframe Hq
    isplitr
    · ipureintro; rw [hreg']; exact Hreg
    iright
    iexists s, σ, cmdsAt M s ++ pre.flatMap (regCmd M) ++ [cmdOf i], outOf σ i
    isplitr
    · ipureintro
      refine ⟨hreq r hr, ?_, hstep⟩
      rw [hst r hr, hidx, HσL]
    ileft
    iexists Q
    iframe HsQ HQ

/-- The first decider of slot `s` records its decision `d` (the invariant's body; the later taken
off with a credit): if `d` is an object, the operation of its request is linearized (its atomic
update committed with the model's step at the store of the slots before `s`). -/
theorem invAt_decide (E : CoPset) (hcE : cliE ⊆ E)
    (γ : RabiaNames) (M : Facts) (s : Nat) (d : DVal)
    (hV : Valid M) (hV' : Valid (M.set (.dec s) (.dval d))) (hs : M (.dec s) = none)
    (hprev : s = 0 ∨ M (.dec (s - 1)) ≠ none) :
    £ 1 ∗ ▷ rabiaInvAt (GF := GF) γ M ⊢
      |={E}=> ▷ rabiaInvAt γ (M.set (.dec s) (.dval d)) ∗ fact γ (.dec s) (.dval d) := by
  iintro ⟨Hlc, Hi⟩
  imod lc_fupd_elim_later $$ Hlc Hi with Hi
  unfold rabiaInvAt
  icases Hi with ⟨%MG, %KS, %n, Hf, %HMG, Hfs, Hk, %HKO, Hkw, %Hn, Hkv, HQS, HCS, Hops⟩
  have hsn : s = n := first_undecided hV Hn hs hprev
  subst hsn
  have hMG : MG.lookup (.dec s) = none := by rw [HMG]; exact hs
  imod ghost_map_insert_persist (.dec s) (.dval d) hMG $$ Hf with ⟨Hf, #Hfact⟩
  ihave #Hfact := fact_of_elem γ _ _ $$ Hfact
  -- the record's changes
  have hreg' : ∀ r, (M.set (.dec s) (.dval d)) (.reg r) = M (.reg r) :=
    fun r => Facts.set_ne _ _ (by simp)
  have hpobj' : ∀ id, (M.set (.dec s) (.dval d)) (.pobj id) = M (.pobj id) :=
    fun id => Facts.set_ne _ _ (by simp)
  have hcm : ∀ t ≤ s, cmdsAt (M.set (.dec s) (.dval d)) t = cmdsAt M t :=
    fun t ht => cmdsAt_setdec M s _ t ht
  have hReqOld : ∀ r t, ReqAt M r t → t < s ∧ ReqAt (M.set (.dec s) (.dval d)) r t := by
    rintro r t ⟨id, rs, h1, h2, h3⟩
    have ht : t < s := dec_lt hV Hn (by simp [h1])
    refine ⟨ht, id, rs, ?_, by rw [hpobj']; exact h2, h3⟩
    rw [Facts.set_ne _ _ (by simp; omega)]; exact h1
  have hReqNew : ∀ r t, ReqAt (M.set (.dec s) (.dval d)) r t → t ≠ s → ReqAt M r t := by
    rintro r t ⟨id, rs, h1, h2, h3⟩ ht
    rw [Facts.set_ne _ _ (by simp [ht])] at h1
    rw [hpobj'] at h2
    exact ⟨id, rs, h1, h2, h3⟩
  have hstable : ∀ r, ¬ ReqAt (M.set (.dec s) (.dval d)) r s →
      OpStable M (M.set (.dec s) (.dval d)) r := by
    intro r hr
    refine ⟨hreg' r, fun t => ⟨fun h => hReqNew r t h (fun e => hr (e ▸ h)),
      fun h => (hReqOld r t h).2⟩, fun t h => ?_⟩
    have ht := (hReqOld r t h).1
    unfold stateBefore
    rw [hcm t (Nat.le_of_lt ht),
      cmdsBefore_congr (Facts.set_ne _ _ (by simp; omega)) (fun id _ => hpobj' id) hreg']
  have hKO' := keysOk_insert_none (.dval d) HKO (k := .dec s) rfl
  have hn' := nDec_setdec hV Hn (.dval d)
  have hMG' := lookup_insert_facts MG M (.dec s) (.dval d) HMG
  cases d with
  | null =>
    have hcmd : cmdsAt (M.set (.dec s) (.dval .null)) (s + 1) = cmdsAt M s := by
      rw [cmdsAt_succ, hcm s (Nat.le_refl _)]
      simp [slotCmds, Facts.set_self, dcmds]
    imodintro
    iframe Hfact
    inext
    iexists MG.insert (.dec s) (.dval .null), KS, s + 1
    iframe Hf Hk Hkw
    rw [hcmd]
    iframe Hkv
    isplitr
    · ipureintro; exact hMG'
    isplitl [Hfs]
    · iapply (BigSepM.bigSepM_insert (Φ := fun k v => fact (GF := GF) γ k v) hMG).2
      iframe Hfact
      iexact Hfs
    isplitr
    · ipureintro; exact hKO'
    isplitr
    · ipureintro; exact hn'
    isplitl [HQS]
    · icases HQS with ⟨%QS, HQS, %HQ⟩
      iexists QS
      iframe HQS
      ipureintro; intro r; rw [hreg']; exact HQ r
    isplitl [HCS]
    · icases HCS with ⟨%CS, HCS, %HC⟩
      iexists CS
      iframe HCS
      ipureintro; intro r; rw [hreg']; exact HC r
    · iapply (BigSepM.bigSepM_insert
        (Φ := fun k' _ => opsTerm (GF := GF) γ (M.set (.dec s) (.dval .null)) k') hMG).2
      rw [opsTerm_nonreg γ _ (.dec s) (fun _ => by simp)]
      isplitr
      · itrivial
      iapply ops_stable γ M _ MG ?_ $$ Hops
      intro r _ _
      apply hstable
      rintro ⟨id, rs, h1, -⟩
      simp [Facts.set_self] at h1
  | obj id =>
    obtain ⟨rs, hr0⟩ := valid_dec_pobj hV' (t := s) (id := id) (Facts.set_self _ _ _)
    rw [hpobj'] at hr0
    have hnd : rs.Nodup := valid_pobj_nodup hV hr0
    obtain ⟨c, -, hcOk, hVc'⟩ | h0 := valid_cases hV'
    rotate_left
    · exact absurd (h0 (.dec s)) (by simp [Facts.set_self])
    have hReq0 : ∀ r ∈ rs, ReqAt (M.set (.dec s) (.dval (.obj id))) r s :=
      fun r hr => ⟨id, rs, Facts.set_self _ _ _, by rw [hpobj']; exact hr0, hr⟩
    have hnot : ∀ r ∈ rs, ∀ t, ¬ ReqAt M r t := by
      intro r hr t ht
      obtain ⟨hlt, id1, rs1, h1, h2, h3⟩ := hReqOld r t ht
      have := atMostOnceReq _ hcOk hVc' t s id1 id rs1 rs r h1 (Facts.set_self _ _ _) h2
        (by rw [hpobj']; exact hr0) h3 hr
      omega
    have hst : ∀ r ∈ rs, stateBefore (M.set (.dec s) (.dval (.obj id))) r s =
        stateOfCmds (cmdsAt M s ++ (rs.take (rs.idxOf r)).flatMap (regCmd M)) := by
      intro r _
      simp only [stateBefore, cmdsBefore, Facts.set_self, hpobj', hr0, hcm s (Nat.le_refl _),
        regCmd_congr hreg']
      rfl
    have hin : ∀ r ∈ rs, ∃ v, MG.lookup (.reg r) = some v := by
      intro r hr
      obtain ⟨cm, hcm⟩ := valid_pobj_reg hV hr0 hr
      exact ⟨_, by rw [HMG]; exact hcm⟩
    have hsplit := bigSepM_split_reqs MG (opsTerm (GF := GF) γ M) rs hnd hin
    have hsplit' := bigSepM_split_reqs MG
      (opsTerm (GF := GF) γ (M.set (.dec s) (.dval (.obj id)))) rs hnd hin
    simp only [opsTerm_reg] at hsplit hsplit'
    have hcb := commit_batch (GF := GF) E hcE γ M (M.set (.dec s) (.dval (.obj id))) s rs hnd
      hreg' hReq0 hnot hst rs [] (by simp)
    simp only [List.flatMap_nil, List.append_nil] at hcb
    icases hsplit.1 $$ Hops with ⟨Hl, Hops⟩
    imod hcb $$ [Hkv Hl] with ⟨Hkv, Hl⟩
    · iframe
    have hcmd : cmdsAt (M.set (.dec s) (.dval (.obj id))) (s + 1) =
        cmdsAt M s ++ rs.flatMap (regCmd M) := by
      rw [cmdsAt_succ, hcm s (Nat.le_refl _)]
      simp [slotCmds, Facts.set_self, dcmds, objCmds, hpobj', hr0, regCmd_congr hreg']
    imodintro
    iframe Hfact
    inext
    iexists MG.insert (.dec s) (.dval (.obj id)), KS, s + 1
    iframe Hf Hk Hkw
    rw [hcmd]
    iframe Hkv
    isplitr
    · ipureintro; exact hMG'
    isplitl [Hfs]
    · iapply (BigSepM.bigSepM_insert (Φ := fun k v => fact (GF := GF) γ k v) hMG).2
      iframe Hfact
      iexact Hfs
    isplitr
    · ipureintro; exact hKO'
    isplitr
    · ipureintro; exact hn'
    isplitl [HQS]
    · icases HQS with ⟨%QS, HQS, %HQ⟩
      iexists QS
      iframe HQS
      ipureintro; intro r; rw [hreg']; exact HQ r
    isplitl [HCS]
    · icases HCS with ⟨%CS, HCS, %HC⟩
      iexists CS
      iframe HCS
      ipureintro; intro r; rw [hreg']; exact HC r
    · iapply (BigSepM.bigSepM_insert
        (Φ := fun k' _ => opsTerm (GF := GF) γ (M.set (.dec s) (.dval (.obj id))) k') hMG).2
      rw [opsTerm_nonreg γ _ (.dec s) (fun _ => by simp)]
      isplitr
      · itrivial
      iapply hsplit'.2
      iframe Hl
      iapply BigSepM.bigSepM_mono ?_ $$ Hops
      intro k v _
      unfold offReqs
      by_cases hk : k ∈ rs.map FKey.reg
      · simp only [hk, ite_true]; exact .rfl
      · simp only [hk, ite_false]
        cases k with
        | reg r =>
          apply opState_stable
          apply hstable
          rintro ⟨id', rs', h1, h2, h3⟩
          simp only [Facts.set_self, Option.some.injEq, FVal.dval.injEq, DVal.obj.injEq] at h1
          subst h1
          rw [hpobj', hr0] at h2
          cases h2
          exact hk (List.mem_map_of_mem h3)
        | _ => exact .rfl

/-- The fact of a recorded key, from the invariant's copy. -/
theorem invAt_fact (E : CoPset) (γ : RabiaNames) (M : Facts) (k : FKey) (v : FVal)
    (h : M k = some v) :
    ▷ rabiaInvAt (GF := GF) γ M ⊢ |={E}=> fact γ k v ∗ ▷ rabiaInvAt γ M := by
  iintro Hi
  unfold rabiaInvAt
  icases Hi with ⟨%MG, %KS, %n, Hf, >%HMG, >Hfs, Hrest⟩
  have hk : MG.lookup k = some v := by rw [HMG]; exact h
  icases (BigSepM.bigSepM_lookup_acc (Φ := fun k v => fact (GF := GF) γ k v) hk).1 $$ Hfs
    with ⟨#Hx, Hcl⟩
  ihave Hfs := Hcl $$ Hx
  imodintro
  iframe Hx
  inext
  iexists MG, KS, n
  iframe Hf Hfs Hrest
  ipureintro; exact HMG

theorem mask_client (E : CoPset) (hcl : cliE ## ↑rabiaN)
    (hcE : cliE ⊆ E) :
    cliE ⊆ E \ ↑rabiaN := by
  intro x hx
  rw [LawfulSet.mem_diff]
  exact ⟨hcE x hx, fun h => hcl x ⟨hx, h⟩⟩

/-- A fact one holds is in the record. -/
theorem invAt_fact_in (E : CoPset) (γ : RabiaNames) (M : Facts) (k : FKey) (v : FVal) :
    ▷ rabiaInvAt (GF := GF) γ M ∗ fact γ k v ⊢
      |={E}=> ⌜M k = some v⌝ ∗ ▷ rabiaInvAt γ M := by
  iintro ⟨Hi, #Hx⟩
  unfold rabiaInvAt
  icases Hi with ⟨%MG, %KS, %n, >Hf, >%HMG, Hrest⟩
  ihave %h := fact_lookup γ MG k v $$ Hf Hx
  imodintro
  isplitr
  · ipureintro; rw [← HMG]; exact h
  · inext
    iexists MG, KS, n
    iframe Hf Hrest
    ipureintro; exact HMG

theorem savedQ_alloc (E : CoPset) (Q : OpQ GF) : ⊢ |={E}=> ∃ γq, savedQ (GF := GF) γq Q := by
  unfold savedQ
  imod saved_pred_alloc (fun x : List GoString × List GoString × KvOutput GoString =>
      Q (stateOfCmds x.1) (stateOfCmds x.2.1) x.2.2) DFrac.discard DFrac.valid_discard with ⟨%γq, H⟩
  imodintro
  iexists γq
  iexact H

/-- Client `c` registers the free request `(c, n)` with the command of `i`, depositing its
operation's atomic update (the invariant's body, under the later). -/
theorem invAt_register (E : CoPset) (γ : RabiaNames) (M : Facts) (hV : Valid M) (c n : Nat)
    (K : List FKey) (hk : FKey.reg (c, n) ∉ K) (i : KvInput GoString GoString) (hi : inputOk i)
    (Q : OpQ GF) :
    ▷ rabiaInvAt (GF := GF) γ M ∗ keysOf γ (.cli c) K ∗ opAU γ i Q ⊢
      |={E}=> ⌜M (.reg (c, n)) = none⌝ ∗ ▷ rabiaInvAt γ (M.set (.reg (c, n)) (.cmd (cmdOf i))) ∗
        keysOf γ (.cli c) (.reg (c, n) :: K) ∗ fact γ (.reg (c, n)) (.cmd (cmdOf i)) ∗
        (∃ γq, ghostMapElem γ.qs (c, n) .discard γq ∗ savedQ γq Q) ∗
        ghostMapElem γ.col (c, n) (.own 1) () := by
  iintro ⟨Hi, HK, HAU⟩
  unfold rabiaInvAt
  icases Hi with ⟨%MG, %KS, %n0, >Hf, >%HMG, >Hfs, >Hk, >%HKO, >Hkw, >%Hn, >Hkv,
    >HQS, >HCS, Hops⟩
  icases HQS with ⟨%QS, HQS, %HQ⟩
  icases HCS with ⟨%CS, HCS, %HC⟩
  ihave %HKl := keysOf_lookup γ KS _ K $$ Hk HK
  have hfree : M (.reg (c, n)) = none := keysOk_free HKO rfl HKl hk
  have hMG : MG.lookup (.reg (c, n)) = none := by rw [HMG]; exact hfree
  have hQS : QS.lookup (c, n) = none := by
    cases h : QS.lookup (c, n) with
    | none => rfl
    | some _ => exact absurd hfree ((HQ (c, n)).1 (by simp [h]))
  have hCS : CS.lookup (c, n) = none := by
    cases h : CS.lookup (c, n) with
    | none => rfl
    | some _ => exact absurd hfree ((HC (c, n)).1 (by simp [h]))
  imod keysOf_update E γ KS _ K (.reg (c, n) :: K) HKl $$ [Hk Hkw HK] with ⟨Hk, Hkw, HK⟩
  · iframe
  imod ghost_map_insert_persist (.reg (c, n)) (.cmd (cmdOf i)) hMG $$ Hf with ⟨Hf, #Hfact⟩
  ihave #Hfact := fact_of_elem γ _ _ $$ Hfact
  imod savedQ_alloc E Q with ⟨%γq, #HsQ⟩
  imod ghost_map_insert_persist (c, n) γq hQS $$ HQS with ⟨HQS, #Hq⟩
  imod ghost_map_insert (c, n) () hCS $$ HCS with ⟨HCS, Hcol⟩
  -- no object carries the new request
  have hnopobj : ∀ id rs, M (.pobj id) = some (.reqs rs) → (c, n) ∉ rs := by
    intro id rs h hm
    obtain ⟨c', h'⟩ := valid_pobj_reg hV h hm
    rw [hfree] at h'; cases h'
  have hregs : ∀ id rs, M (.pobj id) = some (.reqs rs) → ∀ r' ∈ rs,
      (M.set (.reg (c, n)) (.cmd (cmdOf i))) (.reg r') = M (.reg r') := by
    intro id rs h r' hr'
    refine Facts.set_ne _ _ (fun e => ?_)
    cases e
    exact hnopobj id rs h hr'
  have hobj : ∀ id, objCmds (M.set (.reg (c, n)) (.cmd (cmdOf i))) id = objCmds M id := by
    intro id
    simp only [objCmds, Facts.set_ne _ _ (show FKey.pobj id ≠ .reg (c, n) by simp)]
    cases h : M (.pobj id) with
    | none => rfl
    | some v =>
      cases v with
      | reqs rs => exact flatMap_regCmd_congr rs (hregs id rs h)
      | _ => rfl
  have hr1 : ∀ id, FKey.reg (c, n) ≠ .pobj id := by simp
  have hr3 : ∀ t, FKey.reg (c, n) ≠ .dec t := by simp
  have hreq := fun r t => reqAt_set M (.reg (c, n)) (.cmd (cmdOf i)) r t hr1 hr3
  have hc := cmdsAt_stable (M := M) (M' := M.set (.reg (c, n)) (.cmd (cmdOf i)))
    (fun t => Facts.set_ne _ _ (by simp)) (fun _ id _ => hobj id)
  imodintro
  iframe HK Hfact Hcol
  isplitr
  · ipureintro; exact hfree
  isplitl [Hf Hfs Hk Hkw Hkv HQS HCS Hops HAU]
  · inext
    iexists MG.insert (.reg (c, n)) (.cmd (cmdOf i)), KS.insert (.cli c) (.reg (c, n) :: K), n0
    iframe Hf Hk Hkw
    rw [hc]
    iframe Hkv
    isplitr
    · ipureintro; exact lookup_insert_facts MG M _ _ HMG
    isplitl [Hfs]
    · iapply (BigSepM.bigSepM_insert (Φ := fun k v => fact (GF := GF) γ k v) hMG).2
      iframe Hfact
      iexact Hfs
    isplitr
    · ipureintro; exact keysOk_insert _ HKO rfl HKl
    isplitr
    · ipureintro
      exact ⟨fun t ht => by rw [Facts.set_ne _ _ (by simp)]; exact Hn.1 t ht,
        by rw [Facts.set_ne _ _ (by simp)]; exact Hn.2⟩
    isplitl [HQS]
    · iexists QS.insert (c, n) γq
      iframe HQS
      ipureintro; intro r
      by_cases h : r = (c, n)
      · subst h; simp [Facts.set_self]
      · rw [GMap.lookup_insert_ne _ _ (Ne.symm h),
          Facts.set_ne _ _ (by simp [h])]
        exact HQ r
    isplitl [HCS]
    · iexists CS.insert (c, n) ()
      iframe HCS
      ipureintro; intro r
      by_cases h : r = (c, n)
      · subst h; simp [Facts.set_self]
      · rw [GMap.lookup_insert_ne _ _ (Ne.symm h),
          Facts.set_ne _ _ (by simp [h])]
        exact HC r
    · iapply (BigSepM.bigSepM_insert
        (Φ := fun k' _ => opsTerm (GF := GF) γ (M.set (.reg (c, n)) (.cmd (cmdOf i))) k') hMG).2
      isplitl [HAU]
      · rw [opsTerm_reg]
        unfold opState
        iexists γq, i
        iframe Hq
        isplitr
        · ipureintro; exact ⟨Facts.set_self _ _ _, hi⟩
        ileft
        isplitr
        · ipureintro
          rintro t ⟨id, rs, -, h2, h3⟩
          rw [Facts.set_ne _ _ (by simp)] at h2
          exact hnopobj id rs h2 h3
        iexists Q
        iframe HsQ HAU
      · iapply ops_stable γ M _ MG ?_ $$ Hops
        intro r v hrv
        have hne : r ≠ (c, n) := by
          intro e; subst e; rw [hMG] at hrv; cases hrv
        refine ⟨Facts.set_ne _ _ (by simp [hne]), hreq r, fun t _ => ?_⟩
        unfold stateBefore
        rw [hc t, cmdsBefore_congr' (Facts.set_ne _ _ (by simp)) (fun id _ => Facts.set_ne _ _ (by simp))
          (fun id rs _ h => hregs id rs h)]
  · iexists γq
    iframe Hq HsQ

theorem regList_facts (γ : RabiaNames) :
    ∀ (rs : List ReqId) (bc : List GoString), rs.length = bc.length →
    ([∗list] i ↦ r ∈ rs, ∃ cm, ⌜bc[i]? = some cm⌝ ∗ fact (GF := GF) γ (.reg r) (.cmd cm)) ⊢
      ∃ S : List (FKey × FVal), ([∗list] kv ∈ S, fact γ kv.1 kv.2) ∗
        ⌜(∀ M : Facts, (∀ kv ∈ S, M kv.1 = some kv.2) →
          ∀ j, (rs.take j).flatMap (regCmd M) = bc.take j) ∧
         ∀ r ∈ rs, ∃ cm, (FKey.reg r, FVal.cmd cm) ∈ S⌝
  | [], bc, hl => by
    have : bc = [] := by simpa using hl.symm
    subst this
    iintro -
    iexists []
    isplitr
    · iapply BigSepL.bigSepL_nil.2; iempintro
    · ipureintro; exact ⟨fun M _ j => by simp, fun r h => by simp at h⟩
  | r :: rs, [], hl => by simp at hl
  | r :: rs, b :: bc, hl => by
    have ih := regList_facts γ rs bc (by simpa using hl)
    refine BigSepL.bigSepL_cons.1.trans ?_
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq]
    iintro ⟨⟨%cm, %hcm, #H1⟩, Hl⟩
    subst hcm
    ihave ⟨%S, HS, %hS⟩ := ih $$ Hl
    iexists (FKey.reg r, FVal.cmd b) :: S
    isplitl [HS]
    · iapply BigSepL.bigSepL_cons.2
      iframe H1 HS
    · ipureintro
      refine ⟨fun M hM j => ?_, fun r' hr' => ?_⟩
      · have h1 := hM _ List.mem_cons_self
        simp only at h1
        cases j with
        | zero => simp
        | succ j =>
          simp only [List.take_succ_cons, List.flatMap_cons, regCmd, h1]
          rw [hS.1 M (fun kv h => hM kv (List.mem_cons_of_mem _ h))]
          rfl
      · rcases List.mem_cons.mp hr' with h | h
        · subst h; exact ⟨b, List.mem_cons_self⟩
        · obtain ⟨cm, hcm⟩ := hS.2 r' h
          exact ⟨cm, List.mem_cons_of_mem _ hcm⟩

/-- The facts of a batch's registrations: they determine the batch's commands (and each prefix's),
and each request is registered. -/
theorem regFacts_facts (γ : RabiaNames) (rs : List ReqId) (bc : List GoString) :
    regFacts (GF := GF) γ rs bc ⊢
      ∃ S : List (FKey × FVal), ([∗list] kv ∈ S, fact γ kv.1 kv.2) ∗
        ⌜(∀ M : Facts, (∀ kv ∈ S, M kv.1 = some kv.2) →
          ∀ j, (rs.take j).flatMap (regCmd M) = bc.take j) ∧
         (∀ r ∈ rs, ∃ cm, (FKey.reg r, FVal.cmd cm) ∈ S) ∧ rs.length = bc.length⌝ := by
  unfold regFacts
  iintro ⟨%hl, Hl⟩
  ihave ⟨%S, HS, %hS⟩ := regList_facts γ rs bc hl $$ Hl
  iexists S
  iframe HS
  ipureintro
  exact ⟨hS.1, hS.2, hl⟩

theorem regFacts_cmds {S : List (FKey × FVal)} {rs : List ReqId} {bc : List GoString}
    (hS : (∀ M : Facts, (∀ kv ∈ S, M kv.1 = some kv.2) →
          ∀ j, (rs.take j).flatMap (regCmd M) = bc.take j) ∧
         (∀ r ∈ rs, ∃ cm, (FKey.reg r, FVal.cmd cm) ∈ S) ∧ rs.length = bc.length)
    (M : Facts) (hM : ∀ kv ∈ S, M kv.1 = some kv.2) : rs.flatMap (regCmd M) = bc := by
  have := hS.1 M hM rs.length
  rw [List.take_length, hS.2.2, List.take_length] at this
  exact this

theorem prefixFacts_facts (γ : RabiaNames) (s : Nat) (cmds : List GoString) :
    prefixFacts (GF := GF) γ s cmds ⊢
      ∃ S : List (FKey × FVal), ([∗list] kv ∈ S, fact γ kv.1 kv.2) ∗
        ⌜∀ M : Facts, (∀ kv ∈ S, M kv.1 = some kv.2) → cmdsAt M s = cmds⌝ := by
  induction s generalizing cmds with
  | zero =>
    unfold prefixFacts
    iintro %h
    iexists []
    isplitr
    · iapply BigSepL.bigSepL_nil.2
      iempintro
    · ipureintro; intro M _; rw [h]; rfl
  | succ s ih =>
    unfold prefixFacts
    iintro ⟨%cmds0, %d, Hp, #Hd, Hm⟩
    ihave ⟨%S0, HS0, %hS0⟩ := ih cmds0 $$ Hp
    cases d with
    | null =>
      icases Hm with %hc
      iexists (FKey.dec s, FVal.dval .null) :: S0
      isplitl [HS0]
      · iapply BigSepL.bigSepL_cons.2
        iframe Hd HS0
      · ipureintro
        intro M hM
        have h1 := hM _ List.mem_cons_self
        rw [cmdsAt_succ, hS0 M (fun kv h => hM kv (List.mem_cons_of_mem _ h)), hc]
        simp only at h1
        simp [slotCmds, h1, dcmds]
    | obj id =>
      icases Hm with ⟨%rs, %bc, #Hpo, #Hreg, %hc⟩
      ihave ⟨%S1, HS1, %hS1⟩ := regFacts_facts γ rs bc $$ Hreg
      iexists (FKey.dec s, FVal.dval (.obj id)) :: (FKey.pobj id, FVal.reqs rs) :: (S1 ++ S0)
      isplitl [HS0 HS1]
      · iapply BigSepL.bigSepL_cons.2
        iframe Hd
        iapply BigSepL.bigSepL_cons.2
        iframe Hpo
        iapply BigSepL.bigSepL_append.2
        iframe HS1 HS0
      · ipureintro
        intro M hM
        have h1 := hM _ List.mem_cons_self
        have h2 := hM (FKey.pobj id, FVal.reqs rs) (by simp)
        rw [cmdsAt_succ, hS0 M (fun kv h => hM kv (by simp [h])), hc]
        simp only at h1 h2
        simp only [slotCmds, h1, dcmds, objCmds, h2]
        rw [regFacts_cmds hS1 M (fun kv h => hM kv (by simp [h]))]

theorem cmdOf_inj {i i' : KvInput GoString GoString} (hi : inputOk i) (hi' : inputOk i')
    (h : cmdOf i = cmdOf i') : i = i' := by
  cases i with
  | put k v =>
    cases i' with
    | put k' v' =>
      simp only [cmdOf, putCmd] at h
      have hk : (48#8 :: k).length = (48#8 :: k').length := by simp [hi.1, hi'.1]
      obtain ⟨h1, h2⟩ := List.append_inj h hk
      simp only [List.cons.injEq, _root_.true_and] at h1
      rw [h1, h2]
    | get k' => simp [cmdOf, putCmd, getCmd] at h
  | get k =>
    cases i' with
    | put k' v' => simp [cmdOf, putCmd, getCmd] at h
    | get k' =>
      simp only [cmdOf, getCmd, List.cons.injEq, _root_.true_and] at h
      rw [h]

instance : Inhabited (KvInput GoString GoString) := ⟨.get []⟩
instance : Inhabited (KvOutput GoString) := ⟨.done⟩
instance : Inhabited (kv GoString GoString).Output := ⟨KvOutput.done⟩
instance : Inhabited (kv GoString GoString).State := ⟨fun _ => none⟩

/-- Collecting request `r`'s commit postcondition from its operation (decided at slot `s`, the
only one): the operation keeps the client's token instead. -/
theorem opState_collect (E : CoPset) (γ : RabiaNames) (M : Facts) (r : ReqId) (s : Nat)
    (i : KvInput GoString GoString) (hi : inputOk i) (Q : OpQ GF) (γq : GName)
    (cmds : List GoString)
    (hreq : ReqAt M r s) (hreg : M (.reg r) = some (.cmd (cmdOf i)))
    (hamo : ∀ s', ReqAt M r s' → s' = s) (hst : stateBefore M r s = stateOfCmds cmds) :
    opState (GF := GF) γ M r ∗ ghostMapElem γ.col r (.own 1) () ∗
      □ ghostMapElem γ.qs r .discard γq ∗ □ savedQ γq Q ⊢
      |={E}=> ▷ opState γ M r ∗
        ▷ ∃ σ' o, ⌜(kv GoString GoString).step (stateOfCmds cmds) i σ' o⌝ ∗
          Q (stateOfCmds cmds) σ' o := by
  iintro ⟨Hop, Hcol, #Hq, #HsQ⟩
  unfold opState
  icases Hop with ⟨%γq', %i', #Hq', %Hreg', Hop⟩
  ihave %hγ := ghostMapElem_agree r γ.qs _ _ γq γq' $$ Hq Hq'
  subst hγ
  have hii : i = i' := by
    rw [hreg] at Hreg'
    obtain ⟨h1, h2⟩ := Hreg'
    simp only [Option.some.injEq, FVal.cmd.injEq] at h1
    exact cmdOf_inj hi h2 h1
  subst hii
  icases Hop with (⟨%Hp, -⟩ | ⟨%s', %σ, %L', %o, %Hs, Hdone⟩)
  · exact (Hp s hreq).elim
  obtain ⟨h1, h2, h3⟩ := Hs
  have := hamo s' h1
  subst this
  subst h2
  rw [hst] at h3 ⊢
  icases Hdone with (⟨%Q', #HsQ', HQ'⟩ | Hcol')
  · unfold savedQ
    ihave Heq := saved_pred_agree (A := List GoString × List GoString × KvOutput GoString) γq _ _ _ _
      ((cmds, L', o) : List GoString × List GoString × KvOutput GoString) $$ HsQ HsQ'
    imodintro
    isplitl [Hcol]
    · inext
      iexists γq, i
      iframe Hq'
      isplitr
      · ipureintro; exact ⟨hreg, hi⟩
      iright
      iexists s', stateOfCmds cmds, L', o
      isplitr
      · ipureintro; exact ⟨h1, hst.symm, h3⟩
      iright
      iexact Hcol
    · inext
      iexists stateOfCmds L', o
      isplitr
      · ipureintro; exact h3
      haveI : OFE.NonExpansive (fun x : IProp GF => x) := ⟨fun _ _ _ h => h⟩
      irewrite [Heq]
      iexact HQ'
  · ihave %hne := ghostMapElem_ne γ.col r r _ () () $$ Hcol Hcol'
    exact (hne rfl).elim

end invlemmas

/-! ## The laws (statements; proved in Prove) -/

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF]

attribute [local instance] GooseGlobalGS.gooseInvGS GooseGlobalGS.gooseAllG

/-- Two recorded values of a key are the same. -/
theorem fact_agree (γ : RabiaNames) (k : FKey) (v v' : FVal) :
    fact (GF := GF) γ k v ∗ fact γ k v' ⊢ ⌜v = v'⌝ := by
  unfold fact
  iintro ⟨H1, H2⟩
  iapply ghostMapElem_agree $$ H1 H2

/-- Recorded facts belong to a valid record (so the theorems of `Protocol.lean` apply to them). -/
theorem facts_valid (γ : RabiaNames) (E : CoPset) (hE : ↑rabiaN ⊆ E) (S : List (FKey × FVal)) :
    isRabia (GF := GF) γ ∗ ([∗list] kv ∈ S, fact γ kv.1 kv.2) ⊢
      |={E}=> ⌜∃ M, Valid M ∧ ∀ kv ∈ S, M kv.1 = some kv.2⌝ := by
  unfold isRabia
  iintro ⟨#Hinv, #HS⟩
  imod inv_acc hE $$ Hinv with ⟨Hi, Hclose⟩
  unfold rabiaInv
  icases Hi with ⟨%M, >%HV, Hi⟩
  imod invAt_facts _ γ M S $$ [Hi HS] with ⟨%h, Hi⟩
  · iframe Hi; imodintro; iexact HS
  imod Hclose $$ [Hi] with -
  · inext
    iexists M
    iframe Hi
    ipureintro; exact HV
  imodintro
  ipureintro
  exact ⟨M, HV, h⟩

/-- A writer records the fact `k = v`, justified (with the rules) in every valid record that has
the facts `S` it holds and not yet `k`. -/
theorem fact_insert (γ : RabiaNames) (E : CoPset) (hE : ↑rabiaN ⊆ E) (W : Writer) (K : List FKey)
    (k : FKey) (v : FVal) (S : List (FKey × FVal)) (hW : k.writer = some W) (hk : k ∉ K)
    (hkind : ∀ r id X s, k ≠ .reg r ∧ k ≠ .pobj id ∧ k ≠ .robj X r ∧ k ≠ .mydec X s ∧
      k ≠ .cfg)
    (hJ : ∀ M, Valid M → (∀ kv ∈ S, M kv.1 = some kv.2) → M k = none →
      Valid (M.set k v)) :
    isRabia (GF := GF) γ ∗ keysOf γ W K ∗ ([∗list] kv ∈ S, fact γ kv.1 kv.2) ⊢
      |={E}=> keysOf γ W (k :: K) ∗ fact γ k v := by
  unfold isRabia
  iintro ⟨#Hinv, HK, #HS⟩
  imod inv_acc hE $$ Hinv with ⟨Hi, Hclose⟩
  unfold rabiaInv
  icases Hi with ⟨%M, >%HV, Hi⟩
  imod invAt_facts _ γ M S $$ [Hi HS] with ⟨%hS, Hi⟩
  · iframe Hi; imodintro; iexact HS
  have h1 : ∀ id, k ≠ .pobj id := fun id => (hkind (0, 0) id 0 0).2.1
  have h2 : ∀ r, k ≠ .reg r := fun r => (hkind r (0, 0) 0 0).1
  have h3 : ∀ s, k ≠ .dec s := fun s h => by subst h; simp [model.FKey.writer] at hW
  imod invAt_insert _ γ M k v W K hW hk h2 h3
    (fun _ t id _ => objCmds_set M k v id h1 h2) (fun _ r s => reqAt_set M k v r s h1 h3)
    $$ [Hi HK] with ⟨%hfree, Hi, HK, #Hf⟩
  · iframe
  imod Hclose $$ [Hi] with -
  · inext
    iexists M.set k v
    iframe Hi
    ipureintro; exact hJ M HV hS hfree
  imodintro
  iframe HK
  iexact Hf

/-- Proxy `X` records its new object `(X, q)` carrying the batch `rs` of registered requests of
its clients (`r.1 % c.n = X`), in order, with their commands `bc` (`CmdReceiver`'s batch), and,
for each request, that it is in `(X, q)`. -/
theorem newObj (γ : RabiaNames) (E : CoPset) (hE : ↑rabiaN ⊆ E) (c : RCfg) (X q : Nat)
    (K : List FKey) (rs : List ReqId) (bc : List GoString) (hne : rs ≠ []) (hnd : rs.Nodup)
    (hX : ∀ r ∈ rs, r.1 % c.n = X) (hq : FKey.pobj (X, q) ∉ K)
    (hr : ∀ r ∈ rs, FKey.robj X r ∉ K) :
    isRabia (GF := GF) γ ∗ cfgIs γ c ∗ keysOf γ (.srv X) K ∗ regFacts γ rs bc ⊢
      |={E}=> keysOf γ (.srv X) (rs.map (FKey.robj X) ++ .pobj (X, q) :: K) ∗
        fact γ (.pobj (X, q)) (.reqs rs) ∗ [∗list] r ∈ rs, fact γ (.robj X r) (.obj (X, q)) := by
  unfold isRabia
  iintro ⟨#Hinv, #Hcf, HK, #Hrf⟩
  ihave ⟨%S1, #HS1, %hS1⟩ := regFacts_facts γ rs bc $$ Hrf
  imod inv_acc hE $$ Hinv with ⟨Hi, Hclose⟩
  unfold rabiaInv
  icases Hi with ⟨%M, >%HV, Hi⟩
  imod invAt_facts _ γ M S1 $$ [Hi HS1] with ⟨%hSM1, Hi⟩
  · iframe Hi; imodintro; iexact HS1
  unfold cfgIs
  icases Hcf with ⟨#Hcf, %hcOk⟩
  imod invAt_fact_in _ γ M _ _ $$ [Hi Hcf] with ⟨%hcfM, Hi⟩
  · iframe Hi; iexact Hcf
  -- the new object's key is not a decided object's
  have hnodec : M (.pobj (X, q)) = none → ∀ t, M (.dec t) ≠ some (.dval (.obj (X, q))) := by
    intro h t ht
    obtain ⟨rs', hr'⟩ := valid_dec_pobj HV ht
    rw [h] at hr'; cases hr'
  have hregs : ∀ r, (M.set (.pobj (X, q)) (.reqs rs)) (.reg r) = M (.reg r) :=
    fun r => Facts.set_ne _ _ (by simp)
  have hobj1 : M (.pobj (X, q)) = none → ∀ t id, M (.dec t) = some (.dval (.obj id)) →
      objCmds (M.set (.pobj (X, q)) (.reqs rs)) id = objCmds M id := by
    intro h t id ht
    have hne : FKey.pobj id ≠ .pobj (X, q) := by
      intro e; cases e; exact hnodec h t ht
    unfold objCmds
    rw [Facts.set_ne _ _ hne, regCmd_congr hregs]
  have hreq1 : M (.pobj (X, q)) = none → ∀ r' t,
      ReqAt (M.set (.pobj (X, q)) (.reqs rs)) r' t ↔ ReqAt M r' t := by
    intro h r' t
    constructor
    · rintro ⟨id, rs', h1, h2, h3⟩
      rw [Facts.set_ne _ _ (by simp)] at h1
      have hne : FKey.pobj id ≠ .pobj (X, q) := by
        intro e; cases e; exact hnodec h t h1
      rw [Facts.set_ne _ _ hne] at h2
      exact ⟨id, rs', h1, h2, h3⟩
    · rintro ⟨id, rs', h1, h2, h3⟩
      have hne : FKey.pobj id ≠ .pobj (X, q) := by
        intro e; cases e; exact hnodec h t h1
      exact ⟨id, rs', by rw [Facts.set_ne _ _ (by simp)]; exact h1,
        by rw [Facts.set_ne _ _ hne]; exact h2, h3⟩
  imod invAt_insert _ γ M (.pobj (X, q)) (.reqs rs) (.srv X) K rfl hq (by simp) (by simp) hobj1
    hreq1 $$ [Hi HK] with ⟨%hfree1, Hi, HK, #Hf1⟩
  · iframe
  have hr' : ∀ r ∈ rs, FKey.robj X r ∉ FKey.pobj (X, q) :: K := by
    intro r hrs h
    rcases List.mem_cons.mp h with h | h
    · cases h
    · exact hr r hrs h
  imod invAt_insert_robjs _ γ X (X, q) rs _ _ hnd hr' $$ [Hi HK] with ⟨%hfree2, Hi, HK, #Hf2⟩
  · iframe
  have hXlt : X < c.n := by
    obtain ⟨r0, hr0⟩ := List.exists_mem_of_ne_nil rs hne
    rw [← hX r0 hr0]
    exact Nat.mod_lt _ (by have := hcOk.nf; omega)
  have hV' := Valid.insertObj M hcfM HV (X, q) rs hfree1 hne hnd hXlt (fun r hr => by
    refine ⟨?_, ?_, (hX r hr).symm⟩
    · have := hfree2 r hr
      rwa [Facts.set_ne _ _ (by simp)] at this
    · obtain ⟨cm, hcm⟩ := hS1.2.1 r hr
      exact ⟨cm, hSM1 _ hcm⟩)
  imod Hclose $$ [Hi] with -
  · inext
    iexists rs.foldr (fun r M' => M'.set (.robj X r) (.obj (X, q))) (M.set (.pobj (X, q)) (.reqs rs))
    iframe Hi
    ipureintro
    rw [foldr_setRobj_eq]
    exact hV'
  imodintro
  iframe HK
  isplitr
  · iexact Hf1
  · iexact Hf2

/-- The configuration `c` is recorded first, by the orchestrator (writer `.orch`; stage 3). -/
theorem setCfg (γ : RabiaNames) (E : CoPset) (hE : ↑rabiaN ⊆ E) (c : RCfg) (K : List FKey) :
    isRabia (GF := GF) γ ∗ keysOf γ .orch K ∗ ⌜FKey.cfg ∉ K ∧ c.Ok⌝ ⊢
      |={E}=> keysOf γ .orch (.cfg :: K) ∗ cfgIs γ c := by
  unfold isRabia
  iintro ⟨#Hinv, HK, %hK⟩
  obtain ⟨hk, hc⟩ := hK
  imod inv_acc hE $$ Hinv with ⟨Hi, Hclose⟩
  unfold rabiaInv
  icases Hi with ⟨%M, >%HV, Hi⟩
  have h1 : ∀ id, FKey.cfg ≠ .pobj id := by simp
  have h2 : ∀ r, FKey.cfg ≠ .reg r := by simp
  have h3 : ∀ s, FKey.cfg ≠ .dec s := by simp
  imod invAt_insert _ γ M .cfg (.cfgv c) .orch K rfl hk h2 h3
    (fun _ t id _ => objCmds_set M _ _ id h1 h2) (fun _ r s => reqAt_set M _ _ r s h1 h3)
    $$ [Hi HK] with ⟨%hfree, Hi, HK, #Hf⟩
  · iframe
  have hV' : Valid (M.set .cfg (.cfgv c)) := by
    rcases valid_cases HV with ⟨c', hc', -, -⟩ | h0
    · unfold CfgOf at hc'; rw [hfree] at hc'; cases hc'
    · have : M = fun _ => none := funext h0
      subst this
      exact Valid.setCfg c hc
  imod Hclose $$ [Hi] with -
  · inext
    iexists M.set .cfg (.cfgv c)
    iframe Hi
    ipureintro; exact hV'
  imodintro
  iframe HK
  unfold cfgIs
  iframe Hf
  ipureintro; exact hc

/-- Two recorded configurations are the same. -/
theorem cfgIs_agree (γ : RabiaNames) (c c' : RCfg) :
    cfgIs (GF := GF) γ c ∗ cfgIs γ c' ⊢ ⌜c = c'⌝ := by
  unfold cfgIs
  iintro ⟨⟨H1, -⟩, ⟨H2, -⟩⟩
  ihave %h := fact_agree γ _ _ _ $$ [H1 H2]
  · iframe
  ipureintro
  cases h; rfl

/-- Client `c` registers its `n`-th request, the command of input `i`, depositing its operation's
atomic update: it gets the fact, the request's saved commit predicate and its collection token
(the record has its configuration `cf`). -/
theorem register (γ : RabiaNames) (E : CoPset) (hE : ↑rabiaN ⊆ E) (cf : RCfg) (c n : Nat)
    (K : List FKey) (hk : FKey.reg (c, n) ∉ K) (i : KvInput GoString GoString) (hi : inputOk i)
    (Q : OpQ GF) :
    isRabia (GF := GF) γ ∗ cfgIs γ cf ∗ keysOf γ (.cli c) K ∗ opAU γ i Q ⊢
      |={E}=> keysOf γ (.cli c) (.reg (c, n) :: K) ∗ fact γ (.reg (c, n)) (.cmd (cmdOf i)) ∗
        (∃ γq, ghostMapElem γ.qs (c, n) .discard γq ∗
          savedQ γq Q) ∗
        ghostMapElem γ.col (c, n) (.own 1) () := by
  unfold isRabia
  iintro ⟨#Hinv, #Hcf, HK, HAU⟩
  imod inv_acc hE $$ Hinv with ⟨Hi, Hclose⟩
  unfold rabiaInv
  icases Hi with ⟨%M, >%HV, Hi⟩
  unfold cfgIs
  icases Hcf with ⟨#Hcf, %hcf⟩
  imod invAt_fact_in _ γ M _ _ $$ [Hi Hcf] with ⟨%hcfM, Hi⟩
  · iframe Hi; iexact Hcf
  imod invAt_register _ γ M HV c n K hk i hi Q $$ [Hi HK HAU] with ⟨%hfree, Hi, HK, #Hf, HQ, Hcol⟩
  · iframe
  imod Hclose $$ [Hi] with -
  · inext
    iexists M.set (.reg (c, n)) (.cmd (cmdOf i))
    iframe Hi
    ipureintro
    exact Valid.insert (c := cf) M hcfM HV _ _ hfree trivial (by simp) (by simp) (by simp) (by simp)
      (by simp)
  imodintro
  iframe HK HQ Hcol
  iexact Hf

/-- `decideSlot`, with a later credit (HR-B1: the statement `decideSlot` needs it, to take the
stored atomic updates out of the invariant's later): server `X` records its decision `d` of slot
`s` and, the first time, the slot's decision, committing (in the batch's order) the atomic update
of every request of a decided object. -/
theorem decideSlot (γ : RabiaNames) (E : CoPset) (hE : ↑rabiaN ⊆ E)
    (hcl : cliE ## ↑rabiaN)
    (hcE : cliE ⊆ E) (c : RCfg)
    (X s : Nat) (d : DVal) (K : List FKey) (S : List (FKey × FVal)) (hX : X < c.n)
    (hk : FKey.mydec X s ∉ K)
    (hprev : s = 0 ∨ ∃ d', (FKey.mydec X (s - 1), FVal.dval d') ∈ S)
    (hJ : ∀ M, CfgOf M c → ValidAt c M → (∀ kv ∈ S, M kv.1 = some kv.2) →
      DecEvidence c M s d ∨ M (.dec s) = some (.dval d)) :
    isRabia (GF := GF) γ ∗ cfgIs γ c ∗ £ 1 ∗ keysOf γ (.srv X) K ∗
      ([∗list] kv ∈ S, fact γ kv.1 kv.2) ⊢
      |={E}=> keysOf γ (.srv X) (.mydec X s :: K) ∗ fact γ (.mydec X s) (.dval d) ∗
        fact γ (.dec s) (.dval d) := by
  unfold isRabia
  iintro ⟨#Hinv, #Hcf, Hlc, HK, #HS⟩
  imod inv_acc hE $$ Hinv with ⟨Hi, Hclose⟩
  unfold rabiaInv
  icases Hi with ⟨%M, >%HV, Hi⟩
  imod invAt_facts _ γ M S $$ [Hi HS] with ⟨%hS, Hi⟩
  · iframe Hi; imodintro; iexact HS
  unfold cfgIs
  icases Hcf with ⟨#Hcf, %hcOk⟩
  imod invAt_fact_in _ γ M _ _ $$ [Hi Hcf] with ⟨%hcfM, Hi⟩
  · iframe Hi; iexact Hcf
  have hVc : ValidAt c M := (HV.at hcfM).2
  have hprevM : s = 0 ∨ M (.mydec X (s - 1)) ≠ none := by
    rcases hprev with h | ⟨d', hd'⟩
    · exact Or.inl h
    · right; rw [hS _ hd']; simp
  have hprevD : s = 0 ∨ M (.dec (s - 1)) ≠ none :=
    hprevM.imp id (fun h => hVc.2.2.2.2.2 X _ h)
  have hm1 : ∀ id, FKey.mydec X s ≠ .pobj id := by simp
  have hm2 : ∀ r, FKey.mydec X s ≠ .reg r := by simp
  have hm3 : ∀ t, FKey.mydec X s ≠ .dec t := by simp
  cases hds : M (.dec s) with
  | some v =>
    have hj := hVc.1 _ _ hds
    cases v with
    | dval d0 =>
      have hd : d = d0 := by
        apply agree M hcOk hVc s d d0 _ (Or.inr (Or.inl hds))
        rcases hJ M hcfM hVc hS with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      subst hd
      imod invAt_fact _ γ M (.dec s) (.dval d) hds $$ Hi with ⟨#Hdec, Hi⟩
      imod invAt_insert _ γ M (.mydec X s) (.dval d) (.srv X) K rfl hk hm2 hm3
        (fun _ _ id _ => objCmds_set M _ _ id hm1 hm2) (fun _ r t => reqAt_set M _ _ r t hm1 hm3)
        $$ [Hi HK] with ⟨%hfree, Hi, HK, #Hf⟩
      · iframe
      imod Hclose $$ [Hi] with -
      · inext
        iexists M.set (.mydec X s) (.dval d)
        iframe Hi
        ipureintro
        refine Valid.insert M hcfM HV _ _ hfree ⟨hX, Or.inr hds⟩ (by simp) (by simp) (by simp)
          (by simp) ?_
        intro X' s' h
        cases h
        exact ⟨by simp [hds], hprevM⟩
      imodintro
      iframe HK
      isplitr
      · iexact Hf
      · iexact Hdec
    | _ => exact (False.elim hj)
  | none =>
    have hev : DecEvidence c M s d := by
      rcases hJ M hcfM hVc hS with h | h
      · exact h
      · rw [hds] at h; cases h
    have hV1 : Valid (M.set (.dec s) (.dval d)) := by
      refine Valid.insert M hcfM HV _ _ hds hev (by simp) (by simp) (by simp) ?_ (by simp)
      intro s' h
      cases h
      rcases hprevD with h0 | h1
      · omega
      · simpa using h1
    imod invAt_decide _ (mask_client E hcl hcE) γ M s d HV hV1 hds hprevD $$ [Hlc Hi]
      with ⟨Hi, #Hdec⟩
    · iframe
    imod invAt_insert _ γ (M.set (.dec s) (.dval d)) (.mydec X s) (.dval d) (.srv X) K rfl hk
        hm2 hm3 (fun _ _ id _ => objCmds_set _ _ _ id hm1 hm2)
        (fun _ r t => reqAt_set _ _ _ r t hm1 hm3)
        $$ [Hi HK] with ⟨%hfree, Hi, HK, #Hf⟩
    · iframe
    imod Hclose $$ [Hi] with -
    · inext
      iexists (M.set (.dec s) (.dval d)).set (.mydec X s) (.dval d)
      iframe Hi
      ipureintro
      refine Valid.insert (c := c) _ (by unfold CfgOf; rw [Facts.set_ne _ _ (by simp)]; exact hcfM) hV1 _ _ hfree ⟨hX, Or.inr (Facts.set_self _ _ _)⟩ (by simp) (by simp)
        (by simp) (by simp) ?_
      intro X' s' h
      cases h
      refine ⟨by simp [Facts.set_self], ?_⟩
      rw [Facts.set_ne _ _ (by simp)]
      exact hprevM
    imodintro
    iframe HK
    isplitr
    · iexact Hf
    · iexact Hdec

/-- `collect`, with the client's input premise and a later credit (HR-B2: `inputOk i` identifies
the registered input; `£ 1` because the stored commit postcondition and its saved name are under
the invariant's later): request `r` is `rs[j]` of the object decided at slot `s`, executed on the
slots before `s` (`cmds`) and the requests before it in the batch (`bc.take j`). -/
theorem collect (γ : RabiaNames) (E : CoPset) (hE : ↑rabiaN ⊆ E) (r : ReqId) (s : Nat)
    (i : KvInput GoString GoString) (hi : inputOk i) (Q : OpQ GF) (γq : GName) (id : ObjId)
    (rs : List ReqId) (bc : List GoString) (j : Nat) (hj : rs[j]? = some r)
    (cmds : List GoString) :
    isRabia (GF := GF) γ ∗ £ 1 ∗ ghostMapElem γ.col r (.own 1) () ∗
      ghostMapElem γ.qs r .discard γq ∗ savedQ γq Q ∗
      fact γ (.reg r) (.cmd (cmdOf i)) ∗ fact γ (.dec s) (.dval (.obj id)) ∗
      fact γ (.pobj id) (.reqs rs) ∗ regFacts γ rs bc ∗ prefixFacts γ s cmds ⊢
      |={E}=> ▷ ∃ σ' o, ⌜(kv GoString GoString).step (stateOfCmds (cmds ++ bc.take j)) i σ' o⌝ ∗
        Q (stateOfCmds (cmds ++ bc.take j)) σ' o := by
  unfold isRabia
  iintro ⟨#Hinv, Hlc, Hcol, #Hq, #HsQ, #Hreg, #Hdec, #Hpo, #Hrf, Hpf⟩
  ihave ⟨%S1, #HS1, %hS1⟩ := regFacts_facts γ rs bc $$ Hrf
  ihave ⟨%S, #HS, %hS⟩ := prefixFacts_facts γ s cmds $$ Hpf
  imod inv_acc hE $$ Hinv with ⟨Hi, Hclose⟩
  unfold rabiaInv
  icases Hi with ⟨%M, >%HV, Hi⟩
  imod invAt_facts _ γ M S $$ [Hi HS] with ⟨%hSM, Hi⟩
  · iframe Hi; imodintro; iexact HS
  imod invAt_facts _ γ M S1 $$ [Hi HS1] with ⟨%hSM1, Hi⟩
  · iframe Hi; imodintro; iexact HS1
  imod invAt_fact_in _ γ M _ _ $$ [Hi Hreg] with ⟨%hreg, Hi⟩
  · iframe Hi; iexact Hreg
  imod invAt_fact_in _ γ M _ _ $$ [Hi Hdec] with ⟨%hdec, Hi⟩
  · iframe Hi; iexact Hdec
  imod invAt_fact_in _ γ M _ _ $$ [Hi Hpo] with ⟨%hpo, Hi⟩
  · iframe Hi; iexact Hpo
  imod lc_fupd_elim_later $$ Hlc Hi with Hi
  unfold rabiaInvAt
  icases Hi with ⟨%MG, %KS, %n, Hf, %HMG, Hfs, Hk, %HKO, Hkw, %Hn, Hkv, HQS, HCS, Hops⟩
  have hMGr : MG.lookup (.reg r) = some (.cmd (cmdOf i)) := by rw [HMG]; exact hreg
  icases (BigSepM.bigSepM_delete (Φ := fun k _ => opsTerm (GF := GF) γ M k) hMGr).1 $$ Hops
    with ⟨Hop, Hops⟩
  rw [opsTerm_reg]
  have hrs : r ∈ rs := List.mem_of_getElem? hj
  obtain ⟨c, hcM, hcOk, hVc⟩ | h0 := valid_cases HV
  rotate_left
  · rw [h0] at hreg; cases hreg
  have hreq : ReqAt M r s := ⟨id, rs, hdec, hpo, hrs⟩
  have hamo : ∀ s', ReqAt M r s' → s' = s := by
    rintro s' ⟨id', rs', h1, h2, h3⟩
    exact (atMostOnceReq M hcOk hVc s' s id' id rs' rs r h1 hdec h2 hpo h3 hrs).1
  have hidx : rs.idxOf r = j := by
    obtain ⟨hjl, hjr⟩ := List.getElem?_eq_some_iff.mp hj
    rw [← hjr]
    exact List.Nodup.idxOf_getElem (valid_pobj_nodup HV hpo) j hjl
  have hst : stateBefore M r s = stateOfCmds (cmds ++ bc.take j) := by
    simp only [stateBefore, cmdsBefore, hdec, hpo]
    rw [hS M hSM, hidx, hS1.1 M hSM1 j]
  imod opState_collect _ γ M r s i hi Q γq (cmds ++ bc.take j) hreq hreg hamo hst $$ [Hop Hcol]
    with ⟨Hop, HQ⟩
  · iframe Hop Hcol
    isplitr
    · imodintro; iexact Hq
    · imodintro; iexact HsQ
  imod Hclose $$ [Hf Hfs Hk Hkw Hkv HQS HCS Hops Hop] with -
  · inext
    iexists M
    isplitr
    · ipureintro; exact HV
    iexists MG, KS, n
    iframe Hf Hfs Hk Hkw Hkv HQS HCS
    isplitr
    · ipureintro; exact HMG
    isplitr
    · ipureintro; exact HKO
    isplitr
    · ipureintro; exact Hn
    iapply (BigSepM.bigSepM_delete (Φ := fun k _ => opsTerm (GF := GF) γ M k) hMGr).2
    rw [opsTerm_reg]
    iframe Hop Hops
  imodintro
  iexact HQ


/-- The facts of the first `s` decided slots determine their commands: in any valid record that
has them, `cmdsAt M s = cmds` (what the proxy's store and the replies rest on). -/
theorem prefixFacts_cmds (γ : RabiaNames) (E : CoPset) (hE : ↑rabiaN ⊆ E) (s : Nat)
    (cmds : List GoString) :
    isRabia (GF := GF) γ ∗ prefixFacts γ s cmds ⊢
      |={E}=> ∃ S : List (FKey × FVal), ([∗list] kv ∈ S, fact γ kv.1 kv.2) ∗
        ⌜∀ M, Valid M → (∀ kv ∈ S, M kv.1 = some kv.2) → cmdsAt M s = cmds⌝ := by
  iintro ⟨-, Hp⟩
  ihave ⟨%S, HS, %hS⟩ := prefixFacts_facts γ s cmds $$ Hp
  imodintro
  iexists S
  iframe HS
  ipureintro
  exact fun M _ h => hS M h

end laws

end Perennial.rabia

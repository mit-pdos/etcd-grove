/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Ghost/System.lean (lab master 915f964;
notes/dsv-vr.md): over any `GF`; the client's atomic update is remote's one-shot update (`AUof`).
-/
/-
The system's ghost state (the hub every node's proof uses): the protocol model's state in one
global invariant, the stable facts as persistent witnesses, each replica's half of its own
model state, the abstract key-value state (the client spec's `own_state`), each client's next
request number, and the registry of the clients' pending atomic updates (helping).

Stated over the global ghost state (`GooseGlobalGS .hasLC GF`): the start allocates it
(`ghost_alloc`), and every node's proof (under a `HeapGS` whose global part is this one) uses it.

The number of replicas `n` (a field of the model's state, `VsrModel.Sys.n`) is not known at the
start: node 0 draws it. The system starts "unsized" (at `VsrModel.init 3`, no fact yet); node 0's
size token (`sizeTok`) fixes it once (`ghost_size`), giving the persistent `fact γ (.size n)`,
which every node then learns (the configuration's protocol carries it). Every law that changes
the state or creates a fact takes a `fact γ (.size n)` and gives its hypothesis `s.n = n`.

Laws:
* `ghost_alloc`: the start (five replicas' states, six clients' counters, the size token).
* `ghost_size`: node 0 fixes the number of replicas.
* `ghost_pure`, `ghost_pure_rep`, `fact_plain`: a pure consequence of the invariant and facts
  held (and of a replica's own state), e.g. a valid message's strings are plain.
* `ghost_fact`, `ghost_step`: a replica learns a stable fact, or performs a model step that
  does not touch the linearized log, from its own state and facts it holds.
* `ghost_lin`: a replica executing its `k`-th op (the first to execute it anywhere commits the
  client's atomic update there: the linearization point).
* `ghost_register`, `ghost_retrieve`: a client registers its next request with its atomic
  update (before sending it), and retrieves the update's result when a reply arrives.
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Model.Basic
public import Perennial.Ghost.GhostMap
public import Perennial.Ghost.GhostVar
public import Perennial.Ghost.SavedProp
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Ghost.Impl.Alloc
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Ghost.Impl.Client
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Ghost.Impl.Lin
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Ghost.Impl.Step

@[expose] public section

noncomputable section

namespace VsrGhost

open Perennial Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode VsrModel
open Net

instance fact_decEq : DecidableEq Fact := Impl.factDecEq
instance fact_countable : Pos.Countable Fact := Impl.factCountable
instance rep_countable : Pos.Countable Rep := Impl.repCountable
instance entry_countable : Pos.Countable Entry := Impl.entryCountable

/-- The ghost names of the system. -/
structure Names where
  /-- ghost map (persistent elements): the facts witnessed -/
  facts : GName
  /-- ghost map: replica id ↦ its model state (element: the replica's; auth: the invariant) -/
  reps : GName
  /-- ghost variable (halves): the linearized log (the client spec's abstract state) -/
  abs : GName
  /-- ghost map: client id ↦ its next request number -/
  next : GName
  /-- the registry's ghost names -/
  regm : GName
  regt : GName
  /-- token: the number of replicas is not fixed yet (node 0's) -/
  size : GName

/-- The implementation's ghost names (`regt` is unused). -/
def Names.gn (γ : Names) : Impl.GN := ⟨γ.facts, γ.reps, γ.abs, γ.next, γ.regm, γ.size⟩

/-- The invariants' namespaces. -/
def sysN : Namespace := ndot (ndot nroot "vsr") "sys"
def regN : Namespace := ndot (ndot nroot "vsr") "reg"

/-- The client operation's input from its operation string (the registered ones). -/
abbrev KvIn := KvInput GoString GoString
abbrev KvOut := KvOutput GoString

/-- The key-value model's output for input `i` whose reply string is `res` (a put: done; a get:
the value, `""` meaning none). -/
def outOfReply : KvIn → GoString → KvOut
  | .put _ _, _ => .done
  | .get _, res => .got (if res = [] then none else some res)

theorem outOfReply_eq : outOfReply = Impl.outOfReplyI := by
  funext i res; cases i <;> rfl

section defs
attribute [local instance] GooseGlobalGS.gooseInvGS
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF]

/-- A stable fact holds (persistent). -/
def fact (γ : Names) (f : Fact) : IProp GF :=
  ghostMapElem γ.facts f DFrac.discard ()

/-- Replica `r`'s model state is `p` (its half; exclusive). -/
def repOwn (γ : Names) (r : Nat) (p : Rep) : IProp GF :=
  ghostMapElem γ.reps r (DFrac.own 1) p

/-- The abstract key-value state is `σ` (the client spec's `own_state`; timeless): half of the
ghost variable `γ.abs` holding a log whose store is `σ` (the invariant holds the other half,
the linearized log).
-- sealed: the ghost layer's choice -/
def absOwn (γ : Names) (σ : Store) : IProp GF := Impl.absOwnI γ.gn σ

/-- The number of replicas is not fixed yet (exclusive; node 0's, used once by `ghost_size`). -/
def sizeTok (γ : Names) : IProp GF := token γ.size

/-- Client `c`'s next request number is `n` (exclusive). -/
def nextReq (γ : Names) (c n : Nat) : IProp GF :=
  ghostMapElem γ.next c (DFrac.own 1) n

/-- The system's invariant (timeless contents). -/
def sysInv (γ : Names) : IProp GF := Impl.sysInvI γ.gn

/-- The registry's invariant: each registered request's atomic update, pending or committed. -/
def regInv (γ : Names) : IProp GF := Impl.regInvI γ.gn

/-- Client `c`'s ticket for its registered request `n`, whose atomic update's commit
postcondition is `Q`: what it retrieves `Q` with. -/
def ticket (γ : Names) (c n : Nat) (i : KvIn) (Q : Store → Store → KvOut → IProp GF) :
    IProp GF := Impl.ticketI γ.gn c n i Q

instance fact_persistent (γ : Names) (f : Fact) : Persistent (fact (GF := GF) γ f) :=
  Impl.factI_persistent γ.gn f
instance sysInv_persistent (γ : Names) : Persistent (sysInv (GF := GF) γ) := Impl.sysInvI_persistent γ.gn
instance regInv_persistent (γ : Names) : Persistent (regInv (GF := GF) γ) := Impl.regInvI_persistent γ.gn
instance absOwn_timeless (γ : Names) (σ : Store) : Timeless (absOwn (GF := GF) γ σ) :=
  Impl.absOwnI_timeless γ.gn σ

/-! ## The start -/

/-- The start: the system unsized (at `VsrModel.init 3`), the abstract state empty, each of the
five possible replicas' states (`initRep`), each client's next request number (clients `1..6`,
from 1), and the size token. -/
theorem ghost_alloc :
    ⊢ |={⊤}=> ∃ γ : Names, sysInv (GF := GF) γ ∗ regInv γ ∗ absOwn γ (fun _ => none) ∗ sizeTok γ ∗
      ([∗list] r ∈ List.range 5, repOwn γ r VsrModel.initRep) ∗
      ([∗list] c ∈ List.range 6, nextReq γ (c + 1) 1) := by
  imod Impl.ghost_alloc_impl with ⟨%g, H⟩
  rcases g with ⟨a, b, c, d, e, z⟩
  imodintro
  iexists ⟨a, b, c, d, e, e, z⟩
  simp only [sysInv, regInv, absOwn, sizeTok, repOwn, nextReq, Names.gn, Impl.repOwnI,
    Impl.nextReqI]
  iexact H

/-- Node 0 fixes the number of replicas `n` (once: the token): afterwards the system is
`VsrModel.init n` (nothing has happened yet: no fact exists before), and `n` is known. -/
theorem ghost_size (γ : Names) (E : CoPset) (hE : ↑sysN ⊆ E) (n : Nat) (hn : 0 < n) :
    sysInv (GF := GF) γ -∗ sizeTok γ ={E}=∗ fact γ (.size n) :=
  Impl.ghost_size_impl γ.gn E hE n hn

/-! ## Pure consequences -/

/-- A pure consequence `φ` of the invariant and the facts `fs` (which are kept: persistent). -/
theorem ghost_pure (γ : Names) (E : CoPset) (hE : ↑sysN ⊆ E) (fs : List Fact) (φ : Prop)
    (H : ∀ s, VsrModel.Inv s → (∀ f ∈ fs, Holds s f) → φ) :
    sysInv (GF := GF) γ -∗ ([∗list] f ∈ fs, fact γ f) ={E}=∗ ⌜φ⌝ :=
  Impl.ghost_pure_impl γ.gn E hE fs φ H

/-- A pure consequence `φ` of the invariant, replica `r`'s state `p` and the facts `fs` (its
state kept). -/
theorem ghost_pure_rep (γ : Names) (E : CoPset) (hE : ↑sysN ⊆ E) (r : Nat) (p : Rep)
    (fs : List Fact) (φ : Prop)
    (H : ∀ s, VsrModel.Inv s → s.reps r = p → (∀ f ∈ fs, Holds s f) → φ) :
    sysInv (GF := GF) γ -∗ repOwn γ r p -∗ ([∗list] f ∈ fs, fact γ f) ={E}=∗ repOwn γ r p ∗ ⌜φ⌝ :=
  Impl.ghost_pure_rep_impl γ.gn E hE r p fs φ H

/-- A valid message's strings are plain (`ghost_pure` with `msgValid_plain`). -/
theorem fact_plain (γ : Names) (E : CoPset) (hE : ↑sysN ⊆ E) (m : Msg) :
    sysInv (GF := GF) γ -∗ fact γ (.msg m) ={E}=∗ ⌜PlainMsg m⌝ := by
  iintro #Hs #Hf
  iapply ghost_pure γ E hE [.msg m] (PlainMsg m)
    (fun s h hfs => msgValid_plain s h m (hfs (.msg m) (by simp))) $$ Hs
  iapply BigSepL.bigSepL_cons.2
  isplitl []
  · iexact Hf
  · iapply BigSepL.bigSepL_nil.2; iempintro

/-! ## Replica steps -/

/-- Replica `r` (state `p`, holding facts `fs`) learns a fact `f` that holds of every state it
can be in. -/
theorem ghost_fact (γ : Names) (E : CoPset) (hE : ↑sysN ⊆ E) (n r : Nat) (p : Rep)
    (fs : List Fact) (f : Fact)
    (H : ∀ s, VsrModel.Inv s → s.n = n → s.reps r = p → (∀ f' ∈ fs, Holds s f') → Holds s f) :
    fact (GF := GF) γ (.size n) -∗ sysInv γ -∗ repOwn γ r p -∗ ([∗list] f' ∈ fs, fact γ f') ={E}=∗
      repOwn γ r p ∗ fact γ f :=
  Impl.ghost_fact_impl γ.gn E hE n r p fs f H

/-- Replica `r` (state `p`, holding facts `fs`) performs a model step `st` that leaves the
linearized log and the registry as they are, ends in its state `p'` and gives the facts `fs'`. -/
theorem ghost_step (γ : Names) (E : CoPset) (hE : ↑sysN ⊆ E) (n r : Nat) (p p' : Rep)
    (fs fs' : List Fact) (st : Sys → Sys)
    (H : ∀ s, VsrModel.Inv s → s.n = n → s.reps r = p → (∀ f ∈ fs, Holds s f) →
      VsrModel.Inv (st s) ∧ Le s (st s) ∧ (st s).reps r = p' ∧ (∀ x, x ≠ r → (st s).reps x = s.reps x) ∧
      (st s).lin = s.lin ∧ (st s).reg = s.reg ∧ (∀ f ∈ fs', Holds (st s) f)) :
    fact (GF := GF) γ (.size n) -∗ sysInv γ -∗ repOwn γ r p -∗ ([∗list] f ∈ fs, fact γ f) ={E}=∗
      repOwn γ r p' ∗ [∗list] f ∈ fs', fact γ f :=
  Impl.ghost_step_impl γ.gn E hE n r p p' fs fs' st H

/-- A replica executes the `k`-th op of a committed log `l` (`mine`, a prefix of the linearized
log, is what it executed): the linearized log has `l`'s first `k` entries afterwards, and if
the op is executed here first, the client's atomic update is committed (with the key-value
model's step). The reply string of the op is `outOf (l.take k) (k - 1)`, which the replica's
store computes; the reply is valid (for any view `v`: `Msg.reply`'s view is not constrained).
One later credit pays for the registry's later. -/
theorem ghost_lin (γ : Names) (E : CoPset) (hE : ↑sysN ⊆ E) (hR : ↑regN ⊆ E)
    (hC : ⊤ \ Impl.vsrE ⊆ E) (hd : ↑sysN ∩ ↑regN = (∅ : CoPset))
    (l mine : List Entry) (k : Nat) (e : Entry)
    (hk : mine.length + 1 = k) (hml : mine <+: l) (he : l[k - 1]? = some e) (v w : Nat) :
    £ 1 -∗ sysInv (GF := GF) γ -∗ regInv γ -∗ fact γ (.committedBy w l) -∗
      fact γ (.linPrefix mine) ={E}=∗
      fact γ (.linPrefix (l.take k)) ∗
      fact γ (.msg (.reply e.req e.cid v (outOf (l.take k) (k - 1)))) :=
  Impl.ghost_lin_impl γ.gn E hE hR hC hd l mine k e hk hml he v w

/-! ## Clients -/

/-- Client `c` registers its next request `n` with input `i` (well formed: `InputOk`)
and the atomic update of its operation (commit postcondition `Q`), before it sends it: the
request message is valid, and the client keeps a ticket. The registration is bounded (SF4, D5):
`c` one of the six clients, `n` within the client's budget (below 2^28), the input's strings
short (`InputBounded`). -/
theorem ghost_register (γ : Names) (E : CoPset) (hE : ↑sysN ⊆ E) (hR : ↑regN ⊆ E)
    (N c n : Nat) (i : KvIn) (hi : InputOk i) (hc : 1 ≤ c ∧ c ≤ 6) (hn : 1 ≤ n ∧ n < 2 ^ 28)
    (hb : InputBounded i)
    (Q : Store → Store → KvOut → IProp GF) :
    fact γ (.size N) -∗ sysInv γ -∗ regInv γ -∗ nextReq γ c n -∗
      Impl.AUof γ.gn i Q ={E}=∗
      nextReq γ c (n + 1) ∗ fact γ (.msg (.request n c (encOp i))) ∗ ticket γ c n i Q :=
  Impl.ghost_register_impl γ.gn E hE hR N c n i hi ⟨hc.1, hc.2, hn.1, hn.2, hb⟩ Q

/-- Client `c`, holding the ticket of request `n`, retrieves its atomic update's result from a
valid reply to it: `Q` of the update's step, whose output the reply string gives. -/
theorem ghost_retrieve (γ : Names) (E : CoPset) (hR : ↑regN ⊆ E) (hE : ↑sysN ⊆ E)
    (c n v : Nat) (i : KvIn) (Q : Store → Store → KvOut → IProp GF) (res : GoString) :
    £ 1 -∗ sysInv (GF := GF) γ -∗ regInv γ -∗ ticket γ c n i Q -∗
      fact γ (.msg (.reply n c v res)) ={E}=∗
      ∃ σ σ', Q σ σ' (outOfReply i res) ∗
        ⌜kvStep σ i σ' (outOfReply i res)⌝ := by
  rw [outOfReply_eq]
  exact Impl.ghost_retrieve_impl γ.gn E hR hE c n v i Q res

end defs

end VsrGhost

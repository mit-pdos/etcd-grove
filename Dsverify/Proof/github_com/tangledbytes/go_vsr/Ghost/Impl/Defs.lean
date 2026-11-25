/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Ghost/Impl/Defs.lean (lab master 915f964;
notes/dsv-vr.md): over any `GF`; the client's atomic update is remote's one-shot update (`AUof`).
-/
/-
The ghost layer's implementation: its resources (the bodies of `VsrGhost`'s sealed definitions,
stated over `GN`, the ghost names the laws use) and their basic instances.

Design (notes/prove/ghost.md):
* `sysInvI`: an invariant (timeless contents) holding the model state `s` with `Inv s`; the facts'
  ghost map (auth, every fact true of `s`, and the persistent elements); the replicas' ghost map
  (auth, agreeing with `s.reps`); half of the abstract state's ghost variable (`s.lin`); the
  request counters' ghost map (auth; a counter's numbers from on are unregistered); half of the
  registry's ghost map `M : (c, n) ↦ (γs, γt, γp, i)` (agreeing with `s.reg`), and for each
  registered request half of its status variable `γs` (`none`: pending, `some r`: done with reply
  string `r`; `StatusOk` against `s.lin`) and, while pending, its pending token `γp`; and its
  size state (`sizedI`): unsized (`s = init s.n`, no fact, empty registry) or sized (node 0's size
  token, put in by `ghost_size`). A fact (e.g. `.size n`) rules the unsized state out.
* `regInvI`: an invariant holding the other half of the registry's map and, for each registered
  request, its client's atomic update and its request invariant (pending), or the pending token
  `γp` (committed).
* `reqInv`: one invariant per request (namespace `reqNI (c, n)`), holding the other half of `γs`
  and, once done, the update's result `Q σ σ' o` or the client's ticket token `γt` (retrieved).
* `ticketI`: the client's token `γt`, the request's registry entry, and its request invariant
  (which names the client's `Q`: no saved predicate, so retrieving costs one later credit).
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Ghost.Impl.Pure
public import Perennial.Ghost.GhostMap
public import Perennial.Ghost.GhostVar
public import Perennial.Ghost.Token
public import Perennial.Golang.Theory.IrisTactics
public import Net.Proof.net.Base

@[expose] public section

noncomputable section

namespace VsrGhost.Impl

open Perennial Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode VsrModel
open Net

attribute [local instance] entryCountable statusCountable repCountable factCountable factDecEq
  kvInCountable

/-- The ghost names the implementation uses (`VsrGhost.Names` without `regt`). -/
structure GN where
  facts : GName
  reps : GName
  abs : GName
  next : GName
  regm : GName
  size : GName

def sysNI : Namespace := ndot (ndot nroot "vsr") "sys"
def regNI : Namespace := ndot (ndot nroot "vsr") "reg"
/-- The registry's invariant. -/
def regInvN : Namespace := ndot regNI "r"
/-- Request `k`'s invariant. -/
def reqNI (k : Nat × Nat) : Namespace := ndot (ndot regNI "q") k

/-- A registry entry: status variable, ticket token, pending token, input. -/
abbrev RegVal := GName × GName × GName × KvInI

section defs
attribute [local instance] GooseGlobalGS.gooseInvGS
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF]

abbrev factI (g : GN) (f : Fact) : IProp GF :=
  ghostMapElem g.facts f DFrac.discard ()

abbrev repOwnI (g : GN) (r : Nat) (p : Rep) : IProp GF :=
  ghostMapElem g.reps r (DFrac.own 1) p

abbrev nextReqI (g : GN) (c n : Nat) : IProp GF :=
  ghostMapElem g.next c (DFrac.own 1) n

def absOwnI (g : GN) (σ : Store) : IProp GF :=
  iprop(∃ L : List Entry, ghostVar g.abs (1 : Qp).half L ∗ ⌜storeOf L = σ⌝)

/-- The pending token, held by the system's invariant while the request is pending. -/
def pendTok (γp : GName) : Option GoString → IProp GF
  | none => token γp
  | some _ => emp

/-- The system invariant's part of registered request `k`. -/
def sysEntry (lin : List Entry) (k : Nat × Nat) (v : RegVal) : IProp GF :=
  iprop(∃ st : Option GoString, ghostVar v.1 (1 : Qp).half st ∗ ⌜StatusOk lin k.1 k.2 st⌝ ∗
    pendTok v.2.2.1 st)

/-- The system's size state: unsized (no fact yet, nothing registered, nothing happened: the
start for some `n`), or sized (node 0's size token is here: `ghost_size` has run). -/
def sizedI (g : GN) (F : GMap Fact Unit) (M : GMap (Nat × Nat) RegVal) (s : Sys) :
    IProp GF :=
  iprop(⌜F = ∅ ∧ M = ∅ ∧ s = init s.n⌝ ∨ token g.size)

/-- The system's ghost state at model state `s`. -/
def sysAt (g : GN) (s : Sys) : IProp GF :=
  iprop(∃ (F : GMap Fact Unit) (R : GMap Nat Rep) (N : GMap Nat Nat)
      (M : GMap (Nat × Nat) RegVal),
    ⌜Inv s⌝ ∗
    ghostMapAuth g.facts 1 F ∗ ⌜∀ f u, F !! f = some u → Holds s f⌝ ∗
      ([∗map] f ↦ _u ∈ F, factI g f) ∗
    ghostMapAuth g.reps 1 R ∗ ⌜∀ r p, R !! r = some p → s.reps r = p⌝ ∗
    ghostVar g.abs (1 : Qp).half s.lin ∗
    ghostMapAuth g.next 1 N ∗ ⌜∀ c m, N !! c = some m → ∀ n, m ≤ n → s.reg c n = none⌝ ∗
    ghostMapAuth g.regm (1 : Qp).half M ∗
      ⌜∀ c n, s.reg c n = (M !! (c, n)).map (fun v => v.2.2.2)⌝ ∗
      ([∗map] k ↦ v ∈ M, sysEntry s.lin k v) ∗
    sizedI g F M s)

def sysBody (g : GN) : IProp GF := iprop(∃ s, sysAt g s)

def sysInvI (g : GN) : IProp GF := inv sysNI (sysBody g)

/-- The commit's result for request input `i` with reply string `r`. -/
def Done (i : KvInI) (Q : Store → Store → KvOutI → IProp GF) (r : GoString) :
    IProp GF :=
  iprop(∃ σ σ', Q σ σ' (outOfReplyI i r) ∗
    ⌜kvStep σ i σ' (outOfReplyI i r)⌝)

def reqBody (i : KvInI) (Q : Store → Store → KvOutI → IProp GF) (γt : GName) :
    Option GoString → IProp GF
  | none => emp
  | some r => iprop(Done i Q r ∨ token γt)

/-- Request invariant's contents. -/
def reqInv (i : KvInI) (Q : Store → Store → KvOutI → IProp GF) (γs γt : GName) :
    IProp GF :=
  iprop(∃ st : Option GoString, ghostVar γs (1 : Qp).half st ∗ reqBody i Q γt st)

/-- The system's namespaces (every invariant of the ghost layer is below it): the mask remote's
update for the key-value store leaves open (`RBase.Eop`). -/
def vsrE : CoPset := ↑(ndot nroot "vsr")

theorem sysNI_vsrE : (↑sysNI : CoPset) ⊆ vsrE := by unfold sysNI vsrE; solve_ndisj
theorem regNI_vsrE : (↑regNI : CoPset) ⊆ vsrE := by unfold regNI vsrE; solve_ndisj

/-- A client's update for input `i` with commit postcondition `Q`: remote's one-shot update
(`remote.lin`, over the store's state `absOwnI`), in the relational form the lab's atomic update
had (the step is a function: `kvStep`). -/
def AUof (g : GN) (i : KvInI) (Q : Store → Store → KvOutI → IProp GF) : IProp GF :=
  iprop(|={⊤ \ vsrE, ∅}=> ∃ σ, absOwnI g σ ∗
    ∀ σ' o, absOwnI g σ' ∗ ⌜kvStep σ i σ' o⌝ -∗ |={∅, ⊤ \ vsrE}=> Q σ σ' o)

/-- The registry invariant's part of registered request `k`. -/
def regEntry (g : GN) (k : Nat × Nat) (v : RegVal) : IProp GF :=
  iprop((∃ Q, AUof g v.2.2.2 Q ∗ inv (reqNI k) (reqInv v.2.2.2 Q v.1 v.2.1)) ∨ token v.2.2.1)

def regBody (g : GN) : IProp GF :=
  iprop(∃ M : GMap (Nat × Nat) RegVal, ghostMapAuth g.regm (1 : Qp).half M ∗
    [∗map] k ↦ v ∈ M, regEntry g k v)

def regInvI (g : GN) : IProp GF := inv regInvN (regBody g)

def ticketI (g : GN) (c n : Nat) (i : KvInI) (Q : Store → Store → KvOutI → IProp GF) :
    IProp GF :=
  iprop(∃ γs γt γp, ghostMapElem g.regm (c, n) DFrac.discard ((γs, γt, γp, i) : RegVal) ∗
    token γt ∗ inv (reqNI (c, n)) (reqInv i Q γs γt))

/-! ## Instances -/

instance factI_persistent (g : GN) (f : Fact) : Persistent (factI (GF := GF) g f) := by
  unfold factI; infer_instance

instance factI_timeless (g : GN) (f : Fact) : Timeless (factI (GF := GF) g f) := by
  unfold factI; infer_instance

instance absOwnI_timeless (g : GN) (σ : Store) : Timeless (absOwnI (GF := GF) g σ) := by
  unfold absOwnI; infer_instance

instance pendTok_timeless (γp : GName) (st : Option GoString) : Timeless (pendTok (GF := GF) γp st) := by
  cases st <;> unfold pendTok <;> infer_instance

instance sysEntry_timeless (lin : List Entry) (k : Nat × Nat) (v : RegVal) :
    Timeless (sysEntry (GF := GF) lin k v) := by
  unfold sysEntry; infer_instance

instance sizedI_timeless (g : GN) (F : GMap Fact Unit) (M : GMap (Nat × Nat) RegVal) (s : Sys) :
    Timeless (sizedI (GF := GF) g F M s) := by
  unfold sizedI; infer_instance

set_option synthInstance.maxSize 1024 in
set_option synthInstance.maxHeartbeats 200000 in
instance sysAt_timeless (g : GN) (s : Sys) : Timeless (sysAt (GF := GF) g s) := by
  unfold sysAt; infer_instance

instance sysBody_timeless (g : GN) : Timeless (sysBody (GF := GF) g) := by
  unfold sysBody; infer_instance

instance sysInvI_persistent (g : GN) : Persistent (sysInvI (GF := GF) g) := by
  unfold sysInvI; infer_instance

instance regInvI_persistent (g : GN) : Persistent (regInvI (GF := GF) g) := by
  unfold regInvI; infer_instance

end defs

end VsrGhost.Impl

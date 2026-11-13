/-
The shared mode of the tree: its resources (`TreeShared.lean` has the API,
`notes/wal-fsext-i2-design.md`): the claims as a function of the history (`namesOf`), their
coherence (`NamesCoh`), the log as a map (`logMap`), and the resources (`osNames`, `osCallPerm`,
`osCallS`, `osLogLb`, `osLogEnt`, `osDirFdS`, `osSpine`, `osPathS`, `osSharedInv`, `osLogged`,
`osNamesAfter`). Untrusted.
-/
module

public import GooseLang.Ext.Fs.TreeCrashCommit
public import GooseLang.Ext.Fs.TreeSpecsOpen
public import GooseLang.Ext.Fs.TreeSpecsMeta
public import GooseLang.Ext.Fs.TreeCutProof

@[expose] public section

noncomputable section

namespace Perennial
namespace Fs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode
/-! ## What the claims know, as a function of the history -/

open Classical in
/-- The claim on the names `N` of the directory `j`, as the history `V` has them: their entries at
boot, each entry writing one of them (with their entries right after), their entries now. -/
def namesOf (V : Hist) (j : Ino) (N : NameSet) : NamesH where
  boot := restrictN N (entsOf V.1 j)
  ents := (List.range V.2.length).filterMap (fun x => match V.2[x]? with
    | some e => if ∃ b, N.Mem b ∧ e.op.Writes j b then
        some (x, e, restrictN N (entsOf (prefTree V.1 V.2 (x + 1)) j)) else none
    | none => none)
  cur := restrictN N (entsOf V.now j)

/-- The claims' coherence with the shared history `V`: each claim's history is the history's; the
claims of a directory are disjoint; every name of every directory of the tree is claimed. -/
structure NamesCoh (V : Hist) (Γn : GMap (Ino × NameSet) NamesH) : Prop where
  hist : ∀ j N h, Γn !! (j, N) = some h → h = namesOf V j N
  disj : ∀ j N N' h h' b, Γn !! (j, N) = some h → Γn !! (j, N') = some h' → N ≠ N' →
    N.Mem b → ¬ N'.Mem b
  cover : ∀ j b, j ∈ V.now → ∃ N h, Γn !! (j, N) = some h ∧ N.Mem b

/-- The log's entries, as a map. -/
def logMap (log : List LogEntry) : GMap Nat LogEntry :=
  (List.range log.length).foldl (fun m x => match log[x]? with
    | some e => <[x := e]> m
    | none => m) ∅

section resources
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]

/-- The namespace of the shared mode's invariant (disjoint from `osN`). -/
def osShN : Namespace := nroot .@ "osfsShared"

/-- A claim on the names `N` of the directory `j`, `h` what is known of them. -/
def osNames (j : Ino) (N : NameSet) (dq : DFrac) (h : NamesH) : IProp GF :=
  gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γn (j, N) dq h

/-- A fraction `q` of the call permission. -/
def osCallPerm (q : Qp) : IProp GF :=
  gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γperm () (DFrac.own q) ()

/-- The shared call `t` is in flight, begun when the log had `s` entries, holding `q` of the call
permission (in the state interpretation), which its step gives back. -/
def osCallS (t s : Nat) (q : Qp) : IProp GF :=
  gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γcS t (DFrac.own 1) (s, q)

/-- The log has at least `n` entries (persistent). -/
def osLogLb (n : Nat) : IProp GF :=
  letI := (gooseOsGS (L := L)).osAllG; monoNatLbOwn (gooseOsGS (L := L)).γlen n

/-- The entry `x` of the log is `e` (persistent). -/
def osLogEnt (x : Nat) (e : LogEntry) : IProp GF :=
  gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γlog x DFrac.discard e

/-- The shared directory fd `fd`, on the directory `j`, its read at `ph`. -/
def osDirFdS (fd : w64) (j : Ino) (ph : DirPhS) : IProp GF :=
  gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γdfS fd (DFrac.own 1) (j, ph)

/-- The components `cs` lead from the directory `j` to the directory `j'`: fractions `dq` of the
claim on each component's name, which names the next directory. -/
def osSpine : Ino → List GoString → DFrac → Ino → IProp GF
  | j, [], _, j' => iprop(⌜j = j'⌝)
  | j, c :: cs, dq, j' => iprop(∃ (h : NamesH) (J : Ino),
      osNames j (.only [c]) dq h ∗ ⌜h.cur !! c = some (.dir J)⌝ ∗ osSpine J cs dq j')

/-- The path `p` names the directory `j`: a root of `R` followed by components, each held by a
fraction of its claim. -/
def osPathS (R : Roots) (p : GoString) (dq : DFrac) (j : Ino) : IProp GF :=
  iprop(∃ (r : GoString) (j0 : Ino) (cs : List GoString),
    ⌜(r, j0) ∈ R ∧ (∀ c ∈ cs, NameOk c) ∧ p = joinPath r cs⌝ ∗ osSpine j0 cs dq j)

/-- **The shared mode's invariant**, on the roots `R`: the shared history `Vs`, whole; the claims'
authority, coherent with it; the log's length and entries. -/
def osSharedInv (R : Roots) : IProp GF :=
  inv osShN iprop(∃ (Vs : Hist) (Γn : GMap (Ino × NameSet) NamesH),
    gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γs () (DFrac.own 1) (R, Vs) ∗
    gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γn Γn ∗ ⌜RootsOk R ∧ NamesCoh Vs Γn⌝ ∗
    (letI := (gooseOsGS (L := L)).osAllG; monoNatAuthOwn (gooseOsGS (L := L)).γlen 1 Vs.2.length) ∗
    gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γlog (logMap Vs.2))

instance osSharedInv_persistent (R : Roots) : Persistent (osSharedInv (L := L) R) := by
  unfold osSharedInv; infer_instance
instance osLogLb_persistent (n : Nat) : Persistent (osLogLb (L := L) n) := by
  unfold osLogLb; letI := (gooseOsGS (L := L)).osAllG; infer_instance
instance osLogEnt_persistent (x : Nat) (e : LogEntry) : Persistent (osLogEnt (L := L) x e) := by
  unfold osLogEnt gElem; letI := (gooseOsGS (L := L)).osAllG; infer_instance
instance osNames_timeless (j : Ino) (N : NameSet) (dq : DFrac) (h : NamesH) :
    Timeless (osNames (L := L) j N dq h) := by unfold osNames; infer_instance
instance osCallPerm_timeless (q : Qp) : Timeless (osCallPerm (L := L) q) := by
  unfold osCallPerm; infer_instance
instance osCallS_timeless (t s : Nat) (q : Qp) : Timeless (osCallS (L := L) t s q) := by
  unfold osCallS; infer_instance
instance osDirFdS_timeless (fd : w64) (j : Ino) (ph : DirPhS) :
    Timeless (osDirFdS (L := L) fd j ph) := by unfold osDirFdS; infer_instance

/-- An entry logged at `x ≥ s` by a call begun at `s`: its record, and the log's new length. -/
def osLogged (x : Nat) (e : LogEntry) : IProp GF :=
  iprop(⌜e.start ≤ x⌝ ∗ osLogEnt (L := L) x e ∗ osLogLb (L := L) (x + 1))

/-- A claim after a step that may log `e`: as it was (only if `may` allows no effect), or the entry
logged, the names now `c`. -/
def osNamesAfter (j : Ino) (N : NameSet) (h : NamesH) (e : LogEntry) (c : Ents) (none_ok : Prop) :
    IProp GF :=
  iprop((⌜none_ok⌝ ∗ osNames (L := L) j N (DFrac.own 1) h) ∨
    ∃ x, osLogged (L := L) x e ∗ osNames (L := L) j N (DFrac.own 1) (h.log x e (restrictN N c)))

end resources

section claims
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF]

/-- The claims of a list, each with its fraction. -/
def osClaims (L : GooseLocalGS GF) (cl : List (Claim × DFrac)) : IProp GF :=
  iprop([∗list] c ∈ cl, osNames (L := L) c.1.1 c.1.2.1 c.2 c.1.2.2)

theorem osClaims_cons (L : GooseLocalGS GF) (c : Claim × DFrac) (cl : List (Claim × DFrac)) :
    osClaims L (c :: cl) ⊣⊢ osNames (L := L) c.1.1 c.1.2.1 c.2 c.1.2.2 ∗ osClaims L cl :=
  by unfold osClaims; exact BigSepL.bigSepL_cons

end claims

end Fs
end Perennial

end

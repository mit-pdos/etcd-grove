/-
The tree's resources (`TreeShared.lean` has the API, `notes/wal-fsext-i2-design.md`,
`notes/fs-interp-state-determined.md`; the claims as a function of the history, `namesOf`, their
coherence, `NamesCoh`, and the log as a map, `logMap`, are in `NamesGhost.lean`): the resources (`osNames`, `osCallPerm`,
`osCallS`, `osLogLb`, `osLogEnt`, `osDirFdS`, `osSpine`, `osPathS`, `osSharedInv`, `osLogged`,
`osNamesAfter`), and what a generation starts with (`osShared`, from `osSwitchKitG`:
`osSwitchKit_open`). Untrusted.
-/
module

public import GooseLang.Ext.Fs.TreeCommit
public import GooseLang.Ext.Fs.TreeStepLemmas

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace Fs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode
/-! ## What the claims know, as a function of the history -/

theorem isUnder_prefix {a x : GoString} (h : IsUnder a x) :
    (a ++ [slashB]).IsPrefix (x ++ [slashB]) := by
  rcases h with rfl | h
  · exact List.prefix_refl _
  · exact h.trans (List.prefix_append _ _)

/-- **A path is under at most one root** (well-formed roots: none under another). -/
theorem root_of_isUnder {R : List (GoString × Ino)} (hR : RootsOk R) {r r' : GoString × Ino}
    (hr : r ∈ R) (hr' : r' ∈ R) {x : GoString} (h : IsUnder r.1 x) (h' : IsUnder r'.1 x) :
    r = r' := by
  suffices he : r.1 = r'.1 from eq_of_nodup_map hR.1 hr hr' he
  apply Classical.byContradiction; intro hne
  have p1 := isUnder_prefix h
  have p2 := isUnder_prefix h'
  -- the shorter of the two roots, with its slash, is a prefix of the other root
  have key : ∀ {a b : GoString × Ino}, a ∈ R → b ∈ R → a.1 ≠ b.1 →
      (a.1 ++ [slashB]).IsPrefix (x ++ [slashB]) → (b.1 ++ [slashB]).IsPrefix (x ++ [slashB]) →
      a.1.length ≤ b.1.length → False := by
    intro a b ha hb hab pa pb hl
    have hab' : (a.1 ++ [slashB]).IsPrefix (b.1 ++ [slashB]) :=
      List.prefix_of_prefix_length_le pa pb (by simp; omega)
    rcases Nat.lt_or_ge a.1.length b.1.length with hlt | hge
    · have : (a.1 ++ [slashB]).IsPrefix b.1 :=
        List.prefix_of_prefix_length_le hab' (List.prefix_append _ _) (by simp; omega)
      exact (hR.2.2 a ha).2 b hb hab (.inr this)
    · have hlen : a.1.length = b.1.length := by omega
      have := hab'.eq_of_length (by simp [hlen])
      exact hab (List.append_cancel_right this)
  rcases Nat.le_total r.1.length r'.1.length with hl | hl
  · exact key hr hr' hne p1 p2 hl
  · exact key hr' hr (Ne.symm hne) p2 p1 hl

/-- The key of a path under the root `rj`. -/
theorem callKey_eq {R : Roots} (hR : RootsOk R) {rj : GoString × Ino} (hrj : rj ∈ R) {p : GoString}
    (h : IsUnder rj.1 p) : callKey R p = rj.1 := by
  have hex : ∃ rj ∈ R, IsUnder rj.1 p := ⟨rj, hrj, h⟩
  unfold callKey; rw [dif_pos hex]
  have := hex.choose_spec
  rw [root_of_isUnder hR this.1 hrj this.2 h]

/-- Two paths in one root's tree have one key. -/
theorem callKey_of_sameRoot {R : Roots} (hR : RootsOk R) {a b : GoString} (h : SameRootR R a b) :
    callKey R b = callKey R a := by
  obtain ⟨rj, hrj, ha, hb⟩ := h
  rw [callKey_eq hR hrj ha, callKey_eq hR hrj hb]

/-- A path of a root's tree has the root's key. -/
theorem callKey_joinPath {R : Roots} (hR : RootsOk R) {r : GoString} {j0 : Ino} (hm : (r, j0) ∈ R)
    (cs : List GoString) : callKey R (joinPath r cs) = callKey R r := by
  rw [callKey_eq hR hm (isUnder_joinPath _ _), callKey_eq hR hm (.inl rfl)]

section resources
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]

/-- The namespace of the shared mode's invariant (disjoint from `osN`). -/
def osShN : Namespace := nroot .@ "osfsShared"

/-- A claim on the names `N` of the directory `j`, `h` what is known of them. A claim on no
name (`.only []`, the only key of the empty set) knows nothing (`NamesH.empty`) and is no ghost
resource: so splitting off an empty part never meets another empty claim's key. -/
def osNames (j : Ino) (N : NameSet) (dq : DFrac) (h : NamesH) : IProp GF :=
  if N = .only [] then iprop(⌜h = NamesH.empty⌝)
  else gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γn (j, N) dq h

theorem osNames_of_ne {j : Ino} {N : NameSet} (dq : DFrac) (h : NamesH) (hN : N ≠ .only []) :
    osNames (L := L) j N dq h = gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γn (j, N) dq h := by
  unfold osNames; rw [if_neg hN]

theorem osNames_except (j : Ino) (bs : List GoString) (dq : DFrac) (h : NamesH) :
    osNames (L := L) j (.except bs) dq h =
      gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γn (j, NameSet.except bs) dq h :=
  osNames_of_ne dq h (by simp)

/-- A fraction `q` of the call permission of the key `r` (a root, or `[]`: a call on a path `p`
takes its key's, `callKey R p`). -/
def osCallPerm (r : GoString) (q : Qp) : IProp GF :=
  gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γperm r (DFrac.own q) ()

/-- The whole call permission of every root's key: what a generation starts with (`osShared`). The
key `[]` (the paths under no root) goes to `osAboveInv`. -/
def osCallPerms (R : Roots) : IProp GF :=
  iprop([∗map] r ↦ _u ∈ GMap.delete [] (permMap R), osCallPerm r 1)

/-- The namespace of the dispenser of key `[]` (disjoint from `osN` and `osShN`). -/
def osAbN : Namespace := nroot .@ "osfsAbove"

/-- **The dispenser of key `[]`**, the call permission of the paths under no root (the strict
ancestors of the roots, which the environment keeps existing directories): it holds some fraction of
key `[]` and hands out half of what it holds on each take (`osAboveInv_take`), so a call above the
roots needs no share of its own (`CallBegin` above a root, then `Stat`, `OpenDir`, `Fsync` of the
directory: `os.Stat.specAboveRoot`, `fileutil.OpenDir.specAboveRoot`, `fileutil.syncDir.specAboveRoot`).
Allocated at a generation's start (`osSwitchKit_open`) from key `[]`'s whole permission, which no one gets back:
**no proof needs the whole of key `[]`**. The whole permission of a key is what a directory operation
(mkdir, rmdir, rename, unlink of a directory) on a path of that key needs (its `WholeG`/sole
clauses); no client mutates a directory above a root (the os specs exist only for read-only calls
there, and a mutation above a root is outside every client's paths), so the dispenser loses nothing a
proof could need. -/
def osAboveInv : IProp GF :=
  inv osAbN iprop(∃ q, osCallPerm [] q)

/-- The shared call `t` is in flight, begun on the path `p` when the log had `s` entries, holding `q`
of the call permission (in the state interpretation), which its step gives back. -/
def osCallS (t s : Nat) (p : GoString) (q : Qp) : IProp GF :=
  gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γcS t (DFrac.own 1) ((s, p), q)

/-- The shared **guard call** `t` is in flight, begun on `p` when the log had `s` entries, holding `g` of
the call permission (in the state interpretation). A guard never logs: it is ended by
`wp_osLstatDirGuardS`, which gives `g` back. While it is in flight no call can hold the whole
permission (so no directory is renamed), and a logging call holding the rest (`q + g = 1`, begun
no earlier than the guard) may do a directory operation (`wp_osRmdirSG`, `wp_osMkdirSG`). -/
def osGuardS (t s : Nat) (p : GoString) (g : Qp) : IProp GF :=
  gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γg t (DFrac.own 1) ((s, p), g)

/-- The log has at least `n` entries (persistent). -/
def osLogLb (n : Nat) : IProp GF :=
  letI := (gooseOsGS (L := L)).osAllG; monoNatLbOwn (gooseOsGS (L := L)).γlen n

/-- The entry `x` of the log is `e` (persistent). -/
def osLogEnt (x : Nat) (e : LogEntry) : IProp GF :=
  gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γlog x DFrac.discard e

/-- The shared directory fd `fd`, on the directory `j`, its read at `ph`. -/
def osDirFdS (fd : w64) (j : Ino) (ph : DirPhS) : IProp GF :=
  gFdElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γdfS fd (DFrac.own 1) (j, ph)

/-- The components `cs` lead from the directory `j` to the directory `j'`: fractions `dq` of the
claim on each component's name, which names the next directory. -/
def osSpine : Ino → List GoString → DFrac → Ino → IProp GF
  | j, [], _, j' => iprop(⌜j = j'⌝)
  | j, c :: cs, dq, j' => iprop(∃ (h : NamesH) (J : Ino),
      osNames j (.only [c]) dq h ∗ ⌜h.cur !! c = some (.dir J)⌝ ∗ osSpine J cs dq j')

/-- The path `p` names the directory `j`: a root of `R` (well-formed roots, so the split of `p`
is unique) followed by components, each held by a fraction of its claim. -/
def osPathS (R : Roots) (p : GoString) (dq : DFrac) (j : Ino) : IProp GF :=
  iprop(∃ (r : GoString) (j0 : Ino) (cs : List GoString),
    ⌜RootsOk R ∧ (r, j0) ∈ R ∧ (∀ c ∈ cs, NameOk c) ∧ p = joinPath r cs⌝ ∗ osSpine j0 cs dq j)

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
instance osAboveInv_persistent : Persistent (osAboveInv (L := L)) := by
  unfold osAboveInv; infer_instance
instance osLogLb_persistent (n : Nat) : Persistent (osLogLb (L := L) n) := by
  unfold osLogLb; letI := (gooseOsGS (L := L)).osAllG; infer_instance
instance osLogEnt_persistent (x : Nat) (e : LogEntry) : Persistent (osLogEnt (L := L) x e) := by
  unfold osLogEnt gElem; letI := (gooseOsGS (L := L)).osAllG; infer_instance
instance osNames_timeless (j : Ino) (N : NameSet) (dq : DFrac) (h : NamesH) :
    Timeless (osNames (L := L) j N dq h) := by unfold osNames; split <;> infer_instance
instance osCallPerm_timeless (r : GoString) (q : Qp) : Timeless (osCallPerm (L := L) r q) := by
  unfold osCallPerm; infer_instance
instance osCallS_timeless (t s : Nat) (p : GoString) (q : Qp) : Timeless (osCallS (L := L) t s p q) := by
  unfold osCallS; infer_instance
instance osDirFdS_timeless (fd : w64) (j : Ino) (ph : DirPhS) :
    Timeless (osDirFdS (L := L) fd j ph) := by unfold osDirFdS; infer_instance

/-- An open shared directory fd is not negative. -/
theorem osDirFdS_nonneg (fd : w64) (j : Ino) (ph : DirPhS) :
    osDirFdS (L := L) fd j ph ⊢ ⌜0 ≤ fd.toInt⌝ := by
  unfold osDirFdS; exact gFdElem_nonneg _ _ _ _ _

/-- An entry logged at `x ≥ s` by a call begun at `s`: its record, and the log's new length. -/
def osLogged (x : Nat) (e : LogEntry) : IProp GF :=
  iprop(⌜e.start ≤ x⌝ ∗ osLogEnt (L := L) x e ∗ osLogLb (L := L) (x + 1))

/-- A claim after a step that may log `e`: as it was (only if `may` allows no effect), or the entry
logged, the names now `c`. -/
def osNamesAfter (j : Ino) (N : NameSet) (h : NamesH) (e : LogEntry) (c : Ents) (none_ok : Prop) :
    IProp GF :=
  iprop((⌜none_ok⌝ ∗ osNames (L := L) j N (DFrac.own 1) h) ∨
    ∃ x, osLogged (L := L) x e ∗ osNames (L := L) j N (DFrac.own 1) (h.log x e (restrictN N c)))

/-- The calls on the names of a spine's directory have its key. -/
theorem osPathS_callKey (R : Roots) (d : GoString) (dq : DFrac) (j : Ino) :
    osPathS (L := L) R d dq j ⊢
      osPathS (L := L) R d dq j ∗ ⌜∀ b, callKey R (child d b) = callKey R d⌝ := by
  unfold osPathS
  iintro ⟨%r, %j0, %cs, %hp, Hs⟩
  isplitl [Hs]
  · iexists r, j0, cs; iframe; ipureintro; exact hp
  · ipureintro
    obtain ⟨hR, hr, -, rfl⟩ := hp
    intro b
    rw [callKey_eq hR hr (by rw [← joinPath_snoc]; exact isUnder_joinPath _ _),
      callKey_eq hR hr (isUnder_joinPath _ _)]

theorem osCallPerm_congr {r r' : GoString} (q : Qp) (h : r = r') :
    osCallPerm (L := L) r q ⊢ osCallPerm (L := L) r' q := by
  subst h; exact .rfl

/-- A share of a spine directory's key is a share of the key of a call on one of its names. -/
theorem osCallPerm_child (R : Roots) (d b : GoString) (dq : DFrac) (j : Ino) (q : Qp) :
    ⊢ osPathS (L := L) R d dq j -∗ osCallPerm (L := L) (callKey R d) q -∗
      osPathS (L := L) R d dq j ∗ osCallPerm (L := L) (callKey R (child d b)) q := by
  iintro Hp Hq
  icases osPathS_callKey R d dq j $$ Hp with ⟨Hp, %hk⟩
  iframe Hp
  iapply osCallPerm_congr q (hk b).symm $$ Hq

/-- The converse of `osCallPerm_child`. -/
theorem osCallPerm_unchild (R : Roots) (d b : GoString) (dq : DFrac) (j : Ino) (q : Qp) :
    ⊢ osPathS (L := L) R d dq j -∗ osCallPerm (L := L) (callKey R (child d b)) q -∗
      osPathS (L := L) R d dq j ∗ osCallPerm (L := L) (callKey R d) q := by
  iintro Hp Hq
  icases osPathS_callKey R d dq j $$ Hp with ⟨Hp, %hk⟩
  iframe Hp
  iapply osCallPerm_congr q (hk b) $$ Hq

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

/-- The claim on no name knows nothing. -/
theorem namesOf_empty (V : Hist) (j : Ino) : namesOf V j (.only []) = NamesH.empty := by
  have hr : ∀ e : Ents, restrictN (.only []) e = ∅ := by
    intro e; apply GMap.ext; intro b; simp [restrictN, NameSet.Mem]
  unfold namesOf NamesH.empty
  simp only [hr, NamesH.mk.injEq, true_and, and_true]
  apply List.filterMap_eq_nil_iff.2
  intro x _
  split
  · simp [NameSet.Mem]
  · rfl

/-- A claim held, with the claims' authority coherent with the history `V`: the history's. -/
theorem osNames_auth (L : GooseLocalGS GF) {V : Hist} {Γn : GMap (Ino × NameSet) NamesH}
    (hcoh : NamesCoh V Γn) (j : Ino) (N : NameSet) (dq : DFrac) (h : NamesH) :
    ⊢ gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γn Γn -∗ osNames (L := L) j N dq h -∗
      ⌜h = namesOf V j N⌝ := by
  iintro HA H
  by_cases hN : N = .only []
  · subst hN
    unfold osNames
    rw [if_pos rfl]
    icases H with %h1
    ipureintro; rw [h1, namesOf_empty]
  · rw [osNames_of_ne dq h hN]
    icases gAuth_lookup _ _ _ _ _ _ $$ HA H with %h1
    ipureintro; exact hcoh.hist _ _ _ h1

end claims

/-! ## A generation's start -/

section start
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]

/-- **The tree's resources of a generation's start** (`fs_start`, `crashRest_treeS'`): the shared
invariant, the dispenser of key `[]`, every other root's whole call permission, the log's lower
bound, a whole claim on all names of every directory of the tree. -/
def osShared (R : Roots) (V : Hist) : IProp GF :=
  iprop(osSharedInv (L := L) R ∗ osAboveInv (L := L) ∗ osCallPerms (L := L) R ∗
    osLogLb (L := L) V.2.length ∗
    [∗list] j ∈ dirsOf V, osNames (L := L) j (.except []) (DFrac.own 1) (namesOf V j (.except [])))

/-- **The tree's invariants**: `osSwitchKitG`'s resources for `osShared`. -/
theorem osSwitchKit_open (R : Roots) (V : Hist) (E : CoPset) :
    ⊢ osSwitchKitG (gooseOsGS (L := L)) R V ={E}=∗ osShared (L := L) R V := by
  unfold osSwitchKitG
  iintro ⟨Hs, Han, %hok, Halen, Halog, Hp0, Hperm, #Hlb, Hcl⟩
  imod inv_alloc osAbN E iprop(∃ q, osCallPerm (L := L) [] q) $$ [Hp0] with #Hab
  · inext; iexists 1; unfold osCallPerm; iexact Hp0
  imod inv_alloc osShN E iprop(∃ (Vs : Hist) (Γn : GMap (Ino × NameSet) NamesH),
    gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γs () (DFrac.own 1) (R, Vs) ∗
    gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γn Γn ∗ ⌜RootsOk R ∧ NamesCoh Vs Γn⌝ ∗
    (letI := (gooseOsGS (L := L)).osAllG; monoNatAuthOwn (gooseOsGS (L := L)).γlen 1 Vs.2.length) ∗
    gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γlog (logMap Vs.2)) $$ [Hs Han Halen Halog]
    with #Hsi
  · inext
    iexists V, (claimsInit V (dirsOf V))
    iframe Hs Han Halen Halog
    ipureintro; exact hok
  imodintro
  unfold osShared
  simp only [osNames_except]
  unfold osSharedInv osAboveInv osCallPerms osCallPerm osLogLb
  iframe Hsi Hab Hperm Hlb Hcl

end start

end Fs
end Perennial

end

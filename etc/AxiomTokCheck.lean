/-
**The `axiom-tok` gate** (per-type stage B: B0, enforcing from CP3; the Scope's §5.1, rules 1-8:
`/shared/tmp/stageB/scope-r5.md`). Not part of the lakefile; run with

    lake env lean --run etc/AxiomTokCheck.lean --axioms=FILE [--depth=N] [--part=ROOT]... MODULE...
    lake env lean --run etc/AxiomTokCheck.lean --selftest=FILE [--depth=N] MODULE...

normally through `etc/axiom-tok-check.py`, which takes the axioms from `.lake/tcb.json` and the
module groups from `etc/proof_roots.py`, and judges the output. One JSON object per line.

**What it guards.** No trusted statement may let its user obtain thread or level tokens (the
resource every fork, every reader slot and every pool borrow is accounted in) beyond what the user
gives it, nor obtain a resource it chose itself (`∀ R, … ⊢ R`), nor resources the axiom invents
(`∃ P, P`) without a declared partner.

**The walk.** For every axiom of `--axioms` present in the environment whose type is a `Prop`, the
statement is walked with a polarity (the user *receives* what is positive and *supplies* what is
negative; `→`, `-∗`, `⊢` and a triple's pre flip their left): definitions are unfolded up to
`--depth` (default 14) deep (`axiom` and `opaque` constants are atoms, never unfolded); `⌜…⌝` is
not walked (it holds no resource); a WP is walked only through its postcondition. The result of a
walk is a set of **scenarios** (one per choice of `∨`/`∧`/`if` branch, the `if`s correlated on
their condition), each with what is produced and what is consumed:

- `tok:*` (rule 1): `threadTok`/`threadToks n`/`threadFuel n` (`T`: one token of every level),
  `levelTok l`/`levelToks l n`/`levelTokList l ks` (`L:l`), `threadTokFrom l`/`threadToksFrom l n`
  (`F:l`), `levelsToks l c n` (`LS:l:c`), `ownThreadLoan γ` (`loan:γ`), and `tok:raw` for any other
  occurrence of the ghost name `threadTokName` (a raw token);
- `atom:x` (rule 3): a `∀`-bound (user-chosen) value of `IProp`-carrying type, or a field of one
  (`cd.PDone`), or of an element of a user-chosen list under a big separating conjunction
  (`ms[].spec`); a consumed application also consumes the atoms among its arguments;
- `opq:C` (rules 5, 6): an `IProp`-valued `axiom`/`opaque` constant `C`.

Multiplicities are counts: a literal, a multiset of symbolic terms (a `∀`-bound `n`, `l.length`),
or unbounded. A symbolic term produced must be matched by the same term consumed (else it is
unbounded: the user picks it); a symbolic term consumed and not matched counts `0`; a symbolic term
over a variable the axiom picks (`∃` at positive polarity) counts `0` produced (rule 1's "when it
would favour the axiom", read as: whoever picks the variable picks its worst value for the check).

**Rules** (per scenario):
- rule 2: for every level point (each concrete or symbolic level mentioned, and a generic one) the
  tokens produced covering it are at most the tokens consumed covering it (`T` covers every level,
  `F:l` the levels from `l`, `L:l` the level `l`); `loan:γ` and `raw` are their own points;
- rule 3: every produced atom is covered by the same atom (or the whole record it is a field of)
  consumed;
- `□ P` at positive polarity: whatever `P` produces beyond what it consumes is unbounded (the user
  can use it any number of times);
- rule 4: `inv`, `ncinv`, `cinv`, `isThreadPool*` are neutral (not unfolded, count nothing); one at
  positive polarity whose body mentions a token is reported (`handle-token`);
- rule 5 (greatest fixpoint): opaque predicates start neutral; an axiom producing `C` that fails
  rule 2 or 3 taints `C`; an axiom producing a tainted `C` is `unknown`; iterated to stability;
- rule 6 (holders): an opaque `C` with no persistent instance and no duplicating axiom, all of whose
  producing axioms (those producing `C` without consuming it) consume a net `k` tokens in every
  scenario producing it, carries `k` (pointwise min over producers and scenarios, literal counts
  only); an axiom consuming `C` is credited `k` per copy before rule 2;
- rule 7 (transfers): an `∃`-bound (axiom-picked, positive) value of `IProp`-carrying type is
  neutral when it occurs only in arguments of opaque constants or neutral handles (or not at all in
  a resource position); otherwise it is a `transfer`, reported with its type key for the driver's
  pair matching (`etc/axiom-tok-allow.txt`); each axiom also lists the type keys of the user-chosen
  `IProp`-carrying binders it consumes (`consumesTypes`), the partner side of a pair;
- m2: a `FuncUnfold` instance for a name holding `#model.` is an error (`modelUnfold`).

Each axiom gets `ok` (no finding) or the findings; the driver turns findings into the list of
entries needed (rule 8). Where the walk cannot proceed (a definition past `--depth`, a stuck
`match`, a term it does not know at `IProp` type) it records a `trunc` note and counts nothing for
that subterm: the driver treats an axiom with such a note as unknown (`--check` fails, unless an
entry names the note). A definition cut at `--depth` is noted only when the constants its body
reaches (transitively, through definitions) include a token, the raw token name, an `IProp`-valued
`axiom`/`opaque` or Iris's `∀`/`∃` (`reachesRes`): otherwise the cut loses nothing.

**Leaving a binder** (`bindVar`, CP3): a user-picked atom's rule-3 verdict is final once the walk
leaves its binder (no later step can name it): a scenario where it passes forgets its counts, one
where it fails keeps its findings as `fail3:` keys (`Scen.closeAtom`). Ghost ownership (`own`,
`iOwn`) is a leaf (a raw token at the token name, else nothing; consumed, it consumes the atoms in
its arguments), and so is any application in consumed position of a variable the walk does not
count (an `∃`-picked `Spec`, an axiom-picked family): it consumes the atoms among its arguments
(`consArgs`; rule 3: the user's `Φ` in `Spec md m Φ Ψe`).

**Scenario sets.** Past `PRUNEAT` scenarios, the ones another scenario dominates (produces no less,
consumes no more, the opaque and callback-return counts equal, under fewer conditions) are dropped
(`Res.prune`): every step of the walk and every rule is monotone in that order, so the verdict does
not change. Past `MAXSCEN` undominated scenarios, the set is collapsed into one worst scenario
(the pointwise max of the productions, min of the consumptions): an axiom that passes collapsed
passes, one that fails collapsed is reported `capped` (unknown). Before pruning, an atom both produced and
consumed drops the common part, and an opaque predicate keeps one copy on each side
(`Scen.cancelAtoms`). Rule 6 credits a consumed holder per copy consumed and not produced back
(a transformer `O -∗ O ∗ …` keeps the tokens inside the `O` it returns; CP3, selftest
`st_refuse_transformer`).
-/
import Lean
open Lean Meta Elab

/-! ## Counts -/

structure Cnt where
  n : Nat := 0
  syms : List String := []
  inf : Bool := false
  deriving Inhabited, BEq, Repr

def Cnt.zero : Cnt := {}
def Cnt.one : Cnt := { n := 1 }
def Cnt.isZero (c : Cnt) : Bool := c.n == 0 && c.syms.isEmpty && !c.inf
def Cnt.add (a b : Cnt) : Cnt := ⟨a.n + b.n, a.syms ++ b.syms, a.inf || b.inf⟩
def Cnt.max (a b : Cnt) : Cnt :=
  -- pointwise max: literal max, symbols union (as multisets: the larger multiplicity)
  let syms := (a.syms ++ b.syms).eraseDups.foldl (fun acc s =>
    acc ++ List.replicate (Nat.max (a.syms.count s) (b.syms.count s)) s) []
  ⟨Nat.max a.n b.n, syms, a.inf || b.inf⟩
def Cnt.min (a b : Cnt) : Cnt :=
  let syms := (a.syms ++ b.syms).eraseDups.foldl (fun acc s =>
    acc ++ List.replicate (Nat.min (a.syms.count s) (b.syms.count s)) s) []
  if a.inf then b else if b.inf then a else ⟨Nat.min a.n b.n, syms, false⟩
def Cnt.mul (a b : Cnt) : Cnt :=
  if a.isZero || b.isZero then Cnt.zero
  else if a.inf || b.inf then { inf := true }
  else
    let cross := a.syms.flatMap fun s => b.syms.map fun t => s ++ "*" ++ t
    ⟨a.n * b.n, (List.replicate a.n b.syms).flatten ++ (List.replicate b.n a.syms).flatten ++ cross,
     false⟩
/-- `p ≤ c`: produced at most consumed. -/
def Cnt.le (p c : Cnt) : Bool := Id.run do
  if c.inf then return true
  if p.inf then return false
  let mut cs := c.syms
  for s in p.syms do
    if cs.contains s then cs := cs.erase s else return false
  return p.n ≤ c.n
def Cnt.show (c : Cnt) : String :=
  if c.inf then "∞" else
  let parts := (if c.n == 0 && !c.syms.isEmpty then [] else [toString c.n]) ++ c.syms
  " + ".intercalate parts
def Cnt.toJson (c : Cnt) : Json := Json.str c.show

/-! ## Scenarios -/

abbrev KMap := List (String × Cnt)

def KMap.get (m : KMap) (k : String) : Cnt := (m.lookup k).getD Cnt.zero
def KMap.addK (m : KMap) (k : String) (c : Cnt) : KMap :=
  if c.isZero then m else
  match m.lookup k with
  | some old => m.map fun (k', v) => if k' == k then (k', old.add c) else (k', v)
  | none => m ++ [(k, c)]
def KMap.merge (f : Cnt → Cnt → Cnt) (a b : KMap) : KMap :=
  let ks := (a.map (·.1) ++ b.map (·.1)).eraseDups
  ks.filterMap fun k => let v := f (a.get k) (b.get k); if v.isZero then none else some (k, v)
def KMap.sum (a b : KMap) : KMap := KMap.merge Cnt.add a b

structure Scen where
  prod : KMap := []
  cons : KMap := []
  conds : List (String × Bool) := []
  deriving Inhabited

abbrev Res := Array Scen

def Res.unit : Res := #[{}]
/-- Past this many scenarios the dominated ones are dropped (`Res.prune`: sound, the verdict does not
change); below it every scenario is kept, so that the findings of small walks name every scenario's
counts. -/
def PRUNEAT : Nat := 64
/-- Past this many undominated scenarios the walk collapses them into one (`capped`: unknown). -/
def MAXSCEN : Nat := 1024

/-- Collapse a too-large scenario set into its worst single scenario. -/
def KMap.norm (m : KMap) : KMap :=
  (m.filter (!·.2.isZero)).toArray.qsort (fun a b => a.1 < b.1) |>.toList

/-- Merge the scenarios with the same production and consumption (their conditions intersected:
fewer constraints, so more combinations later: conservative). -/
def kmapKey (m : KMap) : String :=
  ";".intercalate (m.map fun (k, c) => s!"{k}={c.n}/{c.syms}/{c.inf}")

def Res.dedup (r : Res) : Res := Id.run do
  let mut out : Array Scen := #[]
  let mut idx : Std.HashMap String Nat := {}
  for s in r do
    let s := { s with prod := s.prod.norm, cons := s.cons.norm }
    let key := kmapKey s.prod ++ "|" ++ kmapKey s.cons
    match idx[key]? with
    | some i =>
      let t := out[i]!
      out := out.set! i { t with conds := t.conds.filter fun (k, v) => s.conds.lookup k == some v }
    | none =>
      idx := idx.insert key out.size
      out := out.push s
  return out

/-- The keys a dominated scenario must agree on exactly (`Scen.dominates`): a callback's returned
tokens (`ret:`, which rule 2b subtracts from what is supplied directly: not monotone). -/
def exactKey (k : String) : Bool := k.startsWith "ret:"

def opqSupport (m : KMap) : List String :=
  (m.filter fun (k, c) => k.startsWith "opq:" && !c.isZero).map (·.1)

/-- `a ≤ b` pointwise (normalised maps: sorted keys), the exact keys equal. -/
def KMap.leN : KMap → KMap → Bool
  | [], bs => !(bs.any (exactKey ·.1))
  | (k, c) :: as, [] => !exactKey k && c.isZero && KMap.leN as []
  | (k, c) :: as, (k', c') :: bs =>
    if k' < k then !exactKey k' && KMap.leN ((k, c) :: as) bs
    else if k == k' then
      (if exactKey k then c.le c' && c'.le c else c.le c') && KMap.leN as bs
    else -- k < k': k is absent from b
      !exactKey k && c.isZero && KMap.leN as ((k', c') :: bs)
termination_by a b => a.length + b.length

/-- `s` is at least as bad as `t` for every verdict (rules 2, 3, 6, the mint flag), now and after
any further combination: it produces at least as much, consumes at most as much (the exact keys
equal), and holds under fewer conditions (so it survives every `withCond`/`consistent` filter that
`t` survives). Every operation of the walk (`sep`, `maxc`, `union`, `withCond`, `scale`,
`persistentPos`) is monotone in this order, and rules 2 and 3 are (`Cnt.le` is transitive), so a
scenario dominated by another can be dropped without changing whether the axiom passes; the
findings reported are the dominating (worst) scenario's. -/
def Scen.dominates (s t : Scen) : Bool :=
  s.conds.all (fun (k, v) => t.conds.lookup k == some v) && t.prod.leN s.prod && s.cons.leN t.cons &&
  -- the opaque predicates produced, and those consumed, are the same (rule 5's taint reads the
  -- first; rule 6 tells a source, produced and not consumed, from a duplicating law, consumed
  -- fewer times than produced: with the counts ordered as above, `s` is then a source, or
  -- duplicates, when `t` does, with no more net tokens consumed and no more credit)
  opqSupport s.prod == opqSupport t.prod && opqSupport s.cons == opqSupport t.cons

/-- What `a` and `b` have in common (literal part, symbolic terms as multisets); nothing when one
is unbounded. -/
def Cnt.common (a b : Cnt) : Cnt :=
  if a.inf || b.inf then Cnt.zero else
  let syms := a.syms.eraseDups.foldl (fun acc s =>
    acc ++ List.replicate (Nat.min (a.syms.count s) (b.syms.count s)) s) []
  ⟨Nat.min a.n b.n, syms, false⟩
def Cnt.sub (a b : Cnt) : Cnt :=
  ⟨a.n - b.n, b.syms.foldl (fun acc s => acc.erase s) a.syms, a.inf⟩

/-- An atom both produced and consumed in a scenario: the common part dropped from both sides
(rule 3 compares the production of an atom with the consumption of it and of the records it is a
field of: `p + x ≤ c + x` iff `p ≤ c`, and every later step adds to or scales both sides alike).
Only for an atom no field of which (`k.…`, `k[]`) occurs in the scenario, whose consumption covers
it too; a field added by a later step then finds less consumed (more findings, never fewer).
An opaque predicate both produced and consumed keeps one copy on each side (see the loop).
Tokens (whose level coverage differs between production and consumption, `covers`) are left
alone. -/
def Scen.cancelAtoms (s : Scen) : Scen := Id.run do
  let keys := (s.prod ++ s.cons).map (·.1)
  let mut prod := s.prod
  let mut cons := s.cons
  for (k, p) in s.prod do
    if k.startsWith "opq:" then
      -- an opaque predicate both produced and consumed: the literal common part beyond one copy
      -- dropped from both sides, so that whether it is produced, consumed, duplicated (rule 6:
      -- consumed fewer times than produced) or a source, and the net consumption that rule 6
      -- credits, stay the same
      let c := cons.get k
      if p.n ≥ 2 && c.n ≥ 2 then
        let m : Cnt := { n := Nat.min p.n c.n - 1 }
        prod := prod.map fun (k', v) => if k' == k then (k', v.sub m) else (k', v)
        cons := cons.map fun (k', v) => if k' == k then (k', v.sub m) else (k', v)
      continue
    if !k.startsWith "atom:" then continue
    if keys.any (fun k' => k'.startsWith (k ++ ".") || k'.startsWith (k ++ "[]")) then continue
    let c := cons.get k
    let m := p.common c
    if m.isZero then continue
    prod := prod.map fun (k', v) => if k' == k then (k', v.sub m) else (k', v)
    cons := cons.map fun (k', v) => if k' == k then (k', v.sub m) else (k', v)
  return { s with prod := prod.norm, cons := cons.norm }

/-- The scenarios no other scenario dominates (the first of mutually dominating ones). Expects
normalised maps (`Res.dedup`). -/
def Res.prune (r : Res) : Res := Id.run do
  let mut kept : Array Scen := #[]
  for x in r do
    if kept.any (·.dominates x) then continue
    kept := (kept.filter fun k => !x.dominates k).push x
  return kept

def Res.cap (r0 : Res) : Res :=
  let r := r0.dedup
  if r.size ≤ PRUNEAT then r else
  let r := Res.prune (Res.dedup (r.map Scen.cancelAtoms))
  if r.size ≤ MAXSCEN then r else
  let p := r.foldl (fun acc s => KMap.merge Cnt.max acc s.prod) []
  let c := r.foldl (fun acc s => KMap.merge Cnt.min acc s.cons) (r[0]!.cons)
  #[{ prod := p, cons := c, conds := [("<capped>", true)] }]

def consistent (a b : List (String × Bool)) : Bool :=
  a.all fun (k, v) => match b.lookup k with | some w => v == w | none => true

def Res.combine (f : KMap → KMap → KMap) (a b : Res) : Res := Id.run do
  let mut out : Res := #[]
  for x in a do
    for y in b do
      if consistent x.conds y.conds then
        out := out.push { prod := f x.prod y.prod, cons := f x.cons y.cons,
                          conds := (x.conds ++ y.conds).eraseDups }
  if out.isEmpty then out := #[{}]
  return out.cap
def Res.sep (a b : Res) : Res := Res.combine KMap.sum a b
def Res.maxc (a b : Res) : Res := Res.combine (KMap.merge Cnt.max) a b
def Res.union (a b : Res) : Res := (a ++ b).cap
def Res.withCond (r : Res) (k : String) (v : Bool) : Res :=
  r.filterMap fun s => match s.conds.lookup k with
    | some w => if w == v then some s else none
    | none => some { s with conds := (k, v) :: s.conds }
def Res.scale (r : Res) (k : Cnt) : Res :=
  r.map fun s => { s with prod := s.prod.map (fun (x, c) => (x, k.mul c)) |>.filter (!·.2.isZero),
                          cons := s.cons.map (fun (x, c) => (x, k.mul c)) |>.filter (!·.2.isZero) }

/-! ## The walk -/

inductive Pol | pos | neg
  deriving BEq, Inhabited
def Pol.flip : Pol → Pol | .pos => .neg | .neg => .pos

inductive VKind
  | user (key : String) -- picked by the axiom's user, IProp-carrying: a parametric atom
  | plain         -- picked by the axiom's user, not IProp-carrying
  | ax            -- picked by the axiom
  | ex (idx : Nat) -- ∃ at positive polarity, IProp-carrying: a transfer candidate
  | elem (parent : String) -- an element of a list (big op); `parent` is the user list's atom key, or ""
  deriving Inhabited

structure ExInfo where
  name : String
  ty : String
  tyKey : String
  naked : Array String := #[]
  deriving Inhabited

structure WS where
  vars : Std.HashMap FVarId VKind := {}
  exs : Array ExInfo := #[]
  notes : Array String := #[]
  trunc : Array String := #[]
  consTypes : Array String := #[]
  fuel : Nat := 0
  /-- How many times the current position's polarity was flipped (by `-∗`, `→`, `⊢`'s left). -/
  flips : Nat := 0
  /-- How many Hoare triples (or WPs) the user supplies enclose the current position: a
  user-supplied triple's `∀ Φ` at negative polarity, or a WP's postcondition at negative polarity. -/
  cbDepth : Nat := 0
  nkeys : Nat := 0
  /-- `reachesRes` of a constant, across the axioms of a run (`analyze` threads it). -/
  reach : Std.HashMap Name Bool := {}
  deriving Inhabited

abbrev W := StateRefT WS MetaM

def inCallback (x : W α) : W α := do
  modify fun st => { st with cbDepth := st.cbDepth + 1 }
  try x finally modify fun st => { st with cbDepth := st.cbDepth - 1 }

def flipped (x : W α) : W α := do
  modify fun st => { st with flips := st.flips + 1 }
  try x finally modify fun st => { st with flips := st.flips - 1 }

structure Cfg where
  depth : Nat := 14
  fuel : Nat := 400000
  /-- Print each axiom's name before its walk (`--trace`, to find a slow one). -/
  trace : Bool := false

def note (s : String) : W Unit := modify fun st =>
  if st.notes.contains s || st.notes.size > 40 then st else { st with notes := st.notes.push s }
def truncNote (s : String) : W Unit := modify fun st =>
  if st.trunc.contains s || st.trunc.size > 40 then st else { st with trunc := st.trunc.push s }

def lastStr (n : Name) : String := match n with | .str _ s => s | _ => ""

/-- Whether a constant is, by itself, something the walk counts or must see: a token (rule 1), the
raw token name, an `IProp`-valued `axiom`/`opaque` (rules 5, 6), or Iris's `∀`/`∃` (a binder the
walk would turn into an atom or a transfer, rules 3, 7). -/
def resConst (env : Environment) (c : Name) : Bool := Id.run do
  let s := lastStr c
  if c.getRoot == `Perennial && ["threadTok", "threadToks", "threadFuel", "levelTok", "levelToks",
      "levelTokList", "threadTokList", "threadTokFrom", "threadToksFrom", "levelsToks",
      "ownThreadLoan", "threadTokName"].contains s then return true
  if c.getRoot == `Iris && (s == "forall" || s == "exists") then return true
  match env.find? c with
  | some (.axiomInfo i) | some (.opaqueInfo { toConstantVal := i, .. }) =>
    let mut t := i.type
    while t.isForall do t := t.bindingBody!
    let h := t.getAppFn
    return h.isConstOf `Iris.IProp || h.isConstOf `Iris.UPred
  | _ => return false

/-- `reachesRes` on one constant: depth-first, memoizing every positive answer (each constant on
the path to a `resConst` reaches it); a constant met again on the current path counts `false` there
(the cycle adds nothing), so a negative answer is memoized only by `reachesRes`, once the whole
closure is explored. -/
partial def reachC (env : Environment) (c : Name) (visiting : IO.Ref (Std.HashSet Name)) : W Bool := do
  match (← get).reach[c]? with
  | some r => return r
  | none => pure ()
  let vs ← visiting.get
  if vs.contains c then return false
  if vs.size > 50000 then return true
  visiting.set (vs.insert c)
  let mut r := resConst env c
  if !r then
    if let some (.defnInfo d) := env.find? c then
      for d' in d.value.getUsedConstants do
        if ← reachC env d' visiting then r := true; break
  if r then modify fun st => { st with reach := st.reach.insert c true }
  return r

/-- Whether any constant reachable from `roots` through definitions' bodies is a `resConst`: if
not, a term built from them holds nothing the walk counts (besides the free variables in it, which
`stuck` looks at), so cutting the walk there at `--depth` loses nothing. Memoized across the
axioms of a run; a closure past 50000 constants counts as reaching one. -/
def reachesRes (roots : Array Name) : W Bool := do
  let env ← getEnv
  let visiting ← IO.mkRef ({} : Std.HashSet Name)
  let mut found := false
  for c in roots do
    if ← reachC env c visiting then found := true; break
  if !found then
    -- the whole closure was explored and holds no `resConst`
    let vs ← visiting.get
    modify fun st => { st with reach := vs.fold (fun m c => m.insert c false) st.reach }
  return found

def isIrisName (c : Name) (s : String) : Bool := c.getRoot == `Iris && lastStr c == s
def isPerName (c : Name) (s : String) : Bool := c.getRoot == `Perennial && lastStr c == s

def NEUTRAL : List String := ["inv", "ncinv", "cinv", "isThreadPool", "isThreadPoolC",
  "isThreadPoolL", "isThreadPoolCL"]
def isNeutral (c : Name) : Bool :=
  (c.getRoot == `Iris || c.getRoot == `Perennial) && NEUTRAL.contains (lastStr c)

/-- Ghost ownership, `own γ a` (Perennial's) and `iOwn γ a` (Iris's): a leaf (`walkI`). -/
def isGhostOwn (c : Name) : Bool :=
  c == `Perennial.own || c == `Iris.iOwn

def TOKS : List String := ["threadTok", "threadToks", "threadFuel", "levelTok", "levelToks",
  "levelTokList", "threadTokList", "threadTokFrom", "threadToksFrom", "levelsToks", "ownThreadLoan"]
def isTok (c : Name) : Bool := c.getRoot == `Perennial && TOKS.contains (lastStr c)

def mentionsTok (e : Expr) : Bool :=
  (e.find? fun x => match x with
    | .const c _ => isTok c || lastStr c == "threadTokName"
    | _ => false).isSome

def ppS (e : Expr) : MetaM String := do
  let s := toString (← ppExpr e)
  return if s.length > 120 then (s.take 117).toString ++ "..." else s

def ppKey (e : Expr) : MetaM String := do
  return toString (← withOptions (fun o => o.setBool `pp.fieldNotation true) (ppExpr e))

/-- Whether a type carries `IProp`: a function into `IProp`, or a structure with such a field, or a
container of such (depth-limited). -/
partial def carriesIProp (t : Expr) (d : Nat := 3) : MetaM Bool := do
  if d == 0 then return false
  let t ← instantiateMVars t
  forallTelescopeReducing t (whnfType := false) fun _ b => do
    let b := b.consumeMData
    match b.getAppFn with
    | .const c _ =>
      if c == `Iris.IProp || c == `Iris.UPred then return true
      let env ← getEnv
      if [`List, `Option, `Array, `Prod, `Sum, `Subtype, `Sigma, `PSigma].contains c then
        for a in b.getAppArgs do
          if ← (try carriesIProp a (d - 1) catch _ => pure false) then return true
        return false
      if isStructure env c then
        let some (.inductInfo iv) := env.find? c | return false
        let some (.ctorInfo cv) := env.find? iv.ctors[0]! | return false
        -- the constructor's field types (parameters instantiated by the type's arguments)
        let ctorTy ← try instantiateForall cv.type (b.getAppArgs.extract 0 iv.numParams) catch _ => pure cv.type
        let r ← forallTelescope ctorTy fun fs _ => do
          for f in fs do
            let ft ← inferType f
            if ← (try carriesIProp ft (d - 1) catch _ => pure false) then return true
          return false
        return r
      return false
    | _ => return false

/-- The type key of an `IProp`-carrying type, for pair matching: its codomain's head, after the
leading `GoString` (address) arguments are dropped ("up to instantiation of address-indexed
families"). -/
def typeKey (t : Expr) : MetaM String := do
  let rec drop (t : Expr) : Expr :=
    match t with
    | .forallE _ d b _ =>
      if !b.hasLooseBVars && (d.isConstOf `Perennial.GoString) then drop b else t
    | _ => t
  ppS (drop t.consumeMData)

/-- Decode a `GoString` literal (a list of `BitVec.ofNat 8 n`, or `w8` literals). -/
partial def decodeGoString (e : Expr) : Option String := do
  let rec go (e : Expr) (acc : List Char) : Option (List Char) :=
    let e := e.consumeMData
    if e.isAppOfArity ``List.nil 1 then some acc.reverse
    else if e.isAppOfArity ``List.cons 3 then
      let h := (e.getArg! 1).consumeMData
      let h := h.getAppArgs.back?.getD h
      let n? : Option Nat := (h.find? fun x => match x with | .lit (.natVal _) => true | _ => false).bind
        fun x => match x with | .lit (.natVal n) => some n | _ => none
      match n? with
      | some n => go (e.getArg! 2) (Char.ofNat n :: acc)
      | none => none
    else none
  let cs ← go e []
  return String.ofList cs

/-- The multiplicity an expression of type `Nat` stands for. -/
partial def multOf (e : Expr) (pol : Pol) : W Cnt := do
  let e := (← instantiateMVars e).consumeMData
  if let some n := e.rawNatLit? then return { n := n }
  if let some n := (← evalNat e |>.run) then return { n := n }
  if e.isAppOfArity ``HAdd.hAdd 6 then
    return (← multOf (e.getArg! 4) pol).add (← multOf (e.getArg! 5) pol)
  if e.isAppOfArity ``HMul.hMul 6 then
    return (← multOf (e.getArg! 4) pol).mul (← multOf (e.getArg! 5) pol)
  -- picked by the axiom, produced: counts 0
  let st ← get
  if pol == .pos then
    let axPicked := (e.find? fun x => match x with
      | .fvar f => match st.vars[f]? with | some (.ex _) | some .ax => true | _ => false
      | _ => false).isSome
    if axPicked then return Cnt.zero
  return { syms := [← ppS e] }

/-- The multiplicity of a list (for a big op). -/
def listMult (l : Expr) (pol : Pol) : W Cnt := do
  let l := (← instantiateMVars l).consumeMData
  if l.isAppOfArity ``List.replicate 3 then return ← multOf (l.getArg! 1) pol
  -- a literal list
  let mut cur := l
  let mut n := 0
  let mut isLit := false
  for _ in [0:100000] do
    if cur.isAppOfArity ``List.nil 1 then isLit := true; break
    else if cur.isAppOfArity ``List.cons 3 then cur := (cur.getArg! 2).consumeMData; n := n + 1
    else break
  if isLit then return { n := n }
  if pol == .pos then
    let st ← get
    let axPicked := (l.find? fun x => match x with
      | .fvar f => match st.vars[f]? with | some (.ex _) | some .ax => true | _ => false
      | _ => false).isSome
    if axPicked then return Cnt.zero
  return { syms := [s!"len({← ppS l})"] }

def single (pol : Pol) (k : String) (c : Cnt) : Res :=
  if c.isZero then Res.unit else
  match pol with
  | .pos => #[{ prod := [(k, c)] }]
  | .neg => #[{ cons := [(k, c)] }]

/-- The atom key of a term built from a user-picked variable by projections, if any. -/
partial def atomKey? (e : Expr) : W (Option String) := do
  let e := e.consumeMData
  let st ← get
  match e with
  | .fvar f =>
    match st.vars[f]? with
    | some (.user k) => return some k
    | some (.elem p) => return if p == "" then none else some (p ++ "[]")
    | _ => return none
  | .proj _ i s =>
    match ← atomKey? s with
    | some k => return some s!"{k}.{i}"
    | none => return none
  | .app .. =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    match fn with
    | .const c _ =>
      if let some info := (← getEnv).getProjectionFnInfo? c then
        if args.size > info.numParams then
          match ← atomKey? args[info.numParams]! with
          | some k => return some s!"{k}.{lastStr c}"
          | none => return none
      return none
    | _ => return none
  | _ => return none

/-- The `ex` variable a term is built from by projections, if any. -/
partial def exRoot? (e : Expr) : W (Option Nat) := do
  let e := e.consumeMData
  match e with
  | .fvar f => match (← get).vars[f]? with | some (.ex i) => return some i | _ => return none
  | .proj _ _ s => exRoot? s
  | .app .. =>
    match e.getAppFn with
    | .const c _ =>
      if let some info := (← getEnv).getProjectionFnInfo? c then
        if e.getAppArgs.size > info.numParams then return ← exRoot? e.getAppArgs[info.numParams]!
      return none
    | .fvar _ => exRoot? e.getAppFn
    | _ => return none
  | _ => return none

def markNaked (i : Nat) (why : String) : W Unit := modify fun st =>
  if h : i < st.exs.size then
    let x := st.exs[i]
    if x.naked.size > 3 then st else { st with exs := st.exs.set i { x with naked := x.naked.push why } }
  else st

/-- The atoms among the arguments (rule 3: a consumed application consumes them). -/
def argAtoms (args : Array Expr) : W (Array String) := do
  let st ← get
  let mut out := #[]
  for a in args do
    let fvs := (Lean.collectFVars {} a).fvarIds
    for f in fvs do
      if let some (VKind.user k) := st.vars[f]? then
        if !out.contains k then out := out.push k
  return out

/-- Rule 3: an application in consumed position consumes the atoms among its arguments (the user's
`Φ` handed to an axiom-picked `Spec`, `Spec md m Φ Ψe`, is the user's to give). -/
def consArgs (args : Array Expr) (pol : Pol) : W Res := do
  let mut r := Res.unit
  if pol == .neg then
    for k in ← argAtoms args do r := r.sep (single .neg s!"atom:{k}" Cnt.one)
  return r

def isOpaquePred (c : Name) : MetaM Bool := do
  match (← getEnv).find? c with
  | some (.axiomInfo _) | some (.opaqueInfo _) => return true
  | _ => return false

/-- Whether `k'` is the atom `k` or one of its fields or elements. -/
def inFamily (k k' : String) : Bool :=
  k' == k || k'.startsWith (k ++ ".") || k'.startsWith (k ++ "[]")

/-- `s` without its `#n` indices (an atom's key without the binder's number). -/
def dropIndices (s : String) : String := Id.run do
  let mut out := ""
  let mut skip := false
  for ch in s.toList do
    if ch == '#' then skip := true; continue
    if skip && ch.isDigit then continue
    skip := false
    out := out.push ch
  return out

/-- Leaving the scope of a user-picked atom `atom:k` (`bindVar`): no later step can produce or
consume it (its key is fresh, and its variable does not occur outside its binder), so its rule-3
verdict in each scenario is final. A scenario where it passes (each of the family's productions
covered, as in `rule3`) forgets the family's counts, which no later verdict reads; one where it
fails replaces them by its findings, kept as `fail3:` keys (produced; their text without the
binder's `#n`, as the driver's entry keys name them, `finding_key`), which `rule3` reports. This
keeps the scenarios that differ only in balanced uses of inner callbacks' atoms (a branch
producing and consuming a `Φ`), or in which of several like binders fails, from multiplying. -/
def Scen.closeAtom (k : String) (s : Scen) : Scen :=
  let fam := fun (kc : String × Cnt) => inFamily ("atom:" ++ k) kc.1
  let fails := s.prod.filterMap fun (k', c) =>
    if !fam (k', c) then none else
    let avail := s.cons.foldl (fun acc (k'', c'') =>
      if k'' == k' || (k'.startsWith (k'' ++ ".")) || (k'.startsWith (k'' ++ "[]")) then acc.add c''
      else acc) Cnt.zero
    if c.le avail then none
    else some ("fail3:" ++ dropIndices s!"{k'}: produced {c.show}, consumed {avail.show}")
  let prod := s.prod.filter (!fam ·)
  { s with prod := fails.foldl (fun m f => m.addK f Cnt.one) prod, cons := s.cons.filter (!fam ·) }

def bindVar (n : Name) (ty : Expr) (kind : Pol → Bool → W VKind) (pol : Pol)
    (k : Expr → W Res) : W Res := do
  withLocalDeclD n ty fun x => do
    let carries ← (try carriesIProp ty catch _ => pure false)
    let vk ← kind pol carries
    modify fun st => { st with vars := st.vars.insert x.fvarId! vk }
    let r ← k x
    match vk with
    | .user key => return Res.dedup (r.map (Scen.closeAtom key))
    | _ => return r

/-- ∀: the user picks at positive polarity; ∃: the axiom picks at positive polarity. -/
def freshKey (n : Name) : W String := do
  let st ← get
  modify fun st => { st with nkeys := st.nkeys + 1 }
  return s!"{n.eraseMacroScopes}#{st.nkeys}"

def forallKind (n : Name) (pol : Pol) (carries : Bool) : W VKind := do
  if pol == .pos then
    if carries then return .user (← freshKey n) else return .plain
  else return .ax
def existsKind (n : Name) (ty : Expr) (pol : Pol) (carries : Bool) : W VKind := do
  if pol == .pos then
    if carries then
      let i := (← get).exs.size
      let tys ← ppS ty
      let tk ← typeKey ty
      modify fun st => { st with exs := st.exs.push { name := toString n.eraseMacroScopes, ty := tys, tyKey := tk } }
      return .ex i
    return .ax
  else if carries then return .user (← freshKey n) else return .plain

def recordConsType (ty : Expr) : W Unit := do
  let k ← typeKey ty
  modify fun st => if st.consTypes.contains k then st else { st with consTypes := st.consTypes.push k }

def tick (cfg : Cfg) : W Bool := do
  let st ← get
  if st.fuel ≥ cfg.fuel then return false
  set { st with fuel := st.fuel + 1 }
  return true

/-- Apply a binder body (a lambda, or any function) to a fresh variable. -/
def openBody (f : Expr) (k : Name → Expr → (Expr → Expr) → W Res) : W Res := do
  let f := f.consumeMData
  match f with
  | .lam n ty b _ => k n ty (fun x => b.instantiate1 x)
  | _ =>
    let ty ← whnf (← inferType f)
    match ty with
    | .forallE n d _ _ => k n d (fun x => mkApp f x)
    | _ => throwError "openBody: not a function"

mutual

partial def walkI (cfg : Cfg) (e : Expr) (pol : Pol) (d : Nat) : W Res := do
  unless ← tick cfg do
    note "fuel exhausted"
    return Res.unit
  let e := (← instantiateMVars e).consumeMData.headBeta
  let fn := e.getAppFn
  let args := e.getAppArgs
  match fn with
  | .const c _ =>
    let s := lastStr c
    let last := args.back?.getD e
    if c.getRoot == `Iris then
      match s with
      | "sep" => if args.size ≥ 4 then
          return (← walkI cfg args[args.size-2]! pol d).sep (← walkI cfg last pol d)
      | "wand" | "imp" => if args.size ≥ 4 then
          return (← flipped (walkI cfg args[args.size-2]! pol.flip d)).sep (← walkI cfg last pol d)
      | "and" => if args.size ≥ 4 then
          let a ← walkI cfg args[args.size-2]! pol d
          let b ← walkI cfg last pol d
          return if pol == .pos then a.union b else a.maxc b
      | "or" => if args.size ≥ 4 then
          return (← walkI cfg args[args.size-2]! pol d).union (← walkI cfg last pol d)
      | "iff" | "wandIff" => if args.size ≥ 4 then
          let p := args[args.size-2]!
          let a ← (← flipped (walkI cfg p pol.flip d)).sep <$> walkI cfg last pol d
          let b ← (← flipped (walkI cfg last pol.flip d)).sep <$> walkI cfg p pol d
          return a.union b
      | "forall" =>
        return ← openBody last fun n ty body => do
          if pol == .pos && (← (try carriesIProp ty catch _ => pure false)) then recordConsType ty
          let isPost := pol == .neg && ty.consumeMData.isForall &&
            (ty.consumeMData.getForallBody.getAppFn.isConstOf `Iris.IProp)
          let k := bindVar n ty (fun p c => forallKind n p c) pol fun x => walkI cfg (body x) pol d
          if isPost then inCallback k else k
      | "exists" =>
        return ← openBody last fun n ty body =>
          bindVar n ty (fun p c => existsKind n ty p c) pol fun x => walkI cfg (body x) pol d
      | "pure" | "emp" | "True" | "False" => return Res.unit
      | "later" | "laterN" | "except0" | "affinely" | "absorbingly" | "fupd" | "bupd"
      | "affinelyIf" | "absorbinglyIf" | "plainly" =>
        return ← walkI cfg last pol d
      | "persistently" | "intuitionistically" | "intuitionisticallyIf" =>
        let r ← walkI cfg last pol d
        if pol == .pos then return r.map persistentPos
        return r
      | "wp" | "twp" =>
        -- only the postcondition
        return ← (if pol == .neg then inCallback (walkPost cfg last pol d) else walkPost cfg last pol d)
      | "bigSepL" | "bigSepL2" | "bigSepM" | "bigSepS" | "bigSepM2" | "bigSepMS" =>
        return ← walkBig cfg c args pol d
      | _ => pure ()
    if isTok c then return ← walkTok c args pol
    if isGhostOwn c then
      -- a ghost resource: a raw token if at the token name, else nothing the walk counts (a saved
      -- predicate of a user's `R` names `R` and does not give it); consumed, it consumes the atoms
      -- among its arguments, as an opaque predicate does
      if args.any (fun a => (a.find? (·.isConstOf `Perennial.ThreadGS.threadTokName)).isSome) then
        return single pol "tok:raw" Cnt.one
      return ← consArgs args pol
    if isNeutral c then
      -- a handle's arguments are neutral uses of ∃-bound values (rule 7's first case)
      if pol == .pos && args.any mentionsTok then
        note s!"handle-token: {← ppS e}"
      -- in consumed position a handle consumes the atoms among its arguments (rule 3), as an
      -- opaque predicate does
      let mut r := Res.unit
      if pol == .neg then
        for k in ← argAtoms args do r := r.sep (single .neg s!"atom:{k}" Cnt.one)
      return r
    if c == ``ite || c == ``dite then
      if args.size == 5 then
        let cond ← ppKey args[1]!
        let t ← if c == ``ite then walkI cfg args[3]! pol d else
          openBody args[3]! fun n ty b => bindVar n ty (fun _ _ => pure .ax) pol fun x => walkI cfg (b x) pol d
        let f ← if c == ``ite then walkI cfg args[4]! pol d else
          openBody args[4]! fun n ty b => bindVar n ty (fun _ _ => pure .ax) pol fun x => walkI cfg (b x) pol d
        return (t.withCond cond true).union (f.withCond cond false)
    if c == ``cond && args.size == 4 then
      let k ← ppKey args[1]!
      return ((← walkI cfg args[2]! pol d).withCond k true).union
        ((← walkI cfg args[3]! pol d).withCond k false)
    if ← isOpaquePred c then
      let mut r := single pol s!"opq:{c}" Cnt.one
      -- its arguments are neutral uses of ∃-bound values (rule 7's first case)
      if pol == .neg then
        for k in ← argAtoms args do r := r.sep (single .neg s!"atom:{k}" Cnt.one)
      if args.any (fun a => (a.find? (·.isConstOf `Perennial.ThreadGS.threadTokName)).isSome) then
        r := r.sep (single pol "tok:raw" Cnt.one)
      return r
    -- a projection of a user-picked record (`cd.PDone`, `m.spec`)
    if let some k ← atomKey? e then return ← atomUse e k args pol
    if let some i ← exRoot? e then
      markNaked i s!"{if pol == .pos then "produced" else "consumed"}: {← ppS e}"
      return ← consArgs args pol
    -- unfold
    if (e.find? (·.isConstOf `Perennial.ThreadGS.threadTokName)).isSome && lastStr c == "ghostMapElem" then
      return single pol "tok:raw" Cnt.one
    if d ≥ cfg.depth then
      -- cut here: a loss only if the term's definitions reach something the walk counts
      if ← reachesRes e.getUsedConstants then truncNote s!"depth: {c}"
      return ← stuck cfg c e args pol
    match ← (try unfoldDefinition? e catch _ => pure none) with
    | some e' =>
      let e'' ← (try whnfCore e'.headBeta catch _ => pure e'.headBeta)
      return ← walkI cfg e'' pol (d + 1)
    | none =>
      let e' ← (try whnfCore e catch _ => pure e)
      if e' != e then return ← walkI cfg e' pol (d + 1)
      if (e.find? (·.isConstOf `Perennial.ThreadGS.threadTokName)).isSome then
        return single pol "tok:raw" Cnt.one
      -- a stuck `match`: every alternative, over fresh variables
      if let some info ← getMatcherInfo? c then
        let start := info.numParams + 1 + info.numDiscrs
        if args.size ≥ start + info.numAlts then
          let mut r : Option Res := none
          for i in [0:info.numAlts] do
            let alt := args[start + i]!
            let ri ← openAll cfg alt pol d
            r := some (match r with | none => ri | some r0 => r0.union ri)
          return r.getD Res.unit
      return ← stuck cfg c e args pol
  | .fvar f =>
    match (← get).vars[f]? with
    | some (.user k) => return ← atomUse e k args pol
    | some (.ex i) =>
      markNaked i s!"{if pol == .pos then "produced" else "consumed"}: {← ppS e}"
      return ← consArgs args pol
    | some (.elem _) =>
      if let some k ← atomKey? e then return ← atomUse e k args pol
      return ← consArgs args pol
    | _ => return ← consArgs args pol
  | .proj .. =>
    if let some k ← atomKey? fn then return ← atomUse e k args pol
    if let some i ← exRoot? fn then
      markNaked i s!"{if pol == .pos then "produced" else "consumed"}: {← ppS e}"
      return ← consArgs args pol
    let e' ← (try whnfCore e catch _ => pure e)
    if e' != e then return ← walkI cfg e' pol (d + 1)
    truncNote s!"stuck projection: {← ppS e}"
    return Res.unit
  | _ =>
    let e' ← (try whnfCore e catch _ => pure e)
    if e' != e then return ← walkI cfg e' pol (d + 1)
    truncNote s!"unknown term: {← ppS e}"
    return Res.unit

/-- A match alternative: its body over fresh (axiom-picked) variables. -/
partial def openAll (cfg : Cfg) (f : Expr) (pol : Pol) (d : Nat) : W Res := do
  match f.consumeMData with
  | .lam n ty b _ => bindVar n ty (fun _ _ => pure .ax) pol fun x => openAll cfg (b.instantiate1 x) pol d
  | b => walkI cfg b pol (d + 1)

/-- A term the walk cannot open: neutral if it holds no atom, transfer candidate or token; in
consumed position it consumes the atoms among its arguments (rule 3); otherwise a `trunc` note. -/
partial def stuck (_cfg : Cfg) (c : Name) (e : Expr) (args : Array Expr) (pol : Pol) : W Res := do
  let atoms ← argAtoms args
  let st ← get
  let hasEx := (e.find? fun x => match x with
    | .fvar f => match st.vars[f]? with | some (.ex _) => true | _ => false
    | _ => false).isSome
  if hasEx then
    for a in args do
      if let some i ← exRoot? a then markNaked i s!"in a stuck term: {c}"
  if atoms.isEmpty && !hasEx && !mentionsTok e then return Res.unit
  let mut r := Res.unit
  if pol == .neg then
    for k in atoms do r := r.sep (single .neg s!"atom:{k}" Cnt.one)
  else if !atoms.isEmpty || mentionsTok e then
    truncNote s!"stuck: {c}"
  return r

partial def atomUse (_e : Expr) (k : String) (args : Array Expr) (pol : Pol) : W Res := do
  let mut r := single pol s!"atom:{k}" Cnt.one
  if pol == .neg then
    for a in ← argAtoms args do
      if a != k then r := r.sep (single .neg s!"atom:{a}" Cnt.one)
  return r

partial def walkTok (c : Name) (args : Array Expr) (pol : Pol) : W Res := do
  -- tokens handed back through the continuation of a callback the user supplies (consumed under
  -- three or more flips) pay for nothing: the callback may never return (partial correctness)
  let r ← walkTok0 c args pol
  let fl := (← get).cbDepth
  let tag (pre : String) (m : KMap) : KMap :=
    m ++ (m.filter (·.1.startsWith "tok:")).map fun (k, v) => (pre ++ (k.drop 4).toString, v)
  if pol == .neg && fl ≥ 1 then return r.map fun s => { s with cons := tag "ret:" s.cons }
  if pol == .pos && fl ≥ 1 then return r.map fun s => { s with prod := tag "cb:" s.prod }
  return r

partial def walkTok0 (c : Name) (args : Array Expr) (pol : Pol) : W Res := do
  -- the explicit arguments are the last ones
  let ex (i : Nat) : Expr := args[args.size - i]!
  match lastStr c with
  | "threadTok" => return single pol "tok:T" Cnt.one
  | "threadToks" | "threadFuel" => return single pol "tok:T" (← multOf (ex 1) pol)
  | "levelTok" => return single pol s!"tok:L:{← ppS (ex 1)}" Cnt.one
  | "levelToks" => return single pol s!"tok:L:{← ppS (ex 2)}" (← multOf (ex 1) pol)
  | "levelTokList" => return single pol s!"tok:L:{← ppS (ex 2)}" (← listMult (ex 1) pol)
  | "threadTokList" => return single pol "tok:L:0" (← listMult (ex 1) pol)
  | "threadTokFrom" => return single pol s!"tok:F:{← ppS (ex 1)}" Cnt.one
  | "threadToksFrom" => return single pol s!"tok:F:{← ppS (ex 2)}" (← multOf (ex 1) pol)
  | "levelsToks" => return single pol s!"tok:LS:{← ppS (ex 3)}:{← ppS (ex 2)}" (← multOf (ex 1) pol)
  | "ownThreadLoan" => return single pol s!"tok:loan:{← ppS (ex 1)}" Cnt.one
  | _ => return Res.unit

partial def walkPost (cfg : Cfg) (Φ : Expr) (pol : Pol) (d : Nat) : W Res := do
  let Φ := Φ.consumeMData
  match Φ with
  | .lam n ty b _ =>
    -- the value is picked by the program
    bindVar n ty (fun _ _ => pure .ax) pol fun x => walkI cfg (b.instantiate1 x) pol d
  | _ =>
    match Φ.getAppFn with
    | .fvar f =>
      match (← get).vars[f]? with
      | some (.user k) => atomUse Φ k Φ.getAppArgs pol
      | some (.ex i) => markNaked i s!"postcondition: {← ppS Φ}"; consArgs Φ.getAppArgs pol
      | _ => consArgs Φ.getAppArgs pol
    | _ =>
      openBody Φ fun n ty body =>
        bindVar n ty (fun _ _ => pure .ax) pol fun x => walkI cfg (body x) pol d

partial def walkBig (cfg : Cfg) (c : Name) (args : Array Expr) (pol : Pol) (d : Nat) : W Res := do
  let s := lastStr c
  if s == "bigSepL" && args.size ≥ 5 then
    let f := args[args.size-2]!
    let l := args[args.size-1]!
    let parent := (← atomKey? l).getD ""
    let m ← listMult l pol
    let r ← openBody f fun n1 t1 b1 =>
      bindVar n1 t1 (fun _ _ => pure .ax) pol fun i =>
        openBody (b1 i) fun n2 t2 b2 =>
          bindVar n2 t2 (fun _ _ => pure (.elem parent)) pol fun x => walkI cfg (b2 x) pol d
    return r.scale m
  -- the other big ops: the body over fresh variables, with a symbolic multiplicity
  let f := args.findRev? (fun a => a.consumeMData.isLambda) |>.getD (args.back?.getD (mkConst `True))
  let coll := args.back?.getD (mkConst `True)
  let k : Cnt := { syms := [s!"card({← ppS coll})"] }
  let rec go (f : Expr) (n : Nat) : W Res := do
    if n == 0 then return ← walkI cfg f pol d
    match f.consumeMData with
    | .lam nm ty b _ => bindVar nm ty (fun _ _ => pure (.elem "")) pol fun x => go (b.instantiate1 x) (n - 1)
    | _ => walkI cfg f pol d
  let r ← go f 3
  return r.scale k

/-- A `Prop`. -/
partial def walkProp (cfg : Cfg) (e : Expr) (pol : Pol) (d : Nat) : W Res := do
  unless ← tick cfg do
    note "fuel exhausted"
    return Res.unit
  let e := (← instantiateMVars e).consumeMData.headBeta
  match e with
  | .forallE n t b bi =>
    if bi.isInstImplicit then
      return ← withLocalDecl n bi t fun x => walkProp cfg (b.instantiate1 x) pol d
    if !b.hasLooseBVars && (← (try isProp t catch _ => pure false)) then
      return (← flipped (walkProp cfg t pol.flip d)).sep (← walkProp cfg b pol d)
    if pol == .pos && (← (try carriesIProp t catch _ => pure false)) then recordConsType t
    return ← bindVar n t (fun p c => forallKind n p c) pol fun x => walkProp cfg (b.instantiate1 x) pol d
  | _ => pure ()
  let fn := e.getAppFn
  let args := e.getAppArgs
  match fn with
  | .const c _ =>
    if c.getRoot == `Iris && (lastStr c == "Entails") && args.size ≥ 4 then
      let a ← flipped (walkI cfg args[args.size-2]! pol.flip d)
      return a.sep (← walkI cfg args[args.size-1]! pol d)
    if c.getRoot == `Iris && (lastStr c == "EmpValid") && args.size ≥ 3 then
      return ← walkI cfg args[args.size-1]! pol d
    if c.getRoot == `Iris && (lastStr c == "BiEntails" || lastStr c == "Equiv") && args.size ≥ 4 then
      let p := args[args.size-2]!
      let q := args[args.size-1]!
      let isI ← (try do let t ← inferType p; pure (t.getAppFn.isConstOf `Iris.IProp || t.getAppFn.isConstOf `Iris.UPred) catch _ => pure false)
      if isI then
        let a := (← flipped (walkI cfg p pol.flip d)).sep (← walkI cfg q pol d)
        let b := (← flipped (walkI cfg q pol.flip d)).sep (← walkI cfg p pol d)
        return a.union b
      return Res.unit
    if c == ``And && args.size == 2 then
      let a ← walkProp cfg args[0]! pol d
      let b ← walkProp cfg args[1]! pol d
      return if pol == .pos then a.union b else a.sep b
    if c == ``Or && args.size == 2 then
      return (← walkProp cfg args[0]! pol d).union (← walkProp cfg args[1]! pol d)
    if c == ``Iff && args.size == 2 then
      let a := (← flipped (walkProp cfg args[0]! pol.flip d)).sep (← walkProp cfg args[1]! pol d)
      let b := (← flipped (walkProp cfg args[1]! pol.flip d)).sep (← walkProp cfg args[0]! pol d)
      return a.union b
    if c == ``Not && args.size == 1 then return ← flipped (walkProp cfg args[0]! pol.flip d)
    if c == ``Exists && args.size == 2 then
      return ← openBody args[1]! fun n ty body =>
        bindVar n ty (fun p cr => existsKind n ty p cr) pol fun x => walkProp cfg (body x) pol d
    if c == ``Eq && args.size == 3 then
      let t := args[0]!
      if t.getAppFn.isConstOf `Iris.IProp || t.getAppFn.isConstOf `Iris.UPred then
        note s!"IProp equation: {← ppS e}"
      return Res.unit
    -- a Prop-valued definition (a spec's `abbrev`): unfold
    if d < cfg.depth then
      match (← getEnv).find? c with
      | some (.defnInfo _) =>
        match ← (try unfoldDefinition? e catch _ => pure none) with
        | some e' => return ← walkProp cfg e'.headBeta pol (d + 1)
        | none => return Res.unit
      | _ => return Res.unit
    if mentionsTok e then truncNote s!"depth (Prop): {c}"
    return Res.unit
  | _ => return Res.unit

/-- `□ P` at positive polarity: production beyond consumption inside is unbounded. -/
partial def persistentPos (s : Scen) : Scen :=
  -- tokens only: a parametric atom under `□` is counted once (approximation: the persistent
  -- context it would be duplicated from is usually itself persistent, `□ H -∗ □ triple`)
  let prod := s.prod.map fun (k, c) =>
    if !k.startsWith "tok:" || c.le (s.cons.get k) then (k, c) else (k, { inf := true })
  { s with prod := prod }

end

/-! ## Judging a scenario -/

/-- Level points and coverage (rule 2). -/
def tokKind (k : String) : Option (String × String) :=
  if k.startsWith "tok:" then
    let r := (k.drop 4).toString
    if r == "T" then some ("T", "")
    else if r.startsWith "L:" then some ("L", (r.drop 2).toString)
    else if r.startsWith "F:" then some ("F", (r.drop 2).toString)
    else if r.startsWith "LS:" then some ("LS", (r.drop 3).toString)
    else some ("own", r)
  else none

def covers (kind lvl point : String) (forProd : Bool) : Bool :=
  match kind with
  | "T" => !point.startsWith "own:"
  | "L" => point == "L:" ++ lvl
  | "F" =>
    if point.startsWith "own:" then false
    else if point == "*" then forProd || lvl == "0"
    else
      let p := (point.drop 2).toString
      p == lvl || (match lvl.toNat?, p.toNat? with | some a, some b => a ≤ b | _, _ => false)
  | "LS" => point == "LS:" ++ lvl
  | _ => point == "own:" ++ lvl

def tokPoints (s : Scen) : List String :=
  let ks := (s.prod ++ s.cons).map (·.1)
  let pts := ks.filterMap fun k => match tokKind k with
    | some ("L", l) => some ("L:" ++ l)
    | some ("F", l) => some ("L:" ++ l)
    | some ("LS", l) => some ("LS:" ++ l)
    | some ("own", r) => some ("own:" ++ r)
    | _ => none
  ("*" :: pts).eraseDups

def tokAt (m : KMap) (pt : String) (forProd : Bool) (pre : String := "tok:") : Cnt :=
  m.foldl (fun acc (k, c) => match tokKind ("tok:" ++ (if k.startsWith pre then (k.drop pre.length).toString else "\x00")) with
    | some (kind, l) => if covers kind l pt forProd then acc.add c else acc
    | none => acc) Cnt.zero

/-- Rule 2 failures of a scenario. -/
def rule2 (s : Scen) : List String :=
  (tokPoints s).filterMap fun pt =>
    let p := tokAt s.prod pt true
    let c := tokAt s.cons pt false
    if p.isZero || p.le c then
      -- 2b: what the axiom hands a callback the user supplies is paid only by what the user
      -- supplies directly, not by what a callback hands back (the callback may never return)
      let cb := tokAt s.prod pt true "cb:"
      let ret := tokAt s.cons pt false "ret:"
      let direct : Cnt := { n := c.n - ret.n, syms := ret.syms.foldl (fun acc x => acc.erase x) c.syms, inf := c.inf }
      if cb.isZero || cb.le direct then none
      else some s!"level {pt}: handed to a callback {cb.show}, supplied directly {direct.show}"
    else some s!"level {pt}: produced {p.show}, consumed {c.show}"

/-- Rule 3 failures of a scenario: an atom produced beyond what is consumed (of it or of the
record it is a field of). -/
def rule3 (s : Scen) : List String :=
  s.prod.filterMap fun (k, c) =>
    if k.startsWith "fail3:" then some (k.drop 6).toString else
    if !k.startsWith "atom:" then none else
    let avail := s.cons.foldl (fun acc (k', c') =>
      if k' == k || (k.startsWith (k' ++ ".")) || (k.startsWith (k' ++ "[]")) then acc.add c' else acc) Cnt.zero
    if c.le avail then none else some s!"{k}: produced {c.show}, consumed {avail.show}"

def opqProduced (s : Scen) : List (String × Cnt) :=
  s.prod.filter (·.1.startsWith "opq:") |>.map fun (k, c) => ((k.drop 4).toString, c)
def opqConsumed (s : Scen) : List (String × Cnt) :=
  s.cons.filter (·.1.startsWith "opq:") |>.map fun (k, c) => ((k.drop 4).toString, c)

/-! ## Per-axiom results -/

structure AxRes where
  name : Name
  scens : Res
  exs : Array ExInfo
  notes : Array String
  trunc : Array String
  consTypes : Array String
  ms : Nat := 0
  deriving Inhabited

def runW (x : W α) (reach : Std.HashMap Name Bool := {}) : MetaM (α × WS) := x.run { reach := reach }

def analyze (cfg : Cfg) (c : Name) (t : Expr) (reach : Std.HashMap Name Bool := {}) :
    MetaM (AxRes × Std.HashMap Name Bool) := do
  let (r, st) ← runW (walkProp cfg t .pos 0) reach
  let a : AxRes := { name := c, scens := r, exs := st.exs, notes := st.notes, trunc := st.trunc,
                     consTypes := st.consTypes }
  return (a, st.reach)

/-! ## Rules 5 and 6 across the axioms, and the output -/

def kmapJson (m : KMap) : Json := Json.mkObj (m.map fun (k, c) => (k, c.toJson))

def judgeAll (env : Environment) (results : Array AxRes) (persistentOpq : NameSet)
    (emit : Json → IO Unit) : IO (Nat × Nat) := do
  -- rule 6: holders
  let mut dup : NameSet := {}
  for r in results do
    for s in r.scens do
      for (o, c) in opqProduced s do
        let cc := (opqConsumed s).lookup o |>.getD Cnt.zero
        if !cc.isZero && cc.n < c.n then dup := dup.insert o.toName
  let mut credit : Std.HashMap String (Option KMap) := {}
  for r in results do
    for s in r.scens do
      for (o, _) in opqProduced s do
        if (opqConsumed s).lookup o |>.isSome then continue  -- a transformer, not a source
        let net : KMap := (s.cons.filter (·.1.startsWith "tok:")).filterMap fun (k, c) =>
          let p := s.prod.get k
          if c.n > p.n then some (k, { n := c.n - p.n }) else none
        let old := credit.getD o (some net)
        let new := old.map fun o => KMap.merge Cnt.min o net
        credit := credit.insert o new
  let creditOf (o : String) : KMap :=
    if persistentOpq.contains o.toName || dup.contains o.toName then [] else
    (credit.getD o none).getD []
  let applyCredit (s : Scen) : Scen := Id.run do
    let mut cons := s.cons
    for (o, c) in opqConsumed s do
      -- per copy consumed and not produced back (a transformer `O -∗ O ∗ …` keeps the tokens
      -- `O` carries inside the `O` it returns: it is credited nothing for it)
      let net := c.n - (s.prod.get ("opq:" ++ o)).n
      for (k, v) in creditOf o do
        cons := cons.addK k { n := v.n * net }
    return { s with cons := cons }
  -- base verdicts
  let base := results.map fun r =>
    let fails := r.scens.toList.flatMap fun s => let s' := applyCredit s; rule2 s' ++ rule3 s'
    (r, fails.eraseDups)
  -- rule 5: greatest fixpoint of the taint
  let mut tainted : NameSet := {}
  let mut changed := true
  let mut iter := 0
  while changed && iter < 50 do
    changed := false
    iter := iter + 1
    for (r, fails) in base do
      let producesTainted := r.scens.any fun s => (opqProduced s).any fun (o, _) => tainted.contains o.toName
      if !fails.isEmpty || producesTainted then
        for s in r.scens do
          for (o, _) in opqProduced s do
            if !tainted.contains o.toName then
              tainted := tainted.insert o.toName
              changed := true
  let mut nOk := 0
  let mut nBad := 0
  for (r, fails) in base do
    let mut findings : Array Json := #[]
    for f in fails do
      let rule := if f.startsWith "atom:" then "3" else "2"
      findings := findings.push (Json.mkObj [("rule", rule), ("why", f)])
    let tp := (r.scens.toList.flatMap fun s => (opqProduced s).map (·.1)).eraseDups.filter
      fun o => tainted.contains o.toName
    -- only the ones tainted by another axiom (its own failure is reported already)
    if fails.isEmpty then
      for o in tp do
        findings := findings.push (Json.mkObj [("rule", "5"), ("why", s!"produces the tainted opaque {o}")])
    for x in r.exs do
      if !x.naked.isEmpty then
        findings := findings.push (Json.mkObj [("rule", "7"),
          ("why", s!"transfer of ∃ {x.name} : {x.ty} ({", ".intercalate x.naked.toList})"),
          ("type", x.tyKey)])
    for n in r.notes do
      findings := findings.push (Json.mkObj [("rule", if n.startsWith "handle-token" then "4" else "note"), ("why", n)])
    let mints := r.scens.toList.any fun s =>
      let s' := applyCredit s
      (s'.prod.any fun (k, c) => k.startsWith "tok:" && !c.isZero) &&
      !(s'.cons.any fun (k, c) => k.startsWith "tok:" && !c.isZero) && !(rule2 s').isEmpty
    let ok := findings.isEmpty
    if ok then nOk := nOk + 1 else nBad := nBad + 1
    let scensJ := r.scens.toList.take 8 |>.map fun s => Json.mkObj
      [("prod", kmapJson s.prod), ("cons", kmapJson (applyCredit s).cons),
       ("if", Json.mkObj (s.conds.map fun (k, v) => (k, Json.bool v)))]
    emit (Json.mkObj [("t", "ax"), ("name", toString r.name), ("ok", Json.bool ok),
      ("mint", Json.bool mints), ("findings", Json.arr findings),
      ("trunc", Json.arr (r.trunc.map Json.str)), ("consumesTypes", Json.arr (r.consTypes.map Json.str)),
      ("transfersNeutral", Json.arr ((r.exs.filter (·.naked.isEmpty)).map fun x => Json.str s!"{x.name} : {x.ty}")),
      ("scenarios", Json.arr scensJ.toArray), ("nscen", r.scens.size),
      ("opqProd", Json.arr ((r.scens.toList.flatMap fun s => (opqProduced s).map (·.1)).eraseDups.toArray.map Json.str)),
      ("ms", r.ms), ("capped", Json.bool (r.scens.any fun s => s.conds.lookup "<capped>" |>.isSome))])
  for (o, v) in credit.toList do
    if let some m := v then
      if !m.isEmpty && !persistentOpq.contains o.toName && !dup.contains o.toName then
        emit (Json.mkObj [("t", "holder"), ("opq", o), ("carries", kmapJson m)])
  for o in tainted.toList do
    emit (Json.mkObj [("t", "tainted"), ("opq", toString o)])
  let _ := env
  return (nOk, nBad)

/-- The opaque predicates with a `Persistent` instance (rule 6: no holder). -/
def persistentOpaques (env : Environment) : MetaM NameSet := do
  let mut out : NameSet := {}
  for (n, ci) in env.constants.toList do
    if !(Meta.isInstanceCore env n) then continue
    let t := ci.type
    let concl := (Id.run do
      let mut t := t
      while t.isForall do t := t.bindingBody!
      return t)
    if concl.getAppFn.isConstOf `Iris.BI.Persistent then
      if let some p := concl.getAppArgs.back? then
        if let .const c _ := p.getAppFn then out := out.insert c
  return out

/-- m2: a `FuncUnfold` instance for a model-only name. -/
def modelUnfolds (env : Environment) : MetaM (Array String) := do
  let mut out := #[]
  for (n, ci) in env.constants.toList do
    let mut t := ci.type
    while t.isForall do t := t.bindingBody!
    if lastStr t.getAppFn.constName == "FuncUnfold" && t.getAppArgs.size ≥ 3 then
      let args := t.getAppArgs
      for a in args do
        if let some s := decodeGoString a then
          if (s.splitOn "#model.").length > 1 then out := out.push s!"{n}: {s}"
  return out

def runMeta (env : Environment) (x : MetaM α) : IO α := do
  let opts : Options := ({} : Options)
    |>.setBool `pp.universes false |>.setBool `pp.proofs false
    |>.insert `maxRecDepth (.ofNat 100000)
  let ctx : Core.Context := { fileName := "<axiom-tok>", fileMap := default, options := opts,
                              maxHeartbeats := 0, currNamespace := `Perennial.EtcdGrove,
                              openDecls := [`Perennial, `Iris, `Iris.BI].map
                                (OpenDecl.simple · []) }
  let (a, _) ← (x.run' {} {}).toIO ctx { env }
  return a

def checkAxioms (cfg : Cfg) (env : Environment) (names : Array Name) (emit : Json → IO Unit) :
    IO (Nat × Nat) := do
  let mut results : Array AxRes := #[]
  let mut skipped : Nat := 0
  let mut present : Array Json := #[]
  let mut reach : Std.HashMap Name Bool := {}
  for c in names do
    let some ci := env.find? c | continue
    present := present.push (Json.str (toString c))
    let isP ← runMeta env (try isProp ci.type catch _ => pure false)
    if !isP then skipped := skipped + 1; continue
    let t0 ← IO.monoMsNow
    if cfg.trace then IO.eprintln s!"axiom-tok: walking {c}"
    let (r, reach') ← runMeta env (try analyze cfg c ci.type reach catch e => do
      let msg ← e.toMessageData.toString
      let r0 : AxRes := { name := c, scens := Res.unit, exs := #[], notes := #["error: " ++ msg],
                          trunc := #[], consTypes := #[] }
      return (r0, reach))
    reach := reach'
    let dt := (← IO.monoMsNow) - t0
    if dt > 2000 then IO.eprintln s!"axiom-tok: slow: {c} {dt} ms"
    results := results.push { r with ms := dt }
  let pers ← runMeta env (persistentOpaques env)
  let r ← judgeAll env results pers emit
  emit (Json.mkObj [("t", "skipped"), ("n", toJson skipped)])
  emit (Json.mkObj [("t", "present"), ("names", Json.arr present)])
  return r

/-! ## Selftests: elaborate a file of toy axioms over the imported environment -/

def runSelftest (cfg : Cfg) (env : Environment) (file : String) (emit : Json → IO Unit) : IO UInt32 := do
  let src ← IO.FS.readFile file
  let inputCtx := Parser.mkInputContext src file
  let cmdState := Command.mkState env {} {}
  let s ← IO.processCommands inputCtx {} cmdState
  let msgs := s.commandState.messages.toList
  let mut nerr := 0
  for m in msgs do
    if m.severity == .error then
      nerr := nerr + 1
      emit (Json.mkObj [("t", "elab-error"), ("msg", ← m.toString)])
  let env' := s.commandState.env
  -- the new axioms
  let mut names := #[]
  for (n, ci) in env'.constants.map₂.toList do
    if let .axiomInfo _ := ci then names := names.push n
  names := names.qsort (fun a b => a.toString < b.toString)
  emit (Json.mkObj [("t", "selftest-axioms"), ("names", Json.arr (names.map (Json.str ∘ toString)))])
  let _ ← checkAxioms cfg env' names emit
  for u in ← runMeta env' (modelUnfolds env') do
    emit (Json.mkObj [("t", "modelUnfold"), ("inst", u)])
  return if nerr > 0 then 1 else 0

unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let mut cfg : Cfg := {}
  for a in args do
    if let some d := a.dropPrefix? "--depth=" then cfg := { cfg with depth := d.toString.toNat! }
    if let some d := a.dropPrefix? "--fuel=" then cfg := { cfg with fuel := d.toString.toNat! }
    if a == "--trace" then cfg := { cfg with trace := true }
  let axFile := args.findSome? fun a => (a.dropPrefix? "--axioms=").map (·.toString)
  let stFile := args.findSome? fun a => (a.dropPrefix? "--selftest=").map (·.toString)
  let mods : Array Name := (args.filter (!·.startsWith "--")).toArray.map String.toName
  if mods.isEmpty then
    IO.eprintln "usage: etc/AxiomTokCheck.lean (--axioms=FILE | --selftest=FILE) [--depth=N] MODULE..."
    return 2
  let out ← IO.getStdout
  let emit := fun (j : Json) => do out.putStrLn j.compress; out.flush
  let t0 ← IO.monoMsNow
  let env ← importModules (mods.map fun m => { module := m, importAll := true }) {} (loadExts := true)
  let t1 ← IO.monoMsNow
  emit (Json.mkObj [("t", "imported"), ("ms", t1 - t0), ("modules", mods.size)])
  if let some f := stFile then
    return ← runSelftest cfg env f emit
  let some f := axFile | IO.eprintln "need --axioms= or --selftest="; return 2
  let names := (← IO.FS.lines f).filter (· ≠ "") |>.map String.toName
  let (ok, bad) ← checkAxioms cfg env names emit
  for u in ← runMeta env (modelUnfolds env) do
    emit (Json.mkObj [("t", "modelUnfold"), ("inst", u)])
  emit (Json.mkObj [("t", "done"), ("ok", ok), ("findings", bad), ("ms", (← IO.monoMsNow) - t1)])
  return 0

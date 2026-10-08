/-
Temporary tooling (branch `no-wp-auto`): record, for every `wp_auto` run (explicit,
or implicit in `wp_apply`/`wp_if_destruct`/`wp_for`/`wp_for_post`/`wp_join`), a
sequence of user-level tactics that reaches the same goal. Each run of `wp_auto_lc 0`
first runs the real `wp_auto` to get its result `G*`, then (from the original state)
greedily takes manual steps (`wp_pures`, `wp_load`, `wp_store`, `wp_alloc l as H`,
`wp_func_lits`, `wp_call`, `unfold c`) until the goal is `G*` up to the points-to
facts `wp_auto` clears (`iclear ..`). The sequence is appended as a JSON line to
`$WP_AUTO_TRACE_DIR/<module>.jsonl` with the source position of the user tactic.
If no sequence is found, the real `wp_auto` result is kept (status `mismatch`).
-/
import Perennial.Golang.Theory.Auto

namespace Perennial
namespace NoWpAutoTrace
open Lean Elab Tactic Meta Iris.ProofMode

/-- The target of `g`, with the free variables not in `keep` replaced by constants
named after them (runs of the same steps create different fvars with the same
names). -/
def normTarget (keep : Std.HashSet FVarId) (g : MVarId) : MetaM Lean.Expr := g.withContext do
  let t ← instantiateMVars (← g.getType)
  let lctx ← getLCtx
  return t.replace fun e => match e with
    | .fvar id =>
      if keep.contains id then none else
      match lctx.find? id with
      | some d => some (mkConst (`_fv ++ d.userName.eraseMacroScopes))
      | none => none
    | _ => none

def irisHypNames (g : MVarId) : MetaM (Option (List Name × Lean.Expr)) := g.withContext do
  let t ← instantiateMVars (← g.getType)
  let some ig := parseIrisGoal? t | return none
  return some ((hypsList ig.hyps).map (·.1), ig.goal)

/-- Iris goal conclusion of `g`, normalized. -/
def normConcl (keep : Std.HashSet FVarId) (g : MVarId) : MetaM (Option Lean.Expr) := g.withContext do
  let t ← normTarget keep g
  let some ig := parseIrisGoal? t | return none
  return some ig.goal

def parseTac (s : String) : TacticM (TSyntax `tactic) := do
  match Parser.runParserCategory (← getEnv) `tactic s with
  | .ok stx => return ⟨stx⟩
  | .error e => throwError "parseTac: {e}"

/-- Equal Iris goals (context and conclusion; metadata around the entailment ignored). -/
def sameGoal (a b : Lean.Expr) : Bool :=
  match parseIrisGoal? a, parseIrisGoal? b with
  | some x, some y => x.e == y.e && x.goal == y.goal
  | _, _ => a.consumeMData == b.consumeMData

def jsonStr (s : String) : String := (Json.str s).compress

structure Ctx where
  keep : Std.HashSet FVarId
  star : Lean.Expr          -- normalized target of `wp_auto`'s result
  starConcl : Option Lean.Expr
  starNames : List Name

/-- The source text of a tactic that changes nothing but names. -/
def tryStep (c : Ctx) (cur : Lean.Expr) (stx : TSyntax `tactic) : TacticM Bool := do
  let s ← saveState
  try
    evalTactic stx
    let gs ← getUnsolvedGoals
    match gs with
    | [g] =>
      let t ← normTarget c.keep g
      if sameGoal t cur then s.restore; return false
      return true
    | _ => s.restore; return false
  catch _ => s.restore; return false

/-- The newest Lean local and Iris hypothesis after `wp_alloc_auto`, for an explicit
`wp_alloc l as H`. -/
def allocNames (before : MVarId) : TacticM (Option (Name × Name)) := do
  let s ← saveState
  try
    let oldNames := ((← irisHypNames before).map (·.1)).getD []
    let oldL ← before.withContext do return (← getLCtx).getFVarIds
    evalTactic (← `(tactic| wp_alloc_auto))
    let [g] ← getUnsolvedGoals | s.restore; return none
    let newNames := ((← irisHypNames g).map (·.1)).getD []
    let lnames ← g.withContext do
      let lctx ← getLCtx
      return lctx.decls.toList.filterMap fun d? => d?.bind fun d =>
        if oldL.contains d.fvarId || d.isImplementationDetail then none else some d.userName
    -- multiset difference: the new name may shadow an old one
    let hnew := oldNames.foldl (fun acc n => acc.erase n) newNames
    s.restore
    match lnames, hnew with
    | [l], [h] =>
      if l.hasMacroScopes then return none
      if h.hasMacroScopes then return none
      return some (l, h)
    | _, _ => return none
  catch _ => s.restore; return none

initialize failInfo : IO.Ref String ← IO.mkRef ""

def fail (msg : String) : TacticM (Option (Array String)) := do
  failInfo.set msg; return none

def ppTrunc (e : Lean.Expr) : MetaM String := do
  let s := toString (← ppExpr e)
  return if s.length > 800 then (s.take 400).toString ++ " … " ++ (s.drop (s.length - 400)).toString else s

/-- The hypotheses whose (normalized) types differ between `g` and the target. -/
def hypDiff (c : Ctx) (g : MVarId) : MetaM String := g.withContext do
  let t ← normTarget c.keep g
  let some ig := parseIrisGoal? t | return "?"
  let some is := parseIrisGoal? c.star | return "?"
  let hs := hypsList ig.hyps
  let hs' := hypsList is.hyps
  let mut out := ""
  for (n, _, p, ty) in hs do
    match hs'.find? (·.1 == n) with
    | some (_, _, p', ty') =>
      if !(ty == ty' && p == p') then
        out := out ++ s!"[{n}: {← ppTrunc ty} (p={p}) VS {← ppTrunc ty'} (p={p'})] "
    | none => pure ()
  if out.isEmpty then
    out := s!"same hyps; Δ equal: {ig.e == is.e}"
  return out

/-- Same hypothesis names (in order) and definitionally equal types. -/
def defeqHyps (c : Ctx) (g : MVarId) : MetaM Bool := g.withContext do
  let t ← normTarget c.keep g
  let some ig := parseIrisGoal? t | return false
  let some is := parseIrisGoal? c.star | return false
  let hs := hypsList ig.hyps
  let hs' := hypsList is.hyps
  unless hs.map (·.1) == hs'.map (·.1) do return false
  for ((_, _, p, ty), (_, _, p', ty')) in hs.zip hs' do
    unless p == p' do return false
    unless ty == ty' do
      unless ← withoutModifyingState (isDefEq ty ty') do return false
  return true

partial def search (c : Ctx) (fuel : Nat) (acc : Array String) : TacticM (Option (Array String)) := do
  let [g] ← getUnsolvedGoals | fail "goals"
  let cur ← normTarget c.keep g
  if sameGoal cur c.star then return some acc
  if fuel == 0 then return ← fail "fuel"
  -- the points-to facts `wp_auto` clears at the end
  if let some concl := c.starConcl then
    if let some concl' ← normConcl c.keep g then
      if concl' == concl then
        let some (names, _) ← irisHypNames g | return ← fail "names"
        let extras := names.filter (fun n => !c.starNames.contains n)
        if extras.isEmpty then
          if ← defeqHyps c g then return some (acc.push "#defeq")
          let d ← hypDiff c g
          return ← fail s!"concl equal, no extras; names {names} star {c.starNames}; {d}"
        if extras.any (·.hasMacroScopes) then return ← fail s!"inaccessible extras {extras}"
        if extras.any (fun n => (names.filter (· == n)).length > 1) then
          return ← fail s!"dup extras {extras}"
        let stx ← parseTac s!"iclear {" ".intercalate (extras.reverse.map toString)}"
        let s ← saveState
        try
          evalTactic stx
          let [g'] ← getUnsolvedGoals | s.restore; return ← fail "iclear goals"
          if sameGoal (← normTarget c.keep g') c.star then
            return some (acc.push s!"iclear {" ".intercalate (extras.reverse.map toString)}")
          if ← defeqHyps c g' then
            return some ((acc.push s!"iclear {" ".intercalate (extras.reverse.map toString)}").push "#defeq")
          let d ← hypDiff c g'
          s.restore; return ← fail s!"after iclear not equal; names {names} star {c.starNames}; {d}"
        catch _ => s.restore; return ← fail "iclear failed"
  -- the manual steps, in order
  let simple : List (String × TSyntax `tactic) :=
    [("wp_pures", ← `(tactic| wp_pures)), ("wp_load", ← `(tactic| wp_load)),
     ("wp_store", ← `(tactic| wp_store))]
  for (txt, stx) in simple do
    if ← tryStep c cur stx then return ← search c (fuel - 1) (acc.push txt)
  if let some (l, h) ← allocNames g then
    let stx ← parseTac s!"wp_alloc {l} as {h}"
    if ← tryStep c cur stx then return ← search c (fuel - 1) (acc.push s!"wp_alloc {l} as {h}")
  if ← tryStep c cur (← `(tactic| wp_alloc_auto)) then
    return ← search c (fuel - 1) (acc.push "wp_alloc_auto")
  for (txt, stx) in [("wp_func_lits", ← `(tactic| wp_func_lits)), ("wp_call", ← `(tactic| wp_call))] do
    if ← tryStep c cur stx then return ← search c (fuel - 1) (acc.push txt)
  -- a value constant that blocks a step
  let wpc ← g.withContext do
    let t ← instantiateMVars (← g.getType)
    let some ig := parseIrisGoal? t | return none
    let some wp ← parseGooseWp? ig.goal | return none
    findValConst wp.e
  if let some (cst, _) := wpc then
    if let .const n _ := cst.getAppFn then
      let stx ← parseTac s!"unfold {n}"
      if ← tryStep c cur stx then return ← search c (fuel - 1) (acc.push s!"unfold {n}")
  let a ← match ← normConcl c.keep g with | some e => ppTrunc e | none => pure "?"
  let b ← match c.starConcl with | some e => ppTrunc e | none => pure "?"
  fail s!"stuck after {acc}\nCUR: {a}\nSTAR: {b}"

def record (line : String) : TacticM Unit := do
  let some dir ← IO.getEnv "WP_AUTO_TRACE_DIR" | return
  let path := System.FilePath.mk dir / s!"{(← getMainModule)}.jsonl"
  let h ← IO.FS.Handle.mk path .append
  h.putStrLn line

def runTraced : TacticM Unit := do
  let ref ← getRef
  let fm ← getFileMap
  let pos := (ref.getPos? (canonicalOnly := false)).map fm.toPosition
  let posStr := match pos with
    | some p => s!"{p.line}:{p.column}"
    | none => "?"
  let g ← getMainGoal
  let tag := toString (← g.getTag).eraseMacroScopes
  let ngoals := (← getGoals).length
  -- `pos` is spliced as the first field: it carries the goal tag and count too
  let posStr := posStr ++ "\",\"tag\":" ++ jsonStr tag ++ ",\"ngoals\":\"" ++ toString ngoals
  let keep ← g.withContext do return Std.HashSet.ofArray ((← getLCtx).getFVarIds)
  let s0 ← saveState
  -- the real `wp_auto` (errors, e.g. "no progress", propagate as before)
  try
    withOptions (fun o => o.setBool `noWpAuto.inner true) <|
      evalTactic (← `(tactic| wp_auto_lc 0))
  catch ex =>
    record s!"\{\"pos\":\"{posStr}\",\"status\":\"noprogress\"}"
    throw ex
  let gs ← getUnsolvedGoals
  let sAuto ← saveState
  let [gStar] := gs | do
    record s!"\{\"pos\":\"{posStr}\",\"status\":\"multigoal\",\"n\":{gs.length}}"
    return
  let star ← normTarget keep gStar
  let starConcl ← normConcl keep gStar
  let starNames := ((← irisHypNames gStar).map (·.1)).getD []
  s0.restore
  let res ← search { keep, star, starConcl, starNames } 200 #[]
  match res with
  | some seq =>
    let arr := "[" ++ ",".intercalate (seq.toList.map jsonStr) ++ "]"
    record s!"\{\"pos\":\"{posStr}\",\"status\":\"ok\",\"seq\":{arr}}"
  | none =>
    sAuto.restore
    record s!"\{\"pos\":\"{posStr}\",\"status\":\"mismatch\",\"why\":{jsonStr (← failInfo.get)}}"

elab_rules : tactic
  | `(tactic| wp_auto_lc $n:num) => do
    if (← getOptions).getBool `noWpAuto.inner then throwUnsupportedSyntax
    if n.getNat != 0 then throwUnsupportedSyntax
    if (← IO.getEnv "WP_AUTO_TRACE_DIR").isNone then throwUnsupportedSyntax
    runTraced

end NoWpAutoTrace
end Perennial

/- What `Step`'s getter tactics (`wp_get`, `wp_gets` in `ElectionLemmas.lean`, `wp_get`,
`wp_drive` in `ReplLemmas.lean`) read off the goal to choose a spec (2026-10-20).

They used to try every getter spec in turn (`first | wp_apply PB.GetTerm.1 … | …`), and a spec
that does not fit costs about half a second on `Step`'s body (`wp_apply` runs `wp_pures` twice
before giving up): every `wp_gets` paid for six failed attempts at its end, every `wp_drive` for
fourteen, and every step for the alternatives listed before it. Reading the next redex -- the
method a call resolves, or the field a load reads -- picks the one spec that can apply. The step
taken is the same `wp_apply` of the same spec; only the search for it changes. -/
module

public import Perennial.Golang.Theory.ProofMode

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace StepProof

open Lean in
/-- The natural-number literals of `e`. -/
meta partial def natLits : Lean.Expr → List Nat
  | .lit (.natVal n) => [n]
  | .app f a => natLits f ++ natLits a
  | .mdata _ b => natLits b
  | _ => []

open Lean in
/-- The bytes of a byte-list literal `[71#8, 101#8, ...]` as characters (each byte's largest
literal: the other is the width `8`). -/
meta partial def byteChars (l : Lean.Expr) : List Char :=
  if l.isAppOfArity ``List.cons 3 then
    Char.ofNat ((natLits (l.getArg! 1)).foldl max 0) :: byteChars (l.getArg! 2)
  else []

open Lean in
/-- The first byte-list literal of `e`, as a string: a method's or a field's name. -/
meta def firstName? (e : Lean.Expr) : Option String :=
  (e.find? (·.isAppOfArity ``List.cons 3)).map fun l => String.ofList (byteChars l)

open Lean Elab Tactic Meta in
/-- The evaluation-position sub-expressions of the WP goal, innermost (the next redex) first. -/
meta def redexes : TacticM (List Lean.Expr) := withMainContext do
  let t := (← instantiateMVars (← getMainTarget)).consumeMData
  unless t.isAppOfArity ``Iris.ProofMode.Entails' 4 do return []
  let some wp ← Perennial.parseGooseWp? t.appArg! | return []
  return ((← Perennial.allEctx wp.e).reverse.take 4).map (·.2)

open Lean Elab Tactic Meta in
/-- The method whose call is the next redex (`GetType` for
`#(methods (ptrT Message.ty) "GetType" #ml) #()`), if it is a call of a method value. -/
meta def nextMethod? : TacticM (Option String) := withMainContext do
  let some e := (← redexes).head? | return none
  let e ← whnfR e
  let_expr Perennial.Expr.App _ f _ := e | return none
  return firstName? f

open Lean Elab Tactic Meta in
/-- The field the next redex loads (`f` of `![T] #r.[raft, f]`), if it is a load of a field. -/
meta def nextField? : TacticM (Option String) := withMainContext do
  let some e := (← redexes).head? | return none
  let e ← whnfR e
  let_expr Perennial.Expr.App _ f a := e | return none
  unless (f.find? (·.isAppOf ``Perennial.GoInstruction.GoLoad)).isSome do return none
  return firstName? a

open Lean Elab Tactic in
/-- Run the tactic text `s`, parsed at the call site (so its names, `Hm`, `Hphys`, `Hty`, are
the caller's hypotheses). -/
meta def evalTacticString (s : String) : TacticM Unit := do
  match Parser.runParserCategory (← getEnv) `tactic s with
  | .ok stx => evalTactic stx
  | .error e => throwError "evalTacticString: {e}"

end StepProof
end EtcdGrove
end Perennial

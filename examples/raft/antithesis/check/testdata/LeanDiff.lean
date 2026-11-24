/-
The differential test of the Lean transcription (`AntCheck.run`,
`Proof/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/check/Tla/`) against TLC and the
Go checker: on the fixtures `cmd/leanexport` writes (the streams as the Go reader parsed them,
with TLC's and the Go's verdicts), the Lean verdict must agree with TLC's as diff_test.go's
`agrees` says (kind and event; for a violation the properties; for TLC's ERROR an `EvalM`
error), and so with the Go's. Not part of the build (outside every lean_lib); run by
`testdata/lean-diff.sh`:

  lake env lean --run examples/raft/antithesis/check/testdata/LeanDiff.lean fixtures.ndjson
-/
import Lean.Data.Json
import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Tla.Check

open Lean Perennial Perennial.EtcdGrove.AntCheck

def str (s : String) : Str := stringToGoString s

def getStr (j : Json) (k : String) : Except String String := do (← j.getObjVal? k).getStr?
def getInt (j : Json) (k : String) : Except String Int := do (← j.getObjVal? k).getInt?
def getBool (j : Json) (k : String) : Except String Bool := do (← j.getObjVal? k).getBool?
def getArr (j : Json) (k : String) : Except String (Array Json) := do (← j.getObjVal? k).getArr?
def has (j : Json) (k : String) : Bool := (j.getObjVal? k).toOption.isSome
def opt {α : Type} (j : Json) (k : String) (f : Json → String → Except String α) :
    Except String (Option α) :=
  if has j k then some <$> f j k else pure none
def strs (a : Array Json) : Except String (List Str) := a.toList.mapM (fun s => do pure (str (← s.getStr?)))

def decValue (j : Json) : Except String Value := do
  pure { isRec := ← getBool j "isRec", str := str (← getStr j "str"),
         add := ← strs (← getArr j "add"), remove := ← strs (← getArr j "remove"),
         joint := ← getBool j "joint", leave := ← getBool j "leave" }

def decEntries (a : Array Json) : Except String (List Entry) :=
  a.toList.mapM (fun e => do
    pure { term := ← getInt e "term", type := str (← getStr e "type"), value := ← decValue (← e.getObjVal? "value") })

def decMsg (j : Json) : Except String Msg := do
  pure { type := (← opt j "type" getStr).map str, frm := (← opt j "from" getStr).map str,
         to := (← opt j "to" getStr).map str, term := ← opt j "term" getInt,
         index := ← opt j "index" getInt, logTerm := ← opt j "logTerm" getInt,
         entries := ← opt j "entries" (fun j k => do decEntries (← getArr j k)),
         commit := ← opt j "commit" getInt, reject := ← opt j "reject" getBool }

def decEvent (j : Json) : Except String Event := do
  pure { e := str (← getStr j "e"), node := str (← getStr j "node"), bad := str (← getStr j "bad"),
         b := ← getBool j "b", a := ← getBool j "a",
         byE := (← opt j "by" getStr).map str, role := (← opt j "role" getStr).map str,
         term := ← opt j "term" getInt, vote := (← opt j "vote" getStr).map str,
         commit := ← opt j "commit" getInt, first := ← opt j "first" getInt,
         entries := ← opt j "entries" (fun j k => do decEntries (← getArr j k)),
         lastIndex := ← opt j "lastIndex" getInt, lastTerm := ← opt j "lastTerm" getInt,
         applied := ← opt j "applied" getInt,
         voters := ← opt j "voters" (fun j k => do strs (← getArr j k)),
         outgoing := ← opt j "outgoing" (fun j k => do strs (← getArr j k)),
         snap := ← opt j "snap" (fun j k => do
           let s ← j.getObjVal? k
           pure ({ index := ← getInt s "index", term := ← getInt s "term" } : SnapRef)),
         msg := ← opt j "msg" (fun j k => do decMsg (← j.getObjVal? k)),
         cause := ← opt j "cause" (fun j k => do (← getArr j k).toList.mapM decMsg),
         w := ← opt j "w" getInt, more := ← opt j "more" getInt, index := ← opt j "index" getInt,
         ctx := (← opt j "ctx" getStr).map str }

def kindName : Kind → String
  | .accepted => "ACCEPTED" | .rejected => "REJECTED" | .violated => "VIOLATED" | .error => "ERROR"

def nameStr (s : Str) : String := String.fromUTF8! (ByteArray.mk (s.map (fun b => b.toNat.toUInt8)).toArray)

/-- diff_test.go's `agrees`, of the Lean result and TLC's line. -/
def agrees (r : EvalM Verdict) (tlc : String) : Bool :=
  match tlc.splitOn " " with
  | "ERROR" :: _ => (match r with | .error _ => true | .ok _ => false)
  | k :: n :: rest =>
    match r with
    | .error _ => false
    | .ok v =>
      let n := n.toInt!
      if k == "ACCEPTED" then v.kind == .accepted && v.k == n
      else if k == "REJECTED" then v.kind == .rejected && v.k == n
      else if k == "VIOLATED" then
        let want := ((rest.headD "").splitOn ",").toArray.qsort (· < ·)
        let got := (v.names.map nameStr).toArray.qsort (· < ·)
        v.kind == .violated && v.k == n && want == got
      else false
  | _ => false

def main (args : List String) : IO UInt32 := do
  let path := args.headD "fixtures.ndjson"
  let lines := (← IO.FS.lines path).filter (· ≠ "")
  let mut agree := 0
  let mut disagree := 0
  for line in lines do
    let r : Except String (String × String × String × EvalM Verdict) := do
      let j ← Json.parse line
      let cfg : Config := { server := ← strs (← getArr j "servers"), initVoters := ← strs (← getArr j "voters"),
                            bootstrapped := ← getBool j "bootstrapped" }
      let evs ← (← getArr j "events").toList.mapM decEvent
      let g ← j.getObjVal? "go"
      pure (← getStr j "file", ← getStr j "tlc", ← getStr g "kind", run cfg evs)
    match r with
    | .error e => IO.println s!"DECODE {e}"; disagree := disagree + 1
    | .ok (file, tlc, goKind, v) =>
      if agrees v tlc then agree := agree + 1
      else
        disagree := disagree + 1
        let lv := match v with
          | .ok v => s!"{kindName v.kind} {v.k} {v.names.map nameStr}"
          | .error e => s!"ERROR {e}"
        IO.println s!"DIFF {file}: Lean {lv}, TLC {tlc.take 120}, Go {goKind}"
  IO.println s!"agree {agree} disagree {disagree}"
  return if disagree == 0 then 0 else 1

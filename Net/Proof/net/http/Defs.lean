/-
The vocabulary of the net/http model's specs (`Net/Spec/net/http/`; the model `models/net/http`,
translated by project models-net), for `ReadResponse` on net/rpc's `CONNECT` answer (2026-11-23):

* `httpEnv` (persistent): the package state the parse reads: `bufio`'s, `io`'s, `fmt`'s (the
  `badStringError`s) and `strconv`'s (`Atoi`) initialization, and net/http's `NoBody` (the body of a
  response with none). net/http has no package initialization proof yet
  (`notes/dsverify-net-port-plan.md`, phase 5 item 2, 5): a client takes `httpEnv` as a premise.
* `cutByte s c`, `trimLeftByte s c`: what the model's `modelCutByte` and `modelTrimLeftByte` return
  (`strings.Cut(s, string(c))`, `strings.TrimLeft(s, string(c))`, `textproto_model.go`).
* `fieldByte c`: `c` may be in a header field name (textproto's `validHeaderFieldByte`, RFC 7230's
  `tchar`); `canonQuick s`: textproto's `CanonicalMIMEHeaderKey`'s quick check accepts `s` as it is
  (it returns `s` without canonicalizing it: a byte that is no `tchar`, or every letter upper case
  at the start and after each `-` and lower case elsewhere).
* `statusLine`: the status line of net/rpc's answer (`connectAns` without its two `"\n"`).
-/
module

public import Net.GeneratedProof.net.http
public import Net.Proof.net.rpc.Proto
public import Proof.bufio.Defs
public import Perennial.Proof.fmt
public import Perennial.Proof.strconv

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace net.http

section env
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- See the file header. -/
def httpEnv : IProp GF :=
  iprop(isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
    isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ isPkgInit (PROP := IProp GF) pkg_id.strconv ∗
    ∃ nb : net.http.noBody, globalAddr net.http.NoBody ↦□ nb)

instance httpEnv_persistent : Persistent (httpEnv (GF := GF)) := by
  unfold httpEnv; infer_instance

end env

section pure

/-- See the file header. -/
def cutByte (s : List w8) (c : w8) : List w8 × List w8 × Bool :=
  match s.findIdx? (· = c) with
  | some i => (s.take i, s.drop (i + 1), true)
  | none => (s, [], false)

/-- See the file header. -/
def trimLeftByte (s : List w8) (c : w8) : List w8 := s.dropWhile (· = c)

/-- See the file header (RFC 7230's `tchar`). -/
def fieldByte (c : w8) : Bool :=
  decide ((48 ≤ c.toNat ∧ c.toNat ≤ 57) ∨ (97 ≤ c.toNat ∧ c.toNat ≤ 122) ∨
  (65 ≤ c.toNat ∧ c.toNat ≤ 90) ∨
  c ∈ [W8 33, W8 35, W8 36, W8 37, W8 38, W8 39, W8 42, W8 43, W8 45, W8 46, W8 94, W8 95,
    W8 96, W8 124, W8 126])

/-- `CanonicalMIMEHeaderKey`'s quick check from the rest `s`, `upper` whether the next letter
should be upper case. -/
def canonQuickFrom : List w8 → Bool → Bool
  | [], _ => true
  | c :: s, upper =>
    if fieldByte c = false then true
    else if upper = true ∧ 97 ≤ c.toNat ∧ c.toNat ≤ 122 then false
    else if upper = false ∧ 65 ≤ c.toNat ∧ c.toNat ≤ 90 then false
    else canonQuickFrom s (decide (c = W8 45))

/-- See the file header. -/
def canonQuick (s : List w8) : Bool := canonQuickFrom s true

/-- A line without its `"\r"` before the `"\n"` (`modelReadLine`). -/
def dropCR (l : List w8) : List w8 :=
  if l.getLast? = some (W8 13) then l.dropLast else l

/-- See the file header. -/
def statusLine : List w8 := go!"HTTP/1.0 200 Connected to Go RPC"

theorem connectAns_eq : net.rpc.connectAns = statusLine ++ [W8 10, W8 10] := by decide

end pure

end net.http
end Perennial

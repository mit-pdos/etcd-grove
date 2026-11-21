/-
Package initialization of `golang_org.x.crypto.bcrypt`
(item 8, 2026-10-17): its facts and trust-boundary axioms; its `wp_initialize'` is in
`InitLinked.lean` (2026-11-19: the proof applies other packages' `wp_initialize'` and
functions' proofs, so it is a linking module, CLAUDE.md "Import tiers").

Its fact is `True`. Its initializer allocates its variables, initializes its imports and runs
their translated initializers (`bcrypt.go`, `base64.go`; prove-authcrypto, 2026-11-21: until then the
trust-boundary axiom `opaqueInitsOk`): `bcEncoding = base64.NewEncoding(alphabet)`
(`NewEncoding.wp_proof`: the alphabet is 64 distinct symbols, neither `\n` nor `\r`), three
`errors.New` errors (Perennial's `errors.wp_New_errorString`) and the byte-slice literal
`magicCipherData`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.Base
public import Perennial.Proof.errors.Link
public import Proof.encoding.base64.Init
public import Perennial.Proof.errors.NewVar

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial

/-- `x ∈ [a, ..., x, ...]`, linear in the list (`simp` overflows on the long ones). -/
local macro "mem_tac" : tactic =>
  `(tactic| repeat (first | exact List.Mem.head _ | apply List.Mem.tail))

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

end Perennial

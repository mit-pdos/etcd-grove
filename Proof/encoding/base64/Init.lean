/-
Package initialization of `encoding.base64`
(item 8, 2026-10-17): its facts and trust-boundary axioms; its `wp_initialize'` is in
`InitLinked.lean` (2026-11-19: the proof applies other packages' `wp_initialize'` and
functions' proofs, so it is a linking module, CLAUDE.md "Import tiers").

Its fact (`base64Init`, `encoding/base64/Base.lean`; the auth plan's E2x, 2026-10-26;
k8s 7e-2, 2026-11-09): `StdEncoding` and `RawURLEncoding` hold fixed `*Encoding`s whose
`EncodeToString` returns the standard encoding (`stdEnc`), resp. the URL encoding without padding
(`rawUrlEnc`), of its argument's bytes, stated as the method call's own WP; so does
`RawStdEncoding`'s, the standard encoding without padding (`rawStdEnc`; phase 7 S2 core, 2026-11-23).
Its initializer allocates its four variables and runs their translated initializers (`base64.go`,
translated with their bodies since 2026-11-20, prove-b64clock; until then the trust-boundary axioms
`StdEncoding_init`, `RawURLEncoding_init` and `opaqueInitsOk`): `NewEncoding` of the two alphabets
(`NewEncoding.wp_proof`; valid alphabets, `stdAlphabet_ok`, `urlAlphabet_ok`), and `WithPadding(NoPadding)`
of each (`Encoding.WithPadding.wp_proof`); the fact's parts from `EncodeToString`'s spec
(`stdEncInit_intro`, `rawUrlEncInit_intro`, `rawStdEncInit_intro`).
-/
module

public import Proof.encoding.base64.Base
public import Perennial.Proof.strconv.Link
public import Proof.internal.byteorder.Init
public import Proof.encoding.base64.InitFacts

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

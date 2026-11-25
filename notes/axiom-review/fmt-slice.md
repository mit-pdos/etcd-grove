# `fmt.SprintfSlice` and `fmt.ErrorfSlice`: false of the real `fmt` (2026-11-24, retired)

**Axioms.** `fmt.SprintfSlice.wp_proof` and `fmt.ErrorfSlice.wp_proof` (`Spec/fmt/{Sprintf,Errorf}Slice.lean`,
fmtmodel 2026-11-20), the trust base of `k8s_authz_safe`/`k8s_authz_robust`. Each promised that
`fmt.Sprintf`/`fmt.Errorf` return when an argument is a read-only slice under `%v`/`%s`
(`fmt.sliceArgOk`).

**Verdict: false of the semantics** (not of Go). Since the real `fmt` was translated (stage 1, lean
`af4fd74b00`, Perennial `52d62e83c`), `Sprintf`/`Errorf` run `fmt`'s own code. For a slice, `printArg` calls
`printValue`, which reflects into the slice, and Perennial's translation of that code is stuck there. So the
axioms promised a return from an expression whose WP is stuck. The argument was found when stage 1 landed
(#9 7130506276, 7130595434). No proof had used the gap to derive anything Go does not do. Go itself returns
`[` + the elements' `%v` separated by spaces + `]`.

**Retired** (branch `prove-ps2-sprintfslice/2026-11-24`, #9 7136404436). The three call sites (all in the
KEP-5681 fork translated as project `k8s-authz`) now spell the slice out, byte-identically. They are on
`upamanyus/kubernetes` branch `goose-lean-authz-fmt2`, `5b30dab1b14`, which is luxas `c67a81026c8b` plus
one commit:
- `ConditionsAwareDecision.UnconditionalPartsOrFailClosed` (`[]Decision`),
- `unionAuthzHandler.EvaluateConditions` (`[]Decision`),
- `ConditionsAwareDecisionUnion.Add` (`[]string`).

Each site builds the string with a loop and `+=` and formats it with `[%s]`. The fork's Go tests compare
each rewrite with the original call (`authorizer/fmt_spelled_test.go`, `union/union_fmt_test.go`). The
proofs go through `fmt.wp_Sprintf` (Perennial) and `fmt.ErrorfLeaf` (proved). The axioms, their specs and
the slice vocabulary (`fmt.sliceArgOk`, `fmt.argOkAtSl`, `fmt.argsOkSl`, `Decision.sliceArgOkAt`) are
deleted. Trust base −2.

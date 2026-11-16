# `fmt.ErrorfPlain.wp_proof` is false for a flagged `w` verb (2026-11-15)

Found by k8s 7f-5a-P (sixteenth agent) while preparing to apply the approved E3 text
(`notes/k8s-7f5a-draft.md` §11.3), whose review named `%+w`/`%-5w` as wrapping forms. STOPPED for
etcd-grove-81 (soundness finding).

## The axiom

`Spec/fmt/ErrorfPlain.lean`, axiom `Proof/fmt/ErrorfPlain.lean`: for a format with
`¬ List.IsInfix go!"%w" format` and `fmt.argsOk fmt.errorfVerbs format xs`, `fmt.Errorf` returns
`interface.mkOk (*errors.errorString) #x` (a leaf, `errStrCell`).

## Why it is false

The premise looks for the two bytes `%w` only. A `w` directive with flags, width or precision
(`%+w`, `%-5w`, `% w`, `%#w`, `%05.2w`) has no `%w` infix, and `fmt.fmtDirectives` parses it as a
directive with verb `w`, which `fmt.argsOk fmt.errorfVerbs` admits for an error argument. Go's
`doPrintf` records a wrap at every `w` verb with an argument (`fmt/print.go:1051-1052,1146-1147`,
go1.27.3), so `Errorf` returns a `*fmt.wrapError`, not an `*errors.errorString`.

Counterexample (`examples/axiomcx/errorfplain`, passes): `fmt.Errorf("%+w", io.EOF)` is not an
`*errors.errorString`, and `errors.Is(err, io.EOF)` is true; the program `if errors.Is(fmt.Errorf("%+w",
io.EOF), io.EOF) { panic(...) }` panics, while the axiom (a leaf `errorString`, not `io.EOF`'s cell)
lets one prove it does not.

## Reach

Latent: the axiom's only callers, `rafthttp.checkPostResponse` and `rafthttp.streamReader.dial`
(server `Link.lean`), use literal formats with no `w` verb at all (discharged by `decide`).

## Proposed fix (trusted-text change, for etcd-grove-81)

Replace the premise by E3's: `fmt.fmtDirectives format = some ds ∧ ∀ d ∈ ds, d.verb ≠ W8 119`
(the evidence of `examples/premisefix/errorfwrap`, the 200000-format differential test, covers exactly
this premise). The two callers' `by decide` still discharge it. Alternatively derive `ErrorfPlain` from
`fmt.Errorf.spec` once E3 is applied there, leaving one axiom.

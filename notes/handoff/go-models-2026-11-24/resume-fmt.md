# fmt S3 resume (after the adversarial review)
Branch goose-model-overlay-rest-fmt, worktree pgmR-fmt, head 91ddf36c4 (WIP, pushed).

Done (in 91ddf36c4):
- Go model fix: errorf keeps newPrinter/free and reads string(p.buf); doPrintf(b *buffer, ...) writes the
  exact prefix into the buffer, then writeArbitrary chunks before each visitArg and at the end (visitRest
  takes b); pp.doPrint the same; doc comments corrected (pool observable; #61060 environment assumption).
- Perennial/Code/fmt.lean regenerated (strconv.lean churn restored).
- Tests: TestModelAlias (goose/model/fmt/testdata/alias: alias_test.go, alias_goose_test.go,
  gomodel_driven.go), wired into etc/model-tests.sh (real fmt + models with driven choices). Passes; the
  old model fails all 5 cases. Harness updated (buffer stand-in, arbitraryBool, squash). go test ./goose/...
  and etc/model-tests.sh pass.
- Lean port WRITTEN, NOT CHECKED: VisitModel (wp_writeArbitrary, wp_writeArbitrary_ex, wp_visitRest with b/bs),
  DoPrintf (wp_doPrintfB/wp_doPrintf take b bs, post ∃ s, bufferOwn b (bs ++ s)), Fprintf, Fprint (wp_pp_doPrint
  carries ∃ r bufferOwn in the loop invariant), Errorf (newPrinter, doPrintf into p.buf, wp_bytes_to_string,
  errorfResult, free), Results (wp_Fprintf_bytes), Link (etc/gen-link.py).

In flight: nothing (the vmlake --fetch build of Perennial.Proof.fmt was killed while queued; no .lake locally).

Next:
1. `/shared/tmp/vm/vmlake --fetch build Perennial.Proof.fmt` (fails at the proofs; brings back oleans), then
   `etc/lean-check.py` on VisitModel, DoPrintf, Fprintf, Fprint, Errorf, Results in that order. Likely fixes:
   `p.[fmt.pp, go!"buf"]` spelling (or `_`), where wp_auto stops around writeString/writeArbitrary calls,
   `simp only [List.append_assoc]` on the Iris goal, `[] ++ s` in Errorf.
2. Build the cone: Perennial.Proof.{fmt,bytes,log,math.big,crypto.rand,internal.poll} + importers (packet's list).
3. #print axioms (gmr-fmt/FmtAxioms.lean), etc/gen-link.py --check, commit, push.
4. packet.md: add "After the adversarial review" (the fix, TestModelAlias, statements unchanged).

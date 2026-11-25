# Finding: Net's trusted `(*OpError).Error` model calls none of the fields' methods (dsv-fix6)

Recorded 2026-11-25 in worktree `/shared/etcd-grove-dsvfix6` (branch `dsv-fix6` at `38dbbc96bf`),
Perennial `fce59af75`, Go go1.27.3. First seen by the review `log-logger-3.md` ("Related finding"),
outside the axioms that review attacked. **Status: open. Needs its own `axiom` review and a fix decided
by the owner of `Net/TrustedCode/net.lean` (the trusted model is shared by every Net kit). Not fixed
here.**

## The trusted code

`Net/TrustedCode/net.lean`, `OpError.Error.impl` (last changed `715cdf9d44`):

    if e = nil then "<nil>" else
    let s1 := AnyString; let s2 := AnyString
    *e.Op ++ s1 ++ ": " ++ s2

It reads only `e.Op` and calls nothing. Go's `(*OpError).Error` (`src/net/net.go:500-521`, go1.27.3)
calls `e.Source.String()` and `e.Addr.String()` when they are non-nil, and `e.Err.Error()`: methods of
whatever values the program stored in those interface fields. `OpError` is a translated struct, so a
program can build one with any `Err`/`Source`/`Addr`.

The proved spec over it, `net.wp_OpError_Error` (`Net/Proof/net/Errors.lean:189`), asks only
`pe ↦□ v` and gives back the message: nothing of `v.Err'`, `v.Source'`, `v.Addr'`. So every program
that calls `Error()` on an `*OpError` whose fields' methods panic, block or race gets a no-panic triple.

## Crash program

    package main

    import (
    	"fmt"
    	"net"
    )

    // pErr is an error whose Error method panics.
    type pErr struct{}

    func (*pErr) Error() string { panic("pErr.Error called") }

    func main() {
    	pe := &net.OpError{Op: "read", Net: "tcp", Err: &pErr{}}
    	// No further write to *pe: `pe ↦□ v` is obtainable (persist the points-to).
    	msg := pe.Error() // Net's model: `"read" ++ s1 ++ ": " ++ s2`, calls nothing
    	fmt.Println(len(msg))
    }

Run (go1.27.3, linux/amd64), deterministic:

    panic: pErr.Error called

    goroutine 1 [running]:
    main.(*pErr).Error(...)
    	main.go:11
    net.(*OpError).Error(...)
    	.../src/net/net.go:520
    main.main()
    	main.go:16
    exit status 2

Lean side (argued, not built): allocate `pe` with the struct literal, persist its points-to, and
`wp_OpError_Error pe v` proves `{{ True }} pe.Error() {{ RET #msg; True }}` with no condition on `Err`.
`log-logger-3.md` also ran a racy variant (`Err`'s `Error()` writes a map another goroutine writes:
`fatal error: concurrent map writes`, 3/3), reached through `log.Printf("%v", op)` as well.

## Reach

Every `errAny`/`errPlain` of an `*OpError` (`Net/Proof/net/rpc/Errs.lean`'s `errAny_opErr`, `resErr`,
`opErrPtr`; `Net/Proof/net/http/ServeLoopLemmas.lean:214`; `errFmt`'s `*OpError` case in
`Net/Proof/models_lab/ErrFmt.lean`) inherits it. The errors Net itself makes have `Err` among
`poll.errNetClosing`, `*poll.DeadlineExceededError`, `*os.SyscallError` (whose methods do not panic), and
`Source`/`Addr` `*TCPAddr`s or `nil`, so the kits' own programs are not known to reach it; the model is
faithful only for such fields.

## Fix directions (for the owner; none taken)

1. `wp_OpError_Error` (and the specs that turn an `*OpError` into `errAny`) ask, of `v.Err'`, an `errAny`
   (a WP of its `Error()`), and of non-nil `v.Source'`/`v.Addr'` a WP of `String()`; the model then calls
   them (`MethodCall`) as Go does, with the strings it does not explain still `AnyString`.
2. Or keep the model and restrict it in its docstring and specs to fields of net's own types (a premise
   `opErrFieldsNet v`, provable at every Net producer).

Either changes trusted code, so it goes through its own `axiom` review (with this program as the first
attack) before landing.

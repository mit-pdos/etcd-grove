// Package b1 is the Go harness of sweep repairs 1, group b1 (batch 1's non-zap items): each new
// premise of the drafted repairs as a runtime predicate, checked over the counterexamples of the
// axiom sweep (where it must fail) and over the values etcd's own paths produce (where it must
// hold). Not committed; see /shared/tmp/sweep-repairs-1/b1.md.
package b1

import (
	"context"
	"net/http"
	"os"
	"reflect"
	"strings"
	"time"

	"go.etcd.io/etcd/pkg/v3/traceutil"
)

// IsCtxErr is the Go meaning of Perennial's `context.isCtxErr err`: `err` is the value of
// `context.Canceled` or of `context.DeadlineExceeded` (B1's new premise of `errors.IsCtxErr`).
func IsCtxErr(err error) bool {
	return err != nil && (err == context.Canceled || err == context.DeadlineExceeded)
}

// StartTimeOk is the Go meaning of `context.startTimeOk ctx` (B2): `ctx.Value(StartTimeKey{})`
// returns, and returns nil or a `time.Time`. A panic of `Value` is reported as false.
func StartTimeOk(ctx context.Context) (ok bool) {
	defer func() {
		if recover() != nil {
			ok = false
		}
	}()
	v := ctx.Value(traceutil.StartTimeKey{})
	if v == nil {
		return true
	}
	_, isTime := v.(time.Time)
	return isTime
}

// LitPathPat is the Go meaning of `http.litPathPat pat` (B3): a non-empty pattern starting with
// `/` with no space, tab, `{` or `%` (no method, no host, no wildcard, no escape).
func LitPathPat(p string) bool {
	return len(p) > 0 && p[0] == '/' && !strings.ContainsAny(p, " \t{%")
}

// HandlerRegOk is the Go meaning of `http.handlerRegOk h` (B3): a non-nil handler whose dynamic
// type is not `http.HandlerFunc`.
func HandlerRegOk(h http.Handler) bool {
	if h == nil {
		return false
	}
	return reflect.TypeOf(h) != reflect.TypeOf(http.HandlerFunc(nil))
}

// EnvVerifyOff is the Go meaning of the startup fact `envVerifyOff` (B4): `ETCD_VERIFY`,
// lower-cased, is none of `all`, `assert`, `lock` (`verify.IsVerificationEnabled`).
func EnvVerifyOff() bool {
	v := strings.ToLower(os.Getenv("ETCD_VERIFY"))
	return v != "all" && v != "assert" && v != "lock"
}

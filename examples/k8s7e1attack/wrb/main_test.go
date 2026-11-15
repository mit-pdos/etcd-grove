// Copies of etcd's waitRetryBackoff / contextErrToGRPCErr: every return path's description, the
// evidence for waitRetryBackoff.spec's `err = nil ∨ errDesc err ∉ handlerDescs` (k8s 7e-1), and the
// ctxOk gap it found (TestQuietPanics; fixed on lean by premise-fixes-5).
package wrb

// Copies of waitRetryBackoff / contextErrToGRPCErr at etcd 673da07c8f (client/v3/retry_interceptor.go;
// unchanged at the pin a4d2bb1720b9).
import (
	"context"
	"errors"
	"fmt"
	"testing"
	"time"

	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/status"
)

type options struct{ backoffFunc func(uint) time.Duration }

func waitRetryBackoff(ctx context.Context, attempt uint, callOpts *options) error {
	waitTime := time.Duration(0)
	if attempt > 0 {
		waitTime = callOpts.backoffFunc(attempt)
	}
	if waitTime > 0 {
		timer := time.NewTimer(waitTime)
		select {
		case <-ctx.Done():
			timer.Stop()
			return contextErrToGRPCErr(ctx.Err())
		case <-timer.C:
		}
	}
	return nil
}

func contextErrToGRPCErr(err error) error {
	switch {
	case errors.Is(err, context.DeadlineExceeded):
		return status.Error(codes.DeadlineExceeded, err.Error())
	case errors.Is(err, context.Canceled):
		return status.Error(codes.Canceled, err.Error())
	default:
		return status.Error(codes.Unknown, err.Error())
	}
}

var opts = &options{backoffFunc: func(uint) time.Duration { return time.Second }}

func show(t *testing.T, name string, ctx context.Context) {
	err := waitRetryBackoff(ctx, 1, opts)
	t.Logf("%-22s %T msg=%q", name, err, status.Convert(err).Message())
}

func TestPaths(t *testing.T) {
	c1, f1 := context.WithCancel(context.Background())
	f1()
	show(t, "WithCancel", c1)
	c2, f2 := context.WithCancelCause(context.Background())
	f2(errors.New("etcdserver: mvcc: required revision is a future revision"))
	show(t, "WithCancelCause", c2)
	c3, f3 := context.WithTimeout(context.Background(), time.Nanosecond)
	defer f3()
	time.Sleep(time.Millisecond)
	show(t, "WithTimeout", c3)
	c4, f4 := context.WithDeadlineCause(context.Background(), time.Now(), errors.New("etcdserver: mvcc: required revision has been compacted"))
	defer f4()
	show(t, "WithDeadlineCause", c4)
	show(t, "TODO (timer fires)", context.TODO())
	// ctxErrs-style: Err() is an *errors.errorString with an arbitrary message
	show(t, "errString ctx", errCtx{c1, errors.New("custom")})
	// *status.Error as Err(): Message() of the result is the whole Error() string
	show(t, "statusErr ctx", errCtx{c1, status.Error(codes.Aborted, "etcdserver: mvcc: required revision is a future revision")})
}

type errCtx struct {
	context.Context
	e error
}

func (c errCtx) Err() error { return c.e }

// ctxQuiet holds (Err() always nil); Done() is a closed channel.
type quietDone struct{ context.Context }

func (quietDone) Err() error { return nil }

// ctxQuiet holds (Err() always nil); Done() panics (nil receiver).
type quietPanic struct{ ch chan struct{} }

func (*quietPanic) Deadline() (time.Time, bool) { return time.Time{}, false }
func (q *quietPanic) Done() <-chan struct{}     { return q.ch }
func (*quietPanic) Err() error                  { return nil }
func (*quietPanic) Value(any) any               { return nil }

func try(t *testing.T, name string, ctx context.Context) {
	defer func() {
		if r := recover(); r != nil {
			t.Logf("%-22s PANIC: %v", name, r)
		}
	}()
	show(t, name, ctx)
}

func TestQuietPanics(t *testing.T) {
	c, f := context.WithCancel(context.Background())
	f()
	try(t, "quiet, Done closed", quietDone{c})
	var q *quietPanic
	try(t, "quiet, nil receiver", q)
	fmt.Println()
}

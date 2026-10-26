package authkv

import (
	"context"
	"errors"
	"testing"
	"time"

	"go.etcd.io/etcd/api/v3/v3rpc/rpctypes"
	clientv3 "go.etcd.io/etcd/client/v3"
	"go.uber.org/zap"
	"google.golang.org/grpc/metadata"
)

// TestMainRun runs Main for real: one member in a fresh data directory (Main's DataDir is
// relative); the checks must pass. Then it asks the member Main left running, as each principal,
// why its requests were refused (so that the refusals were the auth checks', not timeouts), and
// as root whether u's permitted writes took effect (so that the history check was not vacuous).
func TestMainRun(t *testing.T) {
	t.Chdir(t.TempDir())
	if r := Main(); r != Ok {
		t.Fatalf("got %v", r)
	}

	lg := zap.NewNop()
	newCli := func(user, pw string) *clientv3.Client {
		cli, err := clientv3.New(clientv3.Config{Endpoints: []string{clientAddr}, Username: user,
			Password: pw, Logger: lg})
		if err != nil {
			t.Fatal(err)
		}
		t.Cleanup(func() { cli.Close() })
		return cli
	}
	// one generous timeout for the whole check (bcrypt is slow under the race detector)
	ctx, cancel := context.WithTimeout(context.Background(), 60*time.Second)
	defer cancel()

	// the refusals, by kind
	u, v, anon := newCli("u", uPw), newCli("v", vPw), newCli("", "")
	want := func(who string, err, kind error) {
		if !errors.Is(err, kind) {
			t.Errorf("%s: got %v, want %v", who, err, kind)
		}
	}
	_, err := u.Put(ctx, "c/u/x", "x")
	want("u outside", err, rpctypes.ErrPermissionDenied)
	_, err = u.Get(ctx, lo, clientv3.WithRange("d"))
	want("u past b", err, rpctypes.ErrPermissionDenied)
	_, err = v.Put(ctx, "a/v/x", "x")
	want("v", err, rpctypes.ErrPermissionDenied)
	_, err = anon.Put(ctx, "a/anon/x", "x")
	want("anon", err, rpctypes.ErrUserEmpty)
	_, err = anon.Put(metadata.AppendToOutgoingContext(ctx, "token", badToken), "a/bad/x", "x")
	want("bad", err, rpctypes.ErrInvalidAuthToken)
	if _, err := clientv3.New(clientv3.Config{Endpoints: []string{clientAddr}, Username: "u",
		Password: "wrong", Logger: lg}); !errors.Is(err, rpctypes.ErrAuthFailed) {
		t.Errorf("a wrong password: got %v", err)
	}

	// u's permitted writes took effect, and only u's
	root := newCli("root", rootPw)
	resp, err := root.Get(ctx, "", clientv3.WithPrefix())
	if err != nil {
		t.Fatal(err)
	}
	seen := map[string]bool{}
	for _, kv := range resp.Kvs {
		seen[string(kv.Key)] = true
	}
	for _, k := range []string{"a/u/0", "a/u/t", "c/u/d", "a/v/d", "c/v/d", "a/anon/d", "a/bad/d",
		"z/end"} {
		if !seen[k] {
			t.Errorf("key %s missing after Main", k)
		}
	}
	for _, k := range []string{"a/u/d", "c/u/0", "a/u/t1", "c/u/t1", "c/u/t2", "c/u/t3",
		"a/v/0", "a/anon/0", "a/bad/0"} {
		if seen[k] {
			t.Errorf("key %s present after Main", k)
		}
	}
	t.Logf("revision %d after Main, keys %d", resp.Header.Revision, len(resp.Kvs))
}

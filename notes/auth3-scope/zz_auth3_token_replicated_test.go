// Copy into server/auth at the etcd fork pin 2eaeb872b (notes/auth3-scope.md, section 2.2) and run
// `GOWORK=off go test ./auth/ -run TestAuth3 -v` in server/: passes (go1.27.1, 2026-11-14).
//
// A simple token is a function of the Authenticate entry: the receiving member's prefix, which the
// entry carries (v3_server.go:865-874), and the consistent index at its apply (apply/backend.go:158),
// which every member has at the same value there, the index of the entry before it (server.go's
// applyEntryNormal sets it to each entry's index when the entry is done; upstream #18437 notes it
// is not the Authenticate entry's own index). So every member that applies the entry assigns the
// same token to the same user (simple_token.go:212-218). This test takes that common index as given
// and checks the rest: the members agree; a member that did not apply the entry (a snapshot
// covered it: Recover keeps the provider's map, store.go:399-418, and the snapshot has no tokens)
// refuses the token; a member restarted on its backend keeps users and the enabled flag, not tokens.
package auth

import (
	"context"
	"errors"
	"testing"
	"time"

	"go.uber.org/zap/zaptest"
	"golang.org/x/crypto/bcrypt"
	"google.golang.org/grpc/metadata"

	"go.etcd.io/etcd/api/v3/v3rpc/rpctypes"
)

// applyAuthenticate is what applierV3backend.Authenticate (server/etcdserver/apply/backend.go)
// does with an InternalAuthenticateRequest{Name, SimpleToken: prefix} at consistent index idx.
func applyAuthenticate(t *testing.T, as AuthStore, name, prefix string, idx uint64) string {
	ctx := context.WithValue(context.WithValue(context.Background(), AuthenticateParamIndex{}, idx),
		AuthenticateParamSimpleTokenPrefix{}, prefix)
	resp, err := as.Authenticate(ctx, name, "")
	if err != nil {
		t.Fatal(err)
	}
	return resp.Token
}

func newMemberStore(t *testing.T, be AuthBackend) AuthStore {
	tp, err := NewTokenProvider(zaptest.NewLogger(t), tokenTypeSimple, dummyIndexWaiter, simpleTokenTTLDefault)
	if err != nil {
		t.Fatal(err)
	}
	return NewAuthStore(zaptest.NewLogger(t), be, tp, bcrypt.MinCost)
}

func infoOf(as AuthStore, token string) (*AuthInfo, error) {
	ctx, cancel := context.WithTimeout(context.Background(), time.Second)
	defer cancel()
	ctx = metadata.NewIncomingContext(ctx, metadata.Pairs(rpctypes.TokenFieldNameGRPC, token))
	return as.AuthInfoFromCtx(ctx)
}

func TestAuth3SimpleTokenReplicated(t *testing.T) {
	// three members, each with its own backend, applying the same log: the set-up, then one
	// Authenticate entry (index 42) proposed by a member whose GenTokenPrefix gave "pfx"
	var members []AuthStore
	for i := 0; i < 3; i++ {
		as := newMemberStore(t, newBackendMock())
		defer as.Close()
		if err := enableAuthAndCreateRoot(as); err != nil {
			t.Fatal(err)
		}
		members = append(members, as)
	}
	var tokens []string
	for _, as := range members[:2] { // the third has not applied index 42 (a snapshot will cover it)
		tokens = append(tokens, applyAuthenticate(t, as, "root", "pfx", 42))
	}
	if tokens[0] != "pfx.42" || tokens[1] != tokens[0] {
		t.Fatalf("tokens differ across members: %q", tokens)
	}
	for i, as := range members[:2] {
		ai, err := infoOf(as, tokens[0])
		if err != nil || ai == nil || ai.Username != "root" {
			t.Fatalf("member %d: info %v, %v; want root", i, ai, err)
		}
	}
	// the member that did not apply the entry refuses the token (its waiter has fired: as after
	// a snapshot past index 42, whose install does not carry the token map)
	if _, err := infoOf(members[2], tokens[0]); !errors.Is(err, ErrInvalidAuthToken) {
		t.Fatalf("member 3: err %v; want ErrInvalidAuthToken", err)
	}
	// a member restarted on its backend: users and auth state survive, tokens do not
	restarted := newMemberStore(t, members[0].(*authStore).be)
	defer restarted.Close()
	if !restarted.IsAuthEnabled() {
		t.Fatal("restarted member: auth not enabled")
	}
	if _, err := infoOf(restarted, tokens[0]); !errors.Is(err, ErrInvalidAuthToken) {
		t.Fatalf("restarted member: err %v; want ErrInvalidAuthToken", err)
	}
}

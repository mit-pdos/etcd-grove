package auth

import (
	"testing"

	"go.uber.org/zap/zaptest"
	"golang.org/x/crypto/bcrypt"
)

// TestNewAuthStoreNilTokenProviderAuthEnabled: NewAuthStore with a nil token
// provider on a backend where auth is enabled panics (etcd's NewServer always
// passes NewTokenProvider's result). Uses newBackendMock, dummyIndexWaiter and
// enableAuthAndCreateRoot from the package's tests.
func TestNewAuthStoreNilTokenProviderAuthEnabled(t *testing.T) {
	tp, err := NewTokenProvider(zaptest.NewLogger(t), tokenTypeSimple, dummyIndexWaiter, simpleTokenTTLDefault)
	if err != nil {
		t.Fatal(err)
	}
	be := newBackendMock()
	as := NewAuthStore(zaptest.NewLogger(t), be, tp, bcrypt.MinCost)
	if err := enableAuthAndCreateRoot(as); err != nil {
		t.Fatal(err)
	}
	as.Close()
	defer func() {
		if r := recover(); r != nil {
			t.Fatalf("NewAuthStore(nil tp) on an auth-enabled backend panicked: %v", r)
		}
	}()
	NewAuthStore(zaptest.NewLogger(t), be, nil, bcrypt.MinCost)
}

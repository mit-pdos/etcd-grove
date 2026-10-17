package transport

import (
	"crypto/tls"
	"os"
	"path/filepath"
	"testing"
)

// A cert file with no PEM block, EmptyCN: does ClientConfig panic (pem.Decode nil)?
func TestReviewEmptyCNMalformedCert(t *testing.T) {
	dir := t.TempDir()
	cert := filepath.Join(dir, "c.pem")
	key := filepath.Join(dir, "k.pem")
	os.WriteFile(cert, []byte("not a pem file"), 0o600)
	os.WriteFile(key, []byte("not a pem file"), 0o600)
	defer func() {
		if r := recover(); r != nil {
			t.Fatalf("panicked: %v", r)
		}
	}()
	info := TLSInfo{CertFile: cert, KeyFile: key, EmptyCN: true}
	_, err := info.ClientConfig()
	t.Logf("default parseFunc: err = %v", err)
	// Only with a parseFunc that accepts the file (test-only field) does the closure see it.
	info.parseFunc = func([]byte, []byte) (tls.Certificate, error) { return tls.Certificate{}, nil }
	_, err = info.ClientConfig()
	t.Logf("accepting parseFunc: err = %v", err)
}

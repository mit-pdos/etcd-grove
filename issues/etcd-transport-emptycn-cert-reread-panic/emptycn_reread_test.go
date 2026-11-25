// Copyright 2026 The etcd Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

package transport

import (
	"crypto/ecdsa"
	"crypto/elliptic"
	"crypto/rand"
	"crypto/x509"
	"crypto/x509/pkix"
	"encoding/pem"
	"math/big"
	"os"
	"path/filepath"
	"sync/atomic"
	"testing"
	"time"
)

// TestClientConfigEmptyCNCertRewritten: ClientConfig with EmptyCN (as `etcd grpc-proxy --cert
// --key` builds it) must return a config or an error, never panic, while the certificate file is
// being replaced in place with a valid certificate (`cp renewed.pem cert.pem`: truncate, then
// write).
func TestClientConfigEmptyCNCertRewritten(t *testing.T) {
	dir := t.TempDir()
	key, err := ecdsa.GenerateKey(elliptic.P256(), rand.Reader)
	if err != nil {
		t.Fatal(err)
	}
	tmpl := &x509.Certificate{SerialNumber: big.NewInt(1), Subject: pkix.Name{},
		NotBefore: time.Now(), NotAfter: time.Now().Add(time.Hour)}
	der, err := x509.CreateCertificate(rand.Reader, tmpl, tmpl, &key.PublicKey, key)
	if err != nil {
		t.Fatal(err)
	}
	certPEM := pem.EncodeToMemory(&pem.Block{Type: "CERTIFICATE", Bytes: der})
	kder, err := x509.MarshalECPrivateKey(key)
	if err != nil {
		t.Fatal(err)
	}
	keyFile := filepath.Join(dir, "key.pem")
	if err := os.WriteFile(keyFile, pem.EncodeToMemory(&pem.Block{Type: "EC PRIVATE KEY", Bytes: kder}), 0o600); err != nil {
		t.Fatal(err)
	}
	certFile := filepath.Join(dir, "cert.pem")
	if err := os.WriteFile(certFile, certPEM, 0o600); err != nil {
		t.Fatal(err)
	}

	var stop atomic.Bool
	done := make(chan struct{})
	go func() {
		defer close(done)
		for !stop.Load() {
			os.WriteFile(certFile, certPEM, 0o600) // the same valid certificate, rewritten in place
		}
	}()
	defer func() { stop.Store(true); <-done }()

	info := TLSInfo{CertFile: certFile, KeyFile: keyFile, EmptyCN: true}
	deadline := time.Now().Add(10 * time.Second)
	for time.Now().Before(deadline) {
		func() {
			defer func() {
				if r := recover(); r != nil {
					t.Fatalf("ClientConfig panicked while the certificate file was rewritten: %v", r)
				}
			}()
			info.ClientConfig() // an error (a read of the empty file) is fine
		}()
	}
}

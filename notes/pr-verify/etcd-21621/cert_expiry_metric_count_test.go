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

package embed

// What etcd_server_client_cert_expiration_seconds counts (etcd-io/etcd#21621): one sample per
// gRPC connection when the client URL serves gRPC only (gRPC owns the TLS handshake and calls
// the stats handler's HandleConn(ConnBegin) once per connection), but one sample per RPC on the
// default client URL, which serves gRPC and HTTP on one port: there gRPC is served through
// grpc.Server.ServeHTTP, which calls HandleConn(ConnBegin) for every HTTP/2 request, i.e. every
// unary RPC and every stream.

import (
	"context"
	"crypto/rand"
	"crypto/rsa"
	"crypto/x509"
	"crypto/x509/pkix"
	"encoding/pem"
	"fmt"
	"math/big"
	"net"
	"net/url"
	"os"
	"path/filepath"
	"testing"
	"time"

	"github.com/prometheus/client_golang/prometheus"
	"github.com/stretchr/testify/require"

	"go.etcd.io/etcd/client/pkg/v3/transport"
	clientv3 "go.etcd.io/etcd/client/v3"
)

func certExpirySampleCount(t *testing.T) uint64 {
	mfs, err := prometheus.DefaultGatherer.Gather()
	require.NoError(t, err)
	for _, mf := range mfs {
		if mf.GetName() == "etcd_server_client_cert_expiration_seconds" {
			return mf.GetMetric()[0].GetHistogram().GetSampleCount()
		}
	}
	return 0
}

func writePEM(t *testing.T, path, typ string, der []byte) {
	f, err := os.Create(path)
	require.NoError(t, err)
	require.NoError(t, pem.Encode(f, &pem.Block{Type: typ, Bytes: der}))
	require.NoError(t, f.Close())
}

// genCerts writes ca.crt, server.{crt,key} (for 127.0.0.1) and client.{crt,key} into dir.
func genCerts(t *testing.T, dir string) {
	caKey, err := rsa.GenerateKey(rand.Reader, 2048)
	require.NoError(t, err)
	caTmpl := &x509.Certificate{
		SerialNumber: big.NewInt(1), Subject: pkix.Name{CommonName: "ca"},
		NotBefore: time.Now().Add(-time.Hour), NotAfter: time.Now().Add(24 * time.Hour),
		IsCA: true, BasicConstraintsValid: true,
		KeyUsage: x509.KeyUsageCertSign | x509.KeyUsageDigitalSignature,
	}
	caDER, err := x509.CreateCertificate(rand.Reader, caTmpl, caTmpl, &caKey.PublicKey, caKey)
	require.NoError(t, err)
	writePEM(t, filepath.Join(dir, "ca.crt"), "CERTIFICATE", caDER)
	ca, err := x509.ParseCertificate(caDER)
	require.NoError(t, err)
	for i, name := range []string{"server", "client"} {
		key, err := rsa.GenerateKey(rand.Reader, 2048)
		require.NoError(t, err)
		tmpl := &x509.Certificate{
			SerialNumber: big.NewInt(int64(i + 2)), Subject: pkix.Name{CommonName: name},
			NotBefore: time.Now().Add(-time.Hour), NotAfter: time.Now().Add(2 * time.Hour),
			KeyUsage:    x509.KeyUsageDigitalSignature | x509.KeyUsageKeyEncipherment,
			ExtKeyUsage: []x509.ExtKeyUsage{x509.ExtKeyUsageServerAuth, x509.ExtKeyUsageClientAuth},
			IPAddresses: []net.IP{net.IPv4(127, 0, 0, 1)},
		}
		der, err := x509.CreateCertificate(rand.Reader, tmpl, ca, &key.PublicKey, caKey)
		require.NoError(t, err)
		writePEM(t, filepath.Join(dir, name+".crt"), "CERTIFICATE", der)
		writePEM(t, filepath.Join(dir, name+".key"), "RSA PRIVATE KEY", x509.MarshalPKCS1PrivateKey(key))
	}
}

func freeURL(t *testing.T, scheme string) url.URL {
	l, err := net.Listen("tcp", "127.0.0.1:0")
	require.NoError(t, err)
	defer l.Close()
	return url.URL{Scheme: scheme, Host: l.Addr().String()}
}

// countSamples starts a member with client mTLS, sends rpcs Puts over one client connection, and
// returns how many samples the cert-expiry histogram gained.
func countSamples(t *testing.T, splitHTTP bool, rpcs int) uint64 {
	dir := t.TempDir()
	genCerts(t, dir)
	cfg := NewConfig()
	cfg.Dir = filepath.Join(dir, "data")
	cfg.LogLevel = "error"
	curl := freeURL(t, "https")
	purl := freeURL(t, "http")
	cfg.ListenClientUrls, cfg.AdvertiseClientUrls = []url.URL{curl}, []url.URL{curl}
	cfg.ListenPeerUrls, cfg.AdvertisePeerUrls = []url.URL{purl}, []url.URL{purl}
	cfg.InitialCluster = fmt.Sprintf("%s=%s", cfg.Name, purl.String())
	if splitHTTP {
		cfg.ListenClientHttpUrls = []url.URL{freeURL(t, "https")}
	}
	cfg.ClientTLSInfo = transport.TLSInfo{
		CertFile: filepath.Join(dir, "server.crt"), KeyFile: filepath.Join(dir, "server.key"),
		TrustedCAFile: filepath.Join(dir, "ca.crt"), ClientCertAuth: true,
	}
	e, err := StartEtcd(cfg)
	require.NoError(t, err)
	defer e.Close()
	select {
	case <-e.Server.ReadyNotify():
	case <-time.After(20 * time.Second):
		t.Fatal("server not ready")
	}
	ctls, err := transport.TLSInfo{
		CertFile: filepath.Join(dir, "client.crt"), KeyFile: filepath.Join(dir, "client.key"),
		TrustedCAFile: filepath.Join(dir, "ca.crt"),
	}.ClientConfig()
	require.NoError(t, err)
	before := certExpirySampleCount(t)
	cli, err := clientv3.New(clientv3.Config{Endpoints: []string{curl.Host}, TLS: ctls, DialTimeout: 5 * time.Second})
	require.NoError(t, err)
	defer cli.Close()
	for i := 0; i < rpcs; i++ {
		ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
		_, err := cli.Put(ctx, "k", "v")
		cancel()
		require.NoError(t, err)
	}
	return certExpirySampleCount(t) - before
}

func TestClientCertExpirationSamplesPerConnectionOrPerRPC(t *testing.T) {
	const rpcs = 10
	grpcOnly := countSamples(t, true, rpcs)
	shared := countSamples(t, false, rpcs)
	t.Logf("%d Puts over one client connection: %d sample(s) on a gRPC-only client URL, %d on the default (gRPC+HTTP) client URL", rpcs, grpcOnly, shared)
	require.Equal(t, uint64(1), grpcOnly, "gRPC-only client URL: one sample per connection")
	require.GreaterOrEqual(t, shared, uint64(rpcs), "default client URL: one sample per RPC")
}

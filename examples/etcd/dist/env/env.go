// Package env is what every machine program of etcd_dist_safe does to its environment before
// anything reads it (notes/etcd-dist-plan.md, §4 and Q10): the server's and the clients' Main call
// ClearProxy first.
package env

import "os"

// ClearProxy makes the process proxy-free and ETCD_VERIFY-free. Go's http.ProxyFromEnvironment
// (rafthttp's transports, the lease and member requests between members) and grpc's proxy dialer
// read the proxy variables once, at their first use, which is after this; with non-loopback
// addresses that is what lets the theorem do without a proxy premise (etcd-grove#24: the net/http
// model treats a non-nil proxy as NotModelled). It also clears ETCD_VERIFY, so that verifyEnvOff
// becomes a fact of the program rather than a premise.
// TODO(model): needs specs of os.Unsetenv and of the environment as machine-local state
// (notes/perennial-changes.md).
func ClearProxy() {
	os.Unsetenv("HTTP_PROXY")
	os.Unsetenv("HTTPS_PROXY")
	os.Unsetenv("NO_PROXY")
	os.Unsetenv("http_proxy")
	os.Unsetenv("https_proxy")
	os.Unsetenv("no_proxy")
	os.Unsetenv("ETCD_VERIFY")
}

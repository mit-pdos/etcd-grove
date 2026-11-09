package clientv3client

import (
	"crypto/tls"

	"go.etcd.io/etcd/client/pkg/v3/transport"
	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/client/v3/kubernetes"
	"go.uber.org/zap"
)

// REQ clientv3client/new-tls: Kubernetes' client construction: a TLS configuration from the
// certificate files (nil when none is given), then kubernetes.New; a client or an error, never a
// panic.
// Users: Kubernetes' storagebackend/factory/etcd3.go:286-352 (newETCD3Client).
// Assumes: eps serve the cluster; the certificate's principal is known (tlsPrincipal, 2e: none
// without --client-cert-auth).
// Specs: Transport.TLSInfo.ClientConfig.spec (tlsCfgOk), Kubernetes.New.spec (cfgOk,
// cfgPrincipal_tls / cfgPrincipal_none).
func ReqNewTLS(eps []string, certFile, keyFile, caFile string, lg *zap.Logger) *kubernetes.Client {
	info := transport.TLSInfo{CertFile: certFile, KeyFile: keyFile, TrustedCAFile: caFile}
	var tlsConfig *tls.Config
	var err error
	if certFile != "" || keyFile != "" || caFile != "" {
		tlsConfig, err = info.ClientConfig()
		if err != nil {
			return nil
		}
	}
	kc, err := kubernetes.New(clientv3.Config{Endpoints: eps, TLS: tlsConfig, Logger: lg})
	if err != nil {
		return nil
	}
	return kc
}

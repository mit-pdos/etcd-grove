# etcd-io/etcd#21621: what the report relies on

| File | What it shows | Runs against | Command |
|---|---|---|---|
| `cert_expiry_metric_count_test.go` | `etcd_server_client_cert_expiration_seconds` counts once per gRPC connection on a gRPC-only client URL (`ListenClientHttpUrls` set), but once per RPC (each unary call, each stream) on the default client URL, where gRPC and HTTP share the port and gRPC is served through `grpc.Server.ServeHTTP`: 10 Puts over one client connection give 1 sample in the first case, 11 in the second | the PR head `83a3bbc4a` (etcd-io/etcd, package `server/embed`) | `cp cert_expiry_metric_count_test.go <etcd checkout at the PR head>/server/embed/ && cd <checkout>/server/embed && GOTOOLCHAIN=go1.26.4 go test -count=1 -run TestClientCertExpirationSamplesPerConnectionOrPerRPC -v .` |
| `cert_expiry_metric_count_test.log` | the output of the test above (server error logs filtered out) | same | same |

The fork branch with the PR applied is `mit-pdos/etcd-grove` branch `pr-etcd-21621-goose-lean`
(the fork's `goose-lean` at `09669450f` plus the PR's non-test changes, applied cleanly).

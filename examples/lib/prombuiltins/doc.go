// Package prombuiltins holds the evidence for the one trusted declaration of prometheus's client_golang
// in this repository: its package `init()`, which TrustedCode/github_com/prometheus/client_golang/prometheus.lean
// replaces by the state the built-in process and Go collectors leave in the default registry (constants
// `seed.descIDs`, `seed.dims`, `seed.collectorIDs`; notes/prom-registry.md, route (b)).
//
// Its test, TestSeedConstants, reads those constants from the Lean file and compares them with the maps
// of client_golang v1.24.1's real default registry, on the pinned toolchain (etc/goose.py's GO_TOOLCHAIN:
// go_info's descriptor carries the runtime's version):
//
//	cd examples && GOTOOLCHAIN=go1.27.3 go test ./lib/prombuiltins/
package prombuiltins

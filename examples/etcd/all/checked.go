package etcdall

import "github.com/mit-pdos/etcd-grove/examples/lib/cluster3"

// mulBelow reports whether a*b < bound, for a, b >= 0 and bound > 0, without overflowing.
func mulBelow(a int, b int, bound int) bool {
	return b == 0 || a <= (bound-1)/b
}

// ParamsOk reports whether Main's parameters are in the ranges its proof covers: the cluster sizes
// (k1 at most 1000, k2..k4 at most 300, k5 from 3 to 300), and each workload's client count below
// 2^31 with its total operation count below 2^60 (KV) or 2^62 (the watch and cache workloads).
func ParamsOk(k1 uint64, clients int, ops int, nw int, nops int, cnw int, cnops int, k2 uint64,
	k3 uint64, k4 uint64, k5 uint64) bool {
	return 1 <= k1 && k1 <= 1000 &&
		0 <= clients && clients < 1<<31 && 0 <= ops && mulBelow(clients, ops, 1<<60) &&
		0 <= nw && nw < 1<<31 && 0 <= nops && mulBelow(nw, nops, 1<<62) &&
		0 <= cnw && cnw < 1<<31 && 0 <= cnops && mulBelow(cnw, cnops, 1<<62) &&
		1 <= k2 && k2 <= 300 && 1 <= k3 && k3 <= 300 && 1 <= k4 && k4 <= 300 &&
		3 <= k5 && k5 <= 300
}

// MainChecked is Main on parameters it checks first (ParamsOk; out of range it returns without
// running anything), with fault schedules of n1 and n2 steps that it draws itself
// (cluster3.RandomSchedule).
func MainChecked(k1 uint64, clients int, ops int, n1 int, nw int, nops int, n2 int, cnw int,
	cnops int, k2 uint64, k3 uint64, k4 uint64, k5 uint64) {
	if !ParamsOk(k1, clients, ops, nw, nops, cnw, cnops, k2, k3, k4, k5) {
		return
	}
	Main(k1, clients, ops, cluster3.RandomSchedule(n1), nw, nops, cluster3.RandomSchedule(n2), cnw,
		cnops, k2, k3, k4, k5)
}

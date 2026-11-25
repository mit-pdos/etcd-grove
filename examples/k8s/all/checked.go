package k8sall

import "github.com/mit-pdos/etcd-grove/examples/lib/cluster3"

// mulBelow reports whether a*b < bound, for a, b >= 0 and bound > 0, without overflowing.
func mulBelow(a int, b int, bound int) bool {
	return b == 0 || a <= (bound-1)/b
}

// ParamsOk reports whether Main's parameters are in the ranges its proof covers: k1 from 1 to 1000
// and k2 from 1 to 600 members; clients and watchers nonnegative, fewer than 2^31 together; ops and
// wops nonnegative, with clients*ops + watchers*wops below 2^60 (the second product is checked
// against what the first leaves, which is computed only once the first is known below 2^60).
func ParamsOk(k1 uint64, clients int, ops int, watchers int, wops int, k2 uint64) bool {
	return 1 <= k1 && k1 <= 1000 && 1 <= k2 && k2 <= 600 && 0 <= clients && 0 <= watchers &&
		clients < 1<<31 && watchers < 1<<31-clients && 0 <= ops && 0 <= wops &&
		mulBelow(clients, ops, 1<<60) && mulBelow(watchers, wops, 1<<60-clients*ops)
}

// MainChecked is Main on parameters it checks first (ParamsOk; out of range it returns without
// running anything), with fault schedules of n1 and n2 steps that it draws itself
// (cluster3.RandomSchedule).
func MainChecked(k1 uint64, clients int, ops int, watchers int, wops int, n1 int, k2 uint64, n2 int) {
	if !ParamsOk(k1, clients, ops, watchers, wops, k2) {
		return
	}
	Main(k1, clients, ops, watchers, wops, cluster3.RandomSchedule(n1), k2, cluster3.RandomSchedule(n2))
}

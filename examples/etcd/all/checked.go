package etcdall

// ParamsOk reports whether Main's parameter is in the range its proof covers: restartN's member
// count k5 from 3 to 300.
func ParamsOk(k5 uint64) bool {
	return 3 <= k5 && k5 <= 300
}

// MainChecked is Main on a parameter it checks first (ParamsOk; out of range it returns without
// running anything).
func MainChecked(k5 uint64) {
	if !ParamsOk(k5) {
		return
	}
	Main(k5)
}

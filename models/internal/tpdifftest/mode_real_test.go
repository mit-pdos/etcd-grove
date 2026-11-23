//go:build !tpmodel

package tpdifftest_test

// model: whether the tests run against the models (run.sh: a -modfile replacing the three modules
// by models/gods, models/uuid and models/concurrent-map, tag tpmodel) or against the real modules
// (go.mod).
const model = false

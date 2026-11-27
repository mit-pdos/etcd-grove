// Package idissuecrash attacks the trusted model of idutil's Generator.Next
// over the issue record (notes/axiom-review/idissue-crash.md).
//
// Two shapes, each panicking in Go when two generators of one prefix issue
// one id, and each provable from the model (its `assume` excludes the
// collision):
//
//   - Twice: one process starts two generators of one prefix at one
//     millisecond (a program restriction the model does not state: etcd
//     starts one per run).
//   - Restart: an id issued before a machine's restart, kept in a file, and
//     the restarted run's generator started with its clock behind (an
//     environment assumption: the clock does not step back).
package idissuecrash

import (
	"os"
	"strconv"
	"time"

	"go.etcd.io/etcd/pkg/v3/idutil"
)

// Twice panics if two generators of prefix 7 started at now issue one id.
func Twice(now time.Time) {
	a := idutil.NewGenerator(7, now)
	b := idutil.NewGenerator(7, now)
	if a.Next() == b.Next() {
		panic("reissued id")
	}
}

// Restart is a process's boot: on the first run it records its first id in
// path; on a later run (after a crash) it panics if its first id is the
// recorded one.
func Restart(path string, now time.Time) {
	g := idutil.NewGenerator(7, now)
	id := g.Next()
	b, err := os.ReadFile(path)
	if err != nil {
		if werr := os.WriteFile(path, []byte(strconv.FormatUint(id, 10)), 0o644); werr != nil {
			return
		}
		return
	}
	old, perr := strconv.ParseUint(string(b), 10, 64)
	if perr == nil && old == id {
		panic("reissued id after restart")
	}
}

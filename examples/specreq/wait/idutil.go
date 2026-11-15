package wait

import (
	"time"

	"go.etcd.io/etcd/pkg/v3/idutil"
)

// REQ wait/ids-distinct: a run's ids are distinct and never 0 (the bootstrap conf changes' id).
// Users: v3_server.go:1068 (request ids: the wait registry's keys), read.go:150 (read contexts:
// raft's readCtx_register needs fresh ones), v3_server.go:438 (lease ids).
// Assumes: memberID is the member's prefix from the cluster's allocation (distinct across members,
// not 0: idSpace_alloc; nonissues/etcd-request-id-member-prefix.md,
// etcd-request-id-zero-bootstrap-confchange.md), one generator per run (idPrefixes_take).
// Specs: IdUtil.NewGenerator.spec, IdUtil.Generator.Next.spec; laws: idFresh_excl,
// idFresh_ne_zero.
func ReqIdsDistinct(memberID uint16) {
	g := idutil.NewGenerator(memberID, time.Now())
	a := g.Next()
	b := g.Next()
	if a == b {
		panic("ids: duplicate")
	}
	if a == 0 || b == 0 {
		panic("ids: zero")
	}
}

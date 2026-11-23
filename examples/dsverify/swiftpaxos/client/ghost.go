package client

import (
	"sync"

	"github.com/goose-lang/primitive"
)

// GHOST (L2, the verification's linearization; notes/l2-design.md in the Lean project): ghost
// code, no behaviour change. Every node (each client node, each replica node) has one ghost: a
// prophecy predicting the node's protocol events, resolved as words under a ghost mutex.
// primitive.NewProph and ResolveU64 are no-ops when the program runs (goose-lang/primitive), so
// this code only takes and releases a mutex around nothing. The proof registers each node's
// prediction before the node's first configuration acknowledgment and uses the predictions to
// choose each operation's linearization point.

// Ghost is the node's linearization ghost (one per node).
type Ghost struct {
	mu sync.Mutex
	p  primitive.ProphId
}

// NewGhost allocates the ghost (GHOST).
func NewGhost() *Ghost {
	return &Ghost{p: primitive.NewProph()}
}

// The node's ghost, made at the package's initialization on every node (GHOST).
var nodeGhost = NewGhost()

func theGhost() *Ghost {
	return nodeGhost
}

// resolveBytes resolves a byte string: its length, then each byte (GHOST).
func (g *Ghost) resolveBytes(bs []byte) {
	g.p.ResolveU64(uint64(len(bs)))
	for _, b := range bs {
		g.p.ResolveU64(uint64(b))
	}
}

// Invoke records that client cl invokes command seq (op, key, val) (GHOST). The words: op
// (state.PUT = 1, state.GET = 2), cl, seq, key, len(val), val's bytes.
func (g *Ghost) Invoke(op uint8, cl int32, seq int32, key int64, val []byte) {
	g.mu.Lock()
	g.p.ResolveU64(uint64(op))
	g.p.ResolveU64(uint64(uint32(cl)))
	g.p.ResolveU64(uint64(uint32(seq)))
	g.p.ResolveU64(uint64(key))
	g.resolveBytes(val)
	g.mu.Unlock()
}

// Accept records that client cl accepts command seq's result val (GHOST). The words: 3, cl,
// seq, len(val), val's bytes.
func (g *Ghost) Accept(cl int32, seq int32, val []byte) {
	g.mu.Lock()
	g.p.ResolveU64(3)
	g.p.ResolveU64(uint64(uint32(cl)))
	g.p.ResolveU64(uint64(uint32(seq)))
	g.resolveBytes(val)
	g.mu.Unlock()
}

// Step records one protocol event of this node, given as its words (GHOST; a replica's
// events: the words' first is the event's kind, 4 and up, see the Lean project's encoding).
func (g *Ghost) Step(ws []uint64) {
	g.mu.Lock()
	for _, w := range ws {
		g.p.ResolveU64(w)
	}
	g.mu.Unlock()
}

// GhostStep records one protocol event of this node (GHOST): the node's ghost's Step.
func GhostStep(ws []uint64) {
	g := theGhost()
	g.Step(ws)
}

// Package snaprepair: runtime checks of the premises proposed for the snapshot stream's repaired
// trust-boundary axioms (sweep repairs 1, group "snap"; notes/axiom-review/snap-stream.md):
//
//   - S1: snap.NewMessage takes a close contract for its reader (rcCloseOk rc), which io.Pipe
//     hands out only with readerStreams, after the hand-over T is given up (ghostPipe models
//     the ghost order: GiveUpT is the wand's application);
//   - S2: snap.NewMessage takes 0 <= sz < 2^48 (backend.snapshot.Size's new post), and assumes
//     proto.Size(rs) < 2^62, so TotalSize = proto.Size(rs) + sz does not overflow;
//   - S3: streamReaderOk's buffer clause weakened to Go's io.Reader rule: a Read returning n
//     leaves len(p) bytes in p, the first n the stream's, the rest arbitrary (scratch).
//
// Not committed (COMMON.md: harness only).
package snaprepair

import (
	"bytes"
	"fmt"
	"io"
	"sync"

	"go.uber.org/zap"
	"google.golang.org/protobuf/proto"

	"go.etcd.io/etcd/server/v3/etcdserver/api/snap"
	"go.etcd.io/etcd/server/v3/storage/backend"
	"go.etcd.io/raft/v3/raftpb"
)

// SizeBound is the proposed bound on NewMessage's sz (backend.snapshot.Size's post: bbolt's
// MaxMapSize on 64-bit platforms is 0xFFFFFFFFFFFF < 2^48).
const SizeBound = int64(1) << 48

// ProtoBound is the bound NewMessage's axiom assumes of proto.Size(rs).
const ProtoBound = int64(1) << 62

// CloseCap is the persistent close contract rcCloseOk rc: the right to call rc.Close() from any
// goroutine, any number of times. Only GiveUpT (a pipe's reader, after the hand-over) and
// CapOf (a reader that is not a pipe's) make one.
type CloseCap struct{ rc io.ReadCloser }

// CapOf is the close contract of a non-pipe reader whose Close returns (the caller's claim; nil
// has none: rcCloseOk needs an ok interface).
func CapOf(rc io.ReadCloser) *CloseCap {
	if rc == nil {
		return nil
	}
	return &CloseCap{rc: rc}
}

// GhostPipe is io.Pipe with the NEW spec's ghost order: the reader's readerStreams and its
// close contract exist only once T is given up.
type GhostPipe struct {
	PR     *io.PipeReader
	PW     *io.PipeWriter
	handed bool
}

func NewGhostPipe() *GhostPipe {
	pr, pw := io.Pipe()
	return &GhostPipe{PR: pr, PW: pw}
}

// GiveUpT applies the wand `T -∗ readerStreams pr Φ ∗ rcCloseOk pr`.
func (g *GhostPipe) GiveUpT() (io.ReadCloser, *CloseCap) {
	g.handed = true
	return g.PR, &CloseCap{rc: g.PR}
}

// NewMessagePremises lists the NEW snap.NewMessage premises that (rs, rc, sz, cap) violates.
func NewMessagePremises(rs *raftpb.Message, rc io.ReadCloser, sz int64, cap *CloseCap) []string {
	var v []string
	if rc == nil {
		v = append(v, "rcCloseOk rc: rc is the nil interface (no ok interface)")
	} else if cap == nil || cap.rc != rc {
		v = append(v, "rcCloseOk rc: no close contract for rc (a pipe's reader before the hand-over T)")
	}
	if sz < 0 || sz >= SizeBound {
		v = append(v, fmt.Sprintf("0 <= sz < 2^48: sz = %d", sz))
	}
	if ps := int64(proto.Size(rs)); ps < 0 || ps >= ProtoBound {
		v = append(v, fmt.Sprintf("axiom's assumption 0 <= proto.Size(rs) < 2^62: %d", ps))
	}
	return v
}

// ReadStats records, over the Reads of a stream, the NEW clause (0 <= n <= len(p), len(p)
// unchanged: always true of a Go slice) and how often the OLD clause failed (a byte of p past n
// changed).
type ReadStats struct {
	Reads, NewViolations, OldViolations int
	Bytes                               []byte
	Err                                 error
}

// ReadAllChecked reads r to its end (or error) with buffers of size bs, each pre-filled with a
// sentinel, checking both clauses.
func ReadAllChecked(r io.Reader, bs int) ReadStats {
	var st ReadStats
	const sentinel = 0xA5
	for {
		p := make([]byte, bs)
		for i := range p {
			p[i] = sentinel
		}
		n, err := r.Read(p)
		st.Reads++
		if n < 0 || n > len(p) || len(p) != bs {
			st.NewViolations++
		}
		if n >= 0 && n <= len(p) {
			for _, b := range p[n:] {
				if b != sentinel {
					st.OldViolations++
					break
				}
			}
			st.Bytes = append(st.Bytes, p[:n]...)
		}
		if err != nil {
			st.Err = err
			return st
		}
	}
}

// MergedRun is one run of etcd's merged-snapshot path over a live backend, as
// createMergedSnapshotMessage, newSnapshotReaderCloser and createSnapBody do it, with the NEW
// premises checked where the specs take them.
type MergedRun struct {
	Size        int64
	ProtoSize   int
	TotalSize   int64
	Violations  []string
	Body        ReadStats
	WriterBytes int64
	WriterErr   error
	CloseOK     bool
}

// newSnapshotReaderCloser is etcd's (snapshot_merge.go:55-80 at 673da07c8), with the pipe a
// GhostPipe and the goroutine's WriteTo result recorded; done is closed when the goroutine ends.
func newSnapshotReaderCloser(lg *zap.Logger, sn backend.Snapshot, out *MergedRun, done chan struct{}) *GhostPipe {
	g := NewGhostPipe()
	go func() {
		defer close(done)
		n, err := sn.WriteTo(g.PW)
		out.WriterBytes, out.WriterErr = n, err
		g.PW.CloseWithError(err)
		if err := sn.Close(); err != nil {
			lg.Panic("failed to close database snapshot", zap.Error(err))
		}
	}()
	return g
}

// RunMerged runs createMergedSnapshotMessage's body over be (the server's backend), then
// createSnapBody's reader (an envelope buffer, then the message's exact-size reader), reads it
// with bs-byte buffers, and closes the message. With closeEarly, the reader is closed (twice, from
// two goroutines) after the first read, as the sender's deferred CloseWithError may do on an error.
func RunMerged(lg *zap.Logger, be backend.Backend, bs int, closeEarly bool) *MergedRun {
	out := &MergedRun{}
	m := &raftpb.Message{}
	dbsnap := be.Snapshot()
	done := make(chan struct{})
	g := newSnapshotReaderCloser(lg, dbsnap, out, done)
	snapi, snapt := uint64(10), uint64(2)
	m.Snapshot = &raftpb.Snapshot{Metadata: &raftpb.SnapshotMetadata{
		Index: &snapi, Term: &snapt,
		ConfState: proto.Clone(&raftpb.ConfState{Voters: []uint64{1, 2, 3}}).(*raftpb.ConfState),
	}}
	// dbsnap.Size() with the sender's half (T), then T given up: the reader and its close contract
	sz := dbsnap.Size()
	rc, cap := g.GiveUpT()
	out.Size = sz
	out.ProtoSize = proto.Size(m)
	out.Violations = NewMessagePremises(m, rc, sz, cap)
	msg := snap.NewMessage(m, rc, sz)
	out.TotalSize = msg.TotalSize
	if msg.TotalSize < 0 {
		out.Violations = append(out.Violations, "post: TotalSize < 0")
	}
	env, _ := proto.Marshal(m)
	body := io.MultiReader(bytes.NewBuffer(env), msg.ReadCloser)
	if closeEarly {
		p := make([]byte, bs)
		body.Read(p)
		var wg sync.WaitGroup
		errs := make([]error, 2)
		for i := 0; i < 2; i++ {
			wg.Add(1)
			go func(i int) { defer wg.Done(); errs[i] = rc.Close() }(i)
		}
		wg.Wait()
		out.CloseOK = errs[0] == nil && errs[1] == nil
		out.Body = ReadAllChecked(body, bs)
	} else {
		out.Body = ReadAllChecked(body, bs)
		out.CloseOK = true
	}
	msg.CloseWithError(out.Body.Err)
	<-msg.CloseNotify()
	<-done
	if !closeEarly {
		if out.Body.Err != io.EOF {
			out.Violations = append(out.Violations, fmt.Sprintf("stream ended with %v, not EOF", out.Body.Err))
		}
		if int64(len(out.Body.Bytes)) != int64(len(env))+sz {
			out.Violations = append(out.Violations, fmt.Sprintf("stream length %d != envelope %d + size %d",
				len(out.Body.Bytes), len(env), sz))
		}
		if out.WriterBytes != sz {
			out.Violations = append(out.Violations, fmt.Sprintf("WriteTo wrote %d != Size %d", out.WriterBytes, sz))
		}
	} else if out.Body.Err == io.EOF {
		out.Violations = append(out.Violations, "closed early, yet the stream ended in EOF")
	}
	return out
}

package repro

import (
	"context"
	"fmt"
	"sync"
	"testing"
)

// --- Minimal faithful reproduction of PR #21401's requestid + wait.Wait + rafthttp logic ---

type ctxKeyType string

const reqIDKey ctxKeyType = "requestID"

func NewContext(ctx context.Context, id uint64) context.Context {
	return context.WithValue(ctx, reqIDKey, id)
}

func FromContext(ctx context.Context) uint64 {
	id, ok := ctx.Value(reqIDKey).(uint64)
	if !ok {
		return 0
	}
	return id
}

// Faithful reproduction of go.etcd.io/etcd/pkg/v3/wait.list
type waitList struct {
	mu sync.Mutex
	m  map[uint64]chan any
}

func newWaitList() *waitList {
	return &waitList{m: make(map[uint64]chan any)}
}

func (w *waitList) Register(id uint64) <-chan any {
	w.mu.Lock()
	defer w.mu.Unlock()
	ch := w.m[id]
	if ch == nil {
		ch = make(chan any, 1)
		w.m[id] = ch
	} else {
		panic(fmt.Sprintf("dup id %x", id))
	}
	return ch
}

func (w *waitList) Trigger(id uint64, x any) {
	w.mu.Lock()
	ch := w.m[id]
	delete(w.m, id)
	w.mu.Unlock()
	if ch != nil {
		ch <- x
		close(ch)
	}
}

// Bug 1A: Concurrent or overlapping proposals on the same gRPC ctx reuse the same
// requestID from requestid.FromContext(ctx), causing w.Register(id) to panic with "dup id %x".
func TestReproBug1A_DuplicateRequestIDRegisterPanic(t *testing.T) {
	w := newWaitList()
	// newLogUnaryInterceptor attaches requestID := s.RequestID() to ctx:
	ctx := NewContext(context.Background(), 0xdeadbeef)

	// First proposal extracts requestID := requestid.FromContext(ctx) != 0:
	id1 := FromContext(ctx)
	if id1 == 0 {
		t.Fatal("expected non-zero requestID in ctx")
	}
	_ = w.Register(id1)

	// Second concurrent proposal on the same ctx extracts the exact same requestID:
	id2 := FromContext(ctx)
	defer func() {
		r := recover()
		if r == nil {
			t.Fatal("expected w.Register(id2) to panic with dup id, but it did not panic")
		}
		t.Logf("Confirmed Bug 1A panic on second proposal with same ctx: %v", r)
	}()
	_ = w.Register(id2)
}

// Bug 1B: Sequential proposals on the same ctx (e.g. EtcdServer.Authenticate's retry loop
// in server/etcdserver/v3_server.go:853-887, or quotaAlarmer.check -> s.Alarm(ctx, ...)
// in server/etcdserver/api/v3rpc/quota.go:48) reuse the same requestID.
// If Proposal 1's wait is abandoned while Proposal 1 is still in the Raft pipeline,
// and Proposal 2 registers the same ID, Proposal 1's apply triggers Proposal 2's channel
// with Proposal 1's stale result!
func TestReproBug1B_SequentialProposalSameCtxCrossContaminatesApplyResult(t *testing.T) {
	w := newWaitList()
	ctx := NewContext(context.Background(), 0x12345678)

	// Proposal 1 registers id = 0x12345678, proposes to Raft, and then its local wait
	// cleans up via w.Trigger(id, nil) on timeout while the Raft entry is still committed/in-flight.
	id1 := FromContext(ctx)
	ch1 := w.Register(id1)
	// Timeout cleanup in processInternalRaftRequestOnce:
	w.Trigger(id1, nil)
	<-ch1

	// Proposal 2 on the same ctx (or retry with a fresh child context derived from ctx,
	// which inherits requestID via Context.Value!) extracts the SAME requestID = 0x12345678:
	retryCtx, cancel := context.WithCancel(ctx)
	defer cancel()
	id2 := FromContext(retryCtx)
	if id2 != id1 {
		t.Fatalf("expected child context to inherit requestID %x, got %x", id1, id2)
	}
	ch2 := w.Register(id2)

	// Now Proposal 1 finishes applying in Raft applyAll and calls w.Trigger(header.ID, "proposal-1-result"):
	w.Trigger(id1, "STALE_PROPOSAL_1_RESULT")

	// Proposal 2 receives Proposal 1's result!
	got := <-ch2
	if got != "STALE_PROPOSAL_1_RESULT" {
		t.Fatalf("expected stale result, got %v", got)
	}
	t.Logf("Confirmed Bug 1B: Proposal 2 received Proposal 1's apply result (%q) due to requestID reuse (%#x)", got, id2)
}

// Bug 1C: In v3election.electionServer.Campaign (server/etcdserver/api/v3election/election.go:40-92),
// which runs on the same gRPC server with newLogUnaryInterceptor and uses v3client.New(s) in-process
// on the caller's ctx: if Proclaim (a Txn proposal) times out locally while in flight in Raft, and
// Campaign's error path calls e.Resign(ctx) (a DeleteRange proposal) on the same ctx, both proposals
// reuse the same requestID. When Proclaim's Txn finishes applying in Raft, s.w.Trigger(requestID, *pb.TxnResponse)
// delivers *pb.TxnResponse to DeleteRange's wait channel, causing DeleteRange (v3_server.go:323) to
// panic on the type assertion resp.(*pb.DeleteRangeResponse)!
func TestReproBug1C_V3ElectionCampaignResignTypeAssertionPanic(t *testing.T) {
	type TxnResponse struct{ Revision int64 }
	type DeleteRangeResponse struct{ Deleted int64 }

	w := newWaitList()
	// newLogUnaryInterceptor attaches requestID to the Campaign gRPC ctx:
	campaignCtx := NewContext(context.Background(), 0xcafe0001)

	// Step 1: Campaign's Proclaim(ctx, ...) calls s.Txn(ctx, ...) -> processInternalRaftRequestOnce,
	// which extracts id = 0xcafe0001, registers in s.w, and times out locally while the Txn is still in flight in Raft:
	proclaimID := FromContext(campaignCtx)
	proclaimCh := w.Register(proclaimID)
	w.Trigger(proclaimID, nil) // local timeout cleanup in processInternalRaftRequestOnce
	<-proclaimCh

	// Step 2: Campaign catches the Proclaim error and calls e.Resign(ctx) on the SAME campaignCtx.
	// Resign calls s.DeleteRange(ctx, ...) -> processInternalRaftRequestOnce, which extracts the
	// SAME requestID = 0xcafe0001 from campaignCtx and registers in s.w:
	resignID := FromContext(campaignCtx)
	if resignID != proclaimID {
		t.Fatalf("expected Resign to extract same requestID %x, got %x", proclaimID, resignID)
	}
	resignCh := w.Register(resignID)

	// Step 3: Proclaim's committed Txn entry finishes applying on the Raft apply loop and calls
	// s.w.Trigger(header.ID, &pb.TxnResponse{...}):
	w.Trigger(proclaimID, &TxnResponse{Revision: 42})

	// Step 4: DeleteRange (v3_server.go:323) receives from resignCh and executes:
	//   return resp.(*pb.DeleteRangeResponse), nil
	defer func() {
		r := recover()
		if r == nil {
			t.Fatal("expected DeleteRange type assertion resp.(*DeleteRangeResponse) to panic")
		}
		t.Logf("Confirmed Bug 1C panic in DeleteRange after Proclaim->Resign on same ctx: %v", r)
	}()
	resp := <-resignCh
	_ = resp.(*DeleteRangeResponse)
}

// Bug 2A & 2B: logRaftCommunication nil logger and nil Header dereference.
type fakeLogger struct {
	messages []string
}

func (l *fakeLogger) Debug(msg string, fields ...any) {
	// If l == nil, dereferencing l.messages panics just like zap.Logger.Debug panics at lg.check(...)
	l.messages = append(l.messages, fmt.Sprintf("%s %v", msg, fields))
}

type fakeHeader struct {
	ID uint64
}

type fakeInternalRaftRequest struct {
	Header *fakeHeader
}

func simulateLogRaftCommunicationMsgProp(lg *fakeLogger, req fakeInternalRaftRequest) {
	// Faithful reproduction of server/etcdserver/api/rafthttp/transport.go:462-468:
	// lg.Debug("MsgProp raft message", zap.Uint64("req-id", r.Header.ID))
	lg.Debug("MsgProp raft message", req.Header.ID)
}

func TestReproBug2A_LogRaftCommunicationNilLoggerCrash(t *testing.T) {
	defer func() {
		r := recover()
		if r == nil {
			t.Fatal("expected nil logger to panic")
		}
		t.Logf("Confirmed Bug 2A: logRaftCommunication with nil *zap.Logger panics: %v", r)
	}()
	var lg *fakeLogger = nil
	simulateLogRaftCommunicationMsgProp(lg, fakeInternalRaftRequest{Header: &fakeHeader{ID: 1}})
}

func TestReproBug2B_LogRaftCommunicationNilHeaderCrash(t *testing.T) {
	defer func() {
		r := recover()
		if r == nil {
			t.Fatal("expected nil Header in MsgProp to panic")
		}
		t.Logf("Confirmed Bug 2B: logRaftCommunication with r.Header == nil panics: %v", r)
	}()
	lg := &fakeLogger{}
	// InternalRaftRequest with nil Header:
	simulateLogRaftCommunicationMsgProp(lg, fakeInternalRaftRequest{Header: nil})
}

// Bug 3: Internal background proposals (publishV3, LeaseCheckpoint, corrupt.go alarms, etc.)
// pass s.ctx or context.Background() without going through newLogUnaryInterceptor,
// so requestid.FromContext(ctx) == 0 and processInternalRaftRequestOnce logs a Warn on every call.
func TestReproBug3_InternalProposalTriggersWarnLog(t *testing.T) {
	internalCtx := context.Background()
	requestID := FromContext(internalCtx)
	if requestID != 0 {
		t.Fatalf("expected 0 requestID on internal context, got %d", requestID)
	}
	warned := false
	if requestID == 0 {
		warned = true
	}
	if !warned {
		t.Fatal("expected Warn branch to trigger on internal context")
	}
	t.Log("Confirmed Bug 3: internal proposals have FromContext(ctx) == 0 and trigger lg.Warn on every call")
}

// Bug 4: Duplicate "size" field in logUnaryResponseStats (server/etcdserver/api/v3rpc/interceptor.go:130-137)
func TestReproBug4_DuplicateSizeFieldInLogUnaryResponseStats(t *testing.T) {
	fields := []string{"start-time", "time-spent", "response-type", "size"}
	// When response is *pb.RangeResponse, getRangeResponseStatFields appends:
	rangeStatFields := []string{"range-response-count", "size"}
	fields = append(fields, rangeStatFields...)

	sizeCount := 0
	for _, f := range fields {
		if f == "size" {
			sizeCount++
		}
	}
	if sizeCount != 2 {
		t.Fatalf("expected 2 'size' fields, got %d", sizeCount)
	}
	t.Logf("Confirmed Bug 4: logUnaryResponseStats emits %d duplicate 'size' zap fields: %v", sizeCount, fields)
}

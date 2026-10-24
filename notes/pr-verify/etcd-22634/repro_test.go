package etcd22634repro

import (
	"fmt"
	"strings"
	"testing"

	"go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/pkg/v3/wait"
	"go.etcd.io/etcd/server/v3/etcdserver/api/membership"
	"go.etcd.io/etcd/server/v3/etcdserver/apply"
	"go.etcd.io/etcd/server/v3/storage/wal"
	"go.etcd.io/raft/v3/raftpb"
	"go.uber.org/zap"
	"google.golang.org/protobuf/encoding/protowire"
	"google.golang.org/protobuf/proto"
)

type recordingUberApplier struct {
	got *etcdserverpb.InternalRaftRequest
}

func (rec *recordingUberApplier) Apply(r *apply.InternalRaftRequestWrapper, _ membership.ShouldApplyV3) *apply.Result {
	rec.got = r.InternalRaftRequest
	return &apply.Result{}
}

// legacyRequestBytes matches the helper in server/etcdserver/apply/apply_test.go (etcd#22634).
func legacyRequestBytes(id uint64, method, p, val string) []byte {
	var b []byte
	b = protowire.AppendTag(b, 1, protowire.VarintType)
	b = protowire.AppendVarint(b, id)
	b = protowire.AppendTag(b, 2, protowire.BytesType)
	b = protowire.AppendString(b, method)
	b = protowire.AppendTag(b, 3, protowire.BytesType)
	b = protowire.AppendString(b, p)
	b = protowire.AppendTag(b, 4, protowire.BytesType)
	b = protowire.AppendString(b, val)
	return b
}

// Finding 1: memberAttributePathRegexp in server/etcdserver/apply/legacy_request.go:32
// is unanchored (`regexp.MustCompile(path.Join(membership.StoreMembersPrefix, "[[:xdigit:]]{1,16}", "attributes"))`).
// Combined with `membership.MustParseMemberIDFromKey(lg, path.Dir(r.Path))` (which parses `path.Base(path.Dir(r.Path))`),
// disallowed v2 PUT paths containing `/0/members/<hex>/attributes` as a substring are either:
//   (1a) silently accepted as a ClusterMemberAttrSetRequest for `<hex>` (when `<hex>` is still `path.Base(path.Dir(r.Path))`),
//   (1b) silently accepted with the WRONG Member_ID (when two extra segments follow and the parent segment is hex), or
//   (1c) crash with an unrelated strconv.ParseUint panic inside MustParseMemberIDFromKey instead of the
//        "detected disallowed v2 WAL for stage --v2-deprecation=write-only" panic.
func TestFinding1_UnanchoredMemberAttributePathRegexp(t *testing.T) {
	lg := zap.NewExample()
	w := wait.New()
	valJSON := `{"name":"node1","clientURLs":["http://127.0.0.1:2379"]}`

	t.Run("1a_PrefixAndSuffixAcceptedAsMemberAttrSet", func(t *testing.T) {
		for _, badPath := range []string{
			"/prefix/0/members/1a2b/attributes",
			"/0/members/1a2b/attributes_extra",
		} {
			rec := &recordingUberApplier{}
			ent := &raftpb.Entry{
				Data: legacyRequestBytes(101, "PUT", badPath, valJSON),
			}
			_, id := apply.Apply(lg, ent, rec, w, membership.ApplyBoth)
			if rec.got == nil || rec.got.ClusterMemberAttrSet == nil {
				t.Fatalf("expected %q to be converted to ClusterMemberAttrSet, got %+v", badPath, rec.got)
			}
			t.Logf("disallowed path %q was silently accepted by apply.Apply (id=%d) -> ClusterMemberAttrSet{Member_ID: 0x%x, Name: %q}",
				badPath, id, rec.got.ClusterMemberAttrSet.Member_ID, rec.got.ClusterMemberAttrSet.MemberAttributes.Name)
		}
	})

	t.Run("1b_TrailingSegmentsParseWrongMemberID", func(t *testing.T) {
		// Contains `/0/members/1a2b/attributes`, followed by `/deadbeef/subkey`.
		// `path.Dir(r.Path)` is `/0/members/1a2b/attributes/deadbeef`, whose `path.Base` is `deadbeef`!
		badPath := "/0/members/1a2b/attributes/deadbeef/subkey"
		rec := &recordingUberApplier{}
		ent := &raftpb.Entry{
			Data: legacyRequestBytes(102, "PUT", badPath, valJSON),
		}
		_, id := apply.Apply(lg, ent, rec, w, membership.ApplyBoth)
		if rec.got == nil || rec.got.ClusterMemberAttrSet == nil {
			t.Fatalf("expected %q to be converted to ClusterMemberAttrSet, got %+v", badPath, rec.got)
		}
		gotMemberID := rec.got.ClusterMemberAttrSet.Member_ID
		if gotMemberID != 0xdeadbeef {
			t.Fatalf("expected Member_ID 0xdeadbeef, got 0x%x", gotMemberID)
		}
		t.Logf("disallowed path %q was silently accepted (id=%d) with WRONG Member_ID=0x%x (instead of 0x1a2b)!",
			badPath, id, gotMemberID)
	})

	t.Run("1c_SingleTrailingSegmentPanicsInParseUint", func(t *testing.T) {
		badPath := "/0/members/1a2b/attributes/extra"
		rec := &recordingUberApplier{}
		ent := &raftpb.Entry{
			Data: legacyRequestBytes(103, "PUT", badPath, valJSON),
		}
		defer func() {
			r := recover()
			if r == nil {
				t.Fatalf("expected panic for %q", badPath)
			}
			msg := fmt.Sprint(r)
			if strings.Contains(msg, "detected disallowed v2 WAL") {
				t.Fatalf("expected MustParseMemberIDFromKey panic, got %q", msg)
			}
			t.Logf("disallowed path %q bypassed the v2 WAL guard and panicked inside MustParseMemberIDFromKey: %s",
				badPath, msg)
		}()
		apply.Apply(lg, ent, rec, w, membership.ApplyBoth)
	})
}

// Finding 2: Wire-format overlap between legacy v2 `Request` and v3 `InternalRaftRequest`
// (`reserved 2; reserved "v2";` in raft_internal.proto:40).
// Because `proto.Unmarshal` silently skips reserved field 2 (`Method` in bare v2 `Request`, or `V2`
// in an `InternalRaftRequest`), wire encodings that only populate tag 1 (`ID`) and tag 2 (`Method` / `V2`),
// or also tags 3 (`Path: ""`) and 4 (`Val: ""`), succeed in `proto.Unmarshal(e.Data, &raftReq)` with `err == nil`
// and bypass the `if err != nil` legacy fallback in `apply.Apply`!
func TestFinding2_ProtoUnmarshalWireOverlapBypass(t *testing.T) {
	lg := zap.NewExample()
	w := wait.New()

	t.Run("2a_LegacyRequestBytesWithEmptyPathAndVal", func(t *testing.T) {
		// Using the PR's own legacyRequestBytes helper with a disallowed method ("DELETE") and empty path/val:
		// Tag 1 (varint 42) -> InternalRaftRequest.ID = 42
		// Tag 2 (bytes "DELETE") -> skipped as unknown field (reserved 2)
		// Tag 3 (bytes "") -> empty InternalRaftRequest.Range = &RangeRequest{}
		// Tag 4 (bytes "") -> empty InternalRaftRequest.Put = &PutRequest{}
		data := legacyRequestBytes(42, "DELETE", "", "")
		var probe etcdserverpb.InternalRaftRequest
		if err := proto.Unmarshal(data, &probe); err != nil {
			t.Fatalf("unexpected proto.Unmarshal error: %v", err)
		}

		// Register waiter for ID 42 so apply.Apply dispatches to UberAppliereven when Range != nil.
		_ = w.Register(42)
		rec := &recordingUberApplier{}
		ent := &raftpb.Entry{Data: data}
		_, id := apply.Apply(lg, ent, rec, w, membership.ApplyBoth)
		if rec.got == nil {
			t.Fatalf("expected apply.Apply to dispatch to UberApplier")
		}
		t.Logf("legacyRequestBytes(42, \"DELETE\", \"\", \"\") succeeded in proto.Unmarshal (err == nil), bypassed legacy v2 check, and dispatched as v3 InternalRaftRequest{ID: %d, Range: %+v, Put: %+v}!",
			id, rec.got.Range, rec.got.Put)
	})

	t.Run("2b_InternalRaftRequestWrappingV2InField2", func(t *testing.T) {
		// An InternalRaftRequest that wrapped a v2 Request in field 2 (`V2`, handled in etcd 3.6 via `if raftReq.V2 != nil`):
		// Tag 100 (Header: &RequestHeader{ID: 77})
		// Tag 2 (V2: legacyRequestBytes(77, "PUT", "/0/version", "3.6.0"))
		hdrBytes, err := proto.Marshal(&etcdserverpb.RequestHeader{ID: 77})
		if err != nil {
			t.Fatal(err)
		}
		var data []byte
		data = protowire.AppendTag(data, 100, protowire.BytesType)
		data = protowire.AppendBytes(data, hdrBytes)
		data = protowire.AppendTag(data, 2, protowire.BytesType)
		data = protowire.AppendBytes(data, legacyRequestBytes(77, "PUT", "/0/version", "3.6.0"))

		rec := &recordingUberApplier{}
		ent := &raftpb.Entry{Data: data}
		_, id := apply.Apply(lg, ent, rec, w, membership.ApplyBoth)
		if rec.got == nil {
			t.Fatalf("expected apply.Apply to dispatch to UberApplier")
		}
		if rec.got.ClusterVersionSet != nil {
			t.Fatalf("expected ClusterVersionSet to be nil because field 2 was dropped as unknown")
		}
		t.Logf("InternalRaftRequest with field 2 (V2) succeeded in proto.Unmarshal (err == nil), dropped field 2, and dispatched empty InternalRaftRequest (Header.ID=%d, ClusterVersionSet=%v)!",
			id, rec.got.ClusterVersionSet)
	})
}

// Finding 3: `wal.MinimalEtcdVersion` (`server/storage/wal/version.go:108`) was also stripped of
// its v2 `Request` fallback in commit 073d46a558de, and was NOT updated by etcd#22634.
// Calling `wal.MinimalEtcdVersion` on WAL entries containing the very legacy v2 `/0/version` or
// `/0/members/<id>/attributes` entries that etcd#22634 replays causes `MinimalEtcdVersion` to panic!
func TestFinding3_WALMinimalEtcdVersionPanicsOnLegacyV2Entries(t *testing.T) {
	typ := raftpb.EntryNormal
	idx := uint64(1)
	term := uint64(1)
	ents := []*raftpb.Entry{
		{
			Index: &idx,
			Term:  &term,
			Type:  &typ,
			Data:  legacyRequestBytes(1, "PUT", "/0/version", "3.5.0"),
		},
	}
	defer func() {
		r := recover()
		if r == nil {
			t.Fatalf("expected wal.MinimalEtcdVersion to panic on legacy v2 entry")
		}
		t.Logf("wal.MinimalEtcdVersion panicked on valid legacy v2 `/0/version` entry: %v", r)
	}()
	ver := wal.MinimalEtcdVersion(ents)
	t.Fatalf("expected panic, got version %v", ver)
}

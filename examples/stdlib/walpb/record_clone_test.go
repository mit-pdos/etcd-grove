package walpb

import (
	"testing"

	"go.etcd.io/etcd/server/v3/storage/wal/walpb"
	"google.golang.org/protobuf/proto"
)

// ClonePb at Record (enrolled by pbRecordC_reg) claims c' = c: Clone must keep a non-nil empty Data,
// and Unmarshal must give back a non-nil empty Data for its encoding.
func TestRecordEmptyData(t *testing.T) {
	m := &walpb.Record{Data: []byte{}}
	c := proto.Clone(m).(*walpb.Record)
	if c.Data == nil {
		t.Fatalf("Clone made Data nil")
	}
	b, _ := proto.Marshal(m)
	var d walpb.Record
	if err := proto.Unmarshal(b, &d); err != nil || d.Data == nil {
		t.Fatalf("Unmarshal %x: Data nil (%v)", b, err)
	}
	t.Logf("encoding %x; Clone and Unmarshal keep non-nil empty Data", b)
}

// Package jsonunmarshalalias is the Go counterexample to the trust-boundary axiom
// encoding.json.Unmarshal.wp_proof as it stood until 2026-11-20 (Spec/encoding/json/Unmarshal.lean,
// notes/axiom-review/json-unmarshal-alias.md): for any *ConfigChangeContext p ↦ v it gave back full
// ownership of the decoded PeerURLs (and ClientURLs) slice, "fresh". encoding/json decodes a JSON
// array into the field's existing slice, reusing its backing array while its capacity lasts
// (encoding/json/decode.go:553-556), so a v whose PeerURLs the caller still owns comes back with the
// decoded slice aliased to it: two full points-tos of one cell, from which the proof derives False.
// Latent: both callers (EtcdServer.applyConfChange, RaftCluster.ValidateConfigurationChange) decode
// into new(membership.ConfigChangeContext), whose slices are nil; the fixed spec requires that.
// Tests only, no Goose project.
package jsonunmarshalalias

import (
	"encoding/json"
	"testing"

	"go.etcd.io/etcd/server/v3/etcdserver/api/membership"
)

func TestUnmarshalReusesPeerURLs(t *testing.T) {
	owned := []string{"http://old:2380"}
	cc := new(membership.ConfigChangeContext)
	cc.PeerURLs = owned
	data := []byte(`{"id":1,"peerURLs":["http://new:2380"],"isPromote":false}`)
	if err := json.Unmarshal(data, cc); err != nil {
		t.Fatal(err)
	}
	if &cc.PeerURLs[0] != &owned[0] {
		t.Fatalf("decoded PeerURLs is fresh: not a counterexample")
	}
	if owned[0] != "http://new:2380" {
		t.Fatalf("the caller's slice was not overwritten: %q", owned[0])
	}
}

func TestUnmarshalIntoNewIsFresh(t *testing.T) {
	cc := new(membership.ConfigChangeContext)
	data := []byte(`{"id":1,"peerURLs":["http://new:2380"],"clientURLs":["http://c:2379"]}`)
	if err := json.Unmarshal(data, cc); err != nil {
		t.Fatal(err)
	}
	if len(cc.PeerURLs) != 1 || len(cc.ClientURLs) != 1 {
		t.Fatalf("decode: %+v", cc)
	}
}

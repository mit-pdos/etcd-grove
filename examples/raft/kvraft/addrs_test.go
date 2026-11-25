package kvraft

import (
	"reflect"
	"testing"
)

// TestAddrOk checks AddrOk against the net extension's addrOk (GooseLang/Ext/Net/Deploy.lean) on
// its edge cases.
func TestAddrOk(t *testing.T) {
	for a, want := range map[string]bool{
		"10.0.0.1:7001":         true,
		"127.1.2.3:20000":       true,
		"1.0.0.0:1":             true,
		"223.255.255.255:65535": true,
		"10.0.0.1:32767":        true,
		"10.0.0.1:61000":        true,
		"10.0.0.1:32768":        false, // ephemeral range
		"10.0.0.1:60999":        false,
		"10.0.0.1:0":            false,
		"10.0.0.1:65536":        false,
		"0.1.2.3:7001":          false, // 0.0.0.0/8
		"224.0.0.1:7001":        false, // multicast and above
		"10.0.0.256:7001":       false,
		"10.0.0.01:7001":        false, // leading zero
		"10.0.0.1:07001":        false,
		"10.0.0:7001":           false,
		"10.0.0.1.2:7001":       false,
		"10.0.0.1":              false,
		"10.0.0.1:7001:1":       false,
		"10.0.0.1:":             false,
		":7001":                 false,
		"localhost:7001":        false,
		"10.0.0.1:+7001":        false,
		"":                      false,
	} {
		if got := AddrOk(a); got != want {
			t.Errorf("AddrOk(%q) = %v, want %v", a, got, want)
		}
	}
}

// TestSplitAddrs checks that SplitAddrs reads back JoinAddrs.
func TestSplitAddrs(t *testing.T) {
	for _, as := range [][]string{{"10.0.0.1:7001"}, {"10.0.0.1:7001", "10.0.0.2:7001", "10.0.0.3:7001"}} {
		if got := SplitAddrs(JoinAddrs(as)); !reflect.DeepEqual(got, as) {
			t.Errorf("SplitAddrs(JoinAddrs(%v)) = %v", as, got)
		}
	}
	if !ValidAddrs([]string{"10.0.0.1:7001", "10.0.0.2:7001"}, 2) ||
		ValidAddrs([]string{"10.0.0.1:7001", "10.0.0.1:7001"}, 1) ||
		ValidAddrs([]string{"10.0.0.1:7001"}, 2) || ValidAddrs([]string{"10.0.0.1:7001"}, 0) {
		t.Error("ValidAddrs")
	}
}

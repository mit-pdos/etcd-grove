// Command antcheck checks a stream of rawnode reports with the Go transcription of
// EtcdBinding.tla and prints the verdict as antithesis-fm/tracekit/check/streamcheck.py does
// (ACCEPTED n, REJECTED k, VIOLATED k names, ERROR ...).
//
//	antcheck [-cfg EtcdBindingEmpty.cfg] stream.ndjson
//
// -cfg names one of the binding's configurations (third_party/etcd-raft-formalized/spec/
// EtcdBinding*.cfg). Exit status: 0 accepted, 1 rejected or violated, 2 error.
package main

import (
	"flag"
	"fmt"
	"os"
	"strconv"

	"github.com/mit-pdos/etcd-grove/examples/raft/antithesis/check"
	"github.com/mit-pdos/etcd-grove/examples/raft/antithesis/check/ndjson"
)

func servers(n int) check.Set {
	var s check.Set
	for i := 1; i <= n; i++ {
		s = check.SetAdd(s, "raft"+strconv.Itoa(i))
	}
	return s
}

var configs = map[string]*check.Config{
	"EtcdBinding.cfg":       {Server: servers(3), InitVoters: servers(3), Bootstrapped: true},
	"EtcdBindingEmpty.cfg":  {Server: servers(3), InitVoters: servers(3), Bootstrapped: false},
	"EtcdBinding5.cfg":      {Server: servers(5), InitVoters: servers(5), Bootstrapped: true},
	"EtcdBinding5Empty.cfg": {Server: servers(5), InitVoters: servers(5), Bootstrapped: false},
	"EtcdBindingM.cfg":      {Server: servers(5), InitVoters: servers(3), Bootstrapped: true},
	"EtcdBindingMEmpty.cfg": {Server: servers(5), InitVoters: servers(3), Bootstrapped: false},
}

func main() {
	cfgName := flag.String("cfg", "EtcdBindingEmpty.cfg", "the binding's configuration")
	flag.Parse()
	cfg := configs[*cfgName]
	if cfg == nil || flag.NArg() != 1 {
		fmt.Fprintln(os.Stderr, "usage: antcheck [-cfg EtcdBinding*.cfg] stream.ndjson")
		os.Exit(2)
	}
	evs, err := ndjson.ReadFile(flag.Arg(0))
	if err != nil {
		fmt.Printf("ERROR %v\n", err)
		os.Exit(2)
	}
	v := check.Check(cfg, evs)
	fmt.Println(v)
	switch v.Kind {
	case check.Accepted:
		os.Exit(0)
	case check.Error:
		os.Exit(2)
	}
	os.Exit(1)
}

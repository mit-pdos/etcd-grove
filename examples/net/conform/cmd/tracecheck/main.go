// Command tracecheck checks that the conformance trace directories under ROOT (or in the
// sample archives FILE.tar.gz) are well formed, and prints what they hold
// (examples/net/conform/README.md; package tracecheck). It exits 1 on a problem.
//
//	go run ./net/conform/cmd/tracecheck [-lenient] ROOT|FILE.tar.gz...
package main

import (
	"flag"
	"fmt"
	"os"
	"strings"

	"github.com/mit-pdos/etcd-grove/examples/net/conform/tracecheck"
)

func main() {
	lenient := flag.Bool("lenient", false, "allow unfinished calls in processes no driver saw end (the semantics tests' children)")
	flag.Parse()
	st := tracecheck.NewStats()
	nerr := 0
	report := func(d *tracecheck.Dir) {
		for _, e := range tracecheck.Check(d, st, tracecheck.Options{Lenient: *lenient}) {
			nerr++
			fmt.Fprintln(os.Stderr, e)
		}
	}
	for _, a := range flag.Args() {
		if strings.HasSuffix(a, ".tar.gz") {
			dirs, err := tracecheck.LoadTarGz(a)
			if err != nil {
				fmt.Fprintln(os.Stderr, err)
				os.Exit(1)
			}
			for _, d := range dirs {
				report(d)
			}
			continue
		}
		dns, err := tracecheck.Dirs(a)
		if err != nil {
			fmt.Fprintln(os.Stderr, err)
			os.Exit(1)
		}
		for _, dn := range dns {
			d, err := tracecheck.Load(dn)
			if err != nil {
				fmt.Fprintln(os.Stderr, err)
				nerr++
				continue
			}
			report(d)
		}
	}
	fmt.Print(st)
	if nerr > 0 {
		fmt.Fprintf(os.Stderr, "%d problems\n", nerr)
		os.Exit(1)
	}
}

// fs-v2-r6 e2e: the "application" whose boot reads its records after a crash. Page 0 of each file
// was written by one 4096-byte pwrite at a time (tearw write), all its bytes equal. Boot checks,
// as a recovering application checks its records, the weakest thing the Fs v2 semantics promises
// of such a page after a crash: each 512-byte sector holds a version it had (here: is all one
// byte; NoTearCrash and the device's atomic sectors). It panics on a sector holding two values
// (a record checksummed within one sector would fail), and also reports a page whose sectors
// differ (allowed by the semantics: sectors are independent).
//
//	boot DIR N
package main

import (
	"fmt"
	"os"
	"strconv"
)

func main() {
	n, _ := strconv.Atoi(os.Args[2])
	for j := 0; j < n; j++ {
		p := fmt.Sprintf("%s/f%d", os.Args[1], j)
		b, err := os.ReadFile(p)
		if err != nil {
			panic(err)
		}
		if len(b) != 4096 {
			panic(fmt.Sprintf("%s: size %d", p, len(b)))
		}
		for s := 0; s < 4096; s += 512 {
			for i := s; i < s+512; i++ {
				if b[i] != b[s] {
					panic(fmt.Sprintf("%s: torn sector %d: byte %d = %#02x, byte %d = %#02x", p, s/512, s, b[s], i, b[i]))
				}
			}
		}
		same := true
		for i := range b {
			same = same && b[i] == b[0]
		}
		if same {
			fmt.Printf("%s: record %#02x ok\n", p, b[0])
		} else {
			fmt.Printf("%s: sectors ok, page mixed (allowed)\n", p)
		}
	}
}

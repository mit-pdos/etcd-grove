// RemoveAll of a directory of more than 1024 entries, racing a create: the created
// entry X can be removed while an entry present before RemoveAll began still exists.
package main

import (
	"fmt"
	"os"
	"sync"
)

func run(base string, n int) (violated bool, detail string) {
	d := base + "/D"
	os.RemoveAll(d)
	if err := os.Mkdir(d, 0o755); err != nil {
		panic(err)
	}
	orig := make([]string, n)
	for i := 0; i < n; i++ {
		orig[i] = fmt.Sprintf("%s/f%04d", d, i)
		f, err := os.Create(orig[i])
		if err != nil {
			panic(err)
		}
		f.Close()
	}
	var wg sync.WaitGroup
	wg.Add(1)
	var res string
	var bad bool
	go func() { // T2: wait for a removal, create X, then watch
		defer wg.Done()
		for {
			gone := false
			for _, p := range orig {
				if _, err := os.Stat(p); err != nil {
					gone = true
					break
				}
			}
			if gone {
				break
			}
		}
		x := d + "/X"
		f, err := os.Create(x)
		if err != nil {
			res = "create X: " + err.Error()
			return
		}
		f.Close()
		// survivors: originals present after X was created
		var surv []string
		for _, p := range orig {
			if _, err := os.Stat(p); err == nil {
				surv = append(surv, p)
			}
		}
		for {
			if _, err := os.Stat(x); err != nil {
				for _, s := range surv {
					if _, err := os.Stat(s); err == nil {
						bad = true
						res = fmt.Sprintf("X gone while original %s (one of %d survivors) present", s, len(surv))
						return
					}
				}
				res = fmt.Sprintf("X gone after all %d survivors", len(surv))
				return
			}
		}
	}()
	err := os.RemoveAll(d)
	wg.Wait()
	return bad, fmt.Sprintf("RemoveAll=%v; %s", err, res)
}

func main() {
	base := os.Args[1]
	hits := 0
	for i := 0; i < 20; i++ {
		v, s := run(base, 1100)
		if v {
			hits++
		}
		if i < 5 || v && hits <= 3 {
			fmt.Println(i, v, s)
		}
	}
	fmt.Printf("violations: %d/20\n", hits)
}

// Runs etcd's permSlice sort (Less on Key only) as upstream RoleGrantPermission applies it,
// printing the stored order after each grant, and one direct sort of a crafted slice.
package main

import (
	"bytes"
	"fmt"
	"runtime"
	"sort"
	"strings"
)

type Permission struct{ Key, RangeEnd []byte }

type permSlice []*Permission

func (p permSlice) Len() int           { return len(p) }
func (p permSlice) Less(i, j int) bool { return bytes.Compare(p[i].Key, p[j].Key) < 0 }
func (p permSlice) Swap(i, j int)      { p[i], p[j] = p[j], p[i] }

// upstream etcd's RoleGrantPermission at 4e090c033abc, server/auth/store.go:825-842
func grant(perms []*Permission, k, e string) []*Permission {
	idx := sort.Search(len(perms), func(i int) bool { return bytes.Compare(perms[i].Key, []byte(k)) >= 0 })
	if idx < len(perms) && bytes.Equal(perms[idx].Key, []byte(k)) && bytes.Equal(perms[idx].RangeEnd, []byte(e)) {
		return perms
	}
	perms = append(perms, &Permission{[]byte(k), []byte(e)})
	sort.Sort(permSlice(perms))
	return perms
}

// the verified fork's RoleGrantPermission (8c28a4296, server/auth/store.go:827-845): replace
// every permission on the range, append, sort.
func grantFork(perms []*Permission, k, e string) []*Permission {
	var kept []*Permission
	for _, p := range perms {
		if !bytes.Equal(p.Key, []byte(k)) || !bytes.Equal(p.RangeEnd, []byte(e)) {
			kept = append(kept, p)
		}
	}
	kept = append(kept, &Permission{[]byte(k), []byte(e)})
	sort.Sort(permSlice(kept))
	return kept
}

func show(p []*Permission) string {
	var s []string
	for _, x := range p {
		s = append(s, "["+string(x.Key)+","+string(x.RangeEnd)+")")
	}
	return strings.Join(s, "")
}

func main() {
	fmt.Println(runtime.Version())
	// A role's grants, one by one (the administrator's sequence): keys a..f, then a second
	// range on key "c", then more.
	seq := [][2]string{{"a", "b"}, {"b", "c"}, {"d", "e"}, {"e", "f"}, {"f", "g"}, {"g", "h"},
		{"c", "e"}, {"c", "d"}, {"h", "i"}, {"c", "z"}, {"i", "j"}, {"j", "k"}, {"k", "l"}, {"c", "y"}}
	var perms []*Permission
	for _, g := range seq {
		perms = grant(perms, g[0], g[1])
		fmt.Printf("grant [%s,%s) n=%d: %s\n", g[0], g[1], len(perms), show(perms))
	}
	// A direct sort of 16 permissions, several with equal keys.
	var d []*Permission
	for i, k := range []string{"m", "c", "c", "a", "c", "b", "c", "x", "c", "d", "c", "e", "c", "f", "c", "g"} {
		d = append(d, &Permission{[]byte(k), []byte(fmt.Sprintf("%c%02d", k[0]+1, i))})
	}
	sort.Sort(permSlice(d))
	fmt.Println("direct n=16:", show(d))
	// Pseudo-random grant sequences (a fixed LCG, the same under every Go version).
	x := uint64(1)
	rnd := func(n int) int { x = x*6364136223846793005 + 1442695040888963407; return int((x >> 33) % uint64(n)) }
	for seed := 0; seed < 300; seed++ {
		var p, f []*Permission
		n := 13 + rnd(10)
		for i := 0; i < n; i++ {
			k := string(rune('a' + rnd(6)))
			e := string(rune(k[0] + 1 + byte(rnd(5))))
			p = grant(p, k, e)
			f = grantFork(f, k, e)
		}
		fmt.Printf("fork %d: %s\n", seed, show(f))
		fmt.Printf("seq %d: %s\n", seed, show(p))
		_ = p
	}
}

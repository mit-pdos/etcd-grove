// Upstream etcd's RoleGrantPermission (4e090c033abc, server/auth/store.go:825-842) with permission
// types, over pseudo-random grant sequences: prints, per sequence, the stored record and which
// single keys a user with the role may write (checkKeyPoint: any WRITE/READWRITE range holding it).
package main

import (
	"bytes"
	"fmt"
	"runtime"
	"sort"
	"strings"
)

type Permission struct {
	Key, RangeEnd []byte
	T             string // "R", "W", "RW"
}

type permSlice []*Permission

func (p permSlice) Len() int           { return len(p) }
func (p permSlice) Less(i, j int) bool { return bytes.Compare(p[i].Key, p[j].Key) < 0 }
func (p permSlice) Swap(i, j int)      { p[i], p[j] = p[j], p[i] }

func grant(perms []*Permission, k, e, t string) []*Permission {
	idx := sort.Search(len(perms), func(i int) bool { return bytes.Compare(perms[i].Key, []byte(k)) >= 0 })
	if idx < len(perms) && bytes.Equal(perms[idx].Key, []byte(k)) && bytes.Equal(perms[idx].RangeEnd, []byte(e)) {
		perms[idx].T = t
		return perms
	}
	perms = append(perms, &Permission{[]byte(k), []byte(e), t})
	sort.Sort(permSlice(perms))
	return perms
}

func show(p []*Permission) string {
	var s []string
	for _, x := range p {
		s = append(s, "["+string(x.Key)+","+string(x.RangeEnd)+")"+x.T)
	}
	return strings.Join(s, "")
}

func writable(p []*Permission) string {
	s := ""
	for c := byte('a'); c <= 'k'; c++ {
		ok := false
		for _, x := range p {
			if x.T != "R" && bytes.Compare(x.Key, []byte{c}) <= 0 && bytes.Compare([]byte{c}, x.RangeEnd) < 0 {
				ok = true
			}
		}
		if ok {
			s += string(c)
		}
	}
	return s
}

func main() {
	fmt.Println(runtime.Version())
	x := uint64(7)
	rnd := func(n int) int { x = x*6364136223846793005 + 1442695040888963407; return int((x >> 33) % uint64(n)) }
	types := []string{"R", "RW"}
	for seed := 0; seed < 300; seed++ {
		var p []*Permission
		var ops []string
		n := 13 + rnd(10)
		for i := 0; i < n; i++ {
			k := string(rune('a' + rnd(6)))
			e := string(rune(k[0] + 1 + byte(rnd(3))))
			t := types[rnd(2)]
			ops = append(ops, "["+k+","+e+")"+t)
			p = grant(p, k, e, t)
		}
		fmt.Printf("seq %d grants %s\n  record %s\n  writable %s\n", seed, strings.Join(ops, ""), show(p), writable(p))
	}
}

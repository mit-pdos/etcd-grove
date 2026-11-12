// p1mix: does any byte-wise mix of two meta-slot states minibolt can leave in one slot between
// two syncs validate, other than the two states themselves? (P1, BootP1.lean.)
//
// The slot states minibolt's BootMinibolt can produce (minibolt.go): zeros (a new file; init's
// first WriteAt), meta(0) and meta(1) (init), and meta(t) for t >= 2 (commit t: root = t+2,
// pgid = t+3, freelist 2, pageSize 4096, flags 0). Slot t%2 holds meta(t-2) when commit t writes
// it; init writes meta(j) over zeros in slot j. Each write is followed by an fdatasync before the
// next write to the slot, so between two syncs a slot byte has at most two candidates (a leftover
// torn mix of them from an earlier crash is itself such a mix). Up to txid 2^18 (1 GiB / 4 KiB).
//
// For each pair (A, B): enumerate every mix of the first 56 bytes (each differing byte from A or
// B), compute FNV-64a, and check whether the stored checksum, itself a mix, can equal it: each
// byte of the hash must be A's or B's checksum byte at that position. Report every validating
// mix that is neither A nor B. Usage: go run main.go [maxTxid]
package main

import (
	"encoding/binary"
	"fmt"
	"os"
	"strconv"
)

const magic = 0xED0CDAED

// endpoints counts the validating mixes equal to an endpoint (a check of the method: every valid
// endpoint must be found).
var endpoints int

func fnv(b []byte) uint64 {
	var h uint64 = 14695981039346656037
	for _, c := range b {
		h ^= uint64(c)
		h *= 1099511628211
	}
	return h
}

func meta(txid uint64, root, pgid uint64) [64]byte {
	var m [64]byte
	binary.LittleEndian.PutUint32(m[0:], magic)
	binary.LittleEndian.PutUint32(m[4:], 2)
	binary.LittleEndian.PutUint32(m[8:], 4096)
	binary.LittleEndian.PutUint32(m[12:], 0)
	binary.LittleEndian.PutUint64(m[16:], root)
	binary.LittleEndian.PutUint64(m[24:], 0)
	binary.LittleEndian.PutUint64(m[32:], 2)
	binary.LittleEndian.PutUint64(m[40:], pgid)
	binary.LittleEndian.PutUint64(m[48:], txid)
	binary.LittleEndian.PutUint64(m[56:], fnv(m[:56]))
	return m
}

func metaT(t uint64) [64]byte {
	if t <= 1 {
		return meta(t, 3, 4)
	}
	return meta(t, t+2, t+3)
}

// check returns the number of validating mixes of a and b other than a and b.
func check(a, b [64]byte, label string) int {
	var diff []int
	for i := 0; i < 56; i++ {
		if a[i] != b[i] {
			diff = append(diff, i)
		}
	}
	bad := 0
	var m [56]byte
	for mask := 0; mask < 1<<len(diff); mask++ {
		copy(m[:], a[:56])
		for k, i := range diff {
			if mask&(1<<k) != 0 {
				m[i] = b[i]
			}
		}
		if binary.LittleEndian.Uint32(m[0:]) != magic || binary.LittleEndian.Uint32(m[4:]) != 2 {
			continue
		}
		h := fnv(m[:])
		var hb [8]byte
		binary.LittleEndian.PutUint64(hb[:], h)
		ok := true
		for k := 0; k < 8; k++ {
			if hb[k] != a[56+k] && hb[k] != b[56+k] {
				ok = false
				break
			}
		}
		if !ok {
			continue
		}
		var full [64]byte
		copy(full[:56], m[:])
		copy(full[56:], hb[:])
		if full == a || full == b {
			endpoints++
		} else {
			bad++
			fmt.Printf("%s: validating mix %x\n", label, full)
		}
	}
	return bad
}

func main() {
	max := uint64(1 << 18)
	if len(os.Args) > 1 {
		n, _ := strconv.ParseUint(os.Args[1], 10, 64)
		max = n
	}
	var zero [64]byte
	total, pairs, maxDiff, mixes := 0, 0, 0, 0
	for t := uint64(0); t <= 1; t++ {
		total += check(zero, metaT(t), fmt.Sprintf("zeros/meta(%d)", t))
		pairs++
	}
	for t := uint64(2); t < max; t++ {
		a, b := metaT(t-2), metaT(t)
		d := 0
		for i := 0; i < 56; i++ {
			if a[i] != b[i] {
				d++
			}
		}
		if d > maxDiff {
			maxDiff = d
		}
		mixes += 1 << d
		total += check(a, b, fmt.Sprintf("meta(%d)/meta(%d)", t-2, t))
		pairs++
	}
	fmt.Printf("pairs %d (txid < %d), max differing bytes in [0,56) between commit metas %d, "+
		"first-56 mixes enumerated %d, validating endpoints found %d, validating mixes other than the endpoints: %d\n",
		pairs, max, maxDiff, mixes, endpoints, total)
}

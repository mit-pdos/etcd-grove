package state

// formatInt16 is strconv.FormatInt(i, 16), copied from Go 1.27.1's src/internal/strconv/itoa.go
// (FormatInt, which strconv.FormatInt calls, and formatBits with base 16, not appending), so that
// the verification has its code: Perennial's model of strconv (Code/strconv.toml) has FormatInt
// as a name only (no semantics). Base 16 is a power of two, so formatBits takes its
// shift-and-mask branch, with shift = bits.TrailingZeros(16) = 4 and mask m = 15; the base-10
// and general branches, unused for base 16, are left out.
func formatInt16(i int64) string {
	const digits = "0123456789abcdefghijklmnopqrstuvwxyz"
	u := uint64(i)
	neg := i < 0

	var a [64 + 1]byte // +1 for sign of 64bit value in base 2
	j := len(a)
	if neg {
		u = -u
	}

	// convert bits
	shift := uint(4)
	b := uint64(16)
	m := uint(16) - 1 // == 1<<shift - 1
	for u >= b {
		j--
		a[j] = digits[uint(u)&m]
		u >>= shift
	}
	// u < base
	j--
	a[j] = digits[uint(u)]

	// add sign, if any
	if neg {
		j--
		a[j] = '-'
	}

	return string(a[j:])
}

// formatUint10 is fmt.Sprint(u) for a uint64 (its decimal digits, as strconv.FormatUint(u, 10)
// gives them), so that the verification has its code: Perennial's model of fmt has Sprint as a
// name only (no semantics). Command.String's SCAN branch formats the count with it.
func formatUint10(u uint64) string {
	var a [20]byte // 2^64 - 1 has 20 decimal digits
	j := len(a)
	for u >= 10 {
		j--
		a[j] = byte('0' + u%10)
		u /= 10
	}
	j--
	a[j] = byte('0' + u)
	return string(a[j:])
}

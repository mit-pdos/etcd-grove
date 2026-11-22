package kvnet

// SplitAddrs is the replicas' addresses, s split at every comma: replica i's address is the i-th
// (ids from 1). The top-level theorem gives the programs the addresses this way, one string, so
// that no Go structure has to be encoded in its statement.
func SplitAddrs(s string) []string {
	var addrs []string
	start := 0
	for i := 0; i < len(s); i++ {
		if s[i] == ',' {
			addrs = append(addrs, s[start:i])
			start = i + 1
		}
	}
	return append(addrs, s[start:])
}

// JoinAddrs is the addresses joined by commas (SplitAddrs reads them back when none holds a comma).
func JoinAddrs(addrs []string) string {
	s := ""
	for i, a := range addrs {
		if i > 0 {
			s += ","
		}
		s += a
	}
	return s
}

// decimal is the value of s as a canonical decimal numeral (digits, at least one, no leading
// zero), at most max; false otherwise.
func decimal(s string, max uint64) (uint64, bool) {
	if len(s) == 0 || len(s) > 5 || (len(s) > 1 && s[0] == '0') {
		return 0, false
	}
	n := uint64(0)
	for i := 0; i < len(s); i++ {
		if s[i] < '0' || s[i] > '9' {
			return 0, false
		}
		n = n*10 + uint64(s[i]-'0')
	}
	return n, n <= max
}

// AddrOk says whether a is a well-formed address: the canonical spelling a.b.c.d:p of an IPv4
// address that is not in 0.0.0.0/8 and is below 224.0.0.0, with a port in 1-32767 or 61000-65535
// (outside Linux's default ephemeral range). It is the net extension's addrOk
// (GooseLang/Ext/Net/Deploy.lean), the top-level theorem's premise on every replica address.
func AddrOk(a string) bool {
	var parts [5]string
	n := 0
	start := 0
	for i := 0; i <= len(a); i++ {
		end := i == len(a)
		if end || a[i] == '.' || a[i] == ':' {
			// three dots, then one colon, in that order
			if n >= 5 || (!end && a[i] == '.' && n >= 3) || (!end && a[i] == ':' && n != 3) || (end && n != 4) {
				return false
			}
			parts[n] = a[start:i]
			n++
			start = i + 1
		}
	}
	var v [5]uint64
	for i := 0; i < 5; i++ {
		x, ok := decimal(parts[i], 65535)
		if !ok {
			return false
		}
		v[i] = x
	}
	return 1 <= v[0] && v[0] < 224 && v[1] <= 255 && v[2] <= 255 && v[3] <= 255 &&
		1 <= v[4] && (v[4] < 32768 || 60999 < v[4])
}

// ValidAddrs says whether the replicas' addresses and bootstrap voters are ones the top-level
// theorem's premises allow: every address well formed and none twice, fewer than 2^32 replicas,
// and the bootstrap voters 1..voters among them.
func ValidAddrs(addrs []string, voters uint64) bool {
	for i, a := range addrs {
		if !AddrOk(a) {
			return false
		}
		for j := 0; j < i; j++ {
			if addrs[j] == a {
				return false
			}
		}
	}
	return uint64(len(addrs)) < 1<<32 && 1 <= voters && voters <= uint64(len(addrs))
}

// ValidCluster says whether the cluster is one the top-level theorem's premises allow: valid
// addresses and voters (ValidAddrs), raft's size limits not both 0, and MaxInflightMsgs a
// positive Go int below 2^62 (raft's RestartNode needs it).
func ValidCluster(addrs []string, voters, maxSizePerMsg, maxCommittedSizePerReady, maxInflightMsgs uint64) bool {
	return ValidAddrs(addrs, voters) && !(maxSizePerMsg == 0 && maxCommittedSizePerReady == 0) &&
		0 < maxInflightMsgs && maxInflightMsgs < 1<<62
}

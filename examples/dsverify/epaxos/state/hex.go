package state

// hexEncodeToString is encoding/hex's EncodeToString (with Encode and hextable), copied from Go
// 1.27.1's src/encoding/hex/hex.go, so that the verification has its code: the harness's model of
// encoding/hex (Harness/Code/encoding/hex.lean) has it as a name only (no semantics).
func hexEncodeToString(src []byte) string {
	const hextable = "0123456789abcdef"
	dst := make([]byte, len(src)*2) // EncodedLen(len(src))
	j := 0
	for _, v := range src {
		dst[j] = hextable[v>>4]
		dst[j+1] = hextable[v&0x0f]
		j += 2
	}
	return string(dst)
}
